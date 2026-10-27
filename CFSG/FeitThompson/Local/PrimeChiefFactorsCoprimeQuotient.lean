module

public import Mathlib.GroupTheory.PGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup QuotientGroup

variable {G : Type*} [Group G] {p : ℕ} {K N X Y : Subgroup G}

theorem inf_le_of_coprime_of_isPGroup [Y.Normal] (hcop : (Nat.card N).Coprime p)
    (hp : IsPGroup p (X ⧸ Y.subgroupOf X)) : X ⊓ N ≤ Y := by
  rintro x ⟨hxX, hxN⟩
  set q : X ⧸ Y.subgroupOf X := QuotientGroup.mk ⟨x, hxX⟩ with hq
  have h1 : orderOf q ∣ Nat.card N := by
    refine (orderOf_map_dvd (QuotientGroup.mk' (Y.subgroupOf X)) ⟨x, hxX⟩).trans ?_
    rw [Subgroup.orderOf_mk x hxX]
    exact Subgroup.orderOf_dvd_natCard N hxN
  obtain ⟨k, hk⟩ := hp q
  have h2 : orderOf q = 1 :=
    ((Nat.Coprime.coprime_dvd_left h1 hcop).pow_right k).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one hk)
  have h3 := orderOf_eq_one_iff.mp h2
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem inf_sup_eq_of_inf_le [N.Normal] (hYX : Y ≤ X) (h : X ⊓ N ≤ Y) : X ⊓ (Y ⊔ N) = Y := by
  refine le_antisymm ?_ (le_inf hYX le_sup_left)
  rintro x ⟨hxX, hxYN⟩
  obtain ⟨y, hy, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxYN
  have hnX : n ∈ X := by
    have : y⁻¹ * (y * n) ∈ X := X.mul_mem (X.inv_mem (hYX hy)) hxX
    simpa using this
  exact Y.mul_mem hy (h ⟨hnX, hn⟩)

theorem inf_sup_eq_of_coprime_of_isPGroup [N.Normal] [Y.Normal] (hYX : Y ≤ X)
    (hcop : (Nat.card N).Coprime p) (hp : IsPGroup p (X ⧸ Y.subgroupOf X)) :
    X ⊓ (Y ⊔ N) = Y :=
  inf_sup_eq_of_inf_le hYX (inf_le_of_coprime_of_isPGroup hcop hp)

theorem le_of_inf_sup_eq (h : X ⊓ (Y ⊔ N) = Y) : Y ≤ X := h ▸ inf_le_left

theorem eq_of_inf_sup_eq_of_le_sup (h : X ⊓ (Y ⊔ N) = Y) (hXYN : X ≤ Y ⊔ N) : Y = X :=
  h.symm.trans (inf_eq_left.mpr hXYN)

theorem map_subgroupOf_conjNormal (X Y : Subgroup G) [X.Normal] [Y.Normal] (g : G) :
    Subgroup.map ((MulAut.conjNormal g : X ≃* X) : X →* X) (Y.subgroupOf X) = Y.subgroupOf X := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ((MulAut.conjNormal g y : X) : G) ∈ Y
    rw [MulAut.conjNormal_apply]
    exact ‹Y.Normal›.conj_mem _ hy g
  · intro hx
    refine ⟨(MulAut.conjNormal g)⁻¹ x, ?_, by simp⟩
    rw [MulAut.conjNormal_inv_apply]
    simpa using ‹Y.Normal›.conj_mem _ hx g⁻¹

def factorConjAut (X Y : Subgroup G) [X.Normal] [Y.Normal] (g : G) :
    (X ⧸ Y.subgroupOf X) ≃* (X ⧸ Y.subgroupOf X) :=
  QuotientGroup.congr _ _ (MulAut.conjNormal g) (map_subgroupOf_conjNormal X Y g)

@[simp]
theorem factorConjAut_mk (X Y : Subgroup G) [X.Normal] [Y.Normal] (g : G) (x : X) :
    factorConjAut X Y g (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal g x) :=
  QuotientGroup.congr_mk _ _ _ _ _

def factorConj (X Y : Subgroup G) [X.Normal] [Y.Normal] : G →* MulAut (X ⧸ Y.subgroupOf X) where
  toFun := factorConjAut X Y
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | _ x => simp
  map_mul' g₁ g₂ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | _ x => simp [MulAut.mul_apply]

@[simp]
theorem factorConj_apply_mk (X Y : Subgroup G) [X.Normal] [Y.Normal] (g : G) (x : X) :
    factorConj X Y g (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal g x) :=
  factorConjAut_mk X Y g x

theorem coe_conjNormal_apply (X : Subgroup G) [X.Normal] (g : G) (x : X) :
    ((MulAut.conjNormal (H := X) g x : X) : G) = g * x * g⁻¹ :=
  MulAut.conjNormal_apply g x

def factorSupHom (N X Y : Subgroup G) [Y.Normal] [N.Normal] :
    X →* (X ⊔ N : Subgroup G) ⧸ (Y ⊔ N).subgroupOf (X ⊔ N) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (le_sup_left : X ≤ X ⊔ N))

theorem factorSupHom_apply [Y.Normal] [N.Normal] (x : X) :
    factorSupHom N X Y x = QuotientGroup.mk (Subgroup.inclusion (le_sup_left : X ≤ X ⊔ N) x) :=
  (rfl)

theorem factorSupHom_surjective [Y.Normal] [N.Normal] :
    Function.Surjective (factorSupHom N X Y) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ y =>
    have hy : (y : G) ∈ (X : Set G) * (N : Set G) := by
      rw [← Subgroup.mul_normal]; exact y.2
    obtain ⟨a, ha, n, hn, han⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [factorSupHom_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (a : G)⁻¹ * (y : G) ∈ Y ⊔ N
    rw [← han, ← mul_assoc]
    simpa using (le_sup_right : N ≤ Y ⊔ N) hn

theorem ker_factorSupHom [Y.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) :
    (factorSupHom N X Y).ker = Y.subgroupOf X := by
  ext k
  simp only [MonoidHom.mem_ker, factorSupHom_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  refine ⟨fun hk => ?_, fun hk => (le_sup_left : Y ≤ Y ⊔ N) hk⟩
  rw [← h]
  exact ⟨k.2, hk⟩

noncomputable def quotientEquivSupQuotient [Y.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) :
    X ⧸ Y.subgroupOf X ≃* (X ⊔ N : Subgroup G) ⧸ (Y ⊔ N).subgroupOf (X ⊔ N) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_factorSupHom h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ factorSupHom_surjective)

@[simp]
theorem quotientEquivSupQuotient_mk [Y.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) (x : X) :
    quotientEquivSupQuotient h (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion (le_sup_left : X ≤ X ⊔ N) x) := by
  rw [quotientEquivSupQuotient, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    factorSupHom_apply]

@[simp]
theorem quotientEquivSupQuotient_symm_mk [Y.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) (x : X) :
    (quotientEquivSupQuotient h).symm
        (QuotientGroup.mk (Subgroup.inclusion (le_sup_left : X ≤ X ⊔ N) x)) =
      QuotientGroup.mk x := by
  rw [MulEquiv.symm_apply_eq, quotientEquivSupQuotient_mk]

theorem quotientEquivSupQuotient_factorConj [X.Normal] [Y.Normal] [N.Normal]
    (h : X ⊓ (Y ⊔ N) = Y) (g : G) (q : X ⧸ Y.subgroupOf X) :
    quotientEquivSupQuotient h (factorConj X Y g q) =
      factorConj (X ⊔ N) (Y ⊔ N) g (quotientEquivSupQuotient h q) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [factorConj_apply_mk, quotientEquivSupQuotient_mk, quotientEquivSupQuotient_mk,
      factorConj_apply_mk]
    congr 1

theorem inf_sup_eq_self_of_le_sup [N.Normal] (hNK : N ≤ K) (hK : K ≤ X ⊔ N) :
    (X ⊓ K) ⊔ N = K := by
  refine le_antisymm (sup_le inf_le_right hNK) ?_
  intro w hw
  obtain ⟨x, hx, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hK hw)
  have hxK : x ∈ K := by
    have : (x * n) * n⁻¹ ∈ K := K.mul_mem hw (K.inv_mem (hNK hn))
    simpa using this
  exact Subgroup.mul_mem_sup ⟨hx, hxK⟩ hn

theorem map_mk'_sup_right [N.Normal] : Subgroup.map (mk' N) (X ⊔ N) = Subgroup.map (mk' N) X := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem comap_map_mk' [N.Normal] : Subgroup.comap (mk' N) (Subgroup.map (mk' N) X) = X ⊔ N := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem map_mk'_lt_map_mk' [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) (hYX : Y < X) :
    Subgroup.map (mk' N) Y < Subgroup.map (mk' N) X := by
  refine lt_of_le_of_ne (Subgroup.map_mono hYX.le) fun he => hYX.ne ?_
  have h1 : Y ⊔ N = X ⊔ N := by
    rw [← comap_map_mk' (N := N) (X := Y), ← comap_map_mk' (N := N) (X := X), he]
  exact eq_of_inf_sup_eq_of_le_sup h (h1 ▸ (le_sup_left : X ≤ X ⊔ N))

theorem not_lt_lt_map_mk' [X.Normal] [Y.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y)
    (hchief : ∀ Z : Subgroup G, Z.Normal → Y < Z → ¬Z < X)
    {W : Subgroup (G ⧸ N)} (hW : W.Normal) (hYW : Subgroup.map (mk' N) Y < W) :
    ¬W < Subgroup.map (mk' N) X := by
  intro hWX
  have hsurj := QuotientGroup.mk'_surjective N
  set Z := Subgroup.comap (mk' N) W with hZ
  have hZn : Z.Normal := hW.comap _
  have hNZ : N ≤ Z := by
    intro n hn
    simp only [hZ, Subgroup.mem_comap]
    rw [show (mk' N) n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact W.one_mem
  have hmapZ : Subgroup.map (mk' N) Z = W :=
    Subgroup.map_comap_eq_self_of_surjective hsurj W
  have hYNZ : Y ⊔ N < Z := by
    refine lt_of_le_of_ne ?_ fun he => hYW.ne ?_
    · rw [← comap_map_mk' (N := N) (X := Y)]; exact Subgroup.comap_mono hYW.le
    · rw [← hmapZ, ← he, map_mk'_sup_right]
  have hZXN : Z < X ⊔ N := by
    refine lt_of_le_of_ne ?_ fun he => hWX.ne ?_
    · rw [← comap_map_mk' (N := N) (X := X)]; exact Subgroup.comap_mono hWX.le
    · rw [← hmapZ, he, map_mk'_sup_right]
  have hZ' : (X ⊓ Z) ⊔ N = Z := inf_sup_eq_self_of_le_sup hNZ hZXN.le
  refine hchief (X ⊓ Z) inferInstance ?_ ?_
  · refine lt_of_le_of_ne (le_inf (le_of_inf_sup_eq h)
      (le_trans le_sup_left hYNZ.le)) fun he => hYNZ.ne ?_
    rw [← hZ', ← he]
  · exact lt_of_le_of_ne inf_le_left fun he => hZXN.ne (by rw [← hZ', he])

theorem isChiefFactor_map_mk'_of_inf_sup_eq [X.Normal] [Y.Normal] [N.Normal]
    (h : X ⊓ (Y ⊔ N) = Y) (hYX : Y < X)
    (hchief : ∀ Z : Subgroup G, Z.Normal → Y < Z → ¬Z < X) :
    (Subgroup.map (mk' N) X).Normal ∧ (Subgroup.map (mk' N) Y).Normal ∧
      Subgroup.map (mk' N) Y < Subgroup.map (mk' N) X ∧
      ∀ W : Subgroup (G ⧸ N), W.Normal → Subgroup.map (mk' N) Y < W →
        ¬W < Subgroup.map (mk' N) X :=
  ⟨‹X.Normal›.map _ (QuotientGroup.mk'_surjective N),
    ‹Y.Normal›.map _ (QuotientGroup.mk'_surjective N),
    map_mk'_lt_map_mk' h hYX, fun _ hW hYW => not_lt_lt_map_mk' h hchief hW hYW⟩

theorem isChiefFactor_map_mk'_of_coprime_of_isPGroup [X.Normal] [Y.Normal] [N.Normal]
    (hcop : (Nat.card N).Coprime p) (hp : IsPGroup p (X ⧸ Y.subgroupOf X)) (hYX : Y < X)
    (hchief : ∀ Z : Subgroup G, Z.Normal → Y < Z → ¬Z < X) :
    (Subgroup.map (mk' N) X).Normal ∧ (Subgroup.map (mk' N) Y).Normal ∧
      Subgroup.map (mk' N) Y < Subgroup.map (mk' N) X ∧
      ∀ W : Subgroup (G ⧸ N), W.Normal → Subgroup.map (mk' N) Y < W →
        ¬W < Subgroup.map (mk' N) X :=
  isChiefFactor_map_mk'_of_inf_sup_eq
    (inf_sup_eq_of_coprime_of_isPGroup hYX.le hcop hp) hYX hchief

theorem commutator_sup_le_sup_iff [X.Normal] [N.Normal] (h : X ⊓ (Y ⊔ N) = Y) (K : Subgroup G) :
    ⁅K, X ⊔ N⁆ ≤ Y ⊔ N ↔ ⁅K, X⁆ ≤ Y := by
  constructor
  · intro hle
    rw [← h]
    exact le_inf (Subgroup.commutator_le_right K X)
      (le_trans (Subgroup.commutator_mono le_rfl le_sup_left) hle)
  · intro hle
    rw [Subgroup.commutator_le]
    intro k hk w hw
    obtain ⟨x, hx, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    have hid : k * (x * n) * k⁻¹ * (x * n)⁻¹
        = (k * x * k⁻¹ * x⁻¹) * (x * (k * n * k⁻¹ * n⁻¹) * x⁻¹) := by group
    rw [commutatorElement_def, hid]
    refine Subgroup.mul_mem _ ((le_sup_left : Y ≤ Y ⊔ N) ?_) ((le_sup_right : N ≤ Y ⊔ N) ?_)
    · refine hle ?_
      have := Subgroup.commutator_mem_commutator (H₁ := K) (H₂ := X) hk hx
      rwa [commutatorElement_def] at this
    · exact ‹N.Normal›.conj_mem _ (N.mul_mem (‹N.Normal›.conj_mem _ hn k) (N.inv_mem hn)) x

theorem commutator_sup_le_sup_iff_of_coprime_of_isPGroup [X.Normal] [Y.Normal] [N.Normal]
    (hYX : Y ≤ X) (hcop : (Nat.card N).Coprime p) (hp : IsPGroup p (X ⧸ Y.subgroupOf X))
    (K : Subgroup G) : ⁅K, X ⊔ N⁆ ≤ Y ⊔ N ↔ ⁅K, X⁆ ≤ Y :=
  commutator_sup_le_sup_iff (inf_sup_eq_of_coprime_of_isPGroup hYX hcop hp) K

end

end CFSG.FeitThompson

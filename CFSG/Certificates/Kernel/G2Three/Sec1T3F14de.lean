module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
  CFSG.Open
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen)

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f14de_closK_bit (gs : List ℕ) : ∀ R k, (closK C gs R).testBit k = true → k < 128
  | 0, k, h => by
    rcases Nat.lt_or_ge k 128 with hk | hk
    · exact hk
    · exfalso
      change (1 : ℕ).testBit k = true at h
      rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))] at h
      exact Bool.false_ne_true h
  | R + 1, k, h => by
    rw [closK_succ, stepK_bit] at h
    rcases h with h | ⟨g, -, h⟩
    · exact f14de_closK_bit gs R k h
    · exact testBit_imgR_lt h

theorem f14de_closK_lt (gs : List ℕ) (R : ℕ) : closK C gs R < 2 ^ 128 :=
  lt128_of_testBit (f14de_closK_bit gs R)

theorem f14de_rep (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {m : ℕ} {X : Set Γ}
    (h : mset elt m = X) : RepM elt m X :=
  h ▸ repM_mset hinj m

theorem f14de_mset_land (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) (a b : ℕ) :
    mset elt (Nat.land a b) = mset elt a ∩ mset elt b := by
  ext x
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    rw [hasB_eq] at hb
    change (a &&& b).testBit i = true at hb
    rw [Nat.testBit_and, Bool.and_eq_true] at hb
    exact ⟨⟨i, hi, by rw [hasB_eq]; exact hb.1, rfl⟩, ⟨i, hi, by rw [hasB_eq]; exact hb.2, rfl⟩⟩
  · rintro ⟨⟨i, hi, ha, rfl⟩, hb⟩
    refine ⟨i, hi, ?_, rfl⟩
    have hb' := (mem_mset_iff hinj hi).1 hb
    rw [hasB_eq] at ha hb' ⊢
    change (a &&& b).testBit i = true
    rw [Nat.testBit_and, ha, hb']
    rfl

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f14de_cenS_mset (X : ℕ) : ∀ gs : List ℕ, (∀ g ∈ gs, g < 128) →
    mset elt (cenS P C X gs) = {x | x ∈ mset elt X ∧ ∀ g ∈ gs, x * elt g = elt g * x}
  | [], _ => by
    change mset elt X = _
    ext x
    simp
  | g :: gs, hgs => by
    change mset elt (cenE P C (cenS P C X gs) g) = _
    rw [cenE_mset hR _ (hgs g List.mem_cons_self),
      f14de_cenS_mset X gs fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f14de_conjM_mset (X : ℕ) {s : ℕ} (hs : s < 128) :
    mset elt (conjM P C V s X) = {g | ∃ x ∈ mset elt X, elt s * x * (elt s)⁻¹ = g} := by
  have e : conjM P C V s X = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P s) (rowT C (atR V s)) i)), acc))
      128 := by
    simp only [conjM, strictN_eq]
  rw [e, mset_recMask (hasB X) (fun i => conjR (rowT P s) (rowT C (atR V s)) i)
    fun _ _ => atR_lt _ _]
  ext g
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hs hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hs hi⟩

theorem f14de_normM_sound {Xm Nm : ℕ} {X N : Subgroup Γ} (hX : mset elt Xm = (X : Set Γ))
    (hN : mset elt Nm = (N : Set Γ)) (h : normM P C V Xm Nm = true) :
    (N.subgroupOf X).Normal := by
  have key : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    rw [← SetLike.mem_coe, ← hX] at hx
    obtain ⟨i, hi, hb, rfl⟩ := hx
    unfold normM at h
    rw [strictB_eq, strictB_eq] at h
    have := allBelow_spec h (by decide) i hi
    rw [hb] at this
    have he : conjM P C V i Nm = Nm := Nat.eq_of_beq_eq_true this
    have hm : elt i * n * (elt i)⁻¹ ∈ mset elt (conjM P C V i Nm) := by
      rw [f14de_conjM_mset hR Nm hi, hN]
      exact ⟨n, hn, rfl⟩
    rw [he, hN] at hm
    exact hm
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using key g.1 g.2 n.1 hn

end Tables

theorem f14de_closure_le_centralizer {s : Set Γ} {x : Γ} (h : ∀ g ∈ s, g * x = x * g) :
    ∀ y ∈ closure s, y * x = x * y := by
  have hle : closure s ≤ centralizer {x} := by
    rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ rfl
    exact (h g hg).symm
  intro y hy
  exact ((mem_centralizer_iff.1 (hle hy)) x rfl).symm

theorem f14de_centEl_eq (T : Subgroup Γ) (g : Γ) : centEl T g = centIn T (closure {g}) := by
  ext x
  simp only [centEl, centIn, mem_inf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h => h g (subset_closure rfl)⟩
  exact (f14de_closure_le_centralizer (s := {g}) (x := x) (by rintro _ rfl; first | exact h | exact h.symm) y hy)

theorem f14de_cen_closure {B : Subgroup Γ} {s : Set Γ} (hB : B = closure s) :
    (cen B : Set Γ) = {x | x ∈ B ∧ ∀ g ∈ s, x * g = g * x} := by
  ext x
  simp only [cen, coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_centralizer_iff,
    Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h g hg => (h g (by rw [hB]; exact subset_closure hg)).symm,
    fun h y hy => ?_⟩
  rw [hB] at hy
  exact f14de_closure_le_centralizer (fun g hg => (h g hg).symm) y hy

theorem f14de_mem_sup {U W : Subgroup Γ} (hcomm : ∀ u ∈ U, ∀ v ∈ W, u * v = v * u) {x : Γ}
    (hx : x ∈ U ⊔ W) : ∃ u ∈ U, ∃ v ∈ W, u * v = x := by
  rw [sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, W.one_mem, mul_one y⟩
    · exact ⟨1, U.one_mem, y, hy, one_mul y⟩
  | one => exact ⟨1, U.one_mem, 1, W.one_mem, mul_one 1⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := hy
    obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := hz
    refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, v₁ * v₂, W.mul_mem hv₁ hv₂, ?_⟩
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [hcomm u₂ hu₂ v₁ hv₁]
      _ = u₁ * v₁ * (u₂ * v₂) := by group
  | inv y _ hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, W.inv_mem hv, ?_⟩
    rw [mul_inv_rev]
    exact hcomm _ (U.inv_mem hu) _ (W.inv_mem hv)

theorem f14de_prodEquiv {X U W : Subgroup Γ} (h : IsInternalDirect X U W) :
    Nonempty (↥X ≃* ↥U × ↥W) := by
  have hUV : U ⊔ W = X := h.1
  have hinf : U ⊓ W = ⊥ := h.2.1
  have hcomm : ∀ u ∈ U, ∀ v ∈ W, u * v = v * u := h.2.2
  let φ : ↥U × ↥W →* ↥X :=
    { toFun := fun p => ⟨(p.1 : Γ) * (p.2 : Γ), by
        rw [← hUV]
        exact Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩
        apply Subtype.ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, MonoidHom.coe_mk, OneHom.coe_mk]
        calc (↑u₁ * ↑u₂ : Γ) * (↑v₁ * ↑v₂)
            = ↑u₁ * (↑u₂ * ↑v₁) * ↑v₂ := by group
          _ = ↑u₁ * (↑v₁ * ↑u₂) * ↑v₂ := by rw [hcomm u₂ u₂.2 v₁ v₁.2]
          _ = ↑u₁ * ↑v₁ * (↑u₂ * ↑v₂) := by group }
  have hinj : Function.Injective φ := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ heq
    have hval : (u₁ : Γ) * (v₁ : Γ) = (u₂ : Γ) * (v₂ : Γ) := congrArg Subtype.val heq
    have hthis : (u₂ : Γ)⁻¹ * (u₁ : Γ) = (v₂ : Γ) * (v₁ : Γ)⁻¹ := by
      calc (u₂ : Γ)⁻¹ * (u₁ : Γ)
          = (u₂ : Γ)⁻¹ * ((u₁ : Γ) * (v₁ : Γ)) * (v₁ : Γ)⁻¹ := by group
        _ = (u₂ : Γ)⁻¹ * ((u₂ : Γ) * (v₂ : Γ)) * (v₁ : Γ)⁻¹ := by rw [hval]
        _ = (v₂ : Γ) * (v₁ : Γ)⁻¹ := by group
    have hmem : (u₂ : Γ)⁻¹ * u₁ ∈ U ⊓ W := by
      refine ⟨U.mul_mem (U.inv_mem u₂.2) u₁.2, ?_⟩
      rw [hthis]
      exact W.mul_mem v₂.2 (W.inv_mem v₁.2)
    rw [hinf, Subgroup.mem_bot] at hmem
    have hu : u₁ = u₂ := by
      apply Subtype.ext
      exact (inv_mul_eq_one.1 hmem).symm
    have h2 : (v₂ : Γ) * (v₁ : Γ)⁻¹ = 1 := by rw [← hthis, hmem]
    have hv : v₁ = v₂ := by
      apply Subtype.ext
      exact (mul_inv_eq_one.1 h2).symm
    exact Prod.ext hu hv
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := f14de_mem_sup hcomm (hUV ▸ hx)
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem f14de_closure_invol {c : Γ} (hc2 : c * c = 1) : ∀ x ∈ closure {c}, x = 1 ∨ x = c := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc2
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Or.inr hx
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hc2
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr hci

theorem f14de_isZ2xD8 {X D : Subgroup Γ} {c : Γ} (hc1 : c ≠ 1) (hc2 : c * c = 1)
    (hX : (X : Set Γ) = (D : Set Γ) ∪ (c * ·) '' (D : Set Γ)) (hcD : c ∉ D)
    (hcom : ∀ d ∈ D, d * c = c * d) (φ : DihedralGroup 4 →* Γ) (hφ : Function.Injective φ)
    (hr : Set.range φ = D) : IsZ2xD8Decomp X c D := by
  have hord : orderOf c = 2 := f13_orderOf_eq_two_iff.2 ⟨hc1, hc2⟩
  have hDX : D ≤ X := fun d hd => by
    rw [← SetLike.mem_coe, hX]
    exact Or.inl hd
  have hcX : c ∈ X := by
    rw [← SetLike.mem_coe, hX]
    exact Or.inr ⟨1, D.one_mem, mul_one c⟩
  have hsup : closure {c} ⊔ D = X := by
    refine le_antisymm (sup_le ((closure_le _).2 (by simpa using hcX)) hDX) fun x hx => ?_
    rw [← SetLike.mem_coe, hX] at hx
    rcases hx with hx | ⟨d, hd, rfl⟩
    · exact mem_sup_right hx
    · exact mul_mem_sup (subset_closure rfl) hd
  have hinf : closure {c} ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases f14de_closure_invol hc2 x hx1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hx2 hcD
  have hcomm : ∀ u ∈ closure {c}, ∀ v ∈ D, u * v = v * u := by
    intro u hu v hv
    rcases f14de_closure_invol hc2 u hu with rfl | rfl
    · simp
    · exact (hcom v hv).symm
  have hrange : φ.range = D := SetLike.coe_injective (by rw [MonoidHom.coe_range, hr])
  have hD8 : Nonempty (↥D ≃* DihedralGroup 4) :=
    ⟨((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)).symm⟩
  have hC2 : ↥(closure {c}) ≃* Multiplicative (ZMod 2) := by
    have hcard : Nat.card ↥(zpowers c) = 2 := by rw [Nat.card_zpowers, hord]
    have e1 : ↥(zpowers c) ≃* Multiplicative (ZMod 2) := by
      have h := zmodCyclicMulEquiv (G := ↥(zpowers c)) inferInstance
      rw [hcard] at h
      exact h.symm
    exact (MulEquiv.subgroupCongr (zpowers_eq_closure c)).symm.trans e1
  obtain ⟨eID⟩ := f14de_prodEquiv ⟨hsup, hinf, hcomm⟩
  exact ⟨⟨hsup, hinf, hcomm⟩, hord, hD8,
    ⟨eID.trans (MulEquiv.prodCongr hC2 (Classical.choice hD8))⟩⟩

theorem f14de_maxEA_of_eaMaxK (hR : RealT elt P C V Q) {G₀ : Subgroup Γ} {L m : ℕ}
    (hm : m ≤ 448)
    (hlat : (∀ k < m, ∃ K : Subgroup Γ, K ≤ G₀ ∧ RepM elt (latM L k) K) ∧
      ∀ K ≤ G₀, ∃ k < m, RepM elt (latM L k) K)
    {Xm k1 k2 : ℕ} {X K₁ K₂ : Subgroup Γ} (hX : mset elt Xm = (X : Set Γ)) (hXG : X ≤ G₀)
    (h1 : mset elt (entL L k1) = (K₁ : Set Γ)) (h2 : mset elt (entL L k2) = (K₂ : Set Γ))
    (h : eaMaxK Q L m Xm 1 k1 k2 = true) : maxElemAbelian X = {K₁, K₂} := by
  have hN : mset elt 1 = ((⊥ : Subgroup Γ) : Set Γ) := by
    rw [mset_one hR.one, coe_bot]
  have core := eaMaxK_sound hR hlat hm hXG (f14de_rep hR.inj hX) (f14de_rep hR.inj hN)
    (by norm_num) h (f14de_rep hR.inj h1) (f14de_rep hR.inj h2)
  ext K
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, ← core K]
  simp only [maxElemAbelian, IsMaxSq, Set.mem_setOf_eq, isElemAbelian_iff_sq, bot_le, mem_bot,
    true_and]

variable [Finite Γ]

theorem f14de_eaMax_sound (hR : RealT elt P C V Q) {G₀ : Subgroup Γ} {L m : ℕ} (hm : m ≤ 448)
    (hlat : (∀ k < m, ∃ K : Subgroup Γ, K ≤ G₀ ∧ RepM elt (latM L k) K) ∧
      ∀ K ≤ G₀, ∃ k < m, RepM elt (latM L k) K)
    {Xm Nm k1 k2 : ℕ} {X N K₁ K₂ : Subgroup Γ} (hX : mset elt Xm = (X : Set Γ))
    (hN : mset elt Nm = (N : Set Γ)) (hNb : Nm < 2 ^ 128) (hXG : X ≤ G₀)
    (hn : (N.subgroupOf X).Normal)
    (h1 : mset elt (entL L k1) = (K₁ : Set Γ)) (h2 : mset elt (entL L k2) = (K₂ : Set Γ))
    (h : eaMaxK Q L m Xm Nm k1 k2 = true) :
    SecProp X N (fun Y _ _ π => maxElemAbelian (⊤ : Subgroup Y) =
      {(K₁.subgroupOf X).map π, (K₂.subgroupOf X).map π}) := by
  have hX' := f14de_rep hR.inj hX
  have hN' := f14de_rep hR.inj hN
  have hK₁ := f14de_rep hR.inj h1
  have hK₂ := f14de_rep hR.inj h2
  obtain ⟨hNK, hKX, -⟩ := (eaMaxK_sound hR hlat hm hXG hX' hN' hNb h hK₁ hK₂ K₁).2 (Or.inl rfl)
  exact ⟨hn, eaMaxK_quo hR hlat hm hXG (hNK.trans hKX) hX' hN' hNb h hK₁ hK₂⟩

theorem f14de_setOf_two (u v : Γ) : {x | x ∈ [u, v]} = ({u, v} : Set Γ) := by
  ext x
  simp

theorem f14de_setOf_four (u v w s : Γ) : {x | x ∈ [u, v, w, s]} = ({u, v, w, s} : Set Γ) := by
  ext x
  simp

theorem f14de_S_le {fr : Frame Γ} : fr.S ≤ fr.Sσ := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem f14de_A_le {fr : Frame Γ} : fr.A ≤ fr.S := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem fact14_45_of_twin {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q L N kE kF kA kB kZ R R' : ℕ}
    (hR : RealT elt P C V Q)
    (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (hN : N ≤ 448)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) K) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) K)
    (hZ2 : zSeries 2 fr.S = closure {fr.b₁, fr.b₂})
    (hd : f14dK P C V Q L N 1 2 3 4 5 kE kF R = true)
    (he : f14eK P C V Q L N 1 2 3 4 5 kA kB kZ R' = true) :
    (fr.E ⊔ fr.F = fr.A ⊓ fr.B ∧
      IsZ2xD8Decomp (fr.A ⊓ fr.B) (fr.b₁ * fr.b₂) (closure {fr.a₁ * fr.a₂, fr.b₁}) ∧
      maxElemAbelian (fr.A ⊓ fr.B) = {fr.E, fr.F} ∧ fr.E ⊓ fr.F = cen fr.B) ∧
    (SecProp fr.S fr.F (fun Y _ _ π =>
        maxElemAbelian (⊤ : Subgroup Y) =
          {(fr.A.subgroupOf fr.S).map π, (fr.B.subgroupOf fr.S).map π}) ∧
      SecProp fr.S fr.Z (fun Y _ _ π =>
        maxElemAbelian (⊤ : Subgroup Y) = {(fr.A.subgroupOf fr.S).map π,
          ((zSeries 2 fr.S ⊔ closure {fr.h₀}).subgroupOf fr.S).map π}) ∧
      Nonempty (↥(zSeries 2 fr.S ⊔ closure {fr.h₀}) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) := by
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, -, h123, -, -⟩ := f13_prods hR hg
  have l13 : mulE P 1 3 < 128 := f13_mulE_lt _ _ _
  have l24 : mulE P 2 4 < 128 := f13_mulE_lt _ _ _
  have l123 : mulE P (mulE P 1 2) 3 < 128 := f13_mulE_lt _ _ _
  have lz : atR Q 2 < 128 := atR_lt _ _
  have mA : ∀ {R : ℕ}, closOK C [1, 2, 3, 4] R = true →
      mset elt (closK C [1, 2, 3, 4] R) = (fr.A : Set Γ) := by
    intro R hc
    rw [closK_closure hR (by decide) hc, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4]
    rw [f14de_setOf_four]
    rfl
  have mS : ∀ {R : ℕ}, closOK C [1, 2, 3, 4, 5] R = true →
      mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
    intro R hc
    rw [closK_closure hR (by decide) hc, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
    rw [f13_setOf_five]
    rfl
  have mB : ∀ {S : ℕ}, mset elt S = (fr.S : Set Γ) →
      mset elt (cenE P C S (mulE P 2 4)) = (fr.B : Set Γ) := by
    intro S hS
    rw [f13_cenE hR hS l24, h24, f14de_centEl_eq]
    rfl
  have mF : ∀ {R : ℕ}, closOK C [mulE P 1 3, mulE P 2 4, atR Q 2] R = true →
      mset elt (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R) = (fr.F : Set Γ) := by
    intro R hc
    have hl : ∀ g ∈ [mulE P 1 3, mulE P 2 4, atR Q 2], g < 128 := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exacts [l13, l24, lz]
    rw [closK_closure hR hl hc, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, h13, h24, hz]
    rw [f13_setOf_three]
    rfl
  have hlB : ∀ g ∈ [mulE P 1 3, 2, 4, 5], g < 128 := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exacts [l13, by norm_num, by norm_num, by norm_num]
  have hAB : fr.A ⊓ fr.B ≤ fr.Sσ := inf_le_left.trans (f14de_A_le.trans f14de_S_le)
  refine ⟨?_, ?_⟩
  · simp only [f14dK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at hd
    obtain ⟨cA, cS, cE, cF, cB, hBm, hpr, hpm, hz2, hea, hkE, hkF, hEF⟩ := hd
    have hS := mS cS
    have hA := mA cA
    have hB := mB hS
    have hF := mF cF
    have hE : mset elt (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2] R) =
        (fr.E : Set Γ) := by
      have hl : ∀ g ∈ [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2], g < 128 := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl
        exacts [l24, l123, lz]
      rw [closK_closure hR hl cE, f13_setOf_eq_map]
      simp only [List.map_cons, List.map_nil, h123, h24, hz]
      rw [f13_setOf_three]
      rfl
    have hABm : mset elt (Nat.land (closK C [1, 2, 3, 4] R) (cenE P C (closK C [1, 2, 3, 4, 5] R)
        (mulE P 2 4))) = ((fr.A ⊓ fr.B : Subgroup Γ) : Set Γ) := by
      rw [f14de_mset_land hR.inj, hA, hB, coe_inf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply SetLike.coe_injective
      have hp := permB_spec hR hpm
      rw [hE, hF] at hp
      rw [f13_coe_sup hp, ← hE, ← hF, ← prodM_mset hR, hpr, hABm]
    · obtain ⟨hD, hc1, hc2, hX, hcD, hcom, φ, hφ, hr⟩ := z2d8K_sound hR l24 (by norm_num) l13 hz2
      have hD' : mset elt (closK C [2, mulE P 1 3] R) =
          ((closure {fr.a₁ * fr.a₂, fr.b₁} : Subgroup Γ) : Set Γ) := by
        rw [hD, f13_setOf_eq_map]
        simp only [List.map_cons, List.map_nil, e2, h13]
        rw [f14de_setOf_two, Set.pair_comm]
      rw [hD'] at hX hcD hcom hr
      rw [hABm] at hX
      rw [h24] at hc1 hc2 hX hcD hcom
      exact f14de_isZ2xD8 hc1 hc2 hX hcD hcom φ hφ hr
    · exact f14de_maxEA_of_eaMaxK hR hN hlat hABm hAB (by rw [hkE, hE]) (by rw [hkF, hF]) hea
    · apply SetLike.coe_injective
      have hBc : fr.B = closure {x | ∃ g ∈ [mulE P 1 3, 2, 4, 5], elt g = x} := by
        apply SetLike.coe_injective
        rw [← hB, hBm, closK_closure hR hlB cB]
      rw [coe_inf, ← hE, ← hF, ← f14de_mset_land hR.inj, hEF, f14de_cenS_mset hR _ _ hlB,
        f14de_cen_closure hBc, hB]
      ext x
      simp only [Set.mem_setOf_eq, SetLike.mem_coe]
      refine and_congr_right fun _ => ⟨fun h g hg => ?_, fun h g hg => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := hg
        exact h i hi
      · exact h _ ⟨g, hg, rfl⟩
  · simp only [f14eK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at he
    obtain ⟨cS, cA, cB, cF, cZ, cZ2h, cH0, hBm, hnF, heF, hkA, hkB, hnZ, heZ, hkZ, -, -, hz2⟩ := he
    have hS := mS cS
    have hA := mA cA
    have hB := mB hS
    have hF := mF cF
    have hlz : ∀ g ∈ [atR Q 2], g < 128 := by simp [lz]
    have hZ : mset elt (closK C [atR Q 2] R') = (fr.Z : Set Γ) := by
      rw [closK_closure hR hlz cZ, f13_setOf_eq_map]
      simp only [List.map_cons, List.map_nil, hz]
      rw [f13_setOf_one, ← zpowers_eq_closure]
      rfl
    have hl25 : ∀ g ∈ [2, 4, 5], g < 128 := by decide
    have hZ2h : mset elt (closK C [2, 4, 5] R') =
        ((zSeries 2 fr.S ⊔ closure {fr.h₀} : Subgroup Γ) : Set Γ) := by
      rw [closK_closure hR hl25 cZ2h, f13_setOf_eq_map, hZ2, ← Subgroup.closure_union]
      simp only [List.map_cons, List.map_nil, e2, e4, e5]
      congr 2
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hSG : fr.S ≤ fr.Sσ := f14de_S_le
    refine ⟨?_, ?_, ?_⟩
    · exact f14de_eaMax_sound hR hN hlat hS hF (f14de_closK_lt _ _) hSG
        (f14de_normM_sound hR hS hF hnF) (by rw [hkA, hA]) (by rw [hkB, hB]) heF
    · exact f14de_eaMax_sound hR hN hlat hS hZ (f14de_closK_lt _ _) hSG
        (f14de_normM_sound hR hS hZ hnZ) (by rw [hkA, hA]) (by rw [hkZ, hZ2h]) heZ
    · obtain ⟨hD, hc1, hc2, hX, hcD, hcom, φ, hφ, hr⟩ :=
        z2d8K_sound hR l24 (by norm_num) (by norm_num) hz2
      rw [hD] at hX hcD hcom hr
      rw [hZ2h] at hX
      rw [h24] at hc1 hc2 hX hcD hcom
      exact (f14de_isZ2xD8 hc1 hc2 hX hcD hcom φ hφ hr).2.2.2

end CFSG.KC.G2Three.Sec1T3

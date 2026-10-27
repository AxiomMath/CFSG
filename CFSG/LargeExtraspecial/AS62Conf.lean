module

public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS62O4
public import CFSG.LargeExtraspecial.AS35DSixFour
public import CFSG.LargeExtraspecial.AS35DSixThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] [Finite G]

structure ConfHyp (S : Setting G) (H : Subgroup G) : Prop where
  h22 : S14.AschbacherTwoTwoStmt
  hw : S.width = 2
  hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  hH : S.IsHStar H

omit [Finite G] in
theorem commute_of_mem_closure {s : Set G} (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) {x y : G}
    (hx : x ∈ closure s) (hy : y ∈ closure s) : x * y = y * x := by
  have h1 : closure s ≤ centralizer s :=
    (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb => hs b hb a ha
  have h2 : closure s ≤ centralizer ({x} : Set G) :=
    (closure_le _).mpr fun b hb => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (h1 hx)) b hb)
  exact (mem_centralizer_singleton_iff.mp (h2 hy)).symm

omit [Finite G] in
theorem commute_of_forall_mem_closure {s : Set G} {h : G} (hs : ∀ a ∈ s, h * a = a * h) {x : G}
    (hx : x ∈ closure s) : h * x = x * h := by
  have h1 : closure s ≤ centralizer ({h} : Set G) :=
    (closure_le _).mpr fun a ha => mem_centralizer_singleton_iff.mpr (hs a ha).symm
  exact (mem_centralizer_singleton_iff.mp (h1 hx)).symm

theorem rhoL_mul' (S : Setting G) {x y : G} (hx : x ∈ S.M) (hy : y ∈ S.M) :
    S.rhoL (mul_mem hx hy) = S.rhoL hx * S.rhoL hy := by
  unfold Setting.rhoL
  rw [show (⟨x * y, mul_mem hx hy⟩ : S.M) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
  rfl

omit [Finite G] in
theorem zConj_mul_self (S : Setting G) {H : Subgroup G} {p : G} (hp : p ∈ S.zConj H) :
    p * p = 1 := by
  obtain ⟨k, -, rfl⟩ := hp
  exact S.mul_self_of_isConj (isConj_iff.mpr ⟨k, rfl⟩)

theorem rhoL_eq_one_iff (S : Setting G) {x : G} (hx : x ∈ S.M) : S.rhoL hx = 1 ↔ x ∈ S.QG := by
  rw [← S.ρ_eq_one_iff ⟨x, hx⟩]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem sixFourConcl (hc : ConfHyp S H) : S.SixFourConcl := by
  intro H' hH'
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH'.1.2.2
  exact ⟨(S.sixFour hc.h22 hc.hW hH' hgH hgM).1,
    fun k hk hkM => (S.sixFour hc.h22 hc.hW hH' hk hkM).2⟩

theorem isAFive (hc : ConfHyp S H) : S.IsAFive H := (hc.sixFourConcl H hc.hH).1

omit [Finite G] in
theorem QG_le (hc : ConfHyp S H) : S.QG ≤ H := hc.hH.1.1

omit [Finite G] in
theorem z_mem (hc : ConfHyp S H) : S.z ∈ H := hc.QG_le S.z_mem_QG

theorem ncard_zConj (hc : ConfHyp S H) : (S.zConj H).ncard = 5 := by
  obtain ⟨⟨_, _, h5, -⟩, -⟩ := hc.isAFive
  exact h5

theorem commute_zConj (hc : ConfHyp S H) {a b : G} (ha : a ∈ S.zConj H)
    (hb : b ∈ S.zConj H) : a * b = b * a := by
  obtain ⟨⟨_, _, -, hcomm, -⟩, -⟩ := hc.isAFive
  exact hcomm a ha b hb

theorem commute_V (hc : ConfHyp S H) {x y : G} (hx : x ∈ closure (S.zConj H))
    (hy : y ∈ closure (S.zConj H)) : x * y = y * x :=
  commute_of_mem_closure (fun _ ha _ hb => hc.commute_zConj ha hb) hx hy

theorem card_V (hc : ConfHyp S H) : Nat.card (closure (S.zConj H)) = 16 := by
  obtain ⟨⟨_, _, -, -, hV, -⟩, hC⟩ := hc.isAFive
  rw [hC, card_bot, mul_one] at hV
  exact hV

omit [Finite G] in
theorem zConj_subset (hc : ConfHyp S H) : S.zConj H ⊆ H := by
  rintro _ ⟨h, hh, rfl⟩
  exact H.mul_mem (H.mul_mem hh hc.z_mem) (H.inv_mem hh)

omit [Finite G] in
theorem V_le (hc : ConfHyp S H) : closure (S.zConj H) ≤ H := (closure_le _).mpr hc.zConj_subset

theorem mem_M_of_mem (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) : p ∈ S.M :=
  S.mem_M_iff.mpr (hc.commute_zConj hp (self_mem_conjIn _ _))

theorem V_le_M (hc : ConfHyp S H) : closure (S.zConj H) ≤ S.M :=
  (closure_le _).mpr fun _ hp => hc.mem_M_of_mem hp

omit [Finite G] in
theorem not_mem_QG (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    p ∉ S.QG := by
  obtain ⟨k, -, rfl⟩ := hp
  exact fun hQ => hpz (hc.hW k hQ)

theorem exists_conj_eq (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    ∃ k : G, k * S.z * k⁻¹ = p ∧ S.HAt k = H ∧ p ∈ S.DSet := by
  obtain ⟨k, hkH, rfl⟩ := hp
  have hkM : k ∉ S.M := fun hkM => hpz (S.conj_z_of_mem_M hkM)
  obtain ⟨-, hHk, hD⟩ := S.sixFour hc.h22 hc.hW hc.hH hkH hkM
  exact ⟨k, rfl, hHk.symm, ⟨⟨k, rfl, hHk ▸ hc.hH, hHk ▸ hc.ncard_zConj⟩, hD⟩⟩

theorem fiveOne (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    IsTypeA S.q (S.rhoL (hc.mem_M_of_mem hp)) 2 ∧
      Nat.card S.QG = 4 * Nat.card ↥(S.QG ⊓ centralizer ({p} : Set G)) ∧
      S.cqxSub p = fixSpace (S.rhoL (hc.mem_M_of_mem hp)) := by
  obtain ⟨-, -, -, hD⟩ := hc.exists_conj_eq hp hpz
  exact S.fiveOne_two hc.sixFourConcl hc.hW hD _

theorem finrank_Qt (hc : ConfHyp S H) : finrank (ZMod 2) S.Qt = 4 := by
  rw [S.finrank_Qt_eq_two_mul_width, hc.hw]

theorem card_QG (hc : ConfHyp S H) : Nat.card S.QG = 32 := by
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hc.hw]
  norm_num

theorem cqxSub_eq (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    S.cqxSub p = commSpace (S.rhoL (hc.mem_M_of_mem hp)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hA, -, hK⟩ := hc.fiveOne hp hpz
  rw [hK, fixSpace_eq_commSpace_of_isTypeA hc.finrank_Qt S.q_nondegenerate hA]

theorem cqx_le_V (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    S.QG ⊓ centralizer ({p} : Set G) ≤ closure (S.zConj H) := by
  obtain ⟨k, hk, hkH, hpD⟩ := hc.exists_conj_eq hp hpz
  intro y hy
  have hyQ : y ∈ S.QG := (mem_inf.mp hy).1
  have hcl : S.cl y ∈ commSpace (S.rhoL (hc.mem_M_of_mem hp)) := by
    rw [← hc.cqxSub_eq hp hpz]
    exact S.cl_mem_clSub hy hyQ
  have h1 := S.mem_closure_zConj_of_cl_mem_commSpace hpD.1 hk (hc.mem_M_of_mem hp) hyQ hcl
  rwa [hkH] at h1

theorem cqx_eq (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    S.QG ⊓ centralizer ({p} : Set G) = closure (S.zConj H) ⊓ S.QG := by
  refine le_antisymm (le_inf (hc.cqx_le_V hp hpz) inf_le_left) fun y hy => ?_
  refine mem_inf.mpr ⟨(mem_inf.mp hy).2, mem_centralizer_singleton_iff.mpr ?_⟩
  exact hc.commute_V (mem_inf.mp hy).1 (subset_closure hp)

theorem card_cqx (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    Nat.card ↥(S.QG ⊓ centralizer ({p} : Set G)) = 8 := by
  have h := (hc.fiveOne hp hpz).2.1
  rw [hc.card_QG] at h
  omega

theorem mem_V_of_commute (hc : ConfHyp S H) {h : G} (hh : ∀ ω ∈ S.zConj H, h * ω = ω * h)
    {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) : h ∈ closure (S.zConj H) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hhM : h ∈ S.M := S.mem_M_iff.mpr (hh _ (self_mem_conjIn _ _))
  have hpM := hc.mem_M_of_mem hp
  have hhp : h * p = p * h := hh p hp
  have hcR : ∀ y, y ∈ S.QG → y * p = p * y → y ∈ closure (S.zConj H) := fun y hy hyp =>
    hc.cqx_le_V hp hpz (mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyp⟩)
  obtain ⟨hA, -, -⟩ := hc.fiveOne hp hpz
  have hfix : ∀ v ∈ commSpace (S.rhoL hpM), S.rhoL hhM v = v := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := S.exists_cl v
    have hyR : y ∈ S.QG ⊓ centralizer ({p} : Set G) := by
      rw [← S.clPre_cqxSub hpM, hc.cqxSub_eq hp hpz]
      exact ⟨hy, hv⟩
    rw [S.rhoL_cl hhM hy, commute_of_forall_mem_closure hh (hc.cqx_le_V hp hpz hyR),
      mul_inv_cancel_right]
  rcases eq_one_or_eq_of_isTypeA_of_fix hc.finrank_Qt S.q_nondegenerate hA (S.rhoL_mem hhM)
    hfix with h1 | h1
  · exact hcR h ((rhoL_eq_one_iff S hhM).mp h1) hhp
  · have hpp := zConj_mul_self S hp
    have h2 : S.rhoL (mul_mem hhM hpM) = 1 := by
      rw [rhoL_mul' S hhM hpM, h1, S.rhoL_mul_self hpM hpp]
    have h3 : h * p ∈ closure (S.zConj H) :=
      hcR _ ((rhoL_eq_one_iff S _).mp h2) (by rw [← mul_assoc, hhp])
    have h4 : h = h * p * p := by rw [mul_assoc, hpp, mul_one]
    rw [h4]
    exact mul_mem h3 (subset_closure hp)

theorem exists_QG_conj (hc : ConfHyp S H) {p p' : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z)
    (hp' : p' ∈ S.zConj H) (hp'z : p' ≠ S.z) : ∃ q ∈ S.QG, q * p * q⁻¹ = p' := by
  set O := {x | ∃ q ∈ S.QG, q * p * q⁻¹ = x} with hO
  have hOsub : O ⊆ S.zConj H \ {S.z} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨conj_mem_conjIn_of_mem (hc.QG_le hq) hp, fun h' => hpz ?_⟩
    have h'' : q * p * q⁻¹ = S.z := h'
    calc p = q⁻¹ * (q * p * q⁻¹) * q := by group
      _ = S.z := by rw [h'', mul_assoc, ← S.z_comm_QG hq]; group
  have hcard : O.ncard = 4 := by
    have h1 := Setting.card_eq_relIndex_mul S.QG (centralizer ({p} : Set G))
    rw [Setting.relIndex_centralizer_eq_ncard, ← hO, hc.card_QG, hc.card_cqx hp hpz] at h1
    omega
  have hΩz : (S.zConj H \ {S.z}).ncard = 4 := by
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr (self_mem_conjIn _ _)), hc.ncard_zConj,
      Set.ncard_singleton]
  have hOeq : O = S.zConj H \ {S.z} :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hcard, hΩz]) (Set.toFinite _)
  have hpO : p' ∈ O := by rw [hOeq]; exact ⟨hp', hp'z⟩
  exact hpO

theorem mul_mem_QG (hc : ConfHyp S H) {p p' : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z)
    (hp' : p' ∈ S.zConj H) (hp'z : p' ≠ S.z) : p * p' ∈ S.QG := by
  obtain ⟨q, hq, rfl⟩ := hc.exists_QG_conj hp hpz hp' hp'z
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right (zConj_mul_self S hp)
  rw [show p * (q * p * q⁻¹) = (p * q * p⁻¹) * q⁻¹ by rw [hpinv]; group]
  exact S.QG.mul_mem (S.conj_mem_QG (hc.mem_M_of_mem hp) hq) (S.QG.inv_mem hq)

end ConfHyp

structure Label (S : Setting G) (H : Subgroup G) where
  ι : Fin 5 ≃ S.zConj H
  ι_zero : (ι 0 : G) = S.z

namespace Label

variable {S : Setting G} {H : Subgroup G} (L : Label S H)

@[expose] def zz (i : Fin 5) : G := (L.ι i : G)

@[expose] def σ : H →* Equiv.Perm (Fin 5) :=
  (L.ι.symm.permCongrHom : Equiv.Perm (S.zConj H) ≃* Equiv.Perm (Fin 5)).toMonoidHom.comp
    (conjAct S.z H)

omit [Finite G] in
theorem σ_apply (h : H) (i : Fin 5) : L.σ h i = L.ι.symm (conjAct S.z H h (L.ι i)) := rfl

omit [Finite G] in
theorem conj_zz (h : H) (i : Fin 5) : (h : G) * L.zz i * (h : G)⁻¹ = L.zz (L.σ h i) := by
  rw [zz, zz, σ_apply, Equiv.apply_symm_apply, conjAct_apply]

omit [Finite G] in
theorem zz_zero : L.zz 0 = S.z := L.ι_zero

omit [Finite G] in
theorem zz_mem (i : Fin 5) : L.zz i ∈ S.zConj H := (L.ι i).2

omit [Finite G] in
theorem zz_injective : Function.Injective L.zz := fun _ _ h => L.ι.injective (Subtype.ext h)

omit [Finite G] in
theorem exists_zz_eq {x : G} (hx : x ∈ S.zConj H) : ∃ i, L.zz i = x :=
  ⟨L.ι.symm ⟨x, hx⟩, by rw [zz, Equiv.apply_symm_apply]⟩

omit [Finite G] in
theorem zz_ne_z {i : Fin 5} (hi : i ≠ 0) : L.zz i ≠ S.z := by
  rw [← L.zz_zero]
  exact L.zz_injective.ne hi

omit [Finite G] in
theorem zz_mul_self (i : Fin 5) : L.zz i * L.zz i = 1 := zConj_mul_self S (L.zz_mem i)

omit [Finite G] in
theorem σ_zero_eq_zero_iff (h : H) : L.σ h 0 = 0 ↔ (h : G) ∈ S.M := by
  rw [S.mem_M_iff, ← L.zz_injective.eq_iff, ← L.conj_zz, L.zz_zero]
  constructor
  · intro e
    calc (h : G) * S.z = h * S.z * (h : G)⁻¹ * h := by group
      _ = S.z * h := by rw [e]
  · intro e
    rw [e, mul_inv_cancel_right]

omit [Finite G] in
theorem sign_σ (hA : S.IsAFive H) (h : H) : Equiv.Perm.sign (L.σ h) = 1 := by
  obtain ⟨⟨_, _, -, -, -, hsign, -⟩, -⟩ := hA
  change Equiv.Perm.sign (L.ι.symm.permCongr (conjAct S.z H h)) = 1
  rw [Equiv.Perm.sign_permCongr]
  exact hsign h

omit [Finite G] in
theorem exists_σ_eq (hA : S.IsAFive H) {p : Equiv.Perm (Fin 5)} (hp : Equiv.Perm.sign p = 1) :
    ∃ h : H, L.σ h = p := by
  obtain ⟨⟨_, _, -, -, -, -, hsurj⟩, -⟩ := hA
  obtain ⟨h, hh⟩ := hsurj (L.ι.permCongr p) (by rw [Equiv.Perm.sign_permCongr]; exact hp)
  refine ⟨h, ?_⟩
  change L.ι.symm.permCongr (conjAct S.z H h) = p
  rw [hh]
  ext i
  simp [Equiv.permCongr_apply]

omit [Finite G] in
theorem range_σ (hA : S.IsAFive H) : L.σ.range = alternatingGroup (Fin 5) := by
  ext p
  rw [MonoidHom.mem_range, Equiv.Perm.mem_alternatingGroup]
  exact ⟨fun ⟨h, hh⟩ => hh ▸ L.sign_σ hA h, fun hp => L.exists_σ_eq hA hp⟩

theorem σ_eq_one_iff (hc : ConfHyp S H) (h : H) :
    L.σ h = 1 ↔ (h : G) ∈ closure (S.zConj H) := by
  constructor
  · intro h1
    refine hc.mem_V_of_commute (fun ω hω => ?_) (L.zz_mem 1) (L.zz_ne_z (by decide))
    obtain ⟨i, rfl⟩ := L.exists_zz_eq hω
    have e := L.conj_zz h i
    rw [h1, Equiv.Perm.one_apply] at e
    calc (h : G) * L.zz i = h * L.zz i * (h : G)⁻¹ * h := by group
      _ = L.zz i * h := by rw [e]
  · intro hV
    refine Equiv.ext fun i => ?_
    have e : (h : G) * L.zz i * (h : G)⁻¹ = L.zz i := by
      rw [hc.commute_V hV (subset_closure (L.zz_mem i)), mul_inv_cancel_right]
    rw [L.conj_zz] at e
    rw [Equiv.Perm.one_apply]
    exact L.zz_injective e

theorem ker_σ (hc : ConfHyp S H) : L.σ.ker = (closure (S.zConj H)).subgroupOf H := by
  ext h
  rw [MonoidHom.mem_ker, mem_subgroupOf, L.σ_eq_one_iff hc]

end Label

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem exists_label (hc : ConfHyp S H) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    ∃ L : Label S H, L.zz 1 = p := by
  have hcard : Nat.card (S.zConj H) = 5 := by rw [Nat.card_coe_set_eq, hc.ncard_zConj]
  set Z : S.zConj H := ⟨S.z, self_mem_conjIn _ _⟩
  set P : S.zConj H := ⟨p, hp⟩
  have hPZ : P ≠ Z := fun h => hpz (congrArg Subtype.val h)
  set e₀ := Finite.equivFinOfCardEq hcard
  let e₁ := e₀.trans (Equiv.swap (e₀ Z) 0)
  have he₁Z : e₁ Z = 0 := by simp [e₁]
  have he₁P : e₁ P ≠ 0 := by
    rw [← he₁Z]
    exact e₁.injective.ne hPZ
  let e₂ := e₁.trans (Equiv.swap (e₁ P) 1)
  have he₂Z : e₂ Z = 0 := by
    change Equiv.swap (e₁ P) 1 (e₁ Z) = 0
    rw [he₁Z]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm he₁P) (by decide)
  have he₂P : e₂ P = 1 := by
    change Equiv.swap (e₁ P) 1 (e₁ P) = 1
    exact Equiv.swap_apply_left _ _
  refine ⟨⟨e₂.symm, ?_⟩, ?_⟩
  · rw [show e₂.symm 0 = Z from e₂.symm_apply_eq.mpr he₂Z.symm]
  · change ((e₂.symm 1 : S.zConj H) : G) = p
    rw [show e₂.symm 1 = P from e₂.symm_apply_eq.mpr he₂P.symm]

theorem card_H (hc : ConfHyp S H) : Nat.card H = 960 := by
  obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨L, -⟩ := hc.exists_label hp hpz
  have h1 := Subgroup.card_ker_mul_card_range L.σ
  rw [L.ker_σ hc, L.range_σ hc.isAFive, card_alternatingGroup_five,
    Nat.card_congr (subgroupOfEquivOfLe hc.V_le).toEquiv, hc.card_V] at h1
  omega

theorem card_inf_M (hc : ConfHyp S H) : Nat.card ↥(H ⊓ S.M) = 192 := by
  have h1 := Setting.card_eq_relIndex_mul H S.M
  rw [Setting.relIndex_centralizer_eq_ncard] at h1
  change Nat.card H = (S.zConj H).ncard * _ at h1
  rw [hc.ncard_zConj, hc.card_H] at h1
  omega

theorem card_M_inf (hc : ConfHyp S H) : Nat.card ↥(S.M ⊓ H) = 192 := by
  rw [inf_comm]
  exact hc.card_inf_M

end ConfHyp

end AS62

end CFSG.LargeExtraspecial

module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2GL
public import CFSG.RankThree.Classical.SteinbergBJGL3InvolutionConjugacy

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup

open GL32Aux in
theorem isConj_of_orderOf_two_mulAut {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) {a b : MulAut V} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  classical
  let _ : CommGroup V := commGroupOfMulSelf h2
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (two_nsmul_eq_zero h2)
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive V) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = 8 from hcard] at h
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    exact (Nat.pow_right_injective (le_refl 2) (h8.trans h)).symm
  let L : MulAut V → (Additive V ≃ₗ[ZMod 2] Additive V) := fun f =>
    { (MulEquiv.toAdditive (G := V) (H := V) f) with
      map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive (G := V) (H := V) f) c x }
  let M : (Additive V ≃ₗ[ZMod 2] Additive V) → MulAut V := fun g =>
    MulEquiv.toAdditive.symm g.toAddEquiv
  have hLM : ∀ g, L (M g) = g := fun g => LinearEquiv.ext fun x => rfl
  have hML : ∀ f, M (L f) = f := fun f => MulEquiv.ext fun x => rfl
  have hLmul : ∀ f g, L (f * g) = L f * L g := fun f g => LinearEquiv.ext fun x => rfl
  have hMmul : ∀ f g, M (f * g) = M f * M g := fun f g => MulEquiv.ext fun x => rfl
  have hLord : ∀ f : MulAut V, orderOf (L f) = orderOf f := fun f => by
    let φ : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
      { toFun := L, map_one' := LinearEquiv.ext fun x => rfl, map_mul' := hLmul }
    exact orderOf_injective φ (fun x y hxy => (hML x).symm.trans ((congrArg M hxy).trans (hML y))) f
  have ha' : orderOf (L a) = 2 := by rw [hLord]; exact ha
  have hb' : orderOf (L b) = 2 := by rw [hLord]; exact hb
  obtain ⟨c, hc⟩ := isConj_iff.1
    ((RankThree.Classical.GL3.gl3_two_involution_conjugacy hfin).2.2 (L a) (L b) ha' hb')
  refine isConj_iff.2 ⟨M c, ?_⟩
  have := congrArg M hc
  rw [hMmul, hMmul, hML, hML] at this
  have hMi : M c⁻¹ = (M c)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hMmul, inv_mul_cancel]
    exact hML 1
  rw [hMi] at this
  exact this

theorem eq_of_abelian_relIndex_two {G : Type*} [Group G] [Finite G] {P B B' V : Subgroup G}
    (hB : B ≤ P) (hB' : B' ≤ P) (hBi : B.relIndex P = 2) (hB'i : B'.relIndex P = 2)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x)
    (hB64 : 64 ≤ Nat.card B) (hV : Nat.card V = 8)
    (hZ : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ V) : B' = B := by
  by_contra hne
  have hnle : ¬ B' ≤ B := by
    intro h
    have h1 : B'.relIndex B * B.relIndex P = B'.relIndex P :=
      relIndex_mul_relIndex B' B P h hB
    rw [hBi, hB'i] at h1
    have h2 : B'.relIndex B = 1 := by omega
    exact hne (le_antisymm h (relIndex_eq_one.mp h2))
  have hP : P ≤ B ⊔ B' := by
    have h1 : B.relIndex (B ⊔ B') * (B ⊔ B').relIndex P = B.relIndex P :=
      relIndex_mul_relIndex B (B ⊔ B') P le_sup_left (sup_le hB hB')
    rw [hBi] at h1
    have h2 : B.relIndex (B ⊔ B') ≠ 1 := fun h =>
      hnle (le_trans le_sup_right (relIndex_eq_one.mp h))
    have h3 : (B ⊔ B').relIndex P ≤ 2 := Nat.le_of_dvd Nat.two_pos (Dvd.intro_left _ h1)
    have h5 : (B ⊔ B').relIndex P = 1 := by
      generalize (B ⊔ B').relIndex P = b at h1 h3 ⊢
      generalize B.relIndex (B ⊔ B') = a at h1 h2
      have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hb with rfl | rfl | rfl <;> omega
    exact relIndex_eq_one.mp h5
  have hcent : B' ⊓ B ≤ V := by
    intro x hx
    refine hZ x (hB' hx.1) fun y hy => ?_
    have hle : B ⊔ B' ≤ Subgroup.centralizer {x} := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro h rfl
        exact hBab _ hx.2 _ hz
      · rw [Subgroup.mem_centralizer_iff]
        rintro h rfl
        exact hB'ab _ hx.1 _ hz
    exact Subgroup.mem_centralizer_iff.mp (hle (hP hy)) x rfl
  have h1 : (B' ⊓ B).relIndex P ≤ B'.relIndex P * B.relIndex P := relIndex_inf_le
  have h2 : (B' ⊓ B).relIndex B * B.relIndex P = (B' ⊓ B).relIndex P :=
    relIndex_mul_relIndex (B' ⊓ B) B P inf_le_right hB
  have h3 : B'.relIndex B * Nat.card (B' ⊓ B :) = Nat.card B := relIndex_mul_card B' B
  have h4 : Nat.card (B' ⊓ B :) ≤ 8 := by
    have := Subgroup.card_le_of_le hcent
    rwa [hV] at this
  have h5 : (B' ⊓ B).relIndex B = B'.relIndex B := inf_relIndex_right B' B
  rw [hBi, hB'i] at h1
  rw [hBi, h5] at h2
  have h6 : B'.relIndex B ≤ 2 := by omega
  have h7 := Nat.mul_le_mul h6 h4
  omega

theorem exists_hom_zmod_two {E : Type} [Group E] (h2 : ∀ e : E, e * e = 1) {x : E} (hx : x ≠ 1) :
    ∃ θ : E →* Multiplicative (ZMod 2), θ x ≠ 1 := by
  classical
  let _ : CommGroup E := GL32Aux.commGroupOfMulSelf h2
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (GL32Aux.two_nsmul_eq_zero h2)
  have hx' : Additive.ofMul x ≠ 0 := fun h => hx (by simpa using h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx'
  refine ⟨AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom, ?_⟩
  intro h
  have h1 : f (Additive.ofMul x) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  rw [hf] at h1
  exact one_ne_zero h1

theorem no_fixed_of_orderOf_seven {V : Type} [Group V] (hcard : Nat.card V = 8) {c : MulAut V}
    (hc : orderOf c = 7) {v : V} (hv : v ≠ 1) (hcv : c v = v) : False := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨v₀, hv₀⟩ := GL32Aux.exists_cover_of_orderOf_seven hcard hc
  obtain ⟨k, hk⟩ := hv₀ v hv
  have hfix : c v₀ = v₀ := by
    have h1 : c ((c ^ k) v₀) = (c ^ k) v₀ := by rw [hk]; exact hcv
    have h2 : (c ^ k) (c v₀) = c ((c ^ k) v₀) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
    exact (c ^ k).injective (h2.trans h1)
  have hall : ∀ j : ℕ, (c ^ j) v₀ = v₀ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  have hlt : 2 < Nat.card V := by omega
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : V, a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
    have h3 : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      have : Fintype V := Fintype.ofFinite V
      exact Fintype.two_lt_card_iff.1 (by rwa [← Nat.card_eq_fintype_card])
    obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
    by_cases h1 : a = 1
    · exact ⟨b, c, hbc, fun h => hab (h1.trans h.symm), fun h => hac (h1.trans h.symm)⟩
    · by_cases h2 : b = 1
      · exact ⟨a, c, hac, h1, fun h => hbc (h2.trans h.symm)⟩
      · exact ⟨a, b, hab, h1, h2⟩
  obtain ⟨ja, hja⟩ := hv₀ a ha
  obtain ⟨jb, hjb⟩ := hv₀ b hb
  rw [hall] at hja hjb
  exact hab (hja.symm.trans hjb)

theorem mul_inv_mem_of_relIndex_two {G : Type*} [Group G] {W P : Subgroup G}
    (h : W.relIndex P = 2) {a b : G} (ha : a ∈ P) (hb : b ∈ P) (haW : a ∉ W) (hbW : b ∉ W) :
    a * b⁻¹ ∈ W := by
  have h2 : (W.subgroupOf P).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : P)) (b := (⟨b, hb⟩ : P)⁻¹)).2
  have h3 : (⟨a, ha⟩ : P) * (⟨b, hb⟩ : P)⁻¹ ∈ W.subgroupOf P := by
    apply this
    constructor
    · intro h4
      exact absurd (mem_subgroupOf.1 h4) haW
    · intro h4
      exact absurd (mem_subgroupOf.1 (by simpa using h4)) hbW
  exact mem_subgroupOf.1 h3

theorem exists_pow_orderOf_two {G : Type*} [Group G] {a : G} (ha : a ≠ 1)
    (h2 : ∃ j : ℕ, orderOf a = 2 ^ j) : ∃ k : ℕ, orderOf (a ^ k) = 2 := by
  obtain ⟨j, hj⟩ := h2
  have hj1 : 1 ≤ j := by
    by_contra hlt
    have : j = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hj
    exact ha hj
  refine ⟨2 ^ (j - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega)), hj,
    Nat.pow_div (by omega) (by norm_num)]
  have : j - (j - 1) = 1 := by omega
  rw [this]

end CFSG.OddStandard.ChengHeld.Excl2

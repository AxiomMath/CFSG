module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bDef
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private lemma fzl_zpowers_eq_one_or_eq_of_card_two {G : Type*} [Group G] {a n : G}
    (hcard : Nat.card (Subgroup.zpowers a) = 2) (ha1 : a ≠ 1)
    (hn : n ∈ Subgroup.zpowers a) (hn1 : n ≠ 1) : n = a := by
  by_contra hna
  haveI : Finite (Subgroup.zpowers a) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let g : Fin 3 → Subgroup.zpowers a :=
    ![⟨1, (Subgroup.zpowers a).one_mem⟩, ⟨a, Subgroup.mem_zpowers a⟩, ⟨n, hn⟩]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have hle : Nat.card (Fin 3) ≤ Nat.card (Subgroup.zpowers a) :=
    Nat.card_le_card_of_injective g hg
  simp only [Nat.card_fin] at hle
  omega

theorem fzl_assemble (h21b : Fz21bFix) {N X : Type} [Group N] [CommGroup X]
    (φ : N →* MulAut X) (hX : Nonempty (X ≃* FzZ244)) (ψ : N →* Equiv.Perm (Fin 4))
    (hψ : Function.Surjective ψ) (hφψ : φ.ker ≤ ψ.ker)
    (hK : ∀ k ∈ ψ.ker, (∀ x : X, φ k x = x) ∨ ∀ x : X, φ k x = x⁻¹)
    (hι : ∃ k ∈ ψ.ker, ∀ x : X, φ k x = x⁻¹) {ρ lam : N}
    (hρ3 : ρ ^ 3 ∈ φ.ker) (hρ1 : ρ ∉ φ.ker) (hlam2 : lam ^ 2 ∈ φ.ker) (hlam1 : lam ∉ φ.ker)
    (hlr : lam * ρ * lam⁻¹ * ρ ∈ φ.ker) :
    ∃ f : N →* FzZ2xSigma4, Function.Surjective f ∧ f.ker = φ.ker := by
  classical
  obtain ⟨eX⟩ := hX
  obtain ⟨ι, hιker, hιinv⟩ := hι
  let invAut : MulAut X :=
    { toFun := fun x => x⁻¹
      invFun := fun x => x⁻¹
      left_inv := fun x => inv_inv x
      right_inv := fun x => inv_inv x
      map_mul' := fun x y => mul_inv x y }
  have hinvAut_apply : ∀ x : X, invAut x = x⁻¹ := fun x => rfl
  have hinvAut_sq : invAut * invAut = 1 := by
    apply MulEquiv.ext
    intro x
    change invAut (invAut x) = x
    rw [hinvAut_apply x, hinvAut_apply x⁻¹]
    exact inv_inv x
  let z : FzZ244 := Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 4), (0 : ZMod 4))
  have hz2 : z ^ 2 ≠ 1 := by decide
  have hx4_sq : (eX.symm z) ^ 2 ≠ 1 := by
    intro h
    exact hz2 (by
      have h' := congrArg eX h
      simpa using h')
  have hinvAut_ne_one : invAut ≠ 1 := by
    intro h
    have h' : (eX.symm z)⁻¹ = eX.symm z := by
      have h2 := congrArg (fun f : MulAut X => f (eX.symm z)) h
      simpa [invAut] using h2
    have hsq : (eX.symm z) ^ 2 = 1 := by
      rw [pow_two]
      exact (inv_eq_iff_mul_eq_one).mp h'
    exact hx4_sq hsq
  have hinvAut_center : invAut ∈ Subgroup.center (MulAut X) := by
    rw [Subgroup.mem_center_iff]
    intro f
    apply MulEquiv.ext
    intro x
    change f (invAut x) = invAut (f x)
    rw [hinvAut_apply x, hinvAut_apply (f x)]
    exact map_inv f x
  have hφι : φ ι = invAut :=
    MulEquiv.ext (fun x => by rw [hιinv x, hinvAut_apply x])
  have hmem : invAut ∈ φ.range := ⟨ι, hφι⟩
  let a : φ.range := ⟨invAut, hmem⟩
  let N₀ : Subgroup φ.range := Subgroup.zpowers a
  have ha_ne_one : a ≠ 1 := fun h => hinvAut_ne_one (Subtype.ext_iff.mp h)
  have hgen_center : a ∈ Subgroup.center φ.range := by
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hinvAut_center (n : MulAut X)
  have hN₀_center : N₀ ≤ Subgroup.center φ.range := by
    change Subgroup.zpowers a ≤ Subgroup.center φ.range
    exact Subgroup.zpowers_le.mpr hgen_center
  haveI : N₀.Normal := Subgroup.normal_of_le_center hN₀_center
  have hN₀_card : Nat.card N₀ = 2 := by
    change Nat.card (Subgroup.zpowers a) = 2
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · apply Subtype.ext
      change invAut ^ 2 = (1 : MulAut X)
      rw [pow_two]
      exact hinvAut_sq
    · intro h
      exact hinvAut_ne_one (Subtype.ext_iff.mp h)
  let e : N ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
  let ψb : φ.range →* Equiv.Perm (Fin 4) :=
    (QuotientGroup.lift φ.ker ψ hφψ).comp e.symm.toMonoidHom
  have he_mk : ∀ n : N, e (QuotientGroup.mk' φ.ker n) = φ.rangeRestrict n := fun _ => rfl
  have hψb_apply : ∀ n : N, ψb (φ.rangeRestrict n) = ψ n := by
    intro n
    have h1 : e.symm (φ.rangeRestrict n) = QuotientGroup.mk' φ.ker n := by
      rw [← he_mk n, MulEquiv.symm_apply_apply]
    change (QuotientGroup.lift φ.ker ψ hφψ) (e.symm (φ.rangeRestrict n)) = ψ n
    rw [h1]
    rfl
  have hψb_surj : Function.Surjective ψb := by
    intro σ
    obtain ⟨n, hn⟩ := hψ σ
    exact ⟨φ.rangeRestrict n, by rw [hψb_apply n, hn]⟩
  have hN₀_le : N₀ ≤ ψb.ker := by
    have ha_eq : a = φ.rangeRestrict ι := by
      apply Subtype.ext
      change invAut = φ ι
      rw [hφι]
    have ha_ker : a ∈ ψb.ker := by
      rw [MonoidHom.mem_ker, ha_eq, hψb_apply ι, MonoidHom.mem_ker.mp hιker]
    change Subgroup.zpowers a ≤ ψb.ker
    exact Subgroup.zpowers_le.mpr ha_ker
  have hker_le : ψb.ker ≤ N₀ := by
    intro n' hn'
    obtain ⟨n, rfl⟩ := φ.rangeRestrict_surjective n'
    have hnker : n ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h := MonoidHom.mem_ker.mp hn'
      rwa [hψb_apply n] at h
    rcases hK n hnker with hfix | hinv
    · have h1 : φ.rangeRestrict n = 1 := by
        apply Subtype.ext
        change φ n = (1 : MulAut X)
        apply MulEquiv.ext
        intro x
        rw [hfix x]
        rfl
      rw [h1]
      exact N₀.one_mem
    · have hφn : φ n = invAut :=
        MulEquiv.ext (fun x => by rw [hinv x, hinvAut_apply x])
      have ha : φ.rangeRestrict n = a := by
        apply Subtype.ext
        change φ n = invAut
        exact hφn
      rw [ha]
      exact Subgroup.mem_zpowers a
  have hker : ψb.ker = N₀ := le_antisymm hker_le hN₀_le
  have hq : Nonempty (φ.range ⧸ N₀ ≃* FzSigma4) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψb hψb_surj)⟩
  have hN₀_inv : ∀ n ∈ N₀, n ≠ 1 → ∀ x : X, φ.range.subtype n x = x⁻¹ := by
    intro n hn hn1 x
    have hna : n = a :=
      fzl_zpowers_eq_one_or_eq_of_card_two
        (show Nat.card (Subgroup.zpowers a) = 2 from hN₀_card)
        ha_ne_one (show n ∈ Subgroup.zpowers a from hn) hn1
    rw [hna]
    change invAut x = x⁻¹
    exact hinvAut_apply x
  have hρ3' : (φ.rangeRestrict ρ) ^ 3 = 1 := by
    apply Subtype.ext
    change (φ ρ) ^ 3 = (1 : MulAut X)
    simpa using MonoidHom.mem_ker.mp hρ3
  have hρ1' : φ.rangeRestrict ρ ≠ 1 := by
    intro h
    exact hρ1 (MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp h))
  have hlam2' : (φ.rangeRestrict lam) ^ 2 = 1 := by
    apply Subtype.ext
    change (φ lam) ^ 2 = (1 : MulAut X)
    simpa using MonoidHom.mem_ker.mp hlam2
  have hlam1' : φ.rangeRestrict lam ≠ 1 := by
    intro h
    exact hlam1 (MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp h))
  have horderρ : orderOf (φ.rangeRestrict ρ) = 3 := orderOf_eq_prime hρ3' hρ1'
  have horderlam : orderOf (φ.rangeRestrict lam) = 2 := orderOf_eq_prime hlam2' hlam1'
  have hderived : φ lam * φ ρ * (φ lam)⁻¹ = (φ ρ)⁻¹ := by
    have hcomp : φ lam * φ ρ * (φ lam)⁻¹ * φ ρ = 1 := by
      have h := MonoidHom.mem_ker.mp hlr
      simpa [map_mul, map_inv] using h
    exact mul_eq_one_iff_eq_inv.mp hcomp
  have hrel' : φ.rangeRestrict lam * φ.rangeRestrict ρ * (φ.rangeRestrict lam)⁻¹
      = (φ.rangeRestrict ρ)⁻¹ := by
    apply Subtype.ext
    change φ lam * φ ρ * (φ lam)⁻¹ = (φ ρ)⁻¹
    exact hderived
  obtain ⟨eN⟩ := h21b X φ.range (φ.range.subtype) N₀ (φ.rangeRestrict ρ) (φ.rangeRestrict lam)
    ⟨eX⟩ (fun u v h => Subtype.ext h) hN₀_card hN₀_inv hq horderρ horderlam hrel'
  refine ⟨eN.toMonoidHom.comp φ.rangeRestrict, ?_, ?_⟩
  · exact eN.surjective.comp φ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective φ.rangeRestrict eN.toMonoidHom eN.injective,
      MonoidHom.ker_rangeRestrict]

end CFSG.OddStandard.SmallF3.FritzII

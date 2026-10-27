module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {K : Type} [Group K] [Finite K]

theorem gamma_card_dvd_of_le_normalizer {P L : Subgroup K} (hp : (Nat.card P).Prime)
    (hL : L ≤ Subgroup.normalizer (P : Set K)) :
    Nat.card L ∣ Nat.card ↥(L ⊓ Subgroup.centralizer (P : Set K)) * (Nat.card P - 1) := by
  let f : L →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hL)
  have hf : ∀ (l : L) (x : P), ((f l x : P) : K) = l * x * (l : K)⁻¹ := fun l x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hL l) x
  have hker : f.ker = (L ⊓ Subgroup.centralizer (P : Set K)).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun z : P => (z : K)) (DFunLike.congr_fun hx ⟨y, hy⟩)
      rw [hf, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      simpa using h.symm
    · rintro ⟨_, hxC⟩
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hf, MulAut.one_apply]
      have hy := Subgroup.mem_centralizer_iff.mp hxC (y : K) y.2
      rw [← hy]
      group
  have hcard_ker : Nat.card f.ker = Nat.card ↥(L ⊓ Subgroup.centralizer (P : Set K)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : L ⊓ Subgroup.centralizer (P : Set K) ≤ L)).toEquiv
  have hcard : Nat.card L = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hrange : Nat.card f.range ∣ Nat.card P - 1 := by
    haveI : Fact (Nat.card P).Prime := ⟨hp⟩
    haveI : IsCyclic P := isCyclic_of_prime_card (p := Nat.card P) rfl
    have h1 : Nat.card f.range ∣ Nat.card (MulAut P) := Subgroup.card_subgroup_dvd_card _
    rwa [IsCyclic.card_mulAut, Nat.totient_prime hp] at h1
  rw [hcard, hcard_ker]
  exact mul_dvd_mul_left _ hrange

theorem gamma_card_modEq_of_le_normalizer {q : ℕ} [Fact q.Prime] {P R : Subgroup K}
    (hR : IsPGroup q R) (hRP : R ≤ Subgroup.normalizer (P : Set K)) :
    Nat.card P ≡ Nat.card ↥(P ⊓ Subgroup.centralizer (R : Set K)) [MOD q] := by
  let f : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  letI : MulAction R P := MulAction.compHom P f
  have hsmul : ∀ (r : R) (x : P), ((r • x : P) : K) = r * x * (r : K)⁻¹ := by
    intro r x
    change ((f r x : P) : K) = r * x * (r : K)⁻¹
    exact Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  let e : MulAction.fixedPoints R P ≃ ↥(P ⊓ Subgroup.centralizer (R : Set K)) :=
    { toFun := fun p => ⟨p.1.1, Subgroup.mem_inf.mpr ⟨p.1.2, by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h := congrArg (fun z : P => (z : K)) (p.2 ⟨r, hr⟩)
        rw [hsmul, mul_inv_eq_iff_eq_mul] at h
        simpa using h⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        intro r
        apply Subtype.ext
        rw [hsmul]
        have hx := Subgroup.mem_centralizer_iff.mp x.2.2 (r : K) r.2
        rw [hx]
        group⟩
      left_inv := fun p => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have hcard : Nat.card (MulAction.fixedPoints R P) =
      Nat.card ↥(P ⊓ Subgroup.centralizer (R : Set K)) :=
    Nat.card_congr e
  have h := hR.card_modEq_card_fixedPoints P
  rwa [hcard] at h

end CFSG.EvenSporadicStandard.HNRecog.Section3

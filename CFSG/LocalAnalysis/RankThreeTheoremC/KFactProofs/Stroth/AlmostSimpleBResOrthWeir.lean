module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Module QuadraticMap
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalGroups.Orthogonal
open CFSG.GroupTheory.WeirSylow (IsPlusType IsMinusType)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega

section Pj

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}

theorem exists_pj (hQ0 : ⇑Q = Q₀) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ pj : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) →*
        StatedProj (StatedOmega Q₀),
      Function.Surjective pj ∧ (∀ x, pj x = 1 → x ^ 2 = 1) ∧
        ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
          g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  classical
  obtain ⟨-, -, -, -, -, hsq', -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun g =>
    mem_commutator_of_coe_mem (by simpa using hsq' (g : (ι → F) ≃ₗ[F] (ι → F)) g.2)
  haveI : Nontrivial (ι → F) := by
    obtain ⟨T, hT3, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    have := Submodule.finrank_le T
    omega
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO'
  let Θ₁ : ↥O →* GL ι F := (toLinEquiv ι F).symm.toMonoidHom.comp O.subtype
  have hΘ₁ : ∀ x : ↥O, toLinEquiv ι F (Θ₁ x) = (x : (ι → F) ≃ₗ[F] (ι → F)) := fun x =>
    MulEquiv.apply_symm_apply _ _
  have hmemΩ : ∀ A : GL ι F, A ∈ StatedOmega Q₀ ↔ toLinEquiv ι F A ∈ ⁅O, O⁆ := fun A => by
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    rfl
  have hΘ₁Ω : ∀ x ∈ commutator ↥O, Θ₁ x ∈ StatedOmega Q₀ := by
    intro x hx
    rw [hmemΩ, hΘ₁]
    have : (x : (ι → F) ≃ₗ[F] (ι → F)) ∈ (commutator ↥O).map O.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at this
  let Θ₂ : ↥(commutator ↥O) →* ↥(StatedOmega Q₀) :=
    (Θ₁.comp (commutator ↥O).subtype).codRestrict (StatedOmega Q₀) (fun x => hΘ₁Ω x x.2)
  let pj : ↥(commutator ↥O) →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀))).comp Θ₂
  have hker : ∀ x : ↥(commutator ↥O), pj x = 1 → x ^ 2 = 1 := by
    intro x hx
    have h1 : Θ₂ x ∈ (StatedScalars ι F).subgroupOf (StatedOmega Q₀) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : ↥O) : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) := by
      have := (mem_statedScalars_iff _).1 h1
      rwa [show ((Θ₂ x : ↥(StatedOmega Q₀)) : GL ι F) = Θ₁ (x : ↥O) from rfl, hΘ₁] at this
    obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc, hcv⟩ :=
      CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars h2 (x : ↥O).2 ha₀
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply, hcv v, map_smul, hcv v, smul_smul, ← _root_.sq, hc,
      one_smul]
    rfl
  have hsurj : Function.Surjective pj := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : toLinEquiv ι F (z : GL ι F) ∈ ⁅O, O⁆ := (hmemΩ _).1 z.2
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : Θ₂ ⟨x, hx⟩ = z := Subtype.ext (by
      show Θ₁ x = (z : GL ι F)
      apply (toLinEquiv ι F).injective
      rw [hΘ₁]
      exact hxz)
    show QuotientGroup.mk' _ (Θ₂ ⟨x, hx⟩) = _
    rw [h1]
    rfl
  exact ⟨pj, hsurj, hker, hsq⟩

end Pj

section Weir

open Classical in
@[expose] noncomputable def orthN (p n : ℕ) (F : Type) [Finite F] (ε : ℤ) : ℕ :=
  if (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + ε then n - 1 else n

theorem sylowIso_orthogonal_even {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card F) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n : ℕ} (hn : 1 ≤ n) (hdim : finrank F V = 2 * n)
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q)) :
    SylowIso p ↥(TauCeti.QuadraticMap.orthogonalGroup Q) (StatedSp (orthN p n F ε) F) := by
  classical
  haveI := Fintype.ofFinite F
  intro P
  have hp1 : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpK' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨c1, c2, c3⟩ := CFSG.GroupTheory.WeirSylow.sylow_orthogonal_even hp1 hpK' hn hdim Q hQ hε P
  rw [← Nat.card_eq_fintype_card] at c1 c2 c3
  by_cases hc : (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + ε
  · have hN : orthN p n F ε = n - 1 := by
      unfold orthN
      rw [if_pos hc]
    rw [hN]
    exact c2 (c3.resolve_left (not_not.2 hc))
  · have hN : orthN p n F ε = n := by
      unfold orthN
      rw [if_neg hc]
    rw [hN]
    exact c1 hc

theorem sylowIso_projOmega {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card F) (hQ0 : ⇑Q = Q₀) {n : ℕ} (hn : 1 ≤ n) (hdim : finrank F (ι → F) = 2 * n)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q)) :
    SylowIso p (StatedProj (StatedOmega Q₀)) (StatedSp (orthN p n F ε) F) := by
  obtain ⟨pj, hsurj, hker, hsq⟩ := exists_pj hQ0 hQ hT
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
    haveI : Finite (ι → F) := inferInstance
    exact Finite.of_injective (fun g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
      ((g : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) → (ι → F)))
      (fun a b h => Subtype.ext (LinearEquiv.coe_injective (by simpa using h)))
  exact sylowIso_of_cover hp2 hsq pj hsurj hker
    (sylowIso_orthogonal_even hp2 hpK hn hdim hQ hε)

theorem orth_pair_transfer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {ε : ℤ}
    {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hdim : finrank F (ι → F) = 2 * n) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q))
    {F' : Type} [Field F'] [Finite F'] [CharP F' 2] {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {Q' : QuadraticForm F' (ι' → F')} {Q₀' : (ι' → F') → F'} (hQ0' : ⇑Q' = Q₀')
    (hdim' : finrank F' (ι' → F') = 2 * n) (hQ' : (polarBilin Q').Nondegenerate)
    (hT' : ∃ T : Submodule F' (ι' → F'), finrank F' T = 3 ∧ ∀ x ∈ T, Q' x = 0)
    (hε' : (ε = 1 ∧ IsPlusType Q') ∨ (ε = -1 ∧ IsMinusType Q'))
    (hpF : ¬ p ∣ Nat.card F) (hcong : (Nat.card F : ZMod p) = (Nat.card F' : ZMod p))
    {E : Subgroup (StatedProj (StatedOmega Q₀))} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) :
    ∃ y₁ y₂ : StatedProj (StatedOmega Q₀'), Commute y₁ y₂ ∧ y₁ ^ p = 1 ∧ y₂ ^ p = 1 ∧
      ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF' : ¬ p ∣ Nat.card F' := by
    intro h
    apply hpF
    rw [← ZMod.natCast_eq_zero_iff, hcong, ZMod.natCast_eq_zero_iff]
    exact h
  have hN : orthN p n F ε = orthN p n F' ε := by
    unfold orthN
    have hiff : (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + ε ↔ (p : ℤ) ∣ (Nat.card F' : ℤ) ^ n + ε := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcong]
    simp only [hiff]
  have hS := sylowIso_projOmega hp2 hpF hQ0 hn hdim hQ hT hε
  have hS' := sylowIso_projOmega hp2 hpF' hQ0' hn hdim' hQ' hT' hε'
  have h2e := le_of_elemAbelian_sylowSp hp hp2 hpF hS hE hEc
  rw [hN] at hS h2e
  rw [hcong] at h2e
  exact exists_pair_of_sylowIso hp hp2 hpF' h2e hS'

end Weir

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

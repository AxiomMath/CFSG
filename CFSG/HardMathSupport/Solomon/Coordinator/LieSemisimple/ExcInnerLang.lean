module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerEmbed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem perfectInLayer_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {C : Type} [Group C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    PerfectInLayer β := by
  refine perfectInLayer_of_embedding ι hι β (rootDiagUnit τ a) hβ fun P hP hperf => ?_
  rw [hrange] at hP ⊢
  exact perfect_le_glaLayer_langCentralizer S hT hap h1 hTame P hP hperf

theorem perfectInLayer_of_langSetup_of_prime {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    PerfectInLayer β := by
  refine perfectInLayer_of_embedding ι hι β (rootDiagUnit τ a) hβ fun P hP hperf => ?_
  rw [hrange] at hP ⊢
  exact perfect_le_glaLayer_langCentralizer_of_prime S hp hT hap h1 hTame P hP hperf

theorem monomialToralAt_of_not_dvd {τ : Tag} {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (WeylGroup τ)) : MonomialToralAt τ p := by
  unfold MonomialToralAt
  intro L _ _ _ _ _ _ n hn _ hpow
  have hw : weylQuotientHom τ L ⟨n, hn⟩ = 1 := by
    have hord : orderOf (weylQuotientHom τ L ⟨n, hn⟩) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    have hcard := orderOf_dvd_natCard (weylQuotientHom τ L ⟨n, hn⟩)
    rcases (Nat.dvd_prime hp).1 hord with h0 | h0
    · exact orderOf_eq_one_iff.1 h0
    · rw [h0] at hcard
      exact absurd hcard h
  exact ⟨1, one_mem _, by simpa using mem_torusGroup_of_weylQuotientHom_eq_one hn hw⟩

theorem exists_conj_torusGroup_of_pow_eq_one {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hℓp : ℓ ≠ p) (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L) (hxp : x ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, g⁻¹ * x * g ∈ torusGroup τ L := by
  have hB : Subgroup.zpowers x ≤ adjointGroup τ L := Subgroup.zpowers_le.2 hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hxp⟩
  have hBfin : (Subgroup.zpowers x : Set (ModGL τ L)).Finite :=
    Set.finite_coe_iff.1 (finite_zpowers.2 hfin)
  haveI : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ y ∈ Subgroup.zpowers x, y ^ p = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_monomial_bar hℓp halg hB hBfin hexp
  have hmonx : c * x * c⁻¹ ∈ monomialSubgroup τ L := hcB x (Subgroup.mem_zpowers x)
  have hpow : (c * x * c⁻¹) ^ p = 1 := by
    rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  have hL : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ]
    exact hℓp
  obtain ⟨g', hg', hg't⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hL hmonx hpow
  refine ⟨(g' * c)⁻¹, inv_mem (mul_mem hg' hc), ?_⟩
  rw [inv_inv]
  have e : g' * c * x * (g' * c)⁻¹ = g' * (c * x * c⁻¹) * g'⁻¹ := by group
  rw [e]
  exact hg't

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

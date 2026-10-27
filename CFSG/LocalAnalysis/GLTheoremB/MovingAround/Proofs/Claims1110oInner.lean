module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem two_pow_dvd_d4Two {n : ℕ} (h : 2 ^ n ∣ 174182400) : n ≤ 12 := by
  have h1 : 2 ^ n ∣ 2 ^ 12 * 42525 := by
    simpa using h
  have h2 : 2 ^ n ∣ 2 ^ 12 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 42525)) h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2

section CardNe


theorem card_centerQuotient_ne_of_uniEmbed (hU : UniEmbed) {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {R : Type} [Group R] (f : ↥(componentRootSpan K χ i) →* R)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan K χ i))
    (hperf : Group.IsPerfect ↥(componentRootSpan K χ i))
    (hbig : 4096 < Nat.card K ^ (posRoots (componentRoots χ i)).ncard) :
    Nat.card (R ⧸ Subgroup.center R) ≠ 174182400 := by
  classical
  intro hcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVp, hVcard, hVZ⟩ := hU τ χ i K 2
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf f hf hker
  let g : ↥V →* ↥(componentRootSpan K χ i) ⧸
      Subgroup.center ↥(componentRootSpan K χ i) :=
    (QuotientGroup.mk' _).comp V.subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : ↥(componentRootSpan K χ i)) ∈
        Subgroup.center ↥(componentRootSpan K χ i) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : ↥(componentRootSpan K χ i)) ∈
        V ⊓ Subgroup.center ↥(componentRootSpan K χ i) := ⟨x.2, hx'⟩
    rw [hVZ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdvd : Nat.card V ∣ Nat.card (R ⧸ Subgroup.center R) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_injective g hginj
  rw [hcard] at hdvd
  haveI : Finite ↥V := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥V)).1 hVp
  rw [hn] at hdvd
  have hn12 : n ≤ 12 := two_pow_dvd_d4Two hdvd
  have hVle : Nat.card ↥V ≤ 4096 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hn12
      _ = 4096 := by norm_num
  rw [hVcard] at hVle
  omega

end CardNe

section InnerBig


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem inner_big_card_ne (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (D : InnerData S a i) (hbig : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := isPerfect_componentRootSpan_of_big hτ D (by omega)
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  refine card_centerQuotient_ne_of_uniEmbed uniEmbed_holds (rootCharHom a) i
    (fixSubfield D.σ) g hg hgk hperf ?_
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : 13 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  have hK2 : 2 ≤ Nat.card (fixSubfield D.σ) := Finite.one_lt_card
  calc 4096 < 2 ^ 13 := by norm_num
    _ ≤ 2 ^ (posRoots (componentRoots (rootCharHom a) i)).ncard :=
      Nat.pow_le_pow_right (by norm_num) hN
    _ ≤ Nat.card (fixSubfield D.σ) ^
        (posRoots (componentRoots (rootCharHom a) i)).ncard := Nat.pow_le_pow_left hK2 _

theorem inner_big_card_ne_of_kind (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hbig : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  exact inner_big_card_ne hτ D hbig

end InnerBig

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

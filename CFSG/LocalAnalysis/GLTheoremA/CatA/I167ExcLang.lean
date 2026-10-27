module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangMarkU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangMarkT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangRho

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem exc_natCast_ne_zero_alg {K : Type} [Field K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm

private theorem exc_not_dvd_two_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 ^ e := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))


theorem exc_jbar_rational {p : ℕ} (hp : p.Prime) {X J : Subgroup Ω} {x : Ω}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hnt : Nontrivial (PSimple p X)) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω))
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer ({x} : Set Ω)) J) {C : Type} [Group C] [Finite C]
    (θ : PSimple p X ≃* C) (φx : MulAut C) (hindx : LargeEvenInduces θ (indRel p X x) φx)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (SL : LangSetup τ L p₀)
    (hpL : (p : L) ≠ 0) (hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ SL.D.q) {a : Fin τ.rank → Lˣ}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = SL.Γ)
    (hβ : ∀ c, ι (φx c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hTa : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      Nonempty (PSimple p J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) := by
  classical
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  have hJPc : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φx)
      (K155X.l154JImage p X J θ) := K155X.l154_JImage_glaPComponent hp hxp hxN hJ θ φx hindx
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
    SL hp hpL hsmall hTa hap ha1
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer φx :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_langSetup_of_prime
      SL hp ι hι hrange φx hβ hTa hap ha1 hTame
  have hJPcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJPc
    (hPIL _ hJPc.1 (glaPComponent_perfect hJPc))).1
  obtain ⟨i, hqi, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup SL hp ι hι hrange φx hβ
      hTa hap ha1 hTame hJPcomp
  set Ri := rationalComponent SL.ρ SL.Γ (rootCharHom a) i with hRidef
  set JP : Subgroup C := K155X.l154JImage p X J θ with hJPdef
  let eJ : ↥JP ≃* ↥Ri := (JP.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hqJP : CFSG.IsQuasisimple ↥JP := CFSG.IsQuasisimple.of_mulEquiv eJ hqi
  obtain ⟨e₀⟩ := excLang_jbar_equiv hp hX hnt hJ hJX θ ⟨hqJP.1.commutator_eq_top, hqJP.2.1⟩
  exact ⟨i, hqi, ⟨e₀.trans (QuotientGroup.congr (Subgroup.center ↥JP) (Subgroup.center ↥Ri) eJ
    (Subgroup.map_center_eq eJ))⟩⟩


theorem exc_lang_untw {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup Ω} {x : Ω} {k : DefChar.LieFamily}
    (hk : k = .F4 ∨ k = .E6 ∨ k = .E7 ∨ k = .E8) {qc : TauCeti.PrimePower} (hqc : qc.p = 2)
    {hv : (LocalTwo.excIndex k qc).Valid} (hX : CFSG.Open.IsQuasisimple ↥X) (hnt : Nontrivial (PSimple p X))
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex k qc, hv⟩)) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X)
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer ({x} : Set Ω)) J) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (SL : LangSetup (excTag k) L 5)
      (a : Fin (excTag k).rank → Lˣ) (i : KernelComponent (rootCharHom a))
      (w : WeylGroup (excTag k)),
      SL.D.q = qc.card ∧ (∀ γ, IsRoot (excTag k) γ → SL.ρ γ = w • γ) ∧
      rootDiagUnit (excTag k) a ∈ SL.D.torus ∧ (∀ m, a m ^ p = 1) ∧ rootDiagUnit (excTag k) a ≠ 1 ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      Nonempty (PSimple p J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) := by
  classical
  obtain ⟨K, instF, instFin, θ, φx, h, hchar, hKcard, hperf, hhp, hh1, hhL, hφx, hind⟩ :=
    excLang_untw_marking hp hp2 hk hqc hX hcat hxp hxN hcm hinn
  have hτ : excTag k = .G2 ∨ excTag k = .F4 ∨ excTag k = .E6 ∨ excTag k = .E7 ∨ excTag k = .E8 := by
    rcases hk with rfl | rfl | rfl | rfl <;> simp [excTag]
  have hne : excTag k ≠ Tag.G2 := by rcases hk with rfl | rfl | rfl | rfl <;> simp [excTag]
  have hKe : Nat.card K = 2 ^ qc.exponent := by rw [hKcard, TauCeti.PrimePower.card_def, hqc]
  have hpK : ¬ p ∣ Nat.card K := by rw [hKe]; exact exc_not_dvd_two_pow hp hp2
  have h5K : ¬ 5 ∣ Nat.card K := by rw [hKe]; exact exc_not_dvd_two_pow Nat.prime_five (by norm_num)
  have hmon : MonomialToralAt (excTag k) p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2
  obtain ⟨SL, a, ι, hq, ⟨Fr, hFr, hΦ⟩, hTa, hap, ha1, hι, hrange, hβ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inner_untw_of_prime hτ hp hpK
      Nat.prime_five h5K (Or.inl le_rfl) hmon hperf φx h hhL hφx hhp hh1
  haveI : Finite ↥(adjointGroup (excTag k) K) := Finite.of_equiv _ θ.toEquiv
  haveI : CharP K 2 := hchar
  have hFr' : ∀ c, Fr c = c ^ SL.D.q := fun c => by rw [hq]; exact hFr c
  obtain ⟨w, hn⟩ := SL.D.n_weyl
  obtain ⟨i, hqi, hE⟩ := exc_jbar_rational hp hX hnt hxp hxN hJ θ φx hind SL
    (exc_natCast_ne_zero_alg hp hp2)
    (fun hG2 => absurd hG2 hne) ι hι hrange hβ
    hTa hap ha1
  exact ⟨AlgebraicClosure K, inferInstance, inferInstance,
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2, SL, a, i, w,
    hq.trans hKcard, fun γ hγ => SL.rho_eq_smul_of_frob hFr' hΦ hn hγ, hTa, hap, ha1, hqi, hE⟩


theorem exc_lang_twE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup Ω} {x : Ω}
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2) {hv : (LocalTwo.excIndex .twistedE6 qc).Valid}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hnt : Nontrivial (PSimple p X))
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex .twistedE6 qc, hv⟩)) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hcm : ¬ CentMod p X x)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X)
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer ({x} : Set Ω)) J) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (SL : LangSetup Tag.E6 L 5)
      (a : Fin Tag.E6.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (w : WeylGroup Tag.E6),
      SL.D.q = qc.card ∧ (∀ γ, IsRoot Tag.E6 γ → SL.ρ γ = w • permLattice e6Graph γ) ∧
      rootDiagUnit Tag.E6 a ∈ SL.D.torus ∧ (∀ m, a m ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      Nonempty (PSimple p J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) := by
  classical
  obtain ⟨K, instF, instFin, σ, θ, φx, h, hchar, hKcard, hσ, hh, hhp, hh1, hφx, hind⟩ :=
    excLang_twE6_marking hp hp2 hqc hX hcat hxp hxN hcm hinn
  have hK : Nat.card K = (2 ^ qc.exponent) ^ 2 := by rw [hKcard, TauCeti.PrimePower.card_def, hqc]
  have hσ' : ∀ c, σ c = c ^ (2 ^ qc.exponent) := fun c => by
    rw [hσ c, TauCeti.PrimePower.card_def, hqc]
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨SL, a, ι, hq, ⟨Fr, hFr, hΦ⟩, hTa, hap, ha1, hι, hrange, hβ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      Nat.prime_two qc.exponent_pos hK σ hσ' hp hp2 Nat.prime_five (by norm_num) (Or.inl le_rfl) hmon φx h
      hh hφx hhp hh1
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv _ θ.toEquiv
  haveI : CharP K 2 := hchar
  have hq' : SL.D.q = qc.card := by rw [hq, TauCeti.PrimePower.card_def, hqc]
  have hFr' : ∀ c, Fr c = c ^ SL.D.q := fun c => by rw [hq']; rw [TauCeti.PrimePower.card_def, hqc]; exact hFr c
  obtain ⟨w, hw⟩ := excLang_twE6_rho SL hFr' hΦ
  obtain ⟨i, hqi, hE⟩ := exc_jbar_rational hp hX hnt hxp hxN hJ θ φx hind SL
    (exc_natCast_ne_zero_alg hp hp2) (fun hG2 => absurd hG2 (by decide)) ι hι hrange hβ hTa hap ha1
  exact ⟨AlgebraicClosure K, inferInstance, inferInstance,
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2, SL, a, i, w, hq', hw,
    hTa, hap, ha1, hqi, hE⟩


end CFSG.LocalAnalysis.GLTheoremA.I167

end

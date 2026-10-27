module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenMarkProp)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (mem_twistedTorusOf)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley

section Suppliers


theorem l154td4_exists_frobRoot_of_toral_frob {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {e : ℕ} (he : 1 ≤ e) {p : ℕ} (hpq : Nat.Coprime p (2 ^ e)) {u : ModGL τ L}
    (hup : u ^ p = 1) (hfix : entrywiseFrobGL τ L 2 e u = u)
    (hconj : ∃ g ∈ adjointGroup τ L, g⁻¹ * u * g ∈ torusGroup τ L) :
    ∃ (D : LangDatum τ L) (R : FrobRoot D p),
      D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) ∧ D.q = 2 ^ (e * p) ∧
      R.q0 = 2 ^ e ∧ R.Fr0 = iterateFrobenius L 2 e ∧
      u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom ∧
      R.step0 (D.g0⁻¹ * u * D.g0) = D.g0⁻¹ * u * D.g0 ∧
      (∀ y, R.step0 (D.g0⁻¹ * y * D.g0) = D.g0⁻¹ * Units.map (entrywiseHom R.Fr0) y * D.g0) ∧
      ∃ D₀ : LangDatum τ L, D₀.q = R.q0 ∧ ∀ g, D₀.step g = R.step0 g := by
  obtain ⟨D₀, hΦ₀, hq₀, y, hy, hyu⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langDatum_of_toral_untw e he
      hpq hup hfix hconj
  obtain ⟨D, R, hΦ, hq, hg0, hRq0, hRFr0, hRz0⟩ := exists_langDatum_frobRoot_pow p D₀ hΦ₀
  have hstep : ∀ y, R.step0 y = D₀.n * D₀.Φ y * D₀.n⁻¹ := fun y => by
    rw [R.step0_apply, hRz0, hRFr0, hΦ₀]
  have hlang : Units.map (entrywiseHom R.Fr0) D₀.g0 = D₀.g0 * D₀.n := by
    rw [hRFr0, ← hΦ₀]
    exact D₀.lang
  have hyd : y = D₀.g0⁻¹ * u * D₀.g0 := by
    have h' : D₀.g0 * y * D₀.g0⁻¹ = u := hyu
    rw [← h']
    group
  have hyfix : R.step0 y = y := by
    rw [hstep]
    exact (mem_twistedTorusOf.1 hy).2
  refine ⟨D, R, hΦ, hq, hRq0, hRFr0, ⟨y, R.mem_torus_of_step0_eq (mem_twistedTorusOf.1 hy).1 hyfix,
    by rw [hg0]; exact hyu⟩, ?_, fun y' => ?_, D₀, hq₀.trans hRq0.symm, fun g => (hstep g).symm⟩
  · rw [hg0, ← hyd]
    exact hyfix
  · rw [hg0, R.step0_apply, map_mul, map_mul, map_inv, hlang, hRz0]
    group

theorem l154td4_exists_langSetup_frobRoot_untw_of_mon {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (e * p)) (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL τ K) = Units.map (entrywiseHom T) c)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) (hfix : Units.map (entrywiseHom T) h = h) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧ R.q0 = 2 ^ e ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      (∀ c, ι (φ c) = R.step0 (ι c)) ∧ L154RootD0 S R := by
  classical
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hcomp : (iterateFrobenius L 2 e).comp ι₁ = ι₁.comp T := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, iterateFrobenius_def, hT, map_pow]
  have hcomm := units_map_entrywiseHom_baseChangeGL_comm (τ := τ) ι₁ (iterateFrobenius L 2 e) T
    hcomp
  set u : ModGL τ L := baseChangeGL ι₁ h with hu
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hfix' : entrywiseFrobGL τ L 2 e u = u := by
    show Units.map (entrywiseHom (iterateFrobenius L 2 e)) (baseChangeGL ι₁ h) = baseChangeGL ι₁ h
    rw [hcomm, hfix]
  have hpq : Nat.Coprime p (2 ^ e) := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right e
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon (Ne.symm hp2)
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hhL hup
  obtain ⟨D, R, hΦ, hq, hRq0, hRFr0, hmem, hfixd, hconjstep, hD0⟩ :=
    l154td4_exists_frobRoot_of_toral_frob he hpq hup hfix' hconj
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 (e * p) c
  have hd := langDescent_of_entrywiseFrobenius hτ hFr D hΦ hperf
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL τ K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL τ K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hep : 2 ≤ e * p := by nlinarith [hp.two_le]
  have hq' : 5 ≤ p ∨ 4 ≤ D.q := Or.inr (by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * p) := Nat.pow_le_pow_right (by norm_num) hep)
  obtain ⟨S, a, ι, rfl, hTa, hap, h1, hda, hι, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime_descent Nat.prime_two (le_trans (by norm_num) hep) D hq
      hp hp2 hq' hd.finite_model ι₀ hι₀inj hd.Γ_eq β hβ' hmem hup hu1
  refine ⟨S, R, a, ι, hq.trans hK.symm, hRq0, ⟨_, hFr, hΦ⟩, hTa, hap, h1, ?_, hinj, hrange,
    hconjι, fun c => ?_, hD0⟩
  · rw [hda]
    exact hfixd
  · have h' : ι₀ (φ c) = Units.map (entrywiseHom R.Fr0) (ι₀ c) := by
      rw [hRFr0]
      change baseChangeGL ι₁ (φ c : ModGL τ K) =
        Units.map (entrywiseHom (iterateFrobenius L 2 e)) (baseChangeGL ι₁ (c : ModGL τ K))
      rw [hφ c, hcomm]
    rw [hι (φ c), hι c, hconjstep, h']

end Suppliers

section Full


theorem l154td4_exists_langSetup_frobRoot_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (e * p))
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (T : K →+* K) (hT : ∀ c, T c = c ^ (2 ^ e))
    (β φ : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹)
    (hφ : ∀ c, (φ c : ModGL τ K) = Units.map (entrywiseHom T) c)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) (hfix : Units.map (entrywiseHom T) h = h) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (R : FrobRoot S.D p)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧ R.q0 = 2 ^ e ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      (∀ c, ι (φ c) = R.step0 (ι c)) ∧ L154RootD0 S R :=
  l154td4_exists_langSetup_frobRoot_untw_of_mon hτ hp hp2 he hK
    (monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2) hperf T hT β φ h hhL hβ hφ hp1
    hh1 hfix

end Full

section Setup


theorem l154td4_excUntw_lang {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (PSimple p S) l154ExcUntw) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x) :
    ∃ (τ : Tag) (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
      (SL : LangSetup τ L p) (R : FrobRoot SL.D p) (e : ℕ) (a : Fin τ.rank → Lˣ)
      (i : KernelComponent (rootCharHom a)),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧ 1 ≤ e ∧ R.q0 = 2 ^ e ∧
      L154RootD0 SL R ∧
      rootDiagUnit τ a ∈ SL.D.torus ∧ (∀ k, a k ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
        R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (InnDiagOn p (Subgroup.zpowers y) J →
        LargeEvenMarking ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
          ∃ φ ∈ I, LargeEvenInduces θ
            (fun z z' => R.step0 (z : ModGL τ L) = (z' : ModGL τ L)) φ) ∧
      (IsTD4 p J → catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
          (onLie fun | .trialityD4 _ => True | _ => False)) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := by
    haveI := hSn
    rw [Subgroup.normalizer_eq_top S]
    exact Subgroup.mem_top x
  obtain ⟨τ, K, _, _, e, k, θ, φx, φy, h, T, hτ, hchar, he, hK, hT, hperf, -, hhp, hfix, hhL,
    -, hφx, hφy, hindx, hindy⟩ := excUntw_marking_data hp hp2 hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    have h1 : φx = 1 := by
      ext c
      rw [hφx c]
      simp
    exact hcm (l154_centMod_of_induces_one hqS.1 hxN θ (h1 ▸ hindx))
  obtain ⟨SL, R, a, ι, -, hq0, -, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ, hD0⟩ :=
    l154td4_exists_langSetup_frobRoot_untw hτ hp hp2 he hK hperf T hT φx φy h hhL hφx hφy hhp
      hh1 hfix
  obtain ⟨i, hqi, hstab, hNID, hTD⟩ := l154_lang_of_model hp hSp hxp hxN hJ hJy θ φx φy hindx
    hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨τ, AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i, hτ,
    he, hq0, hD0, hTa, hap, ha1, hfa, hqi, hstab, hNID, hTD⟩

theorem l154OmegaTD4_excUntw_D0 (hTD4 : L154LangTD4ResD0) : L154OmegaTD4 l154ExcUntw := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  rintro ⟨rfl, hT⟩
  by_cases hcm : CentMod 3 S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).2 ⟨rfl, hT⟩
  obtain ⟨τ, L, _, _, _, SL, R, e, a, i, -, he, hq0, hD0, hTa, hap, ha1, hfa, hqi, hstab, -,
    hTD⟩ := l154td4_excUntw_lang hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm
  exact hTD4 τ L 3 SL R e a i hD0 he hq0 hTa hap ha1 hfa hqi hstab (hTD hT)

theorem l154TD4On_excUntw_D0 (hTD4 : L154LangTD4ResD0) : L154TD4On l154ExcUntw :=
  l154TD4On_of_omegaTD4 (l154OmegaTD4_excUntw_D0 hTD4)

end Setup

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

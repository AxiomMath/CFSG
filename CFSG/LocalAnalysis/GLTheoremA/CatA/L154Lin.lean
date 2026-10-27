module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Omega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open scoped commutatorElement MatrixGroups

theorem exists_notInner_of_eq {X : Type} [Group X] {d : ℕ} {D : Type} [Field D]
    {H : Subgroup (GL (Fin d) D)} (hH : H = StatedSL d D) (α : MulAut X)
    (h : ∃ e : X ≃* LargeEvenProj (StatedSL d D),
      MulAut.congr e α ∉ LargeEvenMatConjImage (LargeEvenProjMk (StatedSL d D)) Set.univ) :
    ∃ e : X ≃* LargeEvenProj H,
      MulAut.congr e α ∉ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ := by
  subst hH
  exact h

theorem l154_marking_J {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] {X J : Subgroup G} {y : G}
    (hJ : GLAPComponent p X J) (hy : y ∈ Subgroup.normalizer (J : Set G)) {r k : ℕ} (hr : 1 ≤ r)
    (hk : 1 ≤ k) (hrk : r = 1 → 2 ≤ k) {D₁ : Type} [Field D₁] [Finite D₁] (hD : Nat.card D₁ = 2 ^ k)
    (e : PSimple p J ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) D₁))
    (hnot : MulAut.congr e (MI.indAut p J y hy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) D₁)) Set.univ) :
    CFSG.Assembly.LargeEvenMarking (PQuot p J) fun lab R _ I _ θ =>
      (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) ∧
        MulAut.congr θ (MI.indAut p J y hy) ∉ I := by
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hJ
  refine ⟨(isQuasisimple_pQuot_of_glaPComponent hp hJ).1, ⟨.A, r, k⟩, ⟨hk, hr, hrk⟩, ?_⟩
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeLinear]
  refine ⟨D₁, inferInstance, inferInstance, hD, e.symm.isSimpleGroup, ?_, e, ?_⟩
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  · exact ⟨Or.inl (by decide), by simp, hnot⟩

section Certs


theorem l154_lin_fieldOn (hLD : LinLabelDict) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hQ : catalogIs (PSimple p S) l154Lin)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) : FieldOn p y J := by
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := hInn.1 (Subgroup.mem_zpowers x)
  have hyN : y ∈ Subgroup.normalizer (S : Set Ω) := hF.1
  obtain ⟨d, K, instK, finK, θ, A, B, σ, φx, ψ, hd, h2, hσ, hA, hψ, hindx, hindy⟩ :=
    lin_marking_data hLD hp hQ hInn hF
  obtain ⟨d₁, D₁, instD, finD, ι, E, e₀, h2', hd₁, h22, h23, hιinj, hE, hTv, hequi⟩ :=
    lin_J_equiv hp hp2 hSp hxp hxN hyN hJ hJy h2 hd θ A B σ φx ψ hA hψ hindx hindy
  have hperf₁ : commutator ↥(StatedSL d₁ D₁) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL D₁ hd₁ h22 h23)
  have hnot₀ : MulAut.congr e₀ (MI.indAut p J y hJy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSL d₁ D₁)) Set.univ := by
    rintro ⟨P, -, hP⟩
    refine no_inner_of_transvections ι hperf₁ σ hσ B P E hE hTv ?_
    intro m hm
    obtain ⟨m', z, hφ, hz⟩ := hequi ⟨m, hm⟩
    have hPm : P * m * P⁻¹ ∈ StatedSL d₁ D₁ := (inferInstance : (StatedSL d₁ D₁).Normal).conj_mem m hm P
    have h1 := hP ⟨m, hm⟩ ⟨P * m * P⁻¹, hPm⟩ rfl
    have h2'' : LargeEvenProjMk (StatedSL d₁ D₁) m' =
        LargeEvenProjMk (StatedSL d₁ D₁) ⟨P * m * P⁻¹, hPm⟩ := by rw [← hφ, h1]
    obtain ⟨z', hz'⟩ := (projMk_eq_iff m' ⟨P * m * P⁻¹, hPm⟩).1 h2''
    refine ⟨z, z'⁻¹, ?_⟩
    have h3 : (m' : GL (Fin d₁) D₁) * Matrix.GeneralLinearGroup.scalar (Fin d₁) z' = P * m * P⁻¹ := by
      have : Matrix.GeneralLinearGroup.scalar (Fin d₁) z' = (m' : GL (Fin d₁) D₁)⁻¹ * (P * m * P⁻¹) := hz'
      rw [this]
      group
    have h4 : (m' : GL (Fin d₁) D₁) =
        Matrix.GeneralLinearGroup.scalar (Fin d₁) z'⁻¹ * (P * m * P⁻¹) := by
      rw [← h3, ← mul_assoc, scalar_mul_comm z'⁻¹ (m' : GL (Fin d₁) D₁), mul_assoc, ← map_mul,
        inv_mul_cancel, map_one, mul_one]
    rw [← h4, ← hz]
  have hD : ∃ k, Nat.card D₁ = 2 ^ k := by
    haveI : Fintype D₁ := Fintype.ofFinite D₁
    haveI : CharP D₁ 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2'
    obtain ⟨n, -, hn⟩ := FiniteField.card D₁ 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨k, hk⟩ := hD
  obtain ⟨r, rfl⟩ : ∃ r, d₁ = r + 1 := ⟨d₁ - 1, by omega⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      exact absurd hk (Nat.card_eq_one_iff_unique.not.2 (fun hh => by
        haveI := hh.1
        exact absurd (Subsingleton.elim (0 : D₁) 1) zero_ne_one))
    · exact h0
  have hrk : r = 1 → 2 ≤ k := by
    rintro rfl
    rcases h22 with h | h
    · exact absurd rfl h
    · rcases Nat.lt_or_ge k 2 with hlt | hge
      · exfalso
        apply h
        rw [hk, show k = 1 by omega, pow_one]
      · exact hge
  obtain ⟨e, he⟩ := exists_notInner_of_eq (largeEvenSLGroup_eq_statedSL (K := D₁) (r + 1))
    (MI.indAut p J y hJy) ⟨e₀, hnot₀⟩
  exact fieldOn_of_notInner hp hp2 hJy hyp
    (l154_marking_J hp hJ hJy (by omega) hk1 hrk hk e he)

theorem l154OmegaFld_lin (hLD : LinLabelDict) : L154OmegaFld l154Lin := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  exact l154_lin_fieldOn hLD hp hp2 hSp hxp hyp hQ hInn hF hJ hJy

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X

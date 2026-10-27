module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement


@[expose] def SmallDatumOrder : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel) (D : Type) [Group D] [Finite D], p.Prime → LargeEvenInLambda2 lab → p ∣ lab.n →
    ¬ LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ →
    CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩ (fun R _ _ _ => Nonempty (D ≃* R)) →
      Nat.card D ≤ 35942400

@[expose] def TwF4CentOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (b : G) (hF : FieldOn 3 b L) (lab : LargeEvenLabel),
    lab.tag = .twF4 → lab.n = 3 → MarkedModel lab (PSimple 3 L) →
    Nat.card (FP.fixSub (indAut 3 L b hF.1)) = 35942400

@[expose] def U6CardLarge : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (k : ℕ), 1 ≤ k → catalogIs S (isU6n k) → 35942400 < Nat.card S

theorem pSimple_component_equiv {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1)
    {E : Subgroup (PSimple p L)} (hE : IsSimpleGroup ↥E) (hEC : E ≤ FP.fixSub (indAut p L b hb))
    (hna : ∃ x y : ↥E, x * y ≠ y * x)
    (hperf : ∀ T : Subgroup (PSimple p L), T ≤ FP.fixSub (indAut p L b hb) → ⁅T, T⁆ = T → T ≤ E)
    {J : Subgroup G} (hJ : GLAPComponent p (L ⊓ cx b) J) : Nonempty (PSimple p J ≃* ↥E) := by
  rw [FR.fixSub_indAut hb] at hEC hperf
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hT : chevTransfer p L J = E :=
    FR.eq_core_of_glaPComponent hE hEC hperf (glaPComponent_chevTransfer hp hb hap hJ)
  have hEcomp : GLAPComponent p (fixSubgroup (chevAut p L ⟨b, hb⟩)) E := by
    rw [← hT]
    exact glaPComponent_chevTransfer hp hb hap hJ
  obtain ⟨e₁⟩ := FR.nonempty_pSimple_equiv_of_simple hp hE hna hEcomp
  obtain ⟨e₂⟩ := nonempty_pSimple_equiv_chevTransfer hp hb hap hJ
  rw [hT] at e₂
  exact ⟨e₂.trans e₁⟩

theorem perfect_of_simple_sub {S : Type} [Group S] {D : Subgroup S} (hs : IsSimpleGroup ↥D)
    (hna : ∃ x y : ↥D, x * y ≠ y * x) : ⁅D, D⁆ = D := by
  obtain ⟨x, y, hxy⟩ := hna
  have hN : (⁅(⊤ : Subgroup ↥D), ⊤⁆ : Subgroup ↥D) = ⊥ ∨ ⁅(⊤ : Subgroup ↥D), ⊤⁆ = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  rcases hN with h | h
  · exfalso
    apply hxy
    have hc : ∀ a b : ↥D, a * b = b * a := by
      intro a b
      have hab : a ∈ (⊤ : Subgroup ↥D) := trivial
      have hbb : b ∈ (⊤ : Subgroup ↥D) := trivial
      have hcomm : (⁅(⊤ : Subgroup ↥D), ⊤⁆ : Subgroup ↥D) = ⊥ := h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact (Subgroup.mem_centralizer_iff.1 (hcomm hab) b trivial).symm
    exact hc x y
  · have h1 : Subgroup.map D.subtype ⁅(⊤ : Subgroup ↥D), ⊤⁆ = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have h2 : Subgroup.map D.subtype (⊤ : Subgroup ↥D) = D := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← h1, h, h2]

theorem simple_of_datum {lab : LargeEvenLabel} {D : Type} [Group D]
    (hΛ : LargeEvenInLambda2 lab) (hG : lab.tag ≠ .G2der) (hna : ∃ x y : D, x * y ≠ y * x)
    (hdat : CFSG.Assembly.LargeEvenRawDatum lab (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    IsSimpleGroup D ∧ MarkedModel lab D := by
  have hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Nonempty (D ≃* R) → ∃ a b : R, a * b ≠ b * a := by
    intro R _ I F ⟨e⟩
    obtain ⟨x, y, h⟩ := hna
    exact ⟨e x, e y, fun h' => h (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
  obtain ⟨R', _, I', F', ⟨e'⟩, hMR⟩ :=
    Canonical.largeEvenRawDatum_exists (Canonical.largeEvenRawDatum_markedModel hΛ hQ hdat)
  have hMD : MarkedModel lab D := MarkedModel.of_mulEquiv e'.symm hMR
  exact ⟨(FR.simple_chev_of_markedModel hG hMD).1, hMD⟩

theorem i91U6At_of_residuals (G : Type) [Group G] [Finite G]
    (hSmall : SmallDatumOrder) (hTwF4 : TwF4CentOrder) (hU6 : U6CardLarge) : I91U6At G := by
  intro X L b I' n' hL hbp hF hI hodd
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hF.1
  have hn1 : 1 ≤ n' := hodd.pos
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hcompT := glaPComponent_chevTransfer hp3 hb hap hI
  have hTC : chevTransfer 3 L I' ≤ FP.fixSub (indAut 3 L b hb) := by
    rw [FR.fixSub_indAut hb]; exact hcompT.1
  have hcomp' : GLAPComponent 3 (FP.fixSub (indAut 3 L b hb)) (chevTransfer 3 L I') := by
    rw [FR.fixSub_indAut hb]; exact hcompT
  have hTperf : ⁅chevTransfer 3 L I', chevTransfer 3 L I'⁆ = chevTransfer 3 L I' :=
    glaPComponent_perfect hcompT
  have hTne : chevTransfer 3 L I' ≠ ⊥ := glaPComponent_ne_bot' hcompT
  obtain ⟨lab, hlab, h3, hM, hpn, D, hD, hdat⟩ := FR.fieldOn_subfield hp3 hp2 hF
  have hTD : chevTransfer 3 L I' ≤ D := hTperf ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
  have hna : ∃ x y : ↥D, x * y ≠ y * x := FR.exists_noncomm_of_perfect hTD hTperf hTne
  have hperfD : ∀ T : Subgroup (PSimple 3 L), T ≤ FP.fixSub (indAut 3 L b hb) → ⁅T, T⁆ = T → T ≤ D :=
    fun T hTC' hTp => hTp ▸ (Subgroup.commutator_mono hTC' hTC').trans hD.2.1
  constructor
  ·
    intro hc
    obtain ⟨ht, hr, hn⟩ := label_of_markedModel6 hM (lieModel_of_catalogIs_isU6n hc)
    have hdat' : CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 5, n'⟩ (fun R' _ _ _ => Nonempty (D ≃* R')) := by
      rcases hdat with h | h
      · have hl : (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel) = ⟨.twA, 5, n'⟩ := by
          rw [ht, hr, hn, Nat.mul_div_cancel_left n' (by norm_num : 0 < 3)]
        rw [← hl]
        exact h
      · exfalso
        rcases h with ⟨h1, -, -⟩ | ⟨h1, -⟩ <;> rw [ht] at h1 <;> cases h1
    have hΛ : LargeEvenInLambda2 (⟨.twA, 5, n'⟩ : LargeEvenLabel) := by
      unfold LargeEvenInLambda2
      exact ⟨hn1, by norm_num, fun h => by norm_num at h⟩
    obtain ⟨hDs, hMD⟩ := simple_of_datum hΛ (by intro h; cases h) hna hdat'
    have hMD' : CFSG.Blueprint.LieModel D .PSU 6 2 n' := hMD
    have hcD : catalogIs D (isU6n n') := catalogIs_isU6n_of_lieModel hn1 hMD'
    obtain ⟨e⟩ := pSimple_component_equiv hp3 hb hbp hDs hD.1 hna hperfD hI
    exact (catalogIs_congr e.symm).mp hcD
  ·
    intro hc
    obtain ⟨E, hEC, hEs, hEna, hEperf, -, -⟩ :=
      FR.coreSub_of_fieldOn hp3 hp2 FR.Res.smallDatum_holds (FR.Res.twF4Core_holds hp3 hp2) hF
        ⟨chevTransfer 3 L I', hTC, hTperf, hTne⟩
    have hTE : chevTransfer 3 L I' = E := FR.eq_core_of_glaPComponent hEs hEC hEperf hcomp'
    obtain ⟨e⟩ := pSimple_component_equiv hp3 hb hbp hEs hEC hEna hEperf hI
    have hcardI : Nat.card (PSimple 3 I') = Nat.card E := Nat.card_congr e.toEquiv
    have hcardU : 35942400 < Nat.card (PSimple 3 I') := hU6 (PSimple 3 I') n' hn1 hc
    rcases hdat with hdatum | hexc
    · by_cases hΛ' : LargeEvenInLambda2 (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel)
      · have hG' : (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel).tag ≠ .G2der := by
          intro h
          have h1 : lab.n = 1 := by
            have hl := hlab
            unfold LargeEvenInLambda2 at hl
            rw [show lab.tag = .G2der from h] at hl
            exact hl.2.2
          omega
        obtain ⟨hDs, hMD⟩ := simple_of_datum hΛ' hG' hna hdatum
        have hEleD : E ≤ D := hTE ▸ hTD
        have hDleE : D ≤ E := hEperf D hD.1 (perfect_of_simple_sub hDs hna)
        have hDE : D = E := le_antisymm hDleE hEleD
        subst hDE
        have hLieD : CFSG.Blueprint.LieModel D .PSU 6 2 n' := lieModel_of_catalogIs_isU6n ((catalogIs_congr e).mp hc)
        obtain ⟨ht, hr, hn⟩ := label_of_markedModel6 hMD hLieD
        have ht2 : lab.tag = .twA := ht
        have hr2 : lab.rank = 5 := hr
        have hn3 : lab.n = 3 * n' := by
          have hn' : lab.n / 3 = n' := hn
          omega
        have hML : CFSG.Blueprint.LieModel (PSimple 3 L) .PSU 6 2 (3 * n') := by
          have hM2 := hM
          unfold MarkedModel at hM2
          have e1 : markTag lab = .PSU := by simp [markTag, ht2]
          have e2 : markRank lab = 6 := by simp [markRank, ht2, hr2]
          have e3 : markChar lab = 2 := by simp [markChar, ht2]
          have e4 : markDeg lab = 3 * n' := by simp [markDeg, ht2, hn3]
          rw [e1, e2, e3, e4] at hM2
          exact hM2
        exact catalogIs_isU6n_of_lieModel (by omega) hML
      · exfalso
        have hsmall : Nat.card ↥D ≤ 35942400 := hSmall 3 lab ↥D Nat.prime_three hlab hpn hΛ' hdatum
        have hEle : Nat.card E ≤ Nat.card ↥D := Subgroup.card_le_of_le (hTE ▸ hTD)
        omega
    · exfalso
      rcases hexc with ⟨h1, h2, hsol⟩ | ⟨h1, h2⟩
      · exact (FR.false_of_perfect_solvable hTD hTperf hTne hsol).elim
      · have hC := hTwF4 G L b hF lab h1 h2 hM
        have hEle : Nat.card E ≤ Nat.card (FP.fixSub (indAut 3 L b hF.1)) := Subgroup.card_le_of_le hEC
        omega

end I91T

end CFSG.LocalAnalysis.GLTheoremA

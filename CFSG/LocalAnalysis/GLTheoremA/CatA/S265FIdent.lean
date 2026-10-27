module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open scoped commutatorElement

@[expose] def S265FSmallOrd (N : ℕ) : Prop :=
  N = 360 ∨ N = 720 ∨ N = 6048 ∨ N = 12096 ∨ N ∣ 35942400

section Pure

variable {G : Type} [Group G] [Finite G]

private theorem s265f_pSimple_equiv {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G}
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

end Pure

section Cert


variable {G : Type} [Group G] [Finite G]

private theorem s265f_simple_of_datum {lab : LargeEvenLabel} {D : Type} [Group D]
    (hΛ : LargeEvenInLambda2 lab) (hG : lab.tag ≠ .G2der) (hna : ∃ x y : D, x * y ≠ y * x)
    (hdat : CFSG.Assembly.LargeEvenRawDatum lab (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    IsSimpleGroup D ∧ MarkedModel lab D := by
  have hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Nonempty (D ≃* R) →
      ∃ a b : R, a * b ≠ b * a := by
    intro R _ I F ⟨e⟩
    obtain ⟨x, y, h⟩ := hna
    exact ⟨e x, e y, fun h' => h (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
  obtain ⟨R', _, I', F', ⟨e'⟩, hMR⟩ :=
    Canonical.largeEvenRawDatum_exists (Canonical.largeEvenRawDatum_markedModel hΛ hQ hdat)
  have hMD : MarkedModel lab D := MarkedModel.of_mulEquiv e'.symm hMR
  exact ⟨(FR.simple_chev_of_markedModel hG hMD).1, hMD⟩

private theorem s265f_twF4_cent_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hF : FieldOn p b L) {lab : LargeEvenLabel} (htag : lab.tag = .twF4) (hn : lab.n = p)
    (hM : MarkedModel lab (PSimple p L)) :
    Nat.card ↥(FP.fixSub (indAut p L b hF.1)) = 35942400 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨hβp, hβi⟩ := FR.Res.fieldOn_outer hp hp2 hF
  set β := indAut p L b hF.1 with hβ
  have hβ1 : β ≠ 1 := fun h => hβi ⟨1, by rw [h]; ext x; simp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag hn
  subst htag
  subst hn
  have hL : CFSG.Blueprint.LieModel (PSimple n L) .twistedF4 0 2 n := hM
  obtain ⟨-, hadm, a, hfa, K, _, _, hK, ⟨e0⟩⟩ := hL.reeTitsModel (by simp [reeTitsTags])
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      exact absurd hfa (by simpa using hp.ne_one)
    · exact h0
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ :=
    FR.Res.ree_fix_equiv ha hK' hp hp2 e0 β hβord hβi
  have hb0 : b₀ = 0 := by
    have h1 : (2 * b₀ + 1) * n = 1 * n := by rw [hb, hfa, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have hk' : Nat.card k = 2 ^ (2 * 0 + 1) := by simpa using hk2
  have hΓcard : Nat.card ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma k 0) = 35942400 := by
    have := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      0 k hk').1
    rw [this]
    norm_num
  rw [Nat.card_congr eF.toEquiv, hΓcard]

theorem s265f_ident_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hF : FieldOn p b L) (hbp : b ^ p = 1) (hI : Ipart p L b ≠ ⊥) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ MarkedModel lab (PSimple p L) ∧ p ∣ lab.n ∧
      ((LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ ∧
          MarkedModel ⟨lab.tag, lab.rank, lab.n / p⟩ (PSimple p (Ipart p L b))) ∨
        (S265FSmallOrd (Nat.card (PSimple p (Ipart p L b))) ∧
          (Nat.card (PSimple p (Ipart p L b)) = 17971200 → lab.tag = .twF4 ∧ lab.n = p))) := by
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hF.1
  obtain ⟨lab, hlab, h3, hM, hpn, D, hD, hdat⟩ := FR.fieldOn_subfield hp hp2 hF
  have hcore := FR.coreSub_of_fieldOn hp hp2 FR.Res.smallDatum_holds (FR.Res.twF4Core_holds hp hp2)
    hF (FR.exists_perfect_of_ipart hp hb hbp hI)
  obtain ⟨E, hEC, hEs, hEna, hEperf, h2E, hEch⟩ := hcore
  have hEC' := hEC
  have hEperf' := hEperf
  rw [FR.fixSub_indAut hb] at hEC' hEperf'
  obtain ⟨J₀, hJ₀, hIeq, hTE⟩ := FR.ipart_single hp hb hbp hEs hEC' hEperf' hI
  obtain ⟨e⟩ := s265f_pSimple_equiv hp hb hbp hEs hEC hEna hEperf hJ₀
  have hcardI : Nat.card (PSimple p (Ipart p L b)) = Nat.card E := by
    rw [hIeq]
    exact Nat.card_congr e.toEquiv
  have hEperfect : ⁅E, E⁆ = E := s265f_perfect_of_simple_sub hEs hEna
  have hED : E ≤ D := hEperfect ▸ (Subgroup.commutator_mono hEC hEC).trans hD.2.1
  rcases hdat with hdat | hexc
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩
    ·
      have hG : (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag ≠ .G2der := by
        intro h
        have h1 : lab.n = 1 := by
          have hl := hlab
          unfold LargeEvenInLambda2 at hl
          rw [show lab.tag = .G2der from h] at hl
          exact hl.2.2
        rw [h1] at hpn
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
      have hna' : ∃ x y : ↥D, x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hEna
        exact ⟨⟨x, hED x.2⟩, ⟨y, hED y.2⟩, fun h =>
          hxy (Subtype.ext (congrArg (fun z : ↥D => (z : PSimple p L)) h))⟩
      obtain ⟨hDs, hMD⟩ := s265f_simple_of_datum hΛ hG hna' hdat
      have hDE : D ≤ E := hEperf D hD.1 (s265f_perfect_of_simple_sub hDs hna')
      have hDeq : D = E := le_antisymm hDE hED
      subst hDeq
      refine ⟨lab, hlab, hM, hpn, Or.inl ⟨hΛ, ?_⟩⟩
      rw [hIeq]
      exact MarkedModel.of_mulEquiv e.symm hMD
    ·
      have hEs' : IsSimpleGroup ↥(E.subgroupOf D) :=
        (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hED)).mpr hEs
      have hEna' : ∃ x y : ↥(E.subgroupOf D), x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hEna
        exact ⟨⟨⟨x, hED x.2⟩, x.2⟩, ⟨⟨y, hED y.2⟩, y.2⟩, fun h =>
          hxy (Subtype.ext (congrArg (fun z : ↥(E.subgroupOf D) => ((z : ↥D) : PSimple p L)) h))⟩
      have hEperf'' : ∀ T : Subgroup ↥D, ⁅T, T⁆ = T → T ≤ E.subgroupOf D := by
        intro T hT x hx
        have hTmap : ⁅T.map D.subtype, T.map D.subtype⁆ = T.map D.subtype := by
          rw [← Subgroup.map_commutator, hT]
        have hle : T.map D.subtype ≤ FP.fixSub (indAut p L b hb) :=
          (Subgroup.map_subtype_le T).trans hD.1
        exact hEperf _ hle hTmap ⟨x, hx, rfl⟩
      obtain ⟨hcard, htag⟩ :=
        s265f_small_card_mem hp lab hlab hpn hΛ hdat (E.subgroupOf D) hEs' hEna' hEperf''
      have hcardE : Nat.card ↥(E.subgroupOf D) = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
      rw [hcardE] at hcard htag
      refine ⟨lab, hlab, hM, hpn, Or.inr ⟨?_, fun h => htag (hcardI ▸ h)⟩⟩
      rw [hcardI]
      unfold S265FSmallOrd
      rcases hcard with h | h | h | h | h | h <;> rw [h] <;> norm_num
  ·
    rcases hexc with ⟨htag, hn, hsol⟩ | ⟨htag, hn⟩
    · exfalso
      exact FR.false_of_perfect_solvable hED hEperfect
        (fun h => by
          obtain ⟨x, y, hxy⟩ := hEna
          apply hxy
          have hx : (x : PSimple p L) ∈ (⊥ : Subgroup (PSimple p L)) := by
            rw [← h]
            exact x.2
          have hx1 : (x : PSimple p L) = 1 := Subgroup.mem_bot.1 hx
          exact Subtype.ext (by simp [hx1])) hsol
    · have hC := s265f_twF4_cent_card hp hp2 hF htag hn hM
      have hdvd : Nat.card E ∣ Nat.card ↥(FP.fixSub (indAut p L b hb)) := Subgroup.card_dvd_of_le hEC
      rw [hC] at hdvd
      refine ⟨lab, hlab, hM, hpn, Or.inr ⟨?_, fun _ => ⟨htag, hn⟩⟩⟩
      rw [hcardI]
      exact Or.inr (Or.inr (Or.inr (Or.inr hdvd)))

theorem s265f_ident {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hF : FieldOn p b L) (hbp : b ^ p = 1) (hI : Ipart p L b ≠ ⊥)
    (hN : ¬ S265FSmallOrd (Nat.card (PSimple p (Ipart p L b)))) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ MarkedModel lab (PSimple p L) ∧ p ∣ lab.n ∧
      LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ ∧
      MarkedModel ⟨lab.tag, lab.rank, lab.n / p⟩ (PSimple p (Ipart p L b)) := by
  obtain ⟨lab, hlab, hM, hpn, h⟩ := s265f_ident_gen hp hp2 hF hbp hI
  rcases h with ⟨hΛ, hMD⟩ | ⟨hord, -⟩
  · exact ⟨lab, hlab, hM, hpn, hΛ, hMD⟩
  · exact (hN hord).elim

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S265

end

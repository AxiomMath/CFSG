module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196AmbCore
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.HardMathSupport.Foote.E27.PSU42
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

theorem ambiguousChev_lie_r {r : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : ambiguousChev r (TauCeti.CFSGIndex.lie d)) : r = 2 ∨ r = 3 := by
  obtain ⟨lt, hv⟩ := d
  simp only [ambiguousChev] at h
  split at h
  · rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  · rcases h with ⟨-, h⟩ <;> simp [h]
  · rcases h with ⟨-, h⟩ <;> simp [h]
  · exact absurd h (by simp)

theorem ambiguousChev_three_lie {d : TauCeti.ValidLieTypeIndex}
    (h : ambiguousChev 3 (TauCeti.CFSGIndex.lie d)) :
    (∃ q : TauCeti.PrimePower, d.1 = .A 1 q ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 3 q ∧ q.card = 2) := by
  obtain ⟨lt, hv⟩ := d
  simp only [ambiguousChev] at h
  split at h
  · left
    refine ⟨_, rfl, ?_⟩
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 (by norm_num)
    · exact h1
  · exact absurd h (by simp)
  · right
    refine ⟨_, rfl, ?_⟩
    rcases h with ⟨h1, -⟩
    exact h1
  · exact h.elim

theorem primePower_eq_q2 {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q = CFSG.AGLEmbedding.KFactProofs.Sp62Local.q2 := by
  obtain ⟨p, e, hp, he⟩ := q
  have hcard : p ^ e = 2 := (TauCeti.PrimePower.card_def _).symm.trans hq
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := hcard ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp he)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  subst hp2
  have he1 : e = 1 := by
    have h2 : (2 : ℕ) ^ e = 2 ^ 1 := by simpa using hcard
    exact Nat.pow_right_injective (le_refl 2) h2
  subst he1
  rfl

theorem i196AmbLQ_five : I196AmbLQ 5 := by
  intro H _ _ S hSn hS hnab hamb hC Q hQS hQ hQp h hh hcomm
  haveI := hSn
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    have hn5 : n = 5 := by
      simp only [ambiguousChev] at hi
      omega
    subst hn5
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨f⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_mulEquiv_alternating_five
      (k := ZMod 5) (Or.inr (by simp))
    let g : ↥S ≃* StatedProj (StatedSL 2 (ZMod 5)) :=
      e.trans (f.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)))
    have hcl : StatedClassicalModel ↥S .PSL 2 5 1 :=
      ⟨⟨by norm_num, by norm_num, le_rfl, by norm_num, by norm_num⟩, ZMod 5, inferInstance,
        inferInstance, by simp, ⟨g⟩⟩
    exact ambLQ_of_classical (by norm_num) (by norm_num) S (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hcl hC
      hQS hQ hQp h hh hcomm
  | lie d =>
    exfalso
    rcases ambiguousChev_lie_r hi with h2 | h3
    · omega
    · omega
  | sporadic s => simp [ambiguousChev] at hi

theorem i196AmbLQ_three : I196AmbLQ 3 := by
  intro H _ _ S hSn hS hnab hamb hC Q hQS hQ hQp h hh hcomm
  haveI := hSn
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    have hn6 : n = 6 := by
      simp only [ambiguousChev] at hi
      omega
    subst hn6
    have hk9 : Nat.card (GaloisField 3 2) = 9 := by
      rw [GaloisField.card 3 2 (by norm_num)] <;> norm_num
    obtain ⟨f⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_nine_mulEquiv_alternating_six hk9
    let g : ↥S ≃* StatedProj (StatedSL 2 (GaloisField 3 2)) :=
      e.trans (f.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 2)))
    have hcl : StatedClassicalModel ↥S .PSL 2 3 2 :=
      ⟨⟨by norm_num, by norm_num, le_rfl, by norm_num, by norm_num⟩, GaloisField 3 2, inferInstance,
        inferInstance, hk9.trans (by norm_num), ⟨g⟩⟩
    exact ambLQ_of_classical (by norm_num) (by norm_num) S (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hcl hC
      hQS hQ hQp h hh hcomm
  | lie d =>
    rcases ambiguousChev_three_lie hi with ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩
    ·
      obtain ⟨lt, hv⟩ := d
      simp only at hq
      subst hq
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hk8 : Nat.card (GaloisField 2 3) = q.card := by
        rw [GaloisField.card 2 3 (by norm_num), hq8] <;> norm_num
      obtain ⟨f⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
        (n := 1) (k := GaloisField 2 3) q hv hk8
      let g : ↥S ≃* StatedProj (StatedSL 2 (GaloisField 2 3)) :=
        e.trans (f.symm.trans ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          2 (GaloisField 2 3)).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2
            (GaloisField 2 3))))
      have hcl : StatedClassicalModel ↥S .PSL 2 2 3 :=
        ⟨⟨by norm_num, by norm_num, le_rfl, by norm_num, by norm_num⟩, GaloisField 2 3, inferInstance,
          inferInstance, GaloisField.card 2 3 (by norm_num), ⟨g⟩⟩
      obtain ⟨hR, hH⟩ := psl28Full ↥S hS hnab hcl
      exact lieQ_of_radRigid S hH.holdsTits hR hC hQS hQ hQp h hh hcomm
    ·
      obtain ⟨lt, hv⟩ := d
      simp only at hq
      subst hq
      have hdq : (⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ : TauCeti.ValidLieTypeIndex) =
          CFSG.AGLEmbedding.KFactProofs.Sp62Local.u42Index :=
        Subtype.ext (by
          show TauCeti.LieTypeIndex.twistedA 3 q =
            TauCeti.LieTypeIndex.twistedA 3 CFSG.AGLEmbedding.KFactProofs.Sp62Local.q2
          rw [primePower_eq_q2 hq2])
      have e' : ↥S ≃* (TauCeti.CFSGIndex.lie
          CFSG.AGLEmbedding.KFactProofs.Sp62Local.u42Index).Group := by
        rw [← hdq]
        exact e
      obtain ⟨u⟩ := CFSG.HardMathSupport.Foote.E27.U2_four_mulEquiv_catGroup_u42
      let g : ↥S ≃* StatedProj (StatedSp 2 (ZMod 3)) :=
        e'.trans (u.symm.trans CFSG.GH74.Exceptional.psp43EquivU2.symm)
      have hcl : StatedClassicalModel ↥S .PSp 2 3 1 :=
        ⟨⟨by norm_num, by norm_num, le_rfl, by norm_num⟩, ZMod 3, inferInstance, inferInstance,
          by simp, ⟨g⟩⟩
      exact ambLQ_of_classical (by norm_num) (by norm_num) S (t := .PSp) (by simp [CFSG.Blueprint.classicalTags]) hcl hC
        hQS hQ hQp h hh hcomm
  | sporadic s => simp [ambiguousChev] at hi

theorem i196AmbLQ_holds : ∀ p : ℕ, p.Prime → p ≠ 2 → I196AmbLQ p := by
  intro p hp hp2
  by_cases h3 : p = 3
  · subst h3
    exact i196AmbLQ_three
  by_cases h5 : p = 5
  · subst h5
    exact i196AmbLQ_five
  intro H _ _ S hSn hS hnab hamb
  exfalso
  obtain ⟨i, hi, -⟩ := hamb
  rcases ambiguousChev_prime_of_mem hi with h | h | h
  · exact hp2 h
  · exact h3 h
  · exact h5 h

end CFSG.LocalAnalysis.GLTheoremA

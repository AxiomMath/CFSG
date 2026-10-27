module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Comp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem inner_of_card_two [Finite K] (hK : Nat.card K = 2) :
    ∀ α : MulAut (StatedProj (StatedSp 3 K)), ∃ t, α = MulAut.conj t := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let e : StatedProj (StatedSp 3 K) ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3 ⊕ Fin 3) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 3)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact CFSG.Sporadic.Schreier.Co3.allInner_of_mulEquiv e
    CFSG.Sporadic.Schreier.Co3.sp3_two_allInner

theorem center_eq_bot_of_simple {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem mem_center_of_conj_eq_one {G : Type} [Group G] {z : G} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut G => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem kLevel_le_two_of_k2 {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

theorem fixSubgroup_conj_one {G : Type} [Group G] :
    fixSubgroup (MulAut.conj (1 : G)) = ⊤ := by
  ext g
  rw [mem_fixSubgroup, map_one, MulAut.one_apply]
  simp

theorem downLe_three_two_of_simple [Finite K] (hK : Nat.card K = 2)
    [IsSimpleGroup (StatedProj (StatedSp 3 K))]
    (hnc : ∃ a b : StatedProj (StatedSp 3 K), a * b ≠ b * a)
    (hk : catalogIs (StatedProj (StatedSp 3 K)) (k2 3)) :
    DownLe 3 2 (StatedProj (StatedSp 3 K)) := by
  intro α hα J hJ
  obtain ⟨t, rfl⟩ := inner_of_card_two hK α
  have ht3 : t ^ 3 = 1 := by
    have h1 : MulAut.conj (t ^ 3) = 1 := by rw [map_pow, hα]
    have h2 : t ^ 3 ∈ Subgroup.center _ := mem_center_of_conj_eq_one h1
    rw [center_eq_bot_of_simple hnc, Subgroup.mem_bot] at h2
    exact h2
  by_cases ht1 : t = 1
  · subst ht1
    rw [fixSubgroup_conj_one] at hJ
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hnc hJ
    rw [kLevel_congr 3 f]
    exact kLevel_le_two_of_k2 hk
  · have hord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
    have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
    obtain ⟨x, ⟨hxt, hxo⟩, -⟩ :=
      (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks (r := 3)
        Nat.prime_two le_rfl hK' Nat.prime_three (by norm_num) (by norm_num) (by norm_num) t hord).1
    have hblocks := (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
        (r := 3) Nat.prime_two le_rfl hK' Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
        t hord).2 x hxt hxo
    subst hxt
    have hx3 : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hxo] at this
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact ht1 (map_one _)
    exact (kLevel_le_one_of_component hK hx3 hx1 hblocks hJ).trans (by norm_num)

theorem kdLieRowSp6Two_holds :
    KDLieRowSp6Two := by
  unfold KDLieRowSp6Two
  intro q hv hq2
  obtain ⟨hA, hB⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (q := q) (s := 1)
    Nat.prime_two (by norm_num) (by rw [hq2]; norm_num)
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.B 3 q, hv⟩
  have hKc : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) = 2 := by
    rw [CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B 3 q)
      (TauCeti.LieTypeIndex.fieldExponent_B 3 q), hA, hB]
    norm_num
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hKc]; norm_num)
  let e : (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group ≃*
      StatedProj (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)) :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv hA (le_refl 3)
  have hsT : IsSimpleGroup (StatedProj (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨.B 3 q, hv⟩))) := e.symm.isSimpleGroup
  have hcardT : Nat.card (StatedProj (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨.B 3 q, hv⟩))) = 1451520 := by
    rw [Nat.card_congr (CFSG.Monster.Existence.Compat.statedProjEquivOfBot
      (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩))
      (CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hKc (Fin 3 ⊕ Fin 3))).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hKc]
    decide
  have hnc : ∃ a b : StatedProj (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨.B 3 q, hv⟩)), a * b ≠ b * a :=
    exists_noncomm_of_simple_not_prime (by rw [hcardT]; norm_num)
  have hk : catalogIs (StatedProj (StatedSp 3 ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨.B 3 q, hv⟩))) (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩, ⟨rfl, hq2⟩, ⟨e.symm⟩⟩
  exact downLe_of_mulEquiv e.symm (downLe_three_two_of_simple hKc hnc hk)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

end

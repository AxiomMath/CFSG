module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTools
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowThree
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.RankThree.PartTwo.Sec21.HeringFFLE27
import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Tr

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Generic

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem pow_three_eq_one_of_mem_range_of_odd (σ : I₀ →* Y)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) {y : Y} (hy : y ∈ σ.range)
    (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : CFSG.ComponentClassification.AS76b.oUpperTwo σ.range =
      (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ := by
    rw [SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map]
  have hyJ : y ∈ CFSG.ComponentClassification.AS76b.oUpperTwo σ.range :=
    Subgroup.subset_closure ⟨hy, hodd⟩
  rw [hJ] at hyJ
  obtain ⟨g, hg, rfl⟩ := hyJ
  have h2 : IsPGroup 2 ((CFSG.pCore 2 I₀).map σ) := CFSG.pCore_isPGroup.map σ
  have hmem : σ g ^ 3 ∈ (CFSG.pCore 2 I₀).map σ := by
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem σ (cube_mem_pCore_two hb g hg)
  obtain ⟨n, hn⟩ := h2 ⟨_, hmem⟩
  have hn' : (σ g ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hodd3 : Odd (orderOf (σ g ^ 3)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd 3)
  have hdvd : orderOf (σ g ^ 3) ∣ 1 := by
    have h1 : orderOf (σ g ^ 3) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hcop : Nat.Coprime (orderOf (σ g ^ 3)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd3)
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd dvd_rfl h1
  rw [Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem oUpperTwo_map_le_of_odd (σ : I₀ →* Y) {K : Subgroup Y}
    (hK : ∀ y ∈ σ.range, Odd (orderOf y) → y ∈ K) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K := by
  rw [SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map]
  exact (Subgroup.closure_le _).mpr fun y hy => hK y hy.1 hy.2

theorem eq_one_of_mem_centralizer_of_elemAbelian_card {K E : Subgroup Y}
    (hrk : CFSG.pRank 3 ↥(⊤ : Subgroup Y) ≤ 3) (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hKC : K ⊓ centralizer (K : Set Y) = ⊥) {c : Y}
    (hc : c ∈ centralizer (K : Set Y)) (hc3 : c ^ 3 = 1) : c = 1 := by
  by_contra hc1
  have hcE : c ∉ E := fun h => hc1 (by
    have : c ∈ K ⊓ centralizer (K : Set Y) := ⟨hEK h, hc⟩
    rwa [hKC, Subgroup.mem_bot] at this)
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers c, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a c from Subgroup.mem_centralizer_iff.mp hc a (hEK ha)) k).eq
  have hel := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hE
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hc3) hcomm
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_three hel
  have hlt : E < E ⊔ zpowers c := by
    refine lt_of_le_of_ne le_sup_left fun h => hcE ?_
    rw [h]
    exact mem_sup_right (mem_zpowers c)
  have hcard := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [hEc, hk] at hcard
  have hk4 : 4 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hcard
    omega
  have hle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank (by norm_num) le_top hel hk
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrk
  omega

theorem exists_conj_of_pow_three_of_mulEquiv {K X : Type*} [Group K] [Group X] (e : K ≃* X)
    (hX : ∀ α : MulAut X, α ^ 3 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range) (α : MulAut K)
    (hα : α ^ 3 = 1) : ∃ g : K, α = MulAut.conj g := by
  have h3 : (MulAut.congr e α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨g, hg⟩ := hX _ h3
  refine ⟨e.symm g, ?_⟩
  have h1 : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [← h1, ← hg, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

theorem exists_mul_of_pow_three {K : Subgroup Y} [K.Normal]
    (hX : ∀ α : MulAut K, α ^ 3 = 1 → ∃ g : K, α = MulAut.conj g) {y : Y} (hy : y ^ 3 = 1) :
    ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Y), y = k * c := by
  set θ : Y →* MulAut K := MulAut.conjNormal with hθ
  have hθ3 : θ y ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨g, hg⟩ := hX _ hθ3
  refine ⟨g, g.2, (g : Y)⁻¹ * y, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_, by group⟩
  have h1 := congrArg (fun a : MulAut K => ((a ⟨m, hm⟩ : K) : Y)) hg
  simp only [hθ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  calc m * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * m * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h1]
    _ = (g : Y)⁻¹ * y * m := by group

end Generic

theorem ThreeFourSolvThreeLeAt.of_inner_of_elemAbelian {X : Type*} [Group X]
    (hX : ∀ α : MulAut X, α ^ 3 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range)
    (hE : ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) :
    ThreeFourSolvThreeLeAt X := by
  intro Y _ _ K Y₀ E' R I₀ _ _ σ hK hKX hZ hrk _ _ _ _ _ _ _ _ _ _ _ hb _ _ _
  haveI := hK
  obtain ⟨e⟩ := hKX
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  obtain ⟨E, hEel, hEc⟩ := hE
  set E₁ : Subgroup Y := (E.map e.symm.toMonoidHom).map K.subtype with hE₁
  have hE₁K : E₁ ≤ K := Subgroup.map_subtype_le _
  have hE₁el : IsElemAbelian 3 E₁ := (hEel.map _).map _
  have hE₁c : Nat.card E₁ = 3 ^ 3 := by
    rw [hE₁, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hEc]
  have hinner := exists_conj_of_pow_three_of_mulEquiv e hX
  refine oUpperTwo_map_le_of_odd σ fun y hy hodd => ?_
  have hy3 := pow_three_eq_one_of_mem_range_of_odd σ hb hy hodd
  obtain ⟨k, hk, c, hc, rfl⟩ := exists_mul_of_pow_three hinner hy3
  have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk
  have hc3 : c ^ 3 = 1 := by
    have h1 : k ^ 3 * c ^ 3 = 1 := by rw [← (Commute.mul_pow hkc 3)]; exact hy3
    have h2 : c ^ 3 ∈ K ⊓ centralizer (K : Set Y) := by
      refine ⟨?_, Subgroup.pow_mem _ hc 3⟩
      have : c ^ 3 = (k ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact K.inv_mem (K.pow_mem hk 3)
    rwa [hKC, Subgroup.mem_bot] at h2
  rw [eq_one_of_mem_centralizer_of_elemAbelian_card hrk hE₁K hE₁el hE₁c hKC hc hc3, mul_one]
  exact hk

theorem threeFourSolvThreeLeAt_altNine (h : 5 ≤ 9) :
    ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.alternating 9 h).Group :=
  ThreeFourSolvThreeLeAt.of_inner_of_elemAbelian
    (fun _ hα => CFSG.RankThree.PartTwo.Sec8.Hering611.mem_range_conj_of_pow_three_alt9
      (MulEquiv.refl _) hα)
    CFSG.LocalAnalysis.GLTheoremA.S8.L83.alt9_elemAbelian

theorem threeFourSolvThreeLeAt_uFourTwo (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex)
    (hq2 : q.p = 2) (hq1 : q.exponent = 1) (hd : d.1 = .twistedA 3 q) :
    ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨i, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowThree.nonempty_mulEquiv_SU42
    q hv hq2 hq1
  refine ThreeFourSolvThreeLeAt.of_mulEquiv e.symm
    (ThreeFourSolvThreeLeAt.of_inner_of_elemAbelian
      (fun _ hα => CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.mem_range_conj_of_pow_three hα)
      ⟨CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.E₀,
        CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.isElemAbelian_E₀, ?_⟩)
  rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.card_E₀]
  norm_num

theorem threeFourSolvThreeLeAt_spSixTwo (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex)
    (hq2 : q.p = 2) (hq1 : q.exponent = 1) (hd : d.1 = .B 3 q) :
    ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨i, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hq2 hq1
  obtain ⟨E, hE, hEc⟩ := CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.exists_e27_H6
  refine ThreeFourSolvThreeLeAt.of_mulEquiv e.symm
    (ThreeFourSolvThreeLeAt.of_inner_of_elemAbelian (fun α _ => ?_) ⟨E, hE, by rw [hEc]; norm_num⟩)
  obtain ⟨g, hg⟩ := CFSG.AGLEmbedding.KFactProofs.Sp62Local.all_inner_H6 α
  exact ⟨g, hg.symm⟩

theorem threeFourSolvThreeTargets_of_altSix
    (h6 : ∀ h : 5 ≤ 6, ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.alternating 6 h).Group) :
    ThreeFourSolvThreeTargets := by
  refine ⟨fun n hn h69 => ?_, fun q d hq2 hq1 hd => ?_⟩
  · rcases h69 with rfl | rfl
    · exact h6 hn
    · exact threeFourSolvThreeLeAt_altNine hn
  · rcases hd with hd | hd
    · exact threeFourSolvThreeLeAt_uFourTwo q d hq2 hq1 hd
    · exact threeFourSolvThreeLeAt_spSixTwo q d hq2 hq1 hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

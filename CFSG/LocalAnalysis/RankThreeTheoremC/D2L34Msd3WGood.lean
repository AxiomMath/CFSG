module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape
import CFSG.RankThree.PartOne.N143.GroupLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_map_conj_le {M Q : Subgroup G} {m : G} (hm : m ∈ M)
    (h : Subgroup.normalizer ((Q.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  intro g hg
  have himage : (MulAut.conj m) g ∈ M := by
    apply h
    rw [← Subgroup.map_equiv_normalizer_eq Q (MulAut.conj m)]
    exact Subgroup.mem_map_of_mem _ hg
  have hprod := M.mul_mem (M.mul_mem (M.inv_mem hm) himage) hm
  simpa [MulAut.conj_apply, mul_assoc] using hprod

theorem ne_bot_of_one_le_pRank {Q : Subgroup G} (h : 1 ≤ CFSG.Open.pRank 3 Q) : Q ≠ ⊥ := by
  intro hQ
  obtain ⟨E, hE, -, hEcard⟩ := pRank_attained 3 Nat.prime_three Q
  rw [hQ, le_bot_iff] at hE
  rw [hE, Subgroup.card_bot] at hEcard
  have := Nat.one_lt_pow (by omega : CFSG.Open.pRank 3 Q ≠ 0) Nat.prime_three.one_lt
  omega

omit [Finite G] in
theorem isEA3_of_isElemAbelian {E : Subgroup G} (h : IsElemAbelian 3 E) :
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.IsEA3 E :=
  ⟨fun a ha b hb => congrArg Subtype.val (isMulCommutative_iff.mp h.1 ⟨a, ha⟩ ⟨b, hb⟩), h.2⟩

omit [Finite G] in
theorem isElemAbelian_of_isEA3 {E : Subgroup G}
    (h : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.IsEA3 E) : IsElemAbelian 3 E :=
  ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (h.1 a a.2 b b.2), h.2⟩

theorem exists_E9_le_E27 {F : Subgroup G} (hF : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) :
    ∃ E : Subgroup G, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hEF, hE, hEc⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.exists_sub_ea_of_dvd
      (isEA3_of_isElemAbelian hF) (n := 2) (by rw [hF27]; norm_num)
  exact ⟨E, hEF, isElemAbelian_of_isEA3 hE, by rw [hEc]; norm_num⟩

theorem exists_E27_centralizing_of_normalizes {Z F : Subgroup G} (hZ : IsElemAbelian 3 Z)
    (hZ9 : Nat.card Z = 9) (hF : IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hFN : F ≤ Subgroup.normalizer (Z : Set G)) :
    ∃ F' : Subgroup G, F' ≤ Z ⊔ F ∧ IsElemAbelian 3 F' ∧ Nat.card F' = 27 ∧
      ∀ z ∈ Z, ∀ f ∈ F', z * f = f * z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 Z :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 Z).mpr hZ
  have hFp : IsPGroup 3 F := IsPGroup.of_card (n := 3) (by rw [hF27]; norm_num)
  set ρ : F →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hFN) with hρ
  have hρk := CFSG.RankThree.PartOne.N143.card_le_three_mul_ker Z hZ9 hFp ρ
  set K : Subgroup G := F ⊓ Subgroup.centralizer (Z : Set G) with hK
  have hkerEq : ∀ x : F, x ∈ ρ.ker ↔ (x : G) ∈ Subgroup.centralizer (Z : Set G) := by
    intro x
    rw [hρ, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hmap : ρ.ker.map F.subtype = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hkerEq x).mp hx⟩
    · rintro ⟨hyF, hyC⟩
      exact ⟨⟨y, hyF⟩, (hkerEq ⟨y, hyF⟩).mpr hyC, rfl⟩
  have hKcard : Nat.card K = Nat.card ρ.ker := by
    rw [← hmap, Subgroup.card_map_of_injective F.subtype_injective]
  have hKF : K ≤ F := inf_le_left
  rw [hF27] at hρk
  have hK9 : 9 ≤ Nat.card K := by rw [hKcard]; omega
  have hKle : Nat.card K ≤ 27 := hF27 ▸ Subgroup.card_le_of_le hKF
  have hKdvd : Nat.card K ∣ 27 := hF27 ▸ Subgroup.card_dvd_of_le hKF
  have hKcases : Nat.card K = 9 ∨ Nat.card K = 27 := by
    obtain ⟨c, hc⟩ := hKdvd
    generalize Nat.card K = k at hK9 hKle hc ⊢
    interval_cases k <;> omega
  have hKC : K ≤ Subgroup.centralizer (Z : Set G) := inf_le_right
  rcases hKcases with hK9' | hK27
  ·
    have hKN : K ≤ Subgroup.normalizer (Z : Set G) :=
      hKC.trans (Subgroup.centralizer_le_normalizer _)
    have hZC : Z ≤ Subgroup.centralizer (K : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hKC hk) z hz).symm
    have hZN : Z ≤ Subgroup.normalizer (K : Set G) :=
      hZC.trans (Subgroup.centralizer_le_normalizer _)
    have hcommZK : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := fun z hz k hk =>
      Subgroup.mem_centralizer_iff.mp (hKC hk) z hz
    have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hKN
    rw [hZ9, hK9'] at hcard
    have hZKdvd : Nat.card (Z ⊓ K : Subgroup G) ∣ 9 := hZ9 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hZKne : Nat.card (Z ⊓ K : Subgroup G) ≠ 9 := by
      intro h9
      have hZK : Z ⊓ K = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ9, h9])
      have hZF : Z ≤ F := (hZK.symm.le.trans inf_le_right).trans hKF
      have hFC : F ≤ Subgroup.centralizer (Z : Set G) := fun f hf =>
        Subgroup.mem_centralizer_iff.mpr fun z hz =>
          congrArg Subtype.val (isMulCommutative_iff.mp hF.1 ⟨z, hZF hz⟩ ⟨f, hf⟩)
      have hFK : F ≤ K := le_inf le_rfl hFC
      have := Subgroup.card_le_of_le hFK
      rw [hF27, hK9'] at this
      omega
    have hS27 : 27 ∣ Nat.card (Z ⊔ K : Subgroup G) := by
      have hjpos : 0 < Nat.card (Z ⊓ K : Subgroup G) := Nat.card_pos
      obtain ⟨c, hc⟩ := hZKdvd
      have hjle : Nat.card (Z ⊓ K : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) ⟨c, hc⟩
      generalize Nat.card (Z ⊓ K : Subgroup G) = j at hjpos hjle hc hZKne hcard
      interval_cases j <;> omega
    have hfac : ∀ x ∈ Z ⊔ K, ∃ z ∈ Z, ∃ k ∈ K, x = z * k := by
      intro x hx
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Z K hZN,
        Set.mem_mul] at hx
      obtain ⟨z, hz, k, hk, rfl⟩ := hx
      exact ⟨z, hz, k, hk, rfl⟩
    have hKcomm : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := fun k hk k' hk' =>
      congrArg Subtype.val (isMulCommutative_iff.mp hF.1 ⟨k, hKF hk⟩ ⟨k', hKF hk'⟩)
    have hZcomm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
      congrArg Subtype.val (isMulCommutative_iff.mp hZ.1 ⟨z, hz⟩ ⟨z', hz'⟩)
    have hSea3 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.IsEA3 (Z ⊔ K) := by
      have hUnion : Z ⊔ K = Subgroup.closure ((Z : Set G) ∪ (K : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      rw [hUnion]
      refine CFSG.RankThree.PartOne.N143.closure_comm_exp' (p := 3) _ ?_ ?_
      · rintro a (ha | ha) b (hb | hb)
        · exact hZcomm a ha b hb
        · exact hcommZK a ha b hb
        · exact (hcommZK b hb a ha).symm
        · exact hKcomm a ha b hb
      · rintro a (ha | ha)
        · exact hZ.2 a ha
        · exact hF.2 a (hKF ha)
    obtain ⟨F', hF'S, hF'ea, hF'c⟩ :=
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.exists_sub_ea_of_dvd hSea3 (n := 3)
        (by simpa using hS27)
    have hSC : Z ⊔ K ≤ Subgroup.centralizer (Z : Set G) :=
      sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr fun z' hz' => hZcomm z' hz' z hz) hKC
    exact ⟨F', hF'S.trans (sup_le_sup_left hKF Z), isElemAbelian_of_isEA3 hF'ea,
      by rw [hF'c]; norm_num, fun z hz f hf => Subgroup.mem_centralizer_iff.mp (hSC (hF'S hf)) z hz⟩
  ·
    have hKF' : K = F := Subgroup.eq_of_le_of_card_ge hKF (by rw [hK27, hF27])
    refine ⟨F, le_sup_right, hF, hF27, fun z hz f hf => ?_⟩
    have hfK : f ∈ K := by rw [hKF']; exact hf
    exact Subgroup.mem_centralizer_iff.mp (hKC hfK) z hz

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.normalizer_le_of_centralizes_E27
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {Q F : Subgroup G} (hQM : Q ≤ M)
    (hQp : IsPGroup 3 Q) (hQ1 : Q ≠ ⊥) (hFM : F ≤ M) (hFel : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hcomm : ∀ q ∈ Q, ∀ f ∈ F, q * f = f * q) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have hFp : IsPGroup 3 F := IsPGroup.of_card (n := 3) (by rw [hF27]; norm_num)
  have hQC : Q ≤ Subgroup.centralizer (F : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun f hf => (hcomm q hq f hf).symm
  have hQF : Q ≤ Subgroup.normalizer (F : Set G) := hQC.trans (Subgroup.centralizer_le_normalizer _)
  have hSp : IsPGroup 3 ↥(Q ⊔ F) := IsPGroup.to_sup_of_normal_right' hQp hFp hQF
  have hSM : Q ⊔ F ≤ M := sup_le hQM hFM
  obtain ⟨⟨m, hmM⟩, hm⟩ := exists_conjugate_le_sylow_of_le 3 P hPM hSM hSp
  set Q' : Subgroup G := Q.map (MulAut.conj m).toMonoidHom with hQ'
  set F' : Subgroup G := F.map (MulAut.conj m).toMonoidHom with hF'
  have hQ'P : Q' ≤ (P : Subgroup G) := (Subgroup.map_mono le_sup_left).trans hm
  have hF'P : F' ≤ (P : Subgroup G) := (Subgroup.map_mono le_sup_right).trans hm
  have hQ'1 : Q' ≠ ⊥ := by
    intro hbot
    apply hQ1
    exact Subgroup.map_injective (f := (MulAut.conj m).toMonoidHom)
      (MulAut.conj m).injective (by rw [Subgroup.map_bot]; exact hbot)
  have hF'el : IsElemAbelian 3 F' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hFel _
  have hF'c : Nat.card F' = 3 ^ 3 := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj m).injective, hF27]
    norm_num
  have hF'C : F' ≤ Q' ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (Q' : Set G)) := by
    refine le_trans ?_ le_sup_right
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (Q' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨f, hf, rfl⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc m * q * m⁻¹ * (m * f * m⁻¹) = m * (q * f) * m⁻¹ := by group
        _ = m * (f * q) * m⁻¹ := by rw [hcomm q hq f hf]
        _ = m * f * m⁻¹ * (m * q * m⁻¹) := by group
    exact ⟨hF'P hx, hxC⟩
  have hrank : 3 ≤ CFSG.Open.pRank 3
      (Q' ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (Q' : Set G))) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hF'C hF'el hF'c
  exact normalizer_le_of_map_conj_le hmM
    ((h.threeClause h.sigma P h.core).1 Q' hQ'P hQ'1 hrank)

theorem D2L34SideCtx3.hasGoodE9_of_centralizes
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {X E F : Subgroup G} (hEX : E ≤ X) (hEM : E ≤ M)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hFM : F ≤ M) (hFel : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e) : HasGoodE9 M X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  refine ⟨E, hEX, hEel, hE9, (fullCore_le_iff 3 1 E M).mpr fun Q hQE hrank => ?_⟩
  exact h.normalizer_le_of_centralizes_E27 (hQE.trans hEM) (hEp.to_le hQE)
    (ne_bot_of_one_le_pRank hrank) hFM hFel hF27 fun q hq f hf => hcomm q (hQE hq) f hf

theorem D2L34SideCtx3.hasGoodE9_of_le_E27
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {X E F : Subgroup G} (hEX : E ≤ X) (hEF : E ≤ F)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hFM : F ≤ M) (hFel : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) : HasGoodE9 M X :=
  h.hasGoodE9_of_centralizes hEX (hEF.trans hFM) hEel hE9 hFM hFel hF27 fun e he f hf =>
    congrArg Subtype.val (isMulCommutative_iff.mp hFel.1 ⟨e, hEF he⟩ ⟨f, hf⟩)

theorem D2L34SideCtx3.hasGoodE9_of_E27_le
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {X F : Subgroup G} (hFX : F ≤ X) (hFM : F ≤ M)
    (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) : HasGoodE9 M X := by
  obtain ⟨E, hEF, hEel, hE9⟩ := exists_E9_le_E27 hFel hF27
  exact h.hasGoodE9_of_le_E27 (hEF.trans hFX) hEF hEel hE9 hFM hFel hF27

theorem D2L34SideCtx3.hasGoodE9_of_normalizes
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {X Z F : Subgroup G} (hZX : Z ≤ X) (hZM : Z ≤ M)
    (hZel : IsElemAbelian 3 Z) (hZ9 : Nat.card Z = 9) (hFM : F ≤ M) (hFel : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hFN : F ≤ Subgroup.normalizer (Z : Set G)) : HasGoodE9 M X := by
  obtain ⟨F', hF'ZF, hF'el, hF'27, hcomm⟩ :=
    exists_E27_centralizing_of_normalizes hZel hZ9 hFel hF27 hFN
  exact h.hasGoodE9_of_centralizes hZX hZM hZel hZ9 (hF'ZF.trans (sup_le hZM hFM)) hF'el hF'27
    hcomm

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.Quasithin.Background.F6ResL28
import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.AGLEmbedding

namespace L28Parabolic

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6.L28Res

@[expose] def IsUnip (g : G8) : Prop := g.1.1 = 1 ∧ g.1.2.2.1 = 0 ∧ g.1.2.2.2 = 1

instance : DecidablePred IsUnip := fun g => by unfold IsUnip; infer_instance

@[expose] def unip : Subgroup G8 := uHom.range

theorem mem_unip_iff {g : G8} : g ∈ unip ↔ IsUnip g := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Multiplicative.ofAdd g.1.2.1, Subtype.ext ?_⟩
    obtain ⟨⟨a, b, c, d⟩, hg⟩ := g
    simp only at h1 h2 h3 ⊢
    subst h1 h2 h3
    rfl

theorem card_unip : Nat.card unip = 8 := by
  rw [unip, MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective,
    Subgroup.card_top]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative GF8 ≃ GF8), Nat.card_eq_fintype_card]
  rfl

theorem mem_normalizer_unip_iff {g : G8} :
    g ∈ Subgroup.normalizer (unip : Set G8) ↔
      ∀ t : GF8, IsUnip (g * uHom (Multiplicative.ofAdd t) * g⁻¹) := by
  constructor
  · intro hg t
    exact mem_unip_iff.mp ((Subgroup.mem_normalizer_iff.mp hg _).mp ⟨_, rfl⟩)
  · intro h
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨t, rfl⟩ := hn
    exact mem_unip_iff.mpr (h t.toAdd)

theorem card_normalizer_unip : Nat.card (Subgroup.normalizer (unip : Set G8)) = 56 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_normalizer_unip_iff),
    Nat.card_eq_fintype_card]
  decide +kernel

section Abstract

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem eq_of_le_of_card_eq_fiftySix {N J : Subgroup Λ} (hs : IsSimpleGroup Λ)
    (hcard : Nat.card Λ = 504) (hN : Nat.card N = 56) (hle : N ≤ J) (hJ : J ≠ ⊤) : J = N := by
  obtain ⟨m, hm⟩ := hN ▸ Subgroup.card_dvd_of_le hle
  have hidx := Subgroup.card_mul_index J
  rw [hm, hcard] at hidx
  have hmi : m * J.index = 9 := by
    have h : 56 * (m * J.index) = 56 * 9 := by rw [← mul_assoc]; omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hi : J.index ∣ 3 ^ 2 := by simpa using Dvd.intro_left m hmi
  obtain ⟨k, hk, hk3⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hi
  interval_cases k
  · exact absurd (Subgroup.index_eq_one.mp (by simpa using hk3)) hJ
  · exfalso
    have h3 : J.index = 3 := by simpa using hk3
    have hcore : J.normalCore = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal J.normalCore with h | h
      · exact h
      · exact absurd (top_le_iff.mp (h ▸ J.normalCore_le)) hJ
    have hfin : J.FiniteIndex := ⟨by omega⟩
    have hdvd := J.index_normalCore_dvd_factorial_index
    rw [hcore, Subgroup.index_bot, hcard, h3] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num [Nat.factorial])
  · have hm1 : m = 1 := by
      have h9 : J.index = 9 := by simpa using hk3
      rw [h9] at hmi
      omega
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hm, hm1, hN]

omit [Finite Λ] in
theorem isPGroup_and_not_dvd_index {T : Subgroup Λ} (hT : IsSylowTwoOf T ⊤) :
    IsPGroup 2 T ∧ ¬ 2 ∣ T.index := by
  obtain ⟨-, hT2, hidx⟩ := hT
  exact ⟨hT2, by
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at hidx⟩

theorem pCoreOf_normalizer_eq {T : Subgroup Λ} (hT : IsSylowTwoOf T ⊤) :
    pCoreOf 2 (Subgroup.normalizer (T : Set Λ)) = T := by
  obtain ⟨hT2, hidx⟩ := isPGroup_and_not_dvd_index hT
  let P : Sylow 2 Λ := hT2.toSylow hidx
  exact P.is_maximal' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 T hT2)

theorem card_normalizer_eq_fiftySix {P₀ T : Subgroup Λ} (hcard : Nat.card Λ = 504)
    (h8 : Nat.card P₀ = 8) (h56 : Nat.card (Subgroup.normalizer (P₀ : Set Λ)) = 56)
    (hT : IsSylowTwoOf T ⊤) :
    Nat.card (Subgroup.normalizer (T : Set Λ)) = 56 := by
  obtain ⟨hT2, hidx⟩ := isPGroup_and_not_dvd_index hT
  have hP₀ : IsPGroup 2 P₀ := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hP₀idx : ¬ 2 ∣ P₀.index := by
    have h := Subgroup.card_mul_index P₀
    rw [h8, hcard] at h
    omega
  let S₀ : Sylow 2 Λ := hP₀.toSylow hP₀idx
  let S : Sylow 2 Λ := hT2.toSylow hidx
  have h1 : (Subgroup.normalizer (T : Set Λ)).index = 9 := by
    have hS := Sylow.card_eq_index_normalizer S
    have hS₀ := Sylow.card_eq_index_normalizer S₀
    have hi₀ := Subgroup.card_mul_index (Subgroup.normalizer (P₀ : Set Λ))
    rw [h56, hcard] at hi₀
    have h9 : (Subgroup.normalizer (P₀ : Set Λ)).index = 9 := by omega
    exact hS.symm.trans (hS₀.trans h9)
  have h2 := Subgroup.card_mul_index (Subgroup.normalizer (T : Set Λ))
  rw [h1, hcard] at h2
  omega

end Abstract

open CFSG.LieType.Steinberg.CentralExt in
theorem center_eq_bot
    {Λ : Type} [Group Λ] [Finite Λ] (hΛ : Open.IsQuasisimple Λ)
    (e : Λ ⧸ Subgroup.center Λ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :
    Subgroup.center Λ = ⊥ := by
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hk : Fintype.card (GaloisField 2 3) = 8 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  obtain ⟨-, ⟨eM⟩⟩ := SL2Closed.psl_two_hopfMultiplier (k := GaloisField 2 3) (by omega)
    (by omega)
  have hdvd := card_center_dvd_card_griessHopfMultiplier ⟨hΛ.1⟩ e
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hk] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (by simpa using hdvd))

theorem parabolic_of_equiv {Λ : Type} [Group Λ] [Finite Λ] (hs : IsSimpleGroup Λ) (e : Λ ≃* G8)
    {T J : Subgroup Λ} (hT : IsSylowTwoOf T ⊤) (hle : Subgroup.normalizer (T : Set Λ) ≤ J)
    (hJ : J ≠ ⊤) : pCoreOf 2 J = T := by
  have hcard : Nat.card Λ = 504 := (Nat.card_congr e.toEquiv).trans card_G8
  have h8 : Nat.card (unip.map e.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_unip]
  have h56 : Nat.card (Subgroup.normalizer ((unip.map e.symm.toMonoidHom : Subgroup Λ) :
      Set Λ)) = 56 := by
    rw [← Subgroup.map_equiv_normalizer_eq unip e.symm,
      Subgroup.card_map_of_injective e.symm.injective, card_normalizer_unip]
  rw [eq_of_le_of_card_eq_fiftySix hs hcard (card_normalizer_eq_fiftySix hcard h8 h56 hT) hle
    hJ]
  exact pCoreOf_normalizer_eq hT

end L28Parabolic

theorem kFactL28Parabolic :
    KFactL28Parabolic := by
  intro Λ _ _ hΛ hcase
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hcase
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    let e₁ : Λ ⧸ Subgroup.center Λ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
      e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)
    have hZ : Subgroup.center Λ = ⊥ := L28Parabolic.center_eq_bot hΛ e₁
    refine ⟨hZ, fun T J hT hle hJ => ?_⟩
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hK
    let eΛ : Λ ≃* Λ ⧸ Subgroup.center Λ :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    have : IsSimpleGroup (Λ ⧸ Subgroup.center Λ) := hΛ.2
    exact L28Parabolic.parabolic_of_equiv eΛ.isSimpleGroup
      ((eΛ.trans e₁).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂))
      hT hle hJ
  · omega

end CFSG.AGLEmbedding

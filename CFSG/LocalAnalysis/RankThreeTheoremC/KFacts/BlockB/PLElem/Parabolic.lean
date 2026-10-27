module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.SURank
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviMain
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def ParabolicThreeElemOfRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
    J ≠ Subgroup.normalizer (T : Set Y) →
    (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U

section Free

theorem isElemAbelian_of_map_three {W W₁ : Type*} [Group W] [Group W₁] {ρ : W →* W₁}
    (hcop : Nat.Coprime 3 (Nat.card ρ.ker)) {J : Subgroup W}
    (hE : ∀ U₁ : Subgroup W₁, U₁ ≤ J.map ρ → IsPGroup 3 U₁ → IsElemAbelian 3 U₁) :
    ∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hUJ hU
  have hU1 := hE (U.map ρ) (Subgroup.map_mono hUJ) (hU.map ρ)
  have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 => by
    obtain ⟨e, he⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_of_coprime_three hcop h1 (by simpa using congrArg Subtype.val he)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hc := hU1.1.is_comm.comm ⟨ρ x, x, x.2, rfl⟩ ⟨ρ y, y, y.2, rfl⟩
    have hc' : ρ ((x : W) * (y : W) * ((y : W) * (x : W))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem x.2 y.2) (inv_mem (mul_mem y.2 x.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · exact hinj _ (pow_mem hx 3) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)

theorem isElemAbelian_of_model_two_of_pRank (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y₁ X : Type} [Group Y₁] [Finite Y₁] [Group X] (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X)
    (hρ₁ : Function.Surjective ρ₁) (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker)
    (hX : Subgroup.center X = ⊥) {t : StatedLieTag} {n : ℕ} (hc : StatedClassicalModel X t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y₁) ≤ 3) (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y₁, U ≤ J₁ → IsPGroup 3 U → IsElemAbelian 3 U := by
  have : Finite X := Finite.of_surjective ρ₁ hρ₁
  obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central hρ₁ hk T₁ hNJ hJ hperf
  obtain ⟨Tb, hTb'⟩ := exists_sylow_of_isSylowTwoOf_top hTb
  rw [← hTb'] at hNb hJb
  by_cases htu : t = .PSU
  · subst htu
    obtain ⟨⟨-, -, hn, hne⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := id hc
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    have hn4 : 4 ≤ n := by
      by_contra h4
      exact hne (by rw [show n = 3 by omega]; rfl)
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
    have hB := borelQuotient_su hcard (by omega) ζ hζ e
    obtain ⟨α, hα, hαker⟩ := exists_lift_su hGA hcard hn4 hc hX _ hB.surj
      (fun z hz => hB.ker_central z hz) hY₁ ρ₁ hρ₁ hk h3
    by_cases he : Even n
    · exact isElemAbelian_of_su_even hcard hn4 he α hα hαker T₁ J₁ hNJ hJ hperf
    · exfalso
      have hn5 : 5 ≤ n := by
        rcases Nat.even_or_odd n with h | ⟨k, rfl⟩
        · exact absurd h he
        · omega
      have := four_le_pRank_of_su_hom hcard hn5 α hαker
      omega
  · have ht' : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
      rcases ht with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h htu
    have hb := ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3
      (coprime_three_card_hopfMultiplier_of_model_two hGA hc ht')
    refine isElemAbelian_of_map_three (ρ := ρ₁) (by rw [hb, Subgroup.card_bot]; norm_num) ?_
    rcases ht' with rfl | rfl | rfl | rfl
    · exact isElemAbelian_of_model_psl_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_psp_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaPlus_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaMinus_two hc Tb _ hNb hJb hperfb

end Free

section Small


open CFSG.Blueprint.Multiplier in
theorem isElemAbelian_of_small (hGA : CFSG.Open.GriessAllModelsStatement) {Y₁ X : Type}
    [Group Y₁] [Finite Y₁] [Group X] (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X)
    (hρ₁ : Function.Surjective ρ₁) (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker)
    (hX : Subgroup.center X = ⊥)
    (hsmall : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y₁, U ≤ J₁ → IsPGroup 3 U → IsElemAbelian 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Finite.of_surjective ρ₁ hρ₁
  obtain ⟨hTb, hNb, -, hperfb⟩ := map_overgroup_of_central hρ₁ hk T₁ hNJ hJ hperf
  have hXp : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hρ₁
    exact this.commutator_eq_top
  have hnine : NineFreeOver X → ¬ 9 ∣ Nat.card (J₁.map ρ₁) := fun hNF h9 => by
    have htop := hNF _ _ hTb (Subgroup.le_normalizer.trans hNb) h9
    have hc := hperfb ⊤ htop.ge hXp
    rw [← htop] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc ((dvd_mul_right 3 3).trans h9)
  have hbot : ρ₁.ker = ⊥ → (∀ U : Subgroup X, U ≤ J₁.map ρ₁ → IsPGroup 3 U →
      IsElemAbelian 3 U) → ∀ U : Subgroup Y₁, U ≤ J₁ → IsPGroup 3 U → IsElemAbelian 3 U :=
    fun hb hE => isElemAbelian_of_map_three (by rw [hb, Subgroup.card_bot]; norm_num) hE
  rcases hsmall with ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases hm with rfl | rfl | rfl
    ·
      have hb := eq_bot_of_isPGroup_three_of_dvd_two h3
        (by simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e)
      refine hbot hb (isElemAbelian_of_not_nine_dvd fun h9 => ?_)
      have h60 : Nat.card X = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      have := h9.trans (Subgroup.card_subgroup_dvd_card _)
      rw [h60] at this
      norm_num at this
    ·
      have hk6 : Nat.card ρ₁.ker ∣ 6 := by
        simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e
      have h9 : ¬ 9 ∣ Nat.card (J₁.map ρ₁) :=
        hnine (NineFreeOver.of_mulEquiv e.symm nineFreeOver_alt_six)
      have hZ : Subgroup.center Y₁ = ρ₁.ker := by
        refine le_antisymm (fun z hz => ?_) hk
        have : ρ₁ z ∈ Subgroup.center X := by
          rw [Subgroup.mem_center_iff]
          intro w
          obtain ⟨w, rfl⟩ := hρ₁ w
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
        rw [hX, Subgroup.mem_bot] at this
        exact this
      have hexp : ∀ l : Y₁, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1 := by
        obtain ⟨j, hj⟩ := h3.exists_card_eq
        have hj1 : j ≤ 1 := by
          by_contra hj1
          have := (pow_dvd_pow 3 (show 2 ≤ j by omega)).trans (hj ▸ hk6)
          norm_num at this
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · intro l ⟨k, hlk⟩
          have hb : ρ₁.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
          have hperm :
              ((e (ρ₁ l) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 3 ^ k = 1 := by
            rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hlk, map_one, map_one, Subgroup.coe_one]
          have h3' := perm_fin_six_pow_three_eq_one hperm
          have : ρ₁ (l ^ 3) = 1 := by
            apply e.injective
            rw [map_pow, map_pow, map_one]
            exact Subtype.ext (by simpa using h3')
          have hmem : l ^ 3 ∈ ρ₁.ker := this
          rw [hb, Subgroup.mem_bot] at hmem
          exact hmem
        · exact kFactThreeASixExpThree_holds Y₁ (by rw [hZ, hj, pow_one])
            ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
              ((QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁).trans e)⟩
      intro U hUJ hU
      refine ⟨?_, fun x hx => hexp x ?_⟩
      · let f : U →* U.map ρ₁ := (ρ₁.comp U.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
        have hcard := card_dvd_three_of_not_nine_dvd h9 (Subgroup.map_mono hUJ) (hU.map ρ₁)
        have : IsCyclic (U.map ρ₁) := by
          rcases (Nat.dvd_prime Nat.prime_three).1 hcard with h1 | h1
          · have : Subsingleton (U.map ρ₁) := (Nat.card_eq_one_iff_unique.1 h1).1
            exact isCyclic_of_subsingleton
          · exact isCyclic_of_prime_card h1
        refine f.isMulCommutative_of_isCyclic_of_ker_le_center fun u hu => ?_
        have hu1 : ρ₁ (u : Y₁) = 1 := congrArg Subtype.val hu
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_center_iff.1 (hk hu1) w)
      · obtain ⟨k, hk'⟩ := hU ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk'⟩
    ·
      have hb := eq_bot_of_isPGroup_three_of_dvd_two h3
        (by simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e)
      exact hbot hb fun U _ hU => isElemAbelian_three_of_map_injective (f := e.toMonoidHom)
        e.injective (isElemAbelian_alt_eight _ (hU.map _))
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
      have hc := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at hc
      have hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
      exact hbot (ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3 hM)
        (isElemAbelian_of_not_nine_dvd (hnine (nineFreeOver_catalog_seven hq rfl e)))
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
      have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at hc
      have hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
      exact hbot (ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3 hM)
        (isElemAbelian_of_not_nine_dvd (hnine (nineFreeOver_catalog_psu_three_three hq rfl e)))

end Small

section Main


theorem parabolicThreeElemOfRank_of (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabolicThreeElemOfRank := by
  intro Y _ _ hY hcl hr T J hT hNJ hJ hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have : Group.IsPerfect Y := ⟨hY.1⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 3 with hOdef
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (primeComplementCore_coprime 3)
  rcases le_center_or_eq_top_of_normal_quasisimple hY O with hO | hO
  · have hρ₀ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
    have hker₀ : (QuotientGroup.mk' O).ker = O := QuotientGroup.ker_mk' O
    refine isElemAbelian_of_map_three (ρ := QuotientGroup.mk' O)
      (by rw [hker₀]; exact primeComplementCore_coprime 3) ?_
    obtain ⟨hT₁, hN₁, hJ₁, hperf₁⟩ :=
      map_overgroup_of_central hρ₀ (hker₀.le.trans hO) S hNJ hJ hperf
    obtain ⟨S₁, hS₁⟩ := exists_sylow_of_isSylowTwoOf_top hT₁
    rw [← hS₁] at hN₁ hJ₁
    have hY₁ : Group.IsPerfect (Y ⧸ O) := Group.IsPerfect.ofSurjective hρ₀
    have hX := center_centerQuotient_eq_bot hY
    have hr₁ : CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ O)) ≤ 3 := by
      rw [CFSG.SectionRank.pRank_quotient_eq O hO3]
      exact hr
    obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central
      (QuotientGroup.mk'_surjective (Subgroup.center Y)) (QuotientGroup.ker_mk' _).le S hNJ hJ
      hperf
    rcases kFactParabolicThreeCensus _ hcl _ _ hTb hNb hJb hperfb with ⟨d, hd, ⟨e⟩⟩ | hsmall
    · obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
      exact isElemAbelian_of_model_two_of_pRank hGA hY₁ _ (quotCenterOfLeCenter_surjective hO)
        (ker_quotCenterOfLeCenter_le_center hO) (isPGroup_ker_quotCenterOfLeCenter hO) hX hc ht
        hr₁ S₁ _ hN₁ hJ₁ hperf₁
    · exact isElemAbelian_of_small hGA hY₁ _ (quotCenterOfLeCenter_surjective hO)
        (ker_quotCenterOfLeCenter_le_center hO) (isPGroup_ker_quotCenterOfLeCenter hO) hX hsmall
        S₁ _ hN₁ hJ₁ hperf₁
  · intro U _ hU
    refine isElemAbelian_of_card_dvd_three ?_
    have hcop : Nat.Coprime 3 (Nat.card (⊤ : Subgroup Y)) := hO ▸ primeComplementCore_coprime 3
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    have hdvd : Nat.card U ∣ Nat.card (⊤ : Subgroup Y) := Subgroup.card_dvd_of_le le_top
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · norm_num
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem

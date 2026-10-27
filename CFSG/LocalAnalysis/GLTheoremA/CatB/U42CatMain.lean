module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatAct
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatLift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatRank
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem commute_of_inf_commute {A : Type*} [Group A] {U N : Subgroup A} [N.Normal] (hU : IsPGroup 2 ↥U)
    {ε : A} (hε : ε ^ 3 = 1) (hεN : ε ∈ N) (hεU : ε ∈ Subgroup.normalizer (U : Set A))
    (hcomm : ∀ c ∈ U ⊓ N, ε * c = c * ε) {u : A} (hu : u ∈ U) : ε * u = u * ε := by
  set c := u * ε * u⁻¹ * ε⁻¹ with hc
  have hcN : c ∈ N := by
    have h1 : u * ε * u⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance ε hεN u
    exact N.mul_mem h1 (N.inv_mem hεN)
  have hcU : c ∈ U := by
    have h1 : ε * u⁻¹ * ε⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hεU _).1 (U.inv_mem hu)
    have e : c = u * (ε * u⁻¹ * ε⁻¹) := by simp only [hc]; group
    rw [e]
    exact U.mul_mem hu h1
  have hcε : ε * c = c * ε := hcomm c ⟨hcU, hcN⟩
  have h2 : c * ε = u * ε * u⁻¹ := by simp only [hc]; group
  have h3 : (c * ε) ^ 3 = 1 := by
    rw [h2, conj_pow, hε]
    group
  have h4 : (c * ε) ^ 3 = c ^ 3 * ε ^ 3 := Commute.mul_pow (show Commute c ε from hcε.symm) 3
  rw [h4, hε, mul_one] at h3
  have hc1 : c = 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU ⟨c, hcU⟩
    have hk' : orderOf c = 2 ^ k := by simpa using hk
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [hk'] at hdvd
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact hk'
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd) (by norm_num)
  have h5 : u * ε * u⁻¹ * ε⁻¹ = 1 := hc1
  have h6 : u * ε = ε * u :=
    calc u * ε = (u * ε * u⁻¹ * ε⁻¹) * ε * u := by group
      _ = ε * u := by rw [h5]; group
  exact h6.symm

theorem u42CatAt_of_slevel (h1 : U42E81At) (h2 : U42E27At) (h3 : U42RankAt) (G : Type) [Group G]
    [Finite G] : U42CatAt G := by
  intro B x L D K hS hB4 hL hinner hStd hK hT₀
  obtain ⟨T₀, hT₀C, hT₀2, hT₀B, hT₀ne, hT₀O⟩ := hT₀
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL' : catalogIs (PSimple 3 L) IsU42Host := hL
  have hBm := IsSStarMax.bmax hS
  have hBe : IsElemAbelian 3 B := hBm.1
  have hBcard : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hBm.2.1
  obtain ⟨hxB, hx1, -⟩ := IsSStarMax.essential hS
  have hcomp := IsSStarMax.component hS
  have hBN := IsSStarMax.normalizes hS
  have hcyc := IsSStarMax.cycMod hS
  have hxo : orderOf x = 3 := orderOf_eq_prime (hBe.2 x hxB) hx1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
    IsSTriple.mem_centralizer ⟨hBm, IsSStarMax.essential hS, hcomp⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hBC : B ≤ C := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBe hb hxB)
  have hB3 : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hBe
  obtain ⟨ρ, hρ, hρker, hρcard, hρelem⟩ := exists_act hS hinner
  set E := ρ.range with hE
  have hE27 : 3 ^ 3 ≤ Nat.card E := by
    have : 3 ^ 4 ≤ 3 * Nat.card E := by rw [hρcard]; exact hB4
    omega
  have hEp : IsPGroup 3 ↥E := isPGroup_of_isElemAbelian hρelem
  have hnc : ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup 3 ↥Q ∧ ¬ IsCyclic ↥Q := by
    obtain ⟨Q, hQp, hQnc⟩ := exists_noncyclic_pSubgroup_of_surjective (p := 3) (chevQuotHom 3 L)
      (chevQuotHom_surjective 3 L) hEp
      (not_isCyclic_of_exponent Nat.prime_three hρelem.2 (by omega))
    refine ⟨Q.map L.subtype, Subgroup.map_subtype_le Q, hQp.map _, fun hcyc' => hQnc ?_⟩
    exact (Subgroup.equivMapOfInjective Q L.subtype L.subtype_injective).isCyclic.2 hcyc'
  have hCN : C ≤ Subgroup.normalizer (L : Set G) :=
    cent_le_normalizer Nat.prime_three hcomp hcyc hnc
  set Φ := actC L hCN with hΦ
  set U : Subgroup (MulAut (PSimple 3 L)) := (T₀.subgroupOf C).map Φ with hU
  have hU2 : IsPGroup 2 ↥U := by
    have h1 : IsPGroup 2 ↥(T₀.subgroupOf C) :=
      hT₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀C).symm
    exact h1.map Φ
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hT₀O
    intro t ht
    have htC : t ∈ C := hT₀C ht
    have hΦt : Φ ⟨t, htC⟩ = 1 := by
      have : Φ ⟨t, htC⟩ ∈ U := ⟨⟨t, htC⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have htm : t ∈ centModSubgroup 3 L := (mem_ker_actC hcomp hCN ⟨t, htC⟩).1 hΦt
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT₀2 ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by
      have : orderOf t = 2 ^ k := by simpa using hk
      rw [← this]
      exact pow_orderOf_eq_one t
    exact isTwoElem_mem_core hcomp hcyc hxo hxL hCN htC htm htk
  have hΦb : ∀ b : ↥B, Φ ⟨b, hBC b.2⟩ = MulAut.conj (ρ b) := fun b => hρ b
  have hUnorm : ∀ b : ↥B, MulAut.conj (ρ b) ∈ Subgroup.normalizer (U : Set (MulAut (PSimple 3 L))) := by
    intro b
    rw [← hΦb b]
    have hbN : (⟨b, hBC b.2⟩ : ↥C) ∈
        Subgroup.normalizer ((T₀.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.1 (hT₀B b.2) (t : G)
    exact Subgroup.le_normalizer_map Φ ⟨_, hbN, rfl⟩
  have hEnorm : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (U : Set (MulAut (PSimple 3 L))) := by
    rintro _ ⟨b, rfl⟩
    exact hUnorm b
  by_cases hbig : 3 ^ 5 ≤ Nat.card B
  ·
    exfalso
    have hE81 : 3 ^ 4 ≤ Nat.card E := by
      have : 3 ^ 5 ≤ 3 * Nat.card E := by rw [hρcard]; exact hbig
      omega
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hEp hE81
    set E' : Subgroup (PSimple 3 L) := K'.map E.subtype with hE'
    have hE'E : E' ≤ E := Subgroup.map_subtype_le K'
    refine hUne (h1 (PSimple 3 L) hL' E' (isElemAbelian_mono hρelem hE'E) ?_ U hU2
      (fun e he => hEnorm e (hE'E he)))
    rw [hE', Subgroup.card_map_of_injective E.subtype_injective, hK']
  · push Not at hbig
    have hTLR : GLATwoLocalRank 3 G = 4 := by
      have hm : 3 ^ 4 ≤ 3 ^ GLATwoLocalRank 3 G := hBcard ▸ hB4
      have hm' : 3 ^ GLATwoLocalRank 3 G < 3 ^ 5 := hBcard ▸ hbig
      have h4 : 4 ≤ GLATwoLocalRank 3 G := (Nat.pow_le_pow_iff_right (by norm_num)).1 hm
      have h5 : GLATwoLocalRank 3 G < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hm'
      omega
    have hB81 : Nat.card B = 3 ^ 4 := by rw [hBcard, hTLR]
    have hE27' : Nat.card E = 3 ^ 3 := by
      have : 3 * Nat.card E = 3 ^ 4 := by rw [hρcard, hB81]
      omega
    by_cases hcent : ∀ u ∈ U, ∀ b : ↥B, MulAut.conj (ρ b) * u = u * MulAut.conj (ρ b)
    ·
      exfalso
      obtain ⟨t, ht, b, hb, hne⟩ : ∃ t ∈ T₀, ∃ b ∈ B, ⁅t, b⁆ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hT₀ne
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have h := hcon t ht b hb
        rw [commutatorElement_def] at h
        have : t * b = b * t :=
          calc t * b = (t * b * t⁻¹ * b⁻¹) * (b * t) := by group
            _ = b * t := by rw [h, one_mul]
        exact this.symm
      have hbt : b * t⁻¹ * b⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.1 (hT₀B hb) _).1 (T₀.inv_mem ht)
      have hcT : ⁅t, b⁆ ∈ T₀ := by
        rw [commutatorElement_def]
        have e : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
        rw [e]
        exact T₀.mul_mem ht hbt
      have hcC : ⁅t, b⁆ ∈ C := hT₀C hcT
      have htC : t ∈ C := hT₀C ht
      have hbC : b ∈ C := hBC hb
      have hΦc : Φ ⟨⁅t, b⁆, hcC⟩ = 1 := by
        have e : (⟨⁅t, b⁆, hcC⟩ : ↥C) = ⟨t, htC⟩ * ⟨b, hbC⟩ * ⟨t, htC⟩⁻¹ * ⟨b, hbC⟩⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hΦt : Φ ⟨t, htC⟩ ∈ U := ⟨⟨t, htC⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
        have hcomm := hcent _ hΦt ⟨b, hb⟩
        rw [hΦb ⟨b, hb⟩]
        generalize Φ ⟨t, htC⟩ = a at hcomm ⊢
        generalize MulAut.conj (ρ ⟨b, hb⟩) = c at hcomm ⊢
        rw [← hcomm]
        group
      have hcm : ⁅t, b⁆ ∈ centModSubgroup 3 L := (mem_ker_actC hcomp hCN ⟨⁅t, b⁆, hcC⟩).1 hΦc
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT₀2 ⟨⁅t, b⁆, hcT⟩
      have hck : orderOf ⁅t, b⁆ = 2 ^ k := by simpa using hk
      have hcO : ⁅t, b⁆ ∈ GLAPPrimeCoreOf 3 C :=
        isTwoElem_mem_core hcomp hcyc hxo hxL hCN hcC hcm
          (by rw [← hck]; exact pow_orderOf_eq_one _)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hck
        exact hne hck
      have heven : Even (Nat.card (GLAPPrimeCoreOf 3 C)) := by
        have h1 : orderOf ⁅t, b⁆ ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
          Subgroup.orderOf_dvd_natCard _ hcO
        rw [hck] at h1
        exact even_iff_two_dvd.2 ((dvd_pow_self 2 hk0).trans h1)
      obtain ⟨W, hWle, hWe, hWc⟩ := exists_rank_five h3 hcomp hxL hxo hL'
      have hWC : W ≤ C := hWle.trans (sup_le hcomp.1 (Subgroup.zpowers_le.2 hxC))
      have hWY : W ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G) :=
        hWC.trans (le_normalizer_glaPPrimeCoreOf 3 C)
      have hcop : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
          (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three C)
      obtain ⟨T, hTne, -, hT2, hWT⟩ := exists_twoGroup_normalized_of_coprime_even Nat.prime_three
        (by norm_num) (isPGroup_of_isElemAbelian hWe) hWY hcop heven
      have h4 := pRank_le_glaTwoLocalRank_of_normalizes (p := 3) Nat.prime_three hTne hT2 hWT
      have h5 : 5 ≤ CFSG.Open.pRank 3 W :=
        CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hWe hWc
      rw [hTLR] at h4
      omega
    ·
      push Not at hcent
      obtain ⟨u, huU, b0, hu⟩ := hcent
      have hκ := conj_injective_pSimple hcomp
      set U₀ : Subgroup (PSimple 3 L) :=
        U.comap (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)) with hU₀
      have hU₀2 : IsPGroup 2 ↥U₀ := hU2.comap_of_injective _ hκ
      have hEU₀ : E ≤ Subgroup.normalizer (U₀ : Set (PSimple 3 L)) := by
        intro e he
        rw [Subgroup.mem_normalizer_iff]
        intro s
        simp only [hU₀, Subgroup.mem_comap, map_mul, map_inv]
        exact Subgroup.mem_normalizer_iff.1 (hEnorm e he) _
      haveI hNnormal : (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)).range.Normal := ⟨by
        rintro _ ⟨s, rfl⟩ g
        refine ⟨g s, ?_⟩
        ext z
        simp [MulAut.conj_apply]⟩
      have hcomm₀ : (⁅U₀, E⁆ : Subgroup (PSimple 3 L)) ≠ ⊥ := by
        intro hbot
        apply hu
        have hcen : U₀ ≤ Subgroup.centralizer (E : Set (PSimple 3 L)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
        refine commute_of_inf_commute
          (N := (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)).range) hU2 ?_ ⟨ρ b0, rfl⟩
          (hUnorm b0) ?_ huU
        · rw [← map_pow, hρelem.2 (ρ b0) ⟨b0, rfl⟩, map_one]
        · rintro c ⟨hcU, s, rfl⟩
          have hsU₀ : s ∈ U₀ := hcU
          have := Subgroup.mem_centralizer_iff.1 (hcen hsU₀) (ρ b0) ⟨b0, rfl⟩
          rw [← map_mul, ← map_mul, this]
      have hD : Nat.card D = 3 ^ 2 := hStd.2.2.1
      obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
        by_contra hcon
        push Not at hcon
        have hle : D ≤ Subgroup.zpowers x := fun d hd => hcon d hd
        have := Subgroup.card_le_of_le hle
        rw [hD, Nat.card_zpowers, hxo] at this
        omega
      have hDB : D ≤ B := hStd.1
      set d' : ↥B := ⟨d, hDB hdD⟩ with hd'
      have hs1 : ρ d' ≠ 1 := fun h => hdx ((hρker d').1 h)
      have hsE : ρ d' ∈ E := ⟨d', rfl⟩
      have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) := hStd.2.2.2.2.2.1
      have hKL : K ≤ L := hKcomp.1.trans inf_le_left
      have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
      have hKd : K ≤ Subgroup.centralizer ({(d' : G)} : Set G) :=
        hKcomp.1.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD)))
      have hBK : B ≤ Subgroup.normalizer (K : Set G) := by
        have hbcs : ∀ b ∈ B, b ∈ Subgroup.centralizer (D : Set G) := fun b hb => by
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          exact isElemAbelian_commute hBe (hDB hd) hb
        have hBX : B ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
          fun b hb => S12.mem_normalizer_inf' (hBN hb) (Subgroup.le_normalizer (hbcs b hb))
        intro b hb
        rw [hStd.2.2.2.2.1]
        exact S12.mem_normalizer_glaLayer' (hBX hb)
      haveI : IsSimpleGroup (PSimple 3 K) := S10.isSimple_of_isU4two hK
      have hKs : Nontrivial (PSimple 3 K) := inferInstance
      obtain ⟨f, hf⟩ := exists_surj_chevTransfer hKL hKq
      obtain ⟨T', hT'K, hT'2, hT'E, hT'c, hT'8, hT'z⟩ := h2 (PSimple 3 L) hL' E U₀ hρelem hE27' hU₀2
        hEU₀ hcomm₀ (ρ d') hsE hs1 (chevTransfer 3 L K) (chevTransfer_le_centralizer hBN hρ hKd)
        (isPerfect_chevTransfer hKL hKq) ⟨PSimple 3 K, inferInstance, hK, f, hf⟩
      have hT'N : ∀ b : ↥B, ρ b ∈ Subgroup.normalizer (T' : Set (PSimple 3 L)) :=
        fun b => hT'E ⟨b, rfl⟩
      have hT'a : ∃ (b : ↥B) (t : PSimple 3 L), t ∈ T' ∧ ρ b * t * (ρ b)⁻¹ ≠ t := by
        by_contra hcon
        push Not at hcon
        apply hT'c
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        rintro e ⟨b, rfl⟩
        have h := hcon b t ht
        calc ρ b * t = ρ b * t * (ρ b)⁻¹ * ρ b := by group
          _ = t * ρ b := by rw [h]
      obtain ⟨T, hTK, hT2', hTB, hTc, hTcard, hTO⟩ :=
        exists_T_of_T' hBN hρ hB3 hKL hKq hBK hKs hT'K hT'2 hT'N hT'a hT'z
      exact ⟨T, hTK, hT2', hTB, hTc, lt_of_lt_of_le hT'8 hTcard, hTO⟩

theorem u42CatAt_of_sLevel (h : U42SLevel) (G : Type) [Group G] [Finite G] : U42CatAt G :=
  u42CatAt_of_slevel h.e81 h.e27 h.rank G

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end

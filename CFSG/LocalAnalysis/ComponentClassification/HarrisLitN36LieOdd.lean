module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Alt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieSel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36MType

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank

theorem pPrimeCore_eq_center_of_quasisimple {L : Type*} [Group L] (hq : IsQuasisimple L)
    [IsSimpleGroup (L ⧸ pPrimeCore 2 L)] (hna : ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a) :
    pPrimeCore 2 L = center L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · rcases LocalCores.quasisimple_normal_subgroups hq (pPrimeCore_normal (p := 2) (G := L)) with
      htop | hle
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      have ha : (QuotientGroup.mk a : L ⧸ pPrimeCore 2 L) = 1 :=
        (QuotientGroup.eq_one_iff a).mpr (htop ▸ mem_top a)
      have hb : (QuotientGroup.mk b : L ⧸ pPrimeCore 2 L) = 1 :=
        (QuotientGroup.eq_one_iff b).mpr (htop ▸ mem_top b)
      exact hab (by rw [ha, hb])
    · exact hle
  · intro z hz
    have hs : center (L ⧸ pPrimeCore 2 L) = ⊥ := CatLeaf.center_eq_bot_of_simple hna
    have hc : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hz w)]
    rw [hs, mem_bot] at hc
    exact (QuotientGroup.eq_one_iff z).mp hc

theorem ne_of_psl_two_eight {q : ℕ} (hq7 : 7 ≤ q) : q * (q ^ 2 - 1) ≠ 1008 := by
  intro h
  have hq : q ≤ 10 := by
    by_contra hgt
    have h11 : 11 ≤ q := by omega
    have : 11 * (11 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h11 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h11 2) 1)
    omega
  interval_cases q <;> norm_num at h

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem quotAut_sq_and_ne_one (h : Config G p m τ K) :
    quotAut τ * quotAut τ = 1 ∧ quotAut τ ≠ 1 := by
  have hσ2 := h.orderOf_bar
  refine ⟨by rw [← pow_two, ← hσ2, pow_orderOf_eq_one], fun h1 => ?_⟩
  rw [h1, orderOf_one] at hσ2
  exact absurd hσ2 (by norm_num)

theorem bar_conj_mem (h : Config G p m τ K) :
    ∀ c ∈ fixedPoints (quotAut τ), ∀ l ∈ K.map (QuotientGroup.mk' (center G)),
      c * l * c⁻¹ ∈ K.map (QuotientGroup.mk' (center G)) := by
  intro c hc l hl
  have h1 := h.bar_normal.conj_mem ⟨l, h.isTwoComponentIn_bar.1 hl⟩
    (by rw [mem_subgroupOf]; exact hl) ⟨c, hc⟩
  rw [mem_subgroupOf] at h1
  exact h1

theorem quasisimple_bar_of_oddLie
    (h : Config G p m τ K) {t : StatedLieTag} {n r f : ℕ}
    (hr2 : r ≠ 2) (hL : Blueprint.LieModel (G ⧸ center G) t n r f) :
    IsQuasisimple ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
      (fixedPoints (quotAut τ))) := by
  have := h.simple_bar
  have hadm := admissible_of_lieModel' hL
  obtain ⟨hσσ, hσ1⟩ := h.quotAut_sq_and_ne_one
  have hc := h.isTwoComponentIn_bar
  exact CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType h.nonabelian_bar
    ⟨t, n, r, f, hadm.1, hr2, hadm, hL⟩ (quotAut τ) hσσ hσ1 _ ((isTwoComponentIn_iff hc.1).mp hc)

theorem bar_center_facts (h : Config G p m τ K)
    (hq : IsQuasisimple ↥(K.map (QuotientGroup.mk' (center G)))) :
    pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center G))) =
        center ↥(K.map (QuotientGroup.mk' (center G))) ∧
      Blueprint.LieModel (↥(K.map (QuotientGroup.mk' (center G))) ⧸
        center ↥(K.map (QuotientGroup.mk' (center G)))) .PSL 2 p m ∧
      Odd (Nat.card ↥(center ↥(K.map (QuotientGroup.mk' (center G))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLb := h.lieModel_bar
  have := isSimpleGroup_of_lieModel_psl2 hLb
  have hOZ := pPrimeCore_eq_center_of_quasisimple hq (nonabelian_of_lieModel_psl2 hLb)
  refine ⟨hOZ, GSThmB.OddQuot.lieModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hOZ) hLb, ?_⟩
  rw [← hOZ]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))

theorem concl_of_charP (hD : L4U4PartialCoverFact) (hGA : TBLit.GriessMultipliersAllModels)
    (h : Config G p m τ K) (hq : IsQuasisimple ↥(K.map (QuotientGroup.mk' (center G))))
    {t : StatedLieTag} {n f : ℕ} (hL : Blueprint.LieModel (G ⧸ center G) t n p f) :
    Concl G p m τ := by
  have := h.simple_bar
  obtain ⟨-, hLZ, hZodd⟩ := h.bar_center_facts hq
  have hKC := h.isTwoComponentIn_bar.1
  have hconj := h.bar_conj_mem
  have h7 := h.seven_le
  have hcase : ∀ k : ℕ, (Blueprint.LieModel (G ⧸ center G) .PSL 4 p k ∨
      Blueprint.LieModel (G ⧸ center G) .PSU 4 p k) → Concl G p m τ := fun k hk =>
    Or.inr (Or.inr (Or.inr ⟨k, hD G h.quasisimple h.oddCore h.not_simple p k h.prime h.ne_two hk
      h.not_mType τ h.orderOf_eq m h.one_le h.sixteen_dvd K h.comp h.unique h.lieModel, hk⟩))
  obtain ⟨n', k', hPSL | hPSU⟩ := h.exists_even_model hL
  · obtain ⟨hmod, hne⟩ := hPSL
    have hadm := admissible_of_lieModel' hmod
    have hk' : 1 ≤ k' := hadm.2.1
    have hn2 : 2 ≤ 2 * n' := hadm.2.2.1
    rcases (by omega : n' = 1 ∨ n' = 2 ∨ 3 ≤ n') with rfl | rfl | hn3
    ·
      exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hm' : Models.LieModel (G ⧸ center G) .PSL 2 p k' :=
        GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hmod
      have hcardM := GH74.Generic.card_hopfMultiplier_of_griess hGA hm'
      have hdvd := GH74.Generic.card_center_dvd_hopfMultiplier h.quasisimple (MulEquiv.refl _)
      rw [hcardM] at hdvd
      have hp2 := h.ne_two
      have hodd : Odd ((Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').1 *
          (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').2) := by
        have hexc : Odd (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').1 ∧
            Odd (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').2 := by
          unfold Blueprint.Multiplier.exceptionalOrders
          split <;> simp_all
          all_goals decide
        exact hexc.1.mul hexc.2
      have hgcd : Nat.gcd (2 * 1) (p ^ k' - 1) = 2 := by
        obtain ⟨i, hi⟩ : Odd (p ^ k') := (h.prime.odd_of_ne_two hp2).pow
        rw [mul_one, hi, Nat.add_sub_cancel]
        exact Nat.gcd_eq_left ⟨i, rfl⟩
      have hgen : (Blueprint.Multiplier.genericOrders .PSL 2 p k').1 = 2 := by
        simpa [Blueprint.Multiplier.genericOrders] using hgcd
      have hgen2 : (Blueprint.Multiplier.genericOrders .PSL 2 p k').2 = 1 := by
        simp [Blueprint.Multiplier.genericOrders]
      rw [hgen, hgen2, mul_one] at hdvd
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h.center_isPGroup
      have hj1 : j ≤ 1 := by
        rw [hj] at hdvd
        have hcop : Nat.Coprime (2 ^ j) ((Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').1 *
            (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').2) :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
        have h2 := hcop.dvd_of_dvd_mul_right hdvd
        have h3 : 2 ^ j ∣ 2 ^ 1 := by rwa [pow_one]
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h3
      have hj0 : j ≠ 0 := by
        rintro rfl
        apply h.center_ne_bot
        rw [pow_zero] at hj
        exact Subgroup.eq_bot_of_card_eq _ hj
      obtain rfl : j = 1 := by omega
      exact hne (by rw [hj, pow_one, hgcd])
    · exact hcase k' (Or.inl hmod)
    · exfalso
      exact false_of_psl_ge_five_of_component h.nonabelian_bar (by omega) h.prime h.ne_two
        (statedClassicalModel_of_lieModel' (.inl rfl) hmod) h.ne_two h.orderOf_bar hKC hconj hq
        hLZ hZodd
  · obtain ⟨hmod, hne⟩ := hPSU
    have hadm := admissible_of_lieModel' hmod
    have hk' : 1 ≤ k' := hadm.2.1
    have hn3 : 3 ≤ 2 * n' := hadm.2.2.1
    rcases (by omega : n' = 2 ∨ 3 ≤ n') with rfl | hn3
    · exact hcase k' (Or.inr hmod)
    · exfalso
      exact false_of_psu_ge_five_of_component h.nonabelian_bar (by omega) h.prime h.ne_two hk'
        (statedClassicalModel_of_lieModel' (.inr rfl) hmod) h.prime h.ne_two h.one_le
        (by omega) h.orderOf_bar hKC hconj hq hLZ hZodd

theorem concl_of_oddLie
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hC : PSLTwoOddCharacteristicFact) (hD : L4U4PartialCoverFact)
    (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p m τ K) {t : StatedLieTag}
    {n r f : ℕ} (hr2 : r ≠ 2) (hL : Blueprint.LieModel (G ⧸ center G) t n r f) :
    Concl G p m τ := by
  have := h.simple_bar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := K.map (QuotientGroup.mk' (center G)) with hKbdef
  have hKC := h.isTwoComponentIn_bar.1
  have hadm := admissible_of_lieModel' hL
  set C' := FixedCommutingProduct.fixedSubgroup (quotAut τ) with hC'
  have hKC' : Kb ≤ C' := hKC
  have hqL : IsQuasisimple ↥(Kb.subgroupOf C') := h.quasisimple_bar_of_oddLie hr2 hL
  let eS : ↥(Kb.subgroupOf C') ≃* ↥Kb := subgroupOfEquivOfLe hKC'
  have hq : IsQuasisimple ↥Kb := LocalCores.isQuasisimple_of_mulEquiv eS hqL
  obtain ⟨hOZ, hLZ, -⟩ := h.bar_center_facts hq
  have hcS : (center ↥(Kb.subgroupOf C')).map (eS : ↥(Kb.subgroupOf C') →* ↥Kb) =
      center ↥Kb := Subgroup.map_center_eq eS
  let eQ := QuotientGroup.congr _ _ eS hcS
  have hLm : Blueprint.LieModel (↥(Kb.subgroupOf C') ⧸ center ↥(Kb.subgroupOf C')) .PSL 2 p m :=
    GSThmB.OddQuot.lieModel_of_equiv eQ.symm hLZ
  have hpc : IsPComponent 2 (Kb.subgroupOf C') :=
    (isTwoComponentIn_iff hKC).mp h.isTwoComponentIn_bar
  have hcomp : IsComponent (Kb.subgroupOf C') := by
    obtain ⟨-, -, hsub, -⟩ := hpc
    exact ⟨hqL, hsub⟩
  have hrp : r = p := by
    rcases hGLS _ t n r f hadm.1 hr2 hadm hL (quotAut τ) h.orderOf_bar (Kb.subgroupOf C') hcomp
      with ⟨τ', n', f', -, hm'⟩ | ⟨-, -, -, h8⟩
    · exact hC _ p m τ' n' r f' h.prime h.ne_two h.seven_le hr2 hLm hm'
    ·
      exfalso
      have hs8 := isSimpleGroup_of_lieModel_psl2 h8
      have : IsSimpleGroup ↥Kb := eS.symm.isSimpleGroup
      have h504 : Nat.card ↥(Kb.subgroupOf C') = 504 := by
        rw [GH74.card_of_lieModel_PSL (by norm_num) h8]
        decide
      have hZ : center ↥Kb = ⊥ := by
        obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 h8
        exact CatLeaf.center_eq_bot_of_simple
          ⟨eS a, eS b, fun hc => hab (eS.injective (by rw [map_mul, map_mul, hc]))⟩
      have hcardq : Nat.card (↥Kb ⧸ pPrimeCore 2 ↥Kb) = 504 := by
        rw [hOZ, hZ, Nat.card_congr (QuotientGroup.quotientBot (G := ↥Kb)).toEquiv,
          ← Nat.card_congr eS.toEquiv, h504]
      have hNq := h.card_quot_bar
      rw [hcardq] at hNq
      exact ne_of_psl_two_eight h.seven_le hNq.symm
  rw [hrp] at hL
  exact h.concl_of_charP hD hGA hq hL

end Config

end CFSG.ComponentClassification.HarrisLit.N36

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KSylowTwo

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLevi

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal coprime_card_relPPrimeCore relPPrimeCore_eq_map)

variable {A : Type} [Group A] [Finite A]

noncomputable def pSectionTop (p : ℕ) (X : Subgroup A) : Subgroup A :=
  rankThreePrimeCore p X ⊔ closure {x : A | x ∈ X ∧ orderOf x = p}

theorem conj_mem_of_normal {N X : Subgroup A} (h : (N.subgroupOf X).Normal) {x n : A}
    (hx : x ∈ X) (hn : n ∈ N) (hnX : n ∈ X) : x * n * x⁻¹ ∈ N := by
  have := h.conj_mem ⟨n, hnX⟩ (mem_subgroupOf.mpr hn) ⟨x, hx⟩
  simpa [mem_subgroupOf] using this

theorem normal_of_conj {N X : Subgroup A} (h : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    (N.subgroupOf X).Normal :=
  ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using h g g.2 n hn⟩

theorem conj_mem_closure {S : Set A} {g : A} (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) {h : A}
    (hh : h ∈ closure S) : g * h * g⁻¹ ∈ closure S := by
  induction hh using Subgroup.closure_induction with
  | mem s hs => exact subset_closure (hS s hs)
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

variable {p : ℕ}

theorem core_le (X : Subgroup A) : rankThreePrimeCore p X ≤ X := relPPrimeCore_le X

theorem pSectionTop_le (X : Subgroup A) : pSectionTop p X ≤ X :=
  sup_le (core_le X) ((closure_le X).mpr fun _ hx => hx.1)

theorem core_le_top (X : Subgroup A) : rankThreePrimeCore p X ≤ pSectionTop p X := le_sup_left

theorem gen_mem_top {X : Subgroup A} {x : A} (hx : x ∈ X) (ho : orderOf x = p) :
    x ∈ pSectionTop p X :=
  le_sup_right (a := rankThreePrimeCore p X) (subset_closure ⟨hx, ho⟩)

theorem not_dvd_card_core (hp : p.Prime) (X : Subgroup A) :
    ¬ p ∣ Nat.card (rankThreePrimeCore p X) := fun h =>
  hp.one_lt.ne' ((coprime_card_relPPrimeCore hp X).eq_one_of_dvd h)

theorem core_conj (hp : p.Prime) {X : Subgroup A} {x n : A} (hx : x ∈ X)
    (hn : n ∈ rankThreePrimeCore p X) : x * n * x⁻¹ ∈ rankThreePrimeCore p X :=
  conj_mem_of_normal (relPPrimeCore_normal hp X) hx hn (core_le X hn)

theorem top_eq_closure (X : Subgroup A) : pSectionTop p X =
    closure ((rankThreePrimeCore p X : Set A) ∪ {x : A | x ∈ X ∧ orderOf x = p}) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq]; rfl

theorem top_conj (hp : p.Prime) {X : Subgroup A} {x h : A} (hx : x ∈ X)
    (hh : h ∈ pSectionTop p X) : x * h * x⁻¹ ∈ pSectionTop p X := by
  rw [top_eq_closure] at hh ⊢
  refine conj_mem_closure ?_ hh
  rintro s (hs | ⟨hsX, hso⟩)
  · exact Or.inl (core_conj hp hx hs)
  · refine Or.inr ⟨mul_mem (mul_mem hx hsX) (inv_mem hx), ?_⟩
    have hsc : SemiconjBy x s (x * s * x⁻¹) := by unfold SemiconjBy; group
    rw [← hso]; exact (hsc.orderOf_eq).symm

theorem not_mem_of_orderOf {N : Subgroup A} {y : A} (hy : y ∈ N) (hpN : ¬ p ∣ Nat.card N)
    (ho : orderOf y = p) : False := by
  apply hpN
  rw [← ho, ← Subgroup.orderOf_mk y hy]
  exact orderOf_dvd_natCard _

theorem relIndex_eq_of_sup_eq {Y W M : Subgroup A} (hWY : W ≤ Y) (hWn : (W.subgroupOf Y).Normal)
    (hMY : M ≤ Y) (h : M ⊔ W = Y) : W.relIndex Y = W.relIndex M := by
  have := relIndex_sup_right (H := M.subgroupOf Y) (K := W.subgroupOf Y)
  rw [← subgroupOf_sup hMY hWY, h, subgroupOf_self, relIndex_subgroupOf hMY,
    relIndex_top_right] at this
  exact this

theorem sup_normal_in {Y W M : Subgroup A} (hWY : W ≤ Y) (hWn : (W.subgroupOf Y).Normal)
    (hMY : M ≤ Y) (hMn : (M.subgroupOf Y).Normal) : ((M ⊔ W).subgroupOf Y).Normal := by
  rw [subgroupOf_sup hMY hWY]
  infer_instance

theorem skeleton (hp : p.Prime) {X Y W : Subgroup A}
    (hX : CFSG.Open.pRank p X ≤ 1) (hYX : Y ≤ X) (hYW : S622IsSimpleSection Y W)
    (hpYW : p ∣ W.relIndex Y) (hpW : ¬ p ∣ Nat.card W) :
    pSectionTop p X ≤ X ∧ ((pSectionTop p X).subgroupOf X).Normal ∧
      S622IsSimpleSection (pSectionTop p X) (rankThreePrimeCore p X) ∧
      W.relIndex Y ∣ (rankThreePrimeCore p X).relIndex (pSectionTop p X) ∧
      ¬ p ∣ Nat.card (rankThreePrimeCore p X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := rankThreePrimeCore p X with hO
  set H := pSectionTop p X with hH
  obtain ⟨hWY, hWn, -, hsimp, hnab⟩ := hYW
  have hHX : H ≤ X := pSectionTop_le X
  have hOH : O ≤ H := core_le_top X
  have hpO : ¬ p ∣ Nat.card O := not_dvd_card_core hp X
  have hHn : (H.subgroupOf X).Normal := normal_of_conj fun x hx n hn => top_conj hp hx hn
  have hOnH : (O.subgroupOf H).Normal :=
    normal_of_conj fun x hx n hn => core_conj hp (hHX hx) hn
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p
    (hpYW.trans (relIndex_dvd_card W Y))
  have hyo' : orderOf (y : A) = p := by rw [Subgroup.orderOf_coe]; exact hyo
  have hyH : (y : A) ∈ H := gen_mem_top (hYX y.2) hyo'
  have hyW : (y : A) ∉ W := fun h => not_mem_of_orderOf h hpW hyo'
  have hyO : (y : A) ∉ O := fun h => not_mem_of_orderOf h hpO hyo'
  have hYOn : ((Y ⊓ O).subgroupOf Y).Normal := normal_of_conj fun x hx n hn =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx (Subgroup.mem_inf.mp hn).1) (inv_mem hx),
      core_conj hp (hYX hx) (Subgroup.mem_inf.mp hn).2⟩
  have hYO : Y ⊓ O ≤ W := by
    rcases hsimp ((Y ⊓ O) ⊔ W) le_sup_right (sup_le inf_le_left hWY)
        (sup_normal_in hWY hWn inf_le_left hYOn) with h | h
    · exact le_sup_left.trans h.le
    · exfalso
      rw [relIndex_eq_of_sup_eq hWY hWn inf_le_left h] at hpYW
      exact hpO (hpYW.trans ((relIndex_dvd_card W _).trans (card_dvd_of_le inf_le_right)))
  have hYHn : ((Y ⊓ H).subgroupOf Y).Normal := normal_of_conj fun x hx n hn =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx (Subgroup.mem_inf.mp hn).1) (inv_mem hx),
      top_conj hp (hYX hx) (Subgroup.mem_inf.mp hn).2⟩
  have hYH : (Y ⊓ H) ⊔ W = Y := by
    rcases hsimp ((Y ⊓ H) ⊔ W) le_sup_right (sup_le inf_le_left hWY)
        (sup_normal_in hWY hWn inf_le_left hYHn) with h | h
    · exact absurd ((le_sup_left.trans h.le) ⟨y.2, hyH⟩) hyW
    · exact h
  have hdvd : W.relIndex Y ∣ O.relIndex H := by
    rw [relIndex_eq_of_sup_eq hWY hWn inf_le_left hYH]
    have h1 : W.relIndex (Y ⊓ H) ∣ O.relIndex (Y ⊓ H) := by
      rw [← inf_relIndex_right W (Y ⊓ H), ← inf_relIndex_right O (Y ⊓ H)]
      exact relIndex_dvd_of_le_left _ fun x hx => ⟨hYO ⟨hx.2.1, hx.1⟩, hx.2⟩
    have h2 : O.relIndex (Y ⊓ H) ∣ O.relIndex H := by
      rw [← relIndex_subgroupOf (inf_le_right : Y ⊓ H ≤ H)]
      exact relIndex_dvd_index_of_normal _ _
    exact h1.trans h2
  refine ⟨hHX, hHn, ⟨hOH, hOnH, fun h => hyO (h ▸ hyH), ?_, ?_⟩, hdvd, hpO⟩
  ·
    intro N hON hNH hNn
    by_cases hpN : p ∣ Nat.card N
    · right
      refine le_antisymm hNH (sup_le hON ((closure_le N).mpr ?_))
      rintro x ⟨hxX, hxo⟩
      exact KPCov.mem_of_normal_of_dvd
        ((CFSG.SectionRank.pRank_mono hp.one_lt hHX).trans hX) hNH hNn hpN
        (gen_mem_top hxX hxo) hxo
    · left
      refine le_antisymm ?_ hON
      have hN1 : N ≤ relPPrimeCore p H :=
        le_sSup ⟨hNH, hNn, (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN⟩
      have hN2 : relPPrimeCore p H ≤ O := by
        rw [relPPrimeCore_eq_map hp]
        exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.pPrimeCore_map_le_relPPrimeCore hHX
          ((normal_subgroupOf_iff_le_normalizer hHX).mp hHn)
      exact hN1.trans hN2
  ·
    intro hab
    apply hnab
    intro a ha b hb
    haveI : (W.subgroupOf Y).Normal := hWn
    have hYnorm : Y ≤ normalizer (W : Set A) := (normal_subgroupOf_iff_le_normalizer hWY).mp hWn
    have hdec : ∀ c ∈ Y, ∃ m ∈ Y ⊓ H, ∃ w ∈ W, m * w = c := by
      intro c hc
      have hc' : c ∈ ((Y ⊓ H ⊔ W : Subgroup A) : Set A) := by rw [hYH]; exact hc
      rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hYnorm)] at hc'
      obtain ⟨m, hm, w, hw, hmw⟩ := hc'
      exact ⟨m, hm, w, hw, hmw⟩
    obtain ⟨m₁, hm₁, w₁, hw₁, rfl⟩ := hdec a ha
    obtain ⟨m₂, hm₂, w₂, hw₂, rfl⟩ := hdec b hb
    have hm₁Y : m₁ ∈ Y := (Subgroup.mem_inf.mp hm₁).1
    have hm₂Y : m₂ ∈ Y := (Subgroup.mem_inf.mp hm₂).1
    have hc : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ W := hYO (Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem (mul_mem hm₁Y hm₂Y) (inv_mem hm₁Y)) (inv_mem hm₂Y),
        hab m₁ (Subgroup.mem_inf.mp hm₁).2 m₂ (Subgroup.mem_inf.mp hm₂).2⟩)
    let M1 : ↥Y := ⟨m₁, hm₁Y⟩
    let M2 : ↥Y := ⟨m₂, hm₂Y⟩
    let W1 : ↥Y := ⟨w₁, hWY hw₁⟩
    let W2 : ↥Y := ⟨w₂, hWY hw₂⟩
    let π := QuotientGroup.mk' (W.subgroupOf Y)
    have e1 : π W1 = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hw₁)
    have e2 : π W2 = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hw₂)
    have e3 : π (M1 * M2 * M1⁻¹ * M2⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hc)
    have key : π (M1 * W1 * (M2 * W2) * (M1 * W1)⁻¹ * (M2 * W2)⁻¹) = 1 := by
      simp only [map_mul, map_inv, e1, e2, mul_one] at e3 ⊢
      exact e3
    have := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp key)
    simpa [M1, M2, W1, W2] using this

end KPLevi

open KPLevi CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

@[expose] def KFactParabolicLeviSub : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ : Subgroup A) (p : ℕ),
    IsChevSimple 2 ↥K → ¬ fusionIsBenderGroup ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) →
    ∃ (f : ℕ) (Y W : Subgroup A), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ 2 ≤ CFSG.Open.pRank f K ∧
      Y ≤ K₀ ∧ S622IsSimpleSection Y W ∧ f ∣ W.relIndex Y ∧
      p ∣ W.relIndex Y ∧ ¬ p ∣ Nat.card W

theorem kFactParabolicLevi_of_sub (h : KFactParabolicLeviSub) : KFactParabolicLevi := by
  intro A _ _ K K₀ p hK hB hp h5 hrank hpar hne hsyl
  obtain ⟨f, Y, W, hf, hf2, hfp, hfr, hYK₀, hYW, hfYW, hpYW, hpW⟩ :=
    h A K K₀ p hK hB hp h5 hrank hpar hne hsyl
  have hK₀ : CFSG.Open.pRank p K₀ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hpar.1).trans hrank
  obtain ⟨hle, hn, hs, hd, hpO⟩ := skeleton hp hK₀ hYK₀ hYW hpYW hpW
  exact ⟨f, pSectionTop p K₀, rankThreePrimeCore p K₀, hf, hf2, hfp, hfr, hle, hn, hs,
    hfYW.trans hd, hpYW.trans hd, hpO⟩


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

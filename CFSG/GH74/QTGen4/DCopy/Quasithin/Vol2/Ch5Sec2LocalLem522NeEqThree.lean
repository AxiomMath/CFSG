module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqThree

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

namespace Hyp5_2_2p

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}

theorem star513_eq_F4 (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat)
    (hOX : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥)
    (hDp : ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G))
    (hT₀syl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B))
    {Lh : Subgroup G}
    (hhat : IsHatComp (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B)
      L₂ Lh)
    (hL4 : LieModel (O2Q L₂) .PSL 2 2 2)
    (hB₂ : Lin2.IsHallTwoPrimeOf (B ⊓ L₂)
      (L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup G) : Set G))) :
    Star513
        (modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) Lh)
        (modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂)
        (modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B)
          (T ⊓ Subgroup.normalizer (L₂ : Set G)))
        (modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B)
          (B ⊓ L₂))
        (modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) Dp) ∧
      ¬ modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) Dp ≤
        Subgroup.normalizer ((modO2Image (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔
          (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂ : Subgroup _) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hT₀N : T₀ ≤ Subgroup.normalizer (L₂ : Set G) := inf_le_right
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hT₀X : T₀ ≤ X₀ := le_sup_right.trans le_sup_left
  have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hB₂X : B ⊓ L₂ ≤ X₀ := inf_le_right.trans hL₂X
  have hT₀Lh : T₀ ≤ Subgroup.normalizer (Lh : Set G) := le_normalizer_hat hhat hT₀X hT₀N
  have hXN : X₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hOX hT₀syl hhat.1
    rwa [Emb512.conjClosure_hat_eq hT₀Lh] at this
  have hOT : pCoreOf 2 X₀ ≤ T₀ := F7.isSylowTwoOf_pCoreOf_le hT₀syl
  have hL₂perf : ⁅L₂, L₂⁆ = L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact hK₁.2.1
    · exact hL₂P.2.1
  have hQN : ∀ y : O2Q X₀,
      y ∈ Subgroup.normalizer ((modO2Image X₀ Lh : Subgroup (O2Q X₀)) : Set (O2Q X₀)) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X₀) y
    exact o2Map_mem_normalizer (hXN x.2)
  have hSsyl : IsSylowTwoOf (modO2Image X₀ T₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hT₀syl) _
      (QuotientGroup.mk'_surjective _)
  have hTKb : modO2Image X₀ T₀ ≤ Subgroup.normalizer
      ((modO2Image X₀ L₂ : Subgroup (O2Q X₀)) : Set (O2Q X₀)) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer hT₀N
  have hTL₂ : T₀ ⊓ L₂ = T ⊓ L₂ := le_antisymm (inf_le_inf_right L₂ inf_le_left)
    (fun x hx => ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩)
  have hB₂' : Lin2.IsHallTwoPrimeOf (B ⊓ L₂)
      (L₂ ⊓ Subgroup.normalizer ((T₀ ⊓ L₂ : Subgroup G) : Set G)) := by
    rw [hTL₂]
    exact hB₂
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image X₀ (B ⊓ L₂))
      (modO2Image X₀ L₂ ⊓ Subgroup.normalizer
        ((modO2Image X₀ T₀ ⊓ modO2Image X₀ L₂ : Subgroup (O2Q X₀)) : Set (O2Q X₀))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := X₀) (inf_le_left.trans hL₂X) hB₂'
    rwa [modO2Image_inf_normalizer hL₂X inf_le_right (fun x hx => ⟨hOT hx.2, hx.1⟩),
      ← modO2Image_inf_of_pCoreOf_le hOT] at h1
  have hYP : B ⊓ L₂ ≤ Subgroup.normalizer ((T₀ ⊓ L₂ : Subgroup G) : Set G) :=
    hB₂'.1.trans inf_le_right
  have hPY : IsSylowTwoOf (T₀ ⊓ L₂)
      (L₂ ⊓ Subgroup.normalizer ((T₀ ⊓ L₂ : Subgroup G) : Set G)) := by
    have hSL : IsSylowTwoOf (T₀ ⊓ L₂) L₂ := by
      rw [hTL₂]
      exact (hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice).1
    exact A4.isSylowTwoOf_mono hSL (le_inf inf_le_right Subgroup.le_normalizer) inf_le_left
  have hYeq : (T₀ ⊓ L₂) ⊔ (B ⊓ L₂) =
      L₂ ⊓ Subgroup.normalizer ((T₀ ⊓ L₂ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact sup_eq_of_isHall_isSylow hB₂' hPY
  have hT₀Y : T₀ ≤ Subgroup.normalizer
      (((T₀ ⊓ L₂) ⊔ (B ⊓ L₂) : Subgroup G) : Set G) := by
    rw [hYeq]
    intro t ht
    have htP : t ∈ Subgroup.normalizer ((T₀ ⊓ L₂ : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hT₀N ht⟩
    refine mem_normalizer_of_conj_mem' fun y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hT₀N ht) y).mp hy.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htP hy.2) (Subgroup.inv_mem _ htP)
  obtain ⟨hpB₁, hpB₂⟩ := exists_mul_eq_of_normalizes hYP inf_le_left hT₀Y
  have hDpTL : Dp ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_right)
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hTLT₀ : T ⊓ L ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ L := by
      rw [hSL]
      exact hx
    exact ⟨hx.1, hyp.S_le hxS.1⟩
  have hT₀YD : T₀ ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) :=
    inf_le_left.trans (hyp.T_le_normalizer_Y l2TorusFact)
  obtain ⟨hpD₁, hpD₂⟩ := exists_mul_eq_of_normalizes hDpTL hTLT₀ hT₀YD
  have hD := hyp.notation59.2.1
  have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
  have hBDp : B ⊓ L₂ ≤ Subgroup.normalizer (Dp : Set G) := fun b hb =>
    mem_normalizer_of_le_of_isCyclic hDcyc hyp.Dp_le (hyp.notation59.2.2 hb.1)
  have : Fact p.Prime := ⟨by rcases hyp.p_cases with rfl | rfl <;> norm_num⟩
  have hDpcyc : IsCyclic ↥Dp := isCyclic_of_prime_card (p := p) hyp.card_Dp
  refine ⟨⟨Subgroup.map_mono fun x hx => hhat.2.1 hx, ?_, ?_, hSsyl.2.1, fun y _ => hQN y, hTKb,
    A4.isSylowTwoOf_inf_normal hSsyl le_top fun y _ => hQN y,
    A4.isSylowTwoOf_inf_normal (QuasithinUnique.isSylowTwoOf_of_le hSsyl le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTKb), hBb,
    modO2Image_mul_comm hB₂X hT₀X hpB₁ hpB₂,
    isCyclic_of_surjective (barMap hDpX) (barMap_surjective hDpX),
    Odd.of_dvd_nat (by rw [hyp.card_Dp]; rcases hyp.p_cases with rfl | rfl <;> decide)
      (Subgroup.card_dvd_of_surjective (barMap_surjective hDpX)),
    fun y _ => hQN y, Vol2.Ch11.SecS.modO2Image_le_normalizer hBDp,
    modO2Image_mul_comm hDpX hT₀X hpD₁ hpD₂⟩, ?_⟩
  ·
    have : Group.IsPerfect ↥L₂ := Subgroup.isPerfect_iff.mpr hL₂perf
    have : Group.IsPerfect ↥(modO2Image X₀ L₂) :=
      Group.IsPerfect.ofSurjective (barMap_surjective hL₂X)
    exact Subgroup.isPerfect_iff.mp this
  ·
    obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hL₂X
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL4
  ·
    intro hle
    apply hDp
    intro d hd
    have hdb : QuotientGroup.mk' (CFSG.pCore 2 ↥X₀) ⟨d, hDpX hd⟩ ∈ modO2Image X₀ Dp :=
      ⟨⟨d, hDpX hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    exact mem_normalizer_of_modO2Image hL₂X hL₂perf (hOT.trans hT₀N) (hDpX hd) (hle hdb)

end Hyp5_2_2p

theorem stmt5_2_2_eq_three_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hL2 : Stmt5_2_L2_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h36 : Vol2Native.A36ForSQTKCat) (hTc : FactType513Aut) (hTp : FactType513Prime)
    (hcart : Stmt5_2_2_eq_cartan_F4) : Stmt5_2_2_eq_three_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp _ hOX _ _ hL₂K hDp hT₀syl Lh hhat _ hL4 _ hnr h314
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  rcases hyp.p_cases with hp | hp
  · exact hp
  exfalso
  obtain ⟨-, -, hB₂⟩ := hcart G T M L V H B D L₂ Dp n p hyp hL₂K hL4
  obtain ⟨hst, hnot⟩ := hyp.star513_eq_F4 h510 h331 hR hL2 h37 h38 hOX hDp hT₀syl hhat hL4 hB₂
  set X₀ := Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B with hX₀def
  have h36Q := Vol2Native.lemma_1_2_1_four_strong hloc h36 hOX hhat.1
  obtain ⟨eH⟩ := modO2_mulEquiv hhat.1
  have hnr' : ¬ IsRank2LieChar2 ↥(modO2Image X₀ Lh) := fun hR2 =>
    hnr (IsRank2LieChar2.of_mulEquiv eH.symm hR2)
  have hDp5 : ∀ d ∈ modO2Image X₀ Dp, d ^ 5 = 1 := by
    intro d hd
    have h1 := orderOf_dvd_natCard (⟨d, hd⟩ : ↥(modO2Image X₀ Dp))
    have h2 : Nat.card ↥(modO2Image X₀ Dp) ∣ 5 := by
      rw [← hp, ← hyp.card_Dp]
      exact Subgroup.card_dvd_of_surjective (barMap_surjective
        (le_sup_left.trans (le_sup_left.trans le_sup_left)))
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
  have hcen : ∀ d ∈ modO2Image X₀ Dp,
      d ∈ Subgroup.centralizer ((modO2Image X₀ Lh : Subgroup (O2Q X₀)) : Set (O2Q X₀)) := by
    rcases Star513.three_or_j1 hst hnot hTc hTp h36Q h314 hnr' with h3 | ⟨-, h7⟩
    · intro d hd
      obtain ⟨k, hk⟩ := h3 d hd
      exact mem_of_pow_three_pow_of_pow_five (hDp5 d hd) hk
    · intro d hd
      have e : (d ^ 7) ^ 3 = d := by
        rw [← pow_mul, show 7 * 3 = 5 * 4 + 1 by norm_num, pow_add, pow_mul, hDp5 d hd, one_pow,
          one_mul, pow_one]
      rw [← e]
      exact Subgroup.pow_mem _ (h7 d hd) 3
  apply hnot
  intro d hd
  refine mem_normalizer_of_conj_mem' fun r hr => ?_
  have hrQ : r ∈ modO2Image X₀ Lh := hst.R_le hr
  rw [← Subgroup.mem_centralizer_iff.mp (hcen d hd) r hrQ]
  simpa [mul_assoc] using hr

end CFSG.Quasithin.H13

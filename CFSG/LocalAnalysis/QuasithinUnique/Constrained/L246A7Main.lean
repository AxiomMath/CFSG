module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Y
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Block
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open CFSG.Quasithin CFSG.SectionRank

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section Normal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isQuasisimple_alt7 {L : Subgroup G} (hshort : IsShort2 L) (hAlt : IsAltType L 7) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨α, hα, hker, -⟩ := hAlt
  rcases hshort.2.2.2.1 with hq | h3
  · exact hq
  · exfalso
    have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    have e2 := QuotientGroup.quotientKerEquivOfSurjective α hα
    have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin 7)) :=
      Nat.card_congr (e1.trans e2).toEquiv
    rw [h3, card_alt7] at hcard
    omega

theorem le_normalizer_of_alt7 {X L : Subgroup G} (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hL : IsBlock2 X L) (hAlt : IsAltType L 7) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc : L ∈ cComp X :=
    C1GN.mem_cComp_of_short hL.1 (isQuasisimple_alt7 hL.1 hAlt) (C1GN.isSubnormal_of_isBlock2 hL)
  have hL' : L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := subgroupOf_mem_cComp hLc
  have hrank : 1 < CFSG.Open.pRank 3 (L.subgroupOf X) := by
    have e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.2.1
    have h1 := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have h2 := pRank_top_subtype (p := 3) (L.subgroupOf X)
    have h3 := pRank_top_subtype (p := 3) L
    have h4 : 2 ≤ CFSG.Open.pRank 3 L := by
      obtain ⟨α, hα, hker, -⟩ := hAlt
      exact C1GN.le_pRank_three_of_alt_quotient α hα hker C1GN.two_le_pRank_alt7
    omega
  have hnorm : (L.subgroupOf X).Normal :=
    L238.normal_of_pRank_gt_one_cat (L238.rank_quotient_le_of_isSQTKCat hSQ) h38 hL' Nat.prime_three
      (by norm_num) hrank
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL.2.1).1 hnorm

end Normal

section MainTheorem

variable {G : Type} [Group G] [Finite G]

theorem c129A7_of_inputs (hMB : MinParabolicBlocks) (h127 : L238.C127StatementCat (G := G))
    (h123 : L238.C123TwoCgsStatement (G := G)) (hB42 : L238.AltBlockStatementJCat (G := G))
    (h38 : Vol2Native.A38ForSQTKCat) : L238.C129A7StatementCat (G := G) := by
  intro X T M L hX hSQ hT hcgs hMX hblk hAlt hLJ hLM
  have h38X : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    h38 _ (Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQ)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_alt7 hSQ h38X hblk hAlt
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hT.1.trans hXN
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨D₀⟩ := isAltType_seven_iff.1 hAlt
  have hSyl : IsSylowTwoOf (T ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hblk.2.1 hblk.2.2
  have hQT : blockQ L ≤ T := fun q hq => (hSyl.pCoreOf_le hq).1
  obtain ⟨σ, hstd⟩ := exists_stdLabel D₀ hSyl
  set D : Alt7Data L := D₀.conj σ with hD
  have C : Cfg7 D T := ⟨hblk.1, hTN, hT2, hstd⟩
  have hT0 : T ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, hρa⟩ := hstd.2 g1 g1_mem
    have ha1 : a = 1 := by
      have := ha.1
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [ha1, rho_one D] at hρa
    exact absurd hρa.symm (by decide)
  have hTG7 : T ≤ G7 D T := fun t ht =>
    ⟨(le_sup_right : T ≤ L ⊔ T) ht, hTN ht, rho_T_fix6 D hTN hstd ht⟩
  have hG7X : G7 D T ≤ X := (G7_le D).trans (sup_le hblk.2.1 hT.1)
  have hX7 : CharTwo (G7 D T) := C1GN.charTwo_of_le hX hT hTG7 hG7X
  have hSQ7 : IsSQTKCat ↥(G7 D T) := L246A7.isSQTKCat_of_le hG7X hSQ
  have h387 : A38Part3 (↥(G7 D T) ⧸ CFSG.pCore 2 ↥(G7 D T)) :=
    h38 _ (Vol2Native.SQTKHypCat.quotient_pCore ↥(G7 D T) hSQ7)
  have hT7 : IsSylowTwoOf T (G7 D T) := C1GN.isSylowTwoOf_of_le hT hTG7 hG7X
  have hcgs7 : cgsIn (G7 D T) T ≤ M := (L238.cgsIn_mono_left hG7X).trans hcgs
  have hG7M : G7 D T ≤ M :=
    le_of_no_chiBlock hMB h127 h123 hB42 hX7 hSQ7 h387 hT7 hT0 hcgs7
      (no_chiBlock_G7 D hTN hT2)
  have hTM : T ≤ M := hTG7.trans hG7M
  obtain ⟨y, hyL, hρy, hycent⟩ := exists_y_central C
  have hCT : (⁅⁅T, T⁆, T⁆ : Subgroup G) ≤ T := by
    have h1 : (⁅T, T⁆ : Subgroup G) ≤ T :=
      Subgroup.commutator_le.2 fun g hg h hh => by
        rw [commutatorElement_def]
        exact T.mul_mem (T.mul_mem (T.mul_mem hg hh) (T.inv_mem hg)) (T.inv_mem hh)
    exact Subgroup.commutator_le.2 fun g hg h hh => by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem (h1 hg) hh) (T.inv_mem (h1 hg))) (T.inv_mem hh)
  have hyM : y ∈ M := by
    have hyX : y ∈ X := hblk.2.1 hyL
    have hynorm : y ∈ Subgroup.normalizer ((⁅⁅T, T⁆, T⁆ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hycent
    have hle : X ⊓ Subgroup.normalizer ((⁅⁅T, T⁆, T⁆ : Subgroup G) : Set G) ≤ cgsIn X T :=
      le_iSup_of_le (⁅⁅T, T⁆, T⁆ : Subgroup G) (le_iSup_of_le hCT
        (le_iSup_of_le (commutator_ne_bot C hQT)
          (le_iSup_of_le (commutator_characteristic T) le_rfl)))
    exact hcgs (hle ⟨hyX, hynorm⟩)
  apply hLM
  let Msub : Subgroup A₇ := (M.subgroupOf L).map D.α
  have hS6 : S6A ≤ Msub := by
    intro a ha
    obtain ⟨ℓ, hℓ⟩ := D.hα a
    have hρℓ : rho D ℓ = (a : S₇) := by rw [rho_of_mem D ℓ.2, hℓ]
    have hℓG7 : (ℓ : G) ∈ G7 D T :=
      ⟨(le_sup_left : L ≤ L ⊔ T) ℓ.2, Subgroup.le_normalizer ℓ.2, by rw [hρℓ]; exact ha⟩
    exact ⟨ℓ, Subgroup.mem_subgroupOf.2 (hG7M hℓG7), hℓ⟩
  have hcc : ccA ∈ Msub := by
    refine ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 hyM, ?_⟩
    apply Subtype.ext
    have := rho_of_mem D hyL
    rw [hρy] at this
    exact this.symm
  have hMtop : Msub = ⊤ := by
    rw [eq_top_iff, ← S6A_sup_zpowers_ccA]
    exact sup_le hS6 ((Subgroup.zpowers_le).2 hcc)
  intro ℓ hℓ
  have hmem : D.α ⟨ℓ, hℓ⟩ ∈ Msub := by rw [hMtop]; exact Subgroup.mem_top _
  obtain ⟨ℓ', hℓ'M, hℓ'⟩ := hmem
  have hker : (⟨ℓ, hℓ⟩ : ↥L)⁻¹ * ℓ' ∈ D.α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hℓ', inv_mul_cancel]
  have hker' : (⟨ℓ, hℓ⟩ : ↥L)⁻¹ * ℓ' ∈ CFSG.pCore 2 ↥L := by rw [← D.hker]; exact hker
  have hQ : (((⟨ℓ, hℓ⟩ : ↥L)⁻¹ * ℓ' : ↥L) : G) ∈ blockQ L := (mem_pCore_iff_mem_blockQ _).1 hker'
  have hℓ'M' : (ℓ' : G) ∈ M := Subgroup.mem_subgroupOf.1 hℓ'M
  have hQM : (((⟨ℓ, hℓ⟩ : ↥L)⁻¹ * ℓ' : ↥L) : G) ∈ M := hTM (hQT hQ)
  have : ℓ = (ℓ' : G) * ((((⟨ℓ, hℓ⟩ : ↥L)⁻¹ * ℓ' : ↥L) : G))⁻¹ := by
    simp
  rw [this]
  exact M.mul_mem hℓ'M' (M.inv_mem hQM)

end MainTheorem

end CFSG.QuasithinUnique.L246A7

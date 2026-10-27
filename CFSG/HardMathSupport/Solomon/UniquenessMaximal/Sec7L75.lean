module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Z2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X4
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2c
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2b
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2a
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2e

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]



namespace Ctx75

variable {B N K : Subgroup G} {x : G}


theorem A_cent (c : Ctx75 B N K x)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))) :
    barX 3 N (centralizerQuot B K) ≤
      Subgroup.centralizer (barX 3 N (GLAPLayer 3 (K ⊓ N)) :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := c.A_cent_of c.K0b_L34 hq

theorem pt_D1 (c : Ctx75 B N K x)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N))))
    {I : Subgroup G} (hIN : I ≤ N) (hK0I : GLAPLayer 3 (K ⊓ N) ≤ I)
    {a : G} (ha : a ∈ centralizerQuot B K) (ha1 : a ≠ 1) :
    ((barX 3 N (GLAPLayer 3 (K ⊓ N)) ⊔ GLAPPrimeCoreOf 3 (barX 3 N I ⊓
        Subgroup.centralizer ({mkN N a (c.AN ha)} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).subgroupOf
      (barX 3 N I ⊓ Subgroup.centralizer ({mkN N a (c.AN ha)} :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).Normal := by
  obtain ⟨J₁, h1, h2, h3, h4, h5⟩ := c.exists_J1
  exact c.pt_D1_of_J1 h1 h2 h3 h4 h5 (c.A_cent hq) hq c.K0b_L34 hIN hK0I ha ha1

theorem pt_D3 (c : Ctx75 B N K x)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N))))
    {I : Subgroup G} (hIN : I ≤ N) (hK0I : GLAPLayer 3 (K ⊓ N) ≤ I)
    {a : G} (ha : a ∈ centralizerQuot B K) (ha1 : a ≠ 1)
    (hcent : barX 3 N I ≤ Subgroup.centralizer ({mkN N a (c.AN ha)} :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))
    (hOI : GLAPPrimeCoreOf 3 (barX 3 N I) = ⊥) :
    ((barX 3 N (GLAPLayer 3 (K ⊓ N))).subgroupOf (barX 3 N I)).Normal := by
  obtain ⟨J₁, h1, h2, h3, h4, h5⟩ := c.exists_J1
  exact c.pt_D3_of_J1 h1 h2 h3 h4 h5 hq c.K0b_L34 hIN hK0I ha ha1 hcent hOI

end Ctx75

theorem Ctx75.case_one {B N K : Subgroup G} {x : G} (c : Ctx75 B N K x) (i145 : Input14_5)
    (i252 : Input25_2) {L : Subgroup G} (hL : GLAPComponent 3 N L)
    (hK0L : GLAPLayer 3 (K ⊓ N) ≤ L) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hxL : GLBConj x L = L) :
    IsComponentOf (barX 3 N (GLAPLayer 3 (K ⊓ N))) ⊤ := by
  have hNK : CFSG.Open.IsKGroup ↥N := isKGroup_of_isKProper c.stand.kProper c.hN
  have hQK : CFSG.Open.IsKGroup (↥N ⧸ GLAPPrimeCore 3 ↥N) :=
    isKGroup_quotient hNK (GLAPPrimeCore 3 ↥N)
  have hxN : x ∈ N := c.hxN
  have hx3 : x ^ 3 = 1 := c.bone.1.1.2 x c.hxB
  set K0 := GLAPLayer 3 (K ⊓ N) with hK0def
  set Ib := barX 3 N L with hIbdef
  have hIbc : IsComponentOf Ib ⊤ := hL.2.2.1
  have hK0Ib : barX 3 N K0 ≤ Ib := barX_mono 3 hK0L
  have hne := c.K0b_ne_bot
  have hperf := c.K0b_perf
  have hgen := c.K0b_gen
  have hL34 := c.K0b_L34
  have hnorm := c.K0b_norm
  have hcent := c.K0b_cent
  set xb := mkN N x hxN with hxbdef
  by_cases hxc : Ib ≤ Subgroup.centralizer ({xb} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))
  ·
    have hn : ((barX 3 N K0).subgroupOf Ib).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK0Ib).2 fun y hy => hnorm (hxc hy)
    have := eq_of_normal_perfect_of_quasisimple hIbc.2.2 hK0Ib hn hperf hne
    rw [this]
    exact hIbc
  ·
    have hxbN : xb ∈ Subgroup.normalizer (Ib : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
      have h1 := barX_le_normalizer (p := 3) (C := N) (S := L)
        (T := Subgroup.zpowers x) (by
          intro y hy
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact zpow_mem ((mem_normalizer_iff_gLBConj_eq.2 hxL)) n)
      exact h1 (mkN_mem_barX hxN (Subgroup.mem_zpowers x))
    have hKIb : CFSG.Open.IsKGroup ↥Ib := isKGroup_of_subgroup hQK Ib
    have hxb3 : xb ^ 3 = 1 := by
      have h1 : (⟨x, hxN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [hxbdef, mkN, ← map_pow, h1, map_one]
    have hxbc : Ib ≤ Subgroup.centralizer ({xb ^ 3} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
      rw [hxb3]
      intro y _
      simp [Subgroup.mem_centralizer_iff]
    have h145 := i145 (↥N ⧸ GLAPPrimeCore 3 ↥N) 3 Nat.prime_three (by norm_num) Ib hIbc.2.2 hKIb
      xb hxbN hxc hxbc
    set C1 := Ib ⊓ Subgroup.centralizer ({xb} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) with hC1def
    have hC1c : GLAPComponent 3 C1 (barX 3 N K0) :=
      glaPComponent_of_normal_generated (le_inf hK0Ib hcent) (fun y hy => hnorm hy.2) hgen hL34
    have hle : barX 3 N K0 ≤ GLAPLayer 3 C1 := le_sSup hC1c
    · have hq : CFSG.Open.IsQuasisimple ↥(barX 3 N K0) := h145 _ hC1c
      set E := barX 3 N (centralizerQuot B K) with hEdef
      have hAB : centralizerQuot B K ≤ B := (Subgroup.closure_le B).2 fun b hb => hb.1
      have hAN : centralizerQuot B K ≤ N := hAB.trans c.hBN
      have hEel : IsElemAbelian 3 E :=
        elemAbelian_barX Nat.prime_three hAN (isElemAbelian_mono c.bone.1.1 hAB)
      have hEcard : Nat.card E = 9 := by
        rw [hEdef, card_barX_of_isPGroup Nat.prime_three hAN
          (isPGroup_of_isElemAbelian' (isElemAbelian_mono c.bone.1.1 hAB))]
        have := c.hf.aK.2.2
        norm_num at this
        exact this
      have hEn : E ≤ Subgroup.normalizer (Ib : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
        barX_le_normalizer (hAB.trans hBL)
      have hOIb : GLAPPrimeCore 3 ↥Ib = ⊥ := glaPPrimeCore_eq_bot_of_isSubnormal hIbc.2.1
      have hxbE : xb ∈ E :=
        mkN_mem_barX hxN (mem_centralizerQuot_of_le_centralizer c.hxB c.hxK.1)
      have hCE : Subgroup.centralizer (E : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) ≤
          Subgroup.centralizer ({xb} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
        Subgroup.centralizer_le (by simpa using hxbE)
      have hJcent : barX 3 N K0 ≤ Subgroup.centralizer (E : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
        Subgroup.le_centralizer_iff.1 (c.A_cent hq)
      have hJ : barX 3 N K0 ≤ Ib ⊓ Subgroup.centralizer (E : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
        le_inf hK0Ib hJcent
      have hJn : ((barX 3 N K0).subgroupOf
          (Ib ⊓ Subgroup.centralizer (E : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hJ).2 fun y hy => hnorm (hCE hy.2)
      have hpt : ∀ b ∈ E, b ≠ 1 → ((barX 3 N K0 ⊔ GLAPPrimeCoreOf 3 (Ib ⊓
          Subgroup.centralizer ({b} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).subgroupOf
          (Ib ⊓ Subgroup.centralizer ({b} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).Normal := by
        intro b hb hb1
        obtain ⟨a, haN, haA, rfl⟩ := exists_mem_of_mem_barX hb
        have ha1 : a ≠ 1 := by
          rintro rfl
          exact hb1 (mkN_one N)
        exact c.pt_D1 hq hL.1 hK0L haA ha1
      have hL34Ib := i252 (↥N ⧸ GLAPPrimeCore 3 ↥N) Ib E (barX 3 N K0) hIbc.2.2 hKIb hOIb hEn
        hEel hEcard hJ hJn hq hL34 hpt
      have hcard : Nat.card ↥Ib = 20160 := card_eq_of_isLThreeFour hL34Ib
      have hcardJ : 20160 ≤ Nat.card ↥(barX 3 N K0) := by
        have h1 := card_eq_of_isLThreeFour hL34
        have h2 := Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥(barX 3 N K0))
        exact h1 ▸ Nat.le_of_dvd Nat.card_pos h2
      have heq : barX 3 N K0 = Ib := Subgroup.eq_of_le_of_card_ge hK0Ib (by omega)
      rw [heq]
      exact hIbc

theorem Ctx75.case_three {B N K : Subgroup G} {x : G} (c : Ctx75 B N K x) (i25 : Input2_5)
    {L₁ L₂ L₃ : Subgroup G} (h₁ : GLAPComponent 3 N L₁) (h₂ : GLAPComponent 3 N L₂)
    (h₃ : GLAPComponent 3 N L₃) (h12 : L₁ ≠ L₂) (h23 : L₂ ≠ L₃) (h31 : L₃ ≠ L₁)
    (hx₁ : GLBConj x L₁ = L₂) (hx₂ : GLBConj x L₂ = L₃) (hx₃ : GLBConj x L₃ = L₁)
    (hK0 : GLAPLayer 3 (K ⊓ N) ≤ L₁ ⊔ L₂ ⊔ L₃)
    (hBI : B ≤ Subgroup.normalizer ((L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) : Set G)) : False := by
  have hxN : x ∈ N := c.hxN
  have hx3 : x ^ 3 = 1 := c.bone.1.1.2 x c.hxB
  set K0 := GLAPLayer 3 (K ⊓ N) with hK0def
  set X₁ := barX 3 N L₁ with hX₁def
  set X₂ := barX 3 N L₂ with hX₂def
  set X₃ := barX 3 N L₃ with hX₃def
  have hX₁ : IsComponentOf X₁ ⊤ := h₁.2.2.1
  have hX₂ : IsComponentOf X₂ ⊤ := h₂.2.2.1
  have hX₃ : IsComponentOf X₃ ⊤ := h₃.2.2.1
  have hX12 : X₁ ≠ X₂ := fun h => h12 (glaPComponent_unique h₁ h₂ h)
  have hX23 : X₂ ≠ X₃ := fun h => h23 (glaPComponent_unique h₂ h₃ h)
  have hX31 : X₃ ≠ X₁ := fun h => h31 (glaPComponent_unique h₃ h₁ h)
  set xb := mkN N x hxN with hxbdef
  have hc₁ : GLBConj xb X₁ = X₂ := by rw [← barX_gLBConj_mk hxN L₁, hx₁]
  have hc₂ : GLBConj xb X₂ = X₃ := by rw [← barX_gLBConj_mk hxN L₂, hx₂]
  have hc₃ : GLBConj xb X₃ = X₁ := by rw [← barX_gLBConj_mk hxN L₃, hx₃]
  have hxb3 : xb ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [hxbdef, mkN, ← map_pow, h1, map_one]
  have hL₁N : L₁ ≤ N := h₁.1
  have hL₂N : L₂ ≤ N := h₂.1
  have hL₃N : L₃ ≤ N := h₃.1
  have hsup : barX 3 N (L₁ ⊔ L₂ ⊔ L₃) = X₁ ⊔ X₂ ⊔ X₃ := by
    rw [barX_sup (sup_le hL₁N hL₂N) hL₃N, barX_sup hL₁N hL₂N]
  set Ib := X₁ ⊔ X₂ ⊔ X₃ with hIbdef
  have hK0N : K0 ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hK0Ib : barX 3 N K0 ≤ Ib := hsup ▸ barX_mono 3 hK0
  obtain ⟨hlay, hcomps⟩ := components_of_product hX₁ hX₂ hX₃ hX12 hX23 hX31
  obtain ⟨hreg1, hreg2, hnormE, hel⟩ :=
    regular_of_cycle hX₁ hX₂ hX₃ hX12 hX23 hX31 hc₁ hc₂ hc₃ hxb3
  obtain ⟨h25a, h25b⟩ := i25 (↥N ⧸ GLAPPrimeCore 3 ↥N) 3 Nat.prime_three Ib
    (Subgroup.zpowers xb) hlay hnormE hel hreg1 hreg2
  set E0 := Subgroup.zpowers xb with hE0def
  have hcentE0 : Subgroup.centralizer (E0 : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) =
      Subgroup.centralizer ({xb} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    centralizer_zpowers_eq_singleton xb
  set C := Ib ⊓ Subgroup.centralizer (E0 : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) with hCdef
  set D := GLALayer C with hDdef
  have hne := c.K0b_ne_bot
  have hperf := c.K0b_perf
  have hMC : barX 3 N K0 ≤ C := le_inf hK0Ib (hcentE0 ▸ c.K0b_cent)
  have hMn : ((barX 3 N K0).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).2 fun y hy =>
      c.K0b_norm (hcentE0 ▸ hy.2)
  have hX₁Ib : IsComponentOf X₁ Ib :=
    ⟨le_sup_left.trans le_sup_left, isSubnormal_of_le_of_le hX₁.2.1
      (le_sup_left.trans le_sup_left) le_top, hX₁.2.2⟩
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := h25a X₁ hX₁Ib
  have hqX₁ : CFSG.Open.IsQuasisimple ↥X₁ := hX₁.2.2
  have hDq : CFSG.Open.IsQuasisimple ↥D :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv φ
      (CFSG.ComponentClassification.Quasisimple.central_quotient hqX₁ Z hZc)
  have hZ₀ : ∀ z ∈ (Subgroup.center ↥Ib).map Ib.subtype ⊓
      Subgroup.centralizer (E0 : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)), ∀ c' ∈ C, z * c' = c' * z := by
    rintro z ⟨⟨z', hz', rfl⟩, -⟩ c' hc'
    have := Subgroup.mem_center_iff.1 hz' ⟨c', hc'.1⟩
    exact congrArg Subtype.val this.symm
  have hEq : barX 3 N K0 = D :=
    eq_of_perfect_normal_in_sup_central h25b hDq hZ₀ hMC hMn hperf hne
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 N K0) := by rw [hEq]; exact hDq
  have hL34D : IsLThreeFour (↥D ⧸ GLAPPrimeCore 3 ↥D) := by
    have := c.K0b_L34
    rw [hEq] at this
    exact this
  have hX₁L34 : IsLThreeFour (↥X₁ ⧸ Subgroup.center ↥X₁) :=
    isLThreeFour_quot_center hqX₁ hDq Z hZc φ hL34D
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥X₁)) ≤ 2 :=
    pRank_mulAut_le_two_of_quot hqX₁.1 hX₁L34
  have hAB : B ≤ N := c.hBN
  have hBel : IsElemAbelian 3 (barX 3 N B) := elemAbelian_barX Nat.prime_three hAB c.bone.1.1
  have hBc : Nat.card (barX 3 N B) = 81 := by
    rw [card_barX_of_isPGroup Nat.prime_three hAB (isPGroup_of_isElemAbelian' c.bone.1.1)]
    exact card_eq_81 c.stand c.bone
  have hxBb : xb ∈ barX 3 N B := mkN_mem_barX hxN c.hxB
  have hBn : barX 3 N B ≤ Subgroup.normalizer (Ib : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    have := barX_le_normalizer (p := 3) (C := N) hBI
    rwa [hsup] at this
  obtain ⟨b, hbB, hb1, hbc⟩ := exists_centralizing_of_rank hX₁ hX₂ hX₃ hX12 hX23 hX31 hc₁ hc₂ hc₃
    hxb3 hBel hBc hxBb hBn hrank
  obtain ⟨y, hyN, hyB, rfl⟩ := exists_mem_of_mem_barX hbB
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hb1 (mkN_one N)
  have hyK : y ∈ centralizerQuot B K := by
    refine c.mem_centralizerQuot_of_centralizes hyB ?_
    exact Subgroup.centralizer_le hK0Ib hbc
  have hIbsn : IsSubnormal Ib ⊤ := isSubnormal_sup_three_components hX₁ hX₂ hX₃
  have hOIb : GLAPPrimeCoreOf 3 Ib = ⊥ := glaPPrimeCoreOf_eq_bot_of_isSubnormal hIbsn
  have hIN : (L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) ≤ N := sup_le (sup_le hL₁N hL₂N) hL₃N
  have hnormal : ((barX 3 N K0).subgroupOf Ib).Normal := by
    have h := c.pt_D3 hq hIN hK0 hyK hy1 (by
      rw [hsup]
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hbc z hz) (by rw [hsup]; exact hOIb)
    rwa [hsup] at h
  exact false_of_normal_perfect_cycled hX₁ hX₂ hX₃ hX12 hX23 hX31 hc₁ hc₂ hc₃ hK0Ib hnormal
    (c.K0b_cent) hperf hne

theorem lemma75_of_inputs (i183 : Input18_3_4) (i25 : Input2_5) (i145 : Input14_5)
    (i252 : Input25_2) (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B)
    (h68 : Prop68Out B) : Lemma75Stmt B := by
  intro K hK N hNtop hBN hcov
  have hf := h68 K hK
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK
  have c : Ctx75 B N K x := ⟨hS, hB, hf, hNtop, hBN, hcov, hxB, hx1, hxK⟩
  have hNK : CFSG.Open.IsKGroup ↥N := isKGroup_of_isKProper hS.kProper hNtop
  have hx3 : x ^ 3 = 1 := hB.1.1.2 x hxB
  have hBlay : B ≤ Subgroup.normalizer (GLAPLayer 3 N : Set G) :=
    hBN.trans (Sec7.le_normalizer_glaPLayer 3 N)
  rcases dichotomy_of_input18_3_4 i183 hNK c.hxN hx3 c.K0_comp with
    ⟨L, hL, hK0L, hIL, hxL⟩ |
    ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hx₁, hx₂, hx₃, hI, hK0⟩
  · have hBL : B ≤ Subgroup.normalizer (L : Set G) := by
      have := le_normalizer_normalClosure c.B_le_normalizer_K0 hBlay
      rwa [hIL] at this
    exact c.case_one i145 i252 hL hK0L hBL hxL
  · exfalso
    have hBI : B ≤ Subgroup.normalizer ((L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) : Set G) := by
      have := le_normalizer_normalClosure c.B_le_normalizer_K0 hBlay
      rwa [hI] at this
    exact c.case_three i25 h₁ h₂ h₃ h12 h23 h31 hx₁ hx₂ hx₃ hK0 hBI

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem oTwoUpper_inf_le_centralizer_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6211 : Stmt6_2_11_F4) :
    oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓ M) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  set H := Subgroup.centralizer (Z : Set G) with hH
  set U := conjClosure (ch6ZS T L V) H with hU
  have hV := h.toHyp611.isElemAbelian
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZSel : IsElemAbelian 2 (ch6ZS T L V) := B2F.isElemAbelian_mono inf_le_left hV
  obtain ⟨⟨-, hUQ, hcomm⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five_F4 h331 h432 h512 h614 h615
  have h9 := stmt6_2_9_F4 h331 h432 h512 h614 h615 G T M L V h
  set C := centralizerMod Z H U with hC
  set V₁ := V ⊓ C with hV₁
  have h11 : V₁.relIndex V = 2 := h6211 G T M L V h

  have hZSV₁ : ch6ZS T L V ≤ V₁ := by
    intro y hy
    have hyH : y ∈ H := Subgroup.mem_centralizer_iff.mpr fun w hw =>
      B2F.isElemAbelian_comm hV (hZZS hw).1 hy.1
    refine ⟨hy.1, mem_centralizerMod.mpr ⟨hyH, Subgroup.centralizer_le_normalizer _ hyH,
      fun u hu => ?_⟩⟩
    have := Subgroup.commutator_mem_commutator (hUQ (le_conjClosure _ H hy)) hu
    rw [Subgroup.commutator_comm] at this
    have h1 := hcomm this
    rwa [commutatorElement_def] at h1
  have hV₁c : Nat.card V₁ = 8 := by
    have h1 := Subgroup.relIndex_mul_card (H := V₁) (K := V)
    rw [inf_of_le_left (inf_le_left : V₁ ≤ V), h11, h.natural.card_eq] at h1
    change 2 * Nat.card ↥V₁ = 2 ^ 2 * 2 ^ 2 at h1
    have e16 : (2 : ℕ) ^ 2 * 2 ^ 2 = 16 := by norm_num
    rw [e16] at h1
    omega
  have hrel1 : V₁.relIndex V = 2 := h11
  have hrel2 : (ch6ZS T L V).relIndex V₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := ch6ZS T L V) (K := V₁)
    rw [inf_of_le_left hZSV₁, hZS4, hV₁c] at h1
    omega
  have hrel3 : Z.relIndex (ch6ZS T L V) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Z) (K := ch6ZS T L V)
    rw [inf_of_le_left hZZS, hZ2, hZS4] at h1
    omega

  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxH, hxM⟩, hxo⟩
  refine ⟨hxM, ?_⟩
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := by
    have : x ∈ H ⊓ M := ⟨hxH, hxM⟩
    rw [h9.1] at this
    exact this.2
  have hxZS : x ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    have : x ∈ H ⊓ Subgroup.normalizer (V : Set G) := ⟨hxH, hxV⟩
    rw [h9.2.1] at this
    exact this.2
  have hxC : x ∈ Subgroup.normalizer (C : Set G) :=
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hxH)
      (Subgroup.le_normalizer hxH) (le_normalizer_conjClosure _ H hxH)
  have hxV₁ : x ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hxV, hxC⟩
  have hx1 : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G) :=
    mem_centralizer_of_odd_ch62 hZSel hZZS hxo (pow_orderOf_eq_one x)
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hxH u hu).symm)
      (fun a ha => commutator_mem_of_relIndex_two_ch62 hrel3 hxZS
        (Subgroup.centralizer_le_normalizer _ hxH) ha)
  have hx2 : x ∈ Subgroup.centralizer (V₁ : Set G) :=
    mem_centralizer_of_odd_ch62 (B2F.isElemAbelian_mono inf_le_left hV) hZSV₁ hxo
      (pow_orderOf_eq_one x) (fun u hu => (Subgroup.mem_centralizer_iff.mp hx1 u hu).symm)
      (fun a ha => commutator_mem_of_relIndex_two_ch62 hrel2 hxV₁ hxZS ha)
  exact mem_centralizer_of_odd_ch62 hV inf_le_left hxo (pow_orderOf_eq_one x)
    (fun u hu => (Subgroup.mem_centralizer_iff.mp hx2 u hu).symm)
    (fun a ha => commutator_mem_of_relIndex_two_ch62 hrel1 hxV hxV₁ ha)

end Hyp6Sec2

theorem stmt6_2_12_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6211 : Stmt6_2_11_F4) : Stmt6_2_12_F4 := by
  intro G _ _ T M L V h Z H U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1a := h.oTwoUpper_inf_le_centralizer_F4 h331 h432 h512 h614 h615 h6211
  have h1b : M ⊓ Subgroup.centralizer (V : Set G) ≤ centralizerMod (pCoreOf 2 L) M L := by
    rintro x ⟨hxM, hxV⟩
    have hxL := h.normal hxM
    refine mem_centralizerMod.mpr ⟨hxM, normalizer_le_normalizer_pCoreOf 2 L hxL, fun l hl => ?_⟩
    exact h.toHyp611Nat.commutator_mem_pCoreOf hxL hxV hl
  refine ⟨⟨h1a, h1b⟩, ?_⟩
  obtain ⟨⟨hchar, -, hcomm⟩, ⟨hCN, hNM, -⟩, -, -⟩ :=
    h.lemma_6_2_10_one_three_five_F4 h331 h432 h512 h614 h615
  set C := centralizerMod Z H U with hC
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hCHM : C ≤ H ⊓ M := fun c hc => ⟨hCH hc, hNM (hCN hc)⟩
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hg)
      (Subgroup.le_normalizer hg) (le_normalizer_conjClosure _ H hg)

  have hY : oTwoUpper C = ⊥ := by
    by_contra hYne
    set Y := oTwoUpper C with hYdef
    have hYC : Y ≤ C := oTwoUpper_le C
    have hYV : Y ≤ Subgroup.centralizer (V : Set G) :=
      ((oTwoUpper_mono hCHM).trans h1a).trans inf_le_right
    have hYM : Y ≤ M := hYC.trans (hCHM.trans inf_le_right)

    have hYL : ∀ y ∈ Y, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      intro y hy l hl
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := h.normal (hYM hy)
      have h1 : l * y * l⁻¹ * y⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp hyN l⁻¹).mp (L.inv_mem hl)
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact L.mul_mem hl this
      have h2 : l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        have hlC : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62
            (h.toHyp611.L_le_normalizer hl)) y).mp (hYV hy)
        exact Subgroup.mul_mem _ hlC (Subgroup.inv_mem _ (hYV hy))
      exact h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨_, h1⟩)
        ((h.data.mem_ker_rho_iff _).mpr h2)
    have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
      hHC.trans (normalizer_le_normalizer_oTwoUpper C)
    have hZV : Z ≤ V := h.omega_le_V_F4 h331 h432 h512 h614 h615
    have hO2LH : pCoreOf 2 L ≤ H := fun x hx =>
      Subgroup.centralizer_le (show (Z : Set G) ⊆ V from hZV)
        (h.toHyp611.pCoreOf_le_centralizer hx)
    have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
      intro l hl
      exact mem_normalizer_oTwoUpper_ch62 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        (hO2LH.trans hHY) (fun y hy => hYL y hy l hl)
        (fun y hy => by simpa using hYL y hy l⁻¹ (L.inv_mem hl))
    have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨⟨-, hy⟩, -⟩
      exact hy
    have hTH : T ≤ H := fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
    have hYchar : CharTwo Y := A4.charTwo_of_normal (hYC.trans hCH) hHY hchar
    have hY2 : pCoreOf 2 Y ≠ ⊥ := by
      intro h0
      apply hYne
      refine le_bot_iff.mp fun y hy => ?_
      have hyC : y ∈ Y ⊓ Subgroup.centralizer (pCoreOf 2 Y : Set G) := by
        refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        rw [h0] at hx
        rw [Subgroup.mem_bot.mp hx, one_mul, mul_one]
      have := hYchar hyC
      rwa [h0] at this
    have hNO : Subgroup.normalizer (pCoreOf 2 Y : Set G) ≤ M :=
      le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM_F4 h432)
        (sup_le (hLY.trans (normalizer_le_normalizer_pCoreOf 2 Y))
          ((hTH.trans hHY).trans (normalizer_le_normalizer_pCoreOf 2 Y)))
        ⟨pCoreOf 2 Y, hY2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
    exact h.not_centralizer_omega_le_F4 h331 h615 fun x hx =>
      hNO (normalizer_le_normalizer_pCoreOf 2 Y (hHY hx))
  refine ⟨hY, le_antisymm (le_pCoreOf_of_le_normalizer 2 hCH hHC ?_) fun q hq => ?_⟩
  · refine A4.isPGroup_two_of_odd_order_eq_one fun c hc hodd => ?_
    have : c ∈ oTwoUpper C := mem_oTwoUpper_of_odd hc hodd
    rw [hY] at this
    exact Subgroup.mem_bot.mp this
  · refine mem_centralizerMod.mpr ⟨pCoreOf_le 2 H hq,
      Subgroup.centralizer_le_normalizer _ (pCoreOf_le 2 H hq), fun u hu => ?_⟩
    have := Subgroup.commutator_mem_commutator hq hu
    rw [Subgroup.commutator_comm] at this
    have h1 := hcomm this
    rwa [commutatorElement_def] at h1

end CFSG.Quasithin.H13

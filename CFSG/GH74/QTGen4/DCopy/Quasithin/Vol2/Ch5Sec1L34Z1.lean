module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Z1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem521
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem normalizer_T_le_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨⟨hmax, -, -⟩, -⟩ := h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34
  have h3 := ((h331 G T hh.simple hh.nonabelian hh.qtke hh.sylow).2 (oTwoUpper H) hmax
    h.isQuasisimple_K).2.2.2.1
  rwa [h.conjClosure_K_eq] at h3

theorem exists_isZ1Choice_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) (h519 : Stmt5_1_19_F4)
    (h520 : Stmt5_1_20_F4) (hF : L2TorusFact) (hFix : L2ModFixTwoFact) (hSum : L4NatSumFact)
    (hnot : ¬ Concl5_1_14_four T L V B D n) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D)
    (h3 : Nat.card D₃ = 3) : ∃ Z₁ : Subgroup G, IsZ1Choice T L Z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hD₃M, -⟩ := h520 G T M L V H B D n h.hyp h.notation59 h.module h.l34 hnot D₃ hD₃ h3
  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdBorel : d ∈ borelL T L := h.notation59.2.1.1 (hD₃ hdD₃)
  have hdL : d ∈ L := hdBorel.1
  have hdT : d ∉ Subgroup.normalizer (T : Set G) := by
    intro hdN
    apply hD₃M
    rw [← zpowers_eq_of_card_prime Nat.prime_three h3 hdD₃ hd1]
    exact Subgroup.zpowers_le.mpr (h.normalizer_T_le_F4 h5114 h331 hdN)
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.2

  obtain ⟨-, hVZel, hVZred⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (hh.isSylowTwoOf le_sup_right) h.charTwo_LT (le_refl (quasithinOmegaOneCenter T))
  rw [hh.conjClosure_sup_eq] at hVZel hVZred
  set VZ := conjClosure (quasithinOmegaOneCenter T) L with hVZdef
  have hZVZ : quasithinOmegaOneCenter T ≤ VZ := le_conjClosure _ L
  have hTVZ : T ≤ Subgroup.normalizer (VZ : Set G) := le_sup_right.trans hVZred.2.1
  have hLVZ : L ≤ Subgroup.normalizer (VZ : Set G) := le_sup_left.trans hVZred.2.1

  have hred := h.module.isTwoReducedIn
  have hVne : V ≠ ⊥ := by
    intro hb
    apply h.module.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp
  obtain ⟨z₀, -, hz₀1, hz₀Z⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl
    (hh.V_le_T h.module) (le_sup_right.trans hred.2.1) hVne
  have hVZL : ⁅VZ, L⁆ ≠ ⊥ := by
    intro hb
    have hC : VZ ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have : z₀ ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hz₀Z, hC (hZVZ hz₀Z)⟩
    rw [hZL, Subgroup.mem_bot] at this
    exact hz₀1 this
  have hVZmod : IsCh5Module T L VZ :=
    ⟨hVZred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hVZred).2, hVZL⟩
  have hVZT : VZ ≤ T := hh.V_le_T hVZmod

  have hZsub : ∀ x ∈ VZ, x ∈ Subgroup.centralizer (T : Set G) → x ∈ quasithinOmegaOneCenter T :=
    fun x hx hxC => mem_quasithinOmegaOneCenter_iff.mpr ⟨hVZT hx, hxC, hVZel.2 x hx⟩
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_inf T).trans inf_le_right

  have hnotZ : ¬ Concl5_1_14_four T L VZ B D n := by
    rintro ⟨-, -, hDB⟩
    apply hD₃M
    rw [hDB] at hD₃
    exact hD₃.trans ((h.notation59.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H))
  rcases h519 G T M L VZ H B D n h.hyp h.notation59 hVZmod h.l34 hnotZ D₃ hD₃ h3 with
    ⟨-, ⟨hn2, hsum⟩ | ⟨hn24, hnat⟩⟩ | ⟨hn48, horth, -⟩ | ⟨-, -, -, -, hD₃M', -⟩
  ·
    subst hn2
    have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (VZ : Set G) := by
      have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
          (hh.sup_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L))
          (pCoreOf_isPGroup 2 L)
      rw [← hh.centralizer_eq_pCoreOf hVZmod] at h1
      exact h1.trans inf_le_right
    have hkerVZ : ∀ W : Subgroup G, W ≤ VZ → IsNatModCh5 L W 2 →
        L ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (VZ : Set G) := by
      intro W _ hW
      have hWne : W ≠ ⊥ := by
        intro hb
        apply hW.not_le_centralizer
        rw [hb]
        intro l _
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hw
        rw [hw, one_mul, mul_one]
      have hWL : ⁅W, L⁆ ≠ ⊥ := by rw [hW.commutator_eq]; exact hWne
      exact (hh.inf_centralizer_le hW.1 hWL).trans hO2
    obtain ⟨V₁, hz₀V₁, hV₁nat, hV₁irr⟩ :=
      hSum G L VZ (T ⊓ L) z₀ hsum
        (fun a ha b hb => congrArg Subtype.val (hVZel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hkerVZ hS
        (hZVZ hz₀Z) (Subgroup.centralizer_le (fun x hx => hx.1) (hZC hz₀Z))
    have hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G) :=
      le_normalizer_of_isNatModCh5 hV₁nat hh.T_le_normalizer hz₀V₁ hz₀1 (hZC hz₀Z)
    have hV₁ne : ⁅V₁, L⁆ ≠ ⊥ := by
      rw [hV₁nat.commutator_eq]
      intro hb
      rw [hb, Subgroup.mem_bot] at hz₀V₁
      exact hz₀1 hz₀V₁
    have hcard := hFix G L T V₁ 2 d (Or.inl ⟨hV₁nat, Or.inl rfl⟩) hT2 hh.T_le_normalizer hTV₁ hS
      (hh.inf_centralizer_le_T (sup_le hV₁nat.1 hTV₁) hV₁ne) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T ⊓ V₁ = V₁ ⊓ Subgroup.centralizer (T : Set G) := by
      refine le_antisymm (fun x hx => ⟨hx.2, hZC hx.1⟩) (fun x hx => ⟨?_, hx.1⟩)
      exact hZsub x (hV₁irr.1 hx.1) hx.2
    refine ⟨quasithinOmegaOneCenter T ⊓ V₁, inf_le_left, by rw [heq]; exact hcard,
      Or.inr ⟨hsum, V₁, hV₁irr, rfl⟩⟩
  ·
    set W := ⁅VZ, L⁆ with hWdef
    have hWV : W ≤ VZ := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv l hl
      have : l * v⁻¹ * l⁻¹ ∈ VZ :=
        (Subgroup.mem_normalizer_iff.mp (hLVZ hl) v⁻¹).mp (VZ.inv_mem hv)
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact VZ.mul_mem hv this
    have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_commutator_of hTVZ hh.T_le_normalizer
    have hZW : quasithinOmegaOneCenter T ≤ W := by
      intro z hz
      have hzVZ := hZVZ hz
      have hnorm := h.norm_eq_one_F4 h5114 hF hD₃ h3 hD₃M hz hdD₃ hd1
      have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)

      have hzb : z * (d * z * d⁻¹) ∈ W := by
        have hc : ⁅z, d⁆ ∈ W := Subgroup.commutator_mem_commutator hzVZ hdL
        have e : ⁅z, d⁆ = z * (d * z * d⁻¹) := by
          rw [commutatorElement_def, hzi]; group
        rwa [e] at hc

      have hc : d ^ 2 * z * (d ^ 2)⁻¹ ∈ W := by
        rw [eq_inv_of_mul_eq_one_right hnorm]
        exact W.inv_mem hzb
      have hd2 : d⁻¹ ^ 2 ∈ L := L.pow_mem (L.inv_mem hdL) 2
      have := (Subgroup.mem_normalizer_iff.mp (hnat.1 hd2) _).mp hc
      have e : d⁻¹ ^ 2 * (d ^ 2 * z * (d ^ 2)⁻¹) * (d⁻¹ ^ 2)⁻¹ = z := by group
      rwa [e] at this
    have hWne : ⁅W, L⁆ ≠ ⊥ := by rw [hnat.commutator_eq]; exact hVZL
    have hcard := hFix G L T W n d (Or.inl ⟨hnat, hn24⟩) hT2 hh.T_le_normalizer hTW hS
      (hh.inf_centralizer_le_T (sup_le hnat.1 hTW) hWne) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T = W ⊓ Subgroup.centralizer (T : Set G) :=
      le_antisymm (fun x hx => ⟨hZW hx, hZC hx⟩) (fun x hx => hZsub x (hWV hx.1) hx.2)
    exact ⟨quasithinOmegaOneCenter T, le_rfl, by rw [heq]; exact hcard, Or.inl rfl⟩
  ·
    have hcard := hFix G L T VZ n d (Or.inr ⟨horth, hn48⟩) hT2 hh.T_le_normalizer hTVZ hS
      (hh.inf_centralizer_le_T hVZred.2.1 hVZL) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T = VZ ⊓ Subgroup.centralizer (T : Set G) :=
      le_antisymm (fun x hx => ⟨hZVZ hx, hZC hx⟩) (fun x hx => hZsub x hx.1 hx.2)
    exact ⟨quasithinOmegaOneCenter T, le_rfl, by rw [heq]; exact hcard, Or.inl rfl⟩
  · exact absurd hD₃M' hD₃M

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13

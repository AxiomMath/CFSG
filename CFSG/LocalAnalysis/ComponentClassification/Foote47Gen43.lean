module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_iSup_of_isKleinFour' {M V L₀ W' F : Subgroup G} (hF : IsKleinFour F)
    (hFX : F ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G))
    (hL₀F : L₀ ≤ centralizer (F : Set G))
    (hW'L₀ : ∀ g ∈ W', V.map (MulAut.conj g).toMonoidHom ≤ L₀) (hVp : IsPGroup 2 V)
    (hL₀ : L₀ ≤ closure (⋃ g ∈ W', ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)))
    (K : G → Subgroup G) (hK₀ : ∀ w ∈ F, w ≠ 1 → L₀ ≤ K w)
    (hKN : ∀ w ∈ F, w ≠ 1 → centralizer ({w} : Set G) ≤ normalizer (K w : Set G))
    (hL₀M : L₀ ≤ M) (hMres : M ≤ oddResidualIn M) (hMsup : M ≤ L₀ ⊔ oddCoreIn M) :
    M ≤ ⨆ w ∈ F, ⨆ (_ : w ≠ 1), K w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LF := ⨆ w ∈ F, ⨆ (_ : w ≠ 1), K w with hLF
  set X := oddCoreIn M with hX
  have hKF : ∀ w ∈ F, w ≠ 1 → K w ≤ LF := fun w hw hw1 =>
    le_iSup₂_of_le (f := fun w (_ : w ∈ F) => ⨆ (_ : w ≠ 1), K w) w hw
      (le_iSup (fun _ : w ≠ 1 => K w) hw1)
  obtain ⟨w₀, hw₀, hw₀1, -⟩ := exists_ne_of_isKleinFour hF 1
  have hL₀LF : L₀ ≤ LF := (hK₀ w₀ hw₀ hw₀1).trans (hKF w₀ hw₀ hw₀1)
  have hL₀X : L₀ ≤ normalizer (X : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hL₀M hx))
  have hXodd : Odd (Nat.card X) := odd_card_oddCoreIn M
  have hXs : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd
  have hXcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hXodd
  set Y := ⨆ w ∈ F, ⨆ (_ : w ≠ 1), ⁅X ⊓ centralizer ({w} : Set G), L₀⁆ with hY
  have hYF : Y ≤ LF := by
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    rw [commutator_le]
    intro z hz l hl
    have hzN : z ∈ normalizer (K w : Set G) := hKN w hw hw1 (mem_inf.mp hz).2
    rw [commutatorElement_def]
    exact hKF w hw hw1 (mul_mem ((mem_normalizer_iff.mp hzN l).mp (hK₀ w hw hw1 hl))
      (inv_mem (hK₀ w hw hw1 hl)))
  have hL₀Y : L₀ ≤ normalizer (Y : Set G) := fun l hl => by
    apply mem_normalizer_of_map_conj_eq
    simp only [hY, Subgroup.map_iSup]
    refine iSup_congr fun w => iSup_congr fun hw => iSup_congr fun hw1 => ?_
    rw [Subgroup.map_commutator, map_inf_eq _ _ _ (MulAut.conj l).injective,
      map_conj_eq_of_mem_normalizer (hL₀X hl), map_conj_eq_self_of_mem hl,
      map_conj_eq_of_mem_normalizer (mem_normalizer_centralizer_singleton
        ((mem_centralizer_iff.mp (hL₀F hl)) w hw).symm)]
  have hXT : ∀ g ∈ W', ⁅X, V.map (MulAut.conj g).toMonoidHom⁆ ≤ Y := by
    intro g hg
    set T := V.map (MulAut.conj g).toMonoidHom with hT
    have hTp : IsPGroup 2 T := hVp.map _
    have hFel : CFSG.Open.IsElemAbelian 2 F :=
      ⟨@IsKleinFour.isMulCommutative F _ hF, fun x hx => sq_eq_one_of_isKleinFour hF hx⟩
    have hTX : T ≤ normalizer (X : Set G) := (hW'L₀ g hg).trans hL₀X
    have hFT : F ≤ centralizer (T : Set G) := fun x hx => mem_centralizer_iff.mpr
      fun y hy => ((mem_centralizer_iff.mp (hL₀F (hW'L₀ g hg hy))) x hx).symm
    rw [CFSG.SignalizerFunctor.Helpers.solvable_normalized_order_fixed_commutator_generation
      2 1 2 Nat.prime_two Nat.prime_two F T X hFel (by rw [hF.card_four]; norm_num) hTp hXs
      hFX hTX hFT hXcop hXcop]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSF, hScard⟩ := hS
    obtain ⟨w, hwS, hw1, hSw⟩ := exists_centralizer_eq_of_card_two (by rw [hScard, pow_one])
    rw [hSw]
    refine (commutator_mono le_rfl (hW'L₀ g hg)).trans ?_
    exact le_iSup₂_of_le (f := fun w (_ : w ∈ F) =>
      ⨆ (_ : w ≠ 1), ⁅X ⊓ centralizer ({w} : Set G), L₀⁆) w (hSF hwS)
      (le_iSup (fun _ : w ≠ 1 => ⁅X ⊓ centralizer ({w} : Set G), L₀⁆) hw1)
  have hXL : ⁅X, L₀⁆ ≤ Y := by
    have hSL : closure (⋃ g ∈ W', ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G)) ≤ L₀ := by
      rw [closure_le]
      intro x hx
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨g, hg, hxg⟩ := hx
      exact hW'L₀ g hg hxg
    rw [commutator_le]
    intro q hq x hx
    refine closure_induction (p := fun x _ => ⁅q, x⁆ ∈ Y) ?_ ?_ ?_ ?_ (hL₀ hx)
    · intro y hy
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hy
      obtain ⟨g, hg, hyg⟩ := hy
      exact hXT g hg (commutator_mem_commutator hq hyg)
    · simp only [commutatorElement_def, mul_one, mul_inv_cancel]
      exact one_mem Y
    · intro y z hy hz py pz
      have e1 : ⁅q, y * z⁆ = ⁅q, y⁆ * (y * ⁅q, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact mul_mem py ((mem_normalizer_iff.mp (hL₀Y (hSL hy)) _).mp pz)
    · intro y hy py
      have e1 : ⁅q, y⁻¹⁆ = y⁻¹ * ⁅q, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact (mem_normalizer_iff.mp (hL₀Y (L₀.inv_mem (hSL hy))) _).mp (inv_mem py)
  set R := L₀ ⊔ ⁅X, L₀⁆ with hR
  have hXR : X ≤ normalizer (R : Set G) := fun x hx => mem_normalizer_of_map_conj_le (by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro l hl
      show x * l * x⁻¹ ∈ R
      have e1 : x * l * x⁻¹ = ⁅x, l⁆ * l := by rw [commutatorElement_def]; group
      rw [e1]
      exact mul_mem (mem_sup_right (commutator_mem_commutator hx hl)) (mem_sup_left hl)
    · rw [map_conj_eq_of_mem_normalizer (le_normalizer_commutator X L₀ hx)]
      exact le_sup_right)
  have hMR : M ≤ R := by
    refine hMres.trans ((closure_le _).mpr fun g hg => ?_)
    obtain ⟨hgM, h2⟩ := hg
    have hg' : g ∈ X ⊔ R :=
      (sup_le (le_sup_left.trans le_sup_right) le_sup_left : L₀ ⊔ X ≤ X ⊔ R) (hMsup hgM)
    exact mem_of_two_element_of_mem_sup hXR
      (by rw [oddResidualIn_eq_bot_of_odd hXodd]; exact bot_le) hg' h2
  exact hMR.trans (sup_le hL₀LF (hXL.trans hYF))

variable {L : Subgroup G}

theorem le_footeME_of_isKleinFour (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {W : Subgroup G} (hW : IsKleinFour W) (hWC : W ≤ coreActionKernel M) :
    M ≤ footeME L W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -⟩ := hM.quotient h
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; norm_num)
  have hMres := hM.le_oddResidualIn h
  set C := M ⊓ centralizer (W : Set G) with hC
  set L₀ := oddResidualIn C with hL₀
  have hMsup : M ≤ L₀ ⊔ oddCoreIn M := le_oddResidualIn_inf_centralizer_sup hWp hWC hMres
  have hCeven : 2 ∣ Nat.card C := by
    by_contra hodd
    have hCo : Odd (Nat.card C) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    have hL₀1 : L₀ = ⊥ := oddResidualIn_eq_bot_of_odd hCo
    rw [hL₀1, bot_sup_eq] at hMsup
    apply hM.not_odd h
    exact Odd.of_dvd_nat (odd_card_oddCoreIn M) (Subgroup.card_dvd_of_le hMsup)
  obtain ⟨⟨v, hvC⟩, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hCeven
  have hv2 : orderOf v = 2 := by rw [← hv, Subgroup.orderOf_mk]
  set V := zpowers v with hV
  have hVp : IsPGroup 2 V :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hV1 : V ≠ ⊥ := fun h1 => by
    have h2 : v ∈ (⊥ : Subgroup G) := h1 ▸ mem_zpowers v
    rw [mem_bot] at h2
    rw [h2, orderOf_one] at hv2
    omega
  have hVC : V ≤ C := zpowers_le.mpr hvC
  obtain ⟨-, hL₀gen⟩ := le_closure_conjugates hWp hWC hVp hV1 hVC
  have hW'L₀ : ∀ g ∈ C, V.map (MulAut.conj g).toMonoidHom ≤ L₀ := fun g hg => by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hVp hy
    refine mem_oddResidualIn (C.mul_mem (C.mul_mem hg (hVC hy)) (C.inv_mem hg)) ⟨k, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]
  have hK₀ : ∀ w ∈ W, w ≠ 1 → L₀ ≤ footeF L w := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hw) hw1
    rw [← (foote_lemma_4_5_i h hM hw2 (hWC hw)).1]
    refine (closure_le _).mpr fun g hg => subset_closure ⟨?_, hg.2⟩
    have hgC := hg.1
    refine mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp hgC).1, ?_⟩)
    exact centralizer_le (Set.singleton_subset_iff.mpr hw) (mem_inf.mp hgC).2
  have hKN : ∀ w ∈ W, w ≠ 1 →
      centralizer ({w} : Set G) ≤ normalizer (footeF L w : Set G) := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hw) hw1
    obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM hw2 (hWC hw)
    exact le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  have hFX : W ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (hWC hx).1
  have hL₀F : L₀ ≤ centralizer (W : Set G) := (oddResidualIn_le C).trans inf_le_right
  have hL₀M : L₀ ≤ M := (oddResidualIn_le C).trans inf_le_left
  exact le_iSup_of_isKleinFour' hW hFX hL₀F hW'L₀ hVp hL₀gen (footeF L) hK₀ hKN hL₀M hMres
    hMsup

end CFSG.ComponentClassification.Foote47

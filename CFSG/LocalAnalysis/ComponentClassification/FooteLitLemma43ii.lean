module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma43Full
import CFSG.LocalAnalysis.ComponentClassification.FooteLitComponentRigidity

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_centralizer_eq_of_card_two {S : Subgroup G} (hS : Nat.card S = 2) :
    ∃ w ∈ S, w ≠ 1 ∧ centralizer (S : Set G) = centralizer ({w} : Set G) := by
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS]; norm_num)
  obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : S)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine ⟨w, hw, hw1', ?_⟩
  have hzS : zpowers w ≤ S := zpowers_le.mpr hw
  have hcard : Nat.card S ≤ Nat.card (zpowers w) := by
    rw [hS, Nat.card_zpowers]
    have h1 : orderOf (⟨w, hw⟩ : S) ∣ 2 := hS ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1'
    · exact h.ge
  have hSz : S = zpowers w := (Subgroup.eq_of_le_of_card_ge hzS hcard).symm
  rw [hSz, centralizer_zpowers_eq]

theorem le_iSup_of_isKleinFour {E V L₀ W' F : Subgroup G}
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (hL₀E : L₀ ≤ centralizer (E : Set G))
    (hW'L₀ : ∀ g ∈ W', V.map (MulAut.conj g).toMonoidHom ≤ L₀) (hVp : IsPGroup 2 V)
    (hL₀ : L₀ ≤ closure (⋃ g ∈ W', ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)))
    (K : G → Subgroup G) (hK₀ : ∀ e ∈ E, e ≠ 1 → L₀ ≤ K e)
    (hKres : ∀ e ∈ E, e ≠ 1 → K e ≤ oddResidualIn (K e))
    (hEN : ∀ e ∈ E, e ≠ 1 → E ≤ normalizer (K e : Set G))
    (hXN : ∀ f ∈ E, f ≠ 1 → oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ⊓
      centralizer ({f} : Set G) ≤ normalizer (K f : Set G))
    (hMsup : (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤
      L₀ ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e))
    (hF : IsKleinFour F) (hFE : F ≤ E) :
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤ ⨆ w ∈ F, ⨆ (_ : w ≠ 1), K w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e with hM
  set LF := ⨆ w ∈ F, ⨆ (_ : w ≠ 1), K w with hLF
  set X := oddCoreIn M with hX
  have hKM : ∀ e ∈ E, e ≠ 1 → K e ≤ M := fun e he he1 =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), K e) e he
      (le_iSup (fun _ : e ≠ 1 => K e) he1)
  have hKF : ∀ w ∈ F, w ≠ 1 → K w ≤ LF := fun w hw hw1 =>
    le_iSup₂_of_le (f := fun w (_ : w ∈ F) => ⨆ (_ : w ≠ 1), K w) w hw
      (le_iSup (fun _ : w ≠ 1 => K w) hw1)
  obtain ⟨w₀, hw₀, hw₀1, -⟩ := exists_ne_of_isKleinFour hF 1
  have hL₀M : L₀ ≤ M := (hK₀ w₀ (hFE hw₀) hw₀1).trans (hKM w₀ (hFE hw₀) hw₀1)
  have hL₀F : L₀ ≤ LF := (hK₀ w₀ (hFE hw₀) hw₀1).trans (hKF w₀ hw₀ hw₀1)
  have hEM : E ≤ normalizer (M : Set G) := fun x hx => by
    apply mem_normalizer_of_map_conj_eq
    simp only [hM, Subgroup.map_iSup]
    exact iSup_congr fun e => iSup_congr fun he => iSup_congr fun he1 =>
      map_conj_eq_of_mem_normalizer (hEN e he he1 hx)
  have hEX : E ≤ normalizer (X : Set G) := fun x hx => mem_normalizer_oddCoreIn (hEM hx)
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
    have hzN : z ∈ normalizer (K w : Set G) := hXN w (hFE hw) hw1 hz
    rw [commutatorElement_def]
    exact hKF w hw hw1 (mul_mem ((mem_normalizer_iff.mp hzN l).mp (hK₀ w (hFE hw) hw1 hl))
      (inv_mem (hK₀ w (hFE hw) hw1 hl)))
  have hL₀Y : L₀ ≤ normalizer (Y : Set G) := fun l hl => by
    apply mem_normalizer_of_map_conj_eq
    simp only [hY, Subgroup.map_iSup]
    refine iSup_congr fun w => iSup_congr fun hw => iSup_congr fun hw1 => ?_
    rw [Subgroup.map_commutator, map_inf_eq _ _ _ (MulAut.conj l).injective,
      map_conj_eq_of_mem_normalizer (hL₀X hl), map_conj_eq_self_of_mem hl,
      map_conj_eq_of_mem_normalizer (mem_normalizer_centralizer_singleton
        ((mem_centralizer_iff.mp (hL₀E hl)) w (hFE hw)).symm)]
  have hXT : ∀ g ∈ W', ⁅X, V.map (MulAut.conj g).toMonoidHom⁆ ≤ Y := by
    intro g hg
    set T := V.map (MulAut.conj g).toMonoidHom with hT
    have hTp : IsPGroup 2 T := hVp.map _
    have hFel : CFSG.Open.IsElemAbelian 2 F :=
      ⟨@IsKleinFour.isMulCommutative F _ hF, fun x hx => hexp x (hFE hx)⟩
    have hTX : T ≤ normalizer (X : Set G) := (hW'L₀ g hg).trans hL₀X
    have hFT : F ≤ centralizer (T : Set G) := fun x hx => mem_centralizer_iff.mpr
      fun y hy => ((mem_centralizer_iff.mp (hL₀E (hW'L₀ g hg hy))) x (hFE hx)).symm
    rw [CFSG.SignalizerFunctor.Helpers.solvable_normalized_order_fixed_commutator_generation
      2 1 2 Nat.prime_two Nat.prime_two F T X hFel (by rw [hF.card_four]; norm_num) hTp hXs
      (hFE.trans hEX) hTX hFT hXcop hXcop]
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
  have hMres : M ≤ oddResidualIn M := iSup₂_le fun e he => iSup_le fun he1 =>
    (hKres e he he1).trans (oddResidualIn_mono (hKM e he he1))
  have hMR : M ≤ R := by
    refine hMres.trans ((closure_le _).mpr fun g hg => ?_)
    obtain ⟨hgM, h2⟩ := hg
    have hg' : g ∈ X ⊔ R :=
      (sup_le (le_sup_left.trans le_sup_right) le_sup_left : L₀ ⊔ X ≤ X ⊔ R) (hMsup hgM)
    exact mem_of_two_element_of_mem_sup hXR
      (by rw [oddResidualIn_eq_bot_of_odd hXodd]; exact bot_le) hg' h2
  exact hMR.trans (sup_le hL₀F (hXL.trans hYF))

theorem foote_lemma_4_3 (hLB : FooteLBalanceInput) {A E V : Subgroup G}
    [IsSimpleGroup (A ⧸ pPrimeCore 2 A)] (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A)
    (hV : IsKleinFour V) (hVA : V ≤ A ⊓ centralizer (E : Set G))
    (h41 : ∀ a ∈ E, a ≠ 1 → ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)))
    (K : G → Subgroup G) (hK : ∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (K e))
    (hKA : ∀ e ∈ E, e ≠ 1 → oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ K e)
    (hKcard : ∀ e ∈ E, e ≠ 1 →
      Nat.card (K e ⧸ pPrimeCore 2 (K e)) = Nat.card (A ⧸ pPrimeCore 2 A)) :
    (Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e)) ≤ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤
        oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e)) ∧
    ∀ F : Subgroup G, IsKleinFour F → F ≤ E →
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) = ⨆ w ∈ F, ⨆ (_ : w ≠ 1), K w := by
  have hi := foote_lemma_4_3_i hLB hEc hexp h8 hEA hV hVA h41 K hK hKA hKcard
  refine ⟨hi, fun F hF hFE => le_antisymm ?_ ?_⟩
  · set W := A ⊓ centralizer (E : Set G) with hW
    have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
    have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
    have hV1 : V ≠ ⊥ := fun h => by
      have h4 := hV.card_four
      rw [h, card_bot] at h4
      omega
    obtain ⟨-, hL₀gen⟩ := le_closure_conjugates hEp hEA hVp hV1 hVA
    have hW'L₀ : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ oddResidualIn W :=
      fun g hg => by
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hVp hv
        refine mem_oddResidualIn (W.mul_mem (W.mul_mem hg (hVA hv)) (W.inv_mem hg)) ⟨k, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]
    have hK₀ : ∀ e ∈ E, e ≠ 1 → oddResidualIn W ≤ K e := fun e he he1 =>
      (oddResidualIn_mono (inf_le_inf_left A (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr he)))).trans (hKA e he he1)
    have hKres : ∀ e ∈ E, e ≠ 1 → K e ≤ oddResidualIn (K e) := fun e he he1 =>
      (oddResidualIn_eq_self_of_isPComponent (hK e he he1).2.1 (hK e he he1).2.2).ge
    have hEN : ∀ e ∈ E, e ≠ 1 → E ≤ normalizer (K e : Set G) := fun e he he1 a ha =>
      (foote_lemma_4_3_le_coreActionKernel hEc h8 hEA hV hVA K hK hKA hKcard e he he1 ha).1
    have hXN : ∀ f ∈ E, f ≠ 1 → oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ⊓
        centralizer ({f} : Set G) ≤ normalizer (K f : Set G) := fun f hf hf1 =>
      inf_centralizer_le_normalizer_of_odd (hK f hf hf1) (odd_card_oddCoreIn _) fun x hx =>
        mem_normalizer_oddCoreIn (le_normalizer (le_iSup₂_of_le
          (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), K e) f hf
          (le_iSup (fun _ : f ≠ 1 => K f) hf1) hx))
    exact le_iSup_of_isKleinFour hexp ((oddResidualIn_le W).trans inf_le_right) hW'L₀ hVp
      hL₀gen K hK₀ hKres hEN hXN hi.2.2 hF hFE
  · exact iSup₂_le fun w hw => iSup_le fun hw1 =>
      le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), K e) w (hFE hw)
        (le_iSup (fun _ : w ≠ 1 => K w) hw1)

omit [Finite G] in
open Classical in
@[expose] noncomputable def footeF (L : Subgroup G) (a : G) : Subgroup G :=
  if h : ∃ B : Subgroup G, IsTwoComponentAt a B ∧ B ∈ footeFamilyOf L then h.choose else ⊥

omit [Finite G] in
open Classical in
theorem footeF_eq_bot {L : Subgroup G} {a : G}
    (h : ¬ ∃ B : Subgroup G, IsTwoComponentAt a B ∧ B ∈ footeFamilyOf L) : footeF L a = ⊥ := by
  unfold footeF
  rw [dite_eq_right_iff.mpr fun h' => absurd h' h]

omit [Finite G] in
theorem eq_footeF {L : Subgroup G}
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    {a : G} {B : Subgroup G} (hB : IsTwoComponentAt a B) (hBF : B ∈ footeFamilyOf L) :
    footeF L a = B := by
  have h : ∃ B : Subgroup G, IsTwoComponentAt a B ∧ B ∈ footeFamilyOf L := ⟨B, hB, hBF⟩
  unfold footeF
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact huniq a _ _ h.choose_spec.1 hB h.choose_spec.2 hBF

theorem foote_lemma_4_3_of_counterexample (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) [IsSimpleGroup G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {E V : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A) (hV : IsKleinFour V)
    (hVA : V ≤ A ⊓ centralizer (E : Set G)) :
    (∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (footeF L e) ∧ footeF L e ∈ footeFamilyOf L ∧
      centralizer ({e} : Set G) ≤ normalizer (footeF L e : Set G) ∧
      oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ footeF L e) ∧
    (Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (footeF L e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (footeF L e)) ≤
        oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e) ≤
        oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔
          oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e)) ∧
    ∀ F : Subgroup G, IsKleinFour F → F ≤ E →
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e) = ⨆ w ∈ F, ⨆ (_ : w ≠ 1), footeF L w := by
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  have hKspec : ∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (footeF L e) ∧
      footeF L e ∈ footeFamilyOf L ∧
      oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ footeF L e := by
    intro e he he1
    have hord : orderOf e = 2 := orderOf_eq_prime (hexp e he) he1
    obtain ⟨B, hB, -, hBF, hBA⟩ :=
      exists_mem_footeFamilyOf_of_mem_coreActionKernel hLB huniq hAmax hAF hord (hEA he)
    rw [eq_footeF huniq hB hBF]
    exact ⟨hB, hBF, hBA⟩
  have hKN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ normalizer (footeF L e : Set G) :=
    fun e he he1 => le_normalizer_of_mem_footeFamilyOf huniq (hKspec e he he1).1
      (hKspec e he he1).2.1
  have hquot : ∀ B ∈ footeFamilyOf L, (∃ b : G, IsTwoComponentAt b B) →
      Nonempty (B ⧸ pPrimeCore 2 B ≃* L ⧸ Open.fusionZStar L) := by
    intro B hBF hB
    obtain ⟨-, ⟨eBL⟩⟩ := id hBF
    obtain ⟨e₁⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA hB
      (footeFamilyType_of_equiv eBL hLfam) (by rw [hrank2 B hBF])
    exact ⟨e₁.trans eBL⟩
  obtain ⟨eA⟩ := hquot A hAF ⟨z, hAmax.1⟩
  have hsimp : IsSimpleGroup (A ⧸ pPrimeCore 2 A) := by
    obtain ⟨hz, hAz, hApc⟩ := hAmax.1
    obtain ⟨hs, -⟩ := zStarQuotient_simple hApc
    obtain ⟨e₂⟩ := nonempty_quotient_fusionZStar_equiv
      (subgroupOfEquivOfLe hAz : ↥(A.subgroupOf (centralizer ({z} : Set G))) ≃* ↥A)
    obtain ⟨-, ⟨eAL⟩⟩ := id hAF
    exact (e₂.trans (eAL.trans eA.symm)).symm.isSimpleGroup
  have h41 := fun a (ha : a ∈ E) (ha1 : a ≠ 1) =>
    foote_lemma_4_1_of_counterexample hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hce huniq
      hrank2 hAmax hAF hEc hexp h8 hEA hV hVA ha ha1
  have h43 := foote_lemma_4_3 hLB hEc hexp h8 hEA hV hVA h41 (footeF L)
    (fun e he he1 => (hKspec e he he1).1) (fun e he he1 => (hKspec e he he1).2.2)
    (fun e he he1 => by
      obtain ⟨eK⟩ := hquot _ (hKspec e he he1).2.1 ⟨e, (hKspec e he he1).1⟩
      exact Nat.card_congr (eK.trans eA.symm).toEquiv)
  exact ⟨fun e he he1 => ⟨(hKspec e he he1).1, (hKspec e he he1).2.1, hKN e he he1,
    (hKspec e he he1).2.2⟩, h43⟩

end CFSG.ComponentClassification.FooteLit

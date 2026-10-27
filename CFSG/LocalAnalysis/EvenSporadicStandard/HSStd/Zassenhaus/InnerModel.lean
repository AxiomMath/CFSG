module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section Model

set_option linter.unusedSectionVars false

noncomputable def hel (x : Equiv.Perm (Fin 3850)) : ↥hsP := by
  classical
  exact if h : x ∈ hsP then ⟨x, h⟩ else 1

theorem hel_val {x : Equiv.Perm (Fin 3850)} (h : x ∈ hsP) : ((hel x : ↥hsP) : Equiv.Perm (Fin 3850)) = x := by
  simp [hel, h]

noncomputable def zM : ↥hsP := ⟨hsT1, hsT1_mem_ord.1⟩

theorem memC_iff {x : ↥hsP} :
    x ∈ (⊤ ⊓ centralizer ({zM} : Set ↥hsP) : Subgroup ↥hsP) ↔ (x : Equiv.Perm (Fin 3850)) ∈ hsC1 := by
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  refine ⟨fun h => ⟨x.2, ?_⟩, fun h => ⟨mem_top _, ?_⟩⟩
  · exact congrArg Subtype.val h.2
  · exact Subtype.ext h.2

theorem memC_hel {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsC1) :
    hel x ∈ (⊤ ⊓ centralizer ({zM} : Set ↥hsP) : Subgroup ↥hsP) := by
  rw [memC_iff, hel_val (mem_inf.1 hx).1]
  exact hx

theorem hsC1_le {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsC1) : x ∈ hsP := (mem_inf.1 hx).1

theorem coe_wordEval (g y : ↥hsP) (w : List Letter) :
    ((wordEval g y w : ↥hsP) : Equiv.Perm (Fin 3850)) = wordEval (g : Equiv.Perm (Fin 3850)) y w :=
  innerMap_wordEval hsP.subtype g y w

theorem innerWordEval_mem {M : Type*} [Group M] (S : Subgroup M) {g y : M} (hg : g ∈ S) (hy : y ∈ S)
    (w : List Letter) : wordEval g y w ∈ S := by
  refine S.list_prod_mem fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  cases l
  · exact hg
  · exact S.inv_mem hg
  · exact hy

noncomputable abbrev gM : ↥hsP := hel eG
noncomputable abbrev aM : ↥hsP := hel eA
noncomputable abbrev hM : ↥hsP := hel eH
noncomputable abbrev ysM (i : Fin 4) : ↥hsP := hel (eY i)
noncomputable abbrev uM : ↥hsP := hel eU

theorem coe_gM : (gM : Equiv.Perm (Fin 3850)) = eG := hel_val (hsC1_le rep_G.2)
theorem coe_aM : (aM : Equiv.Perm (Fin 3850)) = eA := hel_val (hsC1_le rep_A.2)
theorem coe_hM : (hM : Equiv.Perm (Fin 3850)) = eH := hel_val (hsC1_le rep_H.2)
theorem coe_ysM (i : Fin 4) : (ysM i : Equiv.Perm (Fin 3850)) = eY i :=
  hel_val (hsC1_le (rep_Y i.2).2)
theorem coe_uM : (uM : Equiv.Perm (Fin 3850)) = eU := hel_val rep_U.2

theorem coe_wordEval_a (w : List Letter) :
    ((wordEval gM aM w : ↥hsP) : Equiv.Perm (Fin 3850)) = wordEval eG eA w := by
  rw [coe_wordEval, coe_gM, coe_aM]

theorem coe_wordEval_ys (i : Fin 4) (w : List Letter) :
    ((wordEval gM (ysM i) w : ↥hsP) : Equiv.Perm (Fin 3850)) = wordEval eG (eY i) w := by
  rw [coe_wordEval, coe_gM, coe_ysM]

theorem coe_wb : ((wordEval gM aM wbL : ↥hsP) : Equiv.Perm (Fin 3850)) = eB := coe_wordEval_a _

theorem conjZ (x : ↥hsP) (h2 : (x : Equiv.Perm (Fin 3850)) * x = 1)
    (hf : fixC (x : Equiv.Perm (Fin 3850)) = 170) : ∃ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ = x := by
  obtain ⟨g, hg, e⟩ := conj_t1_of_fix x.2 h2 hf
  exact ⟨⟨g, hg⟩, mem_top _, Subtype.ext e⟩

theorem eB_mem : eB ∈ hsP :=
  innerWordEval_mem hsP (hsC1_le rep_G.2) (hsC1_le rep_A.2) _

theorem conjB_aux {x : Equiv.Perm (Fin 3850)} (hx : ∃ g ∈ hsP, g * hsT2 * g⁻¹ = x) :
    ∃ g ∈ hsP, g * eB * g⁻¹ = x := by
  obtain ⟨g, hg, hxe⟩ := hx
  obtain ⟨g', hg', e'⟩ := conj_t2_of_fix eB_mem eB_facts.1 eB_facts.2
  refine ⟨g * g'⁻¹, hsP.mul_mem hg (hsP.inv_mem hg'), ?_⟩
  rw [← hxe, ← e']
  group

theorem conjB (x : ↥hsP) (h2 : (x : Equiv.Perm (Fin 3850)) * x = 1)
    (hf : fixC (x : Equiv.Perm (Fin 3850)) = 30) :
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = x := by
  obtain ⟨g, hg, e⟩ := conjB_aux (conj_t2_of_fix x.2 h2 hf)
  refine ⟨⟨g, hg⟩, mem_top _, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wb]
  exact e

theorem E_map : (closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j))).map hsP.subtype = Ep := by
  rw [MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor <;> rintro ⟨j, rfl⟩ <;> exact ⟨j, by rw [Subgroup.subtype_apply, coe_wordEval_a]⟩

theorem mem_E {x : ↥hsP} :
    x ∈ closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j)) ↔
      (x : Equiv.Perm (Fin 3850)) ∈ Ep := by
  rw [← E_map]
  exact (Subgroup.mem_map_iff_mem hsP.subtype_injective).symm

theorem m_E_elemAbelian :
    CFSG.Open.IsElemAbelian 2 (closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j))) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [isMulCommutative_iff_of_setLike]
    intro x hx y hy
    exact Subtype.ext (Ep_comm (mem_E.1 hx) (mem_E.1 hy))
  · rw [pow_two]
    exact Subtype.ext (Ep_sq (mem_E.1 hx))

theorem m_E_card :
    Nat.card (closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j))) = 16 := by
  rw [← Subgroup.card_map_of_injective hsP.subtype_injective, E_map, Ep_card]

theorem m_z_mem_E : zM ∈ closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j)) :=
  mem_E.2 hsT1_mem_Ep

theorem m_E_conj : ∀ e ∈ closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j)), e ≠ 1 →
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ = e := by
  intro e he he1
  refine conjZ e (Ep_sq (mem_E.1 he)) (Ep_fix (mem_E.1 he) fun h => he1 (Subtype.ext h))

theorem coe_zM : (zM : Equiv.Perm (Fin 3850)) = hsT1 := by simp only [zM]

theorem eY_facts23 {n : ℕ} (h1 : 2 ≤ n) (h2 : n < 4) :
    eY n * eY n = 1 ∧ fixC (eY n) = 30 := by
  obtain ⟨i', hi', rfl⟩ : ∃ i' < 2, n = i' + 2 := ⟨n - 2, by omega, by omega⟩
  exact eY23_facts hi'

theorem eYB_facts' {n : ℕ} (h1 : 2 ≤ n) (h2 : n < 4) :
    wordEval eG (eY n) wbL * wordEval eG (eY n) wbL = 1 ∧ fixC (wordEval eG (eY n) wbL) = 170 := by
  obtain ⟨i', hi', rfl⟩ : ∃ i' < 2, n = i' + 2 := ⟨n - 2, by omega, by omega⟩
  exact eYB_facts hi'

theorem m_pres : ∀ i : Fin 4, i.val < 2 → (∃ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ = ysM i) ∧
    ∃ c ∈ (⊤ ⊓ centralizer ({zM} : Set ↥hsP) : Subgroup ↥hsP), ∀ j : Fin 4,
      c * wordEval gM (ysM i) (eWF j) * c⁻¹ ∈
        closure (Set.range fun j : Fin 4 => wordEval gM aM (eWF j)) := by
  intro i hi
  obtain ⟨h2, hf, c, hc, hcE⟩ := pres_perm hi
  refine ⟨conjZ (ysM i) (by rw [coe_ysM]; exact h2) (by rw [coe_ysM]; exact hf),
    hel c, memC_hel hc, fun j => ?_⟩
  rw [mem_E]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hel_val (hsC1_le hc), coe_wordEval_ys]
  exact hcE j

theorem m_invol : ∀ x ∈ (⊤ : Subgroup ↥hsP), x ≠ 1 → x * x = 1 →
    (∃ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ = x) ∨
      ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = x := by
  intro x _ hx1 hx2
  have hx2' : (x : Equiv.Perm (Fin 3850)) * x = 1 := congrArg Subtype.val hx2
  rcases inv_conj_cases x.2 (fun h => hx1 (Subtype.ext h)) hx2' with ⟨g, hg, e⟩ | h
  · exact Or.inl ⟨⟨g, hg⟩, mem_top _, Subtype.ext e⟩
  · obtain ⟨g, hg, e⟩ := conjB_aux h
    refine Or.inr ⟨⟨g, hg⟩, mem_top _, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wb]
    exact e

theorem m_not_conj : ∀ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ ≠ wordEval gM aM wbL := by
  intro k _ h
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wb, coe_zM] at h'
  have := congrArg fixC h'
  rw [fixC_conj, fixC_hsT1, eB_facts.2] at this
  omega

theorem m_u_comm : uM * wordEval gM aM wbL = wordEval gM aM wbL * uM := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_wb, coe_uM]
  exact eU_facts.2.2.1

theorem m_u_sq : uM * uM = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one, coe_uM]
  exact eU_facts.1

theorem m_u_ne_one : uM ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_uM] at h'
  exact ne_one_of_fixC eU_facts.2.1 (by norm_num) h'

theorem m_u_ne_b : uM ≠ wordEval gM aM wbL := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_uM, coe_wb] at h'
  have h3 := eU_facts.2.2.2
  rw [h', eB_facts.1, fixC_one] at h3
  omega

theorem m_u_conj : ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = uM :=
  conjB uM (by rw [coe_uM]; exact eU_facts.1) (by rw [coe_uM]; exact eU_facts.2.1)

theorem m_ub_conj :
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = uM * wordEval gM aM wbL := by
  refine conjB (uM * wordEval gM aM wbL) ?_ ?_
  · simp only [Subgroup.coe_mul, coe_wb, coe_uM]
    obtain ⟨hu2, -, hc, -⟩ := eU_facts
    obtain ⟨hb2, -⟩ := eB_facts
    calc eU * eB * (eU * eB) = eU * (eB * eU) * eB := by group
      _ = eU * (eU * eB) * eB := by rw [← hc]
      _ = (eU * eU) * (eB * eB) := by group
      _ = 1 := by rw [hu2, hb2, one_mul]
  · simp only [Subgroup.coe_mul, coe_wb, coe_uM]
    exact eU_facts.2.2.2

theorem m_swap_ys : ∀ i : Fin 4, 2 ≤ i.val →
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = ysM i := by
  intro i hi
  obtain ⟨h1, h2⟩ := eY_facts23 hi i.2
  exact conjB (ysM i) (by rw [coe_ysM]; exact h1) (by rw [coe_ysM]; exact h2)

theorem m_swap_b : ∀ i : Fin 4, 2 ≤ i.val →
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * zM * k⁻¹ = wordEval gM (ysM i) wbL := by
  intro i hi
  obtain ⟨h1, h2⟩ := eYB_facts' hi i.2
  exact conjZ _ (by rw [coe_wordEval_ys]; exact h1) (by rw [coe_wordEval_ys]; exact h2)

@[expose] def zmulF : Fin 8 → Fin 8 := ![2, 3, 0, 1, 6, 7, 4, 5]

@[expose] def sigmaF : Fin 2 → Fin 8 → Fin 8 :=
  ![![0, 1, 3, 2, 4, 5, 7, 6], ![0, 2, 1, 3, 7, 5, 6, 4]]

@[expose] def psiF : Fin 2 → Fin 8 → Fin 8 :=
  ![![0, 6, 2, 4, 1, 7, 3, 5], ![0, 4, 2, 6, 3, 7, 1, 5]]

@[expose] def stabWord : Fin 2 → List (Option (Fin 2)) :=
  ![[none, some 0, none, some 0, none, some 1, none],
    [none, some 1, none, some 0, none, some 0, none]]

theorem zmulF_eq : ∀ e : Fin 8, (zmulF e : ℕ) = zmulL.getD e 0 := by decide

theorem sigmaF_eq : ∀ (j : Fin 2) (e : Fin 8), (sigmaF j e : ℕ) = (sigmaL.getD j []).getD e 0 := by
  decide

theorem psiF_eq : ∀ (j : Fin 2) (e : Fin 8), (psiF j e : ℕ) = (psiL.getD j []).getD e 0 := by
  decide

theorem stabRun_ok : ∀ i : Fin 2,
    stabRun (psiF i) zmulF sigmaF (stabWord i) ((0 : Fin 8), true) = (0, true) ∧
      stabRun (psiF i) zmulF sigmaF (stabWord i) ((1 : Fin 8), false) = (4, false) := by
  decide

theorem m_zmul : ∀ e : Fin 8, wordEval gM aM (yWL e) * zM = wordEval gM aM (yWL (zmulF e)) := by
  intro e
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_wordEval_a, coe_zM, zmulF_eq]
  exact zmul_perm e.2

theorem m_eOne : wordEval gM aM (yWL (0 : Fin 8)) = 1 := by
  apply Subtype.ext
  rw [coe_wordEval_a]
  exact eE8_zero

theorem m_eA : wordEval gM aM (yWL (1 : Fin 8)) = aM := by
  apply Subtype.ext
  rw [coe_wordEval_a, coe_aM]
  exact eE8_one

theorem m_stab : ∀ i : Fin 4, 2 ≤ i.val → ∃ (c : ↥hsP) (ψ : Fin 8 → Fin 8) (m : ℕ)
    (gs : Fin m → ↥hsP) (σ : Fin m → Fin 8 → Fin 8) (word : List (Option (Fin m))) (x : Fin 8),
    c ∈ (⊤ ⊓ centralizer ({zM} : Set ↥hsP) : Subgroup ↥hsP) ∧
    (∀ e : Fin 8, c * wordEval gM (ysM i) (yWL e) * c⁻¹ = wordEval gM aM (yWL (ψ e))) ∧
    (∀ j, gs j ∈ (⊤ : Subgroup ↥hsP) ∧ ∀ e : Fin 8,
      gs j * wordEval gM aM (yWL e) * (gs j)⁻¹ = wordEval gM aM (yWL (σ j e))) ∧
    stabRun ψ zmulF σ word ((0 : Fin 8), true) = (0, true) ∧
    stabRun ψ zmulF σ word ((1 : Fin 8), false) = (x, false) ∧
    ∃ k ∈ (⊤ : Subgroup ↥hsP), k * wordEval gM aM wbL * k⁻¹ = wordEval gM aM (yWL x) := by
  intro i hi
  obtain ⟨i', hii⟩ : ∃ i' : Fin 2, i.val = i'.val + 2 :=
    ⟨⟨i.val - 2, by have := i.2; omega⟩, by simp; omega⟩
  obtain ⟨hs0, hs1⟩ := stabRun_ok i'
  refine ⟨hel (eCS (i'.val + 2)), psiF i', 2, fun j => hel (eGS j), sigmaF, stabWord i', 4,
    memC_hel (rep_CS (i := i'.val + 2) ⟨by omega, by have := i'.2; omega⟩).2, fun e => ?_,
    fun j => ⟨mem_top _, fun e => ?_⟩, hs0, hs1, ⟨1, mem_top _, ?_⟩⟩
  · apply Subtype.ext
    have hc := (rep_CS (i := i'.val + 2) ⟨by omega, by have := i'.2; omega⟩).2
    have e1 : eY i.val = eY (i'.val + 2) := by rw [hii]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hel_val (hsC1_le hc), coe_wordEval_ys,
      coe_wordEval_a, e1, psiF_eq]
    exact cs_perm i'.2 e.2
  · apply Subtype.ext
    have hg := (rep_GS j.2).2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hel_val hg, coe_wordEval_a, sigmaF_eq]
    exact gs_perm j.2 e.2
  · simp only [inv_one, one_mul, mul_one]
    rfl

theorem eq_one_iff (x : ↥hsP) : x = 1 ↔ (x : Equiv.Perm (Fin 3850)) = 1 :=
  ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem wb_odd_aux : Odd (yCount wbL) := by decide

theorem innerData_model : Nonempty (InnerData (⊤ : Subgroup ↥hsP) zM) :=
  ⟨{ g₁ := gM
     a := aM
     g₁_mem := memC_hel rep_G.2
     a_mem := memC_hel rep_A.2
     orderOf_g₁ := by rw [← Subgroup.orderOf_coe, coe_gM]; exact orderOf_eG
     order_five := fun x hx h5 => by
       obtain ⟨c, hc, hce⟩ := order_five_perm (memC_iff.1 hx)
         (by rw [Subgroup.orderOf_coe]; exact h5)
       exact ⟨hel c, memC_hel hc, Subtype.ext (by
         simp only [Subgroup.coe_mul, Subgroup.coe_inv, hel_val (hsC1_le hc), coe_gM]
         exact hce)⟩
     h := hM
     h_mem := memC_hel rep_H.2
     h_comm := Subtype.ext (by
       simp only [Subgroup.coe_mul, coe_hM, coe_gM]
       exact eH_comm)
     ys := ysM
     ys_mem := fun i => memC_hel (rep_Y i.2).2
     filter := fun y hy hyp => by
       have hyp' : ∀ w : List Letter,
           wordEval eG (y : Equiv.Perm (Fin 3850)) w = 1 ↔ wordEval eG eA w = 1 := fun w => by
         have h1 := hyp w
         rw [eq_one_iff, eq_one_iff, coe_wordEval, coe_wordEval, coe_gM, coe_aM] at h1
         exact h1
       obtain ⟨k, i, hi, e⟩ := filter_perm (memC_iff.1 hy) hyp'
       refine ⟨k, ⟨i, hi⟩, Subtype.ext ?_⟩
       simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, coe_hM, coe_ysM]
       exact e
     a_conj := conjZ aM (by rw [coe_aM]; exact eA_facts.1) (by rw [coe_aM]; exact eA_facts.2)
     eW := eWF
     E_elemAbelian := m_E_elemAbelian
     E_card := m_E_card
     z_mem_E := m_z_mem_E
     E_conj := m_E_conj
     pres := m_pres
     wb := wbL
     wb_odd := wb_odd_aux
     invol := m_invol
     not_conj := m_not_conj
     u := uM
     u_mem := mem_top _
     u_comm := m_u_comm
     u_sq := m_u_sq
     u_ne_one := m_u_ne_one
     u_ne_b := m_u_ne_b
     u_conj := m_u_conj
     ub_conj := m_ub_conj
     swap_ys := m_swap_ys
     swap_b := m_swap_b
     yW := fun e => yWL e
     zmul := zmulF
     zmul_spec := m_zmul
     eOne := 0
     eOne_spec := m_eOne
     eA := 1
     eA_spec := m_eA
     stab := m_stab }⟩

end Model

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSTwoB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeFactsModel

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

@[expose] def heGSKW (w : List ℕ) : Equiv.Perm (Fin 8330) := (w.map heInnerCP0).prod

theorem heGSKW_append (a b : List ℕ) : heGSKW (a ++ b) = heGSKW a * heGSKW b := by
  simp only [heGSKW, List.map_append, List.prod_append]

theorem size_wordA_heGS (n : ℕ) (S Sinv : Array (Array ℕ)) (w : List ℤ) :
    (CFSG.Monster.B.Co2.Native.wordA n S Sinv w).size = n := by
  cases w <;> simp [CFSG.Monster.B.Co2.Native.wordA, Native.idA, Native.compA]

theorem heDPerm_mem_D {j : ℕ} (hj : j < 5) : heDPerm j ∈ genGroup 105 heDGens heDPerm :=
  Subgroup.subset_closure ⟨j, by simpa [heDGens] using hj, rfl⟩

theorem heDWords_lt (j : ℕ) :
    ∀ i ∈ heDWords.getD j [], i < 9 := by
  by_cases hj : j < 5
  · exact he_local_basic.2.2 j hj
  · rw [List.getD_eq_default _ _ (by simp [heDWords]; omega)]
    intro i hi
    exact absurd hi List.not_mem_nil

theorem heGSEW_lt (l : List ℕ) : ∀ j ∈ heGSEW l, j < 9 := by
  intro j hj
  simp only [heGSEW, List.mem_flatten, List.mem_map] at hj
  obtain ⟨_, ⟨i, -, rfl⟩, hji⟩ := hj
  exact heDWords_lt i j hji

theorem heGSComm2_lt (L : List (List ℕ)) :
    ∀ j ∈ heGSComm2 L, j < 9 := by
  intro j hj
  simp only [heGSComm2, heGSCommW, List.mem_append, List.mem_reverse] at hj
  rcases hj with (((h | h) | h) | h) | (((h | h) | h) | h) <;> exact heGSEW_lt _ j h

theorem heGSVWord_lt : ∀ j ∈ heGSVWord, j < 9 := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | h
  · norm_num
  · exact heDWords_lt 1 j h

section Tables

theorem tabRep_heGSC0Tabs : ∀ j < heGSC0Tabs.size, TabRep heGSC0Tabs[j]! (heInnerCP0 j) := by
  intro j hj
  have hj9 : j < 9 := by simpa [heGSC0Tabs] using hj
  rw [heGSC0Tabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
  exact tabRep_of_rep (rep_heInnerC0 hj9) (by simp [heInnerC0, size_wordA_heGS])

theorem tabRep_heGSKTab {w : List ℕ} (hw : ∀ j ∈ w, j < 9) : TabRep (heGSKTab w) (heGSKW w) :=
  tabRep_wordTabS tabRep_heGSC0Tabs w fun j hj => by simpa [heGSC0Tabs] using hw j hj

theorem heInnerCP0_mem_C0 {j : ℕ} (hj : j < 9) :
    heInnerCP0 j ∈ centralizerIn heP (heGenPerm 0) :=
  heInnerGrp0_le (Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem heGSKW_mem {w : List ℕ} (hw : ∀ j ∈ w, j < 9) :
    heGSKW w ∈ centralizerIn heP (heGenPerm 0) :=
  (centralizerIn heP (heGenPerm 0)).list_prod_mem fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact heInnerCP0_mem_C0 (hw j hj)

theorem tabRep_heGen0 : TabRep (heGen 0) (heGenPerm 0) :=
  tabRep_of_rep (rep_heGen (by norm_num)) (by simp [heGen, Native.hexTable])

theorem heGenPerm0_sq : heGenPerm 0 * heGenPerm 0 = 1 := by
  rw [← sq, ← orderOf_heA0, pow_orderOf_eq_one]

theorem heInnerCP0_sq {j : ℕ} (hj : j < 9) :
    heInnerCP0 j * heInnerCP0 j = 1 := by
  have h := heGS_layer_check.1 j hj
  have h1 := rep_comp (rep_heInnerC0 hj) (rep_heInnerC0 hj)
  rw [h] at h1
  exact h1.unique TabRep.idTab.2

theorem heGSKW_reverse {w : List ℕ} (hw : ∀ j ∈ w, j < 9) :
    heGSKW w.reverse = (heGSKW w)⁻¹ := by
  induction w with
  | nil => simp [heGSKW]
  | cons j w ih =>
    have hj := hw j List.mem_cons_self
    have hc : (heInnerCP0 j)⁻¹ = heInnerCP0 j := inv_eq_of_mul_eq_one_right (heInnerCP0_sq hj)
    rw [List.reverse_cons, heGSKW_append, ih fun i hi => hw i (List.mem_cons_of_mem _ hi)]
    show (heGSKW w)⁻¹ * (heInnerCP0 j * 1) = (heInnerCP0 j * heGSKW w)⁻¹
    rw [mul_one, mul_inv_rev, hc]

@[expose] def heGSE (j : ℕ) : ↥(centralizerIn heP (heGenPerm 0)) :=
  ⟨heGSKW (heDWords.getD j []), heGSKW_mem (heDWords_lt j)⟩

@[expose] def heGSEC (l : List ℕ) : ↥(centralizerIn heP (heGenPerm 0)) := (l.map heGSE).prod

theorem coe_heGSEC (l : List ℕ) :
    ((heGSEC l : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) =
      heGSKW (heGSEW l) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have e1 : heGSEC (j :: l) = heGSE j * heGSEC l := by simp [heGSEC]
    have e2 : heGSEW (j :: l) = heDWords.getD j [] ++ heGSEW l := by simp [heGSEW]
    rw [e1, coe_mul, ih, e2, heGSKW_append]
    rfl

theorem coe_comm (l l' : List ℕ) :
    ((⁅heGSEC l, heGSEC l'⁆ : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) =
      heGSKW (heGSCommW l l') := by
  rw [commutatorElement_def, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv, coe_heGSEC, coe_heGSEC,
    heGSCommW, heGSKW_append, heGSKW_append, heGSKW_append, heGSKW_reverse (heGSEW_lt l),
    heGSKW_reverse (heGSEW_lt l')]

@[expose] def heGSComm2C (L : List (List ℕ)) : ↥(centralizerIn heP (heGenPerm 0)) :=
  ⁅heGSEC (L.getD 0 []), heGSEC (L.getD 1 [])⁆ * ⁅heGSEC (L.getD 2 []), heGSEC (L.getD 3 [])⁆

theorem coe_heGSComm2C (L : List (List ℕ)) :
    ((heGSComm2C L : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) =
      heGSKW (heGSComm2 L) := by
  rw [heGSComm2C, coe_mul, coe_comm, coe_comm, heGSComm2, heGSKW_append]

@[expose] def heGST0 : ↥(centralizerIn heP (heGenPerm 0)) :=
  ⟨heGenPerm 0, mem_centralizerIn.mpr ⟨heGenPerm_mem (by norm_num), rfl⟩⟩

@[expose] def heGSU : ↥(centralizerIn heP (heGenPerm 0)) := heGSComm2C heGSUComm

@[expose] def heGSV : ↥(centralizerIn heP (heGenPerm 0)) := heGST0 * heGSE 1

theorem coe_heGSV : (heGSV : Equiv.Perm (Fin 8330)) = heGSKW heGSVWord := by
  rw [heGSV, coe_mul]
  show heGenPerm 0 * heGSKW (heDWords.getD 1 []) = heInnerCP0 0 * heGSKW (heDWords.getD 1 [])
  rw [heInnerCP0_zero]

theorem tabRep_heGSVTab : TabRep heGSVTab (heGSV : Equiv.Perm (Fin 8330)) := by
  rw [coe_heGSV]
  exact tabRep_heGSKTab heGSVWord_lt

end Tables

section Rho

theorem rho0_eq_of_agree (x : ↥(centralizerIn heP (heGenPerm 0))) {σ : Equiv.Perm (Fin 105)}
    (h : ∀ k, (x : Equiv.Perm (Fin 8330)) (listPt 8330 heOmega0 k) =
      listPt 8330 heOmega0 (σ k)) : HeLay.rho0 x = σ := by
  simp only [HeLay.rho0, heRho0, MonoidHom.comp_apply]
  exact restrictHom_eq_of_agree heOmega0_facts.2 heInnerGrp0_stab' _ h

theorem rho0_eq_one_of_fixesOK {x : ↥(centralizerIn heP (heGenPerm 0))} {t : Tab}
    (ht : Rep 8330 t x) (h : fixesOK 105 t heOmega0 = true) : HeLay.rho0 x = 1 := by
  refine rho0_eq_of_agree x fun k => ?_
  apply Fin.ext
  simp only [fixesOK, allLt_iff, beq_iff_eq] at h
  rw [← ht, Equiv.Perm.one_apply, listPt_val_of_lt heOmega0_facts.1]
  exact h k k.2

theorem rho0_heGSKW {w : List ℕ} (hw : ∀ j ∈ w, j < 9) :
    HeLay.rho0 ⟨heGSKW w, heGSKW_mem hw⟩ = (w.map heKPerm).prod := by
  induction w with
  | nil =>
    have e : (⟨heGSKW [], heGSKW_mem hw⟩ : ↥(centralizerIn heP (heGenPerm 0))) = 1 :=
      Subtype.ext rfl
    rw [e, map_one]
    rfl
  | cons j w ih =>
    have hj := hw j List.mem_cons_self
    have hw' : ∀ i ∈ w, i < 9 := fun i hi => hw i (List.mem_cons_of_mem _ hi)
    have e : (⟨heGSKW (j :: w), heGSKW_mem hw⟩ : ↥(centralizerIn heP (heGenPerm 0))) =
        ⟨heInnerCP0 j, heInnerCP0_mem_C0 hj⟩ * ⟨heGSKW w, heGSKW_mem hw'⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, ih hw', List.map_cons, List.prod_cons,
      rho0_eq_of_agree _ fun k => heInnerCP0_agree' hj k]

theorem rho0_heGSE (j : ℕ) : HeLay.rho0 (heGSE j) = heDPerm j := rho0_heGSKW (heDWords_lt j)

theorem rho0_heGSEC_mem {l : List ℕ} (hl : ∀ j ∈ l, j < 5) :
    HeLay.rho0 (heGSEC l) ∈ genGroup 105 heDGens heDPerm := by
  rw [heGSEC, map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  rw [Function.comp_apply, rho0_heGSE]
  exact heDPerm_mem_D (hl j hj)

theorem ker_comm {a b : ↥(centralizerIn heP (heGenPerm 0))} (ha : a ∈ HeLay.rho0.ker)
    (hb : b ∈ HeLay.rho0.ker) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : Nat.card ↥HeLay.rho0.ker = 2 ^ 2 := by rw [HeLay.card_rho0_ker]; norm_num
  exact congrArg Subtype.val
    ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hG).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem heGST0_mem_ker : heGST0 ∈ HeLay.rho0.ker :=
  rho0_eq_one_of_fixesOK (rep_heGen (by norm_num)) heGS_layer_check.2.2.1

theorem coe_heGSU : (heGSU : Equiv.Perm (Fin 8330)) = heGSKW (heGSComm2 heGSUComm) :=
  coe_heGSComm2C _

theorem heGSU_mem_ker : heGSU ∈ HeLay.rho0.ker := by
  refine rho0_eq_one_of_fixesOK (t := heGSKTab (heGSComm2 heGSUComm)) ?_
    heGS_layer_check.2.2.2.1
  rw [coe_heGSU]
  exact (tabRep_heGSKTab (heGSComm2_lt _)).2

theorem heGST0_eq : heGST0 = heGSComm2C heGST0Comm := by
  apply Subtype.ext
  rw [coe_heGSComm2C]
  have h := tabRep_heGSKTab (heGSComm2_lt heGST0Comm)
  rw [heGS_layer_check.2.1] at h
  exact tabRep_heGen0.perm_eq h

theorem mem_ker_rho0 {k : ↥(centralizerIn heP (heGenPerm 0))} (hk : k ∈ HeLay.rho0.ker) :
    k = 1 ∨ k = heGST0 ∨ k = heGSU ∨ k = heGST0 * heGSU := by
  obtain ⟨-, -, -, -, hu1, hut, -⟩ := heGS_layer_check
  have hU := tabRep_heGSKTab (heGSComm2_lt heGSUComm)
  have ht1 : heGST0 ≠ 1 := fun h => heA0_ne_one (congrArg Subtype.val h)
  have hu1' : heGSU ≠ 1 := fun h => hu1 ((hU.eq_iff TabRep.idTab).2 (by
    rw [← coe_heGSU]; exact congrArg Subtype.val h))
  have hut' : heGSU ≠ heGST0 := fun h => hut ((hU.eq_iff tabRep_heGen0).2 (by
    rw [← coe_heGSU]; exact congrArg Subtype.val h))
  have htt : heGST0 * heGST0 = 1 := Subtype.ext heGenPerm0_sq
  have htinv : heGST0⁻¹ = heGST0 := inv_eq_of_mul_eq_one_right htt
  have h1 : (1 : ↥(centralizerIn heP (heGenPerm 0))) ∉
      ({heGST0, heGSU, heGST0 * heGSU} : Set ↥(centralizerIn heP (heGenPerm 0))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨ht1.symm, hu1'.symm, fun h => hut' ?_⟩
    rw [← htinv]
    exact eq_inv_of_mul_eq_one_right h.symm
  have h2 : heGST0 ∉ ({heGSU, heGST0 * heGSU} : Set ↥(centralizerIn heP (heGenPerm 0))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hut'.symm, fun h => hu1' (by simpa using h.symm)⟩
  have h3 : heGSU ≠ heGST0 * heGSU := fun h => ht1 (by simpa using h.symm)
  have hS : ({1, heGST0, heGSU, heGST0 * heGSU} : Set ↥(centralizerIn heP (heGenPerm 0))) ⊆
      HeLay.rho0.ker := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact heGST0_mem_ker
    · exact heGSU_mem_ker
    · exact mul_mem heGST0_mem_ker heGSU_mem_ker
  have hcard : ({1, heGST0, heGSU, heGST0 * heGSU} :
      Set ↥(centralizerIn heP (heGenPerm 0))).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  have heq := Set.eq_of_subset_of_ncard_le hS (by
    rw [hcard, ← Nat.card_coe_set_eq]
    exact HeLay.card_rho0_ker.le) (Set.toFinite _)
  have hk' : k ∈ ({1, heGST0, heGSU, heGST0 * heGSU} :
      Set ↥(centralizerIn heP (heGenPerm 0))) := by
    rw [heq]
    exact hk
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk'

theorem rho0_heGSV : HeLay.rho0 heGSV = heDPerm 1 := by
  rw [heGSV, map_mul, MonoidHom.mem_ker.mp heGST0_mem_ker, one_mul, rho0_heGSE]

end Rho

section Layer

theorem layer_facts : (pLayer ↥(centralizerIn heP (heGenPerm 0)) 2).Normal ∧
    ⁅pLayer ↥(centralizerIn heP (heGenPerm 0)) 2, pLayer ↥(centralizerIn heP (heGenPerm 0)) 2⁆ =
      pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 ∧
    (pLayer ↥(centralizerIn heP (heGenPerm 0)) 2).map HeLay.rho0 =
      genGroup 105 heDGens heDPerm := by
  obtain ⟨N, -, -, hl, hp, -, hn, hm⟩ := HeLay.layer_t0
  rw [hl]
  exact ⟨hn, hp, hm⟩

theorem layer_comm_ker {n k : ↥(centralizerIn heP (heGenPerm 0))}
    (hn : n ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2) (hk : k ∈ HeLay.rho0.ker) :
    n * k = k * n := by
  have h := HeLay.commute_of_perfect_of_card_four (K := HeLay.rho0.ker) layer_facts.2.1
    HeLay.card_rho0_ker n hn k hk
  calc n * k = n * k * n⁻¹ * n := by group
    _ = k * n := by rw [h]

theorem exists_layer_of_mem_D {x : ↥(centralizerIn heP (heGenPerm 0))}
    (hx : HeLay.rho0 x ∈ genGroup 105 heDGens heDPerm) :
    ∃ k ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2, k⁻¹ * x ∈ HeLay.rho0.ker := by
  rw [← layer_facts.2.2] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  refine ⟨k, hk, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]

theorem comm_mem_layer {x y : ↥(centralizerIn heP (heGenPerm 0))}
    (hx : HeLay.rho0 x ∈ genGroup 105 heDGens heDPerm)
    (hy : HeLay.rho0 y ∈ genGroup 105 heDGens heDPerm) :
    ⁅x, y⁆ ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  obtain ⟨k, hk, hkx⟩ := exists_layer_of_mem_D hx
  obtain ⟨l, hl, hly⟩ := exists_layer_of_mem_D hy
  obtain ⟨a, ha, hxa⟩ : ∃ a ∈ HeLay.rho0.ker, x = k * a := ⟨k⁻¹ * x, hkx, by group⟩
  obtain ⟨b, hb, hyb⟩ : ∃ b ∈ HeLay.rho0.ker, y = l * b := ⟨l⁻¹ * y, hly, by group⟩
  have e1 : a * l = l * a := (layer_comm_ker hl ha).symm
  have e2 : a * b = b * a := ker_comm ha hb
  have e3 : b * k⁻¹ = k⁻¹ * b := (layer_comm_ker (inv_mem hk) hb).symm
  have h : ⁅x, y⁆ = ⁅k, l⁆ :=
    calc ⁅x, y⁆ = k * (a * l) * b * a⁻¹ * k⁻¹ * b⁻¹ * l⁻¹ := by
          rw [hxa, hyb, commutatorElement_def]; group
      _ = k * l * (a * b) * a⁻¹ * k⁻¹ * b⁻¹ * l⁻¹ := by rw [e1]; group
      _ = k * l * (b * k⁻¹) * b⁻¹ * l⁻¹ := by rw [e2]; group
      _ = k * l * (k⁻¹ * b) * b⁻¹ * l⁻¹ := by rw [e3]
      _ = ⁅k, l⁆ := by rw [commutatorElement_def]; group
  rw [h, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hk hl) (inv_mem hk)) (inv_mem hl)

theorem heGST0_mem_layer : heGST0 ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  rw [heGST0_eq, heGSComm2C]
  exact mul_mem (comm_mem_layer (rho0_heGSEC_mem (by decide)) (rho0_heGSEC_mem (by decide)))
    (comm_mem_layer (rho0_heGSEC_mem (by decide)) (rho0_heGSEC_mem (by decide)))

theorem heGSU_mem_layer : heGSU ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  rw [heGSU, heGSComm2C]
  exact mul_mem (comm_mem_layer (rho0_heGSEC_mem (by decide)) (rho0_heGSEC_mem (by decide)))
    (comm_mem_layer (rho0_heGSEC_mem (by decide)) (rho0_heGSEC_mem (by decide)))

theorem ker_le_layer : HeLay.rho0.ker ≤ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  intro k hk
  rcases mem_ker_rho0 hk with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact heGST0_mem_layer
  · exact heGSU_mem_layer
  · exact mul_mem heGST0_mem_layer heGSU_mem_layer

theorem mem_layer_of_rho0_mem {x : ↥(centralizerIn heP (heGenPerm 0))}
    (hx : HeLay.rho0 x ∈ genGroup 105 heDGens heDPerm) :
    x ∈ pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  obtain ⟨k, hk, hkx⟩ := exists_layer_of_mem_D hx
  have h := mul_mem hk (ker_le_layer hkx)
  rwa [mul_inv_cancel_left] at h

theorem mem_heK0_of_rho0_mem {x : ↥(centralizerIn heP (heGenPerm 0))}
    (hx : HeLay.rho0 x ∈ genGroup 105 heDGens heDPerm) :
    (x : Equiv.Perm (Fin 8330)) ∈ heK0 :=
  mem_map_of_mem _ (mem_layer_of_rho0_mem hx)

theorem heGSV_mem_conjClass :
    (heGSV : Equiv.Perm (Fin 8330)) ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  obtain ⟨-, -, -, -, -, -, hv2, hv1, hvf, -⟩ := heGS_layer_check
  exact mem_conjClass_t0_of_tab tabRep_heGSVTab (mem_centralizerIn.mp heGSV.2).1 hv2 hv1 hvf

theorem heldTwoAPairModel : HeldTwoAPairModel := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnc, hnc', -⟩ := heGS_layer_check
  have hE0T := tabRep_heGSKTab (heDWords_lt 0)
  have hE1T := tabRep_heGSKTab (heDWords_lt 1)
  have he0K : ((heGSE 0 : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) ∈ heK0 :=
    mem_heK0_of_rho0_mem (by rw [rho0_heGSE]; exact heDPerm_mem_D (by norm_num))
  refine ⟨heGSV, mem_heK0_of_rho0_mem (by
    rw [rho0_heGSV]; exact heDPerm_mem_D (by norm_num)), heGSV_mem_conjClass, ?_, ?_⟩
  · intro hZ
    rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff] at hZ
    apply hnc
    rw [(hE0T.comp tabRep_heGSVTab).eq_iff (tabRep_heGSVTab.comp hE0T)]
    exact hZ.2 _ he0K
  · intro hZ
    rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff] at hZ
    apply hnc'
    have he1 : heGenPerm 0 * (heGSV : Equiv.Perm (Fin 8330)) = heGSKW (heDWords.getD 1 []) := by
      rw [heGSV, coe_mul]
      show heGenPerm 0 * (heGenPerm 0 * heGSKW (heDWords.getD 1 [])) = _
      rw [← mul_assoc, heGenPerm0_sq, one_mul]
    rw [(hE0T.comp hE1T).eq_iff (hE1T.comp hE0T), ← he1]
    exact hZ.2 _ he0K

end Layer

end CFSG.ComponentClassification.GrSLit.HeGS

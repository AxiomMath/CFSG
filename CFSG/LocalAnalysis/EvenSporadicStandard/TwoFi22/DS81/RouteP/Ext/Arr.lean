module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Sound
public import Certificates.Data.RouteP.M24Defect
public import CFSG.Sporadic.Bridge.TwoGen

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen Certificates.RouteP.M24Defect

theorem idA_getElem_bang {i : ℕ} (hi : i < 24) : idA[i]! = i := by
  simp [idA, hi]

theorem compA_getElem_bang (a b : Array ℕ) {i : ℕ} (hi : i < 24) :
    (compA a b)[i]! = a[b[i]!]! := by
  simp [compA, hi]

theorem hasArr_one : HasArr (1 : Equiv.Perm (Fin 24)) idA := fun i => by
  rw [idA_getElem_bang i.2]
  rfl

theorem HasArr.mul {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : HasArr (σ * τ) (compA a b) := fun i => by
  rw [compA_getElem_bang a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem HasArr.unique {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext (by rw [hσ, hτ])

theorem HasArr.inv_of {σ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hb : ∀ i < 24, b[i]! < 24 ∧ a[b[i]!]! = i) : HasArr σ⁻¹ b := fun i => by
  obtain ⟨h1, h2⟩ := hb i i.2
  have h : i = σ ⟨b[(i : ℕ)]!, h1⟩ := Fin.ext (by rw [hσ]; exact h2.symm)
  have := congrArg Fin.val (Equiv.Perm.inv_eq_iff_eq.2 h)
  exact this

@[expose] noncomputable def genA : ↥AutPerm := ⟨bridgePA, bridgePA_mem⟩

@[expose] noncomputable def genB : ↥AutPerm := ⟨bridgePB⁻¹, AutPerm.inv_mem bridgePB_mem⟩

theorem hasArr_bridgePA : HasArr bridgePA aArr := fun i => by
  rw [bridgePA_image]
  revert i
  decide

theorem hasArr_bridgePB : HasArr bridgePB bInv := fun i => by
  rw [bridgePB_image]
  revert i
  decide

theorem hasArr_genA : HasArr (genA : Equiv.Perm (Fin 24)) aArr := hasArr_bridgePA

theorem hasArr_genA_inv : HasArr (genA : Equiv.Perm (Fin 24))⁻¹ aInv :=
  HasArr.inv_of hasArr_bridgePA (by decide)

theorem hasArr_genB : HasArr (genB : Equiv.Perm (Fin 24)) bArr :=
  HasArr.inv_of hasArr_bridgePB (by decide)

theorem hasArr_genB_inv : HasArr (genB : Equiv.Perm (Fin 24))⁻¹ bInv := by
  have h : (genB : Equiv.Perm (Fin 24))⁻¹ = bridgePB := inv_inv _
  rw [h]
  exact hasArr_bridgePB


@[expose] noncomputable def gens : ℕ → ↥AutPerm := img2 genA genB

theorem hasArr_letterVal (l : ℕ × Bool) (hl : l.1 < 2) :
    HasArr ((letterVal gens l : ↥AutPerm) : Equiv.Perm (Fin 24)) (letArr l.1 l.2) := by
  obtain ⟨i, s⟩ := l
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> cases s
  · simpa [letterVal, gens, img2, letArr] using hasArr_genA_inv
  · simpa [letterVal, gens, img2, letArr] using hasArr_genA
  · simpa [letterVal, gens, img2, letArr] using hasArr_genB_inv
  · simpa [letterVal, gens, img2, letArr] using hasArr_genB

theorem hasArr_letterVal_inv (l : ℕ × Bool) (hl : l.1 < 2) :
    HasArr ((letterVal gens l : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ (letArr l.1 (!l.2)) := by
  obtain ⟨i, s⟩ := l
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> cases s
  · simpa [letterVal, gens, img2, letArr] using hasArr_genA
  · simpa [letterVal, gens, img2, letArr] using hasArr_genA_inv
  · simpa [letterVal, gens, img2, letArr] using hasArr_genB
  · simpa [letterVal, gens, img2, letArr] using hasArr_genB_inv

theorem hasArr_wordProd : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, l.1 < 2) →
    HasArr ((wordProd gens w : ↥AutPerm) : Equiv.Perm (Fin 24)) (wordA w)
  | [], _ => by
    rw [wordProd_nil, Subgroup.coe_one]
    exact hasArr_one
  | l :: w, hw => by
    rw [wordProd_cons, Subgroup.coe_mul]
    exact HasArr.mul (hasArr_letterVal l (hw l List.mem_cons_self))
      (hasArr_wordProd w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem hasArr_wordProd_inv : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, l.1 < 2) →
    HasArr ((wordProd gens w : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ (wordAInv w)
  | [], _ => by
    rw [wordProd_nil, Subgroup.coe_one, inv_one]
    exact hasArr_one
  | l :: w, hw => by
    rw [wordProd_cons, Subgroup.coe_mul, mul_inv_rev]
    exact HasArr.mul (hasArr_wordProd_inv w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (hasArr_letterVal_inv l (hw l List.mem_cons_self))

@[expose] def HAOK (st : HA) (h : ↥AutPerm) : Prop :=
  HasArr (h : Equiv.Perm (Fin 24)) st.fwd ∧ HasArr (h : Equiv.Perm (Fin 24))⁻¹ st.bwd

theorem HAOK.one : HAOK HA.one 1 := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.coe_one]
    exact hasArr_one
  · rw [Subgroup.coe_one, inv_one]
    exact hasArr_one

theorem HAOK.step {st : HA} {h : ↥AutPerm} (hst : HAOK st h) (l : ℕ × Bool) (hl : l.1 < 2) :
    HAOK (st.step l.1 l.2) (h * letterVal gens l) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.coe_mul]
    exact HasArr.mul hst.1 (hasArr_letterVal l hl)
  · rw [Subgroup.coe_mul, mul_inv_rev]
    exact HasArr.mul (hasArr_letterVal_inv l hl) hst.2

theorem edgeStates_forall₂ : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, l.1 < 2) → ∀ (st : HA)
    (h : ↥AutPerm), HAOK st h →
    List.Forall₂ (fun (e : HA × ℕ) (e' : ↥AutPerm × ℕ) => HAOK e.1 e'.1 ∧ e.2 = e'.2 ∧ e.2 < 2)
      (edgeStates w st) (walkEdges gens w h)
  | [], _, _, _, _ => by simp [edgeStates]
  | (i, s) :: w, hw, st, h, hst => by
    have hi : i < 2 := hw (i, s) List.mem_cons_self
    rw [edgeStates, walkEdges_cons]
    refine List.Forall₂.cons ?_ (edgeStates_forall₂ w
      (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) (st.step i s)
      (h * letterVal gens (i, s)) (hst.step (i, s) hi))
    cases s
    · refine ⟨?_, rfl, hi⟩
      have := hst.step (i, false) hi
      simpa [letterVal] using this
    · exact ⟨hst, rfl, hi⟩


theorem relWords_letters : ∀ w ∈ relWords, ∀ l ∈ w, l.1 < 2 := by decide

theorem wordProd_relWords (h : relsOK = true) : ∀ w ∈ relWords, wordProd gens w = 1 := by
  intro w hw
  have h1 : wordA w = idA := by
    have := List.all_eq_true.1 h w hw
    simpa using this
  have h2 := hasArr_wordProd w (relWords_letters w hw)
  rw [h1] at h2
  exact Subtype.ext (HasArr.unique h2 hasArr_one)

theorem treeOK_spec {tab : Array (List (ℕ × Bool))} (h : treeOK tab = true) :
    ∀ u < 24, ∀ v < 24, u ≠ v →
      (wordAInv (tword tab (24 * u + v)))[0]! = u ∧
        (wordAInv (tword tab (24 * u + v)))[1]! = v := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  intro u hu v hv huv
  rcases h.2 u hu v hv with h1 | h1
  · exact absurd h1 huv
  · exact h1

theorem treeLetters_spec {tab : Array (List (ℕ × Bool))} (h : treeLetters tab = true) :
    ∀ c, ∀ l ∈ tword tab c, l.1 < 2 := by
  intro c l hl
  by_cases hc : c < tab.size
  · have h1 : tword tab c = tab[c] := by simp [tword, hc]
    rw [h1] at hl
    unfold treeLetters at h
    rw [Array.all_eq_true] at h
    have h2 := h c hc
    rw [List.all_eq_true] at h2
    have h3 := h2 l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    exact h3.1
  · have h1 : tword tab c = [] := by
      simp [tword, hc]
      rfl
    rw [h1] at hl
    exact absurd hl (List.not_mem_nil)

@[expose] def K22 : Subgroup ↥AutPerm := mog22.subgroupOf AutPerm

theorem mem_K22_iff {h : ↥AutPerm} :
    h ∈ K22 ↔ (h : Equiv.Perm (Fin 24)) 0 = 0 ∧ (h : Equiv.Perm (Fin 24)) 1 = 1 := by
  simp only [K22, Subgroup.mem_subgroupOf, mog22, Subgroup.mem_inf, mem_stab_iff]
  exact ⟨fun h' => ⟨h'.1.2, h'.2⟩, fun h' => ⟨⟨h.2, h'.1⟩, h'.2⟩⟩

@[expose] def qFun (h : ↥AutPerm) : ℕ :=
  24 * ((h : Equiv.Perm (Fin 24))⁻¹ 0 : ℕ) + ((h : Equiv.Perm (Fin 24))⁻¹ 1 : ℕ)

@[expose] noncomputable def trFun (c : ℕ) : ↥AutPerm :=
  wordProd gens (tword (treeTab ()) c)

theorem qFun_mul {k : ↥AutPerm} (hk : k ∈ K22) (h : ↥AutPerm) : qFun (k * h) = qFun h := by
  obtain ⟨hk0, hk1⟩ := mem_K22_iff.1 hk
  have e0 : (k : Equiv.Perm (Fin 24))⁻¹ 0 = 0 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hk0.symm
  have e1 : (k : Equiv.Perm (Fin 24))⁻¹ 1 = 1 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hk1.symm
  simp only [qFun, Subgroup.coe_mul, mul_inv_rev, Equiv.Perm.mul_apply, e0, e1]

theorem kOf_trFun_mem (hC : treeOK (treeTab ()) = true) (hL : treeLetters (treeTab ()) = true)
    (h : ↥AutPerm) : kOf qFun trFun h ∈ K22 := by
  have huv : (((h : Equiv.Perm (Fin 24))⁻¹ 0 : Fin 24) : ℕ) ≠
      (((h : Equiv.Perm (Fin 24))⁻¹ 1 : Fin 24) : ℕ) := by
    intro huv
    have h1 : (h : Equiv.Perm (Fin 24))⁻¹ 0 = (h : Equiv.Perm (Fin 24))⁻¹ 1 := Fin.ext huv
    exact absurd ((h : Equiv.Perm (Fin 24))⁻¹.injective h1) (by decide)
  set u : Fin 24 := (h : Equiv.Perm (Fin 24))⁻¹ 0 with hu
  set v : Fin 24 := (h : Equiv.Perm (Fin 24))⁻¹ 1 with hv
  have hq : qFun h = 24 * (u : ℕ) + (v : ℕ) := rfl
  obtain ⟨t0, t1⟩ := treeOK_spec hC u u.2 v v.2 huv
  have hinv := hasArr_wordProd_inv (tword (treeTab ()) (24 * (u : ℕ) + (v : ℕ)))
    (treeLetters_spec hL _)
  have htr : trFun (qFun h) = wordProd gens (tword (treeTab ()) (24 * (u : ℕ) + (v : ℕ))) := by
    rw [hq]
    rfl
  have e0 : ((trFun (qFun h) : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 0 = u := by
    refine Fin.ext ?_
    rw [htr]
    have h0 := hinv 0
    simp only [Fin.val_zero] at h0
    rw [h0, t0]
  have e1 : ((trFun (qFun h) : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 1 = v := by
    refine Fin.ext ?_
    rw [htr]
    have h1 := hinv 1
    simp only [Fin.val_one] at h1
    rw [h1, t1]
  rw [mem_K22_iff]
  simp only [kOf, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, e0, e1]
  refine ⟨?_, ?_⟩
  · rw [hu, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  · rw [hv, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem ptIdx_eq {st : HA} {h : ↥AutPerm} (hst : HAOK st h) : ptIdx st = qFun h := by
  have h0 := hst.2 0
  have h1 := hst.2 1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  simp only [ptIdx, qFun, h0, h1]

theorem hasArr_kOf (hL : treeLetters (treeTab ()) = true) {st : HA} {h : ↥AutPerm}
    (hst : HAOK st h) :
    HasArr ((kOf qFun trFun h : ↥AutPerm) : Equiv.Perm (Fin 24)) (kArr (treeTab ()) st) := by
  have hinv := hasArr_wordProd_inv (tword (treeTab ()) (qFun h)) (treeLetters_spec hL _)
  rw [kOf, Subgroup.coe_mul, Subgroup.coe_inv, kArr, ptIdx_eq hst]
  exact HasArr.mul hst.1 hinv

theorem haOK_startHA (hL : treeLetters (treeTab ()) = true) (p : ℕ) :
    HAOK (startHA (treeTab ()) p) (trFun p) :=
  ⟨hasArr_wordProd _ (treeLetters_spec hL p), hasArr_wordProd_inv _ (treeLetters_spec hL p)⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

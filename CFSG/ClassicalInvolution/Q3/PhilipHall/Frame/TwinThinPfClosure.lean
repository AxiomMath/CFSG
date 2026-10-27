module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

@[expose] def vecOf (s : List (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ s then 1 else 0

@[expose] def indV (α : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ α then 1 else 0

@[expose] def okItem (F : List (Finset (Fin n))) (α : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ZMod 2) : Prop :=
  (∀ s ∈ F, s.map σ.toEmbedding ∈ F ∧ s.map σ⁻¹.toEmbedding ∈ F) ∧ σ ^ 3 = 1 ∧
    Equiv.Perm.sign σ = 1 ∧ α.map σ.toEmbedding = α ∧ ∑ i, v i = 0

instance (F : List (Finset (Fin n))) (α : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ZMod 2) : Decidable (okItem F α σ v) := by
  unfold okItem; infer_instance

@[expose] def basic (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) : Wr n :=
  ofVec v * ofPerm σ * (ofVec v)⁻¹ * (ofPerm σ)⁻¹

@[expose] def basicVec (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => v i + v (σ⁻¹ i)

@[expose] def certOk (F : List (Finset (Fin n))) (α β : Finset (Fin n))
    (items : List (Equiv.Perm (Fin n) × (Fin n → ZMod 2))) : Prop :=
  (∀ p ∈ items, okItem F α p.1 p.2) ∧
    ((items.map fun p => basicVec p.1 p.2).sum = indV β ∨
      (items.map fun p => basicVec p.1 p.2).sum = fun i => indV β i + 1)

instance (F : List (Finset (Fin n))) (α β : Finset (Fin n))
    (items : List (Equiv.Perm (Fin n) × (Fin n → ZMod 2))) : Decidable (certOk F α β items) := by
  unfold certOk; infer_instance

theorem basic_eq (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    basic σ v = ofVec (basicVec σ v) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (v i + 0 + v (σ.symm i)) + 0 = v i + v (σ⁻¹ i)
    simp [Equiv.Perm.inv_def]
  · show σ * 1 * σ⁻¹ = 1
    simp

theorem ofVec_mul (a b : Fin n → ZMod 2) : ofVec a * ofVec b = ofVec (a + b) := rfl

theorem prod_ofVec (l : List (Fin n → ZMod 2)) : (l.map ofVec).prod = ofVec l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.prod_cons, ih, ofVec_mul, List.sum_cons]

theorem zOf_emb (α : Finset (Fin n)) (h : α.card = 4) : zOf (emb α h) = ofVec (indV α) := by
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  show (zOf (emb α h)).vec x = indV α x
  rw [zOf_vec_apply]
  exact if_congr (by rw [range_emb]; rfl) rfl rfl

theorem ofVec_comm (v w : Fin n → ZMod 2) : ofVec v * ofVec w = ofVec w * ofVec v := by
  refine Wr.ext (funext fun i => ?_) rfl
  show v i + w ((1 : Equiv.Perm (Fin n)).symm i) = w i + v ((1 : Equiv.Perm (Fin n)).symm i)
  exact add_comm _ _

theorem ofPerm_comm_indV {σ : Equiv.Perm (Fin n)} {α : Finset (Fin n)}
    (hα : α.map σ.toEmbedding = α) : ofPerm σ * ofVec (indV α) = ofVec (indV α) * ofPerm σ := by
  refine Wr.ext (funext fun i => ?_) rfl
  show (0 : ZMod 2) + indV α (σ.symm i) = indV α i + 0
  have key : σ.symm i ∈ α ↔ i ∈ α := by
    have := Finset.mem_map_equiv (f := σ) (b := i) (s := α)
    rw [hα] at this
    exact this.symm
  simp only [indV, zero_add, add_zero, key]

variable {F : List (Finset (Fin n))}

theorem ofVec_mem {A : Subgroup (Equiv.Perm (Fin n))} {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) :
    ofVec v ∈ aeSubOver A := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hv
  · show Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) = 1
    exact map_one _
  · show (1 : Equiv.Perm (Fin n)) ∈ A
    exact A.one_mem

theorem ofPerm_mem {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ stabFamily F)
    (hs : Equiv.Perm.sign σ = 1) : ofPerm σ ∈ aeSubOver (stabFamily F) := by
  refine ⟨⟨?_, hs⟩, hσ⟩
  exact Finset.sum_eq_zero fun _ _ => rfl

@[expose] def genSet (F : List (Finset (Fin n))) (α : Finset (Fin n)) (h : α.card = 4) :
    Set (AEQ n) :=
  {x | x ∈ aeBarOver (stabFamily F) ∧ x * zBar α h = zBar α h * x ∧ x ^ 3 = 1}

theorem mkQ_mem_genSet {α : Finset (Fin n)} (h : α.card = 4) {w : Wr n}
    (hw : w ∈ aeSubOver (stabFamily F)) (hc : w * ofVec (indV α) = ofVec (indV α) * w)
    (h3 : w ^ 3 = 1) : mkQ n w ∈ genSet F α h := by
  refine ⟨⟨w, hw, rfl⟩, ?_, ?_⟩
  · unfold zBar
    rw [zOf_emb, ← map_mul, ← map_mul, hc]
  · rw [← map_pow, h3, map_one]

theorem item_mem {α : Finset (Fin n)} (h : α.card = 4) {σ : Equiv.Perm (Fin n)}
    {v : Fin n → ZMod 2} (hok : okItem F α σ v) :
    mkQ n (ofVec v * ofPerm σ * (ofVec v)⁻¹) ∈ genSet F α h ∧ mkQ n (ofPerm σ) ∈ genSet F α h := by
  obtain ⟨hσF, hσ3, hsg, hα, hv⟩ := hok
  have hσ : σ ∈ stabFamily F := hσF
  have hP := ofPerm_mem hσ hsg
  have hV := ofVec_mem (A := stabFamily F) hv
  have hcP : ofPerm σ * ofVec (indV α) = ofVec (indV α) * ofPerm σ := ofPerm_comm_indV hα
  have hcV : ofVec v * ofVec (indV α) = ofVec (indV α) * ofVec v := ofVec_comm _ _
  have h3P : ofPerm σ ^ 3 = 1 := by rw [ofPerm_pow, hσ3, ofPerm_one]
  refine ⟨mkQ_mem_genSet h ?_ ?_ ?_, mkQ_mem_genSet h hP hcP h3P⟩
  · exact (aeSubOver (stabFamily F)).mul_mem ((aeSubOver (stabFamily F)).mul_mem hV hP)
      ((aeSubOver (stabFamily F)).inv_mem hV)
  · have hc1 : Commute (ofVec v) (ofVec (indV α)) := hcV
    have hc2 : Commute (ofPerm σ) (ofVec (indV α)) := hcP
    exact (((hc1.mul_left hc2).mul_left hc1.inv_left)).eq
  · rw [conj_pow, h3P, mul_one, mul_inv_cancel]

theorem cert_mem {α β : Finset (Fin n)} (h : α.card = 4) (h' : β.card = 4)
    {items : List (Equiv.Perm (Fin n) × (Fin n → ZMod 2))} (hc : certOk F α β items) :
    zBar β h' ∈ Subgroup.closure (genSet F α h) := by
  obtain ⟨hok, hprod⟩ := hc
  have hmem : ∀ x ∈ (items.map fun p => mkQ n (basic p.1 p.2)),
      x ∈ Subgroup.closure (genSet F α h) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := item_mem (F := F) h (hok p hp)
    unfold basic
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure h1)
      (by rw [map_inv]; exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure h2))
  have hl := Subgroup.list_prod_mem _ hmem
  have hl2 : (items.map fun p => mkQ n (basic p.1 p.2)).prod =
      mkQ n ((items.map fun p => basic p.1 p.2).prod) := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hl2] at hl
  have hz : zBar β h' = mkQ n (ofVec (indV β)) := by unfold zBar; rw [zOf_emb]
  rw [hz]
  have hprodv : (items.map fun p => basic p.1 p.2).prod =
      ofVec (items.map fun p => basicVec p.1 p.2).sum := by
    rw [← prod_ofVec, List.map_map]
    congr 1
    exact List.map_congr_left fun p _ => basic_eq p.1 p.2
  rw [hprodv] at hl
  rcases hprod with hp | hp
  · rw [hp] at hl; exact hl
  · rw [hp] at hl
    have h1 : ofVec (fun i => indV β i + 1) = ofVec (indV β) * allOnes n := rfl
    rw [h1, map_mul] at hl
    have h2 : mkQ n (allOnes n) = 1 := (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
    rw [h2, mul_one] at hl
    exact hl

abbrev CertData (n : ℕ) :=
  List (Fin n) × List (Fin n) × List (List (Fin n × Fin n × Fin n) × List (Fin n))

@[expose] def cycPerm (cs : List (Fin n × Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  (cs.map fun c => Equiv.swap c.1 c.2.1 * Equiv.swap c.2.1 c.2.2).prod

@[expose] def CertData.check (F : List (Finset (Fin n))) (c : CertData n) : Bool :=
  (c.2.2.all fun p => decide (okItem F c.1.toFinset (cycPerm p.1) (vecOf p.2))) &&
    (decide ((c.2.2.map fun p => basicVec (cycPerm p.1) (vecOf p.2)).sum = indV c.2.1.toFinset) ||
      decide ((c.2.2.map fun p => basicVec (cycPerm p.1) (vecOf p.2)).sum =
        fun i => indV c.2.1.toFinset i + 1))

@[expose] def CertData.ok (F : List (Finset (Fin n))) (c : CertData n) : Prop :=
  certOk F c.1.toFinset c.2.1.toFinset (c.2.2.map fun p => (cycPerm p.1, vecOf p.2))

theorem CertData.ok_of_check {F : List (Finset (Fin n))} {c : CertData n}
    (h : CertData.check F c = true) : CertData.ok F c := by
  unfold CertData.check at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact h1 q hq
  · simpa [List.map_map, Function.comp_def] using h2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

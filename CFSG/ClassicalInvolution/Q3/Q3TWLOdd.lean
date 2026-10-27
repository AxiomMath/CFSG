module

public import CFSG.ClassicalInvolution.Q3.Q3TWLMap
public import CFSG.ClassicalInvolution.Q3.Q3TWInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

section Shift

variable {m n : ℕ} (hmn : m + 2 = n)

@[expose] def shiftIdx (i : Fin m) : Fin n := ⟨i.val + 2, by have := i.isLt; omega⟩

theorem shiftIdx_injective : Function.Injective (shiftIdx hmn) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simpa [shiftIdx] using this)

@[expose] def oddCoord : (Fin m ⊕ Fin m ⊕ Unit) → (Fin n ⊕ Fin n ⊕ Unit) :=
  Sum.map (shiftIdx hmn) (Sum.map (shiftIdx hmn) id)

theorem oddCoord_injective : Function.Injective (oddCoord hmn) :=
  Sum.map_injective.2 ⟨shiftIdx_injective hmn, Sum.map_injective.2
    ⟨shiftIdx_injective hmn, Function.injective_id⟩⟩

variable (K : Type*) [Field K]

@[expose] noncomputable def oddShift :
    (Fin m ⊕ Fin m ⊕ Unit → K) →ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K) :=
  Function.ExtendByZero.linearMap K (oddCoord hmn)

theorem oddShift_coord (v : Fin m ⊕ Fin m ⊕ Unit → K) (a : Fin m ⊕ Fin m ⊕ Unit) :
    oddShift hmn K v (oddCoord hmn a) = v a := by
  simp only [oddShift, Function.ExtendByZero.linearMap, LinearMap.coe_mk]
  exact (oddCoord_injective hmn).extend_apply v 0 a

theorem oddShift_off (v : Fin m ⊕ Fin m ⊕ Unit → K) (b : Fin n ⊕ Fin n ⊕ Unit)
    (hb : b ∉ Set.range (oddCoord hmn)) : oddShift hmn K v b = 0 := by
  simp only [oddShift, Function.ExtendByZero.linearMap, LinearMap.coe_mk]
  exact Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hb ⟨a, ha⟩)

end Shift

section Iso

variable {m n : ℕ} (hmn : m + 2 = n) (K : Type*) [Field K]

theorem oddShift_single (a : Fin m ⊕ Fin m ⊕ Unit) :
    oddShift hmn K (Pi.single a 1) = Pi.single (oddCoord hmn a) 1 := by
  funext b
  by_cases hb : b ∈ Set.range (oddCoord hmn)
  · obtain ⟨a', rfl⟩ := hb
    rw [oddShift_coord, Pi.single_apply, Pi.single_apply]
    simp only [(oddCoord_injective hmn).eq_iff]
  · rw [oddShift_off hmn K _ _ hb, Pi.single_apply]
    symm
    rw [ite_eq_right_iff]
    rintro rfl
    exact absurd ⟨a, rfl⟩ hb

theorem quadOdd_oddShift (v : Fin m ⊕ Fin m ⊕ Unit → K) :
    quadOdd n K (oddShift hmn K v) = quadOdd m K v := by
  rw [quadOdd_apply, quadOdd_apply]
  have h1 : oddShift hmn K v (.inr (.inr ())) = v (.inr (.inr ())) :=
    oddShift_coord hmn K v (.inr (.inr ()))
  rw [h1]
  congr 1
  refine (Fintype.sum_of_injective (shiftIdx hmn) (shiftIdx_injective hmn) _ _ ?_ ?_).symm
  · intro j hj
    have : oddShift hmn K v (.inl j) = 0 := oddShift_off hmn K v _ (fun ⟨a, ha⟩ => by
      rcases a with a | a | a
      · exact hj ⟨a, by simpa [oddCoord] using ha⟩
      · simp [oddCoord] at ha
      · simp [oddCoord] at ha)
    rw [this, zero_mul]
  · intro i
    exact (by rw [show (Sum.inl (shiftIdx hmn i) : Fin n ⊕ Fin n ⊕ Unit) = oddCoord hmn (.inl i)
        from rfl, show (Sum.inr (Sum.inl (shiftIdx hmn i)) : Fin n ⊕ Fin n ⊕ Unit) =
        oddCoord hmn (.inr (.inl i)) from rfl, oddShift_coord, oddShift_coord])

@[expose] noncomputable def oddIso : (quadOdd m K).Isometry (quadOdd n K) where
  toLinearMap := oddShift hmn K
  map_app' v := quadOdd_oddShift hmn K v

theorem oddIso_vec (i : Fin m) (s : Bool) :
    oddIso hmn K (oddVec m K i s) = oddVec n K (shiftIdx hmn i) s := by
  cases s
  · exact oddShift_single hmn K (.inr (.inl i))
  · exact oddShift_single hmn K (.inl i)

theorem oddIso_z : oddIso hmn K (oddZ m K) = oddZ n K :=
  oddShift_single hmn K (.inr (.inr ()))

theorem oddIso_injective : Function.Injective (oddIso hmn K) := by
  intro v w h
  funext a
  have := congrFun h (oddCoord hmn a)
  exact (oddShift_coord hmn K v a).symm.trans (this.trans (oddShift_coord hmn K w a))

end Iso

section Nodes

variable {m n : ℕ} (hmn : m + 2 = n) (K : Type) [Field K]

theorem shiftIdx_succ {k : Fin m} (h : k.val + 1 < m) (h' : (shiftIdx hmn k).val + 1 < n) :
    shiftIdx hmn ⟨k.val + 1, h⟩ = ⟨(shiftIdx hmn k).val + 1, h'⟩ :=
  Fin.ext (by show k.val + 1 + 2 = k.val + 2 + 1; omega)

theorem oddIso_comp_rootB (k : Fin m) :
    (oddIso hmn K).spinGroupMap.comp (rootB K k) = rootB K (shiftIdx hmn k) := by
  by_cases h : k.val + 1 < m
  · have h' : (shiftIdx hmn k).val + 1 < n := by simp only [shiftIdx]; omega
    have hkj : k ≠ ⟨k.val + 1, h⟩ := Fin.ne_of_val_ne (by simp)
    have hkj' : shiftIdx hmn k ≠ ⟨(shiftIdx hmn k).val + 1, h'⟩ := Fin.ne_of_val_ne (by simp)
    rw [rootB_of_lt K h rfl hkj, rootB_of_lt K h' rfl hkj']
    exact spinGroupMap_comp_longRoot (oddIso hmn K) (oddFrame m K).toHypFrame
      (oddFrame n K).toHypFrame hkj hkj' true false (oddIso_vec hmn K k true)
      (by rw [← shiftIdx_succ hmn h h']; exact oddIso_vec hmn K ⟨k.val + 1, h⟩ false)
  · have h' : ¬ (shiftIdx hmn k).val + 1 < n := by simp only [shiftIdx]; omega
    rw [rootB_of_not_lt K h, rootB_of_not_lt K h']
    exact spinGroupMap_comp_shortRoot (oddIso hmn K) (oddFrame m K) (oddFrame n K) k
      (shiftIdx hmn k) true (oddIso_z hmn K) (oddIso_vec hmn K k true)

theorem oddIso_comp_negRootB (k : Fin m) :
    (oddIso hmn K).spinGroupMap.comp (negRootB K k) = negRootB K (shiftIdx hmn k) := by
  by_cases h : k.val + 1 < m
  · have h' : (shiftIdx hmn k).val + 1 < n := by simp only [shiftIdx]; omega
    have hkj : (⟨k.val + 1, h⟩ : Fin m) ≠ k := Fin.ne_of_val_ne (by simp)
    have hkj' : (⟨(shiftIdx hmn k).val + 1, h'⟩ : Fin n) ≠ shiftIdx hmn k :=
      Fin.ne_of_val_ne (by simp)
    rw [negRootB_of_lt K h rfl hkj, negRootB_of_lt K h' rfl hkj']
    exact spinGroupMap_comp_longRoot (oddIso hmn K) (oddFrame m K).toHypFrame
      (oddFrame n K).toHypFrame hkj hkj' true false
      (by rw [← shiftIdx_succ hmn h h']; exact oddIso_vec hmn K ⟨k.val + 1, h⟩ true)
      (oddIso_vec hmn K k false)
  · have h' : ¬ (shiftIdx hmn k).val + 1 < n := by simp only [shiftIdx]; omega
    refine MonoidHom.ext fun c => ?_
    rw [← ofAdd_toAdd c, MonoidHom.comp_apply, negRootB_of_not_lt K h, negRootB_of_not_lt K h']
    exact DFunLike.congr_fun (spinGroupMap_comp_shortRoot (oddIso hmn K) (oddFrame m K)
      (oddFrame n K) k (shiftIdx hmn k) false (oddIso_z hmn K) (oddIso_vec hmn K k false))
      (Multiplicative.ofAdd (-c.toAdd))

theorem oddIso_map_rankOne (k : Fin m) :
    (rankOne (oddDatum m K).rootGroup k).map (oddIso hmn K).spinGroupMap =
      rankOne (oddDatum n K).rootGroup (shiftIdx hmn k) := by
  change ((oddRootGroup m K (Pi.single k 1)) ⊔ (oddRootGroup m K (-Pi.single k 1))).map _ =
    oddRootGroup n K (Pi.single (shiftIdx hmn k) 1) ⊔
      oddRootGroup n K (-Pi.single (shiftIdx hmn k) 1)
  rw [Subgroup.map_sup, oddRootGroup_single, oddRootGroup_neg_single, oddRootGroup_single,
    oddRootGroup_neg_single, map_range_eq_of_comp_eq _ _ _ (oddIso_comp_rootB hmn K k),
    map_range_eq_of_comp_eq _ _ _ (oddIso_comp_negRootB hmn K k)]

end Nodes

section Main

variable {m n : ℕ} (hmn : m + 2 = n)

theorem leviEmbedOdd {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd m p f) (hF : Nat.card K = p ^ f) :
    ∃ Θ : spinGroup (quadOdd m K) →* spinGroup (quadOdd n K), Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin m, (rankOne (oddDatum m K).rootGroup k).map Θ =
        rankOne (oddDatum n K).rootGroup (shiftIdx hmn k)) ∧
      Θ.range = ⨆ k : Fin m, rankOne (oddDatum n K).rootGroup (shiftIdx hmn k) := by
  refine ⟨(oddIso hmn K).spinGroupMap, ker_spinGroupMap_le_center _ (oddIso_injective hmn K),
    oddIso_map_rankOne hmn K, ?_⟩
  refine range_eq_iSup_of_map_eq _ (fun k => rankOne (oddDatum m K).rootGroup k) _ ?_
    (oddIso_map_rankOne hmn K)
  have hgen := (curtisTitsConclusion_spinOdd.{0} hadm hF).1.1
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun J => ?_
  exact iSup₂_le fun j _ => le_iSup (fun k => rankOne (oddDatum m K).rootGroup k) j

theorem leviEmbed3Odd_proved : LeviEmbed3Odd := by
  intro n hn
  have hadm : StatedLieAdmissible .POmegaOdd (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  exact leviEmbedOdd (m := n - 2) (n := n) (by omega) hadm (GaloisField.card 3 1 one_ne_zero)

end Main

end CFSG.ClassicalInvolution.Q3.Q3TW

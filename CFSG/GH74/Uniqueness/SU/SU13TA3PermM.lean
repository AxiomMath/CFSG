module

public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE
public import CFSG.GH74.Uniqueness.SU.SU13TA3PermS
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def Mb : Subgroup (alternatingGroup (Fin 10)) :=
  centralizer ({ea * eb} : Set (alternatingGroup (Fin 10)))

theorem mem_Mb_iff {y : alternatingGroup (Fin 10)} :
    y ∈ Mb ↔ Commute (y : Perm (Fin 10)) (pa * pb) := by
  rw [Mb, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (congrArg Subtype.val h : (y : Perm (Fin 10)) * (pa * pb) = pa * pb * y)
  · intro h
    exact Subtype.ext h.eq

theorem apply_mem_of_mem_Mb {y : alternatingGroup (Fin 10)} (hy : y ∈ Mb) {v : Fin 10}
    (hv : v ∈ ({6, 7, 8, 9} : Finset (Fin 10))) : (y : Perm (Fin 10)) v ∈ ({6, 7, 8, 9} : Finset (Fin 10)) := by
  have hfix : ∀ w : Fin 10, w ∈ ({6, 7, 8, 9} : Finset (Fin 10)) → (pa * pb) w = w := by decide
  have h := apply_pow_of_commute (mem_Mb_iff.mp hy) 1 v
  simp only [pow_one] at h
  have h2 : (pa * pb) ((y : Perm (Fin 10)) v) = (y : Perm (Fin 10)) v := by
    rw [← h, hfix v hv]
  have key : ∀ w : Fin 10, (pa * pb) w = w → w ∈ ({6, 7, 8, 9} : Finset (Fin 10)) := by decide
  exact key _ h2

@[expose] def Obar : Subgroup (alternatingGroup (Fin 10)) := Ebar ⊓ AS

theorem toP_k_zero : ∀ k : Fin 3, (pc ^ (k : ℕ)) 6 = 6 → k = 0 := by decide

theorem mem_Obar_iff {x : alternatingGroup (Fin 10)} :
    x ∈ Obar ↔ ∃ i j : Fin 3, x = toE i j 0 := by
  constructor
  · rintro ⟨hxE, hxA⟩
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hxE
    have h6 := (mem_AS_iff.mp hxA).1
    have hk : k = 0 := by
      refine toP_k_zero k ?_
      have := toP_apply_c i j k 6 (by decide)
      rw [← this]
      exact h6
    exact ⟨i, j, by rw [hk]⟩
  · rintro ⟨i, j, rfl⟩
    refine ⟨mem_Ebar_iff_toE.mpr ⟨i, j, 0, rfl⟩, mem_AS_iff.mpr ⟨?_, ?_, ?_⟩⟩ <;> decide +revert

theorem card_Obar : Nat.card Obar = 9 := by
  let f : Fin 3 × Fin 3 → Obar := fun p => ⟨toE p.1 p.2 0, mem_Obar_iff.mpr ⟨_, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      obtain ⟨h1, h2, -⟩ := toP_injective
        (congrArg (fun x : Obar => ((x : alternatingGroup (Fin 10)) : Perm (Fin 10))) h)
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨i, j, rfl⟩ := mem_Obar_iff.mp hx
      exact ⟨(i, j), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem toE_zero (i j : Fin 3) : toE i j 0 = ea ^ (i : ℕ) * eb ^ (j : ℕ) :=
  Subtype.ext (by
    show pa ^ (i : ℕ) * pb ^ (j : ℕ) * pc ^ ((0 : Fin 3) : ℕ) = _
    simp [Subgroup.coe_mul, coe_ea, coe_eb])

theorem ea_mem_Obar : ea ∈ Obar :=
  ⟨ea_mem_Ebar, mem_AS_iff.mpr ⟨by decide, by decide, by decide⟩⟩

theorem eb_mem_Obar : eb ∈ Obar :=
  ⟨eb_mem_Ebar, mem_AS_iff.mpr ⟨by decide, by decide, by decide⟩⟩

theorem Obar_le_Mb : Obar ≤ Mb := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := mem_Obar_iff.mp hx
  rw [mem_Mb_iff]
  exact ((show Commute (toP i j 0) pa from toP_mul_pa i j 0).mul_right
    (show Commute (toP i j 0) pb from toP_mul_pb i j 0))

theorem conj_pa_mem {y : Perm (Fin 10)} (hy : Commute y (pa * pb)) :
    y * pa * y⁻¹ = pa ∨ y * pa * y⁻¹ = pb := by
  have hy0 : y 0 ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) := by
    have h := apply_pow_of_commute hy 1 0
    simp only [pow_one] at h
    have hne : (pa * pb) (y 0) ≠ y 0 := fun h' => by
      have : y ((pa * pb) 0) = y 0 := h.trans h'
      have := y.injective this
      exact absurd this (by decide)
    revert hne
    generalize y 0 = a
    revert a
    decide
  have h2 : y 2 = (pa * pb) (y 0) := by
    have h := apply_pow_of_commute hy 1 0
    simp only [pow_one] at h
    rw [← h]
    congr 1
  have h1 : y 1 = (pa * pb) ((pa * pb) (y 0)) := by
    have h := apply_pow_of_commute hy 1 2
    simp only [pow_one] at h
    rw [← h2, ← h]
    congr 1
  have hconj : y * pa * y⁻¹ = swap (y 0) (y 1) * swap (y 0) (y 2) := by
    rw [Equiv.swap_apply_apply y 0 1, Equiv.swap_apply_apply y 0 2]
    show y * (swap 0 1 * swap 0 2) * y⁻¹ = y * swap 0 1 * y⁻¹ * (y * swap 0 2 * y⁻¹)
    group
  rw [hconj, h1, h2]
  revert hy0
  generalize y 0 = a
  revert a
  decide

theorem conj_pb_mem {y : Perm (Fin 10)} (hy : Commute y (pa * pb)) :
    y * pb * y⁻¹ = pa ∨ y * pb * y⁻¹ = pb := by
  have hy3 : y 3 ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) := by
    have h := apply_pow_of_commute hy 1 3
    simp only [pow_one] at h
    have hne : (pa * pb) (y 3) ≠ y 3 := fun h' => by
      have : y ((pa * pb) 3) = y 3 := h.trans h'
      have := y.injective this
      exact absurd this (by decide)
    revert hne
    generalize y 3 = a
    revert a
    decide
  have h5 : y 5 = (pa * pb) (y 3) := by
    have h := apply_pow_of_commute hy 1 3
    simp only [pow_one] at h
    rw [← h]
    congr 1
  have h4 : y 4 = (pa * pb) ((pa * pb) (y 3)) := by
    have h := apply_pow_of_commute hy 1 5
    simp only [pow_one] at h
    rw [← h5, ← h]
    congr 1
  have hconj : y * pb * y⁻¹ = swap (y 3) (y 4) * swap (y 3) (y 5) := by
    rw [Equiv.swap_apply_apply y 3 4, Equiv.swap_apply_apply y 3 5]
    show y * (swap 3 4 * swap 3 5) * y⁻¹ = y * swap 3 4 * y⁻¹ * (y * swap 3 5 * y⁻¹)
    group
  rw [hconj, h4, h5]
  revert hy3
  generalize y 3 = a
  revert a
  decide

theorem conj_mem_Obar {y x : alternatingGroup (Fin 10)} (hy : y ∈ Mb) (hx : x ∈ Obar) :
    y * x * y⁻¹ ∈ Obar := by
  obtain ⟨i, j, rfl⟩ := mem_Obar_iff.mp hx
  have hcomm := mem_Mb_iff.mp hy
  have hya : y * ea * y⁻¹ ∈ Obar := by
    rcases conj_pa_mem hcomm with h | h
    · rw [show y * ea * y⁻¹ = ea from Subtype.ext h]
      exact ea_mem_Obar
    · rw [show y * ea * y⁻¹ = eb from Subtype.ext h]
      exact eb_mem_Obar
  have hyb : y * eb * y⁻¹ ∈ Obar := by
    rcases conj_pb_mem hcomm with h | h
    · rw [show y * eb * y⁻¹ = ea from Subtype.ext h]
      exact ea_mem_Obar
    · rw [show y * eb * y⁻¹ = eb from Subtype.ext h]
      exact eb_mem_Obar
  rw [toE_zero]
  have e : y * (ea ^ (i : ℕ) * eb ^ (j : ℕ)) * y⁻¹ =
      (y * ea * y⁻¹) ^ (i : ℕ) * (y * eb * y⁻¹) ^ (j : ℕ) := by
    rw [conj_pow, conj_pow]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hya _) (Subgroup.pow_mem _ hyb _)

theorem pt_mul_toP : ∀ i j k : Fin 3, pt * toP i j k * pt⁻¹ = toP j i (-k) := by decide

theorem toP_diag_zero : ∀ j : Fin 3, toP j j 0 = (pa * pb) ^ (j : ℕ) := by decide

theorem mem_zpowers_of_commute_et {x : alternatingGroup (Fin 10)} (hx : x ∈ Obar)
    (hc : et * x = x * et) : x ∈ zpowers (ea * eb) := by
  obtain ⟨i, j, rfl⟩ := mem_Obar_iff.mp hx
  have h1 : pt * toP i j 0 * pt⁻¹ = toP i j 0 := by
    have : pt * toP i j 0 = toP i j 0 * pt := congrArg Subtype.val hc
    rw [this]
    group
  rw [pt_mul_toP] at h1
  obtain ⟨hij, hji, -⟩ := toP_injective h1
  subst hij
  refine ⟨(j : ℤ), Subtype.ext ?_⟩
  show ((ea * eb : alternatingGroup (Fin 10)) ^ (j : ℤ) : alternatingGroup (Fin 10)).val = toP j j 0
  rw [zpow_natCast, Subgroup.coe_pow]
  exact (toP_diag_zero j).symm

theorem ec_mem_Mb : ec ∈ Mb := by
  rw [mem_Mb_iff]
  show pc * (pa * pb) = pa * pb * pc
  decide

theorem et_mem_Mb : et ∈ Mb := by
  rw [mem_Mb_iff]
  show pt * (pa * pb) = pa * pb * pt
  decide

@[expose] def pv1 : Perm (Fin 10) := swap 6 7 * swap 8 9

@[expose] def pv2 : Perm (Fin 10) := swap 6 8 * swap 7 9

theorem sign_pv1 : Perm.sign pv1 = 1 := by decide

theorem sign_pv2 : Perm.sign pv2 = 1 := by decide

@[expose] def ev1 : alternatingGroup (Fin 10) := ⟨pv1, Perm.mem_alternatingGroup.mpr sign_pv1⟩

@[expose] def ev2 : alternatingGroup (Fin 10) := ⟨pv2, Perm.mem_alternatingGroup.mpr sign_pv2⟩

theorem ev1_mul_self : ev1 * ev1 = 1 := Subtype.ext (by decide)

theorem ev2_mul_self : ev2 * ev2 = 1 := Subtype.ext (by decide)

theorem ev1_comm_ev2 : ev1 * ev2 = ev2 * ev1 := Subtype.ext (by decide)

@[expose] def Vb : Subgroup (alternatingGroup (Fin 10)) :=
  kleinFourOf ev1_mul_self ev2_mul_self ev1_comm_ev2

theorem card_Vb : Nat.card Vb = 4 :=
  card_kleinFourOf _ _ _ (fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
    revert this
    decide) (fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
    revert this
    decide) (fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
    revert this
    decide)

theorem mem_Vb_iff {x : alternatingGroup (Fin 10)} :
    x ∈ Vb ↔ x = 1 ∨ x = ev1 ∨ x = ev2 ∨ x = ev1 * ev2 := mem_kleinFourOf _ _ _

theorem cycleType_Vb {x : alternatingGroup (Fin 10)} (hx : x ∈ Vb) (h1 : x ≠ 1) :
    (x : Perm (Fin 10)).cycleType = {2, 2} := by
  rcases mem_Vb_iff.mp hx with h | rfl | rfl | rfl
  · exact absurd h h1
  · exact cycleType_swap_mul_swap_of_nodup (by decide)
  · exact cycleType_swap_mul_swap_of_nodup (by decide)
  · have : ((ev1 * ev2 : alternatingGroup (Fin 10)) : Perm (Fin 10)) = swap 6 9 * swap 7 8 := by
      decide
    rw [this]
    exact cycleType_swap_mul_swap_of_nodup (by decide)

theorem Vb_le_Mb : Vb ≤ Mb := by
  intro x hx
  rw [mem_Mb_iff]
  rcases mem_Vb_iff.mp hx with rfl | rfl | rfl | rfl
  · exact Commute.one_left _
  · show pv1 * (pa * pb) = pa * pb * pv1
    decide
  · show pv2 * (pa * pb) = pa * pb * pv2
    decide
  · show pv1 * pv2 * (pa * pb) = pa * pb * (pv1 * pv2)
    decide

theorem conj_swap_swap_mem {y : alternatingGroup (Fin 10)} (hy : y ∈ Mb) {p q r s : Fin 10}
    (hp : p ∈ ({6, 7, 8, 9} : Finset (Fin 10))) (hq : q ∈ ({6, 7, 8, 9} : Finset (Fin 10)))
    (hr : r ∈ ({6, 7, 8, 9} : Finset (Fin 10))) (hs : s ∈ ({6, 7, 8, 9} : Finset (Fin 10)))
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (y : Perm (Fin 10)) * (swap p q * swap r s) * (y : Perm (Fin 10))⁻¹ = pv1 ∨
      (y : Perm (Fin 10)) * (swap p q * swap r s) * (y : Perm (Fin 10))⁻¹ = pv2 ∨
      (y : Perm (Fin 10)) * (swap p q * swap r s) * (y : Perm (Fin 10))⁻¹ = pv1 * pv2 := by
  set Y : Perm (Fin 10) := (y : Perm (Fin 10)) with hY
  have e : Y * (swap p q * swap r s) * Y⁻¹ = swap (Y p) (Y q) * swap (Y r) (Y s) := by
    rw [Equiv.swap_apply_apply Y p q, Equiv.swap_apply_apply Y r s]
    group
  rw [e]
  have key : ∀ a b c d : Fin 10, a ∈ ({6, 7, 8, 9} : Finset (Fin 10)) →
      b ∈ ({6, 7, 8, 9} : Finset (Fin 10)) → c ∈ ({6, 7, 8, 9} : Finset (Fin 10)) →
      d ∈ ({6, 7, 8, 9} : Finset (Fin 10)) → a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      swap a b * swap c d = pv1 ∨ swap a b * swap c d = pv2 ∨
        swap a b * swap c d = pv1 * pv2 := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl had | exact absurd rfl hbc | exact absurd rfl hbd | exact absurd rfl hcd | decide
  exact key _ _ _ _ (apply_mem_of_mem_Mb hy hp) (apply_mem_of_mem_Mb hy hq)
    (apply_mem_of_mem_Mb hy hr) (apply_mem_of_mem_Mb hy hs) (fun h => hpq (Y.injective h))
    (fun h => hpr (Y.injective h)) (fun h => hps (Y.injective h)) (fun h => hqr (Y.injective h))
    (fun h => hqs (Y.injective h)) (fun h => hrs (Y.injective h))

theorem conj_ev1_mem_Vb {y : alternatingGroup (Fin 10)} (hy : y ∈ Mb) : y * ev1 * y⁻¹ ∈ Vb := by
  have h := conj_swap_swap_mem hy (p := 6) (q := 7) (r := 8) (s := 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [mem_Vb_iff]
  rcases h with h | h | h
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem conj_ev2_mem_Vb {y : alternatingGroup (Fin 10)} (hy : y ∈ Mb) : y * ev2 * y⁻¹ ∈ Vb := by
  have h := conj_swap_swap_mem hy (p := 6) (q := 8) (r := 7) (s := 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [mem_Vb_iff]
  rcases h with h | h | h
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem conj_mem_Vb {y x : alternatingGroup (Fin 10)} (hy : y ∈ Mb) (hx : x ∈ Vb) :
    y * x * y⁻¹ ∈ Vb := by
  rcases mem_Vb_iff.mp hx with rfl | rfl | rfl | rfl
  · simp
  · exact conj_ev1_mem_Vb hy
  · exact conj_ev2_mem_Vb hy
  · have e : y * (ev1 * ev2) * y⁻¹ = (y * ev1 * y⁻¹) * (y * ev2 * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_ev1_mem_Vb hy) (conj_ev2_mem_Vb hy)

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10

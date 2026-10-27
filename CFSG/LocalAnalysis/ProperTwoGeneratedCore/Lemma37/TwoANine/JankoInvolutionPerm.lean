module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolution

open Equiv Subgroup Janko

theorem cycleType_ybar : (ybar : Perm (Fin 9)).cycleType = {2, 2} := by
  rw [← multiset_replicate_two_two, cycleType_eq_replicate_iff_of_sq_eq_one (by decide)]
  decide

theorem ybar_conj_sbar₂ : ybar * sbar₂ * ybar⁻¹ = sbar₂⁻¹ :=
  Subtype.ext (show (ybar : Perm (Fin 9)) * sbar₂ * (ybar : Perm (Fin 9))⁻¹ =
    (sbar₂ : Perm (Fin 9))⁻¹ by decide)

theorem tbar_mul_ybar : tbar * ybar = ybar * tbar :=
  Subtype.ext (show (tbar : Perm (Fin 9)) * ybar = ybar * tbar by decide)

@[expose] def κbar : alternatingGroup (Fin 9) :=
  ⟨swap 0 8 * swap 8 3 * swap 3 6 * swap 6 7 * swap 7 1 * swap 1 5 * swap 5 2 * swap 2 4,
    Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem κbar_conj_ybar : κbar * ybar * κbar⁻¹ = aNineSylowGenB :=
  Subtype.ext (show (κbar : Perm (Fin 9)) * ybar * (κbar : Perm (Fin 9))⁻¹ = aNineSylowGenB by
    decide)

theorem κbar_conj_tbar : κbar * tbar * κbar⁻¹ = aNineSylowGenA * aNineSylowGenC :=
  Subtype.ext (show (κbar : Perm (Fin 9)) * tbar * (κbar : Perm (Fin 9))⁻¹ =
    (aNineSylowGenA : Perm (Fin 9)) * aNineSylowGenC by decide)

theorem mem_closure_tbar_ybar {g : alternatingGroup (Fin 9)}
    (hg : g ∈ closure ({tbar, ybar} : Set (alternatingGroup (Fin 9)))) :
    g = 1 ∨ g = tbar ∨ g = ybar ∨ g = tbar * ybar := by
  induction hg using closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  | inv x _ hx => rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem tbar_mem_closure : tbar ∈ closure ({tbar, ybar} : Set (alternatingGroup (Fin 9))) :=
  subset_closure (by simp)

theorem ybar_mem_closure : ybar ∈ closure ({tbar, ybar} : Set (alternatingGroup (Fin 9))) :=
  subset_closure (by simp)

theorem card_closure_tbar_ybar :
    Nat.card (closure ({tbar, ybar} : Set (alternatingGroup (Fin 9)))) = 4 := by
  have h : ((closure ({tbar, ybar} : Set (alternatingGroup (Fin 9))) : Set _)) =
      (({1, tbar, ybar, tbar * ybar} : Finset (alternatingGroup (Fin 9))) :
        Set (alternatingGroup (Fin 9))) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    refine ⟨mem_closure_tbar_ybar, ?_⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact tbar_mem_closure
    · exact ybar_mem_closure
    · exact mul_mem tbar_mem_closure ybar_mem_closure
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

theorem centralizer_conj_eq {X : Type*} [Group X] (g a : X) :
    centralizer ({g * a * g⁻¹} : Set X) =
      (centralizer ({a} : Set X)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [hx]
      _ = a * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group

theorem centralizer_inv_eq {X : Type*} [Group X] (s : X) :
    centralizer ({s⁻¹} : Set X) = centralizer ({s} : Set X) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem orderOf_conj_eq {X : Type*} [Group X] (g a : X) : orderOf (g * a * g⁻¹) = orderOf a := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a

theorem card_centralizer_conj_eq {X : Type*} [Group X] (g a : X) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set X)) = Nat.card (centralizer ({a} : Set X)) := by
  rw [centralizer_conj_eq, card_map_of_injective (MulAut.conj g).injective]

theorem card_centralizer_inf_conj_eq {X : Type*} [Group X] (g a b : X) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set X) ⊓ centralizer ({g * b * g⁻¹} : Set X) :
      Subgroup X) =
      Nat.card (centralizer ({a} : Set X) ⊓ centralizer ({b} : Set X) : Subgroup X) := by
  rw [centralizer_conj_eq, centralizer_conj_eq, ← map_inf_eq _ _ _ (MulAut.conj g).injective]
  exact card_map_of_injective (MulAut.conj g).injective

theorem exists_conj_eq_of_sq_eq_one {X : Type*} [Group X] {β γ : X} (hβ : β ^ 2 = 1)
    (hγ : γ ^ 2 = 1) (hodd : Odd (orderOf (γ * β))) :
    ∃ y ∈ zpowers (γ * β), y * β * y⁻¹ = γ := by
  obtain ⟨m, hm⟩ := hodd
  set p := γ * β with hp
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right (by rw [← sq, hβ])
  have hγi : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right (by rw [← sq, hγ])
  have hconj : β * p * β⁻¹ = p⁻¹ := by
    rw [hp, mul_inv_rev, hβi, hγi, mul_assoc, mul_assoc, ← sq, hβ, mul_one]
  have hq : β * (p ^ (m + 1))⁻¹ * β⁻¹ = p ^ (m + 1) := by
    rw [← inv_pow, ← conj_pow, show β * p⁻¹ * β⁻¹ = (β * p * β⁻¹)⁻¹ by group, hconj, inv_inv]
  have hp1 : p ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one p
  refine ⟨p ^ (m + 1), pow_mem (mem_zpowers p) _, ?_⟩
  calc p ^ (m + 1) * β * (p ^ (m + 1))⁻¹
      = p ^ (m + 1) * (β * (p ^ (m + 1))⁻¹ * β⁻¹) * β := by group
    _ = p ^ (2 * m + 1) * p * β := by rw [hq, ← pow_add, ← pow_succ]; ring_nf
    _ = γ := by rw [hp1, one_mul, hp, mul_assoc, ← sq, hβ, mul_one]

private theorem rbar_mem :
    ebar₂ * ebar₃⁻¹ ∈
      centralizer {sbar₃} ⊓ centralizer ({bbar₃} : Set (alternatingGroup (Fin 9))) :=
  ⟨mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide)),
    mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide))⟩

private theorem rbar_ne_one : ebar₂ * ebar₃⁻¹ ≠ 1 := fun h =>
  absurd (congrArg Subtype.val h) (by decide)

private theorem apply_eq_of_commute {c : Perm (Fin 9)} (hs : c * sbar₃ = sbar₃ * c)
    (hb : c * bbar₃ = bbar₃ * c) {j : Fin 9} (hj : c j = j) :
    c ((sbar₃ : Perm (Fin 9)) j) = (sbar₃ : Perm (Fin 9)) j ∧
      c ((bbar₃ : Perm (Fin 9)) j) = (bbar₃ : Perm (Fin 9)) j := by
  constructor
  · rw [← Perm.mul_apply, hs, Perm.mul_apply, hj]
  · rw [← Perm.mul_apply, hb, Perm.mul_apply, hj]

private theorem apply_eq_of_commute_of_lt {c : Perm (Fin 9)} (hs : c * sbar₃ = sbar₃ * c)
    (hb : c * bbar₃ = bbar₃ * c) : c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 2 := by
  have hfix : ∀ i : Fin 9, (bbar₃ : Perm (Fin 9)) i = i → i = 2 := by decide
  have h2 : c 2 = 2 := hfix _ (by
    rw [← Perm.mul_apply, ← hb, Perm.mul_apply, show (bbar₃ : Perm (Fin 9)) 2 = 2 by decide])
  have h0 : c 0 = 0 := by
    have := (apply_eq_of_commute hs hb h2).1
    rwa [show (sbar₃ : Perm (Fin 9)) 2 = 0 by decide] at this
  have h1 : c 1 = 1 := by
    have := (apply_eq_of_commute hs hb h0).1
    rwa [show (sbar₃ : Perm (Fin 9)) 0 = 1 by decide] at this
  exact ⟨h0, h1, h2⟩

private theorem eq_one_of_commute {c : Perm (Fin 9)} (hs : c * sbar₃ = sbar₃ * c)
    (hb : c * bbar₃ = bbar₃ * c) (h3 : c 3 = 3) : c = 1 := by
  obtain ⟨h0, h1, h2⟩ := apply_eq_of_commute_of_lt hs hb
  have step := fun {j : Fin 9} (hj : c j = j) => apply_eq_of_commute hs hb hj
  have h4 : c 4 = 4 := by
    have := (step h3).1; rwa [show (sbar₃ : Perm (Fin 9)) 3 = 4 by decide] at this
  have h5 : c 5 = 5 := by
    have := (step h4).1; rwa [show (sbar₃ : Perm (Fin 9)) 4 = 5 by decide] at this
  have h7 : c 7 = 7 := by
    have := (step h3).2; rwa [show (bbar₃ : Perm (Fin 9)) 3 = 7 by decide] at this
  have h6 : c 6 = 6 := by
    have := (step h4).2; rwa [show (bbar₃ : Perm (Fin 9)) 4 = 6 by decide] at this
  have h8 : c 8 = 8 := by
    have := (step h5).2; rwa [show (bbar₃ : Perm (Fin 9)) 5 = 8 by decide] at this
  ext i
  fin_cases i <;> simp_all

theorem card_centralizer_sbar₃_inf_bbar₃ :
    Nat.card (centralizer {sbar₃} ⊓ centralizer ({bbar₃} : Set (alternatingGroup (Fin 9))) :
      Subgroup _) = 3 := by
  set X := centralizer {sbar₃} ⊓ centralizer ({bbar₃} : Set (alternatingGroup (Fin 9)))
  have hcomm : ∀ c ∈ X, (c : Perm (Fin 9)) * sbar₃ = sbar₃ * c ∧
      (c : Perm (Fin 9)) * bbar₃ = bbar₃ * c := fun c hc =>
    ⟨congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc.1),
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc.2)⟩
  let f : X → {i : Fin 9 // 3 ≤ (i : ℕ)} := fun c => ⟨(c : Perm (Fin 9)) 3, by
    obtain ⟨hs, hb⟩ := hcomm c c.2
    obtain ⟨h0, h1, h2⟩ := apply_eq_of_commute_of_lt hs hb
    by_contra hlt
    have : ((c : alternatingGroup (Fin 9)) : Perm (Fin 9)) 3 = 0 ∨ (c : Perm (Fin 9)) 3 = 1 ∨
        (c : Perm (Fin 9)) 3 = 2 := by omega
    rcases this with h | h | h
    · exact absurd ((c : Perm (Fin 9)).injective (h.trans h0.symm)) (by decide)
    · exact absurd ((c : Perm (Fin 9)).injective (h.trans h1.symm)) (by decide)
    · exact absurd ((c : Perm (Fin 9)).injective (h.trans h2.symm)) (by decide)⟩
  have hf : Function.Injective f := by
    intro c c' h
    have h3 : ((c'⁻¹ * c : X) : Perm (Fin 9)) 3 = 3 := by
      have h' : (c : Perm (Fin 9)) 3 = (c' : Perm (Fin 9)) 3 := congrArg Subtype.val h
      simp only [coe_mul, coe_inv, Perm.mul_apply, h']
      simp
    obtain ⟨hs, hb⟩ := hcomm _ (c'⁻¹ * c).2
    have h1 := eq_one_of_commute hs hb h3
    have : c'⁻¹ * c = 1 := Subtype.ext (Subtype.ext h1)
    exact (inv_mul_eq_one.mp this).symm
  have hle : Nat.card X ≤ 6 := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := {i : Fin 9 // 3 ≤ (i : ℕ)}),
      show Fintype.card {i : Fin 9 // 3 ≤ (i : ℕ)} = 6 by decide] at this
  have hd : Nat.card X ∣ 81 := card_centralizer_sbar₃ ▸ card_dvd_of_le inf_le_left
  have h1 : Nat.card X ≠ 1 := fun h => rbar_ne_one (by
    have hsub : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨_, rbar_mem⟩ : X) 1))
  have hpos : 0 < Nat.card X := Nat.card_pos
  generalize Nat.card X = n at hd hle h1 hpos
  interval_cases n <;> omega

theorem bbar₃_sq : bbar₃ ^ 2 = 1 :=
  Subtype.ext (show (bbar₃ : Perm (Fin 9)) ^ 2 = 1 by decide)

theorem card_centralizer_sbar₃_inf {β : alternatingGroup (Fin 9)} (hβ : β ^ 2 = 1)
    (hβs : β * sbar₃ * β⁻¹ = sbar₃⁻¹) :
    Nat.card (centralizer {sbar₃} ⊓ centralizer ({β} : Set (alternatingGroup (Fin 9))) :
      Subgroup _) = 3 := by
  have hp : β * bbar₃ ∈ centralizer {sbar₃} := by
    rw [mem_centralizer_singleton_iff]
    have hb : bbar₃ * sbar₃ * bbar₃⁻¹ = sbar₃⁻¹ := bbar₃_conj_sbar₃
    calc β * bbar₃ * sbar₃ = β * (bbar₃ * sbar₃ * bbar₃⁻¹) * β⁻¹ * (β * bbar₃) := by group
      _ = (β * sbar₃ * β⁻¹)⁻¹ * (β * bbar₃) := by rw [hb]; group
      _ = sbar₃ * (β * bbar₃) := by rw [hβs, inv_inv]
  have hodd : Odd (orderOf (β * bbar₃)) := by
    have h := orderOf_dvd_natCard (⟨_, hp⟩ : centralizer {sbar₃})
    rw [card_centralizer_sbar₃, Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat (by decide) h
  obtain ⟨y, hy, hyb⟩ := exists_conj_eq_of_sq_eq_one bbar₃_sq hβ hodd
  have hys : y * sbar₃ * y⁻¹ = sbar₃ := by
    rw [mem_centralizer_singleton_iff.mp ((zpowers_le.mpr hp) hy), mul_inv_cancel_right]
  rw [← hyb, ← card_centralizer_sbar₃_inf_bbar₃]
  conv_lhs => rw [← hys]
  exact card_centralizer_inf_conj_eq y sbar₃ bbar₃

theorem orderOf_ρbar_mul_sbar₁ : orderOf (ρbar * sbar₁) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ (ρbar * sbar₁) ^ 3 ^ 1 = 1 := fun h => by
    have h' : ((ρbar : Perm (Fin 9)) * sbar₁) ^ 3 = 1 := by
      simpa using congrArg Subtype.val h
    exact absurd h' (by decide)
  have h9 : (ρbar * sbar₁) ^ 3 ^ (1 + 1) = 1 :=
    Subtype.ext (show ((ρbar : Perm (Fin 9)) * sbar₁) ^ 9 = 1 by decide +kernel)
  exact orderOf_eq_prime_pow h3 h9

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolution

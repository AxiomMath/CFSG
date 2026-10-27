module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBad

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

@[expose] def wX : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2] * List.formPerm [1, 3] * List.formPerm [5, 10] * List.formPerm [7, 11]

section DecideFacts

set_option maxRecDepth 100000

theorem J_sq : bfJ * bfJ = 1 := by decide
theorem U_sq : u1P * u1P = 1 := by decide
theorem X_sq : wX * wX = 1 := by decide
theorem J_ne_one : bfJ ≠ 1 := by decide

end DecideFacts

@[expose] def InW (x : Equiv.Perm (Fin 12)) : Prop :=
  x = 1 ∨ x = bfJ ∨ x = u1P ∨ x = wX ∨ x = bfJ * u1P ∨ x = bfJ * wX ∨ x = u1P * wX ∨
    x = bfJ * u1P * wX

@[expose] def Wperm : Subgroup (Equiv.Perm (Fin 12)) := closure {bfJ, u1P, wX}

section MulFacts

set_option maxRecDepth 100000

theorem InW_mul_gen {x : Equiv.Perm (Fin 12)} (hx : InW x) {g : Equiv.Perm (Fin 12)}
    (hg : g = bfJ ∨ g = u1P ∨ g = wX) : InW (x * g) := by
  unfold InW at hx ⊢
  rcases hg with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end MulFacts

theorem mem_Wperm_iff {x : Equiv.Perm (Fin 12)} : x ∈ Wperm ↔ InW x := by
  constructor
  · intro hx
    refine Subgroup.closure_induction_right (p := fun x _ => InW x) ?_ ?_ ?_ hx
    · exact Or.inl rfl
    · intro y _ g hg ih
      exact InW_mul_gen ih (by simpa using hg)
    · intro y _ g hg ih
      have hg' : g = bfJ ∨ g = u1P ∨ g = wX := by simpa using hg
      have hgi : g⁻¹ = g := by
        rcases hg' with rfl | rfl | rfl
        · exact inv_eq_of_mul_eq_one_right J_sq
        · exact inv_eq_of_mul_eq_one_right U_sq
        · exact inv_eq_of_mul_eq_one_right X_sq
      rw [hgi]
      exact InW_mul_gen ih hg'
  · intro hx
    have hJ : bfJ ∈ Wperm := subset_closure (by simp)
    have hU : u1P ∈ Wperm := subset_closure (by simp)
    have hX : wX ∈ Wperm := subset_closure (by simp)
    unfold InW at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hJ
    · exact hU
    · exact hX
    · exact mul_mem hJ hU
    · exact mul_mem hJ hX
    · exact mul_mem hU hX
    · exact mul_mem (mul_mem hJ hU) hX

section MulFacts2

set_option maxRecDepth 100000

theorem gen_normalizes {g : Equiv.Perm (Fin 12)} (hg : g = bfE ∨ g = bfN ∨ g = bfF ∨ g = sP)
    {w : Equiv.Perm (Fin 12)} (hw : InW w) : InW (g * w * g⁻¹) ∧ InW (g⁻¹ * w * g) := by
  unfold InW at hw ⊢
  rcases hg with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem conj_u1_words :
    (1 : Equiv.Perm (Fin 12)) * u1P * 1⁻¹ = u1P ∧ (sP * bfE) * u1P * (sP * bfE)⁻¹ = wX ∧
    bfE * u1P * bfE⁻¹ = bfJ * u1P ∧ sP * u1P * sP⁻¹ = bfJ * wX ∧
    (sP * sP) * u1P * (sP * sP)⁻¹ = u1P * wX ∧
    (bfE * sP) * u1P * (bfE * sP)⁻¹ = bfJ * u1P * wX := by
  decide

end MulFacts2

section Certified

set_option linter.unusedSectionVars false

theorem Cgen_le_normalizer_Wperm : Cgen ≤ normalizer Wperm := by
  rw [Cgen, closure_le]
  intro g hg
  have hg' : g = bfE ∨ g = bfN ∨ g = bfF ∨ g = sP := by simpa using hg
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro h
  rw [mem_Wperm_iff, mem_Wperm_iff]
  constructor
  · exact fun hh => (gen_normalizes hg' hh).1
  · intro hh
    have := (gen_normalizes hg' hh).2
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rwa [e] at this

theorem exists_conj_u1 {w : Equiv.Perm (Fin 12)} (hw : InW w) (h1 : w ≠ 1) (hJ : w ≠ bfJ) :
    ∃ h ∈ Cgen, h * u1P * h⁻¹ = w := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := conj_u1_words
  have hE : bfE ∈ Cgen := subset_closure (by simp)
  have hs : sP ∈ Cgen := subset_closure (by simp)
  unfold InW at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl hJ
  · exact ⟨1, one_mem _, c1⟩
  · exact ⟨sP * bfE, mul_mem hs hE, c2⟩
  · exact ⟨bfE, hE, c3⟩
  · exact ⟨sP, hs, c4⟩
  · exact ⟨sP * sP, mul_mem hs hs, c5⟩
  · exact ⟨bfE * sP, mul_mem hE hs, c6⟩

@[expose] def Wset7 : Finset (Equiv.Perm (Fin 12)) :=
  [bfJ, u1P, wX, bfJ * u1P, bfJ * wX, u1P * wX, bfJ * u1P * wX].toFinset

section Wset

set_option maxRecDepth 100000

theorem mem_Wset7_iff {x : Equiv.Perm (Fin 12)} : x ∈ Wset7 ↔ InW x ∧ x ≠ 1 := by
  have hne : bfJ ≠ 1 ∧ u1P ≠ 1 ∧ wX ≠ 1 ∧ bfJ * u1P ≠ 1 ∧ bfJ * wX ≠ 1 ∧ u1P * wX ≠ 1 ∧
      bfJ * u1P * wX ≠ 1 := by decide
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hne
  unfold Wset7 InW
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), n1⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), n2⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), n3⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), n4⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), n5⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), n6⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), n7⟩
  · rintro ⟨h | h | h | h | h | h | h | h, hx⟩
    · exact absurd h hx
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem card_Wset7 : Wset7.card = 7 := by
  have hnd : [bfJ, u1P, wX, bfJ * u1P, bfJ * wX, u1P * wX, bfJ * u1P * wX].Nodup := by decide
  unfold Wset7
  rw [List.toFinset_card_of_nodup hnd]
  rfl

end Wset

@[expose] def NW : Subgroup (Equiv.Perm (Fin 12)) := normalizer Wperm ⊓ NativeSporadic.M12

@[expose] def NWact (γ : ↥NW) (w : ↥Wset7) : ↥Wset7 :=
  ⟨(γ : Equiv.Perm (Fin 12)) * w * (γ : Equiv.Perm (Fin 12))⁻¹, by
    obtain ⟨hw, hw1⟩ := mem_Wset7_iff.1 w.2
    rw [mem_Wset7_iff]
    refine ⟨?_, ?_⟩
    · rw [← mem_Wperm_iff] at hw ⊢
      exact (mem_normalizer_iff.1 γ.2.1 _).1 hw
    · intro h
      apply hw1
      have := congrArg (fun z => (γ : Equiv.Perm (Fin 12))⁻¹ * z * (γ : Equiv.Perm (Fin 12))) h
      simpa [mul_assoc] using this⟩

noncomputable instance : MulAction ↥NW ↥Wset7 where
  smul := NWact
  one_smul w := Subtype.ext (by simp [HSMul.hSMul, SMul.smul, NWact])
  mul_smul a b w := Subtype.ext (by simp [HSMul.hSMul, SMul.smul, NWact, mul_assoc])

theorem NWact_coe (γ : ↥NW) (w : ↥Wset7) :
    ((γ • w : ↥Wset7) : Equiv.Perm (Fin 12)) =
      (γ : Equiv.Perm (Fin 12)) * w * (γ : Equiv.Perm (Fin 12))⁻¹ := rfl

theorem Cgen_le_NW : Cgen ≤ NW := by
  refine le_inf Cgen_le_normalizer_Wperm ?_
  intro x hx
  exact (Cgen_le hx).1

theorem NW_le_centralizer {m : Equiv.Perm (Fin 12)} (hm : m ∈ NW) : m * bfJ = bfJ * m := by
  by_contra hmove
  have hJW : bfJ ∈ Wset7 := mem_Wset7_iff.2 ⟨Or.inr (Or.inl rfl), J_ne_one⟩
  set Jx : ↥Wset7 := ⟨bfJ, hJW⟩ with hJx
  have hw0 : m * bfJ * m⁻¹ ∈ Wset7 := (NWact ⟨m, hm⟩ Jx).2
  have hw0ne : m * bfJ * m⁻¹ ≠ bfJ := by
    intro h
    apply hmove
    have := congrArg (· * m) h
    simpa [mul_assoc] using this
  obtain ⟨hw0W, -⟩ := mem_Wset7_iff.1 hw0
  obtain ⟨hw01, hw0J⟩ : m * bfJ * m⁻¹ ≠ 1 ∧ m * bfJ * m⁻¹ ≠ bfJ :=
    ⟨(mem_Wset7_iff.1 hw0).2, hw0ne⟩
  obtain ⟨h₀, hh₀, hh₀u⟩ := exists_conj_u1 hw0W hw01 hw0J
  have hγ' : (h₀⁻¹ * m) * bfJ * (h₀⁻¹ * m)⁻¹ = u1P := by
    have : h₀⁻¹ * (m * bfJ * m⁻¹) * h₀ = u1P := by
      rw [← hh₀u]; group
    calc (h₀⁻¹ * m) * bfJ * (h₀⁻¹ * m)⁻¹ = h₀⁻¹ * (m * bfJ * m⁻¹) * h₀ := by group
      _ = u1P := this
  have hγ'mem : h₀⁻¹ * m ∈ NW := mul_mem (inv_mem (Cgen_le_NW hh₀)) hm
  have htrans : ∀ x : ↥Wset7, ∃ γ : ↥NW, γ • Jx = x := by
    intro x
    by_cases hx : (x : Equiv.Perm (Fin 12)) = bfJ
    · exact ⟨1, Subtype.ext (by rw [hJx]; simpa using hx.symm)⟩
    · obtain ⟨hxW, hx1⟩ := mem_Wset7_iff.1 x.2
      obtain ⟨hx', hhx, hhxu⟩ := exists_conj_u1 hxW hx1 hx
      refine ⟨⟨hx' * (h₀⁻¹ * m), mul_mem (Cgen_le_NW hhx) hγ'mem⟩, Subtype.ext ?_⟩
      rw [NWact_coe]
      show hx' * (h₀⁻¹ * m) * bfJ * (hx' * (h₀⁻¹ * m))⁻¹ = x
      calc hx' * (h₀⁻¹ * m) * bfJ * (hx' * (h₀⁻¹ * m))⁻¹
          = hx' * ((h₀⁻¹ * m) * bfJ * (h₀⁻¹ * m)⁻¹) * hx'⁻¹ := by group
        _ = x := by rw [hγ', hhxu]
  have hpre : MulAction.IsPretransitive ↥NW ↥Wset7 := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨γx, hx⟩ := htrans x
    obtain ⟨γy, hy⟩ := htrans y
    refine ⟨γy * γx⁻¹, ?_⟩
    rw [mul_smul, ← hx, inv_smul_smul, hy]
  have hidx := MulAction.index_stabilizer_of_transitive ↥NW Jx
  have hcard7 : Nat.card ↥Wset7 = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_Wset7]
  have hdvd1 : (MulAction.stabilizer ↥NW Jx).index ∣ Nat.card ↥NW := Subgroup.index_dvd_card _
  have hdvd2 : Nat.card ↥NW ∣ Nat.card ↥(NativeSporadic.M12) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hM : Nat.card ↥(NativeSporadic.M12) = 95040 := card_G12
  rw [hidx, hcard7] at hdvd1
  have h7 : 7 ∣ 95040 := hM ▸ hdvd1.trans hdvd2
  omega

theorem bfJ_mem_M12 : bfJ ∈ NativeSporadic.M12 := (Jelt : G12).2

theorem wX_mem_M12 : wX ∈ NativeSporadic.M12 := by
  have h : wX = (sP * bfE) * u1P * (sP * bfE)⁻¹ := conj_u1_words.2.1.symm
  rw [h]
  exact mul_mem (mul_mem (mul_mem sP_mem_M12 bfE_mem_M12) u1P_mem_M12)
    (inv_mem (mul_mem sP_mem_M12 bfE_mem_M12))

theorem Wperm_le_M12 : Wperm ≤ NativeSporadic.M12 := by
  rw [Wperm, closure_le]
  intro x hx
  have : x = bfJ ∨ x = u1P ∨ x = wX := by simpa using hx
  rcases this with rfl | rfl | rfl
  · exact bfJ_mem_M12
  · exact u1P_mem_M12
  · exact wX_mem_M12

@[expose] def Wsub : Subgroup G12 := Wperm.subgroupOf NativeSporadic.M12

theorem mem_Wsub_iff {w : G12} : w ∈ Wsub ↔ InW (w : Equiv.Perm (Fin 12)) := by
  rw [Wsub, mem_subgroupOf, mem_Wperm_iff]

theorem Jelt_mem_Wsub : (Jelt : G12) ∈ Wsub := mem_Wsub_iff.2 (Or.inr (Or.inl rfl))

theorem card_Wsub : Nat.card Wsub = 8 := by
  have h1 : Nat.card Wsub = Nat.card Wperm :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Wperm_le_M12).toEquiv
  have h2 : (Wperm : Set (Equiv.Perm (Fin 12))) = ↑(insert (1 : Equiv.Perm (Fin 12)) Wset7) := by
    ext x
    rw [SetLike.mem_coe, mem_Wperm_iff, Finset.mem_coe, Finset.mem_insert, mem_Wset7_iff]
    unfold InW
    constructor
    · intro h
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl h
      · exact h
  rw [h1]
  have h3 : Nat.card Wperm = (Wperm : Set (Equiv.Perm (Fin 12))).ncard :=
    Nat.card_coe_set_eq (Wperm : Set (Equiv.Perm (Fin 12)))
  rw [h3, h2, Set.ncard_coe_finset]
  have h1n : (1 : Equiv.Perm (Fin 12)) ∉ Wset7 := fun h => (mem_Wset7_iff.1 h).2 rfl
  rw [Finset.card_insert_of_notMem h1n, card_Wset7]

section CommFacts

set_option maxRecDepth 100000

theorem InW_comm {x y : Equiv.Perm (Fin 12)} (hx : InW x) (hy : InW y) : x * y = y * x := by
  unfold InW at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end CommFacts

theorem Wsub_comm {w w' : G12} (hw : w ∈ Wsub) (hw' : w' ∈ Wsub) : w * w' = w' * w :=
  Subtype.ext (InW_comm (mem_Wsub_iff.1 hw) (mem_Wsub_iff.1 hw'))

theorem exists_conj_J {w : G12} (hw : w ∈ Wsub) (h1 : w ≠ 1) :
    ∃ m : G12, m * Jelt * m⁻¹ = w := by
  have hw' := mem_Wsub_iff.1 hw
  by_cases hJ : (w : Equiv.Perm (Fin 12)) = bfJ
  · refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact Subtype.ext hJ.symm
  · have h1' : (w : Equiv.Perm (Fin 12)) ≠ 1 := fun h => h1 (Subtype.ext h)
    obtain ⟨h, hh, hhu⟩ := exists_conj_u1 hw' h1' hJ
    have hhM : h ∈ NativeSporadic.M12 := (Cgen_le hh).1
    refine ⟨⟨h, hhM⟩ * nG12, ?_⟩
    have e1 : (⟨h, hhM⟩ * nG12) * Jelt * (⟨h, hhM⟩ * nG12)⁻¹ =
        ⟨h, hhM⟩ * (nG12 * Jelt * nG12⁻¹) * (⟨h, hhM⟩ : G12)⁻¹ := by group
    rw [e1, nG12_conj]
    exact Subtype.ext hhu

theorem Jelt_isSq : ∃ g : G12, g * g = Jelt := by
  refine ⟨Felt * Felt, Subtype.ext ?_⟩
  show bfF * bfF * (bfF * bfF) = bfF ^ 4
  simp [pow_succ, mul_assoc]

theorem Wsub_isSq {w : G12} (hw : w ∈ Wsub) : ∃ g : G12, g * g = w := by
  by_cases h1 : w = 1
  · exact ⟨1, by simp [h1]⟩
  · obtain ⟨m, hm⟩ := exists_conj_J hw h1
    obtain ⟨g, hg⟩ := Jelt_isSq
    refine ⟨m * g * m⁻¹, ?_⟩
    rw [← hm, ← hg]
    group

theorem normalizes_Wsub {σ : G12} (hσ : σ * Jelt = Jelt * σ) {w : G12} (hw : w ∈ Wsub) :
    σ * w * σ⁻¹ ∈ Wsub := by
  have hσc : (σ : Equiv.Perm (Fin 12)) ∈ Cgen := by
    rw [Cgen_eq, mem_centralizerIn]
    have hJ : ((Jelt : G12) : Equiv.Perm (Fin 12)) = bfJ := rfl
    have h := congrArg (fun z : G12 => (z : Equiv.Perm (Fin 12))) hσ
    simp only [Subgroup.coe_mul, hJ] at h
    exact ⟨σ.2, h⟩
  have hn := Cgen_le_normalizer_Wperm hσc
  rw [mem_Wsub_iff] at hw ⊢
  rw [← mem_Wperm_iff] at hw ⊢
  exact (mem_normalizer_iff.1 hn _).1 hw

theorem mem_NW_of_normalizes {σ : G12} (h1 : ∀ w ∈ Wsub, σ * w * σ⁻¹ ∈ Wsub)
    (h2 : ∀ w ∈ Wsub, σ⁻¹ * w * σ ∈ Wsub) : (σ : Equiv.Perm (Fin 12)) ∈ NW := by
  refine ⟨?_, σ.2⟩
  show (σ : Equiv.Perm (Fin 12)) ∈ normalizer Wperm
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhM : h ∈ NativeSporadic.M12 := Wperm_le_M12 hh
    have := h1 ⟨h, hhM⟩ (by rw [mem_Wsub_iff]; exact mem_Wperm_iff.1 hh)
    rw [mem_Wsub_iff] at this
    exact mem_Wperm_iff.2 this
  · intro hh
    have hM : (σ : Equiv.Perm (Fin 12)) * h * (σ : Equiv.Perm (Fin 12))⁻¹ ∈ NativeSporadic.M12 :=
      Wperm_le_M12 hh
    have hhM : h ∈ NativeSporadic.M12 := by
      have : (σ : Equiv.Perm (Fin 12))⁻¹ *
          ((σ : Equiv.Perm (Fin 12)) * h * (σ : Equiv.Perm (Fin 12))⁻¹) *
          (σ : Equiv.Perm (Fin 12)) = h := by group
      rw [← this]
      exact mul_mem (mul_mem (inv_mem σ.2) hM) σ.2
    have h3 := h2 ⟨(σ : Equiv.Perm (Fin 12)) * h * (σ : Equiv.Perm (Fin 12))⁻¹, hM⟩
      (by rw [mem_Wsub_iff]; exact mem_Wperm_iff.1 hh)
    rw [mem_Wsub_iff] at h3
    have e2 : (((σ⁻¹ * ⟨(σ : Equiv.Perm (Fin 12)) * h * (σ : Equiv.Perm (Fin 12))⁻¹, hM⟩ * σ :
        G12)) : Equiv.Perm (Fin 12)) = h := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e2] at h3
    exact mem_Wperm_iff.2 h3

end Certified

end CFSG.EvenSporadicStandard.M12Std.Yosh

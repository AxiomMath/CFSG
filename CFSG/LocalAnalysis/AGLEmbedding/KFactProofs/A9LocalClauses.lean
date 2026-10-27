module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

theorem fst_apply_of_mem_centralizer {g : Perm Pt}
    (hg : g ∈ Subgroup.centralizer (baseGroup : Set (Perm Pt))) (i z : ZMod 3) :
    (g (i, z)).1 = i := by
  rw [Subgroup.mem_centralizer_iff] at hg
  by_contra hne
  have h := congrArg (fun σ : Perm Pt => (σ (i, z)).2)
    (hg (shiftPerm (Pi.single (g (i, z)).1 1)) (shiftPerm_mem_baseGroup _))
  simp [Ne.symm hne] at h

theorem mem_baseGroup_of_mem_centralizer {g : Perm Pt}
    (hg : g ∈ Subgroup.centralizer (baseGroup : Set (Perm Pt))) : g ∈ baseGroup := by
  have h1 := fst_apply_of_mem_centralizer hg
  rw [Subgroup.mem_centralizer_iff] at hg
  have h2 : ∀ i z, (g (i, z + 1)).2 = (g (i, z)).2 + 1 := by
    intro i z
    have h := congrArg (fun σ : Perm Pt => (σ (i, z)).2)
      (hg (shiftPerm (Pi.single i 1)) (shiftPerm_mem_baseGroup _))
    simpa [h1] using h.symm
  have h3 : ∀ i z, (g (i, z)).2 = (g (i, 0)).2 + z := by
    intro i z
    rcases (by decide : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 1 + 1) z with rfl | rfl | rfl
    · simp
    · simpa using h2 i 0
    · have h4 := h2 i 1
      have h5 := h2 i 0
      simp only [zero_add] at h5
      rw [h4, h5]
      ring
  refine mem_baseGroup_iff.2 ⟨fun i => (g (i, 0)).2, ?_⟩
  ext ⟨i, z⟩
  · simp [h1]
  · rw [h3 i z]
    simp [add_comm]

namespace Clauses

theorem signAt_mem {M : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M) (k : ZMod 3) :
    signAt k ∈ M :=
  hEM ⟨signAt_mem_alternatingGroup k, signAt_mem_nrm k⟩

theorem blockShift_mem {M : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M) :
    blockShift ∈ M :=
  hEM ⟨blockShift_mem_alternatingGroup, blockShift_mem_nrm⟩

theorem baseGroup_le {M : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M) :
    baseGroup ≤ M :=
  fun _ hb => hEM ⟨baseGroup_le_alternatingGroup hb, baseGroup_le_nrm hb⟩

theorem sylowT_le {M : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M) :
    sylowT ≤ M :=
  fun _ hb => hEM ⟨sylowT_le_alternatingGroup hb, sylowT_le_nrm hb⟩

end Clauses

namespace Clauses

theorem shiftPerm_single_mem {M V : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M)
    (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) {f : ZMod 3 → ZMod 3} {j : ZMod 3}
    (hv : shiftPerm f ∈ V) (hj : f j ≠ 0) (c : ZMod 3) : shiftPerm (Pi.single j c) ∈ V := by
  have hs := hMV _ (signAt_mem hEM j) _ hv
  rw [signAt_conj_shiftPerm] at hs
  have h2 := V.mul_mem hv hs
  rw [← shiftPerm_add] at h2
  have hf : f + (fun i => if i = j then f i else - f i) = Pi.single j (f j + f j) := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hf] at h2
  have ha : f j + f j ≠ 0 := by
    revert hj
    generalize f j = a
    revert a
    decide
  rcases (by decide : ∀ a c : ZMod 3, a ≠ 0 → c = 0 ∨ c = a ∨ c = a + a) (f j + f j) c ha with
    rfl | rfl | rfl
  · simp [shiftPerm_zero, V.one_mem]
  · exact h2
  · rw [Pi.single_add, shiftPerm_add]
    exact V.mul_mem h2 h2

theorem shiftPerm_single_succ_mem {M V : Subgroup (Perm Pt)}
    (hEM : alternatingGroup Pt ⊓ nrm ≤ M) (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    {j c : ZMod 3} (h : shiftPerm (Pi.single j c) ∈ V) :
    shiftPerm (Pi.single (j + 1) c) ∈ V := by
  have e : (fun i => (Pi.single j c : ZMod 3 → ZMod 3) (i - 1)) = Pi.single (j + 1) c := by
    funext i
    simp [Pi.single_apply, sub_eq_iff_eq_add]
  have := hMV _ (blockShift_mem hEM) _ h
  rwa [blockShift_conj_shiftPerm, e] at this

theorem baseGroup_le_of_single_mem {V : Subgroup (Perm Pt)}
    (h : ∀ j c, shiftPerm (Pi.single j c) ∈ V) : baseGroup ≤ V := by
  intro g hg
  obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 hg
  have hf : f = Pi.single 0 (f 0) + Pi.single 1 (f 1) + Pi.single 2 (f 2) := by
    funext i
    rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
      simp +decide
  rw [hf, shiftPerm_add, shiftPerm_add]
  exact V.mul_mem (V.mul_mem (h _ _) (h _ _)) (h _ _)

end Clauses

theorem eq_bot_or_eq_baseGroup {M V : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M)
    (hV : V ≤ baseGroup) (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) : V = ⊥ ∨ V = baseGroup := by
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  right
  rw [Subgroup.eq_bot_iff_forall] at hbot
  push Not at hbot
  obtain ⟨v, hv, hv1⟩ := hbot
  obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 (hV hv)
  have hfj : ∃ j, f j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv1
    rw [← shiftPerm_zero]
    congr 1
    funext i
    exact hcon i
  obtain ⟨j, hj⟩ := hfj
  have h0 := Clauses.shiftPerm_single_mem hEM hMV hv hj
  have h1 : ∀ c, shiftPerm (Pi.single (j + 1) c) ∈ V := fun c =>
    Clauses.shiftPerm_single_succ_mem hEM hMV (h0 c)
  have h2 : ∀ c, shiftPerm (Pi.single (j + 1 + 1) c) ∈ V := fun c =>
    Clauses.shiftPerm_single_succ_mem hEM hMV (h1 c)
  refine le_antisymm hV (Clauses.baseGroup_le_of_single_mem fun j' c => ?_)
  rcases (by decide : ∀ j j' : ZMod 3, j' = j ∨ j' = j + 1 ∨ j' = j + 1 + 1) j j' with
    rfl | rfl | rfl
  · exact h0 c
  · exact h1 c
  · exact h2 c

namespace Clauses

theorem commutator_mem_inf {M W : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M)
    (hMN : M ≤ nrm) (hWM : W ≤ M) (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt)))
    {w b : Perm Pt} (hw : w ∈ W) (hb : b ∈ baseGroup) : w * b * w⁻¹ * b⁻¹ ∈ W ⊓ baseGroup := by
  refine ⟨?_, ?_⟩
  · have h1 : b * w⁻¹ * b⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hN (baseGroup_le hEM hb)) w⁻¹).1 (W.inv_mem hw)
    simpa [mul_assoc] using W.mul_mem hw h1
  · have h1 : w * b * w⁻¹ ∈ baseGroup :=
      ((Subgroup.mem_set_normalizer_iff.1 (hMN (hWM hw)) b).1 hb :)
    exact baseGroup.mul_mem h1 (baseGroup.inv_mem hb)

theorem eq_bot_of_inf_baseGroup_eq_bot {M W : Subgroup (Perm Pt)}
    (hEM : alternatingGroup Pt ⊓ nrm ≤ M) (hMN : M ≤ nrm) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (h : W ⊓ baseGroup = ⊥) : W = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  have hc : w ∈ Subgroup.centralizer (baseGroup : Set (Perm Pt)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := commutator_mem_inf hEM hMN hWM hN hw hb
    rw [h, Subgroup.mem_bot] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  have h2 : w ∈ W ⊓ baseGroup := ⟨hw, mem_baseGroup_of_mem_centralizer hc⟩
  rwa [h, Subgroup.mem_bot] at h2

end Clauses

theorem eq_bot_of_coprime {M W : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M)
    (hMN : M ≤ nrm) (hWM : W ≤ M) (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt)))
    (hW : Nat.Coprime 3 (Nat.card W)) : W = ⊥ := by
  refine Clauses.eq_bot_of_inf_baseGroup_eq_bot hEM hMN hWM hN ?_
  have h1 : Nat.card ↥(W ⊓ baseGroup) ∣ Nat.card W := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(W ⊓ baseGroup) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : W ⊓ baseGroup ≤ baseGroup)
    rwa [card_baseGroup] at this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  have hcop : Nat.Coprime 3 (Nat.card ↥(W ⊓ baseGroup)) := hW.coprime_dvd_right h1
  have hi0 : i = 0 := by
    by_contra hne
    have h3 : 3 ∣ Nat.card ↥(W ⊓ baseGroup) := hi ▸ dvd_pow_self 3 hne
    exact absurd (hcop.eq_one_of_dvd h3) (by norm_num)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hi, hi0]; rfl)

theorem eq_bot_or_baseGroup_le {M W : Subgroup (Perm Pt)} (hEM : alternatingGroup Pt ⊓ nrm ≤ M)
    (hMN : M ≤ nrm) (hWM : W ≤ M) (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) :
    W = ⊥ ∨ baseGroup ≤ W := by
  have hinv : ∀ m ∈ M, ∀ v ∈ W ⊓ baseGroup, m * v * m⁻¹ ∈ W ⊓ baseGroup := by
    intro m hm v hv
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hN hm) v).1 hv.1, ?_⟩
    exact ((Subgroup.mem_set_normalizer_iff.1 (hMN hm) v).1 hv.2 :)
  rcases eq_bot_or_eq_baseGroup hEM inf_le_right hinv with h | h
  · exact Or.inl (Clauses.eq_bot_of_inf_baseGroup_eq_bot hEM hMN hWM hN h)
  · exact Or.inr (h ▸ inf_le_left)

theorem inf_centralizer_le {M : Subgroup (Perm Pt)} :
    M ⊓ Subgroup.centralizer (baseGroup : Set (Perm Pt)) ≤ baseGroup :=
  fun _ hg => mem_baseGroup_of_mem_centralizer hg.2

namespace Clauses

theorem signAt_conj_affPerm_apply (k l : ZMod 3) (f : ZMod 3 → ZMod 3) (i z : ZMod 3) :
    (signAt k * affPerm l f * (signAt k)⁻¹) (i, z) =
      (i + l, (if i + l = k then 1 else -1) * ((if i = k then 1 else -1) * z + f i)) := by
  rw [signAt_inv]
  by_cases h1 : i + l = k <;> by_cases h2 : i = k <;> simp [h1, h2]

theorem eq_zero_of_forall_sign_mul_eq_one :
    ∀ l : ZMod 3, (∀ i : ZMod 3,
      (if i + l = 2 then (1 : ZMod 3) else -1) * (if i = 2 then (1 : ZMod 3) else -1) = 1) →
      l = 0 := by
  decide

theorem eq_zero_of_signAt_conj_mem_sylowT {l : ZMod 3} {f : ZMod 3 → ZMod 3}
    (h : signAt 2 * affPerm l f * (signAt 2)⁻¹ ∈ sylowT) : l = 0 := by
  obtain ⟨l', f', h'⟩ := h
  refine eq_zero_of_forall_sign_mul_eq_one l fun i => ?_
  have h0 := congrArg (fun σ : Perm Pt => (σ (i, 0)).2) h'
  have h1 := congrArg (fun σ : Perm Pt => (σ (i, 1)).2) h'
  simp only [signAt_conj_affPerm_apply, affPerm_apply] at h0 h1
  linear_combination h1 - h0

end Clauses

theorem le_baseGroup_of_isPGroup {M W : Subgroup (Perm Pt)}
    (hT : ∀ Q : Subgroup (Perm Pt), IsPGroup 3 Q → sylowT ≤ Q → Q = sylowT)
    (hEM : alternatingGroup Pt ⊓ nrm ≤ M) (_hMN : M ≤ nrm) (_hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (hW : IsPGroup 3 W) : W ≤ baseGroup := by
  have hTN : sylowT ≤ Subgroup.normalizer (W : Set (Perm Pt)) := (Clauses.sylowT_le hEM).trans hN
  have hsup : IsPGroup 3 (W ⊔ sylowT : Subgroup (Perm Pt)) :=
    hW.to_sup_of_normal_left' isPGroup_sylowT hTN
  have hWT : W ≤ sylowT := le_sup_left.trans (hT _ hsup le_sup_right).le
  intro w hw
  obtain ⟨l, f, rfl⟩ := hWT hw
  have hs : signAt 2 * affPerm l f * (signAt 2)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.1 (hN (Clauses.signAt_mem hEM 2)) _).1 hw
  obtain rfl := Clauses.eq_zero_of_signAt_conj_mem_sylowT (hWT hs)
  rw [affPerm_zero_left]
  exact shiftPerm_mem_baseGroup f

end CFSG.AGLEmbedding.A9Local

module

public import CFSG.ClassicalInvolution.Q3.AE.Embed
public import CFSG.ClassicalInvolution.Q3.AE.Local

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

@[expose] noncomputable def memK (ι : Fin 4 ↪ Fin n) : Subgroup (Wr n) := kQ.map (embed ι)

@[expose] noncomputable def memKStar (ι : Fin 4 ↪ Fin n) : Subgroup (Wr n) := kQStar.map (embed ι)

@[expose] noncomputable def zOf (ι : Fin 4 ↪ Fin n) : Wr n := embed ι zQ

@[expose] noncomputable def yOf (ι : Fin 4 ↪ Fin n) : Wr n := embed ι yQ

theorem zOf_mem_memK (ι : Fin 4 ↪ Fin n) : zOf ι ∈ memK ι := ⟨zQ, zQ_mem_kQ, rfl⟩

theorem zOf_mem_memKStar (ι : Fin 4 ↪ Fin n) : zOf ι ∈ memKStar ι := ⟨zQ, zQ_mem_kQStar, rfl⟩

theorem memK_equiv (ι : Fin 4 ↪ Fin n) : Nonempty (memK ι ≃* QuaternionGroup 2) := by
  let f : QuaternionGroup 2 →* Wr n :=
    (embed ι).comp
      { toFun := kQHom, map_one' := by decide +kernel, map_mul' := kQHom_mul }
  have hf : Function.Injective f := (embed_injective ι).comp kQHom_injective
  have hrange : f.range = memK ι := by
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      exact ⟨kQHom q, kQHom_mem q, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      have hcard : Nat.card (QuaternionGroup 2) = 8 := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      have hsurj : ∀ a ∈ kQ, ∃ q, kQHom q = a := by
        intro a ha
        exact (by decide +kernel : ∀ a ∈ kList, ∃ q : QuaternionGroup 2, kQHom q = a) a ha
      obtain ⟨q, rfl⟩ := hsurj a ha
      exact ⟨q, rfl⟩
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem memKStar_equiv (ι : Fin 4 ↪ Fin n) : Nonempty (memKStar ι ≃* QuaternionGroup 2) := by
  let f : QuaternionGroup 2 →* Wr n :=
    (embed ι).comp
      { toFun := kQStarHom, map_one' := by decide +kernel, map_mul' := kQStarHom_mul }
  have hf : Function.Injective f := (embed_injective ι).comp kQStarHom_injective
  have hrange : f.range = memKStar ι := by
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      exact ⟨kQStarHom q, kQStarHom_mem q, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨q, rfl⟩ := kQStarHom_surj a ha
      exact ⟨q, rfl⟩
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem natCard_memK (ι : Fin 4 ↪ Fin n) : Nat.card (memK ι) = 8 := by
  obtain ⟨e⟩ := memK_equiv ι
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem natCard_memKStar (ι : Fin 4 ↪ Fin n) : Nat.card (memKStar ι) = 8 := by
  obtain ⟨e⟩ := memKStar_equiv ι
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eq_of_mem_memK_mul_self (ι : Fin 4 ↪ Fin n) :
    ∀ a ∈ memK ι, a * a = 1 → a = 1 ∨ a = zOf ι := by
  rintro _ ⟨a, ha, rfl⟩ h
  rw [← map_mul, ← (embed ι).map_one] at h
  rcases eq_of_mem_kQ_mul_self a ha (embed_injective ι h) with h1 | h1
  · left
    rw [h1, map_one]
  · right
    rw [h1]
    rfl

theorem eq_of_mem_memKStar_mul_self (ι : Fin 4 ↪ Fin n) :
    ∀ a ∈ memKStar ι, a * a = 1 → a = 1 ∨ a = zOf ι := by
  rintro _ ⟨a, ha, rfl⟩ h
  rw [← map_mul, ← (embed ι).map_one] at h
  rcases eq_of_mem_kQStar_mul_self a ha (embed_injective ι h) with h1 | h1
  · left
    rw [h1, map_one]
  · right
    rw [h1]
    rfl

theorem comm_memK_memKStar (ι : Fin 4 ↪ Fin n) :
    ∀ a ∈ memK ι, ∀ b ∈ memKStar ι, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, comm_kQ_kQStar a ha b hb]

theorem yOf_comm_zOf (ι : Fin 4 ↪ Fin n) : yOf ι * zOf ι = zOf ι * yOf ι := by
  unfold yOf zOf
  rw [← map_mul, ← map_mul, yQ_comm_zQ]

theorem yOf_conj_mem_memK (ι : Fin 4 ↪ Fin n) : ∀ a ∈ memK ι, yOf ι * a * (yOf ι)⁻¹ ∈ memK ι := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨yQ * a * yQ⁻¹, yQ_conj_mem_kQ a ha, ?_⟩
  unfold yOf
  rw [map_mul, map_mul, map_inv]

theorem yOf_conj_mem_memKStar (ι : Fin 4 ↪ Fin n) :
    ∀ a ∈ memKStar ι, yOf ι * a * (yOf ι)⁻¹ ∈ memKStar ι := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨yQ * a * yQ⁻¹, yQ_conj_mem_kQStar a ha, ?_⟩
  unfold yOf
  rw [map_mul, map_mul, map_inv]

theorem yOf_not_comm_memK (ι : Fin 4 ↪ Fin n) : ∃ a ∈ memK ι, yOf ι * a ≠ a * yOf ι := by
  obtain ⟨a, ha, hne⟩ := yQ_not_comm_kQ
  refine ⟨embed ι a, ⟨a, ha, rfl⟩, fun h => hne ?_⟩
  unfold yOf at h
  rw [← map_mul, ← map_mul] at h
  exact embed_injective ι h

theorem yOf_not_comm_memKStar (ι : Fin 4 ↪ Fin n) : ∃ a ∈ memKStar ι, yOf ι * a ≠ a * yOf ι := by
  obtain ⟨a, ha, hne⟩ := yQ_not_comm_kQStar
  refine ⟨embed ι a, ⟨a, ha, rfl⟩, fun h => hne ?_⟩
  unfold yOf at h
  rw [← map_mul, ← map_mul] at h
  exact embed_injective ι h

theorem yOf_pow_three (ι : Fin 4 ↪ Fin n) : yOf ι * yOf ι * yOf ι = 1 := by
  unfold yOf
  rw [← map_mul, ← map_mul, yQ_pow_three, map_one]

theorem memK_mul_vec (ι : Fin 4 ↪ Fin n) :
    (∀ a ∈ memK ι, ∃ b ∈ memKStar ι, (a⁻¹ * b).perm = 1) ∧
      (∀ b ∈ memKStar ι, ∃ a ∈ memK ι, (b⁻¹ * a).perm = 1) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := kQ_mul_vec.1 a ha
    refine ⟨embed ι b, ⟨b, hb, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, embed_perm, hab, embedPerm_one]
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hba⟩ := kQ_mul_vec.2 b hb
    refine ⟨embed ι a, ⟨a, ha, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, embed_perm, hba, embedPerm_one]

theorem supportedOn_of_mem_memK (ι : Fin 4 ↪ Fin n) {a : Wr n} (ha : a ∈ memK ι) :
    SupportedOn a (Set.range ι) := by
  obtain ⟨b, -, rfl⟩ := ha
  exact embed_supportedOn ι b

theorem supportedOn_of_mem_memKStar (ι : Fin 4 ↪ Fin n) {a : Wr n} (ha : a ∈ memKStar ι) :
    SupportedOn a (Set.range ι) := by
  obtain ⟨b, -, rfl⟩ := ha
  exact embed_supportedOn ι b

theorem yOf_supportedOn (ι : Fin 4 ↪ Fin n) : SupportedOn (yOf ι) (Set.range ι) :=
  embed_supportedOn ι yQ

theorem comm_of_disjoint_range {ι κ : Fin 4 ↪ Fin n} (h : Disjoint (Set.range ι) (Set.range κ))
    {a b : Wr n} (ha : SupportedOn a (Set.range ι)) (hb : SupportedOn b (Set.range κ)) :
    a * b = b * a :=
  comm_of_disjoint ha hb h

theorem zOf_vec_apply (ι : Fin 4 ↪ Fin n) (x : Fin n) :
    (zOf ι).vec x = if x ∈ Set.range ι then 1 else 0 := by
  classical
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    simp only [Set.mem_range_self, ite_true]
    unfold zOf
    rw [embed_vec, embedVec_apply]
    revert i
    decide
  · simp only [hx, ite_false]
    exact embed_vec_of_not_mem ι zQ hx

theorem zOf_perm (ι : Fin 4 ↪ Fin n) : (zOf ι).perm = 1 := by
  unfold zOf
  rw [embed_perm]
  exact embedPerm_one ι

theorem range_eq_of_zOf_eq {ι κ : Fin 4 ↪ Fin n} (h : zOf ι = zOf κ) :
    Set.range ι = Set.range κ := by
  classical
  ext x
  have := congrFun (congrArg Wr.vec h) x
  rw [zOf_vec_apply, zOf_vec_apply] at this
  by_cases hι : x ∈ Set.range ι <;> by_cases hκ : x ∈ Set.range κ <;> simp_all

theorem exists_d_move : ∀ m : Fin 4 → Bool, (∃ i, m i = true) → (∃ j, m j = false) →
    ∃ d ∈ [d₁, d₂, d₃], ∃ i, m i = true ∧ m (d i) = false := by
  decide

theorem exists_mem_kQ_perm : ∀ d ∈ [d₁, d₂, d₃], ∃ a ∈ kList, a.perm = d := by
  decide +kernel

theorem exists_mem_kQStar_perm : ∀ d ∈ [d₁, d₂, d₃], ∃ a ∈ kStarList, a.perm = d := by
  decide +kernel

theorem perm_mem_of_comm_zOf {ι : Fin 4 ↪ Fin n} {b : Wr n} (h : zOf ι * b = b * zOf ι)
    {x : Fin n} (hx : x ∈ Set.range ι) : b.perm x ∈ Set.range ι := by
  classical
  have hv := congrFun (congrArg Wr.vec h) (b.perm x)
  rw [mul_vec, mul_vec, zOf_perm] at hv
  simp only [Equiv.symm_apply_apply] at hv
  rw [zOf_vec_apply, zOf_vec_apply] at hv
  simp only [hx, ite_true] at hv
  by_contra hbx
  simp only [hbx, ite_false] at hv
  have h3 : b.vec (b.perm x) + 1 = b.vec (b.perm x) + 0 := by
    rw [add_zero]
    have h4 : (1 : Equiv.Perm (Fin n)).symm (b.perm x) = b.perm x := rfl
    rw [h4, zero_add] at hv
    exact hv.symm
  exact absurd (add_left_cancel h3) (by decide)

theorem not_comm_zOf_memK {ι κ : Fin 4 ↪ Fin n} (hne : (Set.range ι ∩ Set.range κ).Nonempty)
    (hneq : ¬ Set.range κ ⊆ Set.range ι) : ∃ b ∈ memK κ, zOf ι * b ≠ b * zOf ι := by
  classical
  obtain ⟨x, hxι, ⟨i, rfl⟩⟩ := hne
  obtain ⟨y, ⟨j, rfl⟩, hyι⟩ := Set.not_subset.mp hneq
  let m : Fin 4 → Bool := fun k => decide (κ k ∈ Set.range ι)
  obtain ⟨d, hd, k, hk1, hk2⟩ := exists_d_move m ⟨i, decide_eq_true hxι⟩ ⟨j, decide_eq_false hyι⟩
  obtain ⟨a, ha, hap⟩ := exists_mem_kQ_perm d hd
  refine ⟨embed κ a, ⟨a, ha, rfl⟩, fun h => ?_⟩
  have hmem := perm_mem_of_comm_zOf h (x := κ k) (of_decide_eq_true hk1)
  rw [embed_perm, hap, embedPerm_apply] at hmem
  have h5 : m (d k) = true := decide_eq_true hmem
  rw [h5] at hk2
  exact Bool.noConfusion hk2

theorem not_comm_zOf_memKStar {ι κ : Fin 4 ↪ Fin n} (hne : (Set.range ι ∩ Set.range κ).Nonempty)
    (hneq : ¬ Set.range κ ⊆ Set.range ι) : ∃ b ∈ memKStar κ, zOf ι * b ≠ b * zOf ι := by
  classical
  obtain ⟨x, hxι, ⟨i, rfl⟩⟩ := hne
  obtain ⟨y, ⟨j, rfl⟩, hyι⟩ := Set.not_subset.mp hneq
  let m : Fin 4 → Bool := fun k => decide (κ k ∈ Set.range ι)
  obtain ⟨d, hd, k, hk1, hk2⟩ := exists_d_move m ⟨i, decide_eq_true hxι⟩ ⟨j, decide_eq_false hyι⟩
  obtain ⟨a, ha, hap⟩ := exists_mem_kQStar_perm d hd
  refine ⟨embed κ a, ⟨a, ha, rfl⟩, fun h => ?_⟩
  have hmem := perm_mem_of_comm_zOf h (x := κ k) (of_decide_eq_true hk1)
  rw [embed_perm, hap, embedPerm_apply] at hmem
  have h5 : m (d k) = true := decide_eq_true hmem
  rw [h5] at hk2
  exact Bool.noConfusion hk2

end CFSG.ClassicalInvolution.Q3.AE

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXPerm

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Subgroup

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem s11s_theta_conj_embB {q : SL23} {v : Equiv.Perm (Fin 4)}
    (hq : ∀ i, q * k5g i * q⁻¹ = k5g (v i) ∨ q * k5g i * q⁻¹ = (k5g (v i))⁻¹) :
    h.theta (MulAut.conj (h.embB q)) = Equiv.Perm.sumCongr 1 v := by
  ext p
  rcases p with i | j
  · have hc : h.embB q * h.gen (Sum.inl i) = h.gen (Sum.inl i) * h.embB q :=
      (h.comm _ (h.gen_mem_A i) _ (h.embB_mem q)).symm
    have key : MulAut.conj (h.embB q) (h.gen (Sum.inl i)) = h.gen (Sum.inl i) := by
      rw [MulAut.conj_apply, hc]
      group
    have hi : h.theta (MulAut.conj (h.embB q)) (Sum.inl i) = Sum.inl i :=
      h.theta_eq (Or.inl key)
    rw [hi]
    simp
  · have key : MulAut.conj (h.embB q) (h.gen (Sum.inr j)) = h.embB (q * k5g j * q⁻¹) := by
      rw [MulAut.conj_apply, ← h.embB_k5g, map_mul, map_mul, map_inv]
    have hj : h.theta (MulAut.conj (h.embB q)) (Sum.inr j) = Sum.inr (v j) := by
      apply h.theta_eq
      rw [key]
      rcases hq j with e | e
      · left
        rw [e, h.embB_k5g]
      · right
        rw [e, map_inv, h.embB_k5g]
    rw [hj]
    simp

theorem s11s_sign_conj (k : K) : Equiv.Perm.sign (h.theta (MulAut.conj k)) = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul k
  obtain ⟨s1, rfl⟩ := h.exists_embA ha
  obtain ⟨s2, rfl⟩ := h.exists_embB hb
  obtain ⟨τ1, hτ1⟩ := s11s_exists_act s1
  obtain ⟨τ2, hτ2⟩ := s11s_exists_act s2
  have e1 : h.theta (MulAut.conj (h.embA s1)) = Equiv.Perm.sumCongr τ1 1 :=
    h.theta_conj_embA hτ1
  have e2 : h.theta (MulAut.conj (h.embB s2)) = Equiv.Perm.sumCongr 1 τ2 :=
    h.s11s_theta_conj_embB hτ2
  rw [map_mul MulAut.conj, map_mul h.theta, Equiv.Perm.sign_mul, e1, e2]
  simp [Equiv.Perm.sign_sumCongr, sign_of_act hτ1, sign_of_act hτ2]

theorem s11s_map_mem_of_genA (X : Subgroup K) {α : MulAut K} (h0 : α (h.gen (Sum.inl 0)) ∈ X)
    (h1 : α (h.gen (Sum.inl 1)) ∈ X) {a : K} (ha : a ∈ A) : α a ∈ X := by
  obtain ⟨s, rfl⟩ := h.exists_embA ha
  refine SL23_induction (P := fun s => α (h.embA s) ∈ X) ?_ ?_ ?_ ?_ ?_ s
  · show α (h.embA 1) ∈ X
    rw [map_one, map_one]
    exact one_mem X
  · intro a b ha hb
    have ha' : α (h.embA a) ∈ X := ha
    have hb' : α (h.embA b) ∈ X := hb
    show α (h.embA (a * b)) ∈ X
    rw [map_mul, map_mul]
    exact mul_mem ha' hb'
  · intro a ha
    have ha' : α (h.embA a) ∈ X := ha
    show α (h.embA a⁻¹) ∈ X
    rw [map_inv, map_inv]
    exact inv_mem ha'
  · show α (h.embA (k5g 0)) ∈ X
    rw [h.embA_k5g]
    exact h0
  · show α (h.embA (k5g 1)) ∈ X
    rw [h.embA_k5g]
    exact h1

theorem s11s_map_mem_of_genB (X : Subgroup K) {α : MulAut K} (h0 : α (h.gen (Sum.inr 0)) ∈ X)
    (h1 : α (h.gen (Sum.inr 1)) ∈ X) {b : K} (hb : b ∈ B) : α b ∈ X := by
  obtain ⟨s, rfl⟩ := h.exists_embB hb
  refine SL23_induction (P := fun s => α (h.embB s) ∈ X) ?_ ?_ ?_ ?_ ?_ s
  · show α (h.embB 1) ∈ X
    rw [map_one, map_one]
    exact one_mem X
  · intro a b ha hb
    have ha' : α (h.embB a) ∈ X := ha
    have hb' : α (h.embB b) ∈ X := hb
    show α (h.embB (a * b)) ∈ X
    rw [map_mul, map_mul]
    exact mul_mem ha' hb'
  · intro a ha
    have ha' : α (h.embB a) ∈ X := ha
    show α (h.embB a⁻¹) ∈ X
    rw [map_inv, map_inv]
    exact inv_mem ha'
  · show α (h.embB (k5g 0)) ∈ X
    rw [h.embB_k5g]
    exact h0
  · show α (h.embB (k5g 1)) ∈ X
    rw [h.embB_k5g]
    exact h1

theorem s11s_block_A (α : MulAut K) : (∀ a ∈ A, α a ∈ A) ∨ (∀ a ∈ A, α a ∈ B) := by
  by_cases h0 : (h.theta α (Sum.inl 0)).isLeft = true
  · left
    have h1 : (h.theta α (Sum.inl 1)).isLeft = true := by
      rw [← h.theta_block α (p := Sum.inl 0) (q := Sum.inl 1) rfl]
      exact h0
    have hm0 : α (h.gen (Sum.inl 0)) ∈ A :=
      h.mem_A_of_isLeft h0 (h.theta_spec α (Sum.inl 0))
    have hm1 : α (h.gen (Sum.inl 1)) ∈ A :=
      h.mem_A_of_isLeft h1 (h.theta_spec α (Sum.inl 1))
    exact fun a ha => h.s11s_map_mem_of_genA A hm0 hm1 ha
  · right
    have hf : (h.theta α (Sum.inl 0)).isLeft = false := Bool.eq_false_iff.mpr h0
    have hf1 : (h.theta α (Sum.inl 1)).isLeft = false := by
      rw [← h.theta_block α (p := Sum.inl 0) (q := Sum.inl 1) rfl]
      exact hf
    have hm0 : α (h.gen (Sum.inl 0)) ∈ B := by
      obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false hf
      have hspec := h.theta_spec α (Sum.inl 0)
      rw [hj] at hspec
      rcases hspec with e | e
      · rw [e]; exact h.gen_mem_B j
      · rw [e]; exact inv_mem (h.gen_mem_B j)
    have hm1 : α (h.gen (Sum.inl 1)) ∈ B := by
      obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false hf1
      have hspec := h.theta_spec α (Sum.inl 1)
      rw [hj] at hspec
      rcases hspec with e | e
      · rw [e]; exact h.gen_mem_B j
      · rw [e]; exact inv_mem (h.gen_mem_B j)
    exact fun a ha => h.s11s_map_mem_of_genA B hm0 hm1 ha

theorem s11s_block_B (α : MulAut K) : (∀ b ∈ B, α b ∈ B) ∨ (∀ b ∈ B, α b ∈ A) := by
  by_cases h0 : (h.theta α (Sum.inr 0)).isLeft = false
  · left
    have h1 : (h.theta α (Sum.inr 1)).isLeft = false := by
      rw [← h.theta_block α (p := Sum.inr 0) (q := Sum.inr 1) rfl]
      exact h0
    have hm0 : α (h.gen (Sum.inr 0)) ∈ B := by
      obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false h0
      have hspec := h.theta_spec α (Sum.inr 0)
      rw [hj] at hspec
      rcases hspec with e | e
      · rw [e]; exact h.gen_mem_B j
      · rw [e]; exact inv_mem (h.gen_mem_B j)
    have hm1 : α (h.gen (Sum.inr 1)) ∈ B := by
      obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false h1
      have hspec := h.theta_spec α (Sum.inr 1)
      rw [hj] at hspec
      rcases hspec with e | e
      · rw [e]; exact h.gen_mem_B j
      · rw [e]; exact inv_mem (h.gen_mem_B j)
    exact fun b hb => h.s11s_map_mem_of_genB B hm0 hm1 hb
  · right
    have h0' : (h.theta α (Sum.inr 0)).isLeft = true := by
      cases hv : (h.theta α (Sum.inr 0)).isLeft with
      | false => exact absurd hv h0
      | true => rfl
    have h1 : (h.theta α (Sum.inr 1)).isLeft = true := by
      rw [← h.theta_block α (p := Sum.inr 0) (q := Sum.inr 1) rfl]
      exact h0'
    have hm0 : α (h.gen (Sum.inr 0)) ∈ A :=
      h.mem_A_of_isLeft h0' (h.theta_spec α (Sum.inr 0))
    have hm1 : α (h.gen (Sum.inr 1)) ∈ A :=
      h.mem_A_of_isLeft h1 (h.theta_spec α (Sum.inr 1))
    exact fun b hb => h.s11s_map_mem_of_genB A hm0 hm1 hb

theorem s11s_theta_inl {α : MulAut K} (hA : ∀ a ∈ A, α a ∈ A) (i : Fin 4) :
    (h.theta α (Sum.inl i)).isLeft = true := by
  by_contra hne
  have hf : (h.theta α (Sum.inl i)).isLeft = false := Bool.eq_false_iff.mpr hne
  obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false hf
  have hspec := h.theta_spec α (Sum.inl i)
  rw [hj] at hspec
  have hmem : α (h.gen (Sum.inl i)) ∈ A := hA _ (h.gen_mem_A i)
  have hgenA : h.gen (Sum.inr j) ∈ A := by
    rcases hspec with e | e
    · rwa [e] at hmem
    · have : (h.gen (Sum.inr j))⁻¹ ∈ A := by rwa [e] at hmem
      simpa using inv_mem this
  exact h.gen_ne_one (Sum.inr j)
    (h.eq_one_of_mem_inf ⟨hgenA, h.gen_mem_B j⟩ (h.gen_pow_three _))

theorem s11s_theta_sumCongr {α : MulAut K} (hA : ∀ a ∈ A, α a ∈ A) :
    ∃ p₁ p₂ : Equiv.Perm (Fin 4), h.theta α = Equiv.Perm.sumCongr p₁ p₂ := by
  have hmaps : Set.MapsTo (h.theta α) (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := eq_inl_of_isLeft_true (h.s11s_theta_inl hA i)
    exact ⟨k, hk.symm⟩
  obtain ⟨p, hp⟩ :=
    MonoidHom.mem_range.mp (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps)
  exact ⟨p.1, p.2, by rw [← hp, Equiv.Perm.sumCongrHom_apply]⟩

theorem s11s_sign_swap {α : MulAut K} (h2 : α * α = 1) (hAB : ∀ a ∈ A, α a ∈ B) :
    Equiv.Perm.sign (h.theta α) = 1 := by
  apply s11s_sign_fpf
  · rw [← map_mul, h2, map_one]
  · intro p hp
    rcases p with i | j
    · have hf : (h.theta α (Sum.inl i)).isLeft = false :=
        h.isLeft_eq_false_of_mem_B (hAB _ (h.gen_mem_A i)) (h.theta_spec α (Sum.inl i))
      rw [hp] at hf
      exact Bool.false_ne_true hf.symm
    · have h2' : h.theta α * h.theta α = 1 := by rw [← map_mul, h2, map_one]
      have hinl : ∀ i, (h.theta α (Sum.inl i)).isLeft = false := fun i =>
        h.isLeft_eq_false_of_mem_B (hAB _ (h.gen_mem_A i)) (h.theta_spec α (Sum.inl i))
      have hfex : ∀ i, ∃ k, h.theta α (Sum.inl i) = Sum.inr k := fun i =>
        eq_inr_of_isLeft_false (hinl i)
      let f : Fin 4 → Fin 4 := fun i => Classical.choose (hfex i)
      have hf_spec : ∀ i, h.theta α (Sum.inl i) = Sum.inr (f i) :=
        fun i => Classical.choose_spec (hfex i)
      have hf_inj : Function.Injective f := by
        intro i1 i2 he
        have hh : h.theta α (Sum.inl i1) = h.theta α (Sum.inl i2) := by
          rw [hf_spec i1, hf_spec i2, he]
        exact Sum.inl.inj ((h.theta α).injective hh)
      have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
      obtain ⟨i, hi⟩ := hf_surj j
      have key : h.theta α (Sum.inr j) = Sum.inl i := by
        have h1 : h.theta α (Sum.inr j) = h.theta α (h.theta α (Sum.inl i)) := by
          rw [hf_spec i, hi]
        rw [h1, ← Equiv.Perm.mul_apply, h2']
        simp
      rw [hp] at key
      exact Sum.inr_ne_inl key

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5

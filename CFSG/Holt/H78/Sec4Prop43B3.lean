module

public import CFSG.Holt.H78.Sec4Prop43B2
import CFSG.Holt.H78.Sec4Box

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Factor

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_commute_involution_alternatingGroup {m : Equiv.Perm Ψ}
    (hmA : m ∈ alternatingGroup Ψ) (hm2 : m * m = 1) (hm1 : m ≠ 1) {c : Ψ} (hmc : m c = c) :
    ∃ m' ∈ alternatingGroup Ψ, m' c = c ∧ m' * m' = 1 ∧ m' ≠ 1 ∧ m' ≠ m ∧ m * m' = m' * m := by
  have hmm : ∀ x, m (m x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, hm2, Equiv.Perm.one_apply]
  obtain ⟨a₁, ha₁⟩ : ∃ a, m a ≠ a := by
    by_contra h
    push Not at h
    exact hm1 (Equiv.ext h)
  obtain ⟨b₁, hb₁def⟩ : ∃ b, m a₁ = b := ⟨_, rfl⟩
  have hb₁ : m b₁ = a₁ := by rw [← hb₁def, hmm]
  have hb₁a₁ : b₁ ≠ a₁ := hb₁def ▸ ha₁
  obtain ⟨a₂, ha₂₁, ha₂₂, ha₂⟩ : ∃ a, a ≠ a₁ ∧ a ≠ b₁ ∧ m a ≠ a := by
    by_contra h
    push Not at h
    have hmeq : m = Equiv.swap a₁ b₁ := by
      refine Equiv.ext fun x => ?_
      by_cases hx₁ : x = a₁
      · rw [hx₁, Equiv.swap_apply_left, hb₁def]
      · by_cases hx₂ : x = b₁
        · rw [hx₂, Equiv.swap_apply_right, hb₁]
        · rw [Equiv.swap_apply_of_ne_of_ne hx₁ hx₂]
          exact h x hx₁ hx₂
    rw [hmeq, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hb₁a₁.symm] at hmA
    exact absurd hmA (by decide)
  obtain ⟨b₂, hb₂def⟩ : ∃ b, m a₂ = b := ⟨_, rfl⟩
  have hb₂ : m b₂ = a₂ := by rw [← hb₂def, hmm]
  have hb₂a₂ : b₂ ≠ a₂ := hb₂def ▸ ha₂
  have hb₂a₁ : b₂ ≠ a₁ := fun h => ha₂₂ (by rw [← hb₂, h, hb₁def])
  have hb₂b₁ : b₂ ≠ b₁ := fun h => ha₂₁ (m.injective (by rw [hb₂def, hb₁def, h]))
  have hnd : [a₁, a₂, b₁, b₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_or, and_true]
    exact ⟨⟨Ne.symm ha₂₁, hb₁a₁.symm, Ne.symm hb₂a₁⟩, ⟨ha₂₂, Ne.symm hb₂a₂⟩, Ne.symm hb₂b₁,
      fun h => h⟩
  have hdisj := Equiv.Perm.disjoint_swap_swap hnd
  set m' := Equiv.swap a₁ a₂ * Equiv.swap b₁ b₂
  have hca₁ : c ≠ a₁ := fun h => ha₁ (h ▸ hmc)
  have hca₂ : c ≠ a₂ := fun h => ha₂ (h ▸ hmc)
  have hcb₁ : c ≠ b₁ := fun h => hb₁a₁ (by rw [← hb₁, ← h, hmc])
  have hcb₂ : c ≠ b₂ := fun h => hb₂a₂ (by rw [← hb₂, ← h, hmc])
  refine ⟨m', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm ha₂₁),
      Equiv.Perm.sign_swap hb₂b₁.symm]
    decide
  · change Equiv.swap a₁ a₂ (Equiv.swap b₁ b₂ c) = c
    rw [Equiv.swap_apply_of_ne_of_ne hcb₁ hcb₂, Equiv.swap_apply_of_ne_of_ne hca₁ hca₂]
  · change Equiv.swap a₁ a₂ * Equiv.swap b₁ b₂ * (Equiv.swap a₁ a₂ * Equiv.swap b₁ b₂) = 1
    rw [mul_assoc, ← mul_assoc (Equiv.swap b₁ b₂), (hdisj.commute).symm.eq, mul_assoc,
      Equiv.swap_mul_self, mul_one, Equiv.swap_mul_self]
  · intro h
    have := congrArg (fun g : Equiv.Perm Ψ => g a₁) h
    change Equiv.swap a₁ a₂ (Equiv.swap b₁ b₂ a₁) = a₁ at this
    rw [Equiv.swap_apply_of_ne_of_ne hb₁a₁.symm hb₂a₁.symm, Equiv.swap_apply_left] at this
    exact ha₂₁ this
  · intro h
    have := congrArg (fun g : Equiv.Perm Ψ => g a₁) h
    change Equiv.swap a₁ a₂ (Equiv.swap b₁ b₂ a₁) = m a₁ at this
    rw [Equiv.swap_apply_of_ne_of_ne hb₁a₁.symm hb₂a₁.symm, Equiv.swap_apply_left, hb₁def] at this
    exact ha₂₂ this
  · have hconj : m * m' * m⁻¹ = m' := by
      have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
      calc m * m' * m⁻¹ = m * Equiv.swap a₁ a₂ * m⁻¹ * (m * Equiv.swap b₁ b₂ * m⁻¹) := by
            simp only [m', mul_assoc, inv_mul_cancel_left]
        _ = Equiv.swap b₁ b₂ * Equiv.swap a₁ a₂ := by
            rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, hb₁, hb₂, hb₁def, hb₂def]
        _ = m' := hdisj.commute.eq.symm
    calc m * m' = m * m' * m⁻¹ * m := by group
      _ = m' * m := by rw [hconj]

theorem IsHoltFactor.exists_commute_involution {M : Subgroup (Equiv.Perm Ψ)}
    (hM : IsHoltFactor M) {m : Equiv.Perm Ψ} (hmM : m ∈ M) (hm2 : m * m = 1) (hm1 : m ≠ 1)
    {c : Ψ} (hmc : m c = c) :
    ∃ m' ∈ M, m' c = c ∧ m' * m' = 1 ∧ m' ≠ 1 ∧ m' ≠ m ∧ m * m' = m' * m := by
  rcases hM with ⟨rfl, -⟩ | hSE
  · exact exists_commute_involution_alternatingGroup hmM hm2 hm1 hmc
  · obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    have hcard := hA.ncard_longInvAt c
    have h4 := hA.four_le_q
    obtain ⟨t, ht, htm⟩ : ∃ t ∈ longInvAt (↥M) Ψ c, (t : Equiv.Perm Ψ) ≠ m := by
      by_contra h
      push Not at h
      have hsub : (longInvAt (↥M) Ψ c).Subsingleton := fun t ht t' ht' =>
        Subtype.ext ((h t ht).trans (h t' ht').symm)
      have := Set.ncard_le_one_iff_subsingleton.mpr hsub
      omega
    have ht2 : (t : Equiv.Perm Ψ) * t = 1 := by
      have h2 := pow_orderOf_eq_one t
      rw [ht.1.1, sq] at h2
      exact congrArg Subtype.val h2
    have htc : (t : Equiv.Perm Ψ) c = c := ht.2
    refine ⟨t, t.2, htc, ht2, fun h => ?_, htm, ?_⟩
    · have h1 : t = 1 := Subtype.ext h
      have := ht.1.1
      rw [h1, orderOf_one] at this
      omega
    · exact hSE.commute_of_mem_mulLongInvClosure (hSE.mem_mulLongInvClosure_of_mul_self hmM hmc hm2)
        (hSE.mem_mulLongInvClosure_of_mul_self t.2 htc ht2)

theorem mem_closure_pair_of_commute {K : Type*} [Group K] {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {g : K} (hg : g ∈ Subgroup.closure {a, b}) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have h1 : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have h3 : ∀ x, b * (a * x) = a * (b * x) := fun x => by rw [← mul_assoc, ← hab, mul_assoc]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [mul_assoc, h1, h3, ← hab, ha, hb, mul_one, one_mul, true_or, or_true]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hainv)
    · exact Or.inr (Or.inr (Or.inl hbinv))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, hainv, hbinv, hab]

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem fixingSubgroup_singleton_perm (c : Ψ) :
    fixingSubgroup (Equiv.Perm Ψ) ({c} : Set Ψ) = stabilizer (Equiv.Perm Ψ) c := by
  ext g
  simp [mem_fixingSubgroup_iff, mem_stabilizer_iff]

end Factor

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_one_of_kerCHom_eq_one (hT : Odd (Nat.card (twoPointKernel G Ω α β))) {i : C.D.ι}
    {q : C.kerC i} (hqP : (q : G) ∈ C.calP) (hq : C.kerCHom i q = 1) : (q : G) = 1 :=
  eq_one_of_smul_eq_of_odd hT (C.sylow.2.1.to_le inf_le_left) hqP (C.kerC_le_inf i q.2)
    (C.smul_eq_of_kerCHom_eq_one hq)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_of_kerCHom_eq (hT : Odd (Nat.card (twoPointKernel G Ω α β))) {i : C.D.ι}
    {q q' : C.kerC i} (hqP : (q : G) ∈ C.calP) (hq'P : (q' : G) ∈ C.calP)
    (h : C.kerCHom i q = C.kerCHom i q') : q = q' := by
  have h1 : C.kerCHom i (q * q'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := C.eq_one_of_kerCHom_eq_one hT (q := q * q'⁻¹)
    (C.calP.mul_mem hqP (C.calP.inv_mem hq'P)) h1
  exact Subtype.ext (mul_inv_eq_one.mp h2)

omit [FaithfulSMul G Ω] in
theorem exists_x_of_lemma44 (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    {i : C.D.ι} (h4 : Fintype.card (C.D.Ψc i) % 4 = 1) :
    ∃ x : G, x * x = 1 ∧ x • α = β ∧ x ∈ stabilizer G ({α, β} : Set Ω) ∧
      (∀ q ∈ C.calP ⊓ C.kerC i, x * q = q * x) ∧
      ∃ y : ∀ j, Equiv.Perm (C.D.Ψc j), (∀ j, y j ∈ longInv (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j)) ∧
        (∀ j, y j (C.D.coord C.γ j) = C.D.coord C.γ j) ∧
        ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = x • (δ : Ω) →
          (∀ j, j ≠ i → C.D.coord δ' j = y j (C.D.coord δ j)) ∧
            C.D.coord δ' i = C.D.coord δ i := by
  obtain ⟨y, hyJ, hyw⟩ := hS.exists_coord_smul_of_mem_longInvSwap hαβ C.D C.w_mem
  have hyγ : ∀ j, y j (C.D.coord C.γ j) = C.D.coord C.γ j := fun j =>
    (congrFun (hyw C.γ C.γ C.w_fix.symm) j).symm
  have hyy : ∀ j c, y j (y j c) = c := fun j c => by
    rw [← Equiv.Perm.mul_apply, mul_self_eq_one_of_mem_longInv (hyJ j), Equiv.Perm.one_apply]
  have hwS : ∀ g ∈ C.S, g * C.w = C.w * g := fun g hg =>
    Subgroup.mem_centralizer_iff.mp C.w_comm g hg
  have hcomm : ∀ q : C.kerC i, (q : G) ∈ C.calP →
      y i * C.kerCHom i q = C.kerCHom i q * y i := by
    intro q hqP
    refine Equiv.ext fun c => ?_
    set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) i c)
    have hδ : C.D.coord δ i = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
    have hwmem : C.w ∈ stabilizer G ({α, β} : Set Ω) :=
      closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure C.w_mem)
    set δ₁ := twoPointElt (C.kerC_le_stabilizer_pair i q.2) • δ
    set δ₂ := twoPointElt hwmem • δ₁
    set δ₃ := twoPointElt hwmem • δ
    set δ₄ := twoPointElt (C.kerC_le_stabilizer_pair i q.2) • δ₃
    have h24 : δ₂ = δ₄ := Subtype.ext (by
      change C.w • (q : G) • (δ : Ω) = (q : G) • C.w • (δ : Ω)
      rw [← mul_smul, ← mul_smul, hwS q (Subgroup.mem_inf.mp hqP).1])
    have e2 := congrFun (hyw δ₁ δ₂ rfl) i
    have e1 := C.coord_smul_eq_kerCHom q (δ := δ) (δ' := δ₁) rfl
    have e3 := congrFun (hyw δ δ₃ rfl) i
    have e4 := C.coord_smul_eq_kerCHom q (δ := δ₃) (δ' := δ₄) rfl
    simp only [Equiv.Perm.mul_apply]
    rw [← hδ, ← e1, ← e2, h24, e4, e3]
  have hV := C.fusionIsSylowIn_Qimg_inf hS hP i
  rw [← fixingSubgroup_singleton_perm] at hV
  have hcard : Nat.card ↥(({C.D.coord C.γ i} : Set (C.D.Ψc i))ᶜ) =
      Fintype.card (C.D.Ψc i) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp
  have hyV : y i ∈ C.Qimg i ⊓ alternatingGroup (C.D.Ψc i) := by
    refine mem_of_commute_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup
      (by rw [hcard]; have := C.D.five_le_card i; omega) hV ?_ fun v hv => ?_
    · rw [fixingSubgroup_singleton_perm]
      exact hyγ i
    · obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hv).1
      exact hcomm q hqP
  obtain ⟨z, hzP, hzy⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hyV).1
  have hzS : (z : G) ∈ C.S := (Subgroup.mem_inf.mp hzP).1
  have hz2 : (z : G) * z = 1 := by
    have h := C.eq_one_of_kerCHom_eq_one hT (q := z * z) (C.calP.mul_mem hzP hzP)
      (by rw [map_mul, hzy, mul_self_eq_one_of_mem_longInv (hyJ i)])
    exact h
  have hzc : ∀ q ∈ C.calP ⊓ C.kerC i, (z : G) * q = q * z := by
    intro q hq
    have := C.eq_of_kerCHom_eq hT (q := z * ⟨q, hq.2⟩) (q' := ⟨q, hq.2⟩ * z)
      (C.calP.mul_mem hzP hq.1) (C.calP.mul_mem hq.1 hzP)
      (by rw [map_mul, map_mul, hzy, hcomm ⟨q, hq.2⟩ hq.1])
    exact congrArg Subtype.val this
  have hwz : (z : G) * C.w = C.w * z := hwS z hzS
  have hw2 : C.w * C.w = 1 := mul_self_eq_one_of_mem_longInv C.w_mem.1
  have hwmem : C.w ∈ stabilizer G ({α, β} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure C.w_mem)
  have hzα : (z : G) • α = α := mem_stabilizer_iff.mp (C.kerC_le_inf i z.2).1
  refine ⟨C.w * z, ?_, ?_, ?_, ?_, y, hyJ, hyγ, ?_⟩
  · calc C.w * z * (C.w * z) = C.w * C.w * (z * z) := by
          rw [mul_assoc, ← mul_assoc (z : G), hwz, mul_assoc, mul_assoc]
      _ = 1 := by rw [hw2, hz2, one_mul]
  · rw [mul_smul, hzα]
    exact C.w_mem.2
  · exact (stabilizer G ({α, β} : Set Ω)).mul_mem hwmem (C.kerC_le_stabilizer_pair i z.2)
  · intro q hq
    rw [mul_assoc, hzc q hq, ← mul_assoc, ← hwS q (Subgroup.mem_inf.mp hq.1).1, mul_assoc]
  · intro δ δ' e
    set δ₁ := twoPointElt (C.kerC_le_stabilizer_pair i z.2) • δ
    have e1 : (δ' : Ω) = C.w • (δ₁ : Ω) := by
      rw [e, mul_smul]
      rfl
    have h1 := hyw δ₁ δ' e1
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [h1]
      dsimp only
      rw [C.coord_smul_of_mem_kerC z.2 (δ' := δ₁) rfl hj]
    · rw [h1]
      dsimp only
      rw [C.coord_smul_eq_kerCHom z (δ' := δ₁) rfl, hzy]
      exact hyy i _

omit [FaithfulSMul G Ω] in
theorem mul_mem_longInv_of_lemma44 (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) {i : C.D.ι} {x : G} (hx2 : x * x = 1)
    (hxα : x • α = β) (hxS : x ∈ stabilizer G ({α, β} : Set Ω))
    (hxQ : ∀ q ∈ C.calP ⊓ C.kerC i, x * q = q * x) {y : ∀ j, Equiv.Perm (C.D.Ψc j)}
    (hyJ : ∀ j, y j ∈ longInv (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j))
    (hyγ : ∀ j, y j (C.D.coord C.γ j) = C.D.coord C.γ j)
    (hxy : ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = x • (δ : Ω) →
      (∀ j, j ≠ i → C.D.coord δ' j = y j (C.D.coord δ j)) ∧ C.D.coord δ' i = C.D.coord δ i)
    {q : C.kerC i} (hqP : (q : G) ∈ C.calP) (hq2 : C.kerCHom i q * C.kerCHom i q = 1)
    (hqfree : ∀ c, c ≠ C.D.coord C.γ i → C.kerCHom i q c ≠ c) :
    x * q ∈ longInv G Ω := by
  have hqQ : (q : G) ∈ C.calP ⊓ C.kerC i := Subgroup.mem_inf.mpr ⟨hqP, q.2⟩
  have hqq : (q : G) * q = 1 := C.eq_one_of_kerCHom_eq_one hT (q := q * q)
    (C.calP.mul_mem hqP hqP) (by rw [map_mul, hq2])
  have hqα : (q : G) • α = α := mem_stabilizer_iff.mp (C.kerC_le_inf i q.2).1
  have h2 : (x * q) ^ 2 = 1 := by
    rw [sq, mul_assoc, ← mul_assoc (q : G), ← hxQ q hqQ, mul_assoc, hqq, mul_one, hx2]
  have hα : (x * q) • α = β := by rw [mul_smul, hqα, hxα]
  have hne : x * q ≠ 1 := fun h => hαβ (by rw [← hα, h, one_smul])
  have h3 := three_le_card_holtDelta_of_holtData hS.star C.D
  refine (hS.mem_longInv_iff_of_odd_twoPointKernel hαβ hT h3 (orderOf_eq_prime h2 hne) hα).mpr ?_
  have hfix : ∀ δ : holtDelta G Ω α β, (x * q) • (δ : Ω) = δ → δ = C.γ := by
    intro δ hδ
    set δ₁ := twoPointElt (C.kerC_le_stabilizer_pair i q.2) • δ
    have e : (δ : Ω) = x • (δ₁ : Ω) := by
      change (δ : Ω) = x • (q : G) • (δ : Ω)
      rw [← mul_smul]
      exact hδ.symm
    obtain ⟨hj, hi⟩ := hxy δ₁ δ e
    refine C.eq_of_coord_eq (funext fun j => ?_)
    by_cases hji : j = i
    · subst hji
      rw [C.coord_smul_eq_kerCHom q (δ' := δ₁) rfl] at hi
      by_contra hne'
      exact hqfree _ hne' hi.symm
    · have h1 := hj j hji
      rw [C.coord_smul_of_mem_kerC q.2 (δ' := δ₁) rfl hji] at h1
      exact (hyJ j).2.unique h1.symm (hyγ j)
  refine ⟨C.γ, ⟨C.γ.2, ?_⟩, fun δ hδ => ?_⟩
  · have hxγ : x • (C.γ : Ω) = C.γ := by
      have hmem : x • (C.γ : Ω) ∈ holtDelta G Ω α β := (twoPointElt hxS • C.γ).2
      obtain ⟨hj, hi⟩ := hxy C.γ ⟨_, hmem⟩ rfl
      have : (⟨_, hmem⟩ : holtDelta G Ω α β) = C.γ := C.eq_of_coord_eq (funext fun j => by
        by_cases hji : j = i
        · subst hji
          exact hi
        · rw [hj j hji, hyγ j])
      exact congrArg Subtype.val this
    rw [mul_smul, C.smul_eq_of_mem_kerC q.2 rfl, hxγ]
  · exact congrArg Subtype.val (hfix ⟨δ, hδ.1⟩ hδ.2)

end AltConfig

end CFSG.Holt.H78

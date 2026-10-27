module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic
public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups
public import CFSG.GH74.Uniqueness.SU.SU1BgTwoMaxClass
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup
open CFSG.GH74.GLS.Stage1.Thm3.Sec6

section Core

@[expose] def DSDData (M : Type) [Group M] : Prop :=
  ∃ (A : Subgroup M) (u : M), IsCyclic ↥A ∧ u ∈ A ∧ orderOf u = 4 ∧
    (∀ x : M, x ∉ A → orderOf x < Nat.card A) ∧ (∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹)

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem pow_four_aux {u : M} (h : orderOf u = 4) : u * (u * (u * u)) = 1 := by
  have h1 : u ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one u
  simpa [pow_succ, mul_assoc] using h1

theorem eq_or_inv_of_orderOf_four {A : Subgroup M} (hA : IsCyclic ↥A) {u x : M} (hu : u ∈ A) (hx : x ∈ A)
    (hu4 : orderOf u = 4) (hx4 : orderOf x = 4) : x = u ∨ x = u⁻¹ := by
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val ((hA.isMulCommutative).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hu4' := pow_four_aux hu4
  have hx4' := pow_four_aux hx4
  have huu2 : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u * (u * (u * u)) := by group
      _ = 1 := hu4'
  have hxx2 : (x * x) * (x * x) = 1 := by
    calc (x * x) * (x * x) = x * (x * (x * x)) := by group
      _ = 1 := hx4'
  have hne : ∀ y : M, orderOf y = 4 → y * y ≠ 1 := by
    intro y hy h
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hy] at this
    omega
  have huu1 := hne u hu4
  have hxx1 := hne x hx4
  have huuA : u * u ∈ A := A.mul_mem hu hu
  have hxxA : x * x ∈ A := A.mul_mem hx hx
  have hsq : x * x = u * u :=
    B.cyclic_invol_unique hA hxxA huuA hxx2 huu2 hxx1 huu1
  have hwA : u⁻¹ * x ∈ A := A.mul_mem (A.inv_mem hu) hx
  have hw2 : (u⁻¹ * x) * (u⁻¹ * x) = 1 := by
    have hc := hAcomm x hx u⁻¹ (A.inv_mem hu)
    calc (u⁻¹ * x) * (u⁻¹ * x) = u⁻¹ * (x * u⁻¹) * x := by group
      _ = u⁻¹ * (u⁻¹ * x) * x := by rw [hc]
      _ = (u⁻¹ * u⁻¹) * (x * x) := by group
      _ = 1 := by rw [hsq]; group
  by_cases hw1 : u⁻¹ * x = 1
  · left
    exact (inv_mul_eq_one.1 hw1).symm
  · right
    have hww : u⁻¹ * x = u * u :=
      B.cyclic_invol_unique hA hwA huuA hw2 huu2 hw1 huu1
    have hinv : u⁻¹ = u * (u * u) := inv_eq_of_mul_eq_one_right hu4'

    calc x = u * (u⁻¹ * x) := by group
      _ = u * (u * u) := by rw [hww]
      _ = u⁻¹ := hinv.symm

theorem dsd_core {A : Subgroup M} (hA : IsCyclic ↥A) {u : M} (hu : u ∈ A) (hu4 : orderOf u = 4)
    (hout : ∀ x : M, x ∉ A → orderOf x < Nat.card A)
    (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹)
    {z : M} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ g : M, g * z = z * g) :
    u * u = z ∧ (∀ φ : M ≃* M, φ u = u ∨ φ u = u * z) ∧
      ∀ b : M, b * b = 1 → b ≠ 1 → b ≠ z → b * u * b⁻¹ = u * z := by
  have hu4' := pow_four_aux hu4
  have huu : u * u ∈ A := A.mul_mem hu hu
  have huu2 : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u * (u * (u * u)) := by group
      _ = 1 := hu4'
  have huu1 : u * u ≠ 1 := by
    intro h
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hu4] at this
    omega
  have hzA : z ∈ A := by
    by_contra hn
    have h1 := hinv z hn
    have h2 : z * u * z⁻¹ = u := by rw [← hzc u]; group
    have h3 : u = u⁻¹ := h2.symm.trans h1
    apply huu1
    calc u * u = u⁻¹ * u := by rw [← h3]
      _ = 1 := inv_mul_cancel u
  have hz_eq : z = u * u := B.cyclic_invol_unique hA hzA huu hz2 huu2 hz1 huu1
  have hinvu : u⁻¹ = u * z := by
    rw [hz_eq]
    exact inv_eq_of_mul_eq_one_right hu4'
  refine ⟨hz_eq.symm, ?_, ?_⟩
  · intro φ
    have hφA : ∀ x ∈ A, φ x ∈ A := by
      intro x hx
      obtain ⟨g, hg⟩ := hA.exists_generator
      have hgord : orderOf (g : M) = Nat.card A := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_card_of_forall_mem_zpowers hg
      have hφg : φ (g : M) ∈ A := by
        by_contra hn
        have := hout _ hn
        rw [MulEquiv.orderOf_eq, hgord] at this
        exact lt_irrefl _ this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      have hxk : x = (g : M) ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      rw [hxk, map_zpow]
      exact A.zpow_mem hφg k
    have hφu : φ u ∈ A := hφA u hu
    have hφ4 : orderOf (φ u) = 4 := by rw [MulEquiv.orderOf_eq]; exact hu4
    rcases eq_or_inv_of_orderOf_four hA hu hφu hu4 hφ4 with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hinvu)
  · intro b hb2 hb1 hbz
    have hbA : b ∉ A := fun hbA =>
      hbz (B.cyclic_invol_unique hA hbA hzA hb2 hz2 hb1 hz1)
    rw [hinv b hbA, hinvu]

end Core

section Transport

theorem DSDData.congr {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (h : DSDData M) : DSDData M' := by
  obtain ⟨A, u, hA, hu, hu4, hout, hinv⟩ := h
  refine ⟨A.map e.toMonoidHom, e u, ?_, Subgroup.mem_map_of_mem _ hu, ?_, ?_, ?_⟩
  · have e1 : ↥A ≃* ↥(A.map e.toMonoidHom) := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
    exact e1.isCyclic.1 hA
  · rw [MulEquiv.orderOf_eq]; exact hu4
  · intro x hx
    have hx' : e.symm x ∉ A := fun hmem => hx ⟨e.symm x, hmem, by simp⟩
    have h1 := hout _ hx'
    rw [MulEquiv.orderOf_eq] at h1
    rw [Subgroup.card_map_of_injective e.injective]
    exact h1
  · intro x hx
    have hx' : e.symm x ∉ A := fun hmem => hx ⟨e.symm x, hmem, by simp⟩
    have h1 := congrArg e (hinv _ hx')
    simpa using h1

end Transport


section Aux

variable {M : Type} [Group M]

theorem exists_two_ne_one_aux {E : Subgroup M} [Finite E] (h : 3 ≤ Nat.card E) :
    ∃ v ∈ E, ∃ w ∈ E, v ≠ 1 ∧ w ≠ 1 ∧ v ≠ w := by
  by_contra hne
  push Not at hne
  by_cases hQ : E = ⊥
  · rw [hQ, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨v, hvQ⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
  have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
  have hsub : (E : Set M) ⊆ {1, v} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hne x hx v hvQ hx1 hv1')
  have h2 : (E : Set M).ncard ≤ ({1, v} : Set M).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, v} : Set M).ncard ≤ 2 := by
    refine (Set.ncard_insert_le 1 {v}).trans ?_
    rw [Set.ncard_singleton]
  have h4 : Nat.card E = (E : Set M).ncard := Nat.card_coe_set_eq (E : Set M)
  omega

end Aux

section Dihedral

open DihedralGroup

theorem dsdData_dihedral (N : ℕ) [NeZero N] (h4 : 4 ∣ N) : DSDData (DihedralGroup N) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN4 : 4 ≤ N := Nat.le_of_dvd hN0 h4
  have hmem : ∀ i : ZMod N, (r i : DihedralGroup N) ∈ zpowers (r 1 : DihedralGroup N) := by
    intro i
    refine Subgroup.mem_zpowers_iff.2 ⟨(i.val : ℤ), ?_⟩
    rw [r_one_zpow]
    simp
  have hord : orderOf (r 1 : DihedralGroup N) = N := orderOf_r_one
  refine ⟨zpowers (r 1), (r 1) ^ (N / 4), inferInstance, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · have hq : N / 4 ≠ 0 := by
      have : 0 < N / 4 := Nat.div_pos hN4 (by norm_num)
      omega
    rw [orderOf_pow_of_dvd hq (by rw [hord]; exact Nat.div_dvd_of_dvd h4), hord]
    exact Nat.div_div_self h4 (NeZero.ne N)
  · intro x hx
    cases x with
    | r i => exact absurd (hmem i) hx
    | sr j =>
      rw [orderOf_sr, Nat.card_zpowers, hord]
      omega
  · intro x hx
    cases x with
    | r i => exact absurd (hmem i) hx
    | sr j =>
      rw [r_one_pow, inv_r, inv_sr, sr_mul_r, sr_mul_sr]
      congr 1
      ring

end Dihedral

section Semidihedral

open CFSG.Semidihedral CFSG.Open

theorem dsdData_semidihedral (n : ℕ) (hn : 4 ≤ n) : DSDData (SemidihedralGroup n) := by
  have hn3 : 3 ≤ n := by omega
  have hhalf : half n = 2 * 2 ^ (n - 3) := half_eq_two_mul_quarter hn3
  have hmod : modulus n = 2 * half n := modulus_eq_two_mul_half (by omega)
  have hq2 : 2 ≤ 2 ^ (n - 3) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : half n / 2 = 2 ^ (n - 3) := by omega
  have hA : Nat.card (rotationSubgroup n) = modulus n := rotationSubgroup_natCard n hn3
  have hsd := sd_quarter_facts n hn
  rw [hq] at hsd
  refine ⟨rotationSubgroup n, r n ^ (2 ^ (n - 3)), rotationSubgroup_cyclic n, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [r_pow_eq_element n hn3, rotation_order_four_iff n hn]
    exact Or.inl rfl
  · intro x hx
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective x
    change element n hn3 i e ∉ rotationSubgroup n at hx
    rw [element_mem_rotationSubgroup_iff n hn3] at hx
    have he : e = 1 := by
      rcases exponent_cases e with h | h
      · exact absurd h hx
      · exact h
    subst he
    change orderOf (element n hn3 i 1) < Nat.card (rotationSubgroup n)
    rw [hA]
    by_cases hp : i.val % 2 = 0
    · rw [(outside_involution_iff n hn3 i).2 hp]
      omega
    · rw [(outside_order_four_iff n hn3 i).2 (by omega)]
      omega
  · intro x hx
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective x
    change element n hn3 i e ∉ rotationSubgroup n at hx
    rw [element_mem_rotationSubgroup_iff n hn3] at hx
    have he : e = 1 := by
      rcases exponent_cases e with h | h
      · exact absurd h hx
      · exact h
    subst he
    change element n hn3 i 1 * r n ^ (2 ^ (n - 3)) * (element n hn3 i 1)⁻¹ = (r n ^ (2 ^ (n - 3)))⁻¹
    have hv : (1 : ZMod 2).val = 1 := rfl
    have hx : element n hn3 i 1 = r n ^ i.val * s n := by
      rw [element_eq, hv, pow_one]
    rw [hx]
    have hc : Commute (r n ^ i.val) (r n ^ (2 ^ (n - 3)))⁻¹ :=
      (Commute.pow_pow_self (r n) i.val (2 ^ (n - 3))).inv_right
    calc (r n ^ i.val * s n) * r n ^ (2 ^ (n - 3)) * (r n ^ i.val * s n)⁻¹
        = r n ^ i.val * (s n * r n ^ (2 ^ (n - 3)) * (s n)⁻¹) * (r n ^ i.val)⁻¹ := by group
      _ = r n ^ i.val * (r n ^ (2 ^ (n - 3)))⁻¹ * (r n ^ i.val)⁻¹ := by rw [hsd.2]
      _ = (r n ^ (2 ^ (n - 3)))⁻¹ := by rw [hc.eq]; group

end Semidihedral


section Eight

variable {M : Type} [Group M] [Finite M]

theorem dsdData_of_card_eight (hcard : Nat.card M = 8) (hnab : ¬ ∀ a b : M, a * b = b * a)
    {E : Subgroup M} (hE : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 4) : DSDData M := by
  classical
  have hcyc_comm : ∀ x : M, orderOf x = 8 → False := by
    intro x hx
    have hc : IsCyclic M := isCyclic_of_orderOf_eq_card x (by rw [hx, hcard])
    exact hnab fun a b => (hc.isMulCommutative).is_comm.comm a b
  obtain ⟨a, ha4⟩ : ∃ a : M, orderOf a = 4 := by
    by_contra hno
    push Not at hno
    apply hnab
    have hord : ∀ x : M, x * x = 1 := by
      intro x
      have hdvd : orderOf x ∣ 2 ^ 3 := by
        have := orderOf_dvd_natCard x
        rw [hcard] at this
        simpa using this
      obtain ⟨i, hi, hxi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      interval_cases i
      · have : x = 1 := orderOf_eq_one_iff.1 (by simpa using hxi)
        rw [this, one_mul]
      · have h2 : orderOf x = 2 := by simpa using hxi
        have h1 := pow_orderOf_eq_one x
        rw [h2, pow_two] at h1
        exact h1
      · exact absurd (by simpa using hxi) (hno x)
      · exact (hcyc_comm x (by simpa using hxi)).elim
    intro a b
    exact B.comm_of_forall_sq (E := ⊤) (fun a _ => hord a) (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hAcyc : IsCyclic ↥(zpowers a) := inferInstance
  have hAcard : Nat.card (zpowers a) = 4 := by rw [Nat.card_zpowers, ha4]
  have hAidx : (zpowers a).index = 2 := by
    have := (zpowers a).card_mul_index
    rw [hAcard, hcard] at this
    omega
  have hAnorm : (zpowers a).Normal := Subgroup.normal_of_index_eq_two hAidx
  have haA : a ∈ zpowers a := Subgroup.mem_zpowers a
  have hAc : ∀ x ∈ zpowers a, ∀ y ∈ zpowers a, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((hAcyc.isMulCommutative).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨b, hbE, hbA, hb1⟩ : ∃ b ∈ E, b ∉ zpowers a ∧ b ≠ 1 := by
    by_contra hno
    push Not at hno
    have hEA : E ≤ zpowers a := by
      intro x hx
      by_cases hxA : x ∈ zpowers a
      · exact hxA
      · rw [hno x hx hxA]
        exact Subgroup.one_mem _
    have hEeq : E = zpowers a := Subgroup.eq_of_le_of_card_ge hEA (by rw [hEc, hAcard])
    have haE : a ∈ E := hEeq ▸ haA
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hE a haE)
    rw [ha4] at h2
    omega
  have hb2 : b * b = 1 := hE b hbE
  have hdec : ∀ x : M, x ∈ zpowers a ∨ x * b⁻¹ ∈ zpowers a := by
    intro x
    have hidx : (zpowers a).relIndex ⊤ ≤ 2 := by
      rw [Subgroup.relIndex_top_right, hAidx]
    exact B.mem_or_mul_inv_mem hidx (Subgroup.mem_top b) hbA (Subgroup.mem_top x)
  have hconj_mem : b * a * b⁻¹ ∈ zpowers a := hAnorm.conj_mem a haA b
  have hconj4 : orderOf (b * a * b⁻¹) = 4 := by
    have := orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective a
    simpa [MulAut.conj_apply, ha4] using this
  have hbA_zpow : ∀ k : ℤ, b * a ^ k * b⁻¹ = (b * a * b⁻¹) ^ k := by
    intro k
    exact conj_zpow.symm
  have hdec' : ∀ x : M, x ∉ zpowers a → x * b⁻¹ ∈ zpowers a := fun x hx =>
    (hdec x).resolve_left hx
  rcases eq_or_inv_of_orderOf_four hAcyc haA hconj_mem ha4 hconj4 with hcomm | hinvb
  ·
    exfalso
    apply hnab
    have hba : b * a = a * b := by
      have := hcomm
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hbc : ∀ x ∈ zpowers a, b * x = x * b := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((show Commute b a from hba).zpow_right k).eq
    have hx_dec : ∀ x : M, x ∈ zpowers a ∨ ∃ α ∈ zpowers a, x = α * b := by
      intro x
      rcases hdec x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨x * b⁻¹, h, by group⟩
    intro x y
    rcases hx_dec x with hx | ⟨α, hα, rfl⟩ <;> rcases hx_dec y with hy | ⟨β, hβ, rfl⟩
    · exact hAc x hx y hy
    · calc x * (β * b) = (x * β) * b := by group
        _ = (β * x) * b := by rw [hAc x hx β hβ]
        _ = β * (x * b) := by group
        _ = β * (b * x) := by rw [← hbc x hx]
        _ = β * b * x := by group
    · calc α * b * y = α * (b * y) := by group
        _ = α * (y * b) := by rw [hbc y hy]
        _ = (α * y) * b := by group
        _ = (y * α) * b := by rw [hAc α hα y hy]
        _ = y * (α * b) := by group
    · calc α * b * (β * b) = α * (b * β) * b := by group
        _ = α * (β * b) * b := by rw [hbc β hβ]
        _ = (α * β) * (b * b) := by group
        _ = (β * α) * (b * b) := by rw [hAc α hα β hβ]
        _ = β * (α * b) * b := by group
        _ = β * (b * α) * b := by rw [← hbc α hα]
        _ = β * b * (α * b) := by group
  ·
    have hbα : ∀ α ∈ zpowers a, b * α * b⁻¹ = α⁻¹ := by
      intro α hα
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hα
      rw [hbA_zpow, hinvb, inv_zpow]
    refine ⟨zpowers a, a, hAcyc, haA, ha4, ?_, ?_⟩
    · intro x hx
      have hα := hdec' x hx
      have hxx : x * x = 1 := by
        have h1 := hbα (x * b⁻¹) hα
        calc x * x = (x * b⁻¹) * (b * (x * b⁻¹) * b⁻¹) * (b * b) := by group
          _ = (x * b⁻¹) * (x * b⁻¹)⁻¹ * (b * b) := by rw [h1]
          _ = 1 := by rw [hb2]; group
      have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
      have h3 : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      rw [hAcard]
      omega
    · intro x hx
      have hα := hdec' x hx
      calc x * a * x⁻¹ = (x * b⁻¹) * (b * a * b⁻¹) * (x * b⁻¹)⁻¹ := by group
        _ = (x * b⁻¹) * a⁻¹ * (x * b⁻¹)⁻¹ := by rw [hinvb]
        _ = a⁻¹ := by
          have hc := hAc (x * b⁻¹) hα a⁻¹ (Subgroup.inv_mem _ haA)
          rw [hc]
          group

end Eight


section MaxClass

open CFSG.GH74.GLS

theorem exists_four_of_pRank {R : Type} [Group R] [Finite R] (h2 : 2 ≤ CFSG.pRank 2 R) :
    ∃ E : Subgroup R, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 4 := by
  obtain ⟨E, hE, hEc⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  exact ⟨E, fun x hx => by simpa [pow_two] using hE.2 x hx, hEc⟩

theorem dsdData_of_maxClass {P : Type} [Group P] [Finite P] (hmax : IsNonabelianMaximalClassTwoGroup P)
    (h4 : ∃ E : Subgroup P, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 4) : DSDData P := by
  obtain ⟨hp, hnab, hnil, hcard⟩ := hmax
  obtain ⟨E, hE, hEc⟩ := h4
  have hnab' : ¬ ∀ a b : P, a * b = b * a := fun h => hnab ⟨⟨h⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Group.nilpotencyClass P := ⟨_, rfl⟩
  rw [← hc] at hcard
  have hm3 : 3 ≤ c + 1 := by
    by_contra hlt
    push Not at hlt
    apply hnab'
    have hc2 : c = 0 ∨ c = 1 := by omega
    rcases hc2 with h0 | h1
    · have h : Nat.card P = 2 := by rw [hcard, h0]; norm_num
      have hcy : IsCyclic P := isCyclic_of_prime_card (p := 2) h
      intro a b
      exact (hcy.isMulCommutative).is_comm.comm a b
    · have h : Nat.card P = 2 ^ 2 := by rw [hcard, h1]
      intro a b
      exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq h).is_comm.comm a b
  have hlcs : (⊤ : Subgroup P).lowerCentralSeries ((c + 1) - 2) ≠ ⊥ := by
    intro hbot
    have := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := P)).1 hbot
    omega
  by_cases h8 : Nat.card P = 8
  · exact dsdData_of_card_eight h8 hnab' hE hEc
  · have h8' : 8 < Nat.card P := by
      have : 2 ^ 3 ≤ 2 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) hm3
      omega
    rcases CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape P hp h8' (c + 1) hcard hlcs with
      ⟨k, hk, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have hNk : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
      have hcd : Nat.card P = 2 * 2 ^ k := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hk3 : 2 ≤ k := by
        by_contra hlt
        push Not at hlt
        have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h4 : 4 ∣ 2 ^ k := by
        have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk3
        simpa using this
      exact DSDData.congr e.symm (dsdData_dihedral (2 ^ k) h4)
    · exfalso
      have hNk : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
      have hfin : Finite ↥E := inferInstance
      obtain ⟨v, hv, w, hw, hv1, hw1, hvw⟩ :=
        exists_two_ne_one_aux (E := E) (by rw [hEc]; norm_num)
      have hq : ∀ x ∈ E, x ≠ 1 → e x = QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
        intro x hx hx1
        have h1 : e x * e x = 1 := by
          rw [← map_mul, hE x hx, map_one]
        rcases B.quat_invol (e x) h1 with h | h
        · exact absurd (e.injective (h.trans (map_one e).symm)) hx1
        · exact h
      exact hvw (e.injective ((hq v hv hv1).trans (hq w hw hw1).symm))
    · exact DSDData.congr e.symm (dsdData_semidihedral n hn)

end MaxClass

end CFSG.GH74.GLS.IVK.Lifted

module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeBasic

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem commutator_eq_top_of_simple (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer] at h
    exact hxy (mem_centralizer_iff.1 (h (mem_top y)) x (mem_top x))
  · exact h

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem a_mem_U : a ∈ U := hS.rad.Q_le_U hS.rad.a_mem_Q

theorem a_mem_L : a ∈ L := hS.U_le_L hS.a_mem_U

theorem a_central_U [Finite G] {x : G} (hx : x ∈ U) : a * x = x * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial U :=
    ⟨⟨⟨a, hS.a_mem_U⟩, 1, fun h => hS.rad.a_ne_one (congrArg Subtype.val h)⟩⟩
  have hnt := hS.rad.U_pgroup.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center U)
  have hzc : ∀ y ∈ U, ((z : U) : G) * y = y * (z : U) := fun y hy => by
    have := mem_center_iff.1 z.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  rcases hS.rad.center_U _ (z : U).2 hzc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hz
  · rw [← h]
    exact hzc x hx

theorem eq_of_commute {z : G} (hzt : z * t = t * z) (hzU : ∀ x ∈ U, z * x = x * z) :
    z = 1 ∨ z = a ∨ z = t ∨ z = t * a := by
  have hzE : z ∈ Q ⊔ zpowers t := hS.data.centralizer_Q
    ⟨mem_centralizer_singleton_iff.2 hzt, mem_centralizer_iff.2 fun x hx =>
      (hzU x (hS.rad.Q_le_U hx)).symm⟩
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hzE
  · rcases hS.rad.center_U _ (hS.rad.Q_le_U (hS.rad.ψ_mem v)) hzU with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hv : ∀ x ∈ U, ψ v * x = x * ψ v := by
      intro x hx
      have h1 := hzU x hx
      have h2 : x * t = t * x := hS.shape.commute_of_mem (hS.U_le_L hx)
      apply mul_left_cancel (a := t)
      calc t * (ψ v * x) = t * ψ v * x := by group
        _ = x * (t * ψ v) := h1
        _ = x * t * ψ v := by group
        _ = t * (x * ψ v) := by rw [h2]; group
    rcases hS.rad.center_U _ (hS.rad.Q_le_U (hS.rad.ψ_mem v)) hv with h | h
    · rw [h, mul_one]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h]
      exact Or.inr (Or.inr (Or.inr rfl))

theorem c_comm_a [Finite G] : c * a = a * c := by
  have hm : c * a * c⁻¹ ∈ U := hS.c_conj_mem_U hS.a_mem_U
  have hcen : ∀ x ∈ U, c * a * c⁻¹ * x = x * (c * a * c⁻¹) := by
    intro x hx
    have hx' : c⁻¹ * x * c ∈ U := by simpa using hS.c_inv_conj_mem_U hx
    have h := hS.a_central_U hx'
    calc c * a * c⁻¹ * x = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * a) * c⁻¹ := by rw [h]
      _ = x * (c * a * c⁻¹) := by group
  rcases hS.rad.center_U _ hm hcen with h | h
  · exfalso
    apply hS.rad.a_ne_one
    have : a = c⁻¹ * (c * a * c⁻¹) * c := by group
    rw [this, h]
    group
  · calc c * a = c * a * c⁻¹ * c := by group
      _ = a * c := by rw [h]

theorem a_comm_TH [Finite G] {x : G} (hx : x ∈ U ⊔ zpowers c) : a * x = x * a := by
  have hat : Commute a t := (hS.shape.commute_of_mem hS.a_mem_L)
  have hac : Commute a c := (hS.c_comm_a).symm
  obtain ⟨u, hu, rfl | rfl | rfl | rfl⟩ := hS.mem_TH_iff.1 hx
  · exact hS.a_central_U hu
  · exact ((show Commute a u from hS.a_central_U hu).mul_right hac).eq
  · exact ((show Commute a u from hS.a_central_U hu).mul_right hat).eq
  · exact ((show Commute a u from hS.a_central_U hu).mul_right (hac.mul_right hat)).eq

omit hS in
theorem t_mem_K : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)

theorem mul_self_ne_conj {x g : G} (hx : x ∈ U ⊔ zpowers t) : x * x ≠ g * t * g⁻¹ := by
  intro h
  have := hS.mul_self_mem_U hx
  rw [h] at this
  exact hS.shape.conj_not_mem hS.rad.odd g (hS.U_le_L this)

theorem inv_mul_mem_K {x : G} (hx : x ∈ U ⊔ zpowers c) (hxK : x ∉ U ⊔ zpowers t) :
    c⁻¹ * x ∈ U ⊔ zpowers t ∧ (c * t)⁻¹ * x ∈ U ⊔ zpowers t := by
  have htK : t ∈ U ⊔ zpowers t := t_mem_K
  obtain ⟨u, hu, rfl | rfl | rfl | rfl⟩ := hS.mem_TH_iff.1 hx
  · exact absurd (mem_sup_left hu) hxK
  · have h1 : c⁻¹ * u * c ∈ U := by simpa using hS.c_inv_conj_mem_U hu
    refine ⟨?_, ?_⟩
    · rw [← mul_assoc]; exact mem_sup_left h1
    · rw [show (c * t)⁻¹ * (u * c) = t⁻¹ * (c⁻¹ * u * c) by group]
      exact mul_mem (inv_mem htK) (mem_sup_left h1)
  · exact absurd (mul_mem (mem_sup_left hu) htK) hxK
  · have h1 : c⁻¹ * u * c ∈ U := by simpa using hS.c_inv_conj_mem_U hu
    refine ⟨?_, ?_⟩
    · rw [show c⁻¹ * (u * (c * t)) = c⁻¹ * u * c * t by group]
      exact mul_mem (mem_sup_left h1) htK
    · rw [show (c * t)⁻¹ * (u * (c * t)) = t⁻¹ * (c⁻¹ * u * c) * t by group]
      exact mul_mem (mul_mem (inv_mem htK) (mem_sup_left h1)) htK

theorem c_t_mul_c_t : c * t * (c * t) = t := by
  calc c * t * (c * t) = c * (t * c) * t := by group
    _ = c * (c * t) * t := by rw [hS.shape.c_comm]
    _ = (c * c) * (t * t) := by group
    _ = t := by rw [hS.shape.sq, hS.shape.mul_self, mul_one]

theorem TH_ne_sylow [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : Sylow 2 G) : (S : Subgroup G) ≠ U ⊔ zpowers c := by
  intro hSTH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : Nat.Coprime 2 (U ⊔ zpowers c : Subgroup G).index := by
    rw [← hSTH]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 S.not_dvd_index
  have hrel := hS.relIndex_K_TH
  have hmain := generalized_thompson_transfer_one (p := 2) (H := U ⊔ zpowers c)
    (K := U ⊔ zpowers t) hindex ⟨hS.K_le_TH, normal_subgroupOf_of_relIndex_eq_two hrel⟩
    (commutator_le_of_relIndex_eq_two hrel) (g := c) c_mem_TH hS.c_not_mem_K
    ⟨2, by norm_num [hS.shape.c_pow_four]⟩ (by
      intro m b hb
      rcases hS.mem_zpowers_c.1 (zpow_mem (mem_zpowers c) m) with h | h | h | h <;>
        rw [h] at hb ⊢
      · simp
      · have hxK : b⁻¹ * c * b ∉ U ⊔ zpowers t := fun hK => hS.mul_self_ne_conj (g := b⁻¹) hK
          (by rw [inv_inv, show b⁻¹ * c * b * (b⁻¹ * c * b) = b⁻¹ * (c * c) * b by group,
            hS.shape.sq])
        exact (hS.inv_mul_mem_K hb hxK).1
      · have hx2 : b⁻¹ * t * b * (b⁻¹ * t * b) = 1 := by
          rw [show b⁻¹ * t * b * (b⁻¹ * t * b) = b⁻¹ * (t * t) * b by group, hS.shape.mul_self]
          group
        exact mul_mem (inv_mem t_mem_K) (hS.mem_K_of_mul_self hb hx2)
      · have hxK : b⁻¹ * (c * t) * b ∉ U ⊔ zpowers t := fun hK =>
          hS.mul_self_ne_conj (g := b⁻¹) hK (by
            rw [inv_inv, show b⁻¹ * (c * t) * b * (b⁻¹ * (c * t) * b) =
              b⁻¹ * (c * t * (c * t)) * b by group, hS.c_t_mul_c_t])
        exact (hS.inv_mul_mem_K hb hxK).2)
  rw [commutator_eq_top_of_simple hG hnab] at hmain
  exact hmain (mem_top c)

omit hS in
theorem conj_central {T : Subgroup G} {n z : G} (hn : n ∈ normalizer (T : Set G))
    (hz : ∀ x ∈ T, z * x = x * z) {x : G} (hx : x ∈ T) : n * z * n⁻¹ * x = x * (n * z * n⁻¹) := by
  have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ T := (mem_normalizer_iff.1 (inv_mem hn) x).1 hx
  rw [inv_inv] at hx'
  have h := hz _ hx'
  calc n * z * n⁻¹ * x = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by rw [h]
    _ = x * (n * z * n⁻¹) := by group

theorem exists_conj_eq_mul [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) :
    ∃ n ∈ normalizer ((U ⊔ zpowers c : Subgroup G) : Set G),
      n * t * n⁻¹ = t * a ∧ n * a * n⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS'⟩ := hS.isPGroup_TH.exists_le_sylow
  have hlt : U ⊔ zpowers c < S := lt_of_le_of_ne hS' (fun h => hS.TH_ne_sylow hG hnab S h.symm)
  obtain ⟨n, hnS, hnN, hnTH⟩ := exists_mem_normalizer_not_mem S.isPGroup' hlt
  have hnt : n * t ≠ t * n := by
    intro hnt
    have hVS : U ⊔ zpowers c ⊔ zpowers n ≤ S := sup_le hS' (zpowers_le.2 hnS)
    have hV := hS.data.sylow (U ⊔ zpowers c ⊔ zpowers n)
      (sup_le hS.TH_le_centralizer (zpowers_le.2 (mem_centralizer_singleton_iff.2 hnt)))
      (S.isPGroup'.to_le hVS) le_sup_left
    exact hnTH (hV ▸ mem_sup_right (mem_zpowers n))
  have htc : ∀ x ∈ U ⊔ zpowers c, t * x = x * t := fun x hx =>
    (mem_centralizer_singleton_iff.1 (hS.TH_le_centralizer hx)).symm
  have hcen : ∀ z, (∀ x ∈ U ⊔ zpowers c, z * x = x * z) →
      n * z * n⁻¹ = 1 ∨ n * z * n⁻¹ = a ∨ n * z * n⁻¹ = t ∨ n * z * n⁻¹ = t * a := by
    intro z hz
    have h := fun x hx => conj_central hnN hz (x := x) hx
    exact hS.eq_of_commute (h t hS.t_mem_TH) fun x hx => h x (mem_sup_left hx)
  have hT1 := hS.shape.conj_not_mem hS.rad.odd
  have hta : n * t * n⁻¹ = t * a := by
    rcases hcen t htc with h | h | h | h
    · exact absurd (conj_eq_one_iff.1 h) hS.shape.ne_one
    · exact absurd (h ▸ hS.a_mem_L) (hT1 n)
    · exact absurd (by calc n * t = n * t * n⁻¹ * n := by group
          _ = t * n := by rw [h]) hnt
    · exact h
  refine ⟨n, hnN, hta, ?_⟩
  rcases hcen a (fun x hx => hS.a_comm_TH hx) with h | h | h | h
  · exact absurd (conj_eq_one_iff.1 h) hS.rad.a_ne_one
  · exact h
  · exfalso
    apply hT1 n⁻¹
    rw [inv_inv, ← h, show n⁻¹ * (n * a * n⁻¹) * n = a by group]
    exact hS.a_mem_L
  · exfalso
    apply hS.shape.not_mem
    have : a = t := by
      have h2 : n * a * n⁻¹ = n * t * n⁻¹ := by rw [h, hta]
      simpa using h2
    exact this ▸ hS.a_mem_L

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime

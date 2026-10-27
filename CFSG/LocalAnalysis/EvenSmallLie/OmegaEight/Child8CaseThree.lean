module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8CaseOne

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup CFSG.Quasithin

structure CaseThreeData (X : Type) [Group X] [Finite X] extends CaseOneData X where
  α : MulAut X
  α_α : ∀ x, α (α x) = x
  α_T : ∀ t ∈ T, α t ∈ T
  α_F : ∀ v, α (ιF v) = ιF v
  outer_E : ∀ t : X, ¬ ∀ v, t * α (ιE v) * t⁻¹ = ιE v
  outer_F : ∀ t : X, (∀ v, t * α (ιF v) * t⁻¹ = ιF v) → t ∈ ιF.range
  centralizer_E : ∀ t : X, (∀ v, t * ιE v = ιE v * t) → t ∈ ιE.range
  mul_ne : ∀ t : X, t * α t ≠ z

section ExtTwo

variable {G : Type*} [Group G]

@[expose] def extTwo (K : Subgroup G) (c : G) (hn : ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hc2 : c * c ∈ K) : Subgroup G where
  carrier := {g | g ∈ K ∨ g * c⁻¹ ∈ K}
  mul_mem' {a b} ha hb := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (mul_mem ha hb)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact mul_mem ha hb
    · refine Or.inr ?_
      have e : a * b * c⁻¹ = a * c⁻¹ * (c * b * c⁻¹) := by group
      rw [e]
      exact mul_mem ha (hn b hb)
    · refine Or.inl ?_
      have e : a * b = a * c⁻¹ * (c * (b * c⁻¹) * c⁻¹) * (c * c) := by group
      rw [e]
      exact mul_mem (mul_mem ha (hn _ hb)) hc2
  one_mem' := Or.inl K.one_mem
  inv_mem' {a} ha := by
    rcases ha with ha | ha
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have e : a⁻¹ * c⁻¹ = (c * (a * c⁻¹) * c⁻¹ * (c * c))⁻¹ := by group
      rw [e]
      exact inv_mem (mul_mem (hn _ ha) hc2)

variable {K : Subgroup G} {c : G} {hn : ∀ k ∈ K, c * k * c⁻¹ ∈ K} {hc2 : c * c ∈ K}

theorem le_extTwo : K ≤ extTwo K c hn hc2 := fun _ hg => Or.inl hg

theorem mem_extTwo_self : c ∈ extTwo K c hn hc2 :=
  Or.inr (by rw [mul_inv_cancel]; exact K.one_mem)

end ExtTwo

namespace CaseThreeData

variable {X : Type} [Group X] [Finite X] (D : CaseThreeData X)
variable {G : Type} [Group G] {ψ : X →* G} {c : G}

theorem mul_self_ne (hψ : Function.Injective ψ) (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x))
    (hcc : c * c = ψ D.z) {g : G} (hg : g * c⁻¹ ∈ ψ.range) : g * g ≠ 1 := by
  obtain ⟨x, hx⟩ := hg
  have hg' : g = ψ x * c := by rw [hx]; group
  intro h
  apply D.mul_ne x
  have h1 : ψ (x * D.α x * D.z) = 1 := by
    rw [map_mul, map_mul, ← hc x, ← hcc, ← h, hg']
    group
  have h2 : x * D.α x * D.z = 1 := hψ (h1.trans (map_one ψ).symm)
  calc x * D.α x = x * D.α x * D.z * D.z := by rw [mul_assoc _ D.z, D.z_mul_self, mul_one]
    _ = D.z := by rw [h2, one_mul]

theorem conj_mem_T (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x)) {k : G} (hk : k ∈ D.T.map ψ) :
    c * k * c⁻¹ ∈ D.T.map ψ := by
  obtain ⟨t, ht, rfl⟩ := hk
  rw [hc]
  exact mem_map_of_mem ψ (D.α_T t ht)

theorem conj_mem_F (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x)) {k : G}
    (hk : k ∈ (ψ.comp D.ιF).range) : c * k * c⁻¹ ∈ (ψ.comp D.ιF).range := by
  obtain ⟨v, rfl⟩ := hk
  rw [MonoidHom.comp_apply, hc, D.α_F]
  exact ⟨v, rfl⟩

theorem zG_mem_T : ψ D.z ∈ D.T.map ψ := mem_map_of_mem ψ D.z_mem_T

theorem zG_mem_F : ψ D.z ∈ (ψ.comp D.ιF).range := ⟨_, D.ψιF_evenZ⟩

@[expose] def SG (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x)) (hcc : c * c = ψ D.z) : Subgroup G :=
  extTwo (D.T.map ψ) c (fun _ hk => D.conj_mem_T hc hk) (hcc ▸ D.zG_mem_T)

@[expose] def E2 (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x)) (hcc : c * c = ψ D.z) : Subgroup G :=
  extTwo (ψ.comp D.ιF).range c (fun _ hk => D.conj_mem_F hc hk) (hcc ▸ D.zG_mem_F)

variable (hc : ∀ x, c * ψ x * c⁻¹ = ψ (D.α x)) (hcc : c * c = ψ D.z)

include hc hcc

omit hcc in
theorem c_comm_F {f : G} (hf : f ∈ (ψ.comp D.ιF).range) : c * f = f * c := by
  obtain ⟨v, rfl⟩ := hf
  rw [MonoidHom.comp_apply]
  have h := hc (D.ιF v)
  rw [D.α_F] at h
  calc c * ψ (D.ιF v) = c * ψ (D.ιF v) * c⁻¹ * c := by group
    _ = ψ (D.ιF v) * c := by rw [h]

theorem E2_le_SG : D.E2 hc hcc ≤ D.SG hc hcc := by
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl (D.F_le_TG hg)
  · exact Or.inr (D.F_le_TG hg)

theorem E2_comm {a b : G} (ha : a ∈ D.E2 hc hcc) (hb : b ∈ D.E2 hc hcc) : a * b = b * a := by
  have key : ∀ f ∈ (ψ.comp D.ιF).range, ∀ g ∈ (ψ.comp D.ιF).range, f * g = g * f :=
    fun f hf g hg => comm_of_mem_range hf hg
  have hcF := fun {f : G} (hf : f ∈ (ψ.comp D.ιF).range) => D.c_comm_F hc hf
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact key _ ha _ hb
  · calc a * b = a * (b * c⁻¹) * c := by group
      _ = b * c⁻¹ * a * c := by rw [key _ ha _ hb]
      _ = b * c⁻¹ * (a * c) := by group
      _ = b * c⁻¹ * (c * a) := by rw [hcF ha]
      _ = b * a := by group
  · calc a * b = a * c⁻¹ * (c * b) := by group
      _ = a * c⁻¹ * (b * c) := by rw [hcF hb]
      _ = a * c⁻¹ * b * c := by group
      _ = b * (a * c⁻¹) * c := by rw [key _ ha _ hb]
      _ = b * a := by group
  · calc a * b = a * c⁻¹ * (c * (b * c⁻¹)) * c := by group
      _ = a * c⁻¹ * (b * c⁻¹ * c) * c := by rw [hcF hb]
      _ = a * c⁻¹ * (b * c⁻¹) * (c * c) := by group
      _ = b * c⁻¹ * (a * c⁻¹) * (c * c) := by rw [key _ ha _ hb]
      _ = b * c⁻¹ * (a * c⁻¹ * c) * c := by group
      _ = b * c⁻¹ * (c * (a * c⁻¹)) * c := by rw [hcF ha]
      _ = b * a := by group

theorem E2_sq {a : G} (ha : a ∈ D.E2 hc hcc) : a * a = 1 ∨ a * a = ψ D.z := by
  rcases ha with ha | ha
  · exact Or.inl (mul_self_of_mem_range ha)
  · right
    calc a * a = a * c⁻¹ * (c * (a * c⁻¹)) * c := by group
      _ = a * c⁻¹ * (a * c⁻¹ * c) * c := by rw [D.c_comm_F hc ha]
      _ = a * c⁻¹ * (a * c⁻¹) * (c * c) := by group
      _ = ψ D.z := by rw [mul_self_of_mem_range ha, one_mul, hcc]

variable (hψ : Function.Injective ψ)
  (hH : ∀ g : G, g * ψ D.z = ψ D.z * g ↔ g ∈ ψ.range ∨ g * c⁻¹ ∈ ψ.range)

include hH in
theorem SG_comm_z {g : G} (hg : g ∈ D.SG hc hcc) : g * ψ D.z = ψ D.z * g := by
  rcases hg with hg | hg
  · exact (hH g).2 (Or.inl (map_le_range ψ D.T hg))
  · exact (hH g).2 (Or.inr (map_le_range ψ D.T hg))

include hψ in
theorem pow_SG [Finite G] {g : G} (hg : g ∈ D.SG hc hcc) : g ^ 2 ^ 14 = 1 := by
  have hT : ∀ k ∈ D.T.map ψ, k ^ 2 ^ 13 = 1 := fun k hk => by
    have h := pow_card_eq_one' (x := (⟨k, hk⟩ : D.T.map ψ))
    rw [card_map_of_injective hψ, D.card_T] at h
    exact congrArg Subtype.val h
  rw [show 2 ^ 14 = 2 * 2 ^ 13 by norm_num, pow_mul]
  rcases hg with hg | hg
  · rw [← pow_mul, mul_comm, pow_mul, hT g hg, one_pow]
  · apply hT
    have e : g ^ 2 = g * c⁻¹ * (c * (g * c⁻¹) * c⁻¹) * (c * c) := by rw [pow_two]; group
    rw [e, hcc]
    exact mul_mem (mul_mem hg (D.conj_mem_T hc hg)) D.zG_mem_T

include hψ in
theorem isPGroup_SG [Finite G] : IsPGroup 2 (D.SG hc hcc) := fun g =>
  ⟨14, Subtype.ext (by rw [SubgroupClass.coe_pow]; exact D.pow_SG hc hcc hψ g.2)⟩

include hψ hH in
theorem SG_max [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hSQ : D.SG hc hcc ≤ Q)
    (hQH : Q ≤ centralizer ({ψ D.z} : Set G)) : Q = D.SG hc hcc := by
  have hTQ : D.T.map ψ ≤ Q ⊓ ψ.range :=
    le_inf ((le_extTwo).trans hSQ) (map_le_range ψ D.T)
  have hQT : Q ⊓ ψ.range = D.T.map ψ :=
    eq_of_card_of_le (by rw [card_map_of_injective hψ, D.card_T])
      (by rw [card_range_of_injective hψ, D.card_X]) (by decide) (hQ.to_inf_left) hTQ
      inf_le_right
  have hcS : c ∈ D.SG hc hcc := Or.inr (by rw [mul_inv_cancel]; exact one_mem _)
  refine le_antisymm (fun q hq => ?_) hSQ
  rcases (hH q).1 (mem_centralizer_singleton_iff.1 (hQH hq)) with h | h
  · exact Or.inl (hQT ▸ ⟨hq, h⟩)
  · exact Or.inr (hQT ▸ ⟨Q.mul_mem hq (Q.inv_mem (hSQ hcS)), h⟩)

include hψ in
theorem SG_center {g : G} (hg : g ∈ D.SG hc hcc) (hcent : ∀ u ∈ D.SG hc hcc, g * u = u * g) :
    g = 1 ∨ g = ψ D.z := by
  rcases hg with hg | hg
  · exact D.center_TG hψ hg fun u hu => hcent u (Or.inl hu)
  · exfalso
    obtain ⟨t, -, ht⟩ := hg
    apply D.outer_E t
    intro v
    apply hψ
    have h1 := hcent (ψ (D.ιE v)) (Or.inl (D.E_le_TG ⟨v, rfl⟩))
    have hg' : g = ψ t * c := by rw [ht]; group
    rw [hg'] at h1
    rw [map_mul, map_mul, map_inv, ← hc]
    calc ψ t * (c * ψ (D.ιE v) * c⁻¹) * (ψ t)⁻¹ =
          ψ t * c * ψ (D.ιE v) * (ψ t * c)⁻¹ := by group
      _ = ψ (D.ιE v) := by rw [h1]; group

include hψ hH in
theorem exists_sylow_SG [Finite G] : ∃ P : Sylow 2 G, (P : Subgroup G) = D.SG hc hcc := by
  refine exists_sylow_eq_of_normalizer_le (H := centralizer ({ψ D.z} : Set G))
    (D.isPGroup_SG hc hcc hψ) (fun Q hQ hSQ hQH => D.SG_max hc hcc hψ hH hQ hSQ hQH) ?_
  intro n hn
  rw [mem_centralizer_singleton_iff]
  exact comm_of_mem_normalizer (Or.inl D.zG_mem_T)
    (fun t ht => D.SG_comm_z hc hcc hH ht) (fun t ht hct => D.SG_center hc hcc hψ ht hct)
    (D.zG_ne_one hψ) hn

include hψ in
theorem mem_E_of_comm {u : G} (hu : u ∈ D.SG hc hcc)
    (hcomm : ∀ v, u * ψ (D.ιE v) = ψ (D.ιE v) * u) : u ∈ (ψ.comp D.ιE).range := by
  rcases hu with hu | hu
  · obtain ⟨t, -, rfl⟩ := hu
    obtain ⟨e, he⟩ := D.centralizer_E t fun v => hψ (by rw [map_mul, map_mul, hcomm v])
    exact ⟨e, by rw [MonoidHom.comp_apply, he]⟩
  · exfalso
    obtain ⟨t, -, ht⟩ := hu
    apply D.outer_E t
    intro v
    apply hψ
    have hu' : u = ψ t * c := by rw [ht]; group
    rw [map_mul, map_mul, map_inv, ← hc]
    calc ψ t * (c * ψ (D.ιE v) * c⁻¹) * (ψ t)⁻¹ = u * ψ (D.ιE v) * u⁻¹ := by rw [hu']; group
      _ = ψ (D.ιE v) := by rw [hcomm v]; group

include hψ in
theorem mem_E2_of_comm {u : G} (hu : u ∈ D.SG hc hcc)
    (hcomm : ∀ v, u * ψ (D.ιF v) = ψ (D.ιF v) * u) : u ∈ D.E2 hc hcc := by
  rcases hu with hu | hu
  · left
    obtain ⟨t, -, rfl⟩ := hu
    obtain ⟨e, he⟩ := D.outer_F t fun v => hψ (by
      rw [D.α_F, map_mul, map_mul, map_inv, hcomm v]
      group)
    exact ⟨e, by rw [MonoidHom.comp_apply, he]⟩
  · right
    obtain ⟨t, -, ht⟩ := hu
    have hu' : u = ψ t * c := by rw [ht]; group
    obtain ⟨e, he⟩ := D.outer_F t fun v => hψ (by
      rw [map_mul, map_mul, map_inv, ← hc]
      calc ψ t * (c * ψ (D.ιF v) * c⁻¹) * (ψ t)⁻¹ = u * ψ (D.ιF v) * u⁻¹ := by rw [hu']; group
        _ = ψ (D.ιF v) := by rw [hcomm v]; group)
    exact ⟨e, by rw [MonoidHom.comp_apply, he, ← ht]⟩

include hψ in
theorem wc_E2 [Finite G] (hcR : c ∉ ψ.range) : IsWeaklyClosedIn (D.E2 hc hcc) (D.SG hc hcc) := by
  intro g hg
  set U := conjSubgroup (D.E2 hc hcc) g
  set B := conjSubgroup (ψ.comp D.ιF).range g
  have hBU : B ≤ U := map_mono le_extTwo
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [mem_conjSubgroup_iff] at hb
    have h1 := mul_self_of_mem_range hb
    calc b * b = g⁻¹ * (g * b * g⁻¹ * (g * b * g⁻¹)) * g := by group
      _ = 1 := by rw [h1]; group
  have hBT : B ≤ D.T.map ψ := fun b hb => by
    rcases hg (hBU hb) with h | h
    · exact h
    · exact absurd (hB2 b hb) (D.mul_self_ne hψ hc hcc (map_le_range ψ D.T h))
  have hBc : Nat.card B = 2 ^ 7 := by
    rw [card_conjSubgroup_eq, card_range_evenSub (ι := ψ.comp D.ιF) (hψ.comp D.ιF_injective)]
  have hUc : ∀ u ∈ U, ∀ b ∈ B, u * b = b * u := fun u hu b hb => by
    rw [mem_conjSubgroup_iff] at hu
    have h1 := D.E2_comm hc hcc hu (mem_conjSubgroup_iff.1 (hBU hb))
    calc u * b = g⁻¹ * (g * u * g⁻¹ * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * (g * u * g⁻¹)) * g := by rw [h1]
      _ = b * u := by group
  have hFE : Nat.card (ψ.comp D.ιF).range < Nat.card (D.E2 hc hcc) := by
    by_contra hle
    push Not at hle
    have h := eq_of_le_of_card_ge (le_extTwo (K := (ψ.comp D.ιF).range)) hle
    have hcE : c ∈ (ψ.comp D.ιF).range := by
      rw [h]
      exact mem_extTwo_self
    obtain ⟨v, hv⟩ := hcE
    exact hcR ⟨D.ιF v, hv⟩
  rcases D.elem_TG hψ hBT (fun b hb => by rw [pow_two]; exact hB2 b hb) hBc with h | h
  · exfalso
    have hUE : U ≤ (ψ.comp D.ιE).range := fun u hu => D.mem_E_of_comm hc hcc hψ (hg hu)
      fun v => hUc u hu _ (h ▸ ⟨v, rfl⟩)
    have h1 := card_le_of_le hUE
    rw [card_conjSubgroup_eq, card_range_evenSub (ι := ψ.comp D.ιE) (hψ.comp D.ιE_injective),
      ← card_range_evenSub (ι := ψ.comp D.ιF) (hψ.comp D.ιF_injective)] at h1
    omega
  · refine eq_of_le_of_card_ge (fun u hu => D.mem_E2_of_comm hc hcc hψ (hg hu)
      fun v => hUc u hu _ (h ▸ ⟨v, rfl⟩)) ?_
    rw [card_conjSubgroup_eq]

include hψ in
theorem normalizer_E2_fixes {n : G} (hn : n ∈ normalizer (D.E2 hc hcc : Set G)) :
    n * ψ D.z * n⁻¹ = ψ D.z := by
  have hcE : c ∈ D.E2 hc hcc := mem_extTwo_self
  have h1 := D.E2_sq hc hcc ((mem_normalizer_iff.1 hn c).1 hcE)
  have e : n * c * n⁻¹ * (n * c * n⁻¹) = n * ψ D.z * n⁻¹ := by rw [← hcc]; group
  rw [e] at h1
  rcases h1 with h1 | h1
  · exfalso
    apply D.zG_ne_one hψ
    calc ψ D.z = n⁻¹ * (n * ψ D.z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · exact h1

include hψ hH in
theorem false_of [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hcR : c ∉ ψ.range) : False := by
  obtain ⟨P, hP⟩ := D.exists_sylow_SG hc hcc hψ hH
  refine false_of_isolated_involution hnonab (D.orderOf_zG hψ) fun y hy hzy => ?_
  have hy2 : y * y = 1 := mul_self_of_isConj D.zG_mul_self hzy
  rcases (hH y).1 (mem_centralizer_singleton_iff.1 hy) with hyR | hyR
  swap
  · exact absurd hy2 (D.mul_self_ne hψ hc hcc hyR)
  obtain ⟨y', rfl⟩ := hyR
  have hy2' : y' * y' = 1 := hψ (by rw [map_mul, map_one]; exact hy2)
  obtain ⟨w, v, hv⟩ := D.inv y' hy2'
  have hx : ψ (D.ιF v) ∈ D.E2 hc hcc := Or.inl ⟨v, rfl⟩
  have hzx : IsConj (ψ D.z) (ψ (D.ιF v)) :=
    hzy.trans (isConj_iff.2 ⟨ψ w, by rw [hv, map_mul, map_mul, map_inv]⟩)
  obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_isWeaklyClosedIn P
    (hP ▸ D.E2_le_SG hc hcc) (fun _ ha _ hb => D.E2_comm hc hcc ha hb)
    (hP ▸ D.wc_E2 hc hcc hψ hcR) (Or.inl D.zG_mem_F) hx hzx
  rw [D.normalizer_E2_fixes hc hcc hψ hn, hv, map_mul, map_mul, map_inv] at hnx
  calc ψ y' = (ψ w)⁻¹ * (ψ w * ψ y' * (ψ w)⁻¹) * ψ w := by group
    _ = (ψ w)⁻¹ * ψ D.z * ψ w := by rw [← hnx]
    _ = (ψ w)⁻¹ * (ψ D.z * ψ w) := by group
    _ = ψ D.z := by rw [← (hH (ψ w)).2 (Or.inl ⟨w, rfl⟩)]; group

end CaseThreeData

end CFSG.EvenSmallLie.OmegaEight.Child8

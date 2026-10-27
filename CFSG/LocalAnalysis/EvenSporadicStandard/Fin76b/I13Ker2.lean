module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Ker

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_into {Θ S₀ : Subgroup G} (hS₀Θ : S₀ ≤ Θ) (hS₀ : IsPGroup 2 S₀)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Θ → S₀ ≤ P → P ≤ S₀) {y : G} (hyΘ : y ∈ Θ)
    (hy2 : y * y = 1) : ∃ g ∈ Θ, g⁻¹ * y * g ∈ S₀ := by
  have hS'p : IsPGroup 2 (S₀.subgroupOf Θ) := hS₀.comap_subtype
  have hmax' : ∀ {Q : Subgroup ↥Θ}, IsPGroup 2 Q → S₀.subgroupOf Θ ≤ Q → Q = S₀.subgroupOf Θ := by
    intro Q hQ hle
    have hQp : IsPGroup 2 (Q.map Θ.subtype) := hQ.map _
    have hQΘ : Q.map Θ.subtype ≤ Θ := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hS₀Q : S₀ ≤ Q.map Θ.subtype := by
      intro s hs
      exact ⟨⟨s, hS₀Θ hs⟩, hle (mem_subgroupOf.2 hs), rfl⟩
    have hQS : Q.map Θ.subtype ≤ S₀ := hmax _ hQp hQΘ hS₀Q
    refine le_antisymm (fun q hq => mem_subgroupOf.2 (hQS ⟨q, hq, rfl⟩)) hle
  let SS : Sylow 2 ↥Θ := ⟨S₀.subgroupOf Θ, hS'p, fun {Q} hQ hle => hmax' hQ hle⟩
  let y' : ↥Θ := ⟨y, hyΘ⟩
  have hy'2 : y' * y' = 1 := Subtype.ext hy2
  have hY' : IsPGroup 2 (zpowers y') := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : (g : ↥Θ) ^ 2 = 1 := by
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hy'2,
        one_zpow]
    simpa using h2
  obtain ⟨Q, hQ⟩ := hY'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Θ SS Q
  have hy'Q : y' ∈ (Q : Subgroup ↥Θ) := hQ (mem_zpowers y')
  rw [← hg, Sylow.coe_subgroup_smul] at hy'Q
  obtain ⟨s, hs, hsy⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy'Q
  have hs' : (s : G) ∈ S₀ := mem_subgroupOf.1 hs
  have hsy' : (g : G) * s * (g : G)⁻¹ = y := by
    have := congrArg Subtype.val hsy
    simpa [MulAut.smul_def] using this
  refine ⟨g, g.2, ?_⟩
  have : (g : G)⁻¹ * y * g = s := by
    rw [← hsy']; group
  rw [this]
  exact hs'

end Sylow

theorem mem_sup_zpowers_of_conj {G : Type} [Group G] {z : G} (hz : z * z = 1) {N : Subgroup G}
    (hN : ∀ n ∈ N, z * n * z⁻¹ ∈ N) {x : G} (hx : x ∈ N ⊔ zpowers z) :
    ∃ k ∈ N, x = k ∨ x = k * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let W : Subgroup G :=
    { carrier := {x | ∃ k ∈ N, x = k ∨ x = k * z}
      mul_mem' := by
        rintro x y ⟨k₁, hk₁, hx⟩ ⟨k₂, hk₂, hy⟩
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
        · exact ⟨k₁ * k₂, mul_mem hk₁ hk₂, Or.inl rfl⟩
        · exact ⟨k₁ * k₂, mul_mem hk₁ hk₂, Or.inr (by group)⟩
        · refine ⟨k₁ * (z * k₂ * z⁻¹), mul_mem hk₁ (hN _ hk₂), Or.inr ?_⟩
          group
        · refine ⟨k₁ * (z * k₂ * z⁻¹), mul_mem hk₁ (hN _ hk₂), Or.inl ?_⟩
          calc k₁ * z * (k₂ * z) = k₁ * (z * k₂ * z⁻¹) * (z * z) := by group
            _ = _ := by rw [hz, mul_one]
      one_mem' := ⟨1, N.one_mem, Or.inl rfl⟩
      inv_mem' := by
        rintro x ⟨k, hk, hx⟩
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨k⁻¹, inv_mem hk, Or.inl rfl⟩
        · refine ⟨z * k⁻¹ * z⁻¹, hN _ (inv_mem hk), Or.inr ?_⟩
          calc (k * z)⁻¹ = z⁻¹ * k⁻¹ := mul_inv_rev _ _
            _ = z * k⁻¹ := by rw [hzi]
            _ = (z * k⁻¹ * z⁻¹) * z := by group }
  have hle : N ⊔ zpowers z ≤ W := by
    refine sup_le (fun k hk => ⟨k, hk, Or.inl rfl⟩) ?_
    rw [zpowers_le]
    exact ⟨1, N.one_mem, Or.inr (by group)⟩
  exact hle hx

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem mem_Thz {x : G} (hx : x ∈ c.KR ⊔ zpowers z) : ∃ k ∈ c.KR, x = k ∨ x = k * z :=
  mem_sup_zpowers_of_conj c.h.z_sq (fun _ hk => c.z_conj_KR hk) hx

theorem zpowers_z_pgroup : IsPGroup 2 (zpowers z) :=
  IsPGroup.of_card (n := 1) (by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, c.h.conf.cfg.z_order]; norm_num)

theorem Zs_pgroup : IsPGroup 2 c.Zs :=
  IsPGroup.of_card (n := 2) (by rw [Zs]; rw [c.h.card_Zs c.hα]; norm_num)

theorem zpowers_le_normalizer_Zs : zpowers z ≤ normalizer (c.Zs : Set G) := by
  rw [zpowers_le, mem_normalizer_iff]
  intro a
  refine ⟨fun ha => c.z_conj_Zs ha, fun ha => ?_⟩
  have := c.z_conj_Zs ha
  rwa [c.z_conj_conj] at this

theorem S0_pgroup : IsPGroup 2 (zpowers z ⊔ c.Zs : Subgroup G) :=
  c.zpowers_z_pgroup.to_sup_of_normal_right' c.Zs_pgroup c.zpowers_le_normalizer_Zs

theorem S0_le_Thz : zpowers z ⊔ c.Zs ≤ c.KR ⊔ zpowers z :=
  sup_le (le_sup_right) (c.Zs_le_KR.trans le_sup_left)

theorem S0_max {P : Subgroup G} (hP : IsPGroup 2 P) (hPΘ : P ≤ c.KR ⊔ zpowers z)
    (hS : zpowers z ⊔ c.Zs ≤ P) : P ≤ zpowers z ⊔ c.Zs := by
  have hzP : z ∈ P := hS (mem_sup_left (mem_zpowers z))
  have hZP : c.Zs ≤ P := le_sup_right.trans hS
  have hP' : IsPGroup 2 (P ⊓ c.KR : Subgroup G) := hP.to_le inf_le_left
  have hK : P ⊓ c.KR ≤ c.Zs := by
    refine c.kl hP' inf_le_right (le_inf hZP c.Zs_le_KR) (fun y hy => ?_)
    exact ⟨(mul_mem (mul_mem hzP hy.1) (inv_mem hzP) : z * y * z⁻¹ ∈ P), c.z_conj_KR hy.2⟩
  intro p hp
  obtain ⟨k, hk, hpk | hpk⟩ := c.mem_Thz (hPΘ hp)
  · rw [hpk] at hp ⊢
    exact mem_sup_right (hK ⟨hp, hk⟩)
  · rw [hpk] at hp ⊢
    have hkP : k ∈ P := by
      have := mul_mem hp (inv_mem hzP)
      simpa using this
    exact mul_mem (mem_sup_right (hK ⟨hkP, hk⟩)) (mem_sup_left (mem_zpowers z))

theorem exists_conj_into_S0 {y : G} (hy : y ∈ c.KR ⊔ zpowers z) (hy2 : y * y = 1) :
    ∃ g ∈ c.KR ⊔ zpowers z, g⁻¹ * y * g ∈ zpowers z ⊔ c.Zs :=
  exists_conj_into c.S0_le_Thz c.S0_pgroup (fun _ hP hPΘ hS => c.S0_max hP hPΘ hS) hy hy2

theorem Zs_conj_Thz {g a : G} (hg : g ∈ c.KR ⊔ zpowers z) (ha : a ∈ c.Zs) :
    g * a * g⁻¹ ∈ c.Zs := by
  obtain ⟨k, hk, hgk⟩ := c.mem_Thz hg
  rcases hgk with hgk | hgk <;> rw [hgk]
  · have : k * a = a * k := c.Zs_comm_N1 ha (c.KR_le_N1 hk)
    rw [this]; simpa using ha
  · have hza := c.z_conj_Zs ha
    have hc : k * (z * a * z⁻¹) = (z * a * z⁻¹) * k := c.Zs_comm_N1 hza (c.KR_le_N1 hk)
    have e : k * z * a * (k * z)⁻¹ = z * a * z⁻¹ := by
      calc k * z * a * (k * z)⁻¹ = k * (z * a * z⁻¹) * k⁻¹ := by group
        _ = z * a * z⁻¹ := by rw [hc]; group
    rw [e]; exact hza

theorem eq_one_or_t_of_sq {a : G} (ha : a ∈ c.Zs) (h : a * z * (a * z) = 1) :
    a = 1 ∨ a = t := by
  have hαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
      _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
  have h2 : a * (z * a * z⁻¹) = 1 := by
    have : a * z * (a * z) = a * (z * a * z⁻¹) * (z * z) := by group
    rwa [this, c.h.z_sq, mul_one] at h
  rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1, c.h.z_conj_alpha c.hα, ← mul_assoc, c.hα.sq, one_mul] at h2
    exact c.h.t_ne h2
  · exfalso
    rw [h1, hαt] at h2
    have : α * t * α = t := by
      have := c.h.t_comm_S α c.hα.mem
      calc α * t * α = t * α * α := by rw [← this]
        _ = t := by rw [mul_assoc, c.hα.sq, mul_one]
    rw [this] at h2
    exact c.h.t_ne h2

theorem t_mul_z : t * z = α * z * α⁻¹ := by
  have hzα : z * α = α * t * z := by
    have := c.h.z_conj_alpha c.hα
    calc z * α = (z * α * z⁻¹) * z := by group
      _ = α * t * z := by rw [this]
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right c.hα.sq
  symm
  calc α * z * α⁻¹ = α * (z * α) := by rw [hαi]; group
    _ = α * (α * t * z) := by rw [hzα]
    _ = t * z := by rw [← mul_assoc α, ← mul_assoc α, c.hα.sq, one_mul]

theorem exists_comm_adjust {n : G} (hn : n ∈ c.N1)
    (hsym : (c.rho ⟨n, hn⟩).1 = (c.rho ⟨n, hn⟩).2) :
    ∃ k ∈ c.KR, (n * k) * z = z * (n * k) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hzn : z * n * z⁻¹ ∈ c.N1 := c.z_conj_N1 hn
  obtain ⟨u, hu⟩ : ∃ u : G, u = (z * n * z⁻¹)⁻¹ * n := ⟨_, rfl⟩
  have huN : u ∈ c.N1 := by rw [hu]; exact mul_mem (inv_mem hzn) hn
  have huK : u ∈ c.KR := by
    refine c.mem_KR.2 ⟨huN, ?_⟩
    have h1 : (⟨u, huN⟩ : ↥c.N1) = (c.zconjN1 ⟨n, hn⟩)⁻¹ * ⟨n, hn⟩ := Subtype.ext hu
    have h2 : ((c.rho ⟨n, hn⟩).2, (c.rho ⟨n, hn⟩).1) = c.rho ⟨n, hn⟩ :=
      Prod.ext hsym.symm hsym
    rw [h1, map_mul, map_inv, c.rho_zconj, h2, inv_mul_cancel]
  have hyeq : z * u = n⁻¹ * z * n := by
    calc z * u = (z * z) * n⁻¹ * z⁻¹ * n := by rw [hu]; group
      _ = n⁻¹ * z * n := by rw [c.h.z_sq, one_mul, hzi]
  have hyΘ : z * u ∈ c.KR ⊔ zpowers z := by
    have : z * u = (z * u * z⁻¹) * z := by group
    rw [this]
    exact mul_mem (mem_sup_left (c.z_conj_KR huK)) (mem_sup_right (mem_zpowers z))
  have hy2 : (z * u) * (z * u) = 1 := by
    rw [hyeq]
    calc n⁻¹ * z * n * (n⁻¹ * z * n) = n⁻¹ * (z * z) * n := by group
      _ = 1 := by rw [c.h.z_sq]; group
  obtain ⟨g, hgΘ, hy'⟩ := c.exists_conj_into_S0 hyΘ hy2
  rw [sup_comm] at hy'
  obtain ⟨a, ha, hya⟩ := mem_sup_zpowers_of_conj c.h.z_sq (fun _ h => c.z_conj_Zs h) hy'
  obtain ⟨k₀, hk₀, hg⟩ := c.mem_Thz hgΘ
  have hgz : g * z * g⁻¹ = k₀ * z * k₀⁻¹ := by
    rcases hg with rfl | rfl <;> group
  have hgα : g * α * g⁻¹ ∈ c.Zs := c.Zs_conj_Thz hgΘ c.alpha_mem_Zs
  have hy' : g⁻¹ * (z * u) * g = g⁻¹ * (z * u) * g := rfl
  have hzu : z * u = g * (g⁻¹ * (z * u) * g) * g⁻¹ := by group
  rcases hya with hya | hya
  ·
    exfalso
    have h1 : z * u = g * a * g⁻¹ := by rw [hzu, hya]
    have h2 : z * u ∈ c.KR := by
      rw [h1]; exact c.Zs_le_KR (c.Zs_conj_Thz hgΘ ha)
    have h3 : z ∈ c.KR := by
      have := mul_mem h2 (inv_mem huK)
      simpa using this
    exact c.h.z_not_mem_cent_alpha c.hα (mem_cent_singleton_iff_conj.2
      (c.mem_N1.1 (c.KR_le_N1 h3)).2)
  · have hsq : a * z * (a * z) = 1 := by
      have : g⁻¹ * (z * u) * g * (g⁻¹ * (z * u) * g) = 1 := by
        calc g⁻¹ * (z * u) * g * (g⁻¹ * (z * u) * g) = g⁻¹ * ((z * u) * (z * u)) * g := by group
          _ = 1 := by rw [hy2]; group
      rwa [hya] at this
    obtain ⟨m, hm, hmz⟩ : ∃ m ∈ c.KR, z * u = m * z * m⁻¹ := by
      rcases c.eq_one_or_t_of_sq ha hsq with h1 | h1
      · refine ⟨k₀, hk₀, ?_⟩
        rw [hzu, hya, h1, one_mul]; exact hgz
      · refine ⟨(g * α * g⁻¹) * k₀, mul_mem (c.Zs_le_KR hgα) hk₀, ?_⟩
        rw [hzu, hya, h1, c.t_mul_z]
        calc g * (α * z * α⁻¹) * g⁻¹ = (g * α * g⁻¹) * (g * z * g⁻¹) * (g * α * g⁻¹)⁻¹ := by
              group
          _ = (g * α * g⁻¹) * (k₀ * z * k₀⁻¹) * (g * α * g⁻¹)⁻¹ := by rw [hgz]
          _ = ((g * α * g⁻¹) * k₀) * z * ((g * α * g⁻¹) * k₀)⁻¹ := by group
    refine ⟨m, hm, ?_⟩
    have : (n * m) * z * (n * m)⁻¹ = z := by
      calc (n * m) * z * (n * m)⁻¹ = n * (m * z * m⁻¹) * n⁻¹ := by group
        _ = n * (z * u) * n⁻¹ := by rw [hmz]
        _ = z := by rw [hyeq]; group
    calc (n * m) * z = ((n * m) * z * (n * m)⁻¹) * (n * m) := by group
      _ = z * (n * m) := by rw [this]

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b

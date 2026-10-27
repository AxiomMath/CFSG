module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Img

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

@[expose] noncomputable def KR : Subgroup G := c.rho.ker.map c.N1.subtype

theorem mem_KR {k : G} : k ∈ c.KR ↔ ∃ h : k ∈ c.N1, c.rho ⟨k, h⟩ = 1 := by
  simp only [KR, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨k, h⟩, hk, rfl⟩

theorem KR_le_N1 : c.KR ≤ c.N1 := fun _ hk => (c.mem_KR.1 hk).1

theorem Zs_le_KR : c.Zs ≤ c.KR := fun _ ha => c.mem_KR.2 ⟨c.Zs_le_N1 ha, c.rho_Zs ha⟩

theorem z_conj_KR {k : G} (hk : k ∈ c.KR) : z * k * z⁻¹ ∈ c.KR := by
  obtain ⟨h, hk1⟩ := c.mem_KR.1 hk
  refine c.mem_KR.2 ⟨c.z_conj_N1 h, ?_⟩
  have := c.rho_zconj ⟨k, h⟩
  rw [hk1] at this
  exact this

theorem Zs_comm_N1 {a n : G} (ha : a ∈ c.Zs) (hn : n ∈ c.N1) : n * a = a * n := by
  obtain ⟨hn1, hn2⟩ := c.mem_N1.1 hn
  have hnt := c.Nc_t hn1
  have hcomm : ∀ u, n * u * n⁻¹ = u → n * u = u * n := by
    intro u hu
    calc n * u = (n * u * n⁻¹) * n := by group
      _ = u * n := by rw [hu]
  apply hcomm
  rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
  · rw [h1]; group
  · rw [h1]; exact hnt
  · rw [h1]; exact hn2
  · rw [h1]
    calc n * (α * t) * n⁻¹ = (n * α * n⁻¹) * (n * t * n⁻¹) := by group
      _ = α * t := by rw [hn2, hnt]

theorem z_conj_Zs {a : G} (ha : a ∈ c.Zs) : z * a * z⁻¹ ∈ c.Zs := by
  have hαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
      _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
  rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
  · rw [h1]; simp
  · rw [h1, c.h.z_conj_t]; exact c.t_mem_Zs
  · rw [h1, c.h.z_conj_alpha c.hα]; exact c.alpha_t_mem_Zs
  · rw [h1, hαt]; exact c.alpha_mem_Zs

theorem exists_k_comm_z {y a : G} (hy : y ∈ c.N1) (ha : a ∈ c.Zs) (h : z * y * z⁻¹ = y * a) :
    ∃ k ∈ c.Zs, (y * k) * z = z * (y * k) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
      _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
  have hyz : ∀ u : G, u ∈ c.Zs → y * u = u * y := fun u hu => c.Zs_comm_N1 hu hy
  have h2 : a * (z * a * z⁻¹) = 1 := by
    have h3 : z * (z * y * z⁻¹) * z⁻¹ = y := c.z_conj_conj y
    rw [h] at h3
    have h4 : z * (y * a) * z⁻¹ = (z * y * z⁻¹) * (z * a * z⁻¹) := by group
    rw [h4, h] at h3
    have h5 : y * (a * (z * a * z⁻¹)) = y * 1 := by rw [← mul_assoc]; simpa using h3
    exact mul_left_cancel h5
  have hnot : ∀ u : G, (u = α ∨ u = α * t) → ¬ (u * (z * u * z⁻¹) = 1) := by
    rintro u (rfl | rfl) hu
    · rw [c.h.z_conj_alpha c.hα, ← mul_assoc, c.hα.sq, one_mul] at hu
      exact c.h.t_ne hu
    · rw [hαt] at hu
      have : α * t * α = t := by
        have := c.h.t_comm_S α c.hα.mem
        calc α * t * α = t * α * α := by rw [← this]
          _ = t := by rw [mul_assoc, c.hα.sq, mul_one]
      rw [this] at hu
      exact c.h.t_ne hu
  rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
  · refine ⟨1, c.Zs.one_mem, ?_⟩
    rw [h1] at h
    have : y * z = z * y := by
      calc y * z = (z * y * z⁻¹) * z := by rw [h]; group
        _ = z * y := by group
    simpa using this
  · refine ⟨α, c.alpha_mem_Zs, ?_⟩
    rw [h1] at h
    have htα : t * α = α * t := (c.h.t_comm_S α c.hα.mem).symm
    have hzα := c.h.z_conj_alpha c.hα
    have : z * (y * α) * z⁻¹ = y * α := by
      calc z * (y * α) * z⁻¹ = (z * y * z⁻¹) * (z * α * z⁻¹) := by group
        _ = (y * t) * (α * t) := by rw [h, hzα]
        _ = y * (t * α) * t := by group
        _ = y * (α * t) * t := by rw [htα]
        _ = y * α := by rw [mul_assoc, mul_assoc, c.h.t_sq, mul_one]
    calc y * α * z = (z * (y * α) * z⁻¹) * z := by rw [this]
      _ = z * (y * α) := by group
  · exact absurd (h1 ▸ h2) (hnot a (Or.inl h1))
  · exact absurd (h1 ▸ h2) (hnot a (Or.inr h1))

theorem mem_Zs_of_comm_z {n : G} (hn : n ∈ c.N1) (hnz : n * z = z * n)
    (hρ : c.rho ⟨n, hn⟩ = 1) : n ∈ c.Zs := by
  have hcz : n ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z :=
    (c.h.normalizer_Q_cent_z_iff c.hα c.hF c.hWr c.hBD).1 ⟨c.mem_Nc.1 (c.N1_le_Nc hn), hnz⟩
  have hAB : zpowers z ≤ centralizer ((L ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => c.h.conf.cfg.z_comm_of_mem_A ha.1
  obtain ⟨ℓ, hℓ, w, hw, hnℓ⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hcz
  rcases mem_zpowers_sq_eq_one c.h.z_sq hw with hw1 | hw1
  · rw [hw1, mul_one] at hnℓ
    subst hnℓ
    have hconv := c.rho_conv ⟨n, hn⟩ hnz (c.W_le_normE hℓ)
    rw [hρ] at hconv
    have h1 : convN (⟨n, c.W_le_normE hℓ⟩ : normalizer (E : Set G)) = 1 :=
      (Prod.ext_iff.1 hconv.symm).1
    have hcomm : ∀ e ∈ E, n * e = e * n := by
      intro e he
      have := congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) h1
      simp only [convN_coe] at this
      calc n * e = (n * e * n⁻¹) * n := by group
        _ = e * n := by rw [this]; rfl
    rcases c.h.wf.cent n hℓ.1 hcomm with h2 | h2
    · rw [h2]; exact c.Zs.one_mem
    · rw [h2]; exact c.t_mem_Zs
  · exfalso
    rw [hw1] at hnℓ
    obtain ⟨e, he, b, hb, hℓeb⟩ := c.exists_eq_mul_of_mem_W hℓ
    have hℓα : ℓ * α = α * ℓ := by
      rw [hℓeb]
      have h1 : e * α = α * e := (c.mem_Qs.1 (c.E_le_Qs he)).2
      have h2 : b * α = α * b := c.h.BS b hb α c.hα.mem
      calc e * b * α = e * (α * b) := by rw [mul_assoc, h2]
        _ = α * (e * b) := by rw [← mul_assoc, h1, mul_assoc]
    have hℓt : ℓ * t = t * ℓ := mem_centralizer_singleton_iff.1 hℓ.2
    have hn2 := (c.mem_N1.1 hn).2
    have : n * α * n⁻¹ = α * t := by
      rw [hnℓ]
      calc ℓ * z * α * (ℓ * z)⁻¹ = ℓ * (z * α * z⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (α * t) * ℓ⁻¹ := by rw [c.h.z_conj_alpha c.hα]
        _ = (ℓ * α * ℓ⁻¹) * (ℓ * t * ℓ⁻¹) := by group
        _ = α * t := by
          rw [hℓα, hℓt]; group
    rw [hn2] at this
    exact c.h.t_ne (by simpa using this.symm)

theorem kl {Y : Subgroup G} (hY : IsPGroup 2 Y) (hYK : Y ≤ c.KR) (hZY : c.Zs ≤ Y)
    (hzY : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) : Y ≤ c.Zs := by
  classical
  by_contra hne
  have hzz := c.h.z_sq
  set A' : Subgroup ↥Y := c.Zs.subgroupOf Y with hA'
  have hN : A'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnZ : (n : G) ∈ c.Zs := mem_subgroupOf.1 hn
    have hcomm : (g : G) * n = n * g := c.Zs_comm_N1 hnZ (c.KR_le_N1 (hYK g.2))
    refine mem_subgroupOf.2 ?_
    show (g : G) * n * (g : G)⁻¹ ∈ c.Zs
    have : (g : G) * n * (g : G)⁻¹ = n := by rw [hcomm]; group
    rw [this]; exact hnZ
  let f : ↥Y →* ↥Y :=
    { toFun := fun y => ⟨z * (y : G) * z⁻¹, hzY y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show z * ((a * b : ↥Y) : G) * z⁻¹ = (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  have hff : ∀ y : ↥Y, f (f y) = y := fun y => Subtype.ext (c.z_conj_conj _)
  have hfA : A' ≤ A'.comap f := by
    intro n hn
    rw [Subgroup.mem_comap]
    exact mem_subgroupOf.2 (c.z_conj_Zs (mem_subgroupOf.1 hn))
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : ↥Y ⧸ A' →* ↥Y ⧸ A',
      ∀ y : ↥Y, σ0 (y : ↥Y ⧸ A') = ((f y : ↥Y) : ↥Y ⧸ A') :=
    ⟨QuotientGroup.map A' A' f hfA, fun y => rfl⟩
  have hinv : Function.Involutive σ0 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hσ0, hσ0, hff]
  let inst : Fintype (↥Y ⧸ A') := Fintype.ofFinite _
  let σ : Equiv.Perm (↥Y ⧸ A') := hinv.toPerm σ0
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [σ, pow_two, hinv x]
  have hidx : A'.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hne
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ A' := by rw [h1]; exact mem_top _
    exact mem_subgroupOf.1 this
  have h2dvd : 2 ∣ Fintype.card (↥Y ⧸ A') := by
    obtain ⟨k, hk⟩ := hY.index A'
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hidx (by simpa using hk)
    exact dvd_pow_self 2 hk0
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) h2dvd hσ2
    (a := 1) (by simp [σ])
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hyA : (y : G) ∉ c.Zs := by
    intro hy
    apply hb1
    exact (QuotientGroup.eq_one_iff y).2 (mem_subgroupOf.2 hy)
  have hfix : (σ0 (y : ↥Y ⧸ A')) = (y : ↥Y ⧸ A') := hb
  rw [hσ0] at hfix
  have h3 := QuotientGroup.eq.1 hfix
  have ha : (z * (y : G) * z⁻¹)⁻¹ * y ∈ c.Zs := mem_subgroupOf.1 h3
  have hyN : (y : G) ∈ c.N1 := c.KR_le_N1 (hYK y.2)
  obtain ⟨k, hk, hkz⟩ := c.exists_k_comm_z hyN (inv_mem ha) (by group)
  have hyk : (y : G) * k ∈ Y := mul_mem y.2 (hZY hk)
  obtain ⟨hn, hρ⟩ := c.mem_KR.1 (hYK hyk)
  have hmem := c.mem_Zs_of_comm_z hn hkz hρ
  apply hyA
  have : (y : G) = (y * k) * k⁻¹ := by group
  rw [this]
  exact mul_mem hmem (inv_mem hk)

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b

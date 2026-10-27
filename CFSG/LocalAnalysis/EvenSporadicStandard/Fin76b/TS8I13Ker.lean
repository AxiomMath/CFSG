module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Img

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

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
  have hmem : n ∈ normalizer (E : Set G) ⊓ centralizer ({z} : Set G) :=
    (c.h.normalizer_Q_cent_z_iff c.hα c.hF c.hM c.hp).1 ⟨c.mem_Nc.1 (c.N1_le_Nc hn), hnz⟩
  have hN : n ∈ normalizer (E : Set G) := hmem.1
  have hconv := c.rho_conv ⟨n, hn⟩ hnz hN
  rw [hρ] at hconv
  have hconv1 : convN (⟨n, hN⟩ : normalizer (E : Set G)) = 1 :=
    (Prod.ext_iff.1 hconv.symm).1
  have hcomm : ∀ e ∈ E, n * e = e * n := by
    intro e he
    have := congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) hconv1
    simp only [convN_coe] at this
    calc n * e = (n * e * n⁻¹) * n := by group
      _ = e * n := by rw [this]; rfl
  have hcE : n ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.2 fun e he => (hcomm e he).symm
  have hn2 : n * α * n⁻¹ = α := (c.mem_N1.1 hn).2
  rcases c.hM.centZ n hcE hnz with e1 | e1 | e1 | e1
  · rw [e1]; exact c.Zs.one_mem
  · exfalso
    have hz : z ∈ centralizer ({α} : Set G) := by
      have := mem_cent_singleton_iff_conj.2 hn2
      rwa [e1] at this
    exact c.h.z_not_mem_cent_alpha c.hα hz
  · rw [e1]; exact c.t_mem_Zs
  · exfalso
    have htα : α * t = t * α := c.h.t_comm_S α c.hα.mem
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.h.t_sq
    have hzα := c.h.z_conj_alpha c.hα
    have htz : t * z * α * (t * z)⁻¹ = α * t := by
      calc t * z * α * (t * z)⁻¹ = t * (z * α * z⁻¹) * t⁻¹ := by group
        _ = t * (α * t) * t⁻¹ := by rw [hzα]
        _ = t * (t * α) * t⁻¹ := by rw [htα]
        _ = (t * t) * α * t⁻¹ := by group
        _ = α * t⁻¹ := by rw [c.h.t_sq, one_mul]
        _ = α * t := by rw [hti]
    rw [e1] at hn2
    have hαt : α * t = α * 1 := by rw [mul_one]; exact htz.symm.trans hn2
    exact c.h.t_ne (mul_left_cancel hαt)

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

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b

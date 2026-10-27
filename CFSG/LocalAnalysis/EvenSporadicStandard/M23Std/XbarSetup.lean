module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Centralizer

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

instance normal_centralizer_subgroupOf (L1 : Subgroup G) :
    ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have hg' := Subgroup.mem_normalizer_iff.1 hg
  have hgi := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg)
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have hy' : g⁻¹ * y * g ∈ L1 := by simpa using (hgi y).1 hy
    have := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * y := by group
  · intro hc y hy
    have hy' : g * y * g⁻¹ ∈ L1 := (hg' y).1 hy
    have := hc _ hy'
    calc y * c = g⁻¹ * ((g * y * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = c * y := by group

abbrev Xbar (L1 : Subgroup G) : Type :=
  ↥(normalizer (L1 : Set G)) ⧸
    (centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G))

namespace Setup

variable (S : Setup L z t F L1 N)

include S

@[expose] def zX : ↥(normalizer (L1 : Set G)) := ⟨z, S.K_le_X S.z_mem_K⟩

@[simp] theorem coe_zX : (S.zX : G) = z := rfl

theorem mk_mem_centralizer_iff (x : ↥(normalizer (L1 : Set G))) :
    (QuotientGroup.mk x : Xbar L1) ∈ centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} :
      Set (Xbar L1)) ↔ z * ((x : G) * z * (x : G)⁻¹) ∈ centralizer (L1 : Set G) := by
  have hxX : (x : G) ∈ normalizer (L1 : Set G) := x.2
  rw [mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hCX : ∀ g ∈ normalizer (L1 : Set G), ∀ c ∈ centralizer (L1 : Set G),
      g * c * g⁻¹ ∈ centralizer (L1 : Set G) := fun g hg c hc =>
    (normal_centralizer_subgroupOf L1).conj_mem ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩ hc
      ⟨g, hg⟩
  have e : (((x * S.zX)⁻¹ * (S.zX * x) : ↥(normalizer (L1 : Set G))) : G) =
      z * (x : G)⁻¹ * z * x := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, zX, mul_inv_rev, hzi, mul_assoc]
  rw [e]
  constructor
  · intro hA
    have h1 := hCX _ hxX _ hA
    have key : ((x : G) * (z * (x : G)⁻¹ * z * x) * (x : G)⁻¹)⁻¹ = z * (x * z * (x : G)⁻¹) := by
      have : ((x : G) * (z * (x : G)⁻¹ * z * x) * (x : G)⁻¹)⁻¹ =
          z⁻¹ * x * z⁻¹ * (x : G)⁻¹ := by group
      rw [this, hzi]
      group
    rw [← key]
    exact Subgroup.inv_mem _ h1
  · intro hB
    have h1 := hCX _ (Subgroup.inv_mem _ hxX) _ (Subgroup.inv_mem _ hB)
    have key : (x : G)⁻¹ * (z * ((x : G) * z * (x : G)⁻¹))⁻¹ * (x : G)⁻¹⁻¹ =
        z * (x : G)⁻¹ * z * x := by
      have : (x : G)⁻¹ * (z * ((x : G) * z * (x : G)⁻¹))⁻¹ * (x : G)⁻¹⁻¹ =
          z⁻¹ * (x : G)⁻¹ * z⁻¹ * x := by group
      rw [this, hzi]
    rw [key] at h1
    exact h1

theorem centralizer_zbar_eq :
    centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) =
      ((centralizer ({z} : Set G)).subgroupOf (normalizer (L1 : Set G))).map
        (QuotientGroup.mk' _) := by
  have hz2 : z * z = 1 := S.one.z_mul_self
  apply le_antisymm
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h := (S.mk_mem_centralizer_iff x).1 hq
    obtain ⟨k, hk, m, hm, u, hu, hxeq⟩ := S.exists_mem_centralizer_of_conj_mem x.2 h
    obtain ⟨huX, huz⟩ := Subgroup.mem_inf.1 hu
    have hmC : m ∈ centralizer (L1 : Set G) := S.N_le hm
    have hkK : k ∈ L1 ⊔ zpowers z := S.K_eq ▸ hk
    have hmX : m ∈ normalizer (L1 : Set G) := S.N_le_X hm
    have hcC : ∀ l ∈ L1, m⁻¹ * l ∈ centralizer (L1 : Set G) := fun l hl =>
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hmC)
        (mem_centralizer_iff.2 fun y hy => S.L1_comm y hy l hl)
    have key : ∃ (c w : G), c ∈ centralizer (L1 : Set G) ∧ w ∈ normalizer (L1 : Set G) ∧
        w ∈ centralizer ({z} : Set G) ∧ (x : G) = c * w := by
      rcases mem_sup_zpowers_cases hz2 S.z_norm hkK with hl | ⟨l, hl, rfl⟩
      · exact ⟨m⁻¹ * k, u, hcC k hl, huX, huz, hxeq⟩
      · refine ⟨m⁻¹ * l, z * u, hcC l hl, ?_, ?_, ?_⟩
        · exact Subgroup.mul_mem _ (S.K_le_X S.z_mem_K) huX
        · rw [mem_centralizer_singleton_iff] at huz ⊢
          calc z * u * z = z * (u * z) := by group
            _ = z * (z * u) := by rw [huz]
        · rw [hxeq]
          group
    obtain ⟨c, w, hc, hw, hwz, hxcw⟩ := key
    refine ⟨⟨w, hw⟩, Subgroup.mem_subgroupOf.2 hwz, ?_⟩
    let cX : ↥(normalizer (L1 : Set G)) := ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩
    have hx : x = cX * ⟨w, hw⟩ := Subtype.ext hxcw
    show (QuotientGroup.mk ⟨w, hw⟩ : Xbar L1) = QuotientGroup.mk x
    rw [hx, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff cX).2 (Subgroup.mem_subgroupOf.2 hc),
      one_mul]
  · rintro _ ⟨y, hy, rfl⟩
    refine (S.mk_mem_centralizer_iff y).2 ?_
    have hyz : (y : G) * z = z * (y : G) := mem_centralizer_singleton_iff.1 hy
    have : (y : G) * z * (y : G)⁻¹ = z := by rw [hyz]; group
    rw [this, hz2]
    exact Subgroup.one_mem _

end Setup

end CFSG.EvenSporadicStandard.M23Std

module

public import CFSG.GH74.GLS.SP.Local.SPLM2a
public import CFSG.GH74.GLS.SP.Local.SPLWt3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

@[expose] def SPLLeafA : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot3 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D.toSPLNot2 → SPL2Ord D.toSPLNot0 →
      SPL3X D → ∃ a : G, SPL3Aa { D with a := a }

@[expose] def SPLLeafR2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot3 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D.toSPLNot2 → SPL2Ord D.toSPLNot0 →
      SPL3X D → SPL3Aa D → SPL3R2 D

section Derived

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem X_le_K [Finite G] (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) : D.X ≤ D.K :=
  sup_le (le_trans hX.X₁_le le_sup_left)
    (le_trans (conjBy_t_le_K₂ D hs hX.X₁_le) le_sup_right)

theorem z_comm_K (hs : SPLSetup D.toSPLNot0) {y : G} (hy : y ∈ D.K) : y * D.z = D.z * y := by
  have hK : D.K ≤ centralizer ({D.z} : Set G) :=
    sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hk))
      (fun k hk => mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ hk))
  exact mem_centralizer_singleton_iff.mp (hK hy)

theorem conjBy_t_Y₁ (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) : conjBy D.t D.Y₁ = D.Y₁ := by
  ext y
  rw [mem_conjBy_iff]
  constructor
  · intro hy
    have h := hX.Y₁_inv _ hy
    have e : D.t * (D.t * y * D.t⁻¹) * D.t⁻¹ = y := by
      have : D.t * (D.t * y * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * y * (D.t * D.t)⁻¹ := by group
      rw [this, t_mul_t D hs]
      simp
    rw [e] at h
    rw [h]
    exact D.Y₁.inv_mem hy
  · intro hy
    rw [hX.Y₁_inv y hy]
    exact D.Y₁.inv_mem hy

theorem conjBy_t_X₃ (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) (ha : D.a ∈ D.Ct) :
    conjBy D.t D.X₃ = D.X₃ := by
  have hat : D.a * D.t = D.t * D.a := mem_centralizer_singleton_iff.mp ha
  rw [SPLNot3.X₃, conjBy_conjBy, hat, ← conjBy_conjBy, conjBy_t_Y₁ D hs hX]

theorem a_z_conj (hs : SPLSetup D.toSPLNot0) (hA : SPL3Aa D) : D.a * D.z * D.a⁻¹ = D.z * D.t := by
  have hat : D.a * D.t = D.t * D.a := mem_centralizer_singleton_iff.mp hA.a_mem
  have haz : D.a⁻¹ * D.z * D.a = D.z * D.t := hA.a_facts.a_z
  have h1 : D.z = D.a * (D.z * D.t) * D.a⁻¹ := by rw [← haz]; group
  have h2 : D.a * D.t * D.a⁻¹ = D.t := by rw [hat]; group
  have h3 : D.z = (D.a * D.z * D.a⁻¹) * D.t := by
    calc D.z = D.a * (D.z * D.t) * D.a⁻¹ := h1
      _ = (D.a * D.z * D.a⁻¹) * (D.a * D.t * D.a⁻¹) := by group
      _ = (D.a * D.z * D.a⁻¹) * D.t := by rw [h2]
  have htt := t_mul_t D hs
  calc D.a * D.z * D.a⁻¹ = (D.a * D.z * D.a⁻¹) * (D.t * D.t) := by rw [htt]; group
    _ = ((D.a * D.z * D.a⁻¹) * D.t) * D.t := by group
    _ = D.z * D.t := by rw [← h3]

theorem z_inv_X₃ [Finite G] (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) (hA : SPL3Aa D) :
    ∀ x ∈ D.X₃, D.z * x * D.z⁻¹ = x⁻¹ := by
  intro x hx
  have hzt := a_z_conj D hs hA
  have hxY : D.a * x * D.a⁻¹ ∈ D.Y₁ := by
    rw [SPLNot3.X₃, mem_conjBy_iff] at hx
    exact hx
  obtain ⟨y, hy⟩ : ∃ y, y = D.a * x * D.a⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hxY
  have hyK : y ∈ D.K := X_le_K D hs hX (hX.Y₁_le hxY)
  have hzy : y * D.z = D.z * y := z_comm_K D hs hyK
  have hzy' : D.z * y⁻¹ = y⁻¹ * D.z := by
    calc D.z * y⁻¹ = y⁻¹ * (y * D.z) * y⁻¹ := by group
      _ = y⁻¹ * (D.z * y) * y⁻¹ := by rw [hzy]
      _ = y⁻¹ * D.z := by group
  have key : D.z * x * D.z⁻¹ =
      D.a⁻¹ * ((D.a * D.z * D.a⁻¹) * y * (D.a * D.z * D.a⁻¹)⁻¹) * D.a := by
    rw [hy]; group
  rw [key, hzt]
  have hzty : D.z * D.t * y * (D.z * D.t)⁻¹ = y⁻¹ := by
    calc D.z * D.t * y * (D.z * D.t)⁻¹ = D.z * (D.t * y * D.t⁻¹) * D.z⁻¹ := by group
      _ = D.z * y⁻¹ * D.z⁻¹ := by rw [hX.Y₁_inv y hxY]
      _ = y⁻¹ := by rw [hzy']; group
  rw [hzty, hy]
  group

theorem R₂_nonab_of (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) (hR : SPL3R2 D) :
    ∃ x ∈ D.R₂, ∃ y ∈ D.R₂, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hcen : center ↥D.R₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon g g.2 x x.2)
  have h1 : (center ↥D.R₂).map D.R₂.subtype = D.R₂ := by
    rw [hcen, Subgroup.map_top, Subgroup.range_subtype]
  rw [hR.R₂_center] at h1
  have h2 : Nat.card ↥D.X₂ = Nat.card ↥D.R₂ := by rw [h1]
  rw [hR.R₂_card, SPLNot3.X₂, card_conjBy, hX.X₁_card] at h2
  have hq : 1 < D.q := by have := hs.q_ge; omega
  have : D.q ^ 1 < D.q ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  rw [pow_one] at this
  omega

theorem z_not_mem_R₂ (hs : SPLSetup D.toSPLNot0) (hR : SPL3R2 D) : D.z ∉ D.R₂ := by
  have : Fact D.p.Prime := ⟨hs.prime⟩
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  have hRp : IsPGroup D.p ↥D.R₂ := IsPGroup.of_card (n := k * 3) (by
    rw [hR.R₂_card, hqk, ← pow_mul])
  intro hz
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hRp) ⟨D.z, hz⟩
  have h2 : orderOf D.z = D.p ^ m := by simpa using hm
  rw [hs.syl.z_inv] at h2
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp at h2
  · have hdvd : D.p ∣ 2 := by rw [h2]; exact dvd_pow_self _ hm0.ne'
    exact hs.p_ne_two ((Nat.prime_dvd_prime_iff_eq hs.prime Nat.prime_two).mp hdvd)

theorem K₁_inf_R₂_eq_bot [Finite G] (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) (hR : SPL3R2 D) :
    D.K₁ ⊓ D.R₂ = ⊥ := by
  have hKN := K₁_normalizes_R₂ D hs hX hR.R₂_normal
  have hN : (D.R₂.subgroupOf D.K₁).Normal :=
    ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥D.K₁) : G) ∈ D.R₂
      simpa using hKN g g.2 n hn⟩
  have hz := z_not_mem_R₂ D hs hR
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hs.comps.quasi₁
      (D.R₂.subgroupOf D.K₁) with hle | htop
  · rw [eq_bot_iff]
    rintro x ⟨hxK, hxR⟩
    have hxc : (⟨x, hxK⟩ : ↥D.K₁) ∈ center ↥D.K₁ := hle hxR
    have hxz : x ∈ zpowers D.z := (mem_center_K₁_iff D hs ⟨x, hxK⟩).mp hxc
    rcases eq_one_or_z hs hxz with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hxR) hz
  · exfalso
    have hzK : (⟨D.z, z_mem_K₁ hs⟩ : ↥D.K₁) ∈ D.R₂.subgroupOf D.K₁ := by rw [htop]; trivial
    exact hz hzK

theorem P_facts [Finite G] (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D) (hR : SPL3R2 D) :
    IsPGroup D.p ↥D.P ∧ Nat.card ↥D.P = D.q ^ 4 := by
  have : Fact D.p.Prime := ⟨hs.prime⟩
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  have hinf : D.R₂ ⊓ D.X₁ = ⊥ := by
    rw [inf_comm, eq_bot_iff]
    exact le_trans (inf_le_inf_right _ hX.X₁_le) (K₁_inf_R₂_eq_bot D hs hX hR).le
  have hn : D.X₁ ≤ normalizer (D.R₂ : Set G) := fun x hx =>
    hR.R₂_normal (K₁_le_M₂ D hs hX (hX.X₁_le hx))
  have hc := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hn
  rw [hinf, Subgroup.card_bot, hR.R₂_card, hX.X₁_card, mul_one] at hc
  have hP : D.P = D.R₂ ⊔ D.X₁ := by rw [SPLNot3.P, sup_comm]
  have hcard : Nat.card ↥D.P = D.q ^ 4 := by
    rw [hP, hc]; ring
  refine ⟨IsPGroup.of_card (n := k * 4) (by rw [hcard, hqk, ← pow_mul]), hcard⟩

end Derived

theorem splLeafM2_of_AR2 (hA : SPLLeafA) (hR : SPLLeafR2) : SPLLeafM2 := by
  intro G _ _ hG D₂ hs h1 h2 hord
  obtain ⟨X₁, X₁', Y₁, hX⟩ := exists_X D₂ hs h1
  obtain ⟨a, ha⟩ := hA G hG ⟨D₂, X₁, X₁', Y₁, 1⟩ hs h1 h2 hord (hX 1)
  have hAD : SPL3Aa (⟨D₂, X₁, X₁', Y₁, a⟩ : SPLNot3 G) := ha
  have hXD : SPL3X (⟨D₂, X₁, X₁', Y₁, a⟩ : SPLNot3 G) := hX a
  have hRD := hR G hG ⟨D₂, X₁, X₁', Y₁, a⟩ hs h1 h2 hord hXD hAD
  refine ⟨⟨D₂, X₁, X₁', Y₁, a⟩, rfl, ?_⟩
  obtain ⟨hPp, hPc⟩ := P_facts (⟨D₂, X₁, X₁', Y₁, a⟩ : SPLNot3 G) hs hXD hRD
  exact ⟨hXD, hAD, hRD, z_inv_X₃ _ hs hXD hAD, conjBy_t_X₃ _ hs hXD hAD.a_mem,
    R₂_nonab_of _ hs hXD hRD, hPp, hPc⟩

end CFSG.GH74.GLS.SP.Local

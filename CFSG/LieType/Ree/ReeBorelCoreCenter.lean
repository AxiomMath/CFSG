module

public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Ree.NormalPositiveGeneration

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem mem_reeFixedTorus_of_mem_normalCore
    {x : t.reeGamma K a}
    (hx : x ∈ ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore) :
    (x : ModGL t.tag K) ∈ t.reeFixedTorus K a := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ t.reeGamma K a :=
    (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  rw [← reeFixedBorel_inf_map_conj (K := K) (a := a) hw₀]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h := hx 1
    rw [one_mul, inv_one, mul_one, Subgroup.mem_subgroupOf] at h
    exact h
  · have h := hx ⟨_, inv_mem hn⟩
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨(canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ * x *
      canonicalRep (coxeterSystem t.tag) K w₀, by simpa using h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem commute_of_mem_normalCore_reeFixedBorel
    {x : t.reeGamma K a}
    (hx : x ∈ ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore)
    {u : t.reeGamma K a} (hu : (u : ModGL t.tag K) ∈ t.reeFixedPosUnipotent K a) :
    u * x = x * u := by
  set L := ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore
  have hk : x * u * x⁻¹ * u⁻¹ ∈ L := by
    have h' : u * x⁻¹ * u⁻¹ ∈ L := (Subgroup.normalCore_normal _).conj_mem _ (inv_mem hx) u
    have := mul_mem hx h'
    simpa [mul_assoc] using this
  have hkH := mem_reeFixedTorus_of_mem_normalCore hk
  have hxH := mem_reeFixedTorus_of_mem_normalCore hx
  have hconj : (x : ModGL t.tag K) * u * (x : ModGL t.tag K)⁻¹ ∈ t.reeFixedPosUnipotent K a :=
    (Subgroup.mem_normalizer_iff.1 (reeFixedBorel_le_normalizer_reeFixedPosUnipotent
      (reeFixedTorus_le_reeFixedBorel hxH)) u).1 hu
  have hkU : ((x * u * x⁻¹ * u⁻¹ : t.reeGamma K a) : ModGL t.tag K) ∈
      t.reeFixedPosUnipotent K a := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem hconj (inv_mem hu)
  have hbot := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.1
  have hk1 : ((x * u * x⁻¹ * u⁻¹ : t.reeGamma K a) : ModGL t.tag K) ∈
      torusGroup t.tag K ⊓ posUnipotent t.tag K :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hkH).1, (Subgroup.mem_inf.1 hkU).1⟩
  rw [hbot, Subgroup.mem_bot] at hk1
  have hk1' : x * u * x⁻¹ * u⁻¹ = 1 := Subtype.ext hk1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk1'
  exact hk1'.symm

theorem normalCore_reeFixedBorel_le_center
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore ≤
      Subgroup.center (t.reeGamma K a) := by
  intro x hx
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have hle : Subgroup.closure {y | ∃ c ∈ t.reeGamma K a, ∃ u ∈ t.reeFixedPosUnipotent K a,
      c * u * c⁻¹ = y} ≤ Subgroup.centralizer {(x : ModGL t.tag K)} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, u, hu, rfl⟩
    have hcx : (⟨c, hc⟩ : t.reeGamma K a)⁻¹ * x * ⟨c, hc⟩ ∈
        ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore := by
      have := (Subgroup.normalCore_normal _).conj_mem _ hx (⟨c, hc⟩ : t.reeGamma K a)⁻¹
      rwa [inv_inv] at this
    have huΓ : u ∈ t.reeGamma K a := reeFixedPosUnipotent_le_reeGamma hu
    have h := commute_of_mem_normalCore_reeFixedBorel hcx (u := ⟨u, huΓ⟩) hu
    have h' : u * (c⁻¹ * x * c) = (c⁻¹ * x * c) * u := congrArg Subtype.val h
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have e : c * u * c⁻¹ * (x : ModGL t.tag K) = c * (u * (c⁻¹ * x * c)) * c⁻¹ := by group
    rw [e, h']
    group
  rw [ree_normal_positive_generation t a K hK] at hle
  have hg := hle g.2 (x : ModGL t.tag K) rfl
  exact Subtype.ext hg.symm

theorem center_le_normalCore_reeFixedBorel :
    Subgroup.center (t.reeGamma K a) ≤
      ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore := by
  refine Subgroup.normal_le_normalCore.2 fun z hz => ?_
  rw [Subgroup.mem_subgroupOf, ← reeGamma_inf_normalizer_reeFixedPosUnipotent]
  refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_normalizer_iff.2 fun u => ?_⟩
  constructor
  · intro hu
    have huΓ : u ∈ t.reeGamma K a := reeFixedPosUnipotent_le_reeGamma hu
    have h : ((⟨u, huΓ⟩ : t.reeGamma K a) * z : t.reeGamma K a) = z * ⟨u, huΓ⟩ :=
      Subgroup.mem_center_iff.1 hz _
    have h' : u * (z : ModGL t.tag K) = z * u := congrArg Subtype.val h
    rw [← h', mul_inv_cancel_right]
    exact hu
  · intro hu
    have hΓ : (z : ModGL t.tag K) * u * (z : ModGL t.tag K)⁻¹ ∈ t.reeGamma K a :=
      reeFixedPosUnipotent_le_reeGamma hu
    have huΓ : u ∈ t.reeGamma K a := by
      have e : u = (z : ModGL t.tag K)⁻¹ * ((z : ModGL t.tag K) * u * (z : ModGL t.tag K)⁻¹) *
          z := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem z.2) hΓ) z.2
    have h : ((⟨u, huΓ⟩ : t.reeGamma K a) * z : t.reeGamma K a) = z * ⟨u, huΓ⟩ :=
      Subgroup.mem_center_iff.1 hz _
    have h' : u * (z : ModGL t.tag K) = z * u := congrArg Subtype.val h
    rwa [← h', mul_inv_cancel_right] at hu

theorem ree_Borel_core_center
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ((t.reeFixedBorel K a).subgroupOf (t.reeGamma K a)).normalCore =
      Subgroup.center (t.reeGamma K a) ∧
    (MulAction.toPermHom (t.reeGamma K a)
        (t.reeGamma K a ⧸ (t.reeFixedBorel K a).subgroupOf (t.reeGamma K a))).ker =
      Subgroup.center (t.reeGamma K a) := by
  have hcore := le_antisymm (normalCore_reeFixedBorel_le_center hK)
    center_le_normalCore_reeFixedBorel
  exact ⟨hcore, by rw [← Subgroup.normalCore_eq_ker, hcore]⟩

end ReeTag

end CFSG.LieType.Ree

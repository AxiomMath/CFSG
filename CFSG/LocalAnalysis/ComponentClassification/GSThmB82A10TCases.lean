module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCtx
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0Fuse

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private theorem propB_mem_S0 (c : Eight2.CtxA0 X) {w : X} (hw : w * w = 1)
    (hc : ∀ u ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y, u * w = w * u) :
    w ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB0 : c.s.h.secB0 c.s.y ≤ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
    le_inf ((c.s.h.secB0_le_B c.s.y).trans c.s.h.B_le_S) le_normalizer
  have ha : c.s.h.a ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
    mem_inf.mpr ⟨c.s.h.a_mem_S, c.s.secCond.a_mem_G0⟩
  have hE : Seven.E c.s.h c.s.y ≤ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
    (Seven.E_le_sup_secB0 c.s.lemma61).trans (sup_le (zpowers_le.mpr ha) hB0)
  have hSyl : Seven.IsSylowIn (c.s.h.S ⊓ normalizer (c.s.h.secB0 c.s.y : Set X))
      (normalizer (c.s.h.secB0 c.s.y : Set X) ⊓ centralizer (Seven.E c.s.h c.s.y : Set X)) :=
    ⟨le_inf inf_le_right c.s.S0_le, c.s.S0_sylow⟩
  have hwM : w ∈ normalizer (c.s.h.secB0 c.s.y : Set X) ⊓
      centralizer (Seven.E c.s.h c.s.y : Set X) :=
    mem_inf.mpr ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => hc b (hB0 hb)),
      mem_centralizer_iff.mpr fun e he => hc e (hE he)⟩
  have h2 : IsPGroup 2 (zpowers w) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw))
  have hQ2 : IsPGroup 2 ↥((c.s.h.S ⊓ normalizer (c.s.h.secB0 c.s.y : Set X)) ⊔ zpowers w) :=
    IsPGroup.to_sup_of_normal_left' (c.s.h.isPGroup_S.to_le inf_le_left) h2
      (zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr hc)))
  have hQ := hSyl.eq_of_le_of_isPGroup (sup_le hSyl.1 (zpowers_le.mpr hwM)) hQ2 le_sup_left
  have hw' : w ∈ (c.s.h.S ⊓ normalizer (c.s.h.secB0 c.s.y : Set X)) ⊔ zpowers w :=
    mem_sup_right (mem_zpowers w)
  rw [hQ] at hw'
  exact hw'

private theorem propB_exists_conj (c : Eight2.CtxA0 X) :
    ∃ g ∈ centralizer ({c.s.h.a * c.Z.z} : Set X),
      ∀ r ∈ (c.s.h.S ⊓ c.s.h.secG0 c.s.y) ⊔ zpowers c.s.t, g * r * g⁻¹ ∈ c.s.h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({c.s.h.a * c.Z.z} : Set X)
  set R := (c.s.h.S ⊓ c.s.h.secG0 c.s.y) ⊔ zpowers c.s.t
  have hSC : c.s.h.S ≤ C := fun u hu => mem_centralizer_singleton_iff.mpr (by
    rw [← mul_assoc, c.s.h.comm_a hu, mul_assoc, c.Z.hzS u hu, ← mul_assoc])
  have hRC : R ≤ C := sup_le (inf_le_left.trans hSC) (zpowers_le.mpr c.t_mem_centralizer_az)
  have hS02 : IsPGroup 2 ↥(c.s.h.S ⊓ c.s.h.secG0 c.s.y) := c.s.h.isPGroup_S.to_le inf_le_left
  obtain ⟨k, hk⟩ := hS02 ⟨c.s.t * c.s.t, c.ht2⟩
  have hk' : (c.s.t * c.s.t) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have ht2 : IsPGroup 2 (zpowers c.s.t) := IsPGroup.of_card_dvd_pow (n := k + 1) (by
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_succ', pow_mul, pow_two]
    exact hk')
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_left' hS02 ht2 (zpowers_le.mpr c.s.t_norm)
  obtain ⟨R0, hR0⟩ := Eight2.isSylow_S_of_caseA c.s.S_sylow c.hN
  have hR0C : (R0 : Subgroup X) ≤ C := hR0.le.trans hSC
  obtain ⟨Q, hQ⟩ := (hR2.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q (R0.subtype hR0C)
  refine ⟨g, g.2, fun r hr => ?_⟩
  have h1 : g * (⟨r, hRC hr⟩ : C) * g⁻¹ ∈ ((g • Q : Sylow 2 C) : Subgroup C) := by
    rw [P29.mem_smul_sylow_iff, show g⁻¹ * (g * ⟨r, hRC hr⟩ * g⁻¹) * g = ⟨r, hRC hr⟩ by group]
    exact hQ (show (⟨r, hRC hr⟩ : C) ∈ R.subgroupOf C from mem_subgroupOf.mpr hr)
  rw [hg, Sylow.coe_subtype, hR0] at h1
  exact mem_subgroupOf.mp h1

theorem gs82PropBStatementK_holds :
    ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
      ∃ g ∈ centralizer ({c.s.h.a * c.Z.z} : Set X),
        ∀ w ∈ ({c.s.h.a, c.Z.z} : Set X),
          g⁻¹ * w * g ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y ∧
          (∀ u ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y, u * (g⁻¹ * w * g) = (g⁻¹ * w * g) * u) ∧
          c.s.t * (g⁻¹ * w * g) = (g⁻¹ * w * g) * c.s.t := by
  intro X _ _ c
  obtain ⟨g, hg, hgR⟩ := propB_exists_conj c
  refine ⟨g, hg, fun w hw => ?_⟩
  have hwS : ∀ u ∈ c.s.h.S, u * w = w * u := by
    rcases hw with rfl | rfl
    · exact fun u hu => c.s.h.comm_a hu
    · exact c.Z.hzS
  have hw2 : w * w = 1 := by
    rcases hw with rfl | rfl
    · exact Six.a_mul_a_self c.s.h
    · exact c.Z.hzz
  have hcR : ∀ r ∈ (c.s.h.S ⊓ c.s.h.secG0 c.s.y) ⊔ zpowers c.s.t,
      r * (g⁻¹ * w * g) = (g⁻¹ * w * g) * r := by
    intro r hr
    have h1 := hwS _ (hgR r hr)
    calc r * (g⁻¹ * w * g) = g⁻¹ * ((g * r * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * r * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * w * g) * r := by group
  have hcS : ∀ u ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y, u * (g⁻¹ * w * g) = (g⁻¹ * w * g) * u :=
    fun u hu => hcR u (mem_sup_left hu)
  refine ⟨propB_mem_S0 c ?_ hcS, hcS, hcR _ (mem_sup_right (mem_zpowers _))⟩
  calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
    _ = 1 := by rw [hw2]; group

namespace Ctx

variable (c : Ctx X)

structure PropBData where
  g : X
  mem_centralizer : g ∈ centralizer ({c.s.h.a * c.Z.z} : Set X)
  mem_S0 : ∀ w ∈ ({c.s.h.a, c.Z.z} : Set X), g⁻¹ * w * g ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y
  comm_S0 : ∀ w ∈ ({c.s.h.a, c.Z.z} : Set X), ∀ u ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y,
    u * (g⁻¹ * w * g) = (g⁻¹ * w * g) * u
  comm_t : ∀ w ∈ ({c.s.h.a, c.Z.z} : Set X), c.s.t * (g⁻¹ * w * g) = (g⁻¹ * w * g) * c.s.t

theorem nonempty_propBData : Nonempty c.PropBData := by
  have hPB := gs82PropBStatementK_holds
  obtain ⟨g, hg, hw⟩ := hPB X c.toCtxA0
  exact ⟨⟨g, hg, fun w hw' => (hw w hw').1, fun w hw' => (hw w hw').2.1,
    fun w hw' => (hw w hw').2.2⟩⟩

private theorem φ_cases {x : ↥(c.s.h.secSub c.s.y)}
    (hxS : ∀ u ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y, u * (x : X) = x * u)
    (hxt : c.s.t * (x : X) = x * c.s.t) :
    c.φ x = 1 ∨ c.φ x = sigmaTwo * z0 ∨ c.φ x = r0 ∨ c.φ x = sigmaTwo * z0 * r0 := by
  refine mem_of_commute_t c.φ_t_normalizes_U0 c.φ_t_conj.1 c.φ_t_conj.2 (fun u hu => ?_) ?_
  · obtain ⟨v, hv, rfl⟩ := mem_map.mp (c.U0_le_map_S0 hu)
    rw [← map_mul, ← map_mul]
    exact congrArg c.φ (Subtype.ext (hxS v (mem_subgroupOf.mp hv)).symm)
  · rw [← map_mul, ← map_mul]
    exact congrArg c.φ (Subtype.ext hxt.symm)

namespace PropBData

variable {c} (d : c.PropBData)

abbrev a' : X := d.g⁻¹ * c.s.h.a * d.g

abbrev z' : X := d.g⁻¹ * c.Z.z * d.g

theorem a'_mem_S0 : d.a' ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
  d.mem_S0 _ (Set.mem_insert _ _)

theorem z'_mem_S0 : d.z' ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
  d.mem_S0 _ (Set.mem_insert_of_mem _ rfl)

theorem a'_mem_secSub : d.a' ∈ c.s.h.secSub c.s.y :=
  c.s.h.S_inf_le_secSub c.s.y d.a'_mem_S0

theorem z'_mem_secSub : d.z' ∈ c.s.h.secSub c.s.y :=
  c.s.h.S_inf_le_secSub c.s.y d.z'_mem_S0

theorem a'_mul_self : d.a' * d.a' = 1 := by
  show d.g⁻¹ * c.s.h.a * d.g * (d.g⁻¹ * c.s.h.a * d.g) = 1
  calc d.g⁻¹ * c.s.h.a * d.g * (d.g⁻¹ * c.s.h.a * d.g) = d.g⁻¹ * (c.s.h.a * c.s.h.a) * d.g := by
        group
    _ = 1 := by rw [Six.a_mul_a_self c.s.h]; group

theorem z'_mul_self : d.z' * d.z' = 1 := by
  show d.g⁻¹ * c.Z.z * d.g * (d.g⁻¹ * c.Z.z * d.g) = 1
  calc d.g⁻¹ * c.Z.z * d.g * (d.g⁻¹ * c.Z.z * d.g) = d.g⁻¹ * (c.Z.z * c.Z.z) * d.g := by group
    _ = 1 := by rw [c.Z.hzz]; group

theorem a'_mul_z' : d.a' * d.z' = c.s.h.a * c.Z.z := by
  have hg := mem_centralizer_singleton_iff.mp d.mem_centralizer
  show d.g⁻¹ * c.s.h.a * d.g * (d.g⁻¹ * c.Z.z * d.g) = c.s.h.a * c.Z.z
  calc d.g⁻¹ * c.s.h.a * d.g * (d.g⁻¹ * c.Z.z * d.g) = d.g⁻¹ * (c.s.h.a * c.Z.z * d.g) := by
        group
    _ = d.g⁻¹ * (d.g * (c.s.h.a * c.Z.z)) := by rw [← hg]
    _ = c.s.h.a * c.Z.z := by group

theorem a'_comm_z' : d.a' * d.z' = d.z' * d.a' :=
  (d.comm_S0 _ (Set.mem_insert _ _) _ d.z'_mem_S0).symm

theorem cases :
    (d.a' ∈ c.s.h.secB0 c.s.y ∧ c.φ ⟨d.z', d.z'_mem_secSub⟩ = sigmaTwo * z0) ∨
    (d.z' ∈ c.s.h.secB0 c.s.y ∧ c.φ ⟨d.a', d.a'_mem_secSub⟩ = sigmaTwo * z0) ∨
    (c.φ ⟨d.a', d.a'_mem_secSub⟩ = r0 ∧ c.φ ⟨d.z', d.z'_mem_secSub⟩ = sigmaTwo * z0 * r0) ∨
    (c.φ ⟨d.z', d.z'_mem_secSub⟩ = r0 ∧ c.φ ⟨d.a', d.a'_mem_secSub⟩ = sigmaTwo * z0 * r0) := by
  have ha := c.φ_cases (x := ⟨d.a', d.a'_mem_secSub⟩) (d.comm_S0 _ (Set.mem_insert _ _))
    (d.comm_t _ (Set.mem_insert _ _))
  have hz := c.φ_cases (x := ⟨d.z', d.z'_mem_secSub⟩) (d.comm_S0 _ (Set.mem_insert_of_mem _ rfl))
    (d.comm_t _ (Set.mem_insert_of_mem _ rfl))
  have hprod : c.φ ⟨d.a', d.a'_mem_secSub⟩ * c.φ ⟨d.z', d.z'_mem_secSub⟩ = sigmaTwo * z0 := by
    rw [← map_mul, ← c.φ_a, ← c.φ_z, ← map_mul]
    exact congrArg c.φ (Subtype.ext d.a'_mul_z')
  have ha2 : d.a' ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact d.a'_mul_self
  have hz2 : d.z' ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact d.z'_mul_self
  rcases ha with ha | ha | ha | ha <;> rcases hz with hz | hz | hz | hz <;>
    rw [ha, hz] at hprod
  all_goals first
    | exact absurd hprod (by decide)
    | skip
  · exact Or.inl ⟨c.mem_B0_of_φ_eq_one (w := ⟨d.a', d.a'_mem_secSub⟩) ha2 ha, hz⟩
  · exact Or.inr (Or.inl ⟨c.mem_B0_of_φ_eq_one (w := ⟨d.z', d.z'_mem_secSub⟩) hz2 hz, ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hz⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, ha⟩))

end PropBData

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T

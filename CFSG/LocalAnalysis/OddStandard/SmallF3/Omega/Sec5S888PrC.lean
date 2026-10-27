module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrA
public import CFSG.Walter.AStar.Subnormal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G :=
  (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem Sec5Pair.proj_subnormal {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {P : Subgroup G} (hP : P ≤ K₁ ⊔ K₂) (hsn : (P.subgroupOf (K₁ ⊔ K₂)).IsSubnormal) :
    ∃ P₂ : Subgroup G, P₂ ≤ K₂ ∧ (P₂.subgroupOf K₂).IsSubnormal ∧
      ∀ b : G, b ∈ P₂ ↔ (b ∈ K₂ ∧ ∃ a ∈ K₁, a * b ∈ P) := by
  let M : Subgroup G := K₁ ⊔ K₂
  let Φ : ↥K₁ × ↥K₂ →* ↥M :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [h.comm q.1 q.1.2 p.2 p.2.2]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  let P' : Subgroup ↥M := P.subgroupOf M
  have hsn' : P'.IsSubnormal := hsn
  let ψ : ↥K₁ × ↥K₂ →* ↥K₂ := MonoidHom.snd ↥K₁ ↥K₂
  have hψsurj : Function.Surjective ψ := fun b => ⟨(1, b), rfl⟩
  let Q₂ : Subgroup ↥K₂ := (P'.comap Φ).map ψ
  have hQ₂sn : Q₂.IsSubnormal := (hsn'.comap Φ).map hψsurj
  refine ⟨Q₂.map K₂.subtype, Subgroup.map_subtype_le Q₂, ?_, ?_⟩
  · have hsub : (Q₂.map K₂.subtype).subgroupOf K₂ = Q₂ :=
      Subgroup.comap_map_eq_self_of_injective K₂.subtype_injective Q₂
    rw [hsub]
    exact hQ₂sn
  · intro b
    constructor
    · intro hb
      obtain ⟨q, hq, hqb⟩ := Subgroup.mem_map.mp hb
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
      have hxΦ : ((x.1 : G) * (x.2 : G)) ∈ P :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hx)
      have hx2 : (x.2 : G) = b := by
        have h1 : (x.2 : G) = (q : G) := by
          have := congrArg (fun y : ↥K₂ => (y : G)) hxq
          simpa [ψ] using this
        exact h1.trans hqb
      refine ⟨?_, (x.1 : G), x.1.2, ?_⟩
      · rw [← hqb]; exact q.2
      · rw [hx2] at hxΦ; exact hxΦ
    · rintro ⟨hbK, a, ha, hab⟩
      have hmem : (⟨a, ha⟩, ⟨b, hbK⟩) ∈ P'.comap Φ := by
        rw [Subgroup.mem_comap]
        exact hab
      have hq : (⟨b, hbK⟩ : ↥K₂) ∈ Q₂ :=
        Subgroup.mem_map.mpr ⟨(⟨a, ha⟩, ⟨b, hbK⟩), hmem, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, hq, rfl⟩

theorem Sec5Pair.oddCore_subnormal [Finite G] {K₁ K₂ : Subgroup G} {z : G}
    (h : Sec5Pair K₁ K₂ z) {P : Subgroup G} (hP : P ≤ K₁ ⊔ K₂)
    (hsn : (P.subgroupOf (K₁ ⊔ K₂)).IsSubnormal) : CFSG.oddCore ↥P = ⊥ := by
  have hPp : CFSG.pPrimeCore 2 ↥(K₁ ⊔ K₂) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two]
    exact h.oddCore_bot
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (X := P.subgroupOf (K₁ ⊔ K₂)) hsn
  rw [hPp, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  have h2 := CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hP)
  rw [h1, Subgroup.map_bot] at h2
  rw [oddCore_eq_pPrimeCore_two]
  exact h2.symm

end CFSG.OddStandard.SmallF3.Omega

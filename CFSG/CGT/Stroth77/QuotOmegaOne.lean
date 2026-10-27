module

public import CFSG.CGT.Stroth77.Section224Deviation

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

@[expose]
def zmodRed (n : ℕ) : ZMod (2 ^ n) →+ ZMod (2 ^ (n - 1)) where
  toFun a := ZMod.cast a
  map_zero' := ZMod.cast_zero
  map_add' a b := ZMod.cast_add (pow_dvd_pow 2 (Nat.sub_le n 1)) a b

@[expose]
def torusRed (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) : Torus k →+ Torus (fun i => k i - 1) where
  toFun v i := zmodRed (k i) (v i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

@[expose]
def twoTorsion (k : Fin 3 → ℕ) : AddSubgroup (Torus k) where
  carrier := {v | (2 : ℤ) • v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_neg, ha, neg_zero]

@[simp]
theorem mem_twoTorsion {k : Fin 3 → ℕ} {v : Torus k} :
    v ∈ twoTorsion k ↔ (2 : ℤ) • v = 0 := Iff.rfl

namespace StrothDatum

variable (Z : StrothDatum X)

theorem one_le_tau_k (hk : ∀ i, 2 ≤ Z.τ.k i) : ∀ i, 1 ≤ Z.τ.k i :=
  fun i => le_trans (by norm_num) (hk i)

@[expose]
def quotOmegaOneHom (hk : ∀ i, 2 ≤ Z.τ.k i) :
    Additive Z.D →+ Torus (fun i => Z.τ.k i - 1) :=
  (torusRed Z.τ.k (Z.one_le_tau_k hk)).comp Z.dataD.e

end StrothDatum

namespace StrothDatum

variable (Z : StrothDatum X)

theorem conjBy_mem_omegaIn_one {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G))
    {d : Z.D} (hd : d ∈ (omegaIn 1 Z.D).subgroupOf Z.D) :
    conjBy hg d ∈ (omegaIn 1 Z.D).subgroupOf Z.D := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, mem_omegaIn_iff_of_comm hcomm] at hd ⊢
  refine ⟨(conjBy hg d).2, ?_⟩
  have hsq : ((d : Z.D) : G) * ((d : Z.D) : G) = 1 := by
    simpa [pow_two] using hd.2
  have hconj : ((conjBy hg d : Z.D) : G) = g⁻¹ * (d : G) * g := rfl
  have h2 : (g⁻¹ * (d : G) * g) * (g⁻¹ * (d : G) * g) = 1 := by
    calc (g⁻¹ * (d : G) * g) * (g⁻¹ * (d : G) * g)
        = g⁻¹ * (((d : Z.D) : G) * ((d : Z.D) : G)) * g := by group
      _ = 1 := by rw [hsq]; group
  rw [hconj]
  simpa [pow_two] using h2

@[expose]
def conjByMul {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) : Z.D →* Z.D where
  toFun d := conjBy hg d
  map_one' := by ext; simp [conjBy]
  map_mul' a b := by ext; simp [conjBy]; group

@[expose]
noncomputable def quotConjBy {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) :
    Z.D ⧸ (omegaIn 1 Z.D).subgroupOf Z.D →* Z.D ⧸ (omegaIn 1 Z.D).subgroupOf Z.D :=
  QuotientGroup.map _ _ (conjByMul Z hg) (fun d hd => Z.conjBy_mem_omegaIn_one hg hd)

@[simp]
theorem quotConjBy_mk {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) (d : Z.D) :
    quotConjBy Z hg (QuotientGroup.mk d) = QuotientGroup.mk (conjBy hg d) := rfl

end StrothDatum

end CFSG.CGT.Stroth77

module

public import CFSG.LargeExtraspecial.S4Span
public import CFSG.GF2Type.Smith1979.IdxFourTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def pre (K : Subgroup S.O) : Subgroup G := (K.comap S.ρ).map S.M.subtype

variable {S}

theorem mem_pre {K : Subgroup S.O} {g : G} :
    g ∈ pre S K ↔ ∃ h : g ∈ S.M, S.ρ ⟨g, h⟩ ∈ K := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem pre_le_M (K : Subgroup S.O) : pre S K ≤ S.M := by
  rintro g hg
  exact (mem_pre.mp hg).1

theorem mem_pre_of_rho {K : Subgroup S.O} (m : S.M) (hm : S.ρ m ∈ K) : (m : G) ∈ pre S K :=
  mem_pre.mpr ⟨m.2, hm⟩

theorem rho_mem_of_mem_pre {K : Subgroup S.O} {g : G} (hg : g ∈ pre S K) (h : g ∈ S.M) :
    S.ρ ⟨g, h⟩ ∈ K := by
  obtain ⟨h', hg'⟩ := mem_pre.mp hg
  exact hg'

theorem QG_le_pre (K : Subgroup S.O) : S.QG ≤ pre S K := by
  intro x hx
  refine mem_pre.mpr ⟨S.QG_le_M hx, ?_⟩
  rw [(S.ρ_eq_one_iff ⟨x, S.QG_le_M hx⟩).mpr hx]
  exact K.one_mem

theorem pre_relIndex {K : Subgroup S.O} (hK : K ≤ S.Mbar) (hidx : K.relIndex S.Mbar = 2) :
    (pre S K).relIndex S.M = 2 := by
  have h1 : (pre S K).relIndex S.M = (K.comap S.ρ).relIndex ⊤ := by
    have h2 : S.M = (⊤ : Subgroup S.M).map S.M.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    conv_lhs => rw [h2]
    exact Subgroup.relIndex_map_map_of_injective (K.comap S.ρ) ⊤ S.M.subtype_injective
  rw [h1, Subgroup.relIndex_comap, ← MonoidHom.range_eq_map]
  exact hidx

theorem comm_le_pre {K : Subgroup S.O} (hK : K ≤ S.Mbar) (hidx : K.relIndex S.Mbar = 2) :
    ⁅S.M, S.M⁆ ≤ pre S K :=
  IdxFour.commutator_le_of_relIndex_eq_two (pre_relIndex hK hidx)

theorem conj_mem_pre {K : Subgroup S.O} (hn : ∀ m ∈ S.Mbar, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {h k : G}
    (hh : h ∈ S.M) (hk : k ∈ pre S K) : h * k * h⁻¹ ∈ pre S K := by
  obtain ⟨hkM, hk'⟩ := mem_pre.mp hk
  refine mem_pre.mpr ⟨S.M.mul_mem (S.M.mul_mem hh hkM) (S.M.inv_mem hh), ?_⟩
  have : S.ρ ⟨h * k * h⁻¹, S.M.mul_mem (S.M.mul_mem hh hkM) (S.M.inv_mem hh)⟩ =
      S.ρ ⟨h, hh⟩ * S.ρ ⟨k, hkM⟩ * (S.ρ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact hn _ ⟨_, rfl⟩ _ hk'

theorem card_pre {K : Subgroup S.O} (hK : K ≤ S.Mbar) :
    Nat.card (pre S K) = Nat.card K * Nat.card S.QG := by
  have hle : pre S K ≤ S.M := pre_le_M K
  set f : pre S K →* S.O := S.ρ.comp (inclusion hle) with hf
  have hrange : f.range = K := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact rho_mem_of_mem_pre y.2 (hle y.2)
    · intro hx
      obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (hK hx)
      exact ⟨⟨m, mem_pre_of_rho m hx⟩, rfl⟩
  have hker : f.ker = S.QG.subgroupOf (pre S K) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have h := card_ker_mul_card_range f
  rw [hrange, hker, Nat.card_congr (subgroupOfEquivOfLe (QG_le_pre K)).toEquiv] at h
  rw [← h, mul_comm]

variable (S) in
@[expose] noncomputable def stab (v : S.Qt) : Subgroup S.O where
  carrier := {x | x ∈ S.Mbar ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {x y} hx hy => ⟨S.Mbar.mul_mem hx.1 hy.1, by
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [hy.2, hx.2]⟩
  one_mem' := ⟨S.Mbar.one_mem, rfl⟩
  inv_mem' := fun {x} hx => ⟨S.Mbar.inv_mem hx.1, by
    conv_lhs => rw [← hx.2]
    exact CFSG.LargeExtraspecial.S4.inv_apply_apply_O x v⟩

theorem mem_stab {v : S.Qt} {x : S.O} :
    x ∈ stab S v ↔ x ∈ S.Mbar ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := Iff.rfl

theorem stab_le_Mbar (v : S.Qt) : stab S v ≤ S.Mbar := fun _ hx => hx.1

end CFSG.GF2Type.Smith1979.IdxFour

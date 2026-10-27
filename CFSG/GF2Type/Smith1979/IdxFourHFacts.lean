module

public import CFSG.GF2Type.Smith1979.IdxFourHSpace
public import CFSG.GF2Type.Smith1979.IdxFourHBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] def OuterData (t : S.O) : Prop := fixO S t ≤ commO S t

@[expose] noncomputable def InnerData (θ : S.O) (g : G) (t : S.O) : Prop :=
  θ * t = t * θ ∧ finrank (ZMod 2) (fixO S t) ≤ 8 ∧ (∀ r ∈ commO S t, S.q r = 0) ∧
  (∀ w ∈ fixO S t, (∀ p ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixO S t, polar S.q w p = 0) →
    ∃ p ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixO S t, ∃ r ∈ commO S t, w = p + r) ∧
  (∀ v ∈ fixO S t, S.q v = 0 →
    ∃ i : ℕ, ∃ u ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixO S t, ∃ r ∈ commO S t,
      v = ((θ ^ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u + r)

structure IdxFourFacts (g : G) (K : Subgroup S.O) (θ xb : S.O) : Prop where
  K_le : K ≤ S.Mbar
  K_index : K.relIndex S.Mbar = 2
  θ_mem : θ ∈ S.Mbar
  θ_cube : θ ^ 3 = 1
  θ_fpf : ∀ v : S.Qt, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0
  x_mem : xb ∈ S.Mbar
  x_not_mem : xb ∉ K
  x_sq : xb * xb = 1
  x_comm : xb * θ = θ * xb
  x_dim : finrank (ZMod 2) (commO S xb) = 2
  x_sing : ∀ w ∈ commO S xb, S.q w = 0
  x_cent : ¬ 2 ^ 9 ∣ Nat.card (S.Mbar ⊓ Subgroup.centralizer ({xb} : Set S.O) : Subgroup S.O)
  lemma5 : ∀ w ∈ commO S xb, w ≠ 0 → ∀ P : Subgroup S.O, P ≤ stab S w →
    (∀ s ∈ stab S w, ∀ p ∈ P, s * p * s⁻¹ ∈ P) → IsPGroup 2 P → Nat.card P ≠ 2 ^ 5
  stab_two : ∀ v : S.Qt, v ≠ 0 → S.q v = 0 → 2 ^ 8 ∣ Nat.card (stab S v)
  inv_conj : ∀ t ∈ K, t ≠ 1 → t * t = 1 → ∃ m ∈ S.Mbar, m * t * m⁻¹ ∈ S.Lbar g
  lbar : ∀ t ∈ S.Lbar g, t ≠ 1 → OuterData S t ∨ InnerData S θ g t

variable {S}

theorem IdxFourFacts.finrank_fixO_le {g : G} {K : Subgroup S.O} {θ xb : S.O}
    (hF : IdxFourFacts S g K θ xb) (hq : finrank (ZMod 2) S.Qt = 12) {t : S.O} (htK : t ∈ K)
    (ht1 : t ≠ 1) (htt : t * t = 1) : finrank (ZMod 2) (fixO S t) ≤ 8 := by
  obtain ⟨m, -, hm⟩ := hF.inv_conj t htK ht1 htt
  set t' : S.O := m * t * m⁻¹ with ht'
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    have : t = m⁻¹ * t' * m := by rw [ht']; group
    rw [this, h]
    group
  have ht'2 : t' * t' = 1 := by
    rw [ht']
    calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have key : finrank (ZMod 2) (fixO S t') ≤ 8 := by
    rcases hF.lbar t' hm ht'1 with hout | ⟨-, hdim, -⟩
    · have heq : commO S t' = fixO S t' := le_antisymm (commO_le_fixO ht'2) hout
      have h1 := finrank_commO_add_fixO t'
      rw [heq, hq] at h1
      omega
    · exact hdim
  rw [← finrank_fixO_conj m t]
  exact key

end CFSG.GF2Type.Smith1979.IdxFour

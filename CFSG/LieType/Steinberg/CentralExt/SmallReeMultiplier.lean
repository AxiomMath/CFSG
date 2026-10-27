module

public import CFSG.LieType.Steinberg.CentralExt.SmallReeThreeCover
public import CFSG.LieType.Steinberg.CentralExt.SylowEightCover
public import CFSG.LieType.Steinberg.CentralExt.PrimeCover
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.RankThree.Chevalley.SmallReeCentralExtension
public import CFSG.Walter.Ree.Model.Fusion

public section

namespace CFSG.LieType.Steinberg.CentralExt.SmallReeClosed

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint.Chevalley


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem smallRee_two_cover_trivial {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* G2.reeGamma K a) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element G2.tag
  obtain ⟨-, hSab, hS8, ⟨P, hP⟩, hconj, -⟩ :=
    CFSG.Walter.Ree.Model.small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  set S := CFSG.Walter.Ree.Model.smallReeE8 a K w₀
  have hmemS : ∀ x ∈ (P : Subgroup (G2.reeGamma K a)), (x : ModGL G2.tag K) ∈ S := by
    intro x hx
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  refine SylowEight.ker_eq_bot_of_sylow_eight P ?_ ?_ ?_ ?_ η hη hC h2
  · intro x hx y hy
    have h := hSab.toIsMulCommutative.is_comm.comm ⟨_, hmemS x hx⟩ ⟨_, hmemS y hy⟩
    have h' : (x : ModGL G2.tag K) * y = y * x := congrArg Subtype.val h
    exact Subtype.ext h'
  · intro x hx
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S) _ (hmemS x hx)
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]; exact h)
  · rw [← hS8, ← hP, Subgroup.card_map_of_injective (G2.reeGamma K a).subtype_injective]
  · intro x hx y hy hx1 hy1
    have hx1' : (x : ModGL G2.tag K) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hy1' : (y : ModGL G2.tag K) ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨g, hg, hgx⟩ := hconj _ (hmemS x hx) hx1'
    obtain ⟨g', hg', hgy⟩ := hconj _ (hmemS y hy) hy1'
    refine ⟨⟨g', hg'⟩⁻¹ * ⟨g, hg⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    calc g'⁻¹ * g * (x : ModGL G2.tag K) * (g⁻¹ * g') = g'⁻¹ * (g * x * g⁻¹) * g' := by group
      _ = y := by rw [hgx, ← hgy]; group

theorem smallRee_cover_trivial (ha : 1 ≤ a) (ℓ : ℕ) (hℓ : ℓ.Prime) (E : Type) [Group E]
    [Finite E] [Group.IsPerfect E] (η : E →* G2.reeGamma K a) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (hp : IsPGroup ℓ η.ker) : η.ker = ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact smallRee_two_cover_trivial hK η hη hC hp
  by_cases h3 : ℓ = 3
  · subst h3
    exact smallRee_three_cover_trivial hK ha η hη hC hp
  have hcop : Nat.Coprime (Nat.card η.ker) 6 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk]
    refine Nat.Coprime.pow_left _ ?_
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hℓ Nat.prime_two).2 h2)
      ((Nat.coprime_primes hℓ Nat.prime_three).2 h3)
  obtain ⟨s, hs, -, hcomm, -⟩ :=
    CFSG.RankThree.Chevalley.small_Ree_central_extension_split a ha K hK η hη hC hcop
  rw [eq_bot_iff]
  intro x hx
  have hxs : x ∈ s.range := by
    rw [← hcomm, Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨g, rfl⟩ := hxs
  have hg : g = 1 := by
    have h1 := DFunLike.congr_fun hs g
    rw [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [← h1]
    exact hx
  rw [hg, map_one]
  exact Subgroup.one_mem _

theorem smallRee_exists_section (ha : 1 ≤ a) (E : Type) [Group E] [Finite E]
    (π : E →* G2.reeGamma K a) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : G2.reeGamma K a →* E, ∀ g, π (σ g) = g := by
  have : Group.IsPerfect (G2.reeGamma K a) := ⟨(ree_generic_fixed_group_perfect G2 a ha K hK).2.1⟩
  exact PrimeCover.exists_section_of_forall_prime
    (fun ℓ hℓ P _ _ _ η hη hC hp => smallRee_cover_trivial hK ha ℓ hℓ P η hη hC hp) E π hπ hcen

theorem smallRee_hopfMultiplier (ha : 1 ≤ a) :
    commutator (G2.reeGamma K a ⧸ Subgroup.center (G2.reeGamma K a)) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier
        (G2.reeGamma K a ⧸ Subgroup.center (G2.reeGamma K a))) := by
  have : Group.IsPerfect (G2.reeGamma K a) := ⟨(ree_generic_fixed_group_perfect G2 a ha K hK).2.1⟩
  exact FieldFour.hopfMultiplier_subsingleton (center_reeGamma_G2_eq_bot hK)
    fun E _ _ π hπ hcen => smallRee_exists_section hK ha E π hπ hcen

end CFSG.LieType.Steinberg.CentralExt.SmallReeClosed

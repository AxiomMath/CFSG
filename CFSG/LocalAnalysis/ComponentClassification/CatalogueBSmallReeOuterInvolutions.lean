module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterPrimeSupport
public import CFSG.LieType.Ree.SmallReeFixedGroupSchreier

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem small_Ree_outer_prime_support (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∃ (R : Subgroup (Outer (ReeTag.G2.reeGamma K a))) (_ : R.Normal), IsPGroup 3 R ∧
      IsCyclic (Outer (ReeTag.G2.reeGamma K a) ⧸ R) ∧
      Nat.card (Outer (ReeTag.G2.reeGamma K a) ⧸ R) ∣ 2 * a + 1) ∧
    ∃ b d : ℕ, 0 < d ∧ d ∣ 2 * a + 1 ∧
      Nat.card (Outer (ReeTag.G2.reeGamma K a)) = 3 ^ b * d := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, -, ⟨⟨P, hPp, hPmax⟩, rfl⟩, hstab, hUn,
    -, hNUV⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨-, -, -, -, -, -, -, hΦ₀, π, -, hπs, hπker, e₀, he₀, hT₀⟩ :=
    small_Ree_positive_Frattini_quotient a ha K hK
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set B' := (ReeTag.G2.reeFixedBorel K a).subgroupOf Γ with hB'
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf Γ with hU'
  set n' : Γ := ⟨_, hn⟩ with hn'
  have hUΓ : ReeTag.G2.reeFixedPosUnipotent K a ≤ Γ := ReeTag.reeFixedPosUnipotent_le_reeGamma
  have hHΓ : ReeTag.G2.reeFixedTorus K a ≤ Γ :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  have hq : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
  have hq3 : 3 ≤ (3 ^ (2 * a + 1)) ^ 3 := hq.trans (Nat.le_self_pow (by norm_num) _)
  have hΩ : 3 ≤ Nat.card (Γ ⧸ B') := by
    rw [hcardΩ]
    omega
  set ι : U' ≃* ReeTag.G2.reeFixedPosUnipotent K a := Subgroup.subgroupOfEquivOfLe hUΓ with hι
  set π' : U' →* Multiplicative K := π.comp ι.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp ι.surjective
  have hΦ' : frattini U' = π'.ker := by
    rw [frattini_eq_comap_mulEquiv ι, hπ', ← MonoidHom.comap_ker, hπker, hΦ₀]
  set e : Additive (U' ⧸ frattini U') ≃+ K := MulEquiv.toAdditiveLeft
    ((QuotientGroup.quotientMulEquivOfEq hΦ').trans
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ's)) with he
  have hee : ∀ x : U', e (Additive.ofMul (x : U' ⧸ frattini U')) =
      e₀ (Additive.ofMul (ι x : ReeTag.G2.reeFixedPosUnipotent K a ⧸
        frattini (ReeTag.G2.reeFixedPosUnipotent K a))) := fun x => by
    rw [he₀]
    rfl
  have hT : (((Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
      Set Γ)).subgroupOf (Subgroup.normalizer (U' : Set Γ))).map
        U'.normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K := by
    rw [← hT₀]
    ext f
    constructor
    · rintro ⟨φ, ⟨t, ht, rfl⟩, rfl⟩
      have htH : ((t : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a := by
        have h : (t : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
            Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
              Set Γ) :=
          Subgroup.mem_inf.2 ⟨t.2, ht⟩
        rw [hNUV] at h
        exact h
      exact ⟨ReeTag.G2.reeFixedTorusConj K a ⟨_, htH⟩, ⟨_, rfl⟩,
        (frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl).symm⟩
    · rintro ⟨φ, ⟨h, rfl⟩, rfl⟩
      have hmem : (⟨h, hHΓ h.2⟩ : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
          Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) : Set Γ) := by
        rw [hNUV]
        exact h.2
      exact ⟨U'.normalizerMonoidHom ⟨_, (Subgroup.mem_inf.1 hmem).1⟩,
        ⟨⟨_, (Subgroup.mem_inf.1 hmem).1⟩, (Subgroup.mem_inf.1 hmem).2, rfl⟩,
        frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl⟩
  have hUξ : U' ≤ MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B') := by
    rw [hstab]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hx
  have hUn' : (U'.subgroupOf (MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B'))).Normal := by
    rw [hstab]
    exact hUn
  have hw : n' • (QuotientGroup.mk 1 : Γ ⧸ B') ≠ QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact hηξ
  have : Finite Γ := inferInstance
  exact Sylow_scalar_Frattini_outer_prime_support hΩ (QuotientGroup.mk 1 : Γ ⧸ B')
    (p := 3) ⟨U', hPp, hPmax⟩ hUξ hUn' (fun ω ω' hω hω' => (hreg ω ω' hω hω').exists) n' hw
    (n := 2 * a + 1) (by omega) hK e hT

theorem small_Ree_automorphism_involutions_inner (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Odd (Nat.card (Outer (ReeTag.G2.reeGamma K a))) ∧
    ∀ α : MulAut (ReeTag.G2.reeGamma K a), orderOf α = 2 →
      ∃! z : ReeTag.G2.reeGamma K a, orderOf z = 2 ∧ α = MulAut.conj z := by
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  obtain ⟨-, b, d, -, hd, hcard⟩ := small_Ree_outer_prime_support a ha K hK
  have hodd : Odd (Nat.card (Outer Γ)) := by
    rw [hcard]
    exact (Odd.pow (by decide : Odd 3)).mul (Odd.of_dvd_nat (by simp) hd)
  refine ⟨hodd, fun α hα => ?_⟩
  have hZ := (small_Ree_fixed_group_center_trivial a K hK).1
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    intro z₁ z₂ h
    have hc : z₂⁻¹ * z₁ ∈ Subgroup.center Γ := Subgroup.mem_center_iff.2 fun g => by
      have hg := DFunLike.congr_fun h g
      rw [MulAut.conj_apply, MulAut.conj_apply] at hg
      calc g * (z₂⁻¹ * z₁) = z₂⁻¹ * (z₂ * g * z₂⁻¹) * z₁ := by group
        _ = z₂⁻¹ * (z₁ * g * z₁⁻¹) * z₁ := by rw [hg]
        _ = z₂⁻¹ * z₁ * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hαi : α ∈ inner Γ := by
    have h2 : orderOf (QuotientGroup.mk' (inner Γ) α) ∣ 2 :=
      hα ▸ orderOf_map_dvd (QuotientGroup.mk' (inner Γ)) α
    have hodd' : orderOf (QuotientGroup.mk' (inner Γ) α) ∣ Nat.card (Outer Γ) :=
      orderOf_dvd_natCard _
    have h1 : orderOf (QuotientGroup.mk' (inner Γ) α) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd (even_iff_two_dvd.2 hodd') (Nat.not_even_iff_odd.2 hodd)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨z, rfl⟩ := hαi
  refine ⟨z, ⟨?_, rfl⟩, fun z' hz' => (hinj hz'.2).symm⟩
  rw [← hα]
  exact (orderOf_injective _ hinj z).symm

end CFSG.ComponentClassification.CatalogueBSmallRee

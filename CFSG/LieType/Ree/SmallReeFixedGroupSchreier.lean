module

public import CFSG.LieType.Ree.SmallReeBorelCosetAction
public import CFSG.LieType.Ree.SmallReeFrattini
public import CFSG.LieType.Ree.SmallReeSylowTorusSchreier

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Transport

variable {P Q : Type*} [Group P] [Group Q] {K : Type*} [Field K]

theorem map_frattini_mulEquiv (ι : P ≃* Q) : (frattini P).map ι.toMonoidHom = frattini Q := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · have h := frattini_le_comap_frattini_of_surjective (φ := ι.symm.toMonoidHom) ι.symm.surjective
    exact ⟨ι.symm x, h hx, by simp⟩

theorem frattini_eq_comap_mulEquiv (ι : P ≃* Q) :
    frattini P = (frattini Q).comap ι.toMonoidHom := by
  rw [← map_frattini_mulEquiv ι, Subgroup.comap_map_eq_self_of_injective ι.injective]

theorem frattiniScalarRep_eq_of_comm (ι : P ≃* Q) (e : Additive (P ⧸ frattini P) ≃+ K)
    (e' : Additive (Q ⧸ frattini Q) ≃+ K)
    (he : ∀ x : P, e (Additive.ofMul (x : P ⧸ frattini P)) =
      e' (Additive.ofMul (ι x : Q ⧸ frattini Q)))
    {α : MulAut P} {β : MulAut Q} (h : ∀ x, ι (α x) = β (ι x)) :
    frattiniScalarRep e α = frattiniScalarRep e' β := by
  have key : ∀ y, (frattiniScalarRep e α).toAdd y = (frattiniScalarRep e' β).toAdd y := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (e.symm y))
    have hy : e.symm y = Additive.ofMul (x : P ⧸ frattini P) := by
      rw [hx]
      rfl
    have hy' : e'.symm y = Additive.ofMul (ι x : Q ⧸ frattini Q) := by
      rw [AddEquiv.symm_apply_eq, ← he, ← hy, AddEquiv.apply_symm_apply]
    rw [frattiniScalarRep_apply, frattiniScalarRep_apply, hy, hy', toMul_ofMul, toMul_ofMul]
    change e (Additive.ofMul (quotientAutomorphism (frattini P) α
        (QuotientGroup.mk' (frattini P) x))) =
      e' (Additive.ofMul (quotientAutomorphism (frattini Q) β
        (QuotientGroup.mk' (frattini Q) (ι x))))
    rw [quotientAutomorphism_apply, quotientAutomorphism_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, he, h]
  exact Multiplicative.toAdd.injective (AddEquiv.ext key)

end Transport

theorem small_Ree_fixed_group_Schreier
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Group.IsSolvable (Outer (ReeTag.G2.reeGamma K a)) := by
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
  exact small_Ree_Sylow_torus_Schreier_criterion hΩ (QuotientGroup.mk 1 : Γ ⧸ B')
    (p := 3) ⟨U', hPp, hPmax⟩ hUξ hUn' (fun ω ω' hω hω' => (hreg ω ω' hω hω').exists) n' hw
    (n := 2 * a + 1) (by omega) hK e hT

end CFSG.LieType.Ree

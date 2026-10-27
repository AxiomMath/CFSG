module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModIso
public import CFSG.GH74.GLS.IVK.Proofs2.NatModNat
public import CFSG.GH74.GLS.IVK.Proofs2.NatModDickson
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK

section Final

theorem exists_isNatIso_of_model {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ n) {K : Type} [Group K] (eK : K ≃* SL2 F)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρK : Representation (ZMod p) K V) (hρ : Function.Injective ρK)
    (hdim : Module.finrank (ZMod p) V = 2 * n) :
    ∃ Φ : (Fin 2 → F) ≃+ V, IsNatIso (eK : K →* SL2 F) ρK Φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite (ZMod p)
  let σ : Representation (ZMod p) (SL2 F) V := ρK.comp (eK.symm : SL2 F →* K)
  have hσ : Function.Injective σ := hρ.comp eK.symm.injective
  have hσneg : ∀ v, σ (-1) v = -v := natMod_neg_one hp hp2 hF σ hσ hdim
  have hV : Nat.card V = Nat.card F ^ 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hdim, Nat.card_zmod, mul_comm, pow_mul, ← hF] at h1
    exact h1
  have hD : OddSylowStmt F := fun S h1 h2 =>
    exists_subgroup_card_eq_of_odd_card_ge hp hp2 hF S h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_natIso hp hp2 hF hD σ hσ hσneg hV
  refine ⟨Φ, fun k v => ?_⟩
  have h := hΦ (eK k) v
  simpa [σ] using h

theorem ivk_11_1b_nat : IVK_11_1b_nat := by
  intro p n hp hp2 H _ _ K _ hK V _ _ _ ρ hρ hdim
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ := hK
  have hFcard' : Nat.card F = p ^ n := hFcard
  let eK : K ≃* SL2 F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have hρK : Function.Injective (resRep ρ K) := hρ.comp K.subtype_injective
  obtain ⟨Φ, hΦ⟩ := exists_isNatIso_of_model hp hp2 hFcard' eK (resRep ρ K) hρK hdim
  have hψ : Function.Surjective (eK : K →* SL2 F) := eK.surjective
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := Finite.one_lt_card (α := F)
      rw [hFcard'] at this
      simp at this
    · exact h
  have : Nontrivial V :=
    Module.nontrivial_of_finrank_pos ((by omega : 0 < 2 * n).trans_eq hdim.symm)
  refine ⟨?_, ?_, ?_⟩
  · exact (Representation.irreducible_iff_isSimpleModule_asModule _).1
      (isIrreducible_of_transitive _ (fun v w hv hw => hΦ.exists_apply_eq hψ hv hw))
  · exact ⟨F, inferInstance, inferInstance, hFcard',
      ⟨((RingEquiv.ofBijective (scalarRingHom hΦ) (scalarRingHom_bijective hψ hΦ)).trans
        (Representation.IntertwiningMap.equivAlgEnd (resRep ρ K)).toRingEquiv).symm⟩⟩
  · intro V' _ _ _ ρ' hρ' hdim'
    obtain ⟨Φ', hΦ'⟩ := exists_isNatIso_of_model hp hp2 hFcard' eK (resRep ρ' K)
      (hρ'.comp K.subtype_injective) hdim'
    exact hΦ.nonempty_linearEquiv hΦ'

end Final

end CFSG.GH74.GLS.IVK.Proofs2

module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem primeResidual_eq_top_of_isPComponent [Finite X] {L C : Subgroup X} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) : CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L C hLC).mp hL).2.1

theorem card_support_action_le [Finite X] {M Je : Subgroup X} {r k : ℕ} (hk : 7 ≤ k)
    (hkr : k ≤ r) (hr6 : r ≠ 6) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ)
    (hJeN : Je ≤ normalizer (M : Set X)) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤)
    (hJeperf : ⁅Je, Je⁆ = Je) {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = k)
    (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup β) {f : X} (hfJe : f ∈ Je)
    (hρf : ρ ⟨f, hJeN hfJe⟩ ≠ 1)
    (hcase : r = k ∨ ∃ t : X, t ∈ normalizer (M : Set X) ∧ t * t = 1 ∧ Je ≤ M ∧
      Je ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X)))) :
    (ρ ⟨f, hJeN hfJe⟩).support.card =
      ((χ ((⟨f, hfJe⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup β) :
        Perm β).support.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eJe : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin k) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  set f' : ↥Je := ⟨f, hfJe⟩ with hf'def
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rcases hcase with hrk | ⟨t, htM, htt, hJeM, hJeC, hJepc⟩
  · subst hrk
    have hA : ∀ x : ↥Je, ρ (inclusion hJeN x) ∈ alternatingGroup (Fin r) := by
      intro x
      have hperf : Group.IsPerfect ↥Je := (Subgroup.isPerfect_iff).mpr hJeperf
      have h1 := Abelianization.commutator_subset_ker
        (Perm.sign.comp (ρ.comp (inclusion hJeN)))
      rw [Group.IsPerfect.commutator_eq_top] at h1
      exact h1 (mem_top x)
    let φ : ↥Je →* alternatingGroup (Fin r) :=
      (ρ.comp (inclusion hJeN)).codRestrict (alternatingGroup (Fin r)) hA
    have hφf : φ f' ≠ 1 := by
      intro h
      apply hρf
      have h1 := congrArg Subtype.val h
      exact h1
    obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres (by omega) eJe φ ⟨f', hφf⟩
      (Q := ⊤) (fun _ => mem_top _) (by
        rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin])
    let Ψ : alternatingGroup β ≃* (⊤ : Subgroup (alternatingGroup (Fin r))) := χ.symm.trans ψ
    have hle : (⊤ : Subgroup (alternatingGroup (Fin r))) ≤ fixAlt 1 := by
      intro x _
      rw [mem_fixAlt]
      simp
    have h1 := card_support_of_le_fixAlt hk (by simp) hle hβ Ψ
      (χ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je))
    have h2 : Ψ (χ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je)) = ψ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je) := by
      change ψ (χ.symm (χ _)) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h2, hψ] at h1
    rw [← h1]
    rfl
  · set π : ↥M →* alternatingGroup (Fin r) :=
      θM.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hπdef
    obtain ⟨τ, hP, hτk⟩ := exists_perm_of_fixed_component htM htt hJeM hJeC hJepc (by omega)
      (by omega) hr6 eJe θM
    let φ : ↥Je →* alternatingGroup (Fin r) := π.comp (inclusion hJeM)
    set P := (Je.subgroupOf M).map π with hPdef
    have hρin : ρ ⟨f, hJeN hfJe⟩ = ((φ f' : alternatingGroup (Fin r)) : Perm (Fin r)) :=
      hρ.apply_of_mem (by omega) (inclusion hJeM f')
    have hφf : φ f' ≠ 1 := by
      intro h
      apply hρf
      rw [hρin, h]
      rfl
    have hQc : Nat.card P ≤ k.factorial / 2 := by
      have h1 := Subgroup.card_le_of_le hP
      rwa [card_fixAlt (by omega), hτk] at h1
    obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres (by omega) eJe φ ⟨f', hφf⟩ (Q := P)
      (fun x => ⟨inclusion hJeM x, x.2, rfl⟩) hQc
    let Ψ : alternatingGroup β ≃* P := χ.symm.trans ψ
    have h1 := card_support_of_le_fixAlt hk hτk hP hβ Ψ (χ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je))
    have h2 : Ψ (χ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je)) = ψ (f' : ↥Je ⧸ pPrimeCore 2 ↥Je) := by
      change ψ (χ.symm (χ _)) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h2, hψ] at h1
    rw [hρin, ← h1]

end CFSG.ComponentClassification.SolMax

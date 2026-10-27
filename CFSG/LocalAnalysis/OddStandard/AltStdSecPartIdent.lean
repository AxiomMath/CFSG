module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2a
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootComp

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.LocalAnalysis.ComponentInitial

section Normal

variable {n : ℕ}

theorem eq_altSub_of_normal_quasisimple_sym {t : Perm (Fin n)} (ht : orderOf t = 2)
    {K : Subgroup (Perm (Fin n))} (hKt : K ≤ centralizer ({t} : Set (Perm (Fin n))))
    (hKn : ∀ c ∈ centralizer ({t} : Set (Perm (Fin n))), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    {f : ℕ} (hf : 5 ≤ f) (eK : K ≃* alternatingGroup (Fin f)) :
    K = altSub (Finset.univ.filter fun i => t i = i) ∧
      5 ≤ (Finset.univ.filter fun i => t i = i).card := by
  classical
  have hcN : centralizer ({t} : Set (Perm (Fin n))) = normalizer (zpowers t : Set (Perm (Fin n))) :=
    centralizer_singleton_eq_normalizer_zpowers ht
  have hle : K ≤ (⊤ : Subgroup (Perm (Fin n))) ⊓ normalizer (zpowers t : Set (Perm (Fin n))) := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    rw [← hcN]
    exact hKt hk
  have hnormal : (K.subgroupOf ((⊤ : Subgroup (Perm (Fin n))) ⊓
      normalizer (zpowers t : Set (Perm (Fin n))))).Normal := by
    refine ⟨fun k hk g => ?_⟩
    have hk' : (k : Perm (Fin n)) ∈ K := hk
    obtain ⟨-, hgN⟩ := Subgroup.mem_inf.1 g.2
    have hgC : (g : Perm (Fin n)) ∈ centralizer ({t} : Set (Perm (Fin n))) := by
      rw [hcN]
      exact hgN
    exact hKn _ hgC _ hk'
  have hcomp : CFSG.Assembly.IsComponentOf K ((⊤ : Subgroup (Perm (Fin n))) ⊓
      normalizer (zpowers t : Set (Perm (Fin n)))) :=
    ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnormal (CFSG.Assembly.IsSubnormal.refl _),
      isQuasisimple_of_alt hf eK⟩
  obtain ⟨hdeg, hK⟩ := ordinary_permutation_local_component_fixed_support
    (T := ⊤) (fun _ _ => Subgroup.mem_top _) Nat.prime_two (fun _ _ => Subgroup.mem_top _)
    (isPGroup_zpowers_of_orderOf_eq_two ht) hcomp
  have hset : MulAction.fixedPoints (zpowers t) (Fin n) =
      ((Finset.univ.filter fun i => t i = i : Finset (Fin n)) : Set (Fin n)) := by
    ext i
    rw [mem_fixedPoints_zpowers_iff]
    simp
  refine ⟨?_, ?_⟩
  · rw [hK]
    convert map_ofSubtype_alternatingGroup_eq_altSub
      (fun i => i ∈ MulAction.fixedPoints (zpowers t) (Fin n))
      (Finset.univ.filter fun i => t i = i) (fun i => by
        rw [Finset.mem_filter, mem_fixedPoints_zpowers_iff]
        simp)
  · rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hdeg
    exact hdeg

@[expose] def NormalAltIdentSym (n f : ℕ) : Prop :=
  ∀ t : Perm (Fin n), orderOf t = 2 → ∀ K : Subgroup (Perm (Fin n)),
    K ≤ alternatingGroup (Fin n) → K ≤ centralizer ({t} : Set (Perm (Fin n))) →
    (∀ c ∈ centralizer ({t} : Set (Perm (Fin n))), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
    Nonempty (K ≃* alternatingGroup (Fin f)) → K = altSub (fixFin t) ∧ (fixFin t).card = f

theorem normalAltIdentSym_of_five_le {f : ℕ} (hf : 5 ≤ f) : NormalAltIdentSym n f := by
  intro t ht K hKA hKt hKn ⟨eK⟩
  obtain ⟨hK, h5⟩ := eq_altSub_of_normal_quasisimple_sym ht hKt hKn hf eK
  refine ⟨hK, ?_⟩
  have h5' : 5 ≤ (fixFin t).card := h5
  have h1 : Nat.card K = f.factorial / 2 := card_eq_of_equiv_alt (by omega) eK
  have h2 : Nat.card K = (fixFin t).card.factorial / 2 :=
    card_eq_of_equiv_alt (by omega) ((MulEquiv.subgroupCongr hK).trans (altSubEquiv (fixFin t)))
  have h3 : 2 ∣ f.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : 2 ∣ (fixFin t).card.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h6 : (fixFin t).card.factorial = f.factorial := by omega
  exact (Nat.factorial_inj (by omega)).1 h6

end Normal

end CFSG.OddStandard.AltStdSec

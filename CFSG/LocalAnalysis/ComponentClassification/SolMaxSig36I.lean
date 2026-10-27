module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36G

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

structure PumpE (S : Sig36 X t J n e E D) (e₀ : X) (L₀ F N : Subgroup X) (r : ℕ)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
    (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
    (DN : Finset (Fin r)) : Prop where
  L₀J : L₀ ≤ J
  L₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X)
  L₀pc : IsPComponent 2 (L₀.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X)))
  FL₀ : F ≤ L₀
  F4 : Nat.card F = 4
  Fsq : ∀ x ∈ F, x * x = 1
  FD : ∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω
  NC : N ≤ centralizer ({e₀} : Set X)
  Npc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X)))
  L₀N : L₀ ≤ N ⊔ N.map (MulAut.conj t).toMonoidHom
  L₀NN : L₀ ≤ normalizer (N : Set X)
  kr : n - 4 ≤ r
  rn : r ≤ n
  perm : IsPermAction θN ρN
  case : r = n - 4 ∨ (N.map (MulAut.conj t).toMonoidHom = N ∧
    IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({t} : Set X))))
  τk : r - τ'.support.card = n - 4
  iso : ∃ ψ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* fixAlt τ', ∀ x : ↥L₀,
    (((ψ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : fixAlt τ') : alternatingGroup (Fin r)) :
      Perm (Fin r)) = ρN ⟨x, L₀NN x.2⟩
  DN4 : DN.card = 4
  DNfix : DN ⊆ τ'.supportᶜ
  Fsupp : ∀ (x : X) (hx : x ∈ F), ∀ ω ∉ DN, ρN ⟨x, L₀NN (FL₀ hx)⟩ ω = ω

theorem exists_pumpE (S : Sig36 X t J n e E D) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    ∃ (L₀ F N : Subgroup X) (r : ℕ) (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
      (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
      (DN : Finset (Fin r)), S.PumpE e₀ L₀ F N r θN ρN τ' DN := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have he₀J : e₀ ∈ J := S.le he₀E
  have h4 := S.card_support_coreImage_E he₀E he₀1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨L₀, hL₀J, hL₀pc, hinv, -, χ, hχ⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 e (le_normalizer he₀J) he₀2
      he₀J (by rw [mul_inv_cancel]; exact one_mem _) (by rw [h4]; omega)
  have hβ : Fintype.card ↥((coreImage e he₀J).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
  let eL₀ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin (n - 4)) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hL₀Ct : L₀ ≤ centralizer ({t} : Set X) := (hL₀J.trans inf_le_left).trans S.pair.1.2.1
  have hL₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X) :=
    le_inf hL₀Ct (hL₀J.trans inf_le_right)
  have hkodd : Odd (n - 4) := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    exact ⟨a - 2, by omega⟩
  obtain ⟨N, r, hNC, hNpc, hL₀N, -, hkr, hrn, ⟨θN⟩, hcase⟩ :=
    exists_pump_data hPump hN1 S.nonab S.kProper S.unbal S.notU S.pair.2.2.2.1 he₀o S.pair.1.1
      hte₀ hL₀C hL₀pc (by omega) hkodd eL₀
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N) (by omega) (by omega) θN
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc hte₀
  have hNtN : N.map (MulAut.conj t).toMonoidHom ≤ normalizer (N : Set X) := by
    by_cases hfix : N.map (MulAut.conj t).toMonoidHom = N
    · rw [hfix]
      exact le_normalizer
    · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hNC hNtC hNpc hNtpc
        (Ne.symm hfix) hz).1
  have hL₀NN : L₀ ≤ normalizer (N : Set X) := hL₀N.trans (sup_le le_normalizer hNtN)
  obtain ⟨F, DF, hFJ, hF4, hFsq, hDF, hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hsuppD : (coreImage e he₀J).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨e₀, he₀J⟩ he₀E ω hωD)
  have hDFc : DF ⊆ (coreImage e he₀J).supportᶜ := by
    intro ω hω
    rw [Finset.mem_compl]
    intro h
    exact Finset.disjoint_left.mp hdisj (hsuppD h) hω
  have hFL₀ : F ≤ L₀ := by
    intro x hx
    have hxJ : x ∈ J := hFJ hx
    refine hinv x hxJ ?_ ⟨1, by rw [pow_one, sq]; exact hFsq x hx⟩ ?_
    · exact (mem_centralizer_iff.mp (hFE hx) e₀ he₀E).symm
    · intro ω hω
      refine hDFc ?_
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hFs ⟨x, hxJ⟩ hx ω hωF)
  have hperf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent hL₀C hL₀pc
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin (n - 4)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (alternatingGroup (Fin (n - 4))) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact eL₀.toEquiv.nontrivial
  have hne := exists_ne_one_of_pump hNC hNpc hte₀ hL₀N hL₀Ct hperf hL₀q (by omega) hρN hL₀NN
  have hcase' : r = n - 4 ∨ ∃ t' : X, t' ∈ normalizer (N : Set X) ∧ t' * t' = 1 ∧ L₀ ≤ N ∧
      L₀ ≤ centralizer ({t'} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({t'} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨t, mem_normalizer_iff_map_conj_eq.mpr hfix, ht2, ?_, hL₀Ct, hpc⟩
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
  obtain ⟨τ', hτ'k, ψ, hψ⟩ := exists_image_equiv (by omega) hkr (by omega) θN hρN hL₀NN
    (primeResidual_eq_top_of_isPComponent hL₀C hL₀pc) hperf hβ χ hne hcase'
  obtain ⟨DN, hDN4, hDNfix, hDNs⟩ := exists_support_of_mulEquiv_fixAlt (by omega) hβ hτ'k
    (χ.symm.trans ψ) (DF.subtype (· ∈ (coreImage e he₀J).supportᶜ))
  have hDYcard : (DF.subtype (· ∈ (coreImage e he₀J).supportᶜ)).card = 4 := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun ω hω => hDFc hω), hDF]
  refine ⟨L₀, F, N, r, θN, ρN, τ', DN, ⟨hL₀J.trans inf_le_left, hL₀C, hL₀pc, hFL₀, hF4,
    hFsq, ⟨DF, hDF, hFs⟩, hNC, hNpc, hL₀N, hL₀NN, hkr, hrn, hρN, hcase, hτ'k, ⟨ψ, hψ⟩,
    by rw [hDN4, hDYcard], hDNfix, ?_⟩⟩
  intro x hx ω hω
  have hxL₀ : x ∈ L₀ := hFL₀ hx
  have hxJ : x ∈ J := hFJ hx
  have hχx : ∀ y ∉ DF.subtype (· ∈ (coreImage e he₀J).supportᶜ),
      ((χ ((⟨x, hxL₀⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup _) :
        Perm ↥((coreImage e he₀J).supportᶜ : Finset (Fin n))) y = y := by
    intro y hy
    rw [Finset.mem_subtype] at hy
    have h1 := congrArg (fun p : Perm (Fin n) => p y.1) (hχ ⟨x, hxL₀⟩ hxJ)
    simp only at h1
    rw [Perm.ofSubtype_apply_of_mem _ y.2] at h1
    have h2 : coreImage e hxJ y.1 = y.1 := hFs ⟨x, hxJ⟩ hx y.1 hy
    exact Subtype.ext (h1.trans h2)
  have h1 := hDNs (χ ((⟨x, hxL₀⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) hχx ω hω
  have h2 : (χ.symm.trans ψ) (χ ((⟨x, hxL₀⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) =
      ψ ((⟨x, hxL₀⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    change ψ (χ.symm (χ _)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h2, hψ ⟨x, hxL₀⟩] at h1
  exact h1

end Sig36

end CFSG.ComponentClassification.SolMax

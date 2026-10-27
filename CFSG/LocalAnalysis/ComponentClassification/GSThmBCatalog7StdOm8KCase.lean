module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Cases
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Indep

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

attribute [local instance] finite_linearEquiv

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {t : H}

theorem twentyfive_le {p f : ℕ} (h5 : 5 ≤ p ^ f) : 25 ≤ p ^ (2 * f) := by
  rw [pow_mul']
  exact le_trans (by norm_num) (Nat.pow_le_pow_left h5 2)

theorem k_caseA {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (D : InvData G Q Θ t) (β : Kˣ) (hβ : (D.c : K) = (β : K) ^ 2) (Kc : Subgroup H)
    (hKC : Kc ≤ centralizer ({t} : Set H)) (hKG : Kc ≤ G)
    (hKc : IsPComponent 2 (Kc.subgroupOf (centralizer ({t} : Set H))))
    (huniq : ∀ M : Subgroup H, M ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set H))) → M = Kc)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hKm : Blueprint.LieModel (Kc ⧸ pPrimeCore 2 Kc) .PSL 2 p (2 * f)) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hr.eq_two_or_odd'.resolve_left hr2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨W, W', ι, hcompl, hnd, hnd', hι⟩ := caseA_data hr hr2 he hK hQ hdim D β hβ
  obtain ⟨M, hM, hMK, hMε⟩ := corr_down D ι Kc hKC hKG hKc
  subst hMK
  obtain ⟨U, U', ψ, hcU, hndU, hndU', hψ, L, hL, hML⟩ :=
    left_normal_form D ι hcompl hnd hnd' hι M hMε
  have hsum : finrank K U + finrank K U' = 8 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcU, hdim]
  have hU3 : 3 ≤ finrank K U := by
    by_contra h
    exact CatalogueBOrthogonal.orthogonal_small_no_pComponent _ h2 hndU (by omega) 2 L hL
  rcases lt_or_ge (finrank K U) 5 with hlt | hge
  · by_cases hex : ∃ L' : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)),
        IsPComponent 2 L'
    · obtain ⟨L', hL'⟩ := hex
      obtain ⟨M', hM', hM'ε, hM'C, -, hM'c⟩ := corr_up D ψ
        ((⊥ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))).prod L')
        (isPComponent_bot_prod hL')
      have h1 := corr_inj D ψ M' M hM' hM (huniq _ hM'C hM'c)
      rw [hM'ε, hML] at h1
      apply ne_bot_of_pComponent hL
      rw [eq_bot_iff]
      intro x hx
      have hx' : ((x, 1) : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) ∈ L.prod ⊥ :=
        ⟨hx, Subgroup.one_mem _⟩
      rw [← h1] at hx'
      exact hx'.1
    · have h4 : finrank K U' = 4 := by
        by_contra h4
        exact hex (exists_pComponent_of_dim hodd hndU' (Or.inl (by omega)))
      have h3 : Nat.card K = 3 := by
        by_contra h3
        exact hex (exists_pComponent_of_dim hodd hndU' (Or.inr (Or.inl ⟨h4, h3⟩)))
      have hU4 : finrank K U = 4 := by omega
      have hLq := (isComponent_of_pComponent hodd hndU hL).1
      obtain ⟨hKq, ⟨eK⟩⟩ := quotient_of_left D ψ M L hLq hML
      have hKZ := lieModel_center_of_pPrimeCore hKq hKm
      have h25 := twentyfive_le h5
      by_cases hS : ∃ S : Submodule K U, finrank K S = 2 ∧ ∀ x ∈ S, (Q.comp U.subtype) x = 0
      · have h1 := pow_eq_of_lieModel_psl_two hp hp2 hr hr2 hKZ
          (LieType.CurtisTits.lieModel_of_mulEquiv eK.symm
            (pComponent_split_four hr hr2 he hK hndU hU4 hS hL))
        rw [← hK, h3] at h1
        omega
      · have h1 := pow_eq_of_lieModel_psl_two hp hp2 hr hr2 hKZ
          (LieType.CurtisTits.lieModel_of_mulEquiv eK.symm
            (pComponent_nonsplit_four hr hr2 he hK hndU hU4 hS hL).2)
        rw [show r ^ (2 * e) = (r ^ e) ^ 2 by ring, ← hK, h3] at h1
        norm_num at h1
        omega
  · have hLc := pComponent_five_le hodd hndU hge hL
    exact false_of_five_le D ψ hψ hodd hndU hge M (by rw [hML, hLc]) hp hp2 hKm

theorem k_caseB {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (hnp : ¬ IsPlusType Q) (D : InvData G Q Θ t) (hns : ¬ IsSquare (D.c : K)) (Kc : Subgroup H)
    (hKC : Kc ≤ centralizer ({t} : Set H)) (hKG : Kc ≤ G)
    (hKc : IsPComponent 2 (Kc.subgroupOf (centralizer ({t} : Set H))))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKm : Blueprint.LieModel (Kc ⧸ pPrimeCore 2 Kc) .PSL 2 p (2 * f)) :
    p ^ f = (r ^ e) ^ 2 := by
  obtain ⟨T, _, _, ι, hT⟩ := caseB_data hr hr2 he hK hQ hdim hnp D hns
  obtain ⟨M, hM, hMK, hMε⟩ := corr_down D ι Kc hKC hKG hKc
  subst hMK
  obtain ⟨hq, hLM⟩ := hT _ hMε
  obtain ⟨hqK, ⟨eK⟩⟩ := centerQuotient_equiv D ι M hq
  have h3 := pow_eq_of_lieModel_psl_two hp hp2 hr hr2 (lieModel_center_of_pPrimeCore hqK hKm)
    (LieType.CurtisTits.lieModel_of_mulEquiv eK.symm hLM)
  have h4 : (p ^ f) ^ 2 = ((r ^ e) ^ 2) ^ 2 := by
    calc (p ^ f) ^ 2 = p ^ (2 * f) := by ring
      _ = r ^ (2 * (2 * e)) := h3
      _ = ((r ^ e) ^ 2) ^ 2 := by ring
  exact Nat.pow_left_injective (by norm_num) h4

theorem k_analysis {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (hnp : ¬ IsPlusType Q) (D : InvData G Q Θ t) (Kc : Subgroup H)
    (hKC : Kc ≤ centralizer ({t} : Set H)) (hKG : Kc ≤ G)
    (hKc : IsPComponent 2 (Kc.subgroupOf (centralizer ({t} : Set H))))
    (huniq : ∀ M : Subgroup H, M ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set H))) → M = Kc)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hKm : Blueprint.LieModel (Kc ⧸ pPrimeCore 2 Kc) .PSL 2 p (2 * f)) :
    ¬ IsSquare (D.c : K) ∧ p ^ f = (r ^ e) ^ 2 := by
  by_cases hsq : IsSquare (D.c : K)
  · exfalso
    obtain ⟨β, hβ⟩ := hsq
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hβ
      exact Units.ne_zero _ hβ
    exact k_caseA hr hr2 he hK hQ hdim D (Units.mk0 β hβ0) (by rw [Units.val_mk0, hβ, sq]) Kc
      hKC hKG hKc huniq hp hp2 h5 hKm
  · exact ⟨hsq, k_caseB hr hr2 he hK hQ hdim hnp D hsq Kc hKC hKG hKc hp hp2 hKm⟩

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

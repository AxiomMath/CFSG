module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallF

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpExactCaseInput
    (P : ∀ (X : Type) [Group X], Subgroup X → X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X), Sol78.IsSolomonPair t J 9 →
    ∀ (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (c e₀ : X) (he₀ : e₀ ∈ J),
      orderOf c = 2 → t * c = c * t → c ∈ normalizer (J : Set X) →
      c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J → (coreImage θ he₀).support.card = 4 →
    ∀ Jc : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) →
      IsPComponent 2 (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))) →
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) →
      (∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ) →
    ∀ χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
        alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)),
      (∀ (x : ↥Jc) (hx : (x : X) ∈ J),
        Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx) →
    ∀ M : Subgroup X, M ≤ centralizer ({c} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      IsPComponent 2 (Jc.subgroupOf ((M ⊔ M.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set X))) →
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M →
      M.map (MulAut.conj t).toMonoidHom = M →
      ¬ Jc ⊔ (pPrimeCore 2 ↥M).map M.subtype = M →
    ∀ a : X, orderOf a = 2 → a * c = c * a → a * t = t * a → a ∈ normalizer (J : Set X) →
      (∃ (j₀ : X) (hj₀ : j₀ ∈ J), a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J ∧
        (coreImage θ hj₀).support.card ≤ 4) →
      (∃ (j : X) (hjJ : j ∈ Jc), a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc ∧
        ((χ ((⟨j, hjJ⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))).support.card ≤ 4) →
      P X M a →
      ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype

@[expose] def SignalizerFivePumpThreeFixInput : Prop :=
  SignalizerFivePumpExactCaseInput fun X _ M a =>
    ∃ (r : ℕ) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)) (haM : a ∈ normalizer (M : Set X)),
      IsPermAction θM ρ ∧ (r = 7 ∨ r = 9) ∧ (ρ ⟨a, haM⟩).supportᶜ.card = 3

@[expose] def SignalizerFivePumpLTwoInput : Prop :=
  SignalizerFivePumpExactCaseInput fun _ _ M _ =>
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (M ⧸ pPrimeCore 2 M) .PSL 2 p f

@[expose] def SignalizerFivePumpHeldInput : Prop :=
  SignalizerFivePumpExactCaseInput fun _ _ M _ =>
    Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.He)

@[expose] def SignalizerFivePumpLThreeFourInput : Prop :=
  SignalizerFivePumpExactCaseInput fun _ _ M _ =>
    Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 3 2 2

theorem eq_one_of_fix_all_but_one {r : ℕ} {σ : Perm (Fin r)} {p : Fin r}
    (h : ∀ v, v ≠ p → σ v = v) : σ = 1 := by
  refine Equiv.ext fun v => ?_
  rw [Perm.one_apply]
  by_cases hv : v = p
  · subst hv
    by_contra hne
    have h1 := h (σ v) hne
    exact hne (σ.injective h1)
  · exact h v hv

variable {X : Type} [Group X]

theorem le_coreActionKernel_of_alt_ne_three [Finite X] {M X₀ : Subgroup X} {r : ℕ}
    (hrodd : Odd r) {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ) {a : X}
    (haM : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1)
    (h3 : (ρ ⟨a, haM⟩).supportᶜ.card ≠ 3) (hX₀N : X₀ ≤ normalizer (M : Set X))
    (hX₀O : X₀ ≤ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  set σ := ρ ⟨a, haM⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have h1 : (⟨a, haM⟩ : ↥(normalizer (M : Set X))) * ⟨a, haM⟩ = 1 := Subtype.ext ha2
    rw [h1, map_one]
  have hev : 2 ∣ σ.support.card := Perm.two_dvd_card_support (by rw [sq]; exact hσ2)
  have hfix : σ.supportᶜ.card = r - σ.support.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hle : σ.support.card ≤ r := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  by_cases h5 : 5 ≤ r - σ.support.card
  · exact hρ.le_coreActionKernel_of_fix haM ha2 h5 hX₀N hX₀O
  have h1 : σ.supportᶜ.card = 1 := by
    obtain ⟨k, hk⟩ := hrodd
    obtain ⟨m, hm⟩ := hev
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  intro x hx
  have hxN := hX₀N hx
  refine hρ.mem_coreActionKernel hxN (eq_one_of_fix_all_but_one (p := p) fun v hv => ?_)
  have hvs : v ∈ σ.support := by
    by_contra hvs
    have h2 : v ∈ σ.supportᶜ := Finset.mem_compl.mpr hvs
    rw [hp, Finset.mem_singleton] at h2
    exact hv h2
  exact hρ.apply_eq_of_mem_oddCore haM ha2 hX₀N hX₀O hx v hvs

theorem signalizerFivePumpExactInput_of_cases (hbal : Sol78.BalanceTwoComponentInput)
    (hTB : SignalizerFivePumpTBInput) (h3 : SignalizerFivePumpThreeFixInput)
    (hL2 : SignalizerFivePumpLTwoInput) (hHe : SignalizerFivePumpHeldInput)
    (hL34 : SignalizerFivePumpLThreeFourInput) : SignalizerFivePumpExactInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hao
    omega
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oc := (pPrimeCore 2 ↥Cc).map Cc.subtype with hOcdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  by_contra hMX
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hac
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers c) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact ha2))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hc2)) hST
  have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = Cc := centralizer_zpowers_eq' c
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = Ca := centralizer_zpowers_eq' a
  rw [hCc', hCa'] at hbc
  obtain ⟨hXN, hcc⟩ := hbc M ⟨hMC, hMpc⟩
  obtain ⟨haN', -, -⟩ := hcc hMX
  have haM : a ∈ normalizer (M : Set X) := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp haN'
    obtain ⟨hga, hgN⟩ := mem_inf.mp hg
    rcases eq_one_or_eq_of_mem_zpowers ha2 hga with h | h
    · exact absurd (Subtype.ext h) hg1
    · exact h ▸ hgN
  have hOMC : (pPrimeCore 2 ↥M).map M.subtype ≤ Oc := pPrimeCore_le_of_isPComponent hMC hMpc
  have hXNM : Oa ⊓ Cc ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN
  have hX : ¬ Oa ⊓ Cc ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hMX ((commutator_le_of_le_coreActionKernel h).trans hOMC)
  have hcase : ∀ (P : ∀ (X : Type) [Group X], Subgroup X → X → Prop),
      SignalizerFivePumpExactCaseInput P → P X M a → False := fun P hP hPMa =>
    hMX (hP X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
      hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hPMa)
  have halt : ∀ r : ℕ, Odd r → 7 ≤ r → (r = 7 ∨ r = 9) →
      Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin r)) → False := by
    rintro r hr hr7 hr79 ⟨θM⟩
    obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
    by_cases h3a : (ρ ⟨a, haM⟩).supportᶜ.card = 3
    · exact hcase _ h3 ⟨r, θM, ρ, haM, hρ, hr79, h3a⟩
    · exact hX (le_coreActionKernel_of_alt_ne_three hr hρ haM ha2 h3a hXNM inf_le_left)
  rcases hTB X hnab hKP hunb hnU c a M hc hao hac hMC hMpc hMX with
    ⟨k, hk, hk9, hθ⟩ | (hθ | hL) | (hHe' | hL')
  · have hkn : k ≤ 9 := hpair.2.2.2.1 c M k ⟨hc, hMC, hMpc, hθ⟩ hk
    exact halt k hk (by omega) (Or.inr (by omega)) hθ
  · exact halt 7 (by decide) le_rfl (Or.inl rfl) hθ
  · exact hcase _ hL2 hL
  · exact hcase _ hHe hHe'
  · exact hcase _ hL34 hL'

end CFSG.ComponentClassification.SolMax

module

public import CFSG.CGT.T75M.StageC
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec3IsoParts
public import CFSG.CGT.Timmesfeld75.BenderInputs5
public import CFSG.CGT.T75M.StageB

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {a : ℕ}

section Stage

theorem normIn_conj_eq (hKL : SzTriangleInput)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : SzData T T₁ a)
    (hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T)
    (h214 : Lemma214) (hInv : InvolutionClassInput) {g : G}
    (hne : conjSubgroup g T ≠ T) (hL' : normIn T (conjSubgroup g T) ≠ ⊥) :
    normIn T (conjSubgroup g T) = normIn T T₁ := by
  classical
  have hcfg := hD.sec3.cfg
  have hS' := Sec3.of_inputs h214 hInv hcfg.wc hne hL'
  have hcfg' := hS'.cfg
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  have hAn : ∀ z ∈ Subgroup.normalizer (T : Set G), conjSubgroup z (normIn T T₁) = normIn T T₁ :=
    fun z hz => conj_normIn_eq hD hB hz
  obtain ⟨t₀, ht₀T, ht₀M⟩ := IsConcreteLE.not_le_iff_exists.1 hS'.not_le_cfgM
  have hC2 : normIn T (conjSubgroup g T) ≤ normIn T T₁ := by
    intro ℓ hℓ
    obtain ⟨u, hu, rfl⟩ := exists_comm_eq hS' ht₀T ht₀M ℓ hℓ
    have huN : u ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hu).2
    have hu2 : u * u = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hcfg.wc.1 g)
      (normIn_le _ _ hu)
    exact comm_mem_normIn_of_normalizes hD (mem_normalizer_sup hKL hnab hD hB huN)
      (mem_normalizer_cfgM hD hB huN) huN hu2 t₀ ht₀T
  have hlt : normIn T (conjSubgroup g T) < T := by
    rw [lt_iff_le_and_ne]
    refine ⟨normIn_le T (conjSubgroup g T), fun h => hS'.not_le_cfgM ?_⟩
    have h1 := Cfg.normIn_le_cfgM_left T (conjSubgroup g T)
    rwa [h] at h1
  have hLlt : normIn T T₁ < T := by
    rw [lt_iff_le_and_ne]
    refine ⟨hLT, fun h => hD.sec3.not_le_cfgM ?_⟩
    have h1 := Cfg.normIn_le_cfgM_left T T₁
    rwa [h] at h1
  have hC1 : normIn T T₁ ≤ normIn T (conjSubgroup g T) := by
    by_contra hLn
    obtain ⟨ℓ, hℓL, hℓ'⟩ := IsConcreteLE.not_le_iff_exists.1 hLn
    have hℓM : ℓ ∉ cfgM T (conjSubgroup g T) := fun hM => hℓ' (by
      rw [← hcfg'.inf_cfgM]; exact ⟨hLT hℓL, hM⟩)
    have hout : ∀ t ∈ T, t ∉ normIn T (conjSubgroup g T) → t ∈ normIn T T₁ := by
      intro t htT htn
      have htM : t ∉ cfgM T (conjSubgroup g T) := fun hM => htn (by
        rw [← hcfg'.inf_cfgM]; exact ⟨htT, hM⟩)
      obtain ⟨z, -, hzN, hz⟩ := hS'.exists_mem_normalizer_conj (hLT hℓL) hℓM htT htM
      have h1 : t ∈ conjSubgroup z (normIn T T₁) := by
        rw [mem_conjSubgroup, ← hz]
        have : z⁻¹ * (z * ℓ * z⁻¹) * z = ℓ := by group
        rw [this]
        exact hℓL
      rwa [hAn z hzN] at h1
    obtain ⟨t₁, ht₁T, ht₁n⟩ := IsConcreteLE.not_le_iff_exists.1 (not_le_of_gt hlt)
    have hTL : T ≤ normIn T T₁ := by
      intro τ hτ
      by_cases hτn : τ ∈ normIn T (conjSubgroup g T)
      · have hτt : τ * t₁ ∉ normIn T (conjSubgroup g T) := fun h => ht₁n (by
          have h3 : τ⁻¹ * (τ * t₁) ∈ normIn T (conjSubgroup g T) :=
            (normIn T (conjSubgroup g T)).mul_mem
              ((normIn T (conjSubgroup g T)).inv_mem hτn) h
          simpa using h3)
        have h1 := hout _ (T.mul_mem hτ ht₁T) hτt
        have h2 := hout _ ht₁T ht₁n
        have h4 : (τ * t₁) * t₁⁻¹ ∈ normIn T T₁ :=
          (normIn T T₁).mul_mem h1 ((normIn T T₁).inv_mem h2)
        simpa using h4
      · exact hout τ hτ hτn
    exact hLlt.ne (le_antisymm hLT hTL)
  exact le_antisymm hC2 hC1

end Stage

section StageD

theorem false_of_hA1 [IsSimpleGroup G] (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (hnab : ∃ a b : G, a * b ≠ b * a) (hS : Sec3 T T₁)
    (hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁) : False := by
  have hT : IsWC T := hS.cfg.wc
  obtain ⟨t₀, ht₀T, ht₀M⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
  have ht₀L : t₀ ∉ normIn T T₁ := fun h => ht₀M (Cfg.normIn_le_cfgM_left T T₁ h)
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀L (h ▸ (normIn T T₁).one_mem)
  have hE : eqE T (normIn T T₁) = {x | IsConj t₀ x} := by
    ext x
    constructor
    · rintro ⟨g, t, htT, htL, rfl⟩
      have htM : t ∉ cfgM T T₁ := fun hM => htL (by
        rw [← hS.cfg.inf_cfgM]; exact ⟨htT, hM⟩)
      obtain ⟨z, -, -, hz⟩ := hS.exists_mem_normalizer_conj ht₀T ht₀M htT htM
      refine isConj_iff.2 ⟨g * z, ?_⟩
      rw [← hz]
      group
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      exact ⟨c, t₀, ht₀T, ht₀L, hc.symm⟩
  have ht₀E : t₀ ∈ eqE T (normIn T T₁) := ⟨1, t₀, ht₀T, ht₀L, by simp⟩
  have hTtop : T ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (elemAbelian_mul_comm hT.1 (h ▸ Subgroup.mem_top a) (h ▸ Subgroup.mem_top b))
  have hTbot : T ≠ ⊥ := hS.cfg.left_ne_bot
  obtain ⟨x₀, -, hx₀⟩ := hS.conj
  have hne : conjSubgroup x₀ T ≠ T := hx₀ ▸ hS.cfg.left_ne_right.symm
  have hL : normIn T (conjSubgroup x₀ T) ≠ ⊥ := hx₀ ▸ hS.cfg.ne
  refine false_of_oddClass hTO hBW hnab hT hTbot hne hL hTtop ht₀1 ht₀T ?_ ?_ ?_
  · intro d hd
    have := (hE ▸ (show d ∈ {x | IsConj t₀ x} from hd) : d ∈ eqE T (normIn T T₁))
    exact mul_self_eq_one_of_mem_eqE hT this
  · intro d e hd he
    have hd' : d ∈ eqE T (normIn T T₁) := hE ▸ (show d ∈ {x | IsConj t₀ x} from hd)
    have he' : e ∈ eqE T (normIn T T₁) := hE ▸ (show e ∈ {x | IsConj t₀ x} from he)
    exact orderOf_mul_cases_eqE_of_normal hT hA1 hd' he'
  · intro u hu huT v hv hc
    have hu' : u ∈ eqE T (normIn T T₁) := hE ▸ (show u ∈ {x | IsConj t₀ x} from hu)
    have hv' : v ∈ eqE T (normIn T T₁) := hE ▸ (show v ∈ {x | IsConj t₀ x} from hv)
    have hvN : v ∈ Subgroup.normalizer (T : Set G) :=
      hT.centralizer_le_normalizer huT (ne_one_of_mem_eqE hu')
        (Subgroup.mem_centralizer_singleton_iff.2 hc.eq.symm)
    exact mem_left_of_mem_eqE_of_normal hA1 hv' hvN

end StageD

section Assembly

theorem section3SzInput_of_triangle
    (hAsc : AschbacherNoPolarInput) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (h214 : Lemma214) (hInv : InvolutionClassInput) (hKL : SzTriangleInput) :
    Section3SzInput := by
  intro G _ _ _ hnab T T₁ hS a ha hiso
  have hD : SzData T T₁ a := ⟨hS, ha, hiso⟩
  have hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T :=
    fun h hh => conj_normIn_le_sup hAsc hKL hnab hD hh
  exact false_of_hA1 hTO benderWCInput_of_repo hnab hS fun g hne hL' =>
    normIn_conj_eq hKL hnab hD hB h214 hInv hne hL'

end Assembly

end CFSG.CGT.T75M

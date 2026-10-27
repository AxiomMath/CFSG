module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4NoAAssembly

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem normIn_eq_of_normal_of_card_le (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hT : IsWC T) {L : Subgroup G} (hLT : L ≤ T) (hLne : L ≠ T)
    (hAn : ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g L = L) {g : G}
    (hne : conjSubgroup g T ≠ T) (hL' : normIn T (conjSubgroup g T) ≠ ⊥)
    (hle : Nat.card (normIn T (conjSubgroup g T)) ≤ Nat.card L) :
    normIn T (conjSubgroup g T) = L := by
  have hS' := Sec3.of_inputs h214 hInv hT hne hL'
  have hlt : normIn T (conjSubgroup g T) < T := by
    rw [lt_iff_le_and_ne]
    refine ⟨normIn_le T (conjSubgroup g T), fun h => hS'.not_le_cfgM ?_⟩
    have h1 := Cfg.normIn_le_cfgM_left T (conjSubgroup g T)
    rwa [h] at h1
  have hLle : L ≤ normIn T (conjSubgroup g T) := by
    by_contra hLn
    obtain ⟨ℓ, hℓL, hℓ'⟩ := IsConcreteLE.not_le_iff_exists.1 hLn
    have hℓM : ℓ ∉ cfgM T (conjSubgroup g T) := fun hM => hℓ' (by
      rw [← hS'.cfg.inf_cfgM]; exact ⟨hLT hℓL, hM⟩)
    have hout : ∀ t ∈ T, t ∉ normIn T (conjSubgroup g T) → t ∈ L := by
      intro t htT htn
      have htM : t ∉ cfgM T (conjSubgroup g T) := fun hM => htn (by
        rw [← hS'.cfg.inf_cfgM]; exact ⟨htT, hM⟩)
      obtain ⟨z, -, hzN, hz⟩ := hS'.exists_mem_normalizer_conj (hLT hℓL) hℓM htT htM
      have h1 : t ∈ conjSubgroup z L := by
        rw [mem_conjSubgroup, ← hz]
        have : z⁻¹ * (z * ℓ * z⁻¹) * z = ℓ := by group
        rw [this]
        exact hℓL
      rwa [hAn z hzN] at h1
    obtain ⟨t₀, ht₀T, ht₀n⟩ := IsConcreteLE.not_le_iff_exists.1 (not_le_of_gt hlt)
    have hTL : T ≤ L := by
      intro τ hτ
      by_cases hτn : τ ∈ normIn T (conjSubgroup g T)
      · have hτt : τ * t₀ ∉ normIn T (conjSubgroup g T) := fun h => ht₀n (by
          have h3 : τ⁻¹ * (τ * t₀) ∈ normIn T (conjSubgroup g T) :=
            (normIn T (conjSubgroup g T)).mul_mem ((normIn T (conjSubgroup g T)).inv_mem hτn) h
          simpa using h3)
        have h1 := hout _ (T.mul_mem hτ ht₀T) hτt
        have h2 := hout _ ht₀T ht₀n
        have h4 : (τ * t₀) * t₀⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem h2)
        simpa using h4
      · exact hout τ hτ hτn
    exact hLne (le_antisymm hLT hTL)
  exact (Subgroup.eq_of_le_of_card_ge hLle hle).symm

theorem false_of_normal_of_maxPair [IsSimpleGroup G]
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hnab : ∃ a b : G, a * b ≠ b * a) (hP : MaxPair T T₁)
    (hS : Sec3 T T₁)
    (hAn : ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g (normIn T T₁) = normIn T T₁) :
    False := by
  have hT : IsWC T := hS.cfg.wc
  have hLne : normIn T T₁ ≠ T := fun h => (card_normIn_lt_card_of_maxPair hP).ne (by rw [h])
  have hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁ := fun g hne hL' =>
    normIn_eq_of_normal_of_card_le h214 hInv hT (normIn_le T T₁) hLne hAn hne hL'
      (hP.maximal g hne)
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

end CFSG.CGT.Timmesfeld75

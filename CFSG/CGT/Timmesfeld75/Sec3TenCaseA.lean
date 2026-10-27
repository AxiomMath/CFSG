module

public import CFSG.CGT.Timmesfeld75.OddClass

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem normIn_eq_of_normal (h214 : Lemma214) (hInv : InvolutionClassInput) (hT : IsWC T)
    {L : Subgroup G} (hLT : L ≤ T) (hcard : Nat.card T = Nat.card L * 2)
    (hAn : ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g L = L) {g : G}
    (hne : conjSubgroup g T ≠ T) (hL' : normIn T (conjSubgroup g T) ≠ ⊥) :
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
    have hTeq : L = T := le_antisymm hLT hTL
    rw [hTeq] at hcard
    have hTpos : 0 < Nat.card T := Nat.card_pos
    omega
  refine (Subgroup.eq_of_le_of_card_ge hLle ?_).symm
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLle
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have h2 : Nat.card (normIn T (conjSubgroup g T)) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le (normIn_le T (conjSubgroup g T))
  rw [hk, hcard] at h2
  have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hLpos h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with h1 | h1
  · rw [hk, h1, mul_one]
  · exfalso
    rw [h1] at hk
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge (normIn_le T (conjSubgroup g T))
      (by rw [hcard, hk]))

omit [Finite G] in
theorem mem_left_of_mem_eqE_of_normal
    (hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁)
    {f : G} (hf : f ∈ eqE T (normIn T T₁)) (hfN : f ∈ Subgroup.normalizer (T : Set G)) :
    f ∈ T := by
  obtain ⟨h, t, htT, htL, rfl⟩ := hf
  by_cases hh : conjSubgroup h⁻¹ T = T
  · have hh' : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hh
    have hh'' : h ∈ Subgroup.normalizer (T : Set G) := by
      simpa using (Subgroup.normalizer (T : Set G)).inv_mem hh'
    exact conj_mem_of_mem_normalizer hh'' htT
  · exfalso
    have hf1 : conjSubgroup t (conjSubgroup h⁻¹ T) = conjSubgroup h⁻¹ T := by
      have hfT : conjSubgroup (h * t * h⁻¹) T = T := mem_normalizer_iff_conjSubgroup_eq.1 hfN
      rw [conjSubgroup_conjSubgroup]
      have e : t * h⁻¹ = h⁻¹ * (h * t * h⁻¹) := by group
      rw [e, ← conjSubgroup_conjSubgroup, hfT]
    have htN : t ∈ Subgroup.normalizer ((conjSubgroup h⁻¹ T : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.2 hf1
    have ht1 : t ≠ 1 := fun h1 => htL (h1 ▸ (normIn T T₁).one_mem)
    have hne : normIn T (conjSubgroup h⁻¹ T) ≠ ⊥ :=
      Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨t, mem_normIn.2 ⟨htT, htN⟩⟩,
        fun h1 => ht1 (congrArg Subtype.val h1)⟩
    have hEq := hA1 _ hh hne
    have : t ∈ normIn T (conjSubgroup h⁻¹ T) := mem_normIn.2 ⟨htT, htN⟩
    rw [hEq] at this
    exact htL this

omit [Finite G] in
theorem central_mem_of_mem_eqE_of_normal (hT : IsWC T)
    (hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁)
    {c t z : G} (htT : t ∈ T) (htL : t ∉ normIn T T₁)
    (hez : c * t * c⁻¹ * z = z * (c * t * c⁻¹))
    (hezE : c * t * c⁻¹ * z ∈ eqE T (normIn T T₁)) : c⁻¹ * z * c ∈ T := by
  have ht1 : t ≠ 1 := fun h => htL (h ▸ (normIn T T₁).one_mem)
  set z' := c⁻¹ * z * c with hz'
  have hcomm : t * z' = z' * t := by
    calc t * z' = c⁻¹ * (c * t * c⁻¹ * z) * c := by rw [hz']; group
      _ = c⁻¹ * (z * (c * t * c⁻¹)) * c := by rw [hez]
      _ = z' * t := by rw [hz']; group
  have hz'N : z' ∈ Subgroup.normalizer (T : Set G) :=
    hT.centralizer_le_normalizer htT ht1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have htz : t * z' ∈ eqE T (normIn T T₁) := by
    have := eqE_conj hezE c⁻¹
    have e : c⁻¹ * (c * t * c⁻¹ * z) * c⁻¹⁻¹ = t * z' := by rw [hz']; group
    rwa [e] at this
  have htzN : t * z' ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer htT) hz'N
  have htzT := mem_left_of_mem_eqE_of_normal hA1 htz htzN
  have := T.mul_mem (T.inv_mem htT) htzT
  simpa using this


theorem orderOf_mul_cases_eqE_of_normal (hT : IsWC T)
    (hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁) {e f : G} (he : e ∈ eqE T (normIn T T₁))
    (hf : f ∈ eqE T (normIn T T₁)) :
    orderOf (e * f) ∣ 2 ∨ Odd (orderOf (e * f)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn2, hnodd⟩ := hcon
  obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hnodd
  have hm0 : 0 < m := by
    have := orderOf_pos (e * f)
    omega
  have hee := mul_self_eq_one_of_mem_eqE hT he
  have hff := mul_self_eq_one_of_mem_eqE hT hf
  obtain ⟨z, -, hz1, hez, hfz, hezE, hfzE⟩ := dihedral_even_central_mem he hf hee hff
    (fun g _ s hs => by simpa using eqE_conj hs g⁻¹) hm0 (by omega)
  obtain ⟨c, t, htT, htL, rfl⟩ := he
  obtain ⟨c', t', ht'T, ht'L, rfl⟩ := hf
  have hzc := central_mem_of_mem_eqE_of_normal hT hA1 htT htL hez hezE
  have hzc' := central_mem_of_mem_eqE_of_normal hT hA1 ht'T ht'L hfz hfzE
  have hzT : z ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup]; exact hzc
  have hzT' : z ∈ conjSubgroup c' T := by
    rw [mem_conjSubgroup]; exact hzc'
  have hTeq : conjSubgroup c' T = conjSubgroup c T := by
    have h1 := (hT.conj c).conj_eq_of_inf_ne_bot (g := c' * c⁻¹) (by
      intro hbot
      have hzm : z ∈ conjSubgroup c T ⊓ conjSubgroup (c' * c⁻¹) (conjSubgroup c T) := by
        refine ⟨hzT, ?_⟩
        rw [conjSubgroup_conjSubgroup, show c' * c⁻¹ * c = c' by group]
        exact hzT'
      rw [hbot, Subgroup.mem_bot] at hzm
      exact hz1 hzm)
    rwa [conjSubgroup_conjSubgroup, show c' * c⁻¹ * c = c' by group] at h1
  have hel : c * t * c⁻¹ ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup]
    have e : c⁻¹ * (c * t * c⁻¹) * c = t := by group
    rw [e]; exact htT
  have hfl : c' * t' * c'⁻¹ ∈ conjSubgroup c T := by
    rw [← hTeq, mem_conjSubgroup]
    have e : c'⁻¹ * (c' * t' * c'⁻¹) * c' = t' := by group
    rw [e]; exact ht'T
  have habel := isElemAbelian_conjSubgroup hT.1 c
  have hprod : (c * t * c⁻¹) * (c' * t' * c'⁻¹) ∈ conjSubgroup c T :=
    (conjSubgroup c T).mul_mem hel hfl
  have hsq : ((c * t * c⁻¹) * (c' * t' * c'⁻¹)) ^ 2 = 1 := habel.2 _ hprod
  exact hn2 (orderOf_dvd_of_pow_eq_one hsq)


theorem false_of_normal [IsSimpleGroup G] (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : Sec3 T T₁)
    (hcard : Nat.card T = Nat.card (normIn T T₁) * 2)
    (hAn : ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g (normIn T T₁) = normIn T T₁) :
    False := by
  have hT : IsWC T := hS.cfg.wc
  have hA1 : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      normIn T (conjSubgroup g T) = normIn T T₁ := fun g hne hL' =>
    normIn_eq_of_normal h214 hInv hT (normIn_le T T₁) hcard hAn hne hL'
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

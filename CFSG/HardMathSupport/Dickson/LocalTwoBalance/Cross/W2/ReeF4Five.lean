module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Faithful
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Conj

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.Ree CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
  CFSG.RankThree.PartOne.SEITZ3


section Layer

variable {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {a : ℕ}

theorem isPLayer_of_decomp (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Plane5 K a)
    (γ : ReeTag.F4.reeGamma K a) {z : (rootsOfUnity 5 (AlgebraicClosure K)) ×
      (rootsOfUnity 5 (AlgebraicClosure K))} (hz : z ≠ 1)
    {A Sg : Subgroup (ReeTag.F4.reeGamma K a)} (hd : IsDecomp P z A Sg)
    {E : Subgroup (MulAut (ReeTag.F4.reeGamma K a))}
    (hmem : MulAut.conj (γ * P.Ψ z * γ⁻¹) ∈ E) :
    IsPLayer 5 E (Sg.map (MulAut.conj γ).toMonoidHom) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hd' := hd
  obtain ⟨-, hcAS, -, hsup, -, ⟨eS⟩⟩ := hd'
  have hSgC : ∀ t ∈ Sg, P.Ψ z * t * (P.Ψ z)⁻¹ = t := by
    intro t ht
    have htC : t ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [← hsup]
      exact (le_sup_right : Sg ≤ A ⊔ Sg) ht
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 htC
    rw [← h1, mul_inv_cancel_right]
  refine ⟨MulAut.conj (γ * P.Ψ z * γ⁻¹), hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 : γ * P.Ψ z * γ⁻¹ = 1 := hinj (by rw [h1, map_one])
    have h3 : P.Ψ z = 1 := by
      have : P.Ψ z = γ⁻¹ * (γ * P.Ψ z * γ⁻¹) * γ := by group
      rw [this, h2]
      group
    exact hz (P.Ψinj (h3.trans (map_one P.Ψ).symm))
  · rintro _ ⟨t, ht, rfl⟩
    change (γ * P.Ψ z * γ⁻¹) * (γ * t * γ⁻¹) * (γ * P.Ψ z * γ⁻¹)⁻¹ = γ * t * γ⁻¹
    calc (γ * P.Ψ z * γ⁻¹) * (γ * t * γ⁻¹) * (γ * P.Ψ z * γ⁻¹)⁻¹
        = γ * (P.Ψ z * t * (P.Ψ z)⁻¹) * γ⁻¹ := by group
      _ = γ * t * γ⁻¹ := by rw [hSgC t ht]
  · intro f hf t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have hf' : (γ * P.Ψ z * γ⁻¹) * f * (γ * P.Ψ z * γ⁻¹)⁻¹ = f := hf
    have hfc : (γ * P.Ψ z * γ⁻¹) * f = f * (γ * P.Ψ z * γ⁻¹) := by
      calc (γ * P.Ψ z * γ⁻¹) * f
          = ((γ * P.Ψ z * γ⁻¹) * f * (γ * P.Ψ z * γ⁻¹)⁻¹) * (γ * P.Ψ z * γ⁻¹) := by group
        _ = f * (γ * P.Ψ z * γ⁻¹) := by rw [hf']
    have hf₀ : γ⁻¹ * f * γ ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (γ⁻¹ * f * γ) * P.Ψ z
          = γ⁻¹ * (f * (γ * P.Ψ z * γ⁻¹)) * γ := by group
        _ = γ⁻¹ * ((γ * P.Ψ z * γ⁻¹) * f) * γ := by rw [hfc]
        _ = P.Ψ z * (γ⁻¹ * f * γ) := by group
    rw [← hsup] at hf₀
    obtain ⟨α, hα, s, hs, hαs⟩ := mem_sup_of_commute' hcAS hf₀
    refine ⟨s * t₀ * s⁻¹, Sg.mul_mem (Sg.mul_mem hs ht₀) (Sg.inv_mem hs), ?_⟩
    have hfeq : f = γ * (α * s) * γ⁻¹ := by
      rw [hαs]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hfeq]
    have hαt : α * (s * t₀ * s⁻¹) * α⁻¹ = s * t₀ * s⁻¹ := by
      have h1 := hcAS α hα (s * t₀ * s⁻¹) (Sg.mul_mem (Sg.mul_mem hs ht₀) (Sg.inv_mem hs))
      rw [h1, mul_inv_cancel_right]
    symm
    calc γ * (α * s) * γ⁻¹ * (γ * t₀ * γ⁻¹) * (γ * (α * s) * γ⁻¹)⁻¹
        = γ * (α * (s * t₀ * s⁻¹) * α⁻¹) * γ⁻¹ := by group
      _ = γ * (s * t₀ * s⁻¹) * γ⁻¹ := by rw [hαt]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Sg.equivMapOfInjective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective).symm.trans
        eS |>.symm) (suzuki_quasisimple ha hK).1
  · intro hcop
    have h5 : 5 ∣ Nat.card (Sg.map (MulAut.conj γ).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, Nat.card_congr eS.toEquiv,
        suzuki_order hK]
      refine Dvd.dvd.mul_left ?_ _
      exact five_dvd_phi4 a
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hcop h5

end Layer

theorem reeF4InnerFiveBalance_holds : ReeF4InnerFiveBalance := by
  intro a K _ _ _ ha hK E hEin hE hEc H hH
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hne : ∃ x ∈ E, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hall
    rw [this, Subgroup.card_bot] at hEc
    norm_num at hEc
  refine localDeltaIn_eq_bot_of_layers_faithful Nat.prime_five hinj hH hne ?_
  intro g hg hcomm hlayers
  obtain ⟨P⟩ := exists_plane5 (K := K) (a := a) hK
  set E₁ : Subgroup (ReeTag.F4.reeGamma K a) := E.comap (MulAut.conj :
    ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) with hE₁
  have hE₁mem : ∀ x, x ∈ E₁ ↔ MulAut.conj x ∈ E := fun x => Iff.rfl
  have hE₁map : E₁.map (MulAut.conj : ReeTag.F4.reeGamma K a →*
      MulAut (ReeTag.F4.reeGamma K a)) = E := by
    rw [hE₁, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hE₁p : ∀ x ∈ E₁, x ^ 5 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  have hE₁c : Nat.card E₁ = 5 ^ 2 := by
    rw [← hEc, ← hE₁map, Subgroup.card_map_of_injective hinj]
  obtain ⟨γ, hγ⟩ := exists_conj_plane hK P E₁ hE₁p hE₁c
  set cγ : MulAut (ReeTag.F4.reeGamma K a) := MulAut.conj γ with hcγ
  have hmem : ∀ z, MulAut.conj (γ * P.Ψ z * γ⁻¹) ∈ E := by
    intro z
    rw [← hE₁mem, hγ, mem_cj]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact ⟨z, rfl⟩
  have hg' : Nat.Coprime 5 (orderOf (cγ⁻¹ * g * cγ)) := by
    have : orderOf (cγ⁻¹ * g * cγ) = orderOf g := by
      have := orderOf_injective (MulAut.conj cγ⁻¹).toMonoidHom (MulAut.conj cγ⁻¹).injective g
      simpa [MulAut.conj_apply] using this
    rwa [this]
  have hcomm' : ∀ z, (cγ⁻¹ * g * cγ) * MulAut.conj (P.Ψ z) =
      MulAut.conj (P.Ψ z) * (cγ⁻¹ * g * cγ) := by
    intro z
    have he := hcomm _ (hmem z)
    have h1 : cγ⁻¹ * g * cγ * MulAut.conj (P.Ψ z) =
        cγ⁻¹ * (g * MulAut.conj (γ * P.Ψ z * γ⁻¹)) * cγ := by
      rw [map_mul, map_mul, map_inv, ← hcγ]
      group
    rw [h1, he, map_mul, map_mul, map_inv, ← hcγ]
    group
  have hfix' : ∀ z, z ≠ 1 → ∀ A Sg, IsDecomp P z A Sg → ∀ t ∈ Sg, (cγ⁻¹ * g * cγ) t = t := by
    intro z hz A Sg hd t ht
    have hL := isPLayer_of_decomp ha hK P γ hz hd (hmem z)
    have h1 := hlayers _ hL (cγ t) ⟨t, ht, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, h1]
    exact MulAut.inv_apply_self _ _ _
  have h1 := faithful_std ha hK P _ hg' hcomm' hfix'
  have : g = cγ * (cγ⁻¹ * g * cγ) * cγ⁻¹ := by group
  rw [this, h1]
  group

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Restrict
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Induced
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Char
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Rigid

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {M W N : Type*} [Group M] [CommGroup W] [Group N] {ρ : M →* MulAut W}

theorem exists_conj_of_aut_preimage (X : ExtData ρ N) {K K' : Subgroup M} {B : Subgroup N}
    (hB : ∀ n, n ∈ B ↔ X.π n ∈ K) [IsSimpleGroup ↥K] (hnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hH1 : ModH1Trivial (ρ.comp K.subtype)) (hEnd : ModEquivAutTrivial (ρ.comp K.subtype))
    (hAut : ∀ α : ↥K ≃* ↥K, ∃ k' ∈ K', ∀ q : ↥K, ((α q : ↥K) : M) = k' * (q : M) * k'⁻¹)
    (γ : ↥B ≃* ↥B) :
    ∃ c : N, X.π c ∈ K' ∧ ∀ b : ↥B, ((γ b : ↥B) : N) = c * (b : N) * c⁻¹ := by
  let XB := X.restrict K B hB
  have hker : ∀ b, XB.π (γ b) = 1 ↔ XB.π b = 1 := XB.π_map_eq_one_iff hnc γ
  obtain ⟨γ', hγ'⟩ := exists_mulEquiv_induced XB.π XB.π_surjective γ hker
  obtain ⟨k', hk', hconj⟩ := hAut γ'
  obtain ⟨c₀, hc₀⟩ := X.π_surjective k'
  have hπc : ∀ b : ↥B, X.π (c₀ * (b : N) * c₀⁻¹) = ((γ' (XB.π b) : ↥K) : M) := by
    intro b
    rw [map_mul, map_mul, map_inv, hc₀, hconj (XB.π b)]
    rfl
  have hmem : ∀ b : ↥B, c₀ * (b : N) * c₀⁻¹ ∈ B := fun b =>
    (hB _).2 (by rw [hπc b]; exact (γ' (XB.π b)).2)
  have hmem' : ∀ b : ↥B, c₀⁻¹ * (b : N) * c₀ ∈ B := by
    intro b
    obtain ⟨q, hq⟩ := γ'.surjective (XB.π b)
    refine (hB _).2 ?_
    have h1 : ((XB.π b : ↥K) : M) = k' * (q : M) * k'⁻¹ := by
      rw [← hq]
      exact hconj q
    have h2 : X.π (c₀⁻¹ * (b : N) * c₀) = (q : M) := by
      rw [map_mul, map_mul, map_inv, hc₀]
      have h3 : X.π (b : N) = k' * (q : M) * k'⁻¹ := h1
      rw [h3]
      group
    rw [h2]
    exact q.2
  let cB : ↥B ≃* ↥B :=
    { toFun := fun b => ⟨c₀ * (b : N) * c₀⁻¹, hmem b⟩
      invFun := fun b => ⟨c₀⁻¹ * (b : N) * c₀, hmem' b⟩
      left_inv := fun b => Subtype.ext (by group)
      right_inv := fun b => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hγcB : ∀ b : ↥B, XB.π (γ b) = XB.π (cB b) := by
    intro b
    apply Subtype.ext
    show X.π ((γ b : ↥B) : N) = X.π (c₀ * (b : N) * c₀⁻¹)
    rw [hπc b, hγ' b]
    rfl
  obtain ⟨x, hx, hxγ⟩ := XB.exists_conj_of_trivialMod hH1 hEnd (cB.symm.trans γ) fun b => by
    show XB.π (γ (cB.symm b)) = XB.π b
    rw [hγcB, MulEquiv.apply_symm_apply]
  have hx' : X.π (x : N) = 1 := congrArg Subtype.val hx
  refine ⟨(x : N) * c₀, ?_, fun b => ?_⟩
  · rw [map_mul, hx', one_mul, hc₀]
    exact hk'
  · have h1 := hxγ (cB b)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    show (x : N) * (c₀ * (b : N) * c₀⁻¹) * (x : N)⁻¹ = (x : N) * c₀ * (b : N) * ((x : N) * c₀)⁻¹
    group

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

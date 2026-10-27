module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open Matrix CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.SectionRank.EvenCover

theorem not_dvd_card_center_specialLinearGroup {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {n : ℕ} :
    ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) := by
  have : NeZero (max (Fintype.card (Fin n)) 1) := ⟨by omega⟩
  have hdvd : Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) ∣ Nat.card Kˣ := by
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  intro h
  have h1 := h.trans hdvd
  have := Fintype.ofFinite K
  obtain ⟨k, hk, hcard⟩ := FiniteField.card K p
  rw [Nat.card_units, Nat.card_eq_fintype_card, hcard] at h1
  have h2 : p ∣ p ^ (k : ℕ) := dvd_pow_self p (PNat.ne_zero k)
  have h3 : p ∣ 1 := by
    have h4 := Nat.dvd_sub h2 h1
    rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hk.pos)] at h4
  exact hk.one_lt.ne' (Nat.dvd_one.mp h3)

section Lift

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
  {E : Type*} [Group E] [Finite E]

theorem sl_existsUnique_section (hn : 1 ≤ n) {π : E →* SpecialLinearGroup (Fin n) K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) :
    ∃! s : SpecialLinearGroup (Fin n) K →* E, ∀ g, π (s g) = g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine existsUnique_section_of_sl2_lift (p := p) (SpecialLinear.isCTGroupDatum m K)
    (SpecialLinear.steinbergExtras m K) SL.isParametrization SL.rankOne hπ hcen hC fun ρ => ?_
  obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem sl_existsUnique_lift (hn : 1 ≤ n) {G : Type*} [Group G] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) (α : SpecialLinearGroup (Fin n) K →* G) :
    ∃! α' : SpecialLinearGroup (Fin n) K →* E, π.comp α' = α := by
  obtain ⟨σ, hσ, huniq⟩ := sl_existsUnique_section hn (pullbackFst_surjective hπ α)
    (pullbackFst_ker_le_center hcen α) (fun h => hC (h.trans (card_pullbackFst_ker_dvd π α)))
  refine ⟨_, comp_snd_section σ hσ, fun τ hτ => ?_⟩
  let τ' : SpecialLinearGroup (Fin n) K →* pullback π α :=
    { toFun := fun g => ⟨(g, τ g), by
        change α g = π (τ g)
        rw [← hτ, MonoidHom.comp_apply]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have h1 := huniq τ' fun g => rfl
  ext g
  exact congrArg (fun f : SpecialLinearGroup (Fin n) K →* pullback π α =>
    ((f g : pullback π α) : SpecialLinearGroup (Fin n) K × E).2) h1

end Lift

theorem exists_mulEquiv_lift {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X] (θ : SpecialLinearGroup (Fin n) K →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (σ : X ≃* X) :
    ∃ α : SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K, ∀ x, θ (α x) = σ (θ x) := by
  have hC : ¬ p ∣ Nat.card θ.ker := fun h =>
    not_dvd_card_center_specialLinearGroup (K := K) (p := p)
      (h.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨α, hα, -⟩ := sl_existsUnique_lift hn hθ hker hC (σ.toMonoidHom.comp θ)
  obtain ⟨α', hα', -⟩ := sl_existsUnique_lift hn hθ hker hC (σ.symm.toMonoidHom.comp θ)
  obtain ⟨β, -, huniq⟩ := sl_existsUnique_lift hn hθ hker hC θ
  have hαx : ∀ x, θ (α x) = σ (θ x) := fun x => DFunLike.congr_fun hα x
  have hαx' : ∀ x, θ (α' x) = σ.symm (θ x) := fun x => DFunLike.congr_fun hα' x
  have h1 : α.comp α' = MonoidHom.id _ :=
    (huniq _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hαx, hαx', MulEquiv.apply_symm_apply])).trans
      (huniq _ (MonoidHom.ext fun x => by simp)).symm
  have h2 : α'.comp α = MonoidHom.id _ :=
    (huniq _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hαx, hαx', MulEquiv.symm_apply_apply])).trans
      (huniq _ (MonoidHom.ext fun x => by simp)).symm
  exact ⟨{ toFun := α
           invFun := α'
           left_inv := fun x => DFunLike.congr_fun h2 x
           right_inv := fun x => DFunLike.congr_fun h1 x
           map_mul' := α.map_mul }, hαx⟩

end CFSG.ClassicalInvolution.ModelFacts.LinearAut

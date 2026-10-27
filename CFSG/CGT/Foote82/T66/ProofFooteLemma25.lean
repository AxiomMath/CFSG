module

public import CFSG.CGT.Foote82.T66.CitedCaseI
public import CFSG.CGT.Foote82.T66.CaseIHeart
public import CFSG.Quasithin.Background.G11Basic
import CFSG.CGT.Foote82.ClimbIrr
import CFSG.CGT.Foote82.Lemma61
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.BookkeepingCocycle
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen
import CFSG.Quasithin.Background.G11Bridge
public import CFSG.CGT.Foote82.T66.CaseIPerm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm

namespace Lemma25Aux

theorem vadd_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod2_sub_eq_one : ∀ p q : ZMod 2, p ≠ q → q - p = 1 := by decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H : Subgroup (GLV V)} {N : ℕ} {φ : ↥H ≃* Perm (Fin N)}

abbrev altSub (H : Subgroup (GLV V)) (φ : ↥H ≃* Perm (Fin N)) : Subgroup (GLV V) :=
  ((alternatingGroup (Fin N)).comap φ.toMonoidHom).map H.subtype

@[expose] noncomputable def tG (φ : ↥H ≃* Perm (Fin N)) : Perm (Fin N) →* GLV V :=
  H.subtype.comp φ.symm.toMonoidHom

theorem tG_apply (σ : Perm (Fin N)) : tG φ σ = ((φ.symm σ : ↥H) : GLV V) := rfl

theorem tG_mem (σ : Perm (Fin N)) : tG φ σ ∈ H := (φ.symm σ).2

theorem tG_phi (g : ↥H) : tG φ (φ g) = g := by
  rw [tG_apply, MulEquiv.symm_apply_apply]

theorem tG_injective : Function.Injective (tG φ) :=
  Subtype.val_injective.comp φ.symm.injective

theorem tG_mem_altSub {σ : Perm (Fin N)} (hσ : σ ∈ alternatingGroup (Fin N)) :
    tG φ σ ∈ altSub H φ :=
  ⟨φ.symm σ, by simpa using hσ, rfl⟩

theorem exists_eq_tG {g : GLV V} (hg : g ∈ altSub H φ) :
    ∃ σ ∈ alternatingGroup (Fin N), tG φ σ = g := by
  obtain ⟨h, hh, rfl⟩ := hg
  exact ⟨φ h, hh, tG_phi h⟩

theorem altSub_eq_map : altSub H φ = (alternatingGroup (Fin N)).map (tG φ) := by
  ext g
  constructor
  · intro hg
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_tG hg
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact tG_mem_altSub hσ

theorem altSub_perfect (hN : 5 ≤ N) : ⁅altSub H φ, altSub H φ⁆ = altSub H φ := by
  rw [altSub_eq_map, ← Subgroup.map_commutator,
    commutator_alternatingGroup_eq_self (by simpa using hN)]

theorem altSub_le : altSub H φ ≤ H := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

theorem conj_mem_altSub {h k : GLV V} (hh : h ∈ H) (hk : k ∈ altSub H φ) :
    h * k * h⁻¹ ∈ altSub H φ := by
  obtain ⟨σ, hσ, rfl⟩ := exists_eq_tG hk
  have e : h * tG φ σ * h⁻¹ = tG φ (φ ⟨h, hh⟩ * σ * (φ ⟨h, hh⟩)⁻¹) := by
    rw [map_mul, map_mul, map_inv, tG_phi]
  rw [e]
  exact tG_mem_altSub
    ((inferInstance : (alternatingGroup (Fin N)).Normal).conj_mem σ hσ (φ ⟨h, hh⟩))

theorem invariant_V₀ : Invariant H (commSpace (altSub H φ) ⊤) :=
  invariant_commSpace (fun _ hh _ hk => conj_mem_altSub hh hk) (invariant_top H)

theorem invariant_V₁ : Invariant H (fixedSpace (altSub H φ)) :=
  invariant_fixedSpace (fun _ hh _ hk => conj_mem_altSub hh hk)

theorem heartFor {β : ↥(commSpace (altSub H φ) ⊤) →+ altHeart N}
    (hβs : Function.Surjective β)
    (hβk : β.ker = ((fixedSpace (altSub H φ)).comap
      (commSpace (altSub H φ) ⊤).subtype).toAddSubgroup)
    (hβc : ∀ (h : ↥H) (w w' : ↥(commSpace (altSub H φ) ⊤)), (w' : V) = (h : GLV V) (w : V) →
      ∀ x : evenWeight N, β w = (x : altHeart N) →
        β w' = (evenWeightPerm (φ h) x : altHeart N)) :
    CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β where
  le := altSub_le
  mem_iff x := ⟨fun hx => by
      obtain ⟨h, hh, he⟩ := hx
      have : h = x := Subtype.ext he
      subst this
      exact hh,
    fun hx => ⟨x, hx, rfl⟩⟩
  surj := hβs
  ker := hβk
  equiv := hβc

variable {β : ↥(commSpace (altSub H φ) ⊤) →+ altHeart N}

theorem beta_tG (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β) (σ : Perm (Fin N))
    (w w' : ↥(commSpace (altSub H φ) ⊤)) (hw : (w' : V) = tG φ σ (w : V)) :
    β w' = altAct σ (β w) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β w)
  have h1 := hH.equiv (φ.symm σ) w w' hw x hx.symm
  rw [h1, ← hx, altAct_mk]
  simp

theorem beta_eq_zero (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β)
    (w : ↥(commSpace (altSub H φ) ⊤)) (hw : (w : V) ∈ fixedSpace (altSub H φ)) : β w = 0 := by
  have : w ∈ β.ker := by rw [hH.ker]; exact hw
  exact this

theorem mem_fixedSpace_of_beta (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β)
    (w : ↥(commSpace (altSub H φ) ⊤)) (hw : β w = 0) : (w : V) ∈ fixedSpace (altSub H φ) := by
  have : w ∈ β.ker := hw
  rw [hH.ker] at this
  exact this

theorem map_fixedSpace_eq {t₁ t₂ : ↥H} (hs : sign (φ t₁) = sign (φ t₂)) :
    (fixedSpace (altSub H φ)).map (((t₁ : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id) =
      (fixedSpace (altSub H φ)).map (((t₂ : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  have hmem : ((t₁⁻¹ * t₂ : ↥H) : GLV V) ∈ altSub H φ := by
    refine ⟨t₁⁻¹ * t₂, ?_, rfl⟩
    show φ (t₁⁻¹ * t₂) ∈ alternatingGroup (Fin N)
    rw [mem_alternatingGroup, map_mul, map_inv, map_mul, map_inv, hs, inv_mul_cancel]
  have key : ∀ v ∈ fixedSpace (altSub H φ), (t₂ : GLV V) v = (t₁ : GLV V) v := by
    intro v hv
    have h1 := hv _ hmem
    have e : (t₂ : GLV V) = (t₁ : GLV V) * ((t₁⁻¹ * t₂ : ↥H) : GLV V) := by
      simp
    rw [e, LinearEquiv.mul_apply, h1]
  ext x
  simp only [Submodule.mem_map, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, by rw [key v hv]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, by rw [key v hv]⟩

open scoped Classical in
@[expose] noncomputable def cocy (φ : ↥H ≃* Perm (Fin N))
    (β : ↥(commSpace (altSub H φ) ⊤) →+ altHeart N) (v : V) (σ : Perm (Fin N)) : altHeart N :=
  if h : σ ∈ alternatingGroup (Fin N) then
    β ⟨tG φ σ v - v, sub_mem_commSpace (tG_mem_altSub h) Submodule.mem_top⟩
  else 0

theorem cocy_of_mem (v : V) {σ : Perm (Fin N)} (hσ : σ ∈ alternatingGroup (Fin N)) :
    cocy φ β v σ =
      β ⟨tG φ σ v - v, sub_mem_commSpace (tG_mem_altSub hσ) Submodule.mem_top⟩ := by
  rw [cocy, dif_pos hσ]

theorem cocy_add (v v' : V) (σ : Perm (Fin N)) :
    cocy φ β (v + v') σ = cocy φ β v σ + cocy φ β v' σ := by
  by_cases hσ : σ ∈ alternatingGroup (Fin N)
  · rw [cocy_of_mem _ hσ, cocy_of_mem _ hσ, cocy_of_mem _ hσ, ← map_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    abel
  · simp only [cocy, dif_neg hσ, add_zero]

theorem cocy_mul (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β) (v : V)
    {σ τ : Perm (Fin N)} (hσ : σ ∈ alternatingGroup (Fin N)) (hτ : τ ∈ alternatingGroup (Fin N)) :
    cocy φ β v (σ * τ) = cocy φ β v σ + altAct σ (cocy φ β v τ) := by
  rw [cocy_of_mem _ (mul_mem hσ hτ), cocy_of_mem _ hσ, cocy_of_mem _ hτ]
  have hmem : tG φ σ (tG φ τ v - v) ∈ commSpace (altSub H φ) ⊤ :=
    invariant_V₀ _ (tG_mem σ) _ (sub_mem_commSpace (tG_mem_altSub hτ) Submodule.mem_top)
  have e : (⟨tG φ (σ * τ) v - v, sub_mem_commSpace (tG_mem_altSub (mul_mem hσ hτ))
      Submodule.mem_top⟩ : ↥(commSpace (altSub H φ) ⊤)) =
      ⟨tG φ σ (tG φ τ v - v), hmem⟩ +
        ⟨tG φ σ v - v, sub_mem_commSpace (tG_mem_altSub hσ) Submodule.mem_top⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_mul, LinearEquiv.mul_apply, map_sub]
    abel
  rw [e, map_add, beta_tG hH σ
    ⟨tG φ τ v - v, sub_mem_commSpace (tG_mem_altSub hτ) Submodule.mem_top⟩ ⟨_, hmem⟩ rfl, add_comm]

theorem mem_sup_of_cob (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β)
    (hN : 5 ≤ N) (v : V) (z : altHeart N)
    (hz : ∀ σ ∈ alternatingGroup (Fin N), cocy φ β v σ = altAct σ z - z) :
    v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ) := by
  obtain ⟨w, hw⟩ := hH.surj z
  obtain ⟨u, hu⟩ : ∃ u : V, u = v - (w : V) := ⟨_, rfl⟩
  have hgu : ∀ g ∈ altSub H φ, g u - u ∈ fixedSpace (altSub H φ) := by
    intro g hg
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_tG hg
    have hgw : tG φ σ (w : V) ∈ commSpace (altSub H φ) ⊤ := invariant_V₀ _ (tG_mem σ) _ w.2
    have hgv : tG φ σ v - v ∈ commSpace (altSub H φ) ⊤ :=
      sub_mem_commSpace (tG_mem_altSub hσ) Submodule.mem_top
    have hmem : tG φ σ u - u ∈ commSpace (altSub H φ) ⊤ :=
      sub_mem_commSpace (tG_mem_altSub hσ) Submodule.mem_top
    have e : (⟨tG φ σ u - u, hmem⟩ : ↥(commSpace (altSub H φ) ⊤)) =
        ⟨tG φ σ v - v, hgv⟩ - (⟨tG φ σ (w : V), hgw⟩ - w) := by
      apply Subtype.ext
      simp only [hu, Submodule.coe_sub, map_sub]
      abel
    have h1 := hz σ hσ
    rw [cocy_of_mem _ hσ] at h1
    refine mem_fixedSpace_of_beta hH ⟨_, hmem⟩ ?_
    rw [e, map_sub, map_sub, h1, beta_tG hH σ w ⟨_, hgw⟩ rfl, hw, sub_self]
  obtain ⟨X, hX⟩ : ∃ X : Submodule (ZMod 2) V, X = (ZMod 2 ∙ u) ⊔ fixedSpace (altSub H φ) :=
    ⟨_, rfl⟩
  have hdec : ∀ x ∈ X, ∃ a : ZMod 2, ∃ f ∈ fixedSpace (altSub H φ), x = a • u + f := by
    intro x hx
    rw [hX] at hx
    obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨a, f, hf, rfl⟩
  have hXinv : Invariant (altSub H φ) X := by
    intro g hg x hx
    obtain ⟨a, f, hf, rfl⟩ := hdec x hx
    have e : g (a • u + f) = a • u + (a • (g u - u) + f) := by
      rw [map_add, map_smul, hf g hg, smul_sub]
      abel
    rw [e, hX]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u))
      (Submodule.add_mem _ (Submodule.smul_mem _ a (hgu g hg)) hf)
  have hXc : commSpace (altSub H φ) X ≤ fixedSpace (altSub H φ) := by
    refine commSpace_le_iff.2 fun g hg x hx => ?_
    obtain ⟨a, f, hf, rfl⟩ := hdec x hx
    have e : g (a • u + f) - (a • u + f) = a • (g u - u) := by
      rw [map_add, map_smul, hf g hg, smul_sub]
      abel
    rw [e]
    exact Submodule.smul_mem _ a (hgu g hg)
  have hfix := trivial_of_commSpace_le_fixedSpace_of_perfect (altSub_perfect hN) hXinv hXc
  have huV₁ : u ∈ fixedSpace (altSub H φ) := fun g hg =>
    hfix g hg u (by rw [hX]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
  have hv : v = (w : V) + u := by rw [hu]; abel
  rw [hv]
  exact Submodule.add_mem_sup w.2 huV₁

theorem exists_complement (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β)
    (hN : 7 ≤ N) : ∃ v₀ : V, ∀ v : V,
      v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ) ∨
        v + v₀ ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ) := by
  set k : Fin N := ⟨0, by omega⟩
  have hcases : ∀ v : V, v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ) ∨
      ∃ z : altHeart N, ∀ σ ∈ alternatingGroup (Fin N),
        cocy φ β v σ = altAct σ z - z + (pairEW k (σ k) : altHeart N) := by
    intro v
    obtain ⟨z, hz | hz⟩ := EightFive.altCocycle_cases hN k (cocy φ β v)
      (fun σ hσ τ hτ => cocy_mul hH v hσ hτ)
    · exact Or.inl (mem_sup_of_cob hH (by omega) v z hz)
    · exact Or.inr ⟨z, hz⟩
  by_cases hall : ∀ v : V, v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ)
  · exact ⟨0, fun v => Or.inl (hall v)⟩
  push Not at hall
  obtain ⟨v₀, hv₀⟩ := hall
  obtain ⟨z₀, hz₀⟩ := (hcases v₀).resolve_left hv₀
  refine ⟨v₀, fun v => ?_⟩
  by_cases hv : v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ)
  · exact Or.inl hv
  obtain ⟨z, hz⟩ := (hcases v).resolve_left hv
  right
  refine mem_sup_of_cob hH (by omega) (v + v₀) (z + z₀) fun σ hσ => ?_
  rw [cocy_add, hz σ hσ, hz₀ σ hσ, map_add]
  have hP := EightFive.altHeart_add_self (pairEW k (σ k) : altHeart N)
  calc altAct σ z - z + (pairEW k (σ k) : altHeart N) +
        (altAct σ z₀ - z₀ + (pairEW k (σ k) : altHeart N))
      = altAct σ z + altAct σ z₀ - (z + z₀) +
          ((pairEW k (σ k) : altHeart N) + (pairEW k (σ k) : altHeart N)) := by abel
    _ = altAct σ z + altAct σ z₀ - (z + z₀) := by rw [hP, add_zero]

theorem finrank_le_of_top {v₀ : V}
    (hv₀ : ∀ v : V, v ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ) ∨
      v + v₀ ∈ commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ)) (t : GLV V) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers t) ⊤) ≤
      Module.finrank (ZMod 2) ↥((commSpace (altSub H φ) ⊤).map
          ((t : V →ₗ[ZMod 2] V) - LinearMap.id)) +
        Module.finrank (ZMod 2) ↥((fixedSpace (altSub H φ)).map
          ((t : V →ₗ[ZMod 2] V) - LinearMap.id)) + 1 := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set f : V →ₗ[ZMod 2] V := (t : V →ₗ[ZMod 2] V) - LinearMap.id with hf
  have htop : (commSpace (altSub H φ) ⊤ ⊔ fixedSpace (altSub H φ)) ⊔ (ZMod 2 ∙ v₀) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    rcases hv₀ v with h | h
    · exact Submodule.mem_sup_left h
    · have e : v = (v + v₀) - v₀ := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left h)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
  have hR : commSpace (Subgroup.zpowers t) ⊤ =
      ((commSpace (altSub H φ) ⊤).map f ⊔ (fixedSpace (altSub H φ)).map f) ⊔
        (ZMod 2 ∙ v₀).map f := by
    rw [commSpace_zpowers_top, ← hf, ← Submodule.map_sup, ← Submodule.map_sup, htop,
      LinearMap.range_eq_map]
  have h1 : Module.finrank (ZMod 2) ↥((ZMod 2 ∙ v₀).map f) ≤ 1 := by
    refine (Submodule.finrank_map_le f _).trans ?_
    have := finrank_span_le_card (R := ZMod 2) ({v₀} : Set V)
    simpa using this
  rw [hR]
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((commSpace (altSub H φ) ⊤).map f) ((fixedSpace (altSub H φ)).map f)
  omega

theorem alternatingGroup_le_of_threeCycles (hN : 5 ≤ N) {i j k : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {K : Subgroup (Perm (Fin N))}
    (h3 : ∀ τ : Perm (Fin N), τ.IsThreeCycle → τ i = i → τ j = j → τ ∈ K)
    (hc : swap i j * swap j k ∈ K) : alternatingGroup (Fin N) ≤ K := by
  have hex : ∀ s : Finset (Fin N), s.card < N → ∃ m, m ∉ s := by
    intro s hs
    by_contra h
    simp only [not_exists, not_not] at h
    have := Finset.card_le_card (fun x _ => h x : (Finset.univ : Finset (Fin N)) ⊆ s)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨m, hm⟩ := hex {i, j, k} (lt_of_le_of_lt Finset.card_le_three (by omega))
  obtain ⟨n, hn⟩ := hex {i, j, k, m} (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm hn
  obtain ⟨hmi, hmj, hmk⟩ := hm
  obtain ⟨hni, hnj, hnk, hnm⟩ := hn
  set c := swap i j * swap j k with hcdef
  set ℓ := swap k m * swap m n with hℓdef
  have hℓj : ℓ j = j := by
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmj) (Ne.symm hnj),
      swap_apply_of_ne_of_ne hjk (Ne.symm hmj)]
  have hℓ : ℓ ∈ K := by
    refine h3 ℓ (CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap (Ne.symm hmk) (Ne.symm hnk)
      (Ne.symm hnm)) ?_ hℓj
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmi) (Ne.symm hni),
      swap_apply_of_ne_of_ne hik (Ne.symm hmi)]
  set g := c * ℓ * c with hgdef
  have hg : g ∈ K := K.mul_mem (K.mul_mem hc hℓ) hc
  have hci : c i = j := by
    rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, swap_apply_left]
  have hcj : c j = k := by
    rw [hcdef, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have hcm : c m = m := by
    rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne hmj hmk, swap_apply_of_ne_of_ne hmi hmj]
  have hℓk : ℓ k = m := by
    rw [hℓdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hmk) (Ne.symm hnk),
      swap_apply_left]
  have hgi : g i = k := by
    rw [hgdef, Perm.mul_apply, Perm.mul_apply, hci, hℓj, hcj]
  have hgj : g j = m := by
    rw [hgdef, Perm.mul_apply, Perm.mul_apply, hcj, hℓk, hcm]
  refine CFSG.AGLEmbedding.alternatingGroup_le_of_disjoint (S₁ := {i, j}) (S₂ := {k, m})
    ?_ ?_ ?_ ?_ ?_ (x := n) ?_ ?_
  · intro τ hτ hd
    refine h3 τ hτ ?_ ?_
    · exact Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    · exact Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
  · intro τ hτ hd
    have hτk : τ k = k := Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    have hτm : τ m = m := Perm.notMem_support.1 (Finset.disjoint_right.1 hd (by simp))
    have h3' : (g⁻¹ * τ * g).IsThreeCycle := by
      have e := Perm.cycleType_conj (σ := τ) (τ := g⁻¹)
      rw [inv_inv] at e
      unfold Perm.IsThreeCycle
      rw [e]
      exact hτ
    have hmem : g⁻¹ * τ * g ∈ K := by
      refine h3 _ h3' ?_ ?_
      · rw [Perm.mul_apply, Perm.mul_apply, hgi, hτk, Perm.inv_eq_iff_eq]
        exact hgi.symm
      · rw [Perm.mul_apply, Perm.mul_apply, hgj, hτm, Perm.inv_eq_iff_eq]
        exact hgj.symm
    have e : τ = g * (g⁻¹ * τ * g) * g⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hg hmem) (K.inv_mem hg)
  · simp [Finset.disjoint_left, hik, Ne.symm hmi, hjk, Ne.symm hmj]
  · rw [Finset.card_pair hij]; omega
  · rw [Finset.card_pair (Ne.symm hmk)]; omega
  · simp [hni, hnj]
  · simp [hnk, hnm]

theorem swap_sub_eq {a b : Fin N} (hab : a ≠ b) (x : evenWeight N) :
    evenWeightPerm (swap a b) x - x = 0 ∨ evenWeightPerm (swap a b) x - x = pairEW a b := by
  by_cases hx : (x : Fin N → ZMod 2) a = (x : Fin N → ZMod 2) b
  · left
    apply Subtype.ext
    funext i
    show (x : Fin N → ZMod 2) ((swap a b)⁻¹ i) - (x : Fin N → ZMod 2) i = 0
    rw [swap_inv]
    by_cases hia : i = a
    · subst hia
      rw [swap_apply_left, hx, sub_self]
    by_cases hib : i = b
    · subst hib
      rw [swap_apply_right, hx, sub_self]
    rw [swap_apply_of_ne_of_ne hia hib, sub_self]
  · right
    apply Subtype.ext
    funext i
    show (x : Fin N → ZMod 2) ((swap a b)⁻¹ i) - (x : Fin N → ZMod 2) i =
      ((pairEW a b : evenWeight N) : Fin N → ZMod 2) i
    rw [swap_inv, pairEW_apply]
    by_cases hia : i = a
    · subst hia
      rw [swap_apply_left, if_pos rfl, if_neg hab, add_zero]
      exact zmod2_sub_eq_one _ _ hx
    by_cases hib : i = b
    · subst hib
      rw [swap_apply_right, if_neg (Ne.symm hab), if_pos rfl, zero_add]
      exact zmod2_sub_eq_one _ _ (Ne.symm hx)
    rw [swap_apply_of_ne_of_ne hia hib, sub_self, if_neg hia, if_neg hib, add_zero]

theorem altAct_swap_sub {a b : Fin N} (hab : a ≠ b) (y : altHeart N) :
    altAct (swap a b) y - y = 0 ∨ altAct (swap a b) y - y = (pairEW a b : altHeart N) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [altAct_mk, ← QuotientAddGroup.mk_sub]
  rcases swap_sub_eq hab x with h | h
  · left
    rw [h, QuotientAddGroup.mk_zero]
  · right
    rw [h]

theorem altAct_fix_pair {τ : Perm (Fin N)} {a b : Fin N} (ha : τ a = a) (hb : τ b = b) :
    altAct τ (pairEW a b : altHeart N) = (pairEW a b : altHeart N) := by
  rw [altAct_mk, evenWeightPerm_pairEW, ha, hb]

theorem eq_of_pow_three {g : GLV V} (hg3 : g ^ 3 = 1) {m : V} (hz : g (g m - m) = g m - m) :
    g m = m := by
  have h3 : g (g (g m)) = m := by
    have := congrArg (fun f : GLV V => f m) hg3
    simpa [pow_succ, mul_assoc] using this
  have h2 : g (g m) = m := by
    have e : g m = m + (g m - m) := by abel
    calc g (g m) = g (m + (g m - m)) := by rw [← e]
      _ = g m + (g m - m) := by rw [map_add, hz]
      _ = m + ((g m - m) + (g m - m)) := by abel
      _ = m := by rw [vadd_self, add_zero]
  calc g m = g (g (g m)) := by rw [h2]
    _ = m := h3

theorem finrank_map_swap_le_one (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β)
    (hN : 7 ≤ N) {t : ↥H} (ht : (φ t).IsSwap) :
    Module.finrank (ZMod 2) ↥((commSpace (altSub H φ) ⊤).map
      (((t : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 1 := by
  obtain ⟨a, b, hab, hσ⟩ := ht
  obtain ⟨k, hka, hkb, -, -⟩ := exists_ne_four (by omega : 5 ≤ N) a b a b
  have hs0 : (t : GLV V) = tG φ (swap a b) := by rw [← hσ, tG_phi]
  obtain ⟨s, hs⟩ : ∃ s : GLV V, s = tG φ (swap a b) := ⟨_, rfl⟩
  rw [hs0, ← hs]
  have hsapp : ∀ v, s v = tG φ (swap a b) v := fun v => by rw [hs]
  have hsH : s ∈ H := by rw [hs]; exact tG_mem _
  have hc3 : (swap a b * swap b k).IsThreeCycle :=
    CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap hab (Ne.symm hka) (Ne.symm hkb)
  obtain ⟨c, hc⟩ : ∃ c : GLV V, c = tG φ (swap a b * swap b k) := ⟨_, rfl⟩
  have hcA : c ∈ altSub H φ := by rw [hc]; exact tG_mem_altSub hc3.mem_alternatingGroup
  have hcodd : Odd (orderOf c) := by
    rw [hc, orderOf_injective (tG φ) tG_injective, hc3.orderOf]
    decide
  set C := commSpace (Subgroup.zpowers c) ⊤ with hC
  have hsV₀ : ∀ v ∈ commSpace (altSub H φ) ⊤, s v ∈ commSpace (altSub H φ) ⊤ :=
    fun v hv => invariant_V₀ s hsH v hv
  have hperm : swap a b * (swap a b * swap b k) = (swap a b * swap b k)⁻¹ * swap a b := by
    rw [mul_inv_rev, swap_inv, swap_inv, ← mul_assoc, swap_mul_self, one_mul, mul_assoc,
      swap_mul_self, mul_one]
  have hsc : s * c = c⁻¹ * s := by
    rw [hs, hc, ← map_mul, ← map_inv, ← map_mul, hperm]
  have hsC : ∀ w ∈ C, s w ∈ C := by
    intro w hw
    rw [hC, commSpace_zpowers_top] at hw
    obtain ⟨v, rfl⟩ := hw
    have e : s ((((c : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V)) v) =
        c⁻¹ (s v) - s v := by
      have := congrArg (fun f : GLV V => f v) hsc
      simp only [LinearEquiv.mul_apply] at this
      simp [this]
    rw [e]
    exact sub_mem_commSpace (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) Submodule.mem_top
  set D : V →ₗ[ZMod 2] V := (s : V →ₗ[ZMod 2] V) - LinearMap.id with hD
  have hDapp : ∀ v, D v = s v - v := fun v => by simp [hD]
  let K : Subgroup (Perm (Fin N)) :=
    { carrier := {σ | ∀ v ∈ commSpace (altSub H φ) ⊤, tG φ σ v - v ∈ C.comap D}
      mul_mem' := fun {σ τ} hσ hτ v hv => by
        have hτv : tG φ τ v ∈ commSpace (altSub H φ) ⊤ := invariant_V₀ _ (tG_mem τ) v hv
        have h := (C.comap D).add_mem (hσ _ hτv) (hτ v hv)
        rwa [sub_add_sub_cancel, ← LinearEquiv.mul_apply, ← map_mul] at h
      one_mem' := fun v _ => by simp
      inv_mem' := fun {σ} hσ v hv => by
        have hv' : tG φ σ⁻¹ v ∈ commSpace (altSub H φ) ⊤ := invariant_V₀ _ (tG_mem _) v hv
        have h := (C.comap D).neg_mem (hσ _ hv')
        rw [neg_sub, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
        simpa using h }
  have hK3 : ∀ τ : Perm (Fin N), τ.IsThreeCycle → τ a = a → τ b = b → τ ∈ K := by
    intro τ hτ hτa hτb v hv
    have hcomm : tG φ τ * s = s * tG φ τ := by
      have h1 : τ * swap a b = swap a b * τ := by
        have h := swap_apply_apply τ a b
        rw [hτa, hτb] at h
        calc τ * swap a b = τ * swap a b * τ⁻¹ * τ := by group
          _ = swap a b * τ := by rw [← h]
      rw [hs, ← map_mul, ← map_mul, h1]
    have hm : s v - v ∈ commSpace (altSub H φ) ⊤ :=
      (commSpace (altSub H φ) ⊤).sub_mem (hsV₀ v hv) hv
    have hgm : tG φ τ (s v - v) ∈ commSpace (altSub H φ) ⊤ := invariant_V₀ _ (tG_mem τ) _ hm
    have hβm : β ⟨tG φ τ (s v - v), hgm⟩ = β ⟨s v - v, hm⟩ := by
      rw [beta_tG hH τ ⟨_, hm⟩ ⟨_, hgm⟩ rfl]
      have e1 : β ⟨s v - v, hm⟩ = altAct (swap a b) (β ⟨v, hv⟩) - β ⟨v, hv⟩ := by
        have e : (⟨s v - v, hm⟩ : ↥(commSpace (altSub H φ) ⊤)) =
            ⟨s v, hsV₀ v hv⟩ - ⟨v, hv⟩ := rfl
        rw [e, map_sub, beta_tG hH (swap a b) ⟨v, hv⟩ ⟨s v, hsV₀ v hv⟩ (hsapp v)]
      rw [e1]
      rcases altAct_swap_sub hab (β ⟨v, hv⟩) with h | h
      · rw [h, map_zero]
      · rw [h, altAct_fix_pair hτa hτb]
    have hz : tG φ τ (s v - v) - (s v - v) ∈ fixedSpace (altSub H φ) := by
      have hmem : tG φ τ (s v - v) - (s v - v) ∈ commSpace (altSub H φ) ⊤ :=
        (commSpace (altSub H φ) ⊤).sub_mem hgm hm
      refine mem_fixedSpace_of_beta hH ⟨_, hmem⟩ ?_
      have e : (⟨tG φ τ (s v - v) - (s v - v), hmem⟩ : ↥(commSpace (altSub H φ) ⊤)) =
          ⟨tG φ τ (s v - v), hgm⟩ - ⟨s v - v, hm⟩ := rfl
      rw [e, map_sub, hβm, sub_self]
    have hg3 : tG φ τ ^ 3 = 1 := by
      rw [← map_pow, ← hτ.orderOf, pow_orderOf_eq_one, map_one]
    have hfix : tG φ τ (s v - v) = s v - v :=
      eq_of_pow_three hg3 (hz _ (tG_mem_altSub hτ.mem_alternatingGroup))
    have h1 : s (tG φ τ v) = tG φ τ (s v) := by
      have := congrArg (fun f : GLV V => f v) hcomm
      simp only [LinearEquiv.mul_apply] at this
      exact this.symm
    show D (tG φ τ v - v) ∈ C
    have e : D (tG φ τ v - v) = tG φ τ (s v - v) - (s v - v) := by
      rw [hDapp, map_sub, map_sub, h1]
      abel
    rw [e, hfix, sub_self]
    exact C.zero_mem
  have hcK : swap a b * swap b k ∈ K := by
    intro v _
    show D (tG φ (swap a b * swap b k) v - v) ∈ C
    rw [← hc]
    have hcv : c v - v ∈ C := sub_mem_commSpace (Subgroup.mem_zpowers c) Submodule.mem_top
    rw [hDapp]
    exact C.sub_mem (hsC _ hcv) hcv
  have hAK : alternatingGroup (Fin N) ≤ K :=
    alternatingGroup_le_of_threeCycles (by omega) hab (Ne.symm hka) (Ne.symm hkb) hK3 hcK
  have hM : ∀ v ∈ commSpace (altSub H φ) ⊤, s v - v ∈ C := by
    have hle : commSpace (altSub H φ) (commSpace (altSub H φ) ⊤) ≤ C.comap D := by
      refine commSpace_le_iff.2 fun g hg u hu => ?_
      obtain ⟨σ, hσ, rfl⟩ := exists_eq_tG hg
      exact hAK hσ u hu
    intro v hv
    rw [← commSpace_commSpace_top_of_perfect (altSub_perfect (by omega))] at hv
    have := hle hv
    rwa [Submodule.mem_comap, hDapp] at this
  have hMV₀ : (commSpace (altSub H φ) ⊤).map D ≤ commSpace (altSub H φ) ⊤ := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hDapp]
    exact (commSpace (altSub H φ) ⊤).sub_mem (hsV₀ v hv) hv
  let F : ↥((commSpace (altSub H φ) ⊤).map D) →+ ZMod 2 :=
    (CaseIHeart.pairFun a k).comp (β.comp (Submodule.inclusion hMV₀).toAddMonoidHom)
  have hF : Function.Injective F := by
    refine (injective_iff_map_eq_zero F).2 fun m hm0 => ?_
    obtain ⟨_, v, hv, rfl⟩ := m
    have hincl : (Submodule.inclusion hMV₀ ⟨D v, v, hv, rfl⟩ : ↥(commSpace (altSub H φ) ⊤)) =
        ⟨s v, hsV₀ v hv⟩ - ⟨v, hv⟩ := Subtype.ext (by simp [hDapp])
    have hβ : β (Submodule.inclusion hMV₀ ⟨D v, v, hv, rfl⟩) =
        altAct (swap a b) (β ⟨v, hv⟩) - β ⟨v, hv⟩ := by
      rw [hincl, map_sub, beta_tG hH (swap a b) ⟨v, hv⟩ ⟨s v, hsV₀ v hv⟩ (hsapp v)]
    have hβ0 : β (Submodule.inclusion hMV₀ ⟨D v, v, hv, rfl⟩) = 0 := by
      rcases altAct_swap_sub hab (β ⟨v, hv⟩) with h | h
      · rw [hβ, h]
      · exfalso
        have h1 : F ⟨D v, v, hv, rfl⟩ = 1 := by
          show CaseIHeart.pairFun a k (β (Submodule.inclusion hMV₀ ⟨D v, v, hv, rfl⟩)) = 1
          rw [hβ, h, CaseIHeart.pairFun_mk, pairEW_apply, pairEW_apply]
          simp [hab, hka, hkb]
        rw [h1] at hm0
        exact absurd hm0 (by decide)
    have hC' : ((Submodule.inclusion hMV₀ ⟨D v, v, hv, rfl⟩ : ↥(commSpace (altSub H φ) ⊤)) : V)
        ∈ C := by
      show D v ∈ C
      rw [hDapp]
      exact hM v hv
    have h0 := CaseIHeart.injOn hH hcA hcodd hC' hβ0
    exact Subtype.ext h0
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_zmod, CaseIHeart.card_eq_two_pow] at hcard
  by_contra hlt
  push Not at hlt
  have : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) ↥((commSpace (altSub H φ) ⊤).map D) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem exists_vec (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β) (t : ↥H)
    (y : evenWeight N) :
    ∃ w : ↥(commSpace (altSub H φ) ⊤), (w : V) ∈ commSpace (Subgroup.zpowers (t : GLV V)) ⊤ ∧
      β w = ((evenWeightPerm (φ t) y - y : evenWeight N) : altHeart N) := by
  obtain ⟨u, hu⟩ := hH.surj (y : altHeart N)
  have htu : (t : GLV V) (u : V) ∈ commSpace (altSub H φ) ⊤ := invariant_V₀ _ t.2 _ u.2
  refine ⟨⟨_, htu⟩ - u, sub_mem_commSpace (Subgroup.mem_zpowers _) Submodule.mem_top, ?_⟩
  rw [map_sub, hH.equiv t u ⟨_, htu⟩ rfl y hu, hu]
  rfl

theorem three_le (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β) {t : GLV V}
    (ht : t ∈ H) (x : Fin 3 → ↥(commSpace (altSub H φ) ⊤))
    (hx : ∀ i, (x i : V) ∈ commSpace (Subgroup.zpowers t) ⊤)
    (μ : Fin 3 → (altHeart N →+ ZMod 2)) (hμ : ∀ i k, μ i (β (x k)) = if i = k then 1 else 0) :
    Module.finrank (ZMod 2) ↥((fixedSpace (altSub H φ)).map
        ((t : V →ₗ[ZMod 2] V) - LinearMap.id)) + 3 ≤
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers t) ⊤) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set R₁ := (fixedSpace (altSub H φ)).map ((t : V →ₗ[ZMod 2] V) - LinearMap.id) with hR₁
  have hR₁R : R₁ ≤ commSpace (Subgroup.zpowers t) ⊤ := by
    rw [hR₁, commSpace_zpowers_top]
    exact LinearMap.map_le_range
  have hR₁V : R₁ ≤ fixedSpace (altSub H φ) := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    exact (fixedSpace (altSub H φ)).sub_mem (invariant_V₁ t ht v hv) hv
  set xs : Fin 3 → V := fun i => (x i : V) with hxs
  let Θ : Fin 3 → (↥(commSpace (altSub H φ) ⊤) →ₗ[ZMod 2] ZMod 2) := fun k =>
    ((μ k).comp β).toZModLinearMap 2
  have key : ∀ ε : Fin 3 → ZMod 2, ∑ i, ε i • xs i ∈ fixedSpace (altSub H φ) → ε = 0 := by
    intro ε hε
    have hyV : ((∑ i, ε i • x i : ↥(commSpace (altSub H φ) ⊤)) : V) = ∑ i, ε i • xs i := by
      rw [Submodule.coe_sum]
      rfl
    have hβy : β (∑ i, ε i • x i) = 0 := beta_eq_zero hH _ (by rw [hyV]; exact hε)
    funext k
    have h1 : Θ k (∑ i, ε i • x i) = ε k := by
      rw [map_sum]
      simp only [map_smul, Θ, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.comp_apply, hμ,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 : Θ k (∑ i, ε i • x i) = 0 := by
      simp only [Θ, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.comp_apply, hβy, map_zero]
    rw [← h1, h2]
    rfl
  have hli : LinearIndependent (ZMod 2) xs := Fintype.linearIndependent_iff.2 fun g hg => by
    have := key g (by rw [hg]; exact (fixedSpace (altSub H φ)).zero_mem)
    intro i
    rw [this]
    rfl
  have hX : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range xs)) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hXR : Submodule.span (ZMod 2) (Set.range xs) ≤ commSpace (Subgroup.zpowers t) ⊤ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  have hdisj : R₁ ⊓ Submodule.span (ZMod 2) (Set.range xs) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨ε, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hy2
    have := key ε (hR₁V hy1)
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq R₁ (Submodule.span (ZMod 2) (Set.range xs))
  rw [hdisj, finrank_bot, hX, add_zero] at h
  have h2 := Submodule.finrank_mono (sup_le hR₁R hXR)
  omega

theorem inj3 {α : Type*} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd h hxy | exact absurd h hxz | exact absurd h hyz
    | exact absurd h.symm hxy | exact absurd h.symm hxz | exact absurd h.symm hyz

theorem pairFun_dual {τ : Perm (Fin N)} (a : Fin 3 → Fin N) (q r : Fin N)
    (ha : Function.Injective a) (haτ : ∀ k i, a k ≠ τ (a i)) (haq : ∀ k, a k ≠ q)
    (haτq : ∀ k, a k ≠ τ q) (hra : ∀ i, r ≠ a i) (hrτa : ∀ i, r ≠ τ (a i))
    (hrq : (r = q ∧ τ q = q) ∨ (r ≠ q ∧ r ≠ τ q)) (k i : Fin 3) :
    CaseIHeart.pairFun (a k) r
        ((evenWeightPerm τ (pairEW (a i) q) - pairEW (a i) q : evenWeight N) : altHeart N) =
      if k = i then 1 else 0 := by
  rw [CaseIHeart.pairFun_comm, if_neg (haτ k i), if_neg (haτq k), if_neg (haq k),
    if_neg (hrτa i), if_neg (hra i)]
  have hlast : ((0 : ZMod 2) + if r = τ q then 1 else 0) - (0 + if r = q then 1 else 0) = 0 := by
    rcases hrq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos (h1.trans h2.symm), if_pos h1, sub_self]
    · rw [if_neg h2, if_neg h1, sub_self]
  rw [hlast, add_zero]
  by_cases hki : k = i
  · subst hki
    simp only [if_true]
    decide
  · rw [if_neg (fun h => hki (ha h)), if_neg hki]
    decide

theorem lower_bound (hH : CaseIHeart.HeartFor H N φ.toMonoidHom (altSub H φ) β) (hN : 7 ≤ N)
    (t : ↥H) (ht2 : φ t * φ t = 1) (hsign : sign (φ t) = -1) (hns : ¬ (φ t).IsSwap) :
    Module.finrank (ZMod 2) ↥((fixedSpace (altSub H φ)).map
        (((t : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id)) + 3 ≤
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (t : GLV V)) ⊤) := by
  classical
  set τ := φ t with hτdef
  obtain ⟨hcard, hsgn⟩ := CaseIPerm.card_support_of_mul_self ht2
  have hmodd : Odd τ.cycleType.card := by
    rcases Nat.even_or_odd τ.cycleType.card with he | ho
    · rw [hsgn, he.neg_one_pow] at hsign
      exact absurd hsign (by decide)
    · exact ho
  have hm1 : τ.cycleType.card ≠ 1 := fun h => hns (card_support_eq_two.1 (by rw [hcard, h]))
  have h6 : 6 ≤ τ.support.card := by
    obtain ⟨r, hr⟩ := hmodd
    omega
  have hinv : ∀ x, τ (τ x) = x := fun x => by rw [← Perm.mul_apply, ht2, Perm.one_apply]
  have hgen : ∀ (a : Fin 3 → Fin N) (q r : Fin N), Function.Injective a →
      (∀ k i, a k ≠ τ (a i)) → (∀ k, a k ≠ q) → (∀ k, a k ≠ τ q) → (∀ i, r ≠ a i) →
      (∀ i, r ≠ τ (a i)) → ((r = q ∧ τ q = q) ∨ (r ≠ q ∧ r ≠ τ q)) →
      Module.finrank (ZMod 2) ↥((fixedSpace (altSub H φ)).map
          (((t : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id)) + 3 ≤
        Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (t : GLV V)) ⊤) := by
    intro a q r ha haτ haq haτq hra hrτa hrq
    choose w hw hβw using fun i : Fin 3 => exists_vec hH t (pairEW (a i) q)
    refine three_le hH t.2 w hw (fun k => CaseIHeart.pairFun (a k) r) fun k i => ?_
    rw [hβw i]
    exact pairFun_dual a q r ha haτ haq haτq hra hrτa hrq k i
  have hne_of_mem : ∀ {x}, x ∈ τ.support → τ x ≠ x := fun hx => Perm.mem_support.1 hx
  obtain ⟨a₁, ha₁⟩ : ∃ a, a ∈ τ.support := Finset.card_pos.1 (by omega)
  obtain ⟨a₂, ha₂, ha₂'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a₁, τ a₁}) (t := τ.support) (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨a₃, ha₃, ha₃'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a₁, τ a₁, a₂, τ a₂}) (t := τ.support) (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₂' ha₃'
  obtain ⟨h21, h21'⟩ := ha₂'
  obtain ⟨h31, h31', h32, h32'⟩ := ha₃'
  have n1 := hne_of_mem ha₁
  have n2 := hne_of_mem ha₂
  have n3 := hne_of_mem ha₃
  have m21 : τ a₂ ≠ a₁ := fun h => h21' (by rw [← h, hinv])
  have m21' : τ a₂ ≠ τ a₁ := fun h => h21 (τ.injective h)
  have m31 : τ a₃ ≠ a₁ := fun h => h31' (by rw [← h, hinv])
  have m31' : τ a₃ ≠ τ a₁ := fun h => h31 (τ.injective h)
  have m32 : τ a₃ ≠ a₂ := fun h => h32' (by rw [← h, hinv])
  have m32' : τ a₃ ≠ τ a₂ := fun h => h32 (τ.injective h)
  have hainj : Function.Injective ![a₁, a₂, a₃] := inj3 (Ne.symm h21) (Ne.symm h31) (Ne.symm h32)
  have haτ : ∀ k i, ![a₁, a₂, a₃] k ≠ τ (![a₁, a₂, a₃] i) := by
    intro k i
    fin_cases k <;> fin_cases i <;> first | assumption | exact Ne.symm (by assumption)
  by_cases hfix : ∃ d, τ d = d
  ·
    obtain ⟨d, hd⟩ := hfix
    have hd1 : d ≠ a₁ := fun h => n1 (by rw [← h]; exact hd)
    have hd2 : d ≠ a₂ := fun h => n2 (by rw [← h]; exact hd)
    have hd3 : d ≠ a₃ := fun h => n3 (by rw [← h]; exact hd)
    have hda : ∀ i, d ≠ ![a₁, a₂, a₃] i := by
      intro i
      fin_cases i <;> assumption
    have hdτa : ∀ i, d ≠ τ (![a₁, a₂, a₃] i) := by
      intro i h
      have h' : τ d = ![a₁, a₂, a₃] i := by rw [h, hinv]
      exact hda i (hd.symm.trans h')
    refine hgen ![a₁, a₂, a₃] d d hainj haτ (fun k => (hda k).symm) (fun k => ?_) hda hdτa
      (Or.inl ⟨rfl, hd⟩)
    rw [hd]
    exact (hda k).symm
  ·
    push Not at hfix
    have hsupp : τ.support = Finset.univ :=
      Finset.eq_univ_of_forall fun x => Perm.mem_support.2 (hfix x)
    have hcardN : τ.support.card = N := by rw [hsupp, Finset.card_univ, Fintype.card_fin]
    have h10 : 10 ≤ τ.support.card := by
      obtain ⟨r, hr⟩ := hmodd
      omega
    obtain ⟨a₄, ha₄, ha₄'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, τ a₁, a₂, τ a₂, a₃, τ a₃}) (t := τ.support)
      (lt_of_le_of_lt Finset.card_le_six (by omega))
    have hcard8 : ({a₁, τ a₁, a₂, τ a₂, a₃, τ a₃, a₄, τ a₄} : Finset (Fin N)).card ≤ 8 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right Finset.card_le_six 1)) 1)
    obtain ⟨a₅, -, ha₅'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, τ a₁, a₂, τ a₂, a₃, τ a₃, a₄, τ a₄}) (t := τ.support)
      (lt_of_le_of_lt hcard8 (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₄' ha₅'
    obtain ⟨h41, h41', h42, h42', h43, h43'⟩ := ha₄'
    obtain ⟨h51, h51', h52, h52', h53, h53', h54, h54'⟩ := ha₅'
    have m41 : τ a₄ ≠ a₁ := fun h => h41' (by rw [← h, hinv])
    have m42 : τ a₄ ≠ a₂ := fun h => h42' (by rw [← h, hinv])
    have m43 : τ a₄ ≠ a₃ := fun h => h43' (by rw [← h, hinv])
    have haq : ∀ k, ![a₁, a₂, a₃] k ≠ a₄ := by
      intro k
      fin_cases k
      · exact Ne.symm h41
      · exact Ne.symm h42
      · exact Ne.symm h43
    have haτq : ∀ k, ![a₁, a₂, a₃] k ≠ τ a₄ := by
      intro k
      fin_cases k
      · exact Ne.symm m41
      · exact Ne.symm m42
      · exact Ne.symm m43
    have hra : ∀ i, a₅ ≠ ![a₁, a₂, a₃] i := by
      intro i
      fin_cases i
      · exact h51
      · exact h52
      · exact h53
    have hrτa : ∀ i, a₅ ≠ τ (![a₁, a₂, a₃] i) := by
      intro i
      fin_cases i
      · exact h51'
      · exact h52'
      · exact h53'
    exact hgen ![a₁, a₂, a₃] a₄ a₅ hainj haτ haq haτq hra hrτa (Or.inr ⟨h54, h54'⟩)

end Lemma25Aux

open Lemma25Aux in
theorem caseIFooteLemma25_holds : CaseIFooteLemma25 := by
  intro V _ _ _ H N φ hN ⟨β, hβs, hβk, hβc⟩ t₁ t₂ ht₁ ht₂ hsign
  by_cases hsw : (φ t₂).IsSwap
  · exact Or.inl hsw
  right
  have hH := heartFor hβs hβk hβc
  obtain ⟨v₀, hv₀⟩ := exists_complement hH hN
  have h1 := finrank_le_of_top hv₀ (t₁ : GLV V)
  have h2 := finrank_map_swap_le_one hH hN ht₁
  have h3 := lower_bound hH hN t₂ ht₂ hsign hsw
  have h4 := map_fixedSpace_eq (φ := φ) (t₁ := t₁) (t₂ := t₂) (by rw [hsign, ht₁.sign_eq])
  rw [h4] at h1
  omega

end CFSG.CGT.Foote82

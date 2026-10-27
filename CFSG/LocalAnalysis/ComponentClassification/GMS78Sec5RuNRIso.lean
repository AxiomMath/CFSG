module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRSplit

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.ComponentClassification.GMS78.RuSModel

section Cert

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

theorem card_kConj (c : MulAut RuR) : Nat.card (kConj c) = 168 := by
  rw [kConj, Subgroup.card_map_of_injective (MulAut.conj c).injective, card_nK]

theorem exists_ruNIso_of_conjData [Finite G] (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) (hcardR : Nat.card R = 2048)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G)) {c : MulAut RuR}
    (hc : ConjData hM hS c) :
    ∃ f : RuNModel ≃* ↥(normalizer (gmsA L T : Set G)),
      ∀ m, m ∈ A1model ↔ ((f m : ↥(normalizer (gmsA L T : Set G))) : G) ∈ gmsA L T := by
  classical
  obtain ⟨K₀, hK₀K, hK₀A, hK₀c⟩ := exists_compl hM hS hNC hidx hcardR hc
  have hK₀N : K₀ ≤ normalizer (R : Set G) := hK₀K.trans (kTil_le_normalizer hM hS c)
  have hK₀R : K₀ ⊓ R = ⊥ := by
    have h : K₀ ⊓ R = K₀ ⊓ gmsA L T := by
      rw [← kTil_inf_R hM hS hNC hc, ← inf_assoc, inf_of_le_left hK₀K]
    rw [h, hK₀A]
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc.sq
  set ψ₀ : K₀ →* MulAut RuR := (actN hM hS).comp (Subgroup.inclusion hK₀N) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ := by
    refine (injective_iff_map_eq_one ψ₀).mpr fun k hk => ?_
    have hA := mem_A_of_actN_eq_one hM hS hNC (Subgroup.inclusion hK₀N k) hk
    have h : (k : G) ∈ K₀ ⊓ gmsA L T := ⟨k.2, hA⟩
    rw [hK₀A, mem_bot] at h
    exact Subtype.ext h
  have hψ₀range : ψ₀.range = kConj c := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨k, rfl⟩
      obtain ⟨hg, h⟩ := (mem_kTil_iff hM hS c k).mp (hK₀K k.2)
      exact h
    · rw [card_kConj, ← Nat.card_congr (MonoidHom.ofInjective hψ₀inj).toEquiv, hK₀c]
  set e₁ : K₀ ≃* kConj c :=
    (MonoidHom.ofInjective hψ₀inj).trans (MulEquiv.subgroupCongr hψ₀range) with he₁
  set e₂ : nK ≃* kConj c := (MulAut.conj c).subgroupMap nK with he₂
  set κ : nK →* G := K₀.subtype.comp (e₂.trans e₁.symm).toMonoidHom with hκ
  have hκK : ∀ k, κ k ∈ K₀ := fun k => ((e₂.trans e₁.symm) k).2
  have hκN : ∀ k, κ k ∈ normalizer (R : Set G) := fun k => hK₀N (hκK k)
  have hκact : ∀ k : nK, actN hM hS ⟨κ k, hκN k⟩ = c * (k : MulAut RuR) * c := by
    intro k
    have h1 : ((e₁ ((e₂.trans e₁.symm) k) : kConj c) : MulAut RuR) = (e₂ k : MulAut RuR) := by
      simp
    have h2 : ((e₁ ((e₂.trans e₁.symm) k) : kConj c) : MulAut RuR) =
        actN hM hS ⟨κ k, hκN k⟩ := rfl
    rw [← h2, h1]
    change MulAut.conj c k = _
    rw [MulAut.conj_apply, hci]
  have hκinj : Function.Injective κ := by
    intro k k' h
    exact (e₂.trans e₁.symm).injective (Subtype.ext h)
  set θ' : RuR →* G := (thetaR hS).comp c.toMonoidHom with hθ'
  have hθ'R : ∀ x, θ' x ∈ R := fun x => thetaR_mem hS _
  have hcompat : ∀ g : nK, θ'.comp ((nK.subtype g).toMonoidHom) =
      (MulAut.conj (κ g)).toMonoidHom.comp θ' := by
    intro g
    refine MonoidHom.ext fun x => ?_
    change thetaR hS (c ((g : MulAut RuR) x)) = κ g * thetaR hS (c x) * (κ g)⁻¹
    rw [← actN_apply hM hS ⟨κ g, hκN g⟩, hκact]
    change thetaR hS (c ((g : MulAut RuR) x)) = thetaR hS (c ((g : MulAut RuR) (c (c x))))
    rw [show c (c x) = (c * c) x from rfl, hc.sq]
    rfl
  set f₀ : RuNModel →* G := SemidirectProduct.lift θ' κ hcompat with hf₀
  have hf₀apply : ∀ m : RuNModel, f₀ m = θ' m.left * κ m.right := by
    intro m
    rw [← SemidirectProduct.inl_left_mul_inr_right m, map_mul, SemidirectProduct.lift_inl,
      SemidirectProduct.lift_inr]
    simp
  have hf₀N : ∀ m, f₀ m ∈ normalizer (R : Set G) := fun m => by
    rw [hf₀apply]
    exact mul_mem (le_normalizer (hθ'R _)) (hκN _)
  set f₁ : RuNModel →* ↥(normalizer (R : Set G)) := f₀.codRestrict _ hf₀N with hf₁
  have hf₁inj : Function.Injective f₁ := by
    refine (injective_iff_map_eq_one f₁).mpr fun m hm => ?_
    have h0 : f₀ m = 1 := congrArg Subtype.val hm
    rw [hf₀apply] at h0
    have hκR : κ m.right ∈ R := by
      have : κ m.right = (θ' m.left)⁻¹ := eq_inv_of_mul_eq_one_right h0
      rw [this]
      exact inv_mem (hθ'R _)
    have hκ1 : κ m.right = 1 := by
      have h : κ m.right ∈ K₀ ⊓ R := ⟨hκK _, hκR⟩
      rwa [hK₀R, mem_bot] at h
    have hr1 : m.right = 1 := hκinj (hκ1.trans (map_one κ).symm)
    rw [hκ1, mul_one] at h0
    have hl1 : m.left = 1 := by
      have h1 : thetaR hS (c m.left) = thetaR hS (c 1) := by
        rw [map_one, map_one]
        exact h0
      exact c.injective (thetaR_injective hS h1)
    exact SemidirectProduct.ext hl1 hr1
  have hf₁bij : Function.Bijective f₁ := by
    refine hf₁inj.bijective_of_nat_card_le ?_
    rw [card_RuNModel, card_normalizer hidx hcardR]
  set f : RuNModel ≃* ↥(normalizer (gmsA L T : Set G)) :=
    (MulEquiv.ofBijective f₁ hf₁bij).trans (MulEquiv.subgroupCongr hNA.symm) with hf
  refine ⟨f, fun m => ?_⟩
  have hfm : ((f m : ↥(normalizer (gmsA L T : Set G))) : G) = f₀ m := rfl
  rw [hfm, hf₀apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x = ⟨0, x.t⟩ := RuR.ext hx rfl
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
    change thetaR hS (c x) ∈ gmsA L T
    rw [hx0, hc.fix_A]
    exact (thetaR_A1 hS _).1
  · intro hA
    have hAR := A_le_R hM hA
    have hκR : κ m.right ∈ R := by
      have : κ m.right = (θ' m.left)⁻¹ * (θ' m.left * κ m.right) := by group
      rw [this]
      exact mul_mem (inv_mem (hθ'R _)) hAR
    have hκ1 : κ m.right = 1 := by
      have h : κ m.right ∈ K₀ ⊓ R := ⟨hκK _, hκR⟩
      rwa [hK₀R, mem_bot] at h
    have hr1 : m.right = 1 := hκinj (hκ1.trans (map_one κ).symm)
    rw [hκ1, mul_one] at hA
    have hcx : c m.left ∈ A1R := by
      have : thetaR hS (c m.left) ∈ A1R.map (thetaR hS) := by
        rw [map_thetaR_A1R hM hS]
        exact hA
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← (thetaR_injective hS) hyx]
    have hx : m.left ∈ A1R := by
      have := hc.fix_m m.left
      rw [mem_A1R_iff] at hcx ⊢
      rw [← this, hcx]
    refine ⟨m.left, hx, ?_⟩
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right m]
    rw [hr1, map_one, mul_one]

end Cert

end CFSG.ComponentClassification.GMS78.RuN

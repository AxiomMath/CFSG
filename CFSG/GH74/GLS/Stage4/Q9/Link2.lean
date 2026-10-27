module

public import CFSG.GH74.GLS.Stage4.Q9.SettingFacts
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

namespace Link2

@[expose] def hom2 {G : Type*} [Group G] (t : G) (ht : t ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G where
  toFun a := t ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ ht]

theorem hom2_ofAdd_one {G : Type*} [Group G] (t : G) (ht : t ^ 2 = 1) :
    hom2 t ht (Multiplicative.ofAdd 1) = t := by
  have h : (1 : ZMod 2).val = 1 := rfl
  show t ^ (1 : ZMod 2).val = t
  rw [h, pow_one]

theorem eq_one_or_eq_ofAdd_one (ε : Multiplicative (ZMod 2)) :
    ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by
  revert ε; decide

theorem symm_sigmaAut_eq {G : Type*} [Group G] {K : Subgroup G} {t : G}
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (ψ : K ≃* SL2)
    (ht : ∀ k k' : K, (k' : G) = t * (k : G) * t⁻¹ → ψ k' = sigmaAut (ψ k)) (M : SL2) :
    ((ψ.symm (sigmaAut M) : K) : G) = t * ((ψ.symm M : K) : G) * t⁻¹ := by
  have h := ht (ψ.symm M) ⟨t * ((ψ.symm M : K) : G) * t⁻¹, hnorm _ (ψ.symm M).2⟩ rfl
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (⟨t * ((ψ.symm M : K) : G) * t⁻¹, hnorm _ (ψ.symm M).2⟩ : K) =
      ψ.symm (sigmaAut M) := by
    rw [← h, MulEquiv.symm_apply_apply]
  rw [← h2]

theorem symm_sigmaHom_eq {G : Type*} [Group G] {K : Subgroup G} {t : G} (htt : t ^ 2 = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (ψ : K ≃* SL2)
    (ht : ∀ k k' : K, (k' : G) = t * (k : G) * t⁻¹ → ψ k' = sigmaAut (ψ k))
    (ε : Multiplicative (ZMod 2)) (M : SL2) :
    ((ψ.symm (sigmaHom ε M) : K) : G) =
      hom2 t htt ε * ((ψ.symm M : K) : G) * (hom2 t htt ε)⁻¹ := by
  rcases eq_one_or_eq_ofAdd_one ε with rfl | rfl
  · simp
  · rw [sigmaHom_ofAdd_one, hom2_ofAdd_one]
    exact symm_sigmaAut_eq hnorm ψ ht M

@[expose] def invHom {G : Type*} [Group G] {K : Subgroup G} (ψ : K ≃* SL2) : SL2 →* G :=
  K.subtype.comp ψ.symm.toMonoidHom

theorem invHom_apply {G : Type*} [Group G] {K : Subgroup G} (ψ : K ≃* SL2) (M : SL2) :
    invHom ψ M = ((ψ.symm M : K) : G) := rfl

theorem invHom_injective {G : Type*} [Group G] {K : Subgroup G} (ψ : K ≃* SL2) :
    Function.Injective (invHom ψ) :=
  Subtype.val_injective.comp ψ.symm.injective

@[expose] def iotaHom {G : Type*} [Group G] (f : SL2 →* G) (τ : Multiplicative (ZMod 2) →* G)
    (h : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f (sigmaHom ε M) = τ ε * f M * (τ ε)⁻¹) :
    Lg →* G :=
  SemidirectProduct.lift f τ fun ε => by
    ext M
    simpa using h ε M

section Iota

variable {G : Type*} [Group G] (f : SL2 →* G) (τ : Multiplicative (ZMod 2) →* G)
  (h : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f (sigmaHom ε M) = τ ε * f M * (τ ε)⁻¹)

theorem iotaHom_innerL (M : SL2) : iotaHom f τ h (innerL M) = f M :=
  SemidirectProduct.lift_inl _ _ _ _

theorem iotaHom_tauL : iotaHom f τ h tauL = τ (Multiplicative.ofAdd 1) :=
  SemidirectProduct.lift_inr _ _ _ (Multiplicative.ofAdd 1)

theorem iotaHom_injective (hf : Function.Injective f)
    (ht : ∀ M : SL2, f M * τ (Multiplicative.ofAdd 1) ≠ 1) :
    Function.Injective (iotaHom f τ h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨M, ε⟩ hl
  change f M * τ ε = 1 at hl
  rcases eq_one_or_eq_ofAdd_one ε with rfl | rfl
  · rw [map_one, mul_one] at hl
    have hM : M = 1 := hf (hl.trans (map_one f).symm)
    subst hM
    rfl
  · exact absurd hl (ht M)

end Iota

@[expose] def piHom {G : Type*} [Group G] (f₁ f₂ : SL2 →* G) (τ : Multiplicative (ZMod 2) →* G)
    (hcomm : ∀ M N : SL2, f₁ M * f₂ N = f₂ N * f₁ M)
    (h₁ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f₁ (sigmaHom ε M) = τ ε * f₁ M * (τ ε)⁻¹)
    (h₂ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f₂ (sigmaHom ε M) = τ ε * f₂ M * (τ ε)⁻¹) :
    ↥Chat →* G where
  toFun c := f₁ c.1.1.left * f₂ c.1.2.left * τ c.1.1.right
  map_one' := by simp
  map_mul' := by
    rintro ⟨⟨l₁, l₂⟩, h⟩ ⟨⟨l₁', l₂'⟩, h'⟩
    have hε : l₁.right = l₂.right := h
    show f₁ (l₁ * l₁').left * f₂ (l₂ * l₂').left * τ (l₁ * l₁').right =
      (f₁ l₁.left * f₂ l₂.left * τ l₁.right) * (f₁ l₁'.left * f₂ l₂'.left * τ l₁'.right)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      ← hε]
    simp only [map_mul]
    have e := hcomm (sigmaHom l₁.right l₁'.left) l₂.left
    calc f₁ l₁.left * f₁ (sigmaHom l₁.right l₁'.left) *
          (f₂ l₂.left * f₂ (sigmaHom l₁.right l₂'.left)) * (τ l₁.right * τ l₁'.right)
        = f₁ l₁.left * (f₁ (sigmaHom l₁.right l₁'.left) * f₂ l₂.left) *
          f₂ (sigmaHom l₁.right l₂'.left) * (τ l₁.right * τ l₁'.right) := by
          simp only [mul_assoc]
      _ = f₁ l₁.left * (f₂ l₂.left * f₁ (sigmaHom l₁.right l₁'.left)) *
          f₂ (sigmaHom l₁.right l₂'.left) * (τ l₁.right * τ l₁'.right) := by rw [e]
      _ = _ := by rw [h₁, h₂]; group

section Pi

variable {G : Type*} [Group G] (f₁ f₂ : SL2 →* G) (τ : Multiplicative (ZMod 2) →* G)
  (hcomm : ∀ M N : SL2, f₁ M * f₂ N = f₂ N * f₁ M)
  (h₁ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f₁ (sigmaHom ε M) = τ ε * f₁ M * (τ ε)⁻¹)
  (h₂ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), f₂ (sigmaHom ε M) = τ ε * f₂ M * (τ ε)⁻¹)

theorem piHom_apply (c : ↥Chat) :
    piHom f₁ f₂ τ hcomm h₁ h₂ c = f₁ c.1.1.left * f₂ c.1.2.left * τ c.1.1.right := rfl

theorem piHom_inner (M N : SL2) :
    piHom f₁ f₂ τ hcomm h₁ h₂ ⟨(innerL M, innerL N), Chat_inner_pair M N⟩ = f₁ M * f₂ N := by
  show f₁ M * f₂ N * τ 1 = _
  rw [map_one, mul_one]

theorem piHom_tauHat :
    piHom f₁ f₂ τ hcomm h₁ h₂ ⟨tauHat, tauHat_mem⟩ = τ (Multiplicative.ofAdd 1) := by
  show f₁ 1 * f₂ 1 * τ (Multiplicative.ofAdd 1) = _
  rw [map_one, map_one, one_mul, one_mul]

theorem piHom_eq_one_iff
    (ht : ∀ M N : SL2, f₁ M * f₂ N * τ (Multiplicative.ofAdd 1) ≠ 1)
    (hz : ∀ M N : SL2, f₁ M * f₂ N = 1 → (M = 1 ∧ N = 1) ∨ (M = minusOne ∧ N = minusOne))
    (hk : f₁ minusOne * f₂ minusOne = 1) (c : ↥Chat) :
    piHom f₁ f₂ τ hcomm h₁ h₂ c = 1 ↔ (c : Lg × Lg) = 1 ∨ (c : Lg × Lg) = kappa0 := by
  rcases c with ⟨⟨l₁, l₂⟩, h⟩
  have hε : l₁.right = l₂.right := h
  constructor
  · intro hc
    rw [piHom_apply] at hc
    change f₁ l₁.left * f₂ l₂.left * τ l₁.right = 1 at hc
    rcases eq_one_or_eq_ofAdd_one l₁.right with h1 | h1
    · rw [h1, map_one, mul_one] at hc
      have h2 : l₂.right = 1 := hε.symm.trans h1
      have hl₁ : l₁ = innerL l₁.left := SemidirectProduct.ext rfl h1
      have hl₂ : l₂ = innerL l₂.left := SemidirectProduct.ext rfl h2
      rcases hz _ _ hc with ⟨hM, hN⟩ | ⟨hM, hN⟩
      · left
        show (l₁, l₂) = 1
        rw [hl₁, hl₂, hM, hN, map_one]
        rfl
      · right
        show (l₁, l₂) = kappa0
        rw [hl₁, hl₂, hM, hN]
        rfl
    · rw [h1] at hc
      exact absurd hc (ht _ _)
  · rintro (h1 | h1)
    · have : (⟨(l₁, l₂), h⟩ : ↥Chat) = 1 := Subtype.ext h1
      rw [this, map_one]
    · rw [piHom_apply]
      change f₁ l₁.left * f₂ l₂.left * τ l₁.right = 1
      have h3 : l₁ = innerL minusOne := congrArg Prod.fst h1
      have h4 : l₂ = innerL minusOne := congrArg Prod.snd h1
      rw [h3, h4]
      change f₁ minusOne * f₂ minusOne * τ 1 = 1
      rw [map_one, mul_one]
      exact hk

end Pi

end Link2

open Link2

theorem q9_link2 {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) (ψ₁ : ↥K₁ ≃* SL2) (ψ₂ : ↥K₂ ≃* SL2)
    (hz₁ : ∀ k : ↥K₁, (k : G) = z → ψ₁ k = minusOne)
    (hz₂ : ∀ k : ↥K₂, (k : G) = z → ψ₂ k = minusOne)
    (ht₁ : ∀ k k' : ↥K₁, (k' : G) = S.t * (k : G) * S.t⁻¹ → ψ₁ k' = sigmaAut (ψ₁ k))
    (ht₂ : ∀ k k' : ↥K₂, (k' : G) = S.t * (k : G) * S.t⁻¹ → ψ₂ k' = sigmaAut (ψ₂ k)) :
    ∃ (ι₁ ι₂ : Lg →* G) (π : ↥Chat →* G),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ M : SL2, ι₁ (innerL M) = ((ψ₁.symm M : ↥K₁) : G)) ∧
      (∀ M : SL2, ι₂ (innerL M) = ((ψ₂.symm M : ↥K₂) : G)) ∧
      ι₁ tauL = S.t ∧ ι₂ tauL = S.t ∧
      (∀ c : ↥Chat, π c ∈ Subgroup.centralizer ({z} : Set G)) ∧
      (∀ g ∈ Subgroup.centralizer ({z} : Set G), ∃ c : ↥Chat, π c = g) ∧
      (∀ c : ↥Chat, π c = 1 ↔ (c : Lg × Lg) = 1 ∨ (c : Lg × Lg) = kappa0) ∧
      (∀ M N : SL2, π ⟨(innerL M, innerL N), Chat_inner_pair M N⟩ =
        ((ψ₁.symm M : ↥K₁) : G) * ((ψ₂.symm N : ↥K₂) : G)) ∧
      π ⟨tauHat, tauHat_mem⟩ = S.t := by
  have htt : S.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one S.t
    rwa [S.t_ord] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [S.z_ord] at this
    simpa [pow_two] using this
  have hnorm₁ : ∀ k ∈ K₁, S.t * k * S.t⁻¹ ∈ K₁ := fun k hk => S.normal₁ S.t S.t_mem k hk
  have hnorm₂ : ∀ k ∈ K₂, S.t * k * S.t⁻¹ ∈ K₂ := fun k hk => S.normal₂ S.t S.t_mem k hk
  have hτ1 : hom2 S.t htt (Multiplicative.ofAdd 1) = S.t := hom2_ofAdd_one S.t htt
  have h₁ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), invHom ψ₁ (sigmaHom ε M) =
      hom2 S.t htt ε * invHom ψ₁ M * (hom2 S.t htt ε)⁻¹ :=
    fun ε M => symm_sigmaHom_eq htt hnorm₁ ψ₁ ht₁ ε M
  have h₂ : ∀ (ε : Multiplicative (ZMod 2)) (M : SL2), invHom ψ₂ (sigmaHom ε M) =
      hom2 S.t htt ε * invHom ψ₂ M * (hom2 S.t htt ε)⁻¹ :=
    fun ε M => symm_sigmaHom_eq htt hnorm₂ ψ₂ ht₂ ε M
  have hcomm : ∀ M N : SL2, invHom ψ₁ M * invHom ψ₂ N = invHom ψ₂ N * invHom ψ₁ M :=
    fun M N => S.comm _ (ψ₁.symm M).2 _ (ψ₂.symm N).2
  have hmem₁ : ∀ M : SL2, invHom ψ₁ M ∈ K₁ := fun M => (ψ₁.symm M).2
  have hmem₂ : ∀ M : SL2, invHom ψ₂ M ∈ K₂ := fun M => (ψ₂.symm M).2
  have hnot : ∀ x ∈ K₁ ⊔ K₂, x * S.t ≠ 1 := by
    intro x hx hxt
    apply S.t_notin
    rw [eq_inv_of_mul_eq_one_right hxt]
    exact inv_mem hx
  have hτC : ∀ ε : Multiplicative (ZMod 2),
      hom2 S.t htt ε ∈ Subgroup.centralizer ({z} : Set G) := by
    intro ε
    rcases eq_one_or_eq_ofAdd_one ε with rfl | rfl
    · rw [map_one]; exact one_mem _
    · rw [hτ1]; exact S.t_mem
  have hkz₁ : invHom ψ₁ minusOne = z := by
    have h := hz₁ ⟨z, S.z_mem₁⟩ rfl
    show ((ψ₁.symm minusOne : K₁) : G) = z
    rw [← h, MulEquiv.symm_apply_apply]
  have hkz₂ : invHom ψ₂ minusOne = z := by
    have h := hz₂ ⟨z, S.z_mem₂⟩ rfl
    show ((ψ₂.symm minusOne : K₂) : G) = z
    rw [← h, MulEquiv.symm_apply_apply]
  have hker : ∀ M N : SL2, invHom ψ₁ M * invHom ψ₂ N = 1 →
      (M = 1 ∧ N = 1) ∨ (M = minusOne ∧ N = minusOne) := by
    intro M N hMN
    have hk₂ : invHom ψ₁ M ∈ K₂ := by
      rw [eq_inv_of_mul_eq_one_left hMN]
      exact inv_mem (hmem₂ N)
    have hcent : ∀ w ∈ K₁, invHom ψ₁ M * w = w * invHom ψ₁ M :=
      fun w hw => (S.comm w hw _ hk₂).symm
    rcases S.K₁_center _ (hmem₁ M) hcent with h | h
    · left
      have h1 : ψ₁.symm M = 1 := Subtype.ext h
      refine ⟨?_, ?_⟩
      · simpa using congrArg ψ₁ h1
      · rw [h, one_mul] at hMN
        have h2 : ψ₂.symm N = 1 := Subtype.ext hMN
        simpa using congrArg ψ₂ h2
    · right
      refine ⟨?_, ?_⟩
      · simpa using hz₁ (ψ₁.symm M) h
      · have hN : invHom ψ₂ N = z := by
          rw [eq_inv_of_mul_eq_one_right hMN, h]
          exact inv_eq_of_mul_eq_one_right hzz
        simpa using hz₂ (ψ₂.symm N) hN
  refine ⟨iotaHom (invHom ψ₁) (hom2 S.t htt) h₁, iotaHom (invHom ψ₂) (hom2 S.t htt) h₂,
    piHom (invHom ψ₁) (invHom ψ₂) (hom2 S.t htt) hcomm h₁ h₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · refine iotaHom_injective _ _ h₁ (invHom_injective ψ₁) fun M => ?_
    rw [hτ1]
    exact hnot _ (Subgroup.mem_sup_left (hmem₁ M))
  · refine iotaHom_injective _ _ h₂ (invHom_injective ψ₂) fun M => ?_
    rw [hτ1]
    exact hnot _ (Subgroup.mem_sup_right (hmem₂ M))
  · exact fun M => iotaHom_innerL _ _ h₁ M
  · exact fun M => iotaHom_innerL _ _ h₂ M
  · rw [iotaHom_tauL, hτ1]
  · rw [iotaHom_tauL, hτ1]
  · intro c
    rw [piHom_apply]
    exact mul_mem (mul_mem (S.le_centralizer₁ (hmem₁ _)) (S.le_centralizer₂ (hmem₂ _)))
      (hτC _)
  · intro g hg
    rcases S.mem_C_cases_prod g hg with ⟨k₁, hk₁, k₂, hk₂, rfl⟩ | ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    · refine ⟨⟨(innerL (ψ₁ ⟨k₁, hk₁⟩), innerL (ψ₂ ⟨k₂, hk₂⟩)), Chat_inner_pair _ _⟩, ?_⟩
      rw [piHom_inner]
      simp [invHom_apply]
    · refine ⟨⟨(innerL (ψ₁ ⟨k₁, hk₁⟩), innerL (ψ₂ ⟨k₂, hk₂⟩)), Chat_inner_pair _ _⟩ *
        ⟨tauHat, tauHat_mem⟩, ?_⟩
      rw [map_mul, piHom_inner, piHom_tauHat, hτ1]
      simp [invHom_apply]
  · intro c
    refine piHom_eq_one_iff _ _ _ hcomm h₁ h₂ (fun M N => ?_) hker ?_ c
    · rw [hτ1]
      exact hnot _ (Subgroup.mul_mem_sup (hmem₁ M) (hmem₂ N))
    · rw [hkz₁, hkz₂]
      exact hzz
  · intro M N
    rw [piHom_inner]
    rfl
  · rw [piHom_tauHat, hτ1]

end CFSG.GH74.GLS.Stage4.Q9

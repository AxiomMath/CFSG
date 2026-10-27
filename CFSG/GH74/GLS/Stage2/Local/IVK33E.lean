module

public import CFSG.GH74.GLS.Stage2.Local.IVK33B
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.Uniqueness.SU.SU13.TA Equiv Equiv.Perm

section Config

def cfgBeta : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def cfgOmega : Perm (Fin 8) := swap 1 2 * swap 2 3 * (swap 5 6 * swap 6 7)

theorem cfgBeta_cycleType : cfgBeta.cycleType = {2, 2, 2, 2} := by
  have h2 : cfgBeta ^ 2 = 1 := by decide
  have hsupp : cfgBeta.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    revert x
    decide
  have hk := Perm.cycleType_of_pow_prime_eq_one h2
  have hsum := Perm.sum_cycleType cfgBeta
  have hcard : cfgBeta.cycleType.card = 4 := by
    have h1 : cfgBeta.cycleType.sum = 8 := by
      rw [hsum, hsupp, Finset.card_univ, Fintype.card_fin]
    rw [hk, Multiset.sum_replicate, smul_eq_mul] at h1
    omega
  rw [hk, hcard]
  rfl

def castSubEquiv {n : ℕ} (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun i := ⟨Fin.castLE hn i, by simp⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := by ext; simp
  right_inv x := by ext; simp

theorem exists_cycle_config {n : ℕ} (hn : 8 ≤ n) :
    ∃ β ω : alternatingGroup (Fin n), (β : Perm (Fin n)).cycleType = {2, 2, 2, 2} ∧
      ω * β * ω⁻¹ ≠ β ∧ ω * (ω * β * ω⁻¹) * ω⁻¹ = β * (ω * β * ω⁻¹) := by
  let ι : Perm (Fin 8) →* Perm (Fin n) := Equiv.Perm.extendDomainHom (castSubEquiv hn)
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective _
  have hsign : ∀ σ : Perm (Fin 8), Perm.sign σ = 1 → ι σ ∈ alternatingGroup (Fin n) := by
    intro σ h
    rw [Perm.mem_alternatingGroup]
    show Perm.sign (σ.extendDomain (castSubEquiv hn)) = 1
    rw [Perm.sign_extendDomain, h]
  have hβs : Perm.sign cfgBeta = 1 := by decide
  have hωs : Perm.sign cfgOmega = 1 := by decide
  refine ⟨⟨ι cfgBeta, hsign _ hβs⟩, ⟨ι cfgOmega, hsign _ hωs⟩, ?_, ?_, ?_⟩
  · show (cfgBeta.extendDomain (castSubEquiv hn)).cycleType = {2, 2, 2, 2}
    rw [Perm.cycleType_extendDomain]
    exact cfgBeta_cycleType
  · intro h
    have h1 : ι (cfgOmega * cfgBeta * cfgOmega⁻¹) = ι cfgBeta := by
      simpa [map_mul, map_inv] using congrArg Subtype.val h
    have h2 : cfgOmega * cfgBeta * cfgOmega⁻¹ = cfgBeta := hι h1
    exact absurd h2 (by decide)
  · apply Subtype.ext
    have h8 : cfgOmega * (cfgOmega * cfgBeta * cfgOmega⁻¹) * cfgOmega⁻¹ =
        cfgBeta * (cfgOmega * cfgBeta * cfgOmega⁻¹) := by decide
    have := congrArg ι h8
    simpa [map_mul, map_inv] using this

end Config

section Lift

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem exists_cycle_of_twoCover (hπ : TwoCover π) (hn : 8 ≤ n) :
    ∃ v₁ v₂ w : H, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
      w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ := by
  obtain ⟨β, ω, hβ, hne, hc⟩ := exists_cycle_config hn
  obtain ⟨b, hb⟩ := hπ.surj β
  obtain ⟨w, hw⟩ := hπ.surj ω
  have hconj : ∀ (g x : alternatingGroup (Fin n)), (x : Perm (Fin n)).cycleType = {2, 2, 2, 2} →
      ((g * x * g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} := by
    intro g x hx
    have : ((g * x * g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        (g : Perm (Fin n)) * (x : Perm (Fin n)) * (g : Perm (Fin n))⁻¹ := rfl
    rw [this, Perm.cycleType_conj, hx]
  have hsq : ∀ x : H, (π x : Perm (Fin n)).cycleType = {2, 2, 2, 2} → x * x = 1 := fun x hx => by
    rw [← sq]
    exact hπ.sq_eq_one_of_cycleType_two_two_two_two hn hx
  have hne1 : ∀ x : alternatingGroup (Fin n), (x : Perm (Fin n)).cycleType = {2, 2, 2, 2} →
      x ≠ 1 := by
    intro x hx h
    rw [h, OneMemClass.coe_one, Perm.cycleType_one] at hx
    simp at hx
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : H, b₂ = w * b * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨b₃, hb₃⟩ : ∃ b₃ : H, b₃ = w * b₂ * w⁻¹ := ⟨_, rfl⟩
  have hπb₂ : π b₂ = ω * β * ω⁻¹ := by rw [hb₂, map_mul, map_mul, map_inv, hb, hw]
  have hπb₃ : π b₃ = ω * (ω * β * ω⁻¹) * ω⁻¹ := by rw [hb₃, map_mul, map_mul, map_inv, hπb₂, hw]
  have hβ₂ : ((ω * β * ω⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} :=
    hconj ω β hβ
  have hβ₃ : ((ω * (ω * β * ω⁻¹) * ω⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType =
      {2, 2, 2, 2} := hconj ω _ hβ₂
  have hb1 : b * b = 1 := hsq b (by rw [hb]; exact hβ)
  have hb2 : b₂ * b₂ = 1 := hsq b₂ (by rw [hπb₂]; exact hβ₂)
  have hπbb₂ : π (b * b₂) = ω * (ω * β * ω⁻¹) * ω⁻¹ := by rw [map_mul, hb, hπb₂, ← hc]
  have hbb₂ : (b * b₂) * (b * b₂) = 1 := hsq _ (by rw [hπbb₂]; exact hβ₃)
  have hcomm : b * b₂ = b₂ * b := by
    have h1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb1
    have h2 : b₂⁻¹ = b₂ := inv_eq_of_mul_eq_one_right hb2
    have h3 : (b * b₂)⁻¹ = b * b₂ := inv_eq_of_mul_eq_one_right hbb₂
    rw [mul_inv_rev, h1, h2] at h3
    exact h3.symm
  obtain ⟨k, hkdef⟩ : ∃ k : H, k = (b * b₂)⁻¹ * b₃ := ⟨_, rfl⟩
  have hk : k ∈ π.ker := by
    rw [hkdef, MonoidHom.mem_ker, map_mul, map_inv, hπbb₂, hπb₃, inv_mul_cancel]
  have hkc : ∀ g : H, g * k = k * g := fun g => Subgroup.mem_center_iff.1 (hπ.ker_le_center hk) g
  have hkk : k * k = 1 := by
    rw [← sq]
    exact hπ.sq_eq_one_of_mem_ker' hk
  have hb₃eq : b₃ = b * b₂ * k := by
    rw [hkdef]
    group
  have hkπ : π k = 1 := MonoidHom.mem_ker.1 hk
  have hxy : ∀ x y : H, x * k * (y * k) = x * y := by
    intro x y
    calc x * k * (y * k) = x * (k * y) * k := by group
      _ = x * (y * k) * k := by rw [← hkc y]
      _ = x * y * (k * k) := by group
      _ = x * y := by rw [hkk, mul_one]
  have hwk : w * k * w⁻¹ = k := by rw [hkc w, mul_inv_cancel_right]
  refine ⟨b * k, b₂ * k, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxy, hb1]
  · rw [hxy, hb2]
  · rw [hxy, hxy, hcomm]
  · intro h
    apply hne1 β hβ
    have := congrArg π h
    rwa [map_mul, hb, hkπ, mul_one, map_one] at this
  · intro h
    apply hne1 _ hβ₂
    have := congrArg π h
    rwa [map_mul, hπb₂, hkπ, mul_one, map_one] at this
  · intro h
    apply hne
    have := congrArg π h
    rw [map_mul, map_mul, hb, hπb₂, hkπ, mul_one, mul_one] at this
    exact this.symm
  · calc w * (b * k) * w⁻¹ = (w * b * w⁻¹) * (w * k * w⁻¹) := by group
      _ = b₂ * k := by rw [hwk, ← hb₂]
  · calc w * (b₂ * k) * w⁻¹ = (w * b₂ * w⁻¹) * (w * k * w⁻¹) := by group
      _ = b₃ * k := by rw [hwk, ← hb₃]
      _ = b * b₂ * k * k := by rw [hb₃eq]
      _ = b * b₂ := by rw [mul_assoc _ k k, hkk, mul_one]
      _ = b * k * (b₂ * k) := (hxy b b₂).symm

end Lift

section Sporadic

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem prop21h_of_sporadic {n : ℕ} (hn : 8 ≤ n) (h : Stage1Sporadic G z S n) : Prop21h z := by
  have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt (CentralizerBar z) n :=
    ⟨h.cover.1, inferInstance, h.cover.2.1, h.cover.2.2⟩
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hT
  obtain ⟨v₁, v₂, w, hv₁, hv₂, hc, h₁, h₂, h₁₂, hw₁, hw₂⟩ := exists_cycle_of_twoCover hπ hn
  have hL : ∀ x : CentralizerBar z, x ∈ LBar z := fun x => by rw [h.eq_L]; exact Subgroup.mem_top x
  exact prop21h_of_cycle hv₁ hv₂ hc h₁ h₂ h₁₂ hw₁ hw₂ (hL v₁) (hL v₂)

end Sporadic

end CFSG.GH74.GLS.Stage2.Local

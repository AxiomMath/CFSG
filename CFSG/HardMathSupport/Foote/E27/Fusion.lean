module

public import CFSG.HardMathSupport.Foote.E27.SporSylow

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

theorem card_centralizer_conj' {G : Type*} [Group G] (k x : G) :
    Nat.card ↥(centralizer ({k * x * k⁻¹} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  rw [← conj_map_centralizer k x]
  exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj k))

theorem card_centralizer_aut {G : Type*} [Group G] (φ : G ≃* G) (x : G) :
    Nat.card ↥(centralizer ({φ x} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  have h : (centralizer ({x} : Set G)).map φ.toMonoidHom = centralizer ({φ x} : Set G) := by
    ext y
    rw [mem_map, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff] at hw
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hw]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← h]
  exact Subgroup.card_map_of_injective φ.injective

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.not_dvd81_centralizer_K (h : E27Config X K R T z) (hz : z ∈ K) :
    ¬ 81 ∣ Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) := by
  have hCcard : Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) =
      Nat.card ↥(centralizer ({z} : Set X) ⊓ K) := by
    rw [← centralizer_map_val_eq K z hz, Subgroup.card_map_of_injective K.subtype_injective]
  have hfac := h.factorization_card_centralizer_inf_of_mem hz
  rw [hCcard]
  intro hdiv
  have hn : Nat.card ↥(centralizer ({z} : Set X) ⊓ K) ≠ 0 := by
    intro h0
    rw [h0] at hfac
    simp at hfac
  have h81 : 3 ^ 4 ∣ Nat.card ↥(centralizer ({z} : Set X) ⊓ K) := by
    norm_num
    exact hdiv
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).mp h81
  omega

theorem E27Config.not_dvd81_of_mem_diff (h : E27Config X K R T z) (hz : z ∈ K) {r : X}
    (hrR : r ∈ R) (hrT : r ∉ T) (hrK : r ∈ K) :
    ¬ 81 ∣ Nat.card ↥(centralizer ({(⟨r, hrK⟩ : ↥K)} : Set ↥K)) := by
  obtain ⟨n, hn, hnr⟩ := h.fus r hrR hrT
  have : K.Normal := h.normal
  set φ : ↥K ≃* ↥K := MulAut.conjNormal n with hφ
  have hrne : r ≠ 1 := fun e => hrT (e ▸ one_mem T)
  have hnrK : n * r * n⁻¹ ∈ K := h.normal.conj_mem r hrK n
  have hφr : φ ⟨r, hrK⟩ = ⟨n * r * n⁻¹, hnrK⟩ := rfl
  rw [← card_centralizer_aut φ, hφr]
  have hzne : z ≠ 1 := fun e => h.z_not_mem (e ▸ one_mem T)
  have hz3 : z ^ 3 = 1 := h.elem.2 z h.z_mem
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hnr
  have hne1 : n * r * n⁻¹ ≠ 1 := by
    intro e
    apply hrne
    have : r = n⁻¹ * (n * r * n⁻¹) * n := by group
    rw [this, e]; group
  have hcases : n * r * n⁻¹ = z ∨ n * r * n⁻¹ = z⁻¹ := by
    rw [← hi] at hne1 ⊢
    have h3 : (z ^ i) = z ^ (i % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
      have : (z ^ (3 : ℤ)) = 1 := by exact_mod_cast hz3
      rw [this, one_zpow, mul_one]
    rw [h3] at hne1 ⊢
    have hlt : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hlt with h0 | h1 | h2
    · rw [h0] at hne1; simp at hne1
    · left; rw [h1]; simp
    · right
      rw [h2]
      have : z ^ (2 : ℤ) * z = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
        exact_mod_cast hz3
      exact eq_inv_of_mul_eq_one_left this
  have hzK : (⟨z, hz⟩ : ↥K) ^ 3 = 1 := Subtype.ext hz3
  have hc : Nat.card ↥(centralizer ({(⟨n * r * n⁻¹, hnrK⟩ : ↥K)} : Set ↥K)) =
      Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) := by
    rcases hcases with e | e
    · have : (⟨n * r * n⁻¹, hnrK⟩ : ↥K) = ⟨z, hz⟩ := Subtype.ext e
      rw [this]
    · have : (⟨n * r * n⁻¹, hnrK⟩ : ↥K) = (⟨z, hz⟩ : ↥K)⁻¹ := Subtype.ext e
      rw [this]
      congr 2
      ext y
      simp only [mem_centralizer_singleton_iff]
      exact Commute.inv_right_iff (a := y) (b := (⟨z, hz⟩ : ↥K))
  rw [hc]
  exact h.not_dvd81_centralizer_K hz


@[expose] def FusGood {G : Type*} [Group G] (S₀ : Subgroup G) (s : G) : Prop :=
  ∃ σ : G ≃* G, σ s ∈ S₀ ∧ 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({σ s} : Set G))

theorem FusGood.dvd {G : Type*} [Group G] {S₀ : Subgroup G} {s : G} (hs : FusGood S₀ s) :
    81 ∣ Nat.card ↥(centralizer ({s} : Set G)) := by
  obtain ⟨σ, -, hdvd⟩ := hs
  rw [← card_centralizer_aut σ s]
  exact hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)

theorem E27Config.false_of_fusion_kill (h : E27Config X K R T z) (hz : z ∈ K) (S₀ : Sylow 3 ↥K)
    (hkill : ∀ s : ↥K, s ∈ (S₀ : Subgroup ↥K) → orderOf s = 3 → FusGood (S₀ : Subgroup ↥K) s) :
    False := by
  obtain ⟨z₀, hz₀S₀, hord, -, -, h81⟩ := h.exists_conj_mem_sylow hz S₀
  exact h81 (hkill z₀ hz₀S₀ hord).dvd

theorem E27Config.exists_E27_in_sylow (h : E27Config X K R T z) (hz : z ∈ K) (S₀ : Sylow 3 ↥K) :
    ∃ R' T' : Subgroup ↥K, R' ≤ (S₀ : Subgroup ↥K) ∧ (∀ x ∈ R', x ^ 3 = 1) ∧
      (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) ∧ Nat.card ↥R' = 27 ∧ T' ≤ R' ∧ Nat.card ↥T' = 9 ∧
      ∀ r ∈ R', r ∉ T' → ¬ 81 ∣ Nat.card ↥(centralizer ({r} : Set ↥K)) := by
  have hRK : R ≤ K := h.le_of_mem hz
  set R₁ : Subgroup ↥K := R.subgroupOf K with hR₁
  set T₁ : Subgroup ↥K := T.subgroupOf K with hT₁
  have hR₁card : Nat.card ↥R₁ = 27 := by
    rw [← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hT₁card : Nat.card ↥T₁ = 9 := by
    rw [← h.card_T]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.T_le_K).toEquiv
  have hR₁p : IsPGroup 3 ↥R₁ := IsPGroup.of_card (n := 3) (by rw [hR₁card]; norm_num)
  obtain ⟨S₁, hS₁⟩ := hR₁p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K S₁ S₀
  have hconj : ∀ x ∈ (S₁ : Subgroup ↥K), MulAut.conj g x ∈ (S₀ : Subgroup ↥K) := by
    intro x hx
    rw [← hg]
    show MulAut.conj g x ∈ ((g • S₁ : Sylow 3 ↥K) : Set ↥K)
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set hx
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := MulEquiv.injective (MulAut.conj g)
  refine ⟨R₁.map (MulAut.conj g).toMonoidHom, T₁.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_,
    Subgroup.map_mono ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hconj y (hS₁ hy)
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : X) ∈ R := Subgroup.mem_subgroupOf.mp hy
    have h3 : y ^ 3 = 1 := Subtype.ext (h.elem.2 _ hy')
    show (g * y * g⁻¹) ^ 3 = 1
    rw [conj_pow, h3]; group
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    have hy' : (y : X) ∈ R := Subgroup.mem_subgroupOf.mp hy
    have hw' : (w : X) ∈ R := Subgroup.mem_subgroupOf.mp hw
    have hcomm : y * w = w * y := by
      have e := h.elem.1.is_comm.comm (⟨y, hy'⟩ : R) ⟨w, hw'⟩
      have e' := congrArg (Subtype.val : ↥R → X) e
      exact Subtype.ext e'
    show g * y * g⁻¹ * (g * w * g⁻¹) = g * w * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hcomm]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  · rw [Subgroup.card_map_of_injective hinj, hR₁card]
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (h.T_le_R (Subgroup.mem_subgroupOf.mp hx))
  · rw [Subgroup.card_map_of_injective hinj, hT₁card]
  · rintro _ ⟨y, hy, rfl⟩ hnT
    have hyR : (y : X) ∈ R := Subgroup.mem_subgroupOf.mp hy
    have hyT : (y : X) ∉ T := fun hT => hnT ⟨y, Subgroup.mem_subgroupOf.mpr hT, rfl⟩
    have := h.not_dvd81_of_mem_diff hz hyR hyT y.2
    have e : (MulAut.conj g) y = g * y * g⁻¹ := rfl
    show ¬ 81 ∣ Nat.card ↥(centralizer ({g * y * g⁻¹} : Set ↥K))
    rw [card_centralizer_conj' g y]
    exact this

theorem E27Config.false_of_fusion_gen (h : E27Config X K R T z) (hz : z ∈ K) (S₀ : Sylow 3 ↥K)
    (hgen : ∀ R' T' : Subgroup ↥K, R' ≤ (S₀ : Subgroup ↥K) → (∀ x ∈ R', x ^ 3 = 1) →
      (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) → Nat.card ↥R' = 27 → T' ≤ R' → Nat.card ↥T' = 9 →
      ∃ r ∈ R', r ∉ T' ∧ 81 ∣ Nat.card ↥(centralizer ({r} : Set ↥K))) : False := by
  obtain ⟨R', T', h1, h2, h3, h4, h5, h6, h7⟩ := h.exists_E27_in_sylow hz S₀
  obtain ⟨r, hr, hrT, hdvd⟩ := hgen R' T' h1 h2 h3 h4 h5 h6
  exact h7 r hr hrT hdvd

end CFSG.HardMathSupport.Foote.E27

end

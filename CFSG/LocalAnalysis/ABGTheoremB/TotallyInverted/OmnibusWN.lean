module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusInputs
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusSetting

public section

namespace CFSG.ABGTheoremB.TotallyInverted.OmnibusW

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion Omnibus
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem isLayerComplement_J (hh : σ.height ≠ 1) (Δ : Data σ r) : σ.IsLayerComplement Δ.J :=
  ⟨Δ.J_le, Δ.L₀_eq, Δ.J_inf.resolve_right fun h => hh h.2.1, Δ.J_normal, Δ.J_centralizes⟩

theorem mem_Ps_zero_of_mem_ON (Δ : Data σ r) {o : G} (ho : o ∈ σ.ON) {k : ℕ}
    (hk : o ^ r ^ k = 1) : o ∈ σ.Ps r 0 := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hp : IsPGroup r (Subgroup.zpowers o) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨g, hg, hle⟩ := exists_le_conjSub_of_isSylowOf Δ.P_sylow
    ((Subgroup.zpowers_le).mpr ho) hp
  have hgP : conjSub g (σ.Ps r 0) = σ.Ps r 0 :=
    conjSub_eq_self (le_normalizer_pCoreIn r σ.N (σ.ON_le_N hg))
  rw [← hgP]
  exact hle (Subgroup.mem_zpowers o)

theorem conjSub_a_pow_zero (Δ : Data σ r) {X : Fin 3 → Subgroup G}
    (hX : ∀ j, conjSub Δ.a (X j) = X (j + 1)) (i : Fin 3) :
    conjSub (Δ.a ^ (i : ℕ)) (X 0) = X i := by
  fin_cases i
  · simp
  · simpa using hX 0
  · have h1 := hX 0
    have h2 := hX 1
    simp only [Fin.zero_add, Fin.reduceAdd] at h1 h2
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [pow_two, conjSub_mul, h1, h2]

theorem nStructure_zero (hσ : σ.IsValid) (hh : σ.height ≠ 1) (hT : σ.TIFacts) (Δ : Data σ r)
    {Z : Subgroup G} (hZN : Z ≤ σ.N) (hZ : Odd (Nat.card Z))
    (hCZ : σ.C ≤ Subgroup.normalizer (Z : Set G)) :
    ∃ P : Subgroup G, σ.C ≤ Subgroup.normalizer (P : Set G) ∧
      (Z : Set G) ⊆ (σ.C : Set G) * (P : Set G) ∧
      ∃ Y ∈ ({σ.Ps r 0, R Δ 0, Rs Δ 0} : Set (Subgroup G)),
        ∀ g ∈ P, (∃ k : ℕ, g ^ r ^ k = 1) → g ∈ Y := by
  have hJ := isLayerComplement_J hh Δ
  obtain ⟨p', X, hp', hX, hZle⟩ :=
    hT.permutable_le Δ.J hJ Z hZN hZ (mul_comm_of_le_normalizer hCZ).symm
  obtain ⟨hXJ, hXp, hCX, hXC⟩ := hX
  have hXN : X ≤ σ.N := hXJ.trans (hJ.le.trans hσ.L₀_le_N)
  have hCON : σ.C ≤ Subgroup.normalizer (σ.ON : Set G) := σ.C_le_N.trans σ.N_le_normalizer_ON
  have hCP : σ.C ≤ Subgroup.normalizer ((X ⊔ σ.ON : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_sup (hCX hc) (hCON hc)
  have key : ∀ g ∈ X ⊔ σ.ON, ∀ k : ℕ, g ^ r ^ k = 1 →
      ∃ x ∈ X, ∃ o ∈ σ.Ps r 0, x ^ r ^ k = 1 ∧ x * o = g := by
    intro g hg k hk
    have hg' : g ∈ ((X ⊔ σ.ON : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hXN.trans σ.N_le_normalizer_ON)] at hg'
    obtain ⟨x, hx, o, ho, rfl⟩ := hg'
    have hcomm : Commute x o :=
      ((Subgroup.mem_centralizer_iff.mp (Δ.J_centralizes (hXJ hx))) o ho).symm
    have h1 : x ^ r ^ k * o ^ r ^ k = 1 := by rw [← hcomm.mul_pow]; exact hk
    have h2 : x ^ r ^ k = (o ^ r ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : x ^ r ^ k ∈ Δ.J ⊓ σ.ON := by
      refine ⟨Δ.J.pow_mem (hXJ hx) _, ?_⟩
      rw [h2]
      exact σ.ON.inv_mem (σ.ON.pow_mem ho _)
    rw [hJ.inf_eq, Subgroup.mem_bot] at h3
    have h4 : o ^ r ^ k = 1 := by rwa [h3, one_mul] at h1
    exact ⟨x, hx, o, mem_Ps_zero_of_mem_ON Δ ho h4, h3, rfl⟩
  refine ⟨X ⊔ σ.ON, hCP, fun z hz => ?_, ?_⟩
  · have hz' : z ∈ ((σ.C ⊔ (X ⊔ σ.ON) : Subgroup G) : Set G) := by
      rw [← sup_assoc]
      exact hZle hz
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCP] at hz'
  by_cases hXr : p' = r ∧ X ≠ ⊥
  · obtain ⟨hpr, hX1⟩ := hXr
    rw [hpr] at hXp
    obtain ⟨hδε, hrp⟩ :=
      hT.layer_signalizer Δ.J hJ r Δ.prime Δ.ne_two X ⟨hXJ, hXp, hCX, hXC⟩ hX1
    have hrq : r ∣ σ.q := by
      rw [Setting.q, hrp]
      exact dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hσ.one_le_f)
    obtain ⟨-, -, -, -, -, hcov, -⟩ := Δ.Q_cases ⟨hδε, hrq⟩ 0
    have hXJ0 : X ≤ conjSub (Δ.a ^ ((0 : Fin 3) : ℕ)) Δ.J := by simpa using hXJ
    rcases hcov X hXJ0 hXp hCX with hXQ | hXQ
    · refine ⟨R Δ 0, Or.inr (Or.inl rfl), fun g hg ⟨k, hk⟩ => ?_⟩
      obtain ⟨x, hx, o, ho, -, rfl⟩ := key g hg k hk
      exact Subgroup.mul_mem_sup (hXQ hx) ho
    · refine ⟨Rs Δ 0, Or.inr (Or.inr rfl), fun g hg ⟨k, hk⟩ => ?_⟩
      obtain ⟨x, hx, o, ho, -, rfl⟩ := key g hg k hk
      exact Subgroup.mul_mem_sup (hXQ hx) ho
  · refine ⟨σ.Ps r 0, Or.inl rfl, fun g hg ⟨k, hk⟩ => ?_⟩
    obtain ⟨x, hx, o, ho, hxk, rfl⟩ := key g hg k hk
    have hx1 : x = 1 := by
      by_cases hpr : p' = r
      · have hX1 : X = ⊥ := by
          by_contra h
          exact hXr ⟨hpr, h⟩
        rw [hX1] at hx
        exact Subgroup.mem_bot.mp hx
      · obtain ⟨m, hm⟩ := hXp ⟨x, hx⟩
        have hxm : x ^ p' ^ m = 1 := by simpa using congrArg Subtype.val hm
        have hcop : Nat.Coprime (p' ^ m) (r ^ k) :=
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' Δ.prime).mpr hpr)
        rw [← orderOf_eq_one_iff]
        exact Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxm) hcop)
          (orderOf_dvd_of_pow_eq_one hxk)
    rw [hx1, one_mul]
    exact ho

theorem nStructure (hσ : σ.IsValid) (hh : σ.height ≠ 1) (hT : σ.TIFacts) (Δ : Data σ r) :
    ABG_II_4_11_Input Δ := by
  intro i Z hZN hZ hCZ
  set g : G := Δ.a ^ (i : ℕ) with hgdef
  have hgM : g ∈ σ.M := a_pow_mem_M Δ _
  have hgC : conjSub g σ.C = σ.C := conjSub_a_pow_C Δ _
  have hgN : conjSub g⁻¹ (σ.Ns i) = σ.N := by
    rw [hgdef, ← conjSub_a_pow_N Δ i, conjSub_inv_conjSub]
  have hZ'N : conjSub g⁻¹ Z ≤ σ.N := hgN ▸ conjSub_mono hZN
  have hZ'odd : Odd (Nat.card (conjSub g⁻¹ Z)) := by rw [card_conjSub]; exact hZ
  have hCZ' : σ.C ≤ Subgroup.normalizer ((conjSub g⁻¹ Z : Subgroup G) : Set G) :=
    le_normalizer_conjSub hCZ (σ.M.inv_mem hgM)
  obtain ⟨P, hCP, hZP, Y, hY, hPY⟩ := nStructure_zero hσ hh hT Δ hZ'N hZ'odd hCZ'
  have hconj : ∀ {X : Fin 3 → Subgroup G}, (∀ j, conjSub Δ.a (X j) = X (j + 1)) →
      conjSub g (X 0) = X i := fun hX => conjSub_a_pow_zero Δ hX i
  have hR : ∀ j, conjSub Δ.a (R Δ j) = R Δ (j + 1) := fun j => by
    rw [R, R, conjSub_sup, (Δ.Q_conj j).1, Δ.P_conj j]
  have hRs : ∀ j, conjSub Δ.a (Rs Δ j) = Rs Δ (j + 1) := fun j => by
    rw [Rs, Rs, conjSub_sup, (Δ.Q_conj j).2, Δ.P_conj j]
  refine ⟨conjSub g P, le_normalizer_conjSub hCP hgM, fun z hz => ?_, conjSub g Y, ?_,
    fun x hx hxr => ?_⟩
  · have hz' : g⁻¹ * z * g ∈ ((conjSub g⁻¹ Z : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, mem_conjSub, show g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z by group]
      exact hz
    obtain ⟨c, hc, p, hp, he⟩ := hZP hz'
    refine ⟨g * c * g⁻¹, ?_, g * p * g⁻¹, conj_mem_conjSub hp, ?_⟩
    · rw [SetLike.mem_coe, ← hgC]
      exact conj_mem_conjSub hc
    · have he' : c * p = g⁻¹ * z * g := he
      change g * c * g⁻¹ * (g * p * g⁻¹) = z
      rw [show g * c * g⁻¹ * (g * p * g⁻¹) = g * (c * p) * g⁻¹ by group, he']
      group
  · rcases hY with h | h | h
    · rw [h, hconj Δ.P_conj]
      exact Or.inl rfl
    · rw [h, hconj hR]
      exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at h
      rw [h, hconj hRs]
      exact Or.inr (Or.inr rfl)
  · obtain ⟨k, hk⟩ := hxr
    rw [mem_conjSub] at hx ⊢
    refine hPY _ hx ⟨k, ?_⟩
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_pow, hk]
    group

end CFSG.ABGTheoremB.TotallyInverted.OmnibusW

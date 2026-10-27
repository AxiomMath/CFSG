module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem inner_of_pow_two_pow_eq_one {n : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n)
    (hF : Even (Nat.card F)) (A : GL (Fin n) F) (m : ℕ) (h : conjAut n F A ^ 2 ^ m = 1) :
    conjAut n F A ∈ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
  have h1 : conjAut n F (A ^ 2 ^ m) = 1 := by
    rw [map_pow]
    exact h
  obtain ⟨-, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ 2 ^ m) 1
    (by rw [map_one, mul_one]; exact h1)
  have hdet2 : (GeneralLinearGroup.det A) ^ 2 ^ m = c ^ n := by
    rw [← map_pow, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hodd : Odd (Nat.card F - 1) := by
    obtain ⟨r, hr⟩ := hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime (Nat.card Fˣ) (2 ^ m) := by
    rw [Nat.card_units F]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  have hbij := Nat.Coprime.pow_left_bijective hcop
  obtain ⟨μ₀, hμ₀⟩ := hbij.2 c
  have hμ₀' : μ₀ ^ 2 ^ m = c := hμ₀
  have hdet : GeneralLinearGroup.det A = μ₀ ^ n := by
    apply hbij.1
    show (GeneralLinearGroup.det A) ^ 2 ^ m = (μ₀ ^ n) ^ 2 ^ m
    rw [hdet2, ← hμ₀']
    exact pow_right_comm _ _ _
  exact conjAut_mem_range_conj_of_det_eq_pow hdet

theorem kgl34_aut_comm {F : Type*} [Field F] {σ₀ : F ≃+* F} (hgen : Subgroup.zpowers σ₀ = ⊤)
    (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  have h1 : σ ∈ Subgroup.zpowers σ₀ := by rw [hgen]; exact Subgroup.mem_top σ
  have h2 : τ ∈ Subgroup.zpowers σ₀ := by rw [hgen]; exact Subgroup.mem_top τ
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h2
  exact ((Commute.refl σ₀).zpow_zpow m k).eq

theorem kgl34_comm_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {α β c d a b : G}
    (hα : α = c * a) (hβ : β = d * b) (hc : c ∈ N) (hd : d ∈ N) (hab : Commute a b) :
    α * β * α⁻¹ * β⁻¹ ∈ N := by
  have hc' : QuotientGroup.mk' N c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
  have hd' : QuotientGroup.mk' N d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
  have hcomm : QuotientGroup.mk' N a * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N a := (hab.map (QuotientGroup.mk' N)).eq
  subst hα hβ
  have key : QuotientGroup.mk' N ((c * a) * (d * b) * (c * a)⁻¹ * (d * b)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hc', hd', _root_.mul_inv_rev, one_mul, mul_one, inv_one]
    rw [hcomm]
    group
  exact (QuotientGroup.eq_one_iff _).mp key

theorem comm_mem_linearAutGroup {n f : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n)
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) (α β : MulAut (projectiveSL n F)) :
    α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup n F := by
  haveI : (linearAutGroup n F).Normal := linearAutGroup_normal_of_three_le hn
  obtain ⟨σ₀, -, -, hgen, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hF
  have hff : ∀ σ τ : F ≃+* F, Commute (fieldAut n F σ) (fieldAut n F τ) := by
    intro σ τ
    show fieldAut n F σ * fieldAut n F τ = fieldAut n F τ * fieldAut n F σ
    rw [← map_mul, ← map_mul, kgl34_aut_comm hgen σ τ]
  have hfd : ∀ τ : F ≃+* F, Commute (dualAut n F) (fieldAut n F τ) :=
    fun τ => dualAut_mul_fieldAut τ
  obtain ⟨A, σ, ε, -, hα⟩ := (automorphism_generation (K := F) hn).2 α
  obtain ⟨B, τ, η, -, hβ⟩ := (automorphism_generation (K := F) hn).2 β
  have hac : Commute (fieldAut n F σ * dualAut n F ^ ε) (fieldAut n F τ) :=
    Commute.mul_left (hff σ τ) ((hfd τ).pow_left ε)
  have had : Commute (fieldAut n F σ * dualAut n F ^ ε) (dualAut n F ^ η) :=
    Commute.mul_left ((hfd σ).symm.pow_right η) ((Commute.refl (dualAut n F)).pow_pow ε η)
  have hab : Commute (fieldAut n F σ * dualAut n F ^ ε) (fieldAut n F τ * dualAut n F ^ η) :=
    Commute.mul_right hac had
  exact kgl34_comm_mem (linearAutGroup n F) (hα.trans (mul_assoc _ _ _))
    (hβ.trans (mul_assoc _ _ _)) (conjAut_mem_linearAutGroup A) (conjAut_mem_linearAutGroup B) hab

theorem inf_linearAutGroup_eq_bot {n : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n)
    (hF : Even (Nat.card F)) {S : Subgroup (MulAut (projectiveSL n F))} (hS : IsPGroup 2 ↥S)
    (hSI : S ⊓ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range = ⊥) :
    S ⊓ linearAutGroup n F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxD⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hxD
  obtain ⟨m, hm⟩ := hS ⟨conjAut n F A, hxS⟩
  have hpow : conjAut n F A ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hinner := inner_of_pow_two_pow_eq_one hn hF A m hpow
  have hmem : conjAut n F A ∈ S ⊓ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range :=
    ⟨hxS, hinner⟩
  rw [hSI] at hmem
  exact hmem

theorem commute_of_mem_S {n f : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n)
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {S : Subgroup (MulAut (projectiveSL n F))}
    (hSD : S ⊓ linearAutGroup n F = ⊥) {s t : MulAut (projectiveSL n F)} (hs : s ∈ S)
    (ht : t ∈ S) : s * t = t * s := by
  have hD := comm_mem_linearAutGroup hn hF hf s t
  have hmem : s * t * s⁻¹ * t⁻¹ ∈ S ⊓ linearAutGroup n F :=
    ⟨S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht), hD⟩
  rw [hSD, Subgroup.mem_bot] at hmem
  calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
    _ = t * s := by rw [hmem, one_mul]

theorem commute_of_mem_normalizer {n f : ℕ} {F : Type*} [Field F] [Finite F] (hn : 3 ≤ n)
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {S : Subgroup (MulAut (projectiveSL n F))}
    (hSD : S ⊓ linearAutGroup n F = ⊥) {b s : MulAut (projectiveSL n F)}
    (hb : b ∈ Subgroup.normalizer (S : Set (MulAut (projectiveSL n F)))) (hs : s ∈ S) :
    b * s = s * b := by
  have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hb s).mp hs
  have hD := comm_mem_linearAutGroup hn hF hf b s
  have hmem : b * s * b⁻¹ * s⁻¹ ∈ S ⊓ linearAutGroup n F :=
    ⟨S.mul_mem hbs (S.inv_mem hs), by simpa [mul_assoc] using hD⟩
  rw [hSD, Subgroup.mem_bot] at hmem
  calc b * s = b * s * b⁻¹ * s⁻¹ * (s * b) := by group
    _ = s * b := by rw [hmem, one_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

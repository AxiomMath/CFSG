module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2L2Nine
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Y

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Field

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_no_hyp_field (hF : L2Field F) (e : K ≃* L2 F) (σ₀ : F ≃+* F)
    (hσ₀ : orderOf σ₀ = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut K)}
    (hP : KAHyp (fieldAutHom e σ₀) p P) : False := by
  have hq : Odd (Nat.card (fixedField σ₀)) := odd_card_fixedField σ₀ hF.1
  have hq1 : 1 < Nat.card (fixedField σ₀) := one_lt_card_fixedField σ₀
  by_cases h3 : Nat.card (fixedField σ₀) = 3
  · exact kaL2_no_hyp_nine hF e σ₀ hσ₀ h3 hp hp2 hP
  · have h5 : 5 ≤ Nat.card (fixedField σ₀) := by
      have := Nat.odd_iff.mp hq
      omega
    have hLq := kaFix_slMap_quasisimple σ₀ (by omega)
    exact ka_false_of_cover (conj_injective_of_L2 e) (kaL2Cover e) (kaL2Cover_surjective e)
      (kaL2Cover_central e) (kaSlMap σ₀) (kaL2Cover_field e σ₀) (kaFix (kaSlMap σ₀)) le_rfl
      (Subgroup.isPerfect_iff.mp hLq.1) (fun g hg => hg) hLq
      (fun p hp hp2 e'' hord _ hfix =>
        kaL2_field_rigid e σ₀ hσ₀ (kaL2_two_ne_zero hF.1) hp hp2 e'' hord hfix) p hp hp2 P hP

theorem kaL2_mem_innDiag_of_hyp (hF : L2Field F) (e : K ≃* L2 F) {α : MulAut K}
    (hα : α * α = 1) (hα1 : α ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut K)} (hP : KAHyp α p P) : α ∈ innDiagSub e := by
  by_contra hαD
  obtain ⟨σ₀, h, hσ₀, hαeq⟩ := kaL2_field_class e α hα hα1 hαD
  have hP' : KAHyp (fieldAutHom e σ₀) p (P.comap (MulAut.congr (h : K ≃* K)).toMonoidHom) :=
    kaHyp_of_congr (h : K ≃* K) (by rw [kaL2_congr_eq_mul, ← hαeq]; exact hP)
  exact kaL2_no_hyp_field hF e σ₀ hσ₀ hp hp2 hP'

end Field

section Dihedral

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_hyp_dvd (hF : L2Field F) (e : K ≃* L2 F) {α : MulAut K} (hα : α * α = 1)
    (hα1 : α ≠ 1) (hαD : α ∈ innDiagSub e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut K)} (hP : KAHyp α p P) : p ∣ Nat.card ↥(fixSub α) := by
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  have hdih := kaL2_inndiag_dihedral hF e α hα hα1 hαD
  have hinn : ∀ e' ∈ P, e' ∈ innAut K := fun e' he' =>
    kaL2_odd_mem_innAut hF e
      (kaL2_dihedral_mem_innDiag hF e α hdih hp hp2 hPp hcomm hnorm e' he')
      (ka_odd_of_mem_pGroup hp hp2 hPp he')
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hX0p := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0ne : kaInner P ≠ ⊥ := kaInner_ne_bot hP1 hinn
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hX0p.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hX0ne (Subgroup.eq_bot_of_card_eq _ (by simpa using hm))
  have hdvd : p ∣ Nat.card ↥(kaInner P) := by
    rw [hm]
    exact dvd_pow_self p hm0
  exact hdvd.trans (Subgroup.card_dvd_of_le hX0C)

theorem kaL2_card_fix_inner (hF : L2Field F) (e : K ≃* L2 F) (ε : ℤ) (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ) (hd : (d : ℤ) = Nat.card F - ε)
    {α : MulAut K} (hα : α * α = 1) (hα1 : α ≠ 1) (hin : α ∈ innAut K) :
    Nat.card ↥(fixSub α) = d := by
  classical
  obtain ⟨u, hu⟩ := hin
  have hu2 : u * u = 1 := by
    have h1 : MulAut.conj (u * u) = (1 : MulAut K) := by rw [map_mul, hu]; exact hα
    exact (conj_injective_of_L2 e) (h1.trans (map_one _).symm)
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hu]; simp)
  have hordu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hdih := (ivk_1_3a F hF K e ε hε1 hε d hd u hordu).2.1
  rw [← hu, kaL2_fixSub_eq, fixedSubgroup_conj_eq_centralizer]
  exact card_of_isDihedralOrder hdih

theorem kaL2_card_fix_outer (hF : L2Field F) (e : K ≃* L2 F) (ε : ℤ) (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ) (hd : (d : ℤ) = Nat.card F + ε)
    {α : MulAut K} (hα : α * α = 1) (hα1 : α ≠ 1) (hαD : α ∈ innDiagSub e)
    (hout : α ∉ innAut K) : Nat.card ↥(fixSub α) = d := by
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
  have hdih := (ivk_1_3b F hF K e ε hε1 hε d hd α hαD hout hα2).2.1
  rw [kaL2_fixSub_eq]
  exact card_of_isDihedralOrder hdih

theorem kaTwoY_L2 (hF : L2Field F) (e : K ≃* L2 F) : KATwoY K := by
  intro α β hα2 hα1 hβ2 hβ1 p hp hp2 P Q hP hQ
  have hαD := kaL2_mem_innDiag_of_hyp hF e hα2 hα1 hp hp2 hP
  have hβD := kaL2_mem_innDiag_of_hyp hF e hβ2 hβ1 hp hp2 hQ
  have hdα := kaL2_hyp_dvd hF e hα2 hα1 hαD hp hp2 hP
  have hdβ := kaL2_hyp_dvd hF e hβ2 hβ1 hβD hp hp2 hQ
  obtain ⟨d₁, d₂, ε, hε1, hε, hd₁, hd₂, -, -⟩ := exists_eps_d (Nat.card F) hF.1 hF.2
  have hsep : ∀ a b : MulAut K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → b ∈ innDiagSub e →
      p ∣ Nat.card ↥(fixSub a) → p ∣ Nat.card ↥(fixSub b) → a ∈ innAut K → b ∉ innAut K →
      False := by
    intro a b ha2 ha1 hb2 hb1 hbD hpa hpb hain hbout
    rw [kaL2_card_fix_inner hF e ε hε1 hε d₁ hd₁ ha2 ha1 hain] at hpa
    rw [kaL2_card_fix_outer hF e ε hε1 hε d₂ hd₂ hb2 hb1 hbD hbout] at hpb
    have h1 : (p : ℤ) ∣ (d₂ : ℤ) - d₁ :=
      dvd_sub (Int.natCast_dvd_natCast.mpr hpb) (Int.natCast_dvd_natCast.mpr hpa)
    have h2 : (d₂ : ℤ) - d₁ = 2 * ε := by rw [hd₁, hd₂]; ring
    rw [h2] at h1
    have h3 : (p : ℤ) ∣ 2 := by
      rcases hε1 with rfl | rfl
      · simpa using h1
      · have := (dvd_neg (a := (p : ℤ)) (b := 2 * -1)).mpr h1
        simpa using this
    have h4 : p ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  by_cases hαin : α ∈ innAut K
  · by_cases hβin : β ∈ innAut K
    · exact (innAut K).mul_mem hαin hβin
    · exact (hsep α β hα2 hα1 hβ2 hβ1 hβD hdα hdβ hαin hβin).elim
  · by_cases hβin : β ∈ innAut K
    · exact (hsep β α hβ2 hβ1 hα2 hα1 hαD hdβ hdα hβin hαin).elim
    · have hidx : ((innAut K).subgroupOf (innDiagSub e)).index = 2 := innAut_relIndex_two e hF
      have h1 : ∀ x y : ↥(innDiagSub e), x * y ∈ (innAut K).subgroupOf (innDiagSub e) ↔
          (x ∈ (innAut K).subgroupOf (innDiagSub e) ↔ y ∈ (innAut K).subgroupOf (innDiagSub e)) :=
        fun x y => Subgroup.mul_mem_iff_of_index_two hidx
      have h2 : (⟨α, hαD⟩ : ↥(innDiagSub e)) * ⟨β, hβD⟩ ∈
          (innAut K).subgroupOf (innDiagSub e) := by
        refine (h1 _ _).mpr ?_
        simp only [Subgroup.mem_subgroupOf]
        exact iff_of_false hαin hβin
      exact h2

end Dihedral

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

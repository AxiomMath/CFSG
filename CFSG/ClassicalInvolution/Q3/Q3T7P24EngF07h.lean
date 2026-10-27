module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF07x
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06h

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem graph_sq (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hT : S24B.TrivMu Ω W c) (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c * c = 1 := by
  have hcN := C.le_normalizer_W hcS
  have hK : conjSub c K = K := by
    have h := C.fix_of_trivMu hcN hT C.D.F.ρ
    rwa [C.hK] at h
  have hK' : conjSub c K' = K' := by
    have h := C.fix_of_trivMu hcN hT C.D.F.ρ'
    rwa [C.hK'] at h
  have hJ : conjSub c C.D.F.ρ₃.K = C.D.F.ρ₃.K := C.fix_of_trivMu hcN hT C.D.F.ρ₃
  have hRQ : ∀ q ∈ R, c * q * c⁻¹ ∈ R := fun q hq => by
    refine (le_of_eq C.inf_S_eq_R) ⟨?_, S.mul_mem (S.mul_mem hcS (C.hd.hR.2.2 hq))
      (S.inv_mem hcS)⟩
    have h := conj_mem_conjSub (n := c) (C.hd.hR.2.1 hq)
    rwa [hK] at h
  have hR'Q : ∀ q ∈ R', c * q * c⁻¹ ∈ R' := fun q hq => by
    refine (le_of_eq C.inf_S_eq_R') ⟨?_, S.mul_mem (S.mul_mem hcS (C.hd.hR'.2.2 hq))
      (S.inv_mem hcS)⟩
    have h := conj_mem_conjSub (n := c) (C.hd.hR'.2.1 hq)
    rwa [hK'] at h
  have hR : R ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.card_R C.r_mem_R
      C.r_not_mem_zpowers hRQ (hinv _ C.D.x₁_mem)
  have hR' : R' ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R'
      C.t_not_mem_zpowers hR'Q (hinv _ C.D.x₂_mem)
  have hQS : W ⊔ Subgroup.zpowers c ≤ (S : Subgroup G) :=
    sup_le C.hd.hWS (Subgroup.zpowers_le.mpr hcS)
  have hQ2 : IsPGroup 2 ↥(W ⊔ Subgroup.zpowers c) := S.isPGroup'.to_le hQS
  have hQJ : W ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (C.D.F.ρ₃.K : Set G) :=
    sup_le (C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃)
      (Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hJ))
  obtain ⟨T₃, hT₃, hT₃n⟩ := T3.exists_sylow_normalized hQ2 hQJ
  have hT₃N : W ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (T₃ : Set G) := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mpr (hT₃n q hq)
  have hx₃T : C.D.x₃ ∈ T₃ := by
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers C.D.x₃) :=
      T7A.isPGroup_zpowers_of_orderOf_four C.orderOf_x₃
    have hle : Subgroup.zpowers C.D.x₃ ≤ Subgroup.normalizer (T₃ : Set G) :=
      Subgroup.zpowers_le.mpr (hT₃N (Subgroup.mem_sup_left C.D.x₃_mem))
    have hsup := h2.to_sup_of_normal_right' hT₃.2.1 hle
    have heq := hT₃.eq_of_le hsup
      (sup_le (Subgroup.zpowers_le.mpr C.x₃_mem_J) hT₃.1) le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hT₃W : T₃ ≤ Subgroup.normalizer (W : Set G) := by
    have hsup := hQ2.to_sup_of_normal_right' hT₃.2.1 hT₃N
    obtain ⟨S'', hS''⟩ := hsup.exists_le_sylow
    have hWS'' : W ≤ (S'' : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS'')
    have hT₃S'' : T₃ ≤ (S'' : Subgroup G) := le_sup_right.trans hS''
    exact (Q3CL.Thompson.mem_DSet_of_le_sylow C.D.c.hΩ C.D.c.hW hWS''
      (mem_RSet_of_isSylow2In C.D.F.ρ₃.hK hT₃) hT₃S'').2
  have hcard : Nat.card ↥T₃ = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₃) := by
    rw [IsSylow2In.natCard_eq hT₃ C.D.F.ρ₃.hRK]
    have h := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    rw [← C.D.h₃] at h
    exact h
  have hU₃ : Subgroup.zpowers C.D.x₃ ≤ T₃ := Subgroup.zpowers_le.mpr hx₃T
  obtain ⟨s₃, hs₃, hs₃U⟩ : ∃ s₃ ∈ T₃, s₃ ∉ Subgroup.zpowers C.D.x₃ := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : T₃ ≤ Subgroup.zpowers C.D.x₃)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers C.D.x₃) := Nat.card_pos
    omega
  have hT₃Q : ∀ q ∈ T₃, c * q * c⁻¹ ∈ T₃ := fun q hq => by
    have h := hT₃n c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    rw [← h]
    exact conj_mem_conjSub hq
  have hT₃c : T₃ ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer hU₃ hcard hs₃ hs₃U hT₃Q (hinv _ C.D.x₃_mem)
  refine S24B.eq_one_of_forall_pow
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (S.mul_mem hcS hcS))) fun k hk => ?_
  exact h3a _ hk
    (S24B.le_centralizer_pow hR k) (S24B.le_centralizer_pow hR' k) T₃ hT₃ hT₃W
    (S24B.le_centralizer_pow hT₃c k)

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem exists_gen_I (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) (hnga : ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G))
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W)
    (hI : ∀ a : ↥C.A, (C.lam a : G) = 1 ∨ (C.lam a : G) = z) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have hdec : ∀ a ∈ C.A, ∃ e ∈ C.Dg, e⁻¹ * a ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro a ha
    rcases C.mem_Dg_of_lam ha (hI ⟨a, ha⟩) with h | h
    · exact ⟨a, h, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
    · refine ⟨_, h, ?_⟩
      have e : (a * C.D.x₂⁻¹)⁻¹ * a = C.D.x₂ := by group
      rw [e]
      exact hx₂P
  obtain ⟨y, hyS, hyM⟩ := IsConcreteLE.not_le_iff_exists.mp hSP
  obtain ⟨x, hxP, a, ha, rfl⟩ := C.exists_mem_A hnga hyS
  obtain ⟨d, hd, hda⟩ := hdec a ha
  have hdS : d ∈ (S : Subgroup G) := C.A_le_S (C.Dg_le_A hd)
  have hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro hdP
    apply hyM
    have e : x * a = x * d * (d⁻¹ * a) := by group
    rw [e]
    exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxP hdP) hda).2
  refine ⟨d, hdS, ?_, ?_, d, hd, C.Dg_sq_of_not_mem h3a hd hdP⟩
  · rw [C.Dg_pow_four h3a hd]
    exact Subgroup.one_mem _
  · intro y' hy'
    obtain ⟨x', hx'P, a', ha', rfl⟩ := C.exists_mem_A hnga hy'
    obtain ⟨e, he, hea⟩ := hdec a' ha'
    by_cases heP : e ∈ (S : Subgroup G) ⊓ MGrp Ω W
    · refine ⟨0, ?_⟩
      have e1 : (d ^ (0 : ℤ))⁻¹ * (x' * a') = x' * e * (e⁻¹ * a') := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx'P heP) hea
    · refine ⟨1, ?_⟩
      have h1 := C.Dg_inv_mul_mem h3a hd he hdP heP
      have h2 := C.P_normal (S.inv_mem hdS) hx'P
      have e1 : (d ^ (1 : ℤ))⁻¹ * (x' * a') =
          d⁻¹ * x' * d⁻¹⁻¹ * ((d⁻¹ * e) * (e⁻¹ * a')) := by group
      rw [e1]
      exact Subgroup.mul_mem _ h2 (Subgroup.mul_mem _ h1 hea)

theorem exists_gen_II (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) (hnga : ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G)) {a : G}
    (ha : a ∈ C.A) (h1 : (C.lam ⟨a, ha⟩ : G) ≠ 1) (hz : (C.lam ⟨a, ha⟩ : G) ≠ z) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have haS : a ∈ (S : Subgroup G) := C.A_le_S ha
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = (C.lam ⟨a, ha⟩ : G) := ⟨_, rfl⟩
  have hy₀mem : y₀ ∈ Subgroup.zpowers C.D.x₂ := hy₀ ▸ (C.lam ⟨a, ha⟩).2
  have hy₀sq : y₀ * y₀ ≠ 1 := by
    intro h
    rcases eq_one_or_eq_sq_of_mem_zpowers C.orderOf_x₂ hy₀mem h with h' | h'
    · exact h1 (hy₀ ▸ h')
    · exact hz (hy₀ ▸ h'.trans C.x₂_sq)
  obtain ⟨hsq, hgen⟩ := sq_and_gen_of_mem_zpowers C.orderOf_x₂ hy₀mem hy₀sq
  have hd₀A : a * a * C.D.x₂⁻¹ ∈ C.A :=
    C.A.mul_mem (C.A.mul_mem ha ha) (C.A.inv_mem C.x₂_mem_A)
  have hd₀ : a * a * C.D.x₂⁻¹ ∈ C.Dg := by
    refine (C.lam_eq_one_iff ⟨_, hd₀A⟩).mp (Subtype.ext ?_)
    have e : (⟨a * a * C.D.x₂⁻¹, hd₀A⟩ : ↥C.A) =
        ⟨a, ha⟩ * ⟨a, ha⟩ * (⟨C.D.x₂, C.x₂_mem_A⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [C.lam_x₂, ← hy₀, hsq, C.x₂_sq, mul_inv_cancel]
  have hca : Commute a C.D.x₂ :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.A_le_centralizer_x₂ ha)
  have hcomm : Commute (a * a) C.D.x₂⁻¹ := (hca.mul_left hca).inv_right
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hzK.sq
  have hsq₀ : (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = a ^ 4 * z := by
    calc (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = (a * a * C.D.x₂⁻¹) ^ 2 := (sq _).symm
      _ = (a * a) ^ 2 * (C.D.x₂ ^ 2)⁻¹ := by rw [hcomm.mul_pow, inv_pow]
      _ = a ^ 4 * z := by
          rw [C.x₂_sq, hzinv]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hd₀P : a * a * C.D.x₂⁻¹ ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro hP
    have h2 : (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = 1 := by
      rcases C.Dg_mem_P hd₀ hP with h | h <;> rw [h]
      · exact mul_one 1
      · exact C.hzK.sq
    rw [hsq₀] at h2
    apply C.pow_four_ne_z ha
    calc a ^ 4 = a ^ 4 * z * z := by rw [mul_assoc, C.hzK.sq, mul_one]
      _ = z := by rw [h2, one_mul]
  have hd₀z := C.Dg_sq_of_not_mem h3a hd₀ hd₀P
  have ha4 : a ^ 4 = 1 := by
    have h := hsq₀.symm.trans hd₀z
    calc a ^ 4 = a ^ 4 * z * z⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  refine ⟨a, haS, by rw [ha4]; exact Subgroup.one_mem _, ?_, _, hd₀, hd₀z⟩
  intro y hy
  obtain ⟨x, hxP, a', ha', rfl⟩ := C.exists_mem_A hnga hy
  obtain ⟨k, hk⟩ := hgen _ (C.lam ⟨a', ha'⟩).2
  have heA : a ^ (-k) * a' ∈ C.A := C.A.mul_mem (C.A.zpow_mem ha (-k)) ha'
  have he : a ^ (-k) * a' ∈ C.Dg := by
    refine (C.lam_eq_one_iff ⟨_, heA⟩).mp (Subtype.ext ?_)
    have e : (⟨a ^ (-k) * a', heA⟩ : ↥C.A) = ⟨a, ha⟩ ^ (-k) * ⟨a', ha'⟩ := rfl
    rw [e, map_mul, map_zpow]
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, OneMemClass.coe_one]
    rw [← hy₀, ← hk, zpow_neg, inv_mul_cancel]
  by_cases heP : a ^ (-k) * a' ∈ (S : Subgroup G) ⊓ MGrp Ω W
  · refine ⟨k, ?_⟩
    have e1 : (a ^ k)⁻¹ * (x * a') = a ^ (-k) * x * (a ^ (-k))⁻¹ * (a ^ (-k) * a') := by group
    rw [e1]
    exact Subgroup.mul_mem _ (C.P_normal (S.zpow_mem haS _) hxP) heP
  · refine ⟨k + 2, ?_⟩
    have h1 := C.Dg_inv_mul_mem h3a hd₀ he hd₀P heP
    have e1 : (a ^ (k + 2))⁻¹ * (x * a') = a ^ (-(k + 2)) * x * (a ^ (-(k + 2)))⁻¹ *
        (C.D.x₂⁻¹ * ((a * a * C.D.x₂⁻¹)⁻¹ * (a ^ (-k) * a'))) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (C.P_normal (S.zpow_mem haS _) hxP)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂P) h1)

theorem exists_gen (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) (hnga : ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G))
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  by_cases hI : ∀ a : ↥C.A, (C.lam a : G) = 1 ∨ (C.lam a : G) = z
  · exact C.exists_gen_I h3a hnga hSP hI
  · push Not at hI
    obtain ⟨⟨a, ha⟩, h1, hz⟩ := hI
    exact C.exists_gen_II h3a hnga ha h1 hz

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8

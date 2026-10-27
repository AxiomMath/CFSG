module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06x
public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc2

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
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem exists_inj_D (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) :
    ∃ μ : ↥C.Dg →* ↥(Subgroup.zpowers C.D.x₃), Function.Injective μ := by
  obtain ⟨T₃, hT₃, hx₃T, hTW, hDN⟩ := C.exists_T3
  have hcard : Nat.card ↥T₃ = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₃) := by
    rw [IsSylow2In.natCard_eq hT₃ C.D.F.ρ₃.hRK]
    have h := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    rw [← C.D.h₃] at h
    exact h
  have hU : Subgroup.zpowers C.D.x₃ ≤ T₃ := Subgroup.zpowers_le.mpr hx₃T
  obtain ⟨s₃, hs₃, hs₃U⟩ : ∃ s₃ ∈ T₃, s₃ ∉ Subgroup.zpowers C.D.x₃ := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : T₃ ≤ Subgroup.zpowers C.D.x₃)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers C.D.x₃) := Nat.card_pos
    omega
  have hDC : C.Dg ≤ Subgroup.centralizer ({C.D.x₃} : Set G) :=
    C.Dg_le_A.trans C.A_le_centralizer_x₃
  refine ⟨qHom hU hcard hs₃ hs₃U hDN hDC, ?_⟩
  rw [injective_iff_map_eq_one]
  intro d hd
  have hT : T₃ ≤ Subgroup.centralizer ({(d : G)} : Set G) :=
    (qHom_eq_one_iff hU hcard hs₃ hs₃U hDN hDC d).mp hd
  have hdA := C.Dg_le_A d.2
  have hdR : R ≤ Subgroup.centralizer ({(d : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ((C.mem_A).mp hdA).2.2.1 y hy
  have hdR' : R' ≤ Subgroup.centralizer ({(d : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp d.2.2 y hy
  apply Subtype.ext
  refine eq_one_of_forall_pow (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (C.A_le_S hdA)))
    fun k hk => ?_
  exact h3a _ hk
    (le_centralizer_pow hdR k) (le_centralizer_pow hdR' k) T₃ hT₃ hTW (le_centralizer_pow hT k)

include C in
theorem exists_mem_A (hnga : ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G)) {y : G}
    (hy : y ∈ (S : Subgroup G)) : ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, ∃ a ∈ C.A, y = x * a := by
  obtain ⟨x, hxP, t, htS, hT, rfl⟩ := C.exists_decomp hy
  have htW : t ∈ Subgroup.centralizer (W : Set G) :=
    hnga t htS hT
  have htN : t ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) htW
  have hK : conjSub t K = K := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ
    rwa [C.hK] at h
  have hK' : conjSub t K' = K' := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ'
    rwa [C.hK'] at h
  have hJ := C.fix_of_trivMu htN hT C.D.F.ρ₃
  obtain ⟨w, hw, hwt⟩ := C.exists_W_mul_mem_centralizer htS htW hK
  have hwP := C.W_le_P hw
  refine ⟨x * w⁻¹, Subgroup.mul_mem _ hxP (Subgroup.inv_mem _ hwP), w * t, ?_, by group⟩
  refine (C.mem_A).mpr ⟨S.mul_mem (C.hd.hWS hw) htS, ?_, hwt, ?_, ?_⟩
  · refine Subgroup.mul_mem _ ?_ htW
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW v hv w hw
  · exact Subgroup.mul_mem _ (C.W_le_normalizer K' C.hK'tw.1 ⟨C.x₂_mem_K', C.D.x₂_mem⟩
      C.orderOf_x₂ hw) (mem_normalizer_iff_conjSub_eq.mpr hK')
  · exact Subgroup.mul_mem _ (C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK
      ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃ hw) (mem_normalizer_iff_conjSub_eq.mpr hJ)

theorem Dg_pow_four (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {d : G} (hd : d ∈ C.Dg) : d ^ 4 = 1 := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3a
  have hy4 : (μ ⟨d, hd⟩ : G) ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← C.orderOf_x₃]
    exact orderOf_dvd_of_mem_zpowers (μ ⟨d, hd⟩).2
  have h : μ (⟨d, hd⟩ ^ 4) = μ 1 := by
    rw [map_pow, map_one]
    exact Subtype.ext hy4
  exact congrArg Subtype.val (hμ h)

theorem Dg_comm (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {d e : G} (hd : d ∈ C.Dg) (he : e ∈ C.Dg) :
    d * e = e * d := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3a
  have h : μ (⟨d, hd⟩ * ⟨e, he⟩) = μ (⟨e, he⟩ * ⟨d, hd⟩) := by
    rw [map_mul, map_mul]
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (μ ⟨d, hd⟩).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (μ ⟨e, he⟩).2
    simp only [Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self C.D.x₃ i j).eq
  exact congrArg Subtype.val (hμ h)

theorem Dg_involution (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {d : G} (hd : d ∈ C.Dg)
    (h2 : d * d = 1) : d = 1 ∨ d = z := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3a
  have key : ∀ e : ↥C.Dg, e * e = 1 → e = 1 ∨ (μ e : G) = C.D.x₃ ^ 2 := by
    intro e he
    have hy : (μ e : G) * (μ e : G) = 1 := by
      have h := congrArg (fun q => (μ q : G)) he
      simpa only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] using h
    rcases eq_one_or_eq_sq_of_mem_zpowers C.orderOf_x₃ (μ e).2 hy with h | h
    · left
      apply hμ
      rw [map_one]
      exact Subtype.ext h
    · exact Or.inr h
  rcases key ⟨d, hd⟩ (Subtype.ext h2) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · right
    rcases key ⟨z, C.z_mem_Dg⟩ (Subtype.ext C.hzK.sq) with h' | h'
    · exact absurd (congrArg Subtype.val h') C.hzK.ne_one
    · have e : (⟨d, hd⟩ : ↥C.Dg) = ⟨z, C.z_mem_Dg⟩ := hμ (Subtype.ext (h.trans h'.symm))
      exact congrArg Subtype.val e

theorem Dg_sq_of_not_mem (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {d : G} (hd : d ∈ C.Dg)
    (hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W) : d * d = z := by
  have hdd : d * d ∈ C.Dg := C.Dg.mul_mem hd hd
  have h4 : (d * d) * (d * d) = 1 := by
    calc (d * d) * (d * d) = d ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := C.Dg_pow_four h3a hd
  rcases C.Dg_involution h3a hdd h4 with h | h
  · exfalso
    apply hdP
    rcases C.Dg_involution h3a hd h with h' | h'
    · rw [h']
      exact Subgroup.one_mem _
    · rw [h']
      exact C.z_mem_P
  · exact h

theorem Dg_inv_mul_mem (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {d e : G} (hd : d ∈ C.Dg)
    (he : e ∈ C.Dg) (hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W)
    (heP : e ∉ (S : Subgroup G) ⊓ MGrp Ω W) : d⁻¹ * e ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  have hd2 := C.Dg_sq_of_not_mem h3a hd hdP
  have he2 := C.Dg_sq_of_not_mem h3a he heP
  have hc : Commute d e := C.Dg_comm h3a hd he
  have hc' : e * d⁻¹ = d⁻¹ * e := hc.inv_left.eq.symm
  have hde : d⁻¹ * e ∈ C.Dg := C.Dg.mul_mem (C.Dg.inv_mem hd) he
  have h2 : (d⁻¹ * e) * (d⁻¹ * e) = 1 := by
    calc (d⁻¹ * e) * (d⁻¹ * e) = d⁻¹ * (e * d⁻¹) * e := by group
      _ = d⁻¹ * (d⁻¹ * e) * e := by rw [hc']
      _ = (d * d)⁻¹ * (e * e) := by group
      _ = 1 := by rw [hd2, he2, inv_mul_cancel]
  rcases C.Dg_involution h3a hde h2 with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact C.z_mem_P

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8

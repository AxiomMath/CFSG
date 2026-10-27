module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10Basic
public import CFSG.GH74.GLS.Stage2.Final.Basic
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section C1

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem not_comm_S (ctx : Stage2Ctx G z k S) : ¬ IsMulCommutative ↥S := by
  obtain ⟨P, hP⟩ := CFSG.GH74.GLS.Stage2.Final.sylow_of_sylowTop ctx.sylow_top
  rw [← hP]
  exact ctx.std.nonab P

theorem exists_normal_four_S (ctx : Stage2Ctx G z k S) :
    ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
  have hS2 : IsPGroup 2 ↥S := ctx.sylow.isPGroup
  have hrk : 2 ≤ pRank 2 ↥(⊤ : Subgroup ↥S) := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    have := CFSG.GH74.GLS.Stage2.Final.Thm4.three_le_pRank_S ctx
    omega
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 2 Nat.prime_two ↥S hS2 ⊤ inferInstance hrk with
    ⟨E, hEn, -, hEe, hEc⟩ | ⟨-, hD | hSD⟩
  · refine ⟨E.map S.subtype, ?_, isFour_map_of_inj S.subtype S.subtype_injective hEe hEc, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact e.2
    · intro s hs x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨⟨s, hs⟩ * e * ⟨s, hs⟩⁻¹, hEn.conj_mem e he ⟨s, hs⟩, rfl⟩
  · exfalso
    obtain ⟨m, hm, ⟨e⟩⟩ := hD
    refine CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S ctx ⟨2 * 2 ^ m, 2 ^ m, rfl, ?_,
      ⟨(Subgroup.topEquiv (G := ↥S)).symm.trans e⟩⟩
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · exfalso
    obtain ⟨n, hn, ⟨e⟩⟩ := hSD
    exact not_SDorWr sdWr_rank2 ctx (Or.inl ⟨n, hn, ⟨(Subgroup.topEquiv (G := ↥S)).symm.trans e⟩⟩)

end C1

section C1b

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem mem_zStar_of_cover (hz : z ∈ M)
    (hcov : ∀ h ∈ M, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 M, h = c * o) : z ∈ zStar M := by
  have hnorm := le_normalizer_pPrimeCoreOf M
  refine ⟨hz, Subgroup.le_normalizer hz, hnorm hz, fun kk hkk => ?_⟩
  obtain ⟨c, hc, o, ho, rfl⟩ := hcov kk hkk
  have hoM : o ∈ M := (Subgroup.map_subtype_le _) ho
  have hcM : c ∈ M := by
    have : c = (c * o) * o⁻¹ := by group
    rw [this]
    exact M.mul_mem hkk (M.inv_mem hoM)
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hu : o * z * o⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 M := by
    have h1 : z * o⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 M :=
      (mem_normalizer_iff.mp (hnorm hz) o⁻¹).mp ((pPrimeCoreOf 2 M).inv_mem ho)
    have : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
    rw [this]
    exact (pPrimeCoreOf 2 M).mul_mem ho h1
  have hu' : c * (o * z * o⁻¹ * z⁻¹) * c⁻¹ ∈ pPrimeCoreOf 2 M :=
    (mem_normalizer_iff.mp (hnorm hcM) _).mp hu
  have hzc : z⁻¹ * c⁻¹ * z = c⁻¹ := by
    have hcz' : z * c⁻¹ = c⁻¹ * z := (Commute.inv_right (show Commute z c from hcz.symm)).eq
    rw [mul_assoc, ← hcz', inv_mul_cancel_left]
  have e : ⁅c * o, z⁆ = c * (o * z * o⁻¹ * z⁻¹) * c⁻¹ := by
    have h2 : c * o * z * (c * o)⁻¹ * z⁻¹ =
        c * (o * z * o⁻¹) * (z⁻¹ * c⁻¹ * z) * z⁻¹ := by
      rw [hzc]; group
    simp only [commutatorElement_def]
    rw [h2]
    group
  rw [e]
  exact hu'

theorem z_mem_zStar_of_typeOne (h34 : Leaf_Prop34) (ctx : Stage2Ctx G z k S) (hone : TypeOneCase G k)
    (hM : M ∈ maximalOverCentralizer z) : z ∈ zStar M := by
  have hCM : Cen z ≤ M := hM.2
  rcases h34 G z k S ctx M hCM hM.1.1 with hcov | hd | ⟨ε, q, L₁, L₂, hk, hL4, hq4, -, -, -, -, -, -⟩
  · exact mem_zStar_of_cover (hCM (mem_Cen_self z)) hcov
  · exact absurd hd (CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S ctx)
  · exfalso
    rcases hone with h1 | h1
    · rcases hL4.fusion with ⟨h2, -⟩ | ⟨h2, x, hx, -⟩
      · cases ε <;> simp at h2 hq4 <;> omega
      · exact hx.x_nonCentral (isCentralInvolution_of_isConj' ctx.central
          (h1 z x ctx.orderOf_z hx.x_inv))
    · rw [hk] at h1
      exact Kind.noConfusion h1

theorem exists_U_typeOne (ctx : Stage2Ctx G z k S) (hone : TypeOneCase G k) :
    ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧ z ∈ U ∧
      AutOrd (⊤ : Subgroup G) U = 6 := by
  by_cases hk : k = Kind.m12
  · subst hk
    have hd := ctx.data
    cases hd with
    | m12 h =>
      obtain ⟨U, hUS, hU4, hUn, hzU, -, -, hAut⟩ := h.four_group
      exact ⟨U, hUS, hU4, hUn, hzU, hAut⟩
  · have hone' : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := hone.resolve_right hk
    obtain ⟨U, hUS, hU4, hUn⟩ := exists_normal_four_S ctx
    obtain ⟨hzU, hAut⟩ := ctx.prop22a hone' (not_comm_S ctx) U hUS hU4 hUn
    exact ⟨U, hUS, hU4, hUn, hzU, hAut⟩

theorem choice10_typeOne (h34 : Leaf_Prop34) (ctx9 : Ctx9 G z k S M p) (hone : TypeOneCase G k) :
    ∃ (T U : Subgroup G) (t g : G), Choice10 G z k S M T U t g := by
  have ctx := ctx9.ctx
  have hz2 : z * z = 1 := ctx9.z_mul_z
  have hz1 : z ≠ 1 := fun h => by
    have := ctx9.orderOf_z
    rw [h, orderOf_one] at this
    omega
  obtain ⟨U, hUS, hU4, hUn, hzU, hAut⟩ := exists_U_typeOne ctx hone
  have hzstar : z ∈ zStar M := z_mem_zStar_of_typeOne h34 ctx hone ctx9.mem
  have htr : TransOn U := transOn_of_three_dvd hU4 (by rw [hAut]; exact ⟨2, rfl⟩)
  obtain ⟨x1, hx1, y1, hy1, hx1o, hy1o, hxy⟩ := exists_two_involutions_of_isFour hU4
  have hne1 : ∀ w : G, orderOf w = 2 → w ≠ 1 := fun w hw h => by
    rw [h, orderOf_one] at hw
    omega
  obtain ⟨t, htU, htz, ht1⟩ : ∃ t ∈ U, t ≠ z ∧ t ≠ 1 := by
    by_cases h : x1 = z
    · exact ⟨y1, hy1, fun h' => hxy (h.trans h'.symm), hne1 _ hy1o⟩
    · exact ⟨x1, hx1, h, hne1 _ hx1o⟩
  obtain ⟨n, hnN, hnz⟩ := htr z hzU hz1 t htU ht1
  refine ⟨S, U, t, n⁻¹, ?_⟩
  exact
    { U_le := hUS
      U_four := hU4
      U_gen := eq_zpowers_sup_of_isFour hU4 hzU htU hz1 ht1 htz.symm
      t_conj := by simpa using hnz.symm
      t_out := fun m hm h => false_of_move_M hU4 hz2 hzU htU htz ht1 (Or.inl hzstar) (M.inv_mem hm)
        (by simpa using h)
      T_one := fun _ => ⟨rfl, hUn⟩
      T_two := fun hn => absurd hone hn
      trans := fun _ => htr
      z_star := Or.inl hzstar
      z_star_one := fun _ => hzstar }

end C1b

end CFSG.GH74.GLS.Stage2.Bender.Thm2

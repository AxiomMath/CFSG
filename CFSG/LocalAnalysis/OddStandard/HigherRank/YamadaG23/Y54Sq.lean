module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Phi
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54X0b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem pCoreOf_eq_self_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 ↥K) :
    pCoreOf 2 K = K := by
  show (pCore 2 ↥K).map K.subtype = K
  apply le_antisymm (Subgroup.map_subtype_le _)
  intro b hb
  have htop : (⊤ : Subgroup ↥K) ≤ pCore 2 ↥K :=
    le_sSup ⟨Subgroup.normal_top, hK.of_equiv Subgroup.topEquiv.symm⟩
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

theorem y54_Y_cover (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ y ∈ f4Y c.s, y ∈ f4X0 c.s ∨
      ∃ n ∈ normIn L c.s.fr.F, ∃ x ∈ f4X0 c.s, y = n * c.d * n⁻¹ * x := by
  intro y hy
  have hfF : f3phi c.s y ∈ c.s.fr.F := y54_phi_mem hH y hy
  by_cases hf1 : f3phi c.s y = 1
  · exact Or.inl ((y54_phi_eq_one hH y hy).mp hf1)
  · obtain ⟨n, hn, hnz⟩ :=
      y54_trans1 hH c.s.fr.z (y54_z_mem_F c.s) (f3phi c.s y) hfF (y54_z_ne_one hH) hf1
    have hnN : n ∈ f4N c.s := y54_NL_le_N hH hn
    have hy' : n * c.d * n⁻¹ ∈ f4Y c.s :=
      y54_N_norm_Y hH n hnN c.d (y54_d_mem_Y hH)
    have hy'inv : (n * c.d * n⁻¹)⁻¹ ∈ f4Y c.s := (f4Y c.s).inv_mem hy'
    have hphi_y' : f3phi c.s (n * c.d * n⁻¹) = f3phi c.s y := by
      rw [y54_phi_conj hH n hnN c.d, y54_phi_d hH]
      exact hnz
    have hprod : f3phi c.s ((n * c.d * n⁻¹)⁻¹) * f3phi c.s (n * c.d * n⁻¹) = 1 := by
      rw [← y54_phi_mul hH ((n * c.d * n⁻¹)⁻¹) hy'inv (n * c.d * n⁻¹) hy']
      rw [inv_mul_cancel]
      simp [f3phi]
    have hinv : f3phi c.s ((n * c.d * n⁻¹)⁻¹) = (f3phi c.s (n * c.d * n⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    have hxY : (n * c.d * n⁻¹)⁻¹ * y ∈ f4Y c.s := (f4Y c.s).mul_mem hy'inv hy
    have hxphi : f3phi c.s ((n * c.d * n⁻¹)⁻¹ * y) = 1 := by
      rw [y54_phi_mul hH ((n * c.d * n⁻¹)⁻¹) hy'inv y hy, hinv, hphi_y']
      rw [inv_mul_cancel]
    refine Or.inr ⟨n, hn, (n * c.d * n⁻¹)⁻¹ * y,
      (y54_phi_eq_one hH _ hxY).mp hxphi, ?_⟩
    group

theorem y54_Y_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : ∀ y ∈ f4Y c.s, y ^ 2 ∈ c.s.fr.F := by
  intro y hy
  rcases y54_Y_cover c hH y hy with hyX0 | ⟨n, hn, x, hx, rfl⟩
  · rw [y54_X0_sq c hH y hyX0]
    exact c.s.fr.F.one_mem
  · have hn' : n⁻¹ ∈ normIn L c.s.fr.F := (normIn L c.s.fr.F).inv_mem hn
    have hnN : n ∈ f4N c.s := y54_NL_le_N hH hn
    have hx1 : n⁻¹ * x * n ∈ f4X0 c.s := by
      simpa using y54_N_norm_X0 hH n⁻¹ (y54_NL_le_N hH hn') x hx
    have hf1 : ⁅n⁻¹, x⁆ ∈ c.s.fr.F := y54_NL_X0 hH n⁻¹ hn' x hx
    have hf2 : ⁅c.d, n⁻¹ * x * n⁆ ∈ c.s.fr.F := y54_d_comm_X0 c hH _ hx1
    have hf3 : ⁅n, x⁆ ∈ c.s.fr.F := y54_NL_X0 hH n hn x hx
    have hd2 : c.d * c.d = 1 := by
      have h := pow_orderOf_eq_one c.d
      rw [c.d_order] at h
      simpa [pow_two] using h
    have hdinv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hd2
    have hx2 : x * x = 1 := by rw [← pow_two]; exact y54_X0_sq c hH x hx
    have hmain : (n * c.d * n⁻¹ * x) ^ 2 =
        (n * (⁅c.d, n⁻¹ * x * n⁆ * ⁅n⁻¹, x⁆) * n⁻¹) * (⁅n, x⁆ * (x * x)) := by
      rw [pow_two, commutatorElement_def, commutatorElement_def, commutatorElement_def, hdinv]
      group
    rw [hmain]
    refine c.s.fr.F.mul_mem ?_ ?_
    · exact (Subgroup.mem_set_normalizer_iff.mp hn.2
        (⁅c.d, n⁻¹ * x * n⁆ * ⁅n⁻¹, x⁆)).mp (c.s.fr.F.mul_mem hf2 hf1)
    · rw [hx2, mul_one]
      exact hf3

private theorem y54_comm_of_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e)
    (hsq : ∀ y ∈ f4Y c.s, y ^ 2 ∈ c.s.fr.F) :
    ∀ y ∈ f4Y c.s, ∀ y' ∈ f4Y c.s, ⁅y, y'⁆ ∈ c.s.fr.F := by
  have hPY : c.s.fr.F ≤ f4Y c.s := y54_F_le_Y hH
  have hnorm : ∀ k ∈ f4Y c.s, ∀ h ∈ c.s.fr.F, k * h * k⁻¹ ∈ c.s.fr.F := by
    intro k hk h hh
    have hkc : k ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
      rw [f4Y, centIn, Subgroup.mem_inf] at hk
      exact hk.2
    have hcomm : h * k = k * h := (Subgroup.mem_centralizer_iff.mp hkc) h hh
    have : k * h * k⁻¹ = h := by rw [← hcomm]; group
    rwa [this]
  haveI hnorm' : (c.s.fr.F.subgroupOf (f4Y c.s)).Normal :=
    (Subgroup.normal_subgroupOf_iff hPY).mpr fun h k hh hk => hnorm k hk h hh
  have hexp : ∀ g : (↥(f4Y c.s) ⧸ (c.s.fr.F).subgroupOf (f4Y c.s)), g ^ 2 = 1 := by
    intro g
    refine QuotientGroup.induction_on g fun y => ?_
    change (QuotientGroup.mk' ((c.s.fr.F).subgroupOf (f4Y c.s)) y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥(f4Y c.s)) : ↥(f4Y c.s) ⧸ (c.s.fr.F).subgroupOf (f4Y c.s)) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (y : G) y.2
  have hcomm : IsMulCommutative (↥(f4Y c.s) ⧸ (c.s.fr.F).subgroupOf (f4Y c.s)) := by
    apply IsMulCommutative.of_comm
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexp (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexp g
        have hh := hexp h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  have hcommle : _root_.commutator ↥(f4Y c.s) ≤ (c.s.fr.F).subgroupOf (f4Y c.s) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥(f4Y c.s))
      (N := (c.s.fr.F).subgroupOf (f4Y c.s))).mp hcomm
  intro y hy y' hy'
  have hmem : ⁅(⟨y, hy⟩ : ↥(f4Y c.s)), (⟨y', hy'⟩ : ↥(f4Y c.s))⁆ ∈
      _root_.commutator ↥(f4Y c.s) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcoe : ((⁅(⟨y, hy⟩ : ↥(f4Y c.s)), (⟨y', hy'⟩ : ↥(f4Y c.s))⁆ : ↥(f4Y c.s)) : G) =
      ⁅y, y'⁆ :=
    map_commutatorElement (f := (f4Y c.s).subtype) _ _
  have hmem' := hcommle hmem
  rw [Subgroup.mem_subgroupOf] at hmem'
  simpa [hcoe] using hmem'

theorem y54_Y_comm (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ y ∈ f4Y c.s, ∀ y' ∈ f4Y c.s, ⁅y, y'⁆ ∈ c.s.fr.F :=
  y54_comm_of_sq c hH (y54_Y_sq c hH)

theorem y54_Y_isPGroup (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsPGroup 2 ↥(f4Y c.s) := by
  intro y
  have hy2 : (y : G) ^ 2 ∈ c.s.fr.F := y54_Y_sq c hH (y : G) y.2
  have hy4 : (y : G) ^ 4 = 1 := by
    have h := y54_F_sq hH ((y : G) ^ 2) hy2
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact h
  exact ⟨2, Subtype.ext (by simpa using hy4)⟩

theorem y54_C3_eq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    C3 c.s = ⁅f4Y c.s, f4N c.s⁆ ⊔ f4P c.s := by
  rw [f4_C3_eq]
  have hKle : ⁅f4Y c.s, f4N c.s⁆ ≤ f4Y c.s := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b * a * b⁻¹ ∈ f4Y c.s := y54_N_norm_Y hH b hb a ha
    have hcomm : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [hcomm]
    exact (f4Y c.s).mul_mem ha ((f4Y c.s).inv_mem hb')
  rw [pCoreOf_eq_self_of_isPGroup ((y54_Y_isPGroup c hH).to_le hKle)]

end CFSG.OddStandard.HigherRank.YamadaG23

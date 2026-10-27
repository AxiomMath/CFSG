module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Phi
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Abs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YIdx2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem f3_T1_sq_mem_R {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ e.T₁, x ^ 2 ∈ s.R := by
  intro x hx
  have hxT : x ^ 2 ∈ s.T := sq_mem_of_relIndex_two e.T_le hH.hDef.2.1 hx
  have hR1le : e.R₁ ≤ e.T₁ := by
    unfold Setting3.Ext.R₁
    split_ifs
    · exact le_rfl
    · exact inf_le_left
  have hxR₁ : x ^ 2 ∈ e.R₁ := by
    by_cases hRT : s.R = s.T
    · unfold Setting3.Ext.R₁
      rw [if_pos hRT]
      exact e.T₁.pow_mem hx 2
    · exact sq_mem_of_relIndex_two hR1le (hH.h32.2.2.2 hRT) hx
  rw [← hH.h32.2.2.1]
  exact Subgroup.mem_inf.mpr ⟨hxR₁, hxT⟩

theorem f3_Y_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ f3Y s, y ^ 2 ∈ f3P s := by
  obtain ⟨u, huT₁, huY, hu_conj⟩ := f3_exists_u hH
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  have hu2R : u ^ 2 ∈ s.R := f3_T1_sq_mem_R hH u huT₁
  rw [s3_R_eq s hH.hS] at hu2R
  have hu2M : u ^ 2 ∈ L ⊔ centIn s.H L := (Subgroup.mem_inf.mp hu2R).2
  have hu2Y : u ^ 2 ∈ f3Y s := (f3Y s).pow_mem huY 2
  have hz2 : s.fr.z ^ 2 = 1 := by
    rw [← s3_z_order s hA]
    exact pow_orderOf_eq_one s.fr.z
  have hconjz : u * s.fr.z * u⁻¹ = s.fr.z := s3_conj_z s hA e hH.h32 huT₁
  have key : u ^ 2 * s.t * (u ^ 2)⁻¹ = s.t := by
    calc u ^ 2 * s.t * (u ^ 2)⁻¹
        = u * (u * s.t * u⁻¹) * u⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
      _ = u * (s.fr.z * s.t) * u⁻¹ := by rw [hu_conj]
      _ = (u * s.fr.z * u⁻¹) * (u * s.t * u⁻¹) := by group
      _ = s.fr.z * (s.fr.z * s.t) := by rw [hconjz, hu_conj]
      _ = s.fr.z ^ 2 * s.t := by rw [pow_two]; group
      _ = s.t := by rw [hz2]; group
  have hu2H : u ^ 2 ∈ s.H := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp key
  have hu2X0 : u ^ 2 ∈ f3X0 s := by
    rw [← f3_Y_inf_H hH]
    exact Subgroup.mem_inf.mpr ⟨hu2Y, hu2H⟩
  have hu2P : u ^ 2 ∈ f3P s := f3_X0_inf_M hH (u ^ 2) hu2X0 hu2M
  have hcov : ∀ y ∈ f3Y s, y ∈ f3X0 s ∨
      ∃ m ∈ f3N s, ∃ a ∈ f3X0 s, y = m * u * m⁻¹ * a := by
    intro y hy
    have hphi_mem : f3phi s y ∈ cen s.fr.B := f3_phi_mem hH y hy
    by_cases hv1 : f3phi s y = 1
    · exact Or.inl ((f3_phi_eq_one hH y hy).mp hv1)
    · right
      obtain ⟨k, hkN, _, _, _, hktrans, _⟩ := f3_exists_k hH
      obtain ⟨_, _, hzV, _, hz1, _, _, _, _, _⟩ := f3_V_elems hH
      obtain ⟨i, hi⟩ := hktrans s.fr.z hzV hz1 (f3phi s y) hphi_mem hv1
      have hkL : k ∈ L := (Subgroup.mem_inf.mp hkN).1
      have hkB : k ∈ normalizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hkN).2
      have hmN : k ^ i ∈ f3N s :=
        Subgroup.mem_inf.mpr
          ⟨s3_L_le_H s hH.hS (L.pow_mem hkL i),
            (normalizer (s.fr.B : Set G)).pow_mem hkB i⟩
      have hmX : k ^ i ∈ s.X := f3_N_le_X s hmN
      have hy'Y : k ^ i * u * (k ^ i)⁻¹ ∈ f3Y s := f3_Y_normal hH (k ^ i) hmX u huY
      have hphiu : f3phi s u = s.fr.z := by
        simp only [f3phi]
        rw [hu_conj]
        group
      have hcomm : k ^ i * s.t = s.t * k ^ i := s3_comm_t_of_mem_L s (L.pow_mem hkL i)
      have hphiy' : f3phi s (k ^ i * u * (k ^ i)⁻¹) = f3phi s y := by
        rw [f3_phi_conj s hcomm u, hphiu]
        exact hi
      have haY : (k ^ i * u * (k ^ i)⁻¹)⁻¹ * y ∈ f3Y s :=
        (f3Y s).mul_mem ((f3Y s).inv_mem hy'Y) hy
      have haX0 : (k ^ i * u * (k ^ i)⁻¹)⁻¹ * y ∈ f3X0 s := by
        apply (f3_phi_eq_one hH ((k ^ i * u * (k ^ i)⁻¹)⁻¹ * y) haY).mp
        have hmul := f3_phi_mul hH (k ^ i * u * (k ^ i)⁻¹) hy'Y
          ((k ^ i * u * (k ^ i)⁻¹)⁻¹ * y) haY
        have hy_eq : k ^ i * u * (k ^ i)⁻¹ * ((k ^ i * u * (k ^ i)⁻¹)⁻¹ * y) = y := by
          group
        rw [hy_eq, hphiy'] at hmul
        have h1 : f3phi s y * f3phi s ((k ^ i * u * (k ^ i)⁻¹)⁻¹ * y) = f3phi s y * 1 := by
          rw [mul_one]
          exact hmul.symm
        exact mul_left_cancel h1
      exact ⟨k ^ i, hmN, (k ^ i * u * (k ^ i)⁻¹)⁻¹ * y, haX0, by group⟩
  exact ext_sq (f3_extCtx hH) huY hu2P hcov

end CFSG.OddStandard.HigherRank.YamadaG23

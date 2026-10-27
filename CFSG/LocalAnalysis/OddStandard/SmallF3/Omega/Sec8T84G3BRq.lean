module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BRg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BAut

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {E E0 Y Y' V V' F F' P H : Subgroup G}

theorem sec8t84g3b_norm_image {B : Type} [Group B] [Finite B] (π : ↥Y →* B) {y : G}
    (hy : y ∈ Y) (hV : ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hF : ∀ f ∈ F, y * f * y⁻¹ ∈ F) :
    π ⟨y, hy⟩ ∈ normalizer ((((V.subgroupOf Y).map π ⊔ (F.subgroupOf Y).map π : Subgroup B)) :
      Set B) := by
  refine sec8t84g3b_mem_normalizer_of_conj (sec8t84g3b_conj_sup (fun a ha => ?_)
    (fun a ha => ?_))
  · obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨⟨y, hy⟩ * v' * ⟨y, hy⟩⁻¹, ?_, ?_⟩)
    · exact hV v' hv'
    · rw [map_mul, map_mul, map_inv]
  · obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨⟨y, hy⟩ * f' * ⟨y, hy⟩⁻¹, ?_, ?_⟩)
    · exact hF f' hf'
    · rw [map_mul, map_mul, map_inv]

theorem sec8t84g3b_odd_image {B : Type} [Group B] (π : ↥Y →* B) {y : G} (hy : y ∈ Y)
    (h : Odd (orderOf y)) : Odd (orderOf (π ⟨y, hy⟩)) := by
  have h1 := orderOf_map_dvd π (⟨y, hy⟩ : ↥Y)
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat h h1

theorem sec8t84g3b_phi_mem (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {B : Type} [Group B]
    [Finite B] (π : ↥Y →* B) {Vb Fb : Subgroup B} (hVb : Vb = (V.subgroupOf Y).map π)
    (hFb : Fb = (F.subgroupOf Y).map π) (hS1 : Vb ⊔ Fb ≤ sec8t84g3b_M Vb Fb) :
    ∀ z ∈ sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F'), ∀ hzY : z ∈ Y,
      π ⟨z, hzY⟩ ∈ sec8t84g3b_M Vb Fb := by
  subst hVb hFb
  have hK : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤
      ((sec8t84g3b_M ((V.subgroupOf Y).map π) ((F.subgroupOf Y).map π)).comap π).map
        Y.subtype := by
    refine sec8t84g3b_Z_le (fun y hyQ hyC hodd => ?_) (fun u hu => ?_)
    · have hyY : y ∈ Y := S.odd_Y (sec8t84g3b_Q_le_E hyQ) hodd (fun v hv =>
        (Subgroup.mem_centralizer_iff.mp hyC v (Subgroup.mem_sup_left hv)).symm)
      refine Subgroup.mem_map.mpr ⟨⟨y, hyY⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      unfold sec8t84g3b_M twoRes
      exact Subgroup.subset_closure ⟨sec8t84g3b_norm_image π hyY (S.conj_V hyY)
        (S.conj_F hyY (sec8t84g3b_Q_le_E0 hyQ)), sec8t84g3b_odd_image π hyY hodd⟩
    · have hle : V ⊔ F ≤
          (((V.subgroupOf Y).map π ⊔ (F.subgroupOf Y).map π).comap π).map Y.subtype := by
        refine sup_le (fun v hv => ?_) (fun f hf => ?_)
        · exact Subgroup.mem_map.mpr ⟨⟨v, S.ydata.V_le hv⟩, Subgroup.mem_comap.mpr
            (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π
              (x := ⟨v, S.ydata.V_le hv⟩) hv)), rfl⟩
        · exact Subgroup.mem_map.mpr ⟨⟨f, S.F_le_Y hf⟩, Subgroup.mem_comap.mpr
            (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem π
              (x := ⟨f, S.F_le_Y hf⟩) hf)), rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hle hu)
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr (hS1 (Subgroup.mem_comap.mp hx)),
        rfl⟩
  intro z hz hzY
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp (hK hz)
  have hxe : x = ⟨z, hzY⟩ := Subtype.ext hxz
  rw [← hxe]
  exact Subgroup.mem_comap.mp hx

theorem sec8t84g3b_range_gen (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {B : Type} [Group B]
    [Finite B] (π : ↥Y →* B) (hπs : Function.Surjective π)
    (hker : ∀ x : ↥Y, π x = 1 ↔ (x : G) ∈ oddCoreIn (normalizer (E : Set G)))
    {Vb Fb : Subgroup B} (hVb : Vb = (V.subgroupOf Y).map π)
    (hFb : Fb = (F.subgroupOf Y).map π)
    (hNJ : normalizer ((Vb ⊔ Fb : Subgroup B) : Set B) ≤ normalizer (Fb : Set B)) :
    ∀ g ∈ normalizer ((Vb ⊔ Fb : Subgroup B) : Set B), Odd (orderOf g) →
      ∃ z ∈ sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F'), ∃ hzY : z ∈ Y,
        π ⟨z, hzY⟩ = g := by
  subst hVb hFb
  intro g hg hodd
  obtain ⟨y0, rfl⟩ := hπs g
  have hnF := hNJ hg
  have hy0Y : (y0 : G) ∈ Y := y0.2
  have hnorm : (y0 : G) ∈ normalizer ((E0 ⊔ oddCoreIn (normalizer (E : Set G)) : Subgroup G) :
      Set G) := by
    rw [S.E0_eq]
    refine sec8t84g3b_mem_normalizer_of_conj (sec8t84g3b_conj_sup (fun x hx => ?_)
      (fun x hx => ?_))
    · refine sec8t84g3b_conj_sup (fun f hf => ?_) (fun f' hf' => ?_) x hx
      · have hfY : f ∈ Y := S.F_le_Y hf
        have h1 : π ⟨f, hfY⟩ ∈ (F.subgroupOf Y).map π :=
          Subgroup.mem_map_of_mem π (x := ⟨f, hfY⟩) hf
        have h2 := (Subgroup.mem_normalizer_iff.mp hnF _).mp h1
        obtain ⟨f1, hf1, hf1e⟩ := Subgroup.mem_map.mp h2
        have h3 : π (f1⁻¹ * (y0 * ⟨f, hfY⟩ * y0⁻¹)) = 1 := by
          simp only [map_mul, map_inv]
          rw [hf1e]
          exact inv_mul_cancel _
        have h4 : (f1 : G)⁻¹ * ((y0 : G) * f * (y0 : G)⁻¹) ∈
            oddCoreIn (normalizer (E : Set G)) := (hker _).mp h3
        have h5 : (y0 : G) * f * (y0 : G)⁻¹ =
            (f1 : G) * ((f1 : G)⁻¹ * ((y0 : G) * f * (y0 : G)⁻¹)) := by group
        rw [h5]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (show (f1 : G) ∈ F from hf1))) (Subgroup.mem_sup_right h4)
      · have h1 := S.comm y0 hy0Y f' (S.F'_le hf')
        have h2 : (y0 : G) * f' * (y0 : G)⁻¹ =
            ((y0 : G) * f' * (y0 : G)⁻¹ * f'⁻¹) * f' := by group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right hf'))
    · exact Subgroup.mem_sup_right
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (S.Y_le hy0Y) hx)
  obtain ⟨n, hn, hyQ⟩ := S.frattini (y0 : G) (S.Y_le hy0Y) hnorm
  have hy1Y : (y0 : G) * n ∈ Y := Y.mul_mem hy0Y (S.N_le hn)
  have hπy1 : π ⟨(y0 : G) * n, hy1Y⟩ = π y0 := by
    have h1 : (⟨(y0 : G) * n, hy1Y⟩ : ↥Y) = y0 * ⟨n, S.N_le hn⟩ := rfl
    rw [h1, map_mul, (hker ⟨n, S.N_le hn⟩).mpr hn, mul_one]
  have hy1odd : Odd (orderOf ((y0 : G) * n)) := by
    have h1 : (π ⟨(y0 : G) * n, hy1Y⟩) ^ (orderOf (π y0)) = 1 := by
      rw [hπy1]; exact pow_orderOf_eq_one _
    have h2 : π (⟨(y0 : G) * n, hy1Y⟩ ^ orderOf (π y0)) = 1 := by rw [map_pow]; exact h1
    have h3 : ((y0 : G) * n) ^ orderOf (π y0) ∈ oddCoreIn (normalizer (E : Set G)) := by
      have h4 := (hker _).mp h2
      rwa [Subgroup.coe_pow] at h4
    have h4 : ((y0 : G) * n) ^ orderOf (π y0) ∈ oddCoreIn (sec8t84g_Q E E0) := by
      rw [S.O_eq]; exact ⟨Subgroup.pow_mem _ hyQ _, h3⟩
    exact sec8t84g3b_odd_of_pow hodd h4
  have hy1C : (y0 : G) * n ∈ centralizer ((V' ⊔ F' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ Y' := S.U'_le_Y' hu
    have h1 := S.comm ((y0 : G) * n) hy1Y u hu'
    have h2 : ((y0 : G) * n) * u * ((y0 : G) * n)⁻¹ ∈ E ⊔ E0 :=
      sec8t84g3b_conj_W hyQ u (S.U'_le_W hu)
    have h3 : ((y0 : G) * n) * u * ((y0 : G) * n)⁻¹ * u⁻¹ ∈ E ⊔ E0 :=
      (E ⊔ E0).mul_mem h2 ((E ⊔ E0).inv_mem (S.U'_le_W hu))
    have h4 : ((y0 : G) * n) * u * ((y0 : G) * n)⁻¹ * u⁻¹ ∈
        (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨h3, h1⟩
    rw [S.W_inf, Subgroup.mem_bot] at h4
    have h5 : ((y0 : G) * n) * u = u * ((y0 : G) * n) := by
      calc ((y0 : G) * n) * u
          = (((y0 : G) * n) * u * ((y0 : G) * n)⁻¹ * u⁻¹) * (u * ((y0 : G) * n)) := by group
        _ = u * ((y0 : G) * n) := by rw [h4, one_mul]
    exact h5.symm
  exact ⟨(y0 : G) * n, Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨hyQ, hy1C⟩, hy1odd⟩),
    hy1Y, hπy1⟩

end CFSG.OddStandard.SmallF3.Omega

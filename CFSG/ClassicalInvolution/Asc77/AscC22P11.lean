module

public import CFSG.ClassicalInvolution.Asc77.AscS22E
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7JCent
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace C22P

set_option linter.unusedSectionVars false

section Alpha

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z g₀ g₁ g₂ : G}


omit [Finite G] [IsSimpleGroup G] in
theorem mem_normalizer_alphaOf_of_conjSub_eq {A : Subgroup G} {y : G} (h : conjSub y A = A) :
    y ∈ Subgroup.normalizer (alphaOf A : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have h1 := alphaOf_conjSub y A
  rw [h] at h1
  exact h1.symm

theorem mem_normalizer_alpha_of_frame (hs : Hyp22Setting p f Ω K K' K₃ z g₀ g₁ g₂)
    (hb : S22.Big Ω K) {y t : G} (hyu : y * (g₀ * g₁) = (g₀ * g₁) * y)
    (hyz : y * z * y⁻¹ = t) (hzt : z * t = t * z) (ht2 : t * t = 1)
    (htw : t * (g₁ * g₂) = (g₁ * g₂) * t)
    (hw : y * (g₁ * g₂) * y⁻¹ = g₁ * g₂ ∨ y * (g₁ * g₂) * y⁻¹ = (t * z) * (g₁ * g₂)) :
    y ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({g₀ * g₁, z} : Set G)) : Set G) := by
  classical
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz2 : z * z = 1 := hz.sq
  have h2 := S22.c22_2S p f G Ω K K' K₃ z g₀ g₁ g₂ hs hb
  have hcg := S22.comm_gen hs
  set u : G := g₀ * g₁ with hu
  set w : G := g₁ * g₂ with hwdef
  have huB : u ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_fst
  have hzB : z ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_snd
  have hwB : w ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_thd
  have cuz : u * z = z * u := hcg u (by simp [hu]) z (by simp)
  have cuw : u * w = w * u := hcg u (by simp [hu, hwdef]) w (by simp [hwdef])
  have czw : z * w = w * z := hcg z (by simp) w (by simp [hwdef])
  have hu2 : u * u = 1 := hs.sq_12
  have hw2 : w * w = 1 := hs.sq_23
  obtain ⟨hu1, huz⟩ := T7S22.mul_ne_one_of_twins hΩ hK hK' hs.hne.symm hz hs.hu₁.1 hs.hu₂.1
    hs.hu₂.2
  obtain ⟨hw1, hwz⟩ := T7S22.mul_ne_one_of_twins hΩ hK' hK₃Ω hs.hK₃K'.symm hzK' hs.hu₂.1
    hs.hu₃.1 hs.hu₃.2
  have hg12 : g₁ * g₂ = g₂ * g₁ := hs.comm₂₃
  have huw : u ≠ w := by
    intro h
    have e : g₀ = g₂ := by
      have h' : g₀ * g₁ = g₂ * g₁ := by rw [← hg12]; exact h
      exact mul_right_cancel h'
    exact T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃Ω hs.hK₃K hs.hu₃.2 (e ▸ hs.hu₁.1) hs.hu₃.1
  have huwz : u ≠ w * z := by
    intro h
    have e : g₀ = g₂ * z := by
      have hzg₁ : z * g₁ = g₁ * z := hs.comm_z₂
      have h' : g₀ * g₁ = (g₂ * z) * g₁ := by
        calc g₀ * g₁ = g₁ * g₂ * z := h
          _ = g₂ * g₁ * z := by rw [hg12]
          _ = g₂ * (g₁ * z) := by rw [mul_assoc]
          _ = g₂ * (z * g₁) := by rw [hzg₁]
          _ = (g₂ * z) * g₁ := by rw [mul_assoc]
      exact mul_right_cancel h'
    exact T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃Ω hs.hK₃K hs.hu₁.2 hs.hu₁.1
      (e ▸ K₃.mul_mem hs.hu₃.1 hzK₃.mem)
  have key : ∀ w' ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G), w' ≠ 1 → u ≠ w' →
      w' * w' = 1 → u * w' = w' * u → y * w' = w' * y →
      y ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({g₀ * g₁, z} : Set G)) : Set G) := by
    intro w' hw'B hw'1 huw' hw'2 hcomm hyw'
    have hA2 : IsElemAbelian2 (Subgroup.closure ({u, w'} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hu2 hw'2 hu1 hw'1 huw' hcomm
    have hAB : Subgroup.closure ({u, w'} : Set G) ≤
        Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huB
      · exact hw'B
    have hα := (h2.2 _ hAB hA2)
    have hyu' : y * u * y⁻¹ = u := by rw [hyu]; group
    have hyw'' : y * w' * y⁻¹ = w' := by rw [hyw']; group
    have hconj : conjSub y (Subgroup.closure ({u, w'} : Set G)) =
        Subgroup.closure ({u, w'} : Set G) := by
      rw [T7A.conjSub_closure_pair, hyu', hyw'']
    have := mem_normalizer_alphaOf_of_conjSub_eq hconj
    rwa [hα] at this
  rcases hw with h1 | h1
  · refine key w hwB hw1 huw hw2 cuw ?_
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [h1]
  · have hww : (w * z) * (w * z) = 1 := by
      calc (w * z) * (w * z) = (w * w) * (z * z) := by
            calc (w * z) * (w * z) = w * (z * w) * z := by group
              _ = w * (w * z) * z := by rw [czw]
              _ = (w * w) * (z * z) := by group
        _ = 1 := by rw [hw2, hz2]; group
    have hwzB : w * z ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := mul_mem hwB hzB
    have hwz1 : w * z ≠ 1 := by
      intro h
      apply hwz
      have : w = z⁻¹ := eq_inv_of_mul_eq_one_left h
      exact this.trans (inv_eq_of_mul_eq_one_right hz2)
    have hcomm : u * (w * z) = (w * z) * u := by
      calc u * (w * z) = (u * w) * z := by group
        _ = (w * u) * z := by rw [cuw]
        _ = w * (u * z) := by group
        _ = w * (z * u) := by rw [cuz]
        _ = (w * z) * u := by group
    refine key (w * z) hwzB hwz1 huwz hww hcomm ?_
    have hyz' : y * z = t * y := by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = t * y := by rw [hyz]
    have hyw : y * w = (t * z) * w * y := by
      calc y * w = (y * w * y⁻¹) * y := by group
        _ = (t * z) * w * y := by rw [h1]
    calc y * (w * z) = (y * w) * z := by group
      _ = (t * z) * w * y * z := by rw [hyw]
      _ = (t * z) * w * (y * z) := by group
      _ = (t * z) * w * (t * y) := by rw [hyz']
      _ = ((t * z) * (w * t)) * y := by group
      _ = ((t * z) * (t * w)) * y := by rw [← htw]
      _ = (t * (z * t) * w) * y := by group
      _ = (t * (t * z) * w) * y := by rw [hzt]
      _ = ((t * t) * (z * w)) * y := by group
      _ = (w * z) * y := by rw [ht2, czw]; group

theorem oddCore_centralizer_le_normalizer_alpha
    {u₁ u₂ u₃ : G} (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : S22.Big Ω K) :
    oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) ≤
      Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  classical
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have h2 := S22.c22_2S p f G Ω K K' K₃ z u₁ u₂ u₃ hs hb
  have hCz := S22.centralizer_le_normalizer_alpha (S22.c22_2S p f) hs hb
  set α₀ := alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) with hα₀
  obtain ⟨hu1, -⟩ := T7S22.mul_ne_one_of_twins hΩ hs.stand.mem hs.hK'.1 hs.hne.symm hs.hz
    hs.hu₁.1 hs.hu₂.1 hs.hu₂.2
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
      Subgroup.closure ({u₁ * u₂, z} : Set G)⁆ ≤ α₀ := by
    refine le_trans ?_ le_sup_left
    exact le_iSup₂_of_le (u₁ * u₂) (Subgroup.subset_closure (by simp))
      (le_iSup_of_le hu1 le_rfl)
  have hodd : ∀ x ∈ α₀, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat h2.1 (Subgroup.orderOf_dvd_natCard α₀ hx)
  intro n hn
  have hmα : ⁅n⁻¹, z⁆ ∈ α₀ :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hn)
      (Subgroup.subset_closure (by simp)))
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨m, hmdef⟩ : ∃ m : G, m = ⁅n⁻¹, z⁆ := ⟨_, rfl⟩
  rw [← hmdef] at hmα
  have hm : m = n⁻¹ * z * n * z := by
    rw [hmdef, commutatorElement_def, hzi]
    group
  have hzm : z * m * z⁻¹ = m⁻¹ := by
    rw [hm, hzi]
    calc z * (n⁻¹ * z * n * z) * z = z * n⁻¹ * z * n * (z * z) := by group
      _ = z * n⁻¹ * z * n := by rw [hz2]; group
      _ = (n⁻¹ * z * n * z)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]
  obtain ⟨s, hsm, hss⟩ := T7J.exists_sq_mem_zpowers (hodd m hmα)
  have hzs : z * s * z⁻¹ = s⁻¹ := T7J.conj_inv_of_mem_zpowers hzm hsm
  have hsα : s ∈ α₀ := (Subgroup.zpowers_le.mpr hmα) hsm
  have hzn : z * n * z⁻¹ = n * m := by
    rw [hm, hzi]
    group
  have hc : n * s ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : z * (n * s) * z⁻¹ = n * s := by
      calc z * (n * s) * z⁻¹ = (z * n * z⁻¹) * (z * s * z⁻¹) := by group
        _ = (n * m) * s⁻¹ := by rw [hzn, hzs]
        _ = n * (s * s) * s⁻¹ := by rw [hss]
        _ = n * s := by group
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hnn : n = (n * s) * s⁻¹ := by group
  rw [hnn]
  exact Subgroup.mul_mem _ (hCz hc) (Subgroup.inv_mem _ (Subgroup.le_normalizer hsα))

end Alpha

end C22P

end CFSG.ClassicalInvolution.Asc77

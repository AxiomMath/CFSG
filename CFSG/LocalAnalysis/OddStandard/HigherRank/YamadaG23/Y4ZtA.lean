module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GJ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma y4Zt_zmod4_pow_four (x : Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  simp [show (4 : ZMod 4) = 0 from by decide]

private lemma y4Zt_zmod4_prod_pow_four
    (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  apply Prod.ext
  · have h := map_pow (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x 4
    rw [show (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) (x ^ 4)
        = (x ^ 4).1 from rfl,
      show (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x = x.1
        from rfl] at h
    rw [h]
    exact y4Zt_zmod4_pow_four x.1
  · have h := map_pow (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x 4
    rw [show (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) (x ^ 4)
        = (x ^ 4).2 from rfl,
      show (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x = x.2
        from rfl] at h
    rw [h]
    exact y4Zt_zmod4_pow_four x.2

private theorem y4_b1_mem_B (c : Ctx4 s e) : s.fr.b₁ ∈ s.fr.B := by
  rw [SFrame.B, centIn, Subgroup.centralizer_closure, Subgroup.mem_inf]
  refine ⟨Subgroup.subset_closure (by simp), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hc : Commute s.fr.b₁ s.fr.b₂ :=
    commutatorElement_eq_one_iff_commute.mp c.hRel.b1b2
  exact ((Commute.refl s.fr.b₁).mul_right hc).eq.symm

private theorem y4_b2_mem_B (c : Ctx4 s e) : s.fr.b₂ ∈ s.fr.B := by
  rw [SFrame.B, centIn, Subgroup.centralizer_closure, Subgroup.mem_inf]
  refine ⟨Subgroup.subset_closure (by simp), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hc : Commute s.fr.b₁ s.fr.b₂ :=
    commutatorElement_eq_one_iff_commute.mp c.hRel.b1b2
  exact ((hc.symm).mul_right (Commute.refl s.fr.b₂)).eq.symm

private theorem y4_J_comm_exp (c : Ctx4 s e) :
    (∀ a ∈ thompsonSubgroup s.fr.B, ∀ b ∈ thompsonSubgroup s.fr.B, a * b = b * a) ∧
      (∀ j ∈ thompsonSubgroup s.fr.B, j ^ 4 = 1) := by
  obtain ⟨-, -, -, -, -, -, hJ, hJiso, -, -⟩ := c.hLF.fact14.2.2.1
  have hJ' : thompsonSubgroup s.fr.B =
      closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ
  obtain ⟨e₀⟩ := hJiso
  let e : ↥(thompsonSubgroup s.fr.B) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    (MulEquiv.subgroupCongr hJ').trans e₀
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    have h : (⟨a, ha⟩ : ↥(thompsonSubgroup s.fr.B)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    simpa using congrArg (fun z : ↥(thompsonSubgroup s.fr.B) => (z : G)) h
  · intro j hj
    have h4 : e ⟨j, hj⟩ ^ 4 = 1 := y4Zt_zmod4_prod_pow_four _
    have h : (⟨j, hj⟩ : ↥(thompsonSubgroup s.fr.B)) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h4, map_one]
    simpa using congrArg Subtype.val h

private theorem y4_C2_normalizer_J (c : Ctx4 s e) {x : G} (hx : x ∈ s.C₂) :
    x ∈ normalizer (thompsonSubgroup s.fr.B : Set G) := by
  have hxN : x ∈ normalizer (s.fr.B : Set G) :=
    c.h33.1.2.2 (Subgroup.mem_sup_right hx)
  have hmap : s.fr.B.map (MulAut.conj x : G →* G) = s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
  have hJmap := thompsonSubgroup_map (f := (MulAut.conj x : G →* G))
    (MulAut.conj x).injective s.fr.B
  rw [hmap] at hJmap
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJmap.symm

theorem y4_S'_cases (c : Ctx4 s e) {a : G} (ha : a ∈ closure ({s.fr.b₁, s.fr.b₂} : Set G)) :
    a ∈ cen s.fr.B ∨ s.fr.b₁⁻¹ * a ∈ cen s.fr.B := by
  have hb1B : s.fr.b₁ ∈ s.fr.B := y4_b1_mem_B c
  have hb2B : s.fr.b₂ ∈ s.fr.B := y4_b2_mem_B c
  have hcomm1 : ∀ {u : G}, u ∈ cen s.fr.B → Commute u s.fr.b₁ := fun {u} hu =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 s.fr.b₁ hb1B).symm
  have hcomm2 : ∀ {u : G}, u ∈ cen s.fr.B → Commute u s.fr.b₂ := fun {u} hu =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 s.fr.b₂ hb2B).symm
  have hb1inv : s.fr.b₁⁻¹ = s.fr.b₁ * s.fr.z := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, ← SFrame.z, ← pow_two, c.hRel.z_sq]
  have hzinv : s.fr.z⁻¹ = s.fr.z := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact c.hRel.z_sq
  have hb1sq : s.fr.b₁ * s.fr.b₁ = s.fr.z := by rw [← pow_two, SFrame.z]
  have hb1sq_inv : s.fr.b₁⁻¹ * s.fr.b₁⁻¹ = s.fr.z := by
    rw [← mul_inv_rev, hb1sq, hzinv]
  have hzV : s.fr.z ∈ cen s.fr.B := y4_z_mem_V c
  have hwV : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := y4_w_mem_V c
  have hz2 : Commute s.fr.z s.fr.b₂ :=
    (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (by rw [inv_mul_cancel]; exact (cen s.fr.B).one_mem)
      · refine Or.inr ?_
        have h : s.fr.b₁⁻¹ * s.fr.b₂ = (s.fr.b₁ * s.fr.b₂) * s.fr.z := by
          rw [hb1inv, mul_assoc, hz2.eq, mul_assoc]
        rw [h]
        exact (cen s.fr.B).mul_mem hwV hzV
  | one => exact Or.inl (cen s.fr.B).one_mem
  | mul x y hx hy ihx ihy =>
      rcases ihx with hxV | hxu
      · rcases ihy with hyV | hyu
        · exact Or.inl ((cen s.fr.B).mul_mem hxV hyV)
        · refine Or.inr ?_
          have hbx : s.fr.b₁⁻¹ * x = x * s.fr.b₁⁻¹ :=
            ((hcomm1 hxV).inv_right).eq.symm
          have h1 : s.fr.b₁⁻¹ * (x * y) = x * (s.fr.b₁⁻¹ * y) := by
            rw [← mul_assoc, hbx, mul_assoc]
          rw [h1]
          exact (cen s.fr.B).mul_mem hxV hyu
      · rcases ihy with hyV | hyu
        · refine Or.inr ?_
          have h1 : s.fr.b₁⁻¹ * (x * y) = (s.fr.b₁⁻¹ * x) * y := by rw [mul_assoc]
          rw [h1]
          exact (cen s.fr.B).mul_mem hxu hyV
        · refine Or.inl ?_
          set u : G := s.fr.b₁⁻¹ * x with hu
          set w : G := s.fr.b₁⁻¹ * y with hw
          have huV : u ∈ cen s.fr.B := by rw [hu]; exact hxu
          have hwV : w ∈ cen s.fr.B := by rw [hw]; exact hyu
          have hc : Commute u s.fr.b₁ := hcomm1 huV
          have hx_eq : x = s.fr.b₁ * u := by rw [hu]; group
          have hy_eq : y = s.fr.b₁ * w := by rw [hw]; group
          have hkey : (s.fr.b₁ * u) * (s.fr.b₁ * w) = s.fr.z * (u * w) := by
            calc (s.fr.b₁ * u) * (s.fr.b₁ * w)
                = s.fr.b₁ * (u * s.fr.b₁) * w := by group
              _ = s.fr.b₁ * (s.fr.b₁ * u) * w := by rw [hc.eq]
              _ = s.fr.z * (u * w) := by rw [← hb1sq]; group
          have h1 : x * y = s.fr.z * ((s.fr.b₁⁻¹ * x) * (s.fr.b₁⁻¹ * y)) := by
            calc x * y = (s.fr.b₁ * u) * (s.fr.b₁ * w) := by rw [hx_eq, hy_eq]
              _ = s.fr.z * (u * w) := hkey
              _ = s.fr.z * ((s.fr.b₁⁻¹ * x) * (s.fr.b₁⁻¹ * y)) := by rw [hu, hw]
          rw [h1]
          exact (cen s.fr.B).mul_mem hzV ((cen s.fr.B).mul_mem huV hwV)
  | inv x hx ih =>
      rcases ih with hxV | hxu
      · exact Or.inl ((cen s.fr.B).inv_mem hxV)
      · refine Or.inr ?_
        set u : G := s.fr.b₁⁻¹ * x with hu
        have huV : u ∈ cen s.fr.B := by rw [hu]; exact hxu
        have hcu : Commute u⁻¹ s.fr.b₁⁻¹ := (hcomm1 huV).inv_left.inv_right
        have hx' : x = s.fr.b₁ * u := by rw [hu]; group
        have h : s.fr.b₁⁻¹ * x⁻¹ = u⁻¹ * s.fr.z := by
          calc s.fr.b₁⁻¹ * x⁻¹
              = s.fr.b₁⁻¹ * (s.fr.b₁ * u)⁻¹ := by rw [hx']
            _ = s.fr.b₁⁻¹ * (u⁻¹ * s.fr.b₁⁻¹) := by rw [mul_inv_rev]
            _ = s.fr.b₁⁻¹ * (s.fr.b₁⁻¹ * u⁻¹) := by rw [hcu.eq]
            _ = (s.fr.b₁⁻¹ * s.fr.b₁⁻¹) * u⁻¹ := by group
            _ = s.fr.z * u⁻¹ := by rw [hb1sq_inv]
            _ = u⁻¹ * s.fr.z := y4_V_comm c hzV ((cen s.fr.B).inv_mem huV)
        rw [h]
        exact (cen s.fr.B).mul_mem ((cen s.fr.B).inv_mem huV) hzV

theorem y4_comm_b1_T (c : Ctx4 s e) {τ : G} (hτ : τ ∈ s.T) : ⁅s.fr.b₁, τ⁆ ∈ cen s.fr.B := by
  have hτN : τ ∈ normalizer (s.fr.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s3_S_le_T s)).mp
      (s3_S_normal_T s c.hS) hτ
  have hzS2 : zSeries 2 s.fr.S = closure ({s.fr.b₁, s.fr.b₂} : Set G) :=
    c.hLF.fact14.1.2.1.trans c.hLF.fact14.1.2.2.1
  have hb1z : s.fr.b₁ ∈ zSeries 2 s.fr.S := by
    rw [hzS2]; exact Subgroup.subset_closure (by simp)
  have hb'z : τ * s.fr.b₁ * τ⁻¹ ∈ zSeries 2 s.fr.S := y4_conj_zSeries 2 hτN hb1z
  have hb'cl : τ * s.fr.b₁ * τ⁻¹ ∈ closure ({s.fr.b₁, s.fr.b₂} : Set G) := by
    rwa [hzS2] at hb'z
  have hb'sq : (τ * s.fr.b₁ * τ⁻¹) ^ 2 = s.fr.z := by
    have h : (τ * s.fr.b₁ * τ⁻¹) ^ 2 = τ * s.fr.b₁ ^ 2 * τ⁻¹ := by rw [conj_pow]
    rw [h, show s.fr.b₁ ^ 2 = s.fr.z from rfl, s3_conj_z s c.hA e c.h32 (e.T_le hτ)]
  have hb'notV : τ * s.fr.b₁ * τ⁻¹ ∉ cen s.fr.B := by
    intro hmem
    have h1 : s.fr.z = 1 := by
      rw [← hb'sq]
      exact y4_V_sq c hmem
    exact y4_z_ne_one c h1
  have hb1invb' : s.fr.b₁⁻¹ * (τ * s.fr.b₁ * τ⁻¹) ∈ cen s.fr.B := by
    rcases y4_S'_cases c hb'cl with h | h
    · exact absurd h hb'notV
    · exact h
  set v : G := s.fr.b₁⁻¹ * (τ * s.fr.b₁ * τ⁻¹) with hv
  have hvV : v ∈ cen s.fr.B := by rw [hv]; exact hb1invb'
  have hvv : Commute v s.fr.b₁ :=
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp hvV).2 s.fr.b₁ (y4_b1_mem_B c)).symm
  have hw : τ * s.fr.b₁ * τ⁻¹ = s.fr.b₁ * v := by rw [hv]; group
  have hgoal : ⁅s.fr.b₁, τ⁆ = v⁻¹ := by
    rw [commutatorElement_def]
    calc s.fr.b₁ * τ * s.fr.b₁⁻¹ * τ⁻¹
        = s.fr.b₁ * (τ * s.fr.b₁ * τ⁻¹)⁻¹ := by group
      _ = s.fr.b₁ * (s.fr.b₁ * v)⁻¹ := by rw [hw]
      _ = v⁻¹ := by
            rw [mul_inv_rev, ← mul_assoc, hvv.symm.inv_right.eq]
            group
  rw [hgoal]
  exact (cen s.fr.B).inv_mem hvV

theorem y4_comm_b1_C2 (c : Ctx4 s e) {x : G} (hx : x ∈ s.C₂) : ⁅s.fr.b₁, x⁆ ∈ cen s.fr.B := by
  obtain ⟨-, -, -, -, -, -, hJ, -, hΩ, -⟩ := c.hLF.fact14.2.2.1
  have hJ' : thompsonSubgroup s.fr.B = closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ
  have hΩ' : cen s.fr.B = omega1 (thompsonSubgroup s.fr.B) := hΩ
  obtain ⟨hab, hexp⟩ := y4_J_comm_exp c
  have hb1J : s.fr.b₁ ∈ thompsonSubgroup s.fr.B := by
    rw [hJ']; exact Subgroup.subset_closure (by simp)
  have hxNJ : x ∈ normalizer (thompsonSubgroup s.fr.B : Set G) := y4_C2_normalizer_J c hx
  have hxΩ : ∀ w ∈ omega1 (thompsonSubgroup s.fr.B), x * w * x⁻¹ = w := by
    intro w hw
    rw [← hΩ'] at hw
    exact y4_C2_cent_V c hx hw
  have hx_b1 : ⁅x, s.fr.b₁⁆ ∈ cen s.fr.B := by
    have h := y4_comm_mem_omega1 hab hexp hxNJ hxΩ s.fr.b₁ hb1J
    rwa [← hΩ'] at h
  rw [show ⁅s.fr.b₁, x⁆ = ⁅x, s.fr.b₁⁆⁻¹ from (commutatorElement_inv x s.fr.b₁).symm]
  exact (cen s.fr.B).inv_mem hx_b1

theorem y4_b1_mem_Zt (c : Ctx4 s e) : s.fr.b₁ ∈ y4Zt c := by
  rw [y4_mem_Zt c]
  refine ⟨y4_S_le_T2 s (Subgroup.subset_closure (by simp)), ?_⟩
  intro y hy
  obtain ⟨τ, hτ, x, hx, rfl⟩ := f3_mem_T₂ c.toF33 y hy
  have h1 : ⁅s.fr.b₁, τ⁆ ∈ cen s.fr.B := y4_comm_b1_T c hτ
  have h2 : ⁅s.fr.b₁, x⁆ ∈ cen s.fr.B := y4_comm_b1_C2 c hx
  have h3 : τ * ⁅s.fr.b₁, x⁆ * τ⁻¹ ∈ cen s.fr.B :=
    y4_T2_normV c τ (y4_T_le_T2 s hτ) _ h2
  rw [show ⁅s.fr.b₁, τ * x⁆ = ⁅s.fr.b₁, τ⁆ * (τ * ⁅s.fr.b₁, x⁆ * τ⁻¹) by
    rw [commutatorElement_def]; group]
  exact (cen s.fr.B).mul_mem h1 h3

end CFSG.OddStandard.HigherRank.YamadaG23

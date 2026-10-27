module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Y52K (s : Setting3 G L) (k : G) : Prop where
  mem : k ∈ normIn L s.fr.B
  cube : k ^ 3 = 1
  fix : ∀ v ∈ cen s.fr.B, k * v * k⁻¹ = v → v = 1
  conj : ∀ n ∈ normIn L s.fr.B, ∃ b ∈ s.fr.B, n * k * n⁻¹ = k * b ∨ n * k * n⁻¹ = k⁻¹ * b

private lemma y52_V_ncard {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (cen s.fr.B : Set G).ncard = 4 := by
  have h := (f3_V_isE2 hH).2
  norm_num at h
  exact h

private lemma y52_V_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ cen s.fr.B, x ^ 2 = 1 := by
  intro x hx
  have h := (f3_V_isE2 hH).1.2 (⟨x, hx⟩ : ↥(cen s.fr.B)) (Subgroup.mem_top _)
  simpa using congrArg Subtype.val h

private lemma y52_conj_mem {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {k : G} (hk : Y52K s k) {u : G} (hu : u ∈ cen s.fr.B) :
    k * u * k⁻¹ ∈ cen s.fr.B := by
  obtain ⟨_, hkN⟩ := hk.mem
  obtain ⟨huB, huc⟩ := Subgroup.mem_inf.mp hu
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hkN u).mp huB, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : k⁻¹ * b * k ∈ s.fr.B := (Subgroup.mem_normalizer_iff''.mp hkN b).mp hb
  have hcomm : (k⁻¹ * b * k) * u = u * (k⁻¹ * b * k) :=
    Subgroup.mem_centralizer_iff.mp huc _ hb'
  have h1 : (k * u * k⁻¹) * b = k * (u * (k⁻¹ * b * k)) * k⁻¹ := by group
  have h2 : k * (u * (k⁻¹ * b * k)) * k⁻¹ = k * ((k⁻¹ * b * k) * u) * k⁻¹ := by
    rw [hcomm.symm]
  have h3 : k * ((k⁻¹ * b * k) * u) * k⁻¹ = b * (k * u * k⁻¹) := by group
  rw [h1, h2, h3]

private lemma y52_conj_sq (k u : G) :
    k * (k * u * k⁻¹) * k⁻¹ = k ^ 2 * u * (k ^ 2)⁻¹ := by
  rw [pow_two k, mul_inv_rev]
  group

private lemma y52_orbit_ne {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {k : G} (hk : Y52K s k) {u : G} (hu : u ∈ cen s.fr.B) (hu1 : u ≠ 1) :
    u ≠ k * u * k⁻¹ ∧ u ≠ k ^ 2 * u * (k ^ 2)⁻¹ ∧
      k * u * k⁻¹ ≠ k ^ 2 * u * (k ^ 2)⁻¹ := by
  have hk3 : k ^ 3 = 1 := hk.cube
  refine ⟨fun h => hu1 (hk.fix u hu h.symm), ?_, ?_⟩
  · intro h
    apply hu1
    have h' := congrArg (fun x => k * x * k⁻¹) h
    have hl : k * (k ^ 2 * u * (k ^ 2)⁻¹) * k⁻¹ = u := by
      calc k * (k ^ 2 * u * (k ^ 2)⁻¹) * k⁻¹ = k ^ 3 * u * (k ^ 3)⁻¹ := by group
        _ = u := by rw [hk3]; group
    rw [hl] at h'
    exact hk.fix u hu h'
  · intro h
    apply hu1
    have h' := congrArg (fun x => k⁻¹ * x * k) h
    have hl : k⁻¹ * (k * u * k⁻¹) * k = u := by group
    have hr : k⁻¹ * (k ^ 2 * u * (k ^ 2)⁻¹) * k = k * u * k⁻¹ := by group
    rw [hl, hr] at h'
    exact hk.fix u hu h'.symm

private lemma y52_orbit_ne_one {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {k : G} (hk : Y52K s k) {u : G} (hu : u ∈ cen s.fr.B) (hu1 : u ≠ 1) :
    k * u * k⁻¹ ≠ 1 ∧ k ^ 2 * u * (k ^ 2)⁻¹ ≠ 1 := by
  have hk3 : k ^ 3 = 1 := hk.cube
  refine ⟨?_, ?_⟩
  · intro h
    apply hu1
    have h' : k * u * k⁻¹ = k * 1 * k⁻¹ := by rw [h]; group
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    apply hu1
    have h' := congrArg (fun x => k * x * k⁻¹) h
    have hl : k * (k ^ 2 * u * (k ^ 2)⁻¹) * k⁻¹ = u := by
      calc k * (k ^ 2 * u * (k ^ 2)⁻¹) * k⁻¹ = k ^ 3 * u * (k ^ 3)⁻¹ := by group
        _ = u := by rw [hk3]; group
    rw [hl] at h'
    simpa using h'

private lemma y52_orbit {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {k : G} (hk : Y52K s k) {u v : G} (hu : u ∈ cen s.fr.B) (hu1 : u ≠ 1)
    (hv : v ∈ cen s.fr.B) (hv1 : v ≠ 1) :
    v = u ∨ v = k * u * k⁻¹ ∨ v = k ^ 2 * u * (k ^ 2)⁻¹ := by
  have hku : k * u * k⁻¹ ∈ cen s.fr.B := y52_conj_mem hH hk hu
  have hk2u : k ^ 2 * u * (k ^ 2)⁻¹ ∈ cen s.fr.B := by
    have h := y52_conj_mem hH hk hku
    rwa [y52_conj_sq k u] at h
  obtain ⟨hne1, hne2, hne3⟩ := y52_orbit_ne hH hk hu hu1
  obtain ⟨hku1, hk2u1⟩ := y52_orbit_ne_one hH hk hu hu1
  have hS3 : ({x | x ∈ cen s.fr.B ∧ x ≠ 1} : Set G).ncard = 3 := by
    have hsub : ({1} : Set G) ⊆ (cen s.fr.B : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (cen s.fr.B).one_mem
    have hd := Set.ncard_sdiff (s := ({1} : Set G)) (t := (cen s.fr.B : Set G)) hsub
    have hsingle : ({1} : Set G).ncard = 1 := Set.ncard_singleton 1
    have hdiffset : (cen s.fr.B : Set G) \ ({1} : Set G) =
        {x | x ∈ cen s.fr.B ∧ x ≠ 1} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      tauto
    rw [hdiffset, hsingle, y52_V_ncard hH] at hd
    omega
  have hTsub : ({u, k * u * k⁻¹, k ^ 2 * u * (k ^ 2)⁻¹} : Set G) ⊆
      {x | x ∈ cen s.fr.B ∧ x ≠ 1} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hu, hu1⟩
    · exact ⟨hku, hku1⟩
    · exact ⟨hk2u, hk2u1⟩
  have hTcard : ({u, k * u * k⁻¹, k ^ 2 * u * (k ^ 2)⁻¹} : Set G).ncard = 3 := by
    have h1 : u ∉ ({k * u * k⁻¹, k ^ 2 * u * (k ^ 2)⁻¹} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hne1 h
      · exact hne2 h
    have h2 : k * u * k⁻¹ ∉ ({k ^ 2 * u * (k ^ 2)⁻¹} : Set G) := by
      simpa using hne3
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_singleton]
  have hST : ({u, k * u * k⁻¹, k ^ 2 * u * (k ^ 2)⁻¹} : Set G) =
      {x | x ∈ cen s.fr.B ∧ x ≠ 1} :=
    Set.eq_of_subset_of_ncard_le hTsub (by rw [hS3, hTcard])
  have hvT : v ∈ ({u, k * u * k⁻¹, k ^ 2 * u * (k ^ 2)⁻¹} : Set G) := by
    rw [hST]
    exact ⟨hv, hv1⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvT
  rcases hvT with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private lemma y52_third {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {a b c : G}
    (ha : a ∈ cen s.fr.B) (hb : b ∈ cen s.fr.B) (hc : c ∈ cen s.fr.B)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : c = a * b := by
  have habV : a * b ∈ cen s.fr.B := (cen s.fr.B).mul_mem ha hb
  have hab_ne1 : a * b ≠ 1 := by
    intro h
    have hb_eq : b = a := by
      have ha2 : a * a = 1 := by rw [← pow_two]; exact y52_V_sq hH a ha
      calc b = a⁻¹ := mul_eq_one_iff_eq_inv'.mp h
        _ = a := inv_eq_of_mul_eq_one_left ha2
    exact hab hb_eq.symm
  have hab_ne_a : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (by rw [h, mul_one]))
  have hab_ne_b : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (by rw [h, one_mul]))
  have h4sub : ({1, a, b, a * b} : Set G) ⊆ (cen s.fr.B : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (cen s.fr.B).one_mem
    · exact ha
    · exact hb
    · exact habV
  have h4card : ({1, a, b, a * b} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ha1 h.symm
      · exact hb1 h.symm
      · exact hab_ne1 h.symm
    have h2 : a ∉ ({b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hab h
      · exact hab_ne_a h.symm
    have h3 : b ∉ ({a * b} : Set G) := by
      simpa using hab_ne_b.symm
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have h4eq : ({1, a, b, a * b} : Set G) = (cen s.fr.B : Set G) :=
    Set.eq_of_subset_of_ncard_le h4sub (by rw [h4card, y52_V_ncard hH])
  have hc4 : c ∈ ({1, a, b, a * b} : Set G) := by
    rw [h4eq]
    exact hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc4
  rcases hc4 with h | h | h | h
  · exact absurd h hc1
  · exact absurd h.symm hac
  · exact absurd h.symm hbc
  · exact h

private lemma y52_prod_three {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {a b c : G}
    (ha : a ∈ cen s.fr.B) (hb : b ∈ cen s.fr.B) (hc : c ∈ cen s.fr.B)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a * b * c = 1 := by
  rw [y52_third hH ha hb hc ha1 hb1 hc1 hab hac hbc]
  simpa [pow_two] using y52_V_sq hH (a * b) ((cen s.fr.B).mul_mem ha hb)

private lemma y52_mem_P_of_phi_one {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {q : G} (hq : q ∈ s.C₂) (h : f3phi s q = 1) : q ∈ f3P s := by
  have hqY : q ∈ f3Y s := f3_C₂_le_Y hH hq
  have hX0 : q ∈ f3X0 s := (f3_phi_eq_one hH q hqY).mp h
  have hmem : q ∈ s.C₂ ⊓ f3X0 s := ⟨hq, hX0⟩
  rwa [f3_C₂_inf_X0 hH] at hmem

private lemma y52_phi_cancel {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {q1 q2 : G} (hq1 : q1 ∈ s.C₂) (hq2 : q2 ∈ s.C₂)
    (h : f3phi s q1 = f3phi s q2) : q1 * q2⁻¹ ∈ f3P s := by
  have hq2inv : q2⁻¹ ∈ s.C₂ := s.C₂.inv_mem hq2
  refine y52_mem_P_of_phi_one hH (s.C₂.mul_mem hq1 hq2inv) ?_
  have hq1Y : q1 ∈ f3Y s := f3_C₂_le_Y hH hq1
  have hq2invY : q2⁻¹ ∈ f3Y s := f3_C₂_le_Y hH hq2inv
  have hmul := f3_phi_mul hH q1 hq1Y q2⁻¹ hq2invY
  have hq2inv_phi : f3phi s q2⁻¹ = (f3phi s q2)⁻¹ := by
    have hmul2 := f3_phi_mul hH q2 (f3_C₂_le_Y hH hq2) q2⁻¹ hq2invY
    rw [mul_inv_cancel] at hmul2
    have hone : f3phi s (1 : G) = 1 := by simp [f3phi]
    rw [hone] at hmul2
    exact mul_eq_one_iff_eq_inv'.mp hmul2.symm
  rw [hmul, hq2inv_phi, h, mul_inv_cancel]

theorem y52_exists_K {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k : G, Y52K s k := by
  obtain ⟨k, hk, hk3, _, hkfix, _, hkconj⟩ := f3_exists_k hH
  exact ⟨k, hk, hk3, hkfix, hkconj⟩

theorem y52_cover {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : Y52K s k) {y : G} (hy : y ∈ s.C₂) (hyP : y ∉ f3P s) :
    ∀ x ∈ s.C₂, ∃ p ∈ f3P s, x = p ∨ x = p * y ∨ x = p * (k * y * k⁻¹) ∨
      x = p * (k ^ 2 * y * (k ^ 2)⁻¹) := by
  intro x hx
  by_cases hxP : x ∈ f3P s
  · exact ⟨x, hxP, Or.inl rfl⟩
  have hkL : k ∈ L := hk.mem.1
  have hkN : k ∈ f3N s := ⟨s3_L_le_H s hH.hS hkL, hk.mem.2⟩
  have hkX : k ∈ s.X := f3_N_le_X s hkN
  have hk2X : k ^ 2 ∈ s.X := f3_N_le_X s ((f3N s).pow_mem hkN 2)
  have hkyC : k * y * k⁻¹ ∈ s.C₂ := f3_C₂_normal hH k hkX y hy
  have hk2yC : k ^ 2 * y * (k ^ 2)⁻¹ ∈ s.C₂ := f3_C₂_normal hH (k ^ 2) hk2X y hy
  have hyY : y ∈ f3Y s := f3_C₂_le_Y hH hy
  have hxY : x ∈ f3Y s := f3_C₂_le_Y hH hx
  have hyphi : f3phi s y ≠ 1 := fun h => hyP (y52_mem_P_of_phi_one hH hy h)
  have hxphi : f3phi s x ≠ 1 := fun h => hxP (y52_mem_P_of_phi_one hH hx h)
  have hphi_ky : f3phi s (k * y * k⁻¹) = k * f3phi s y * k⁻¹ :=
    f3_phi_conj s (s3_comm_t_of_mem_L s hkL) y
  have hphi_k2y : f3phi s (k ^ 2 * y * (k ^ 2)⁻¹) = k ^ 2 * f3phi s y * (k ^ 2)⁻¹ :=
    f3_phi_conj s (s3_comm_t_of_mem_L s (L.pow_mem hkL 2)) y
  rcases y52_orbit hH hk (f3_phi_mem hH y hyY) hyphi (f3_phi_mem hH x hxY) hxphi with
    h | h | h
  · exact ⟨x * y⁻¹, y52_phi_cancel hH hx hy h, Or.inr (Or.inl (by group))⟩
  · exact ⟨x * (k * y * k⁻¹)⁻¹, y52_phi_cancel hH hx hkyC (h.trans hphi_ky.symm),
      Or.inr (Or.inr (Or.inl (by group)))⟩
  · exact ⟨x * (k ^ 2 * y * (k ^ 2)⁻¹)⁻¹,
      y52_phi_cancel hH hx hk2yC (h.trans hphi_k2y.symm),
      Or.inr (Or.inr (Or.inr (by group)))⟩

theorem y52_cover_prod {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : Y52K s k) {y : G} (hy : y ∈ s.C₂) (hyP : y ∉ f3P s) :
    y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ f3P s := by
  have hkL : k ∈ L := hk.mem.1
  have hkN : k ∈ f3N s := ⟨s3_L_le_H s hH.hS hkL, hk.mem.2⟩
  have hkX : k ∈ s.X := f3_N_le_X s hkN
  have hk2X : k ^ 2 ∈ s.X := f3_N_le_X s ((f3N s).pow_mem hkN 2)
  have hkyC : k * y * k⁻¹ ∈ s.C₂ := f3_C₂_normal hH k hkX y hy
  have hk2yC : k ^ 2 * y * (k ^ 2)⁻¹ ∈ s.C₂ := f3_C₂_normal hH (k ^ 2) hk2X y hy
  have hprodC : y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ s.C₂ :=
    s.C₂.mul_mem (s.C₂.mul_mem hy hkyC) hk2yC
  refine y52_mem_P_of_phi_one hH hprodC ?_
  have hyY : y ∈ f3Y s := f3_C₂_le_Y hH hy
  have hkyY : k * y * k⁻¹ ∈ f3Y s := f3_C₂_le_Y hH hkyC
  have hk2yY : k ^ 2 * y * (k ^ 2)⁻¹ ∈ f3Y s := f3_C₂_le_Y hH hk2yC
  have hmul1 := f3_phi_mul hH y hyY (k * y * k⁻¹) hkyY
  have hmul2 := f3_phi_mul hH (y * (k * y * k⁻¹)) (f3_C₂_le_Y hH (s.C₂.mul_mem hy hkyC))
    (k ^ 2 * y * (k ^ 2)⁻¹) hk2yY
  rw [hmul2, hmul1, f3_phi_conj s (s3_comm_t_of_mem_L s hkL) y,
    f3_phi_conj s (s3_comm_t_of_mem_L s (L.pow_mem hkL 2)) y]
  have haV : f3phi s y ∈ cen s.fr.B := f3_phi_mem hH y hyY
  have hbV : k * f3phi s y * k⁻¹ ∈ cen s.fr.B := y52_conj_mem hH hk haV
  have hcV : k ^ 2 * f3phi s y * (k ^ 2)⁻¹ ∈ cen s.fr.B := by
    have h := y52_conj_mem hH hk hbV
    rwa [y52_conj_sq k (f3phi s y)] at h
  have ha1 : f3phi s y ≠ 1 := fun h => hyP (y52_mem_P_of_phi_one hH hy h)
  obtain ⟨hb1, hc1⟩ := y52_orbit_ne_one hH hk haV ha1
  obtain ⟨hab, hac, hbc⟩ := y52_orbit_ne hH hk haV ha1
  exact y52_prod_three hH haV hbV hcV ha1 hb1 hc1 hab hac hbc

theorem y52_a_swap {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : Y52K s k) {y : G} (hy : y ∈ s.C₂) (hφ : f3phi s y = s.fr.z) :
    y5a s * (k * y * k⁻¹) * (y5a s)⁻¹ * (k ^ 2 * y * (k ^ 2)⁻¹)⁻¹ ∈ f3P s ∧
      y5a s * (k ^ 2 * y * (k ^ 2)⁻¹) * (y5a s)⁻¹ * (k * y * k⁻¹)⁻¹ ∈ f3P s := by
  obtain ⟨_, _, hzV, _, hz1, _, _, hzsq, _, _⟩ := f3_V_elems hH
  have hkL : k ∈ L := hk.mem.1
  have hkN : k ∈ f3N s := ⟨s3_L_le_H s hH.hS hkL, hk.mem.2⟩
  have hkX : k ∈ s.X := f3_N_le_X s hkN
  have hk2X : k ^ 2 ∈ s.X := f3_N_le_X s ((f3N s).pow_mem hkN 2)
  have hkyC : k * y * k⁻¹ ∈ s.C₂ := f3_C₂_normal hH k hkX y hy
  have hk2yC : k ^ 2 * y * (k ^ 2)⁻¹ ∈ s.C₂ := f3_C₂_normal hH (k ^ 2) hk2X y hy
  have haL : y5a s ∈ L := s3_S_le_L s (y5a_mem_S s)
  have haH : y5a s ∈ s.H := s3_L_le_H s hH.hS haL
  have haN : y5a s ∈ f3N s := ⟨haH, (y5a_mem_normB hH).2⟩
  have haX : y5a s ∈ s.X := f3_N_le_X s haN
  have hcomm_a : y5a s * s.t = s.t * y5a s := s3_comm_t_of_mem_L s haL
  have hk_comm : k * s.t = s.t * k := s3_comm_t_of_mem_L s hkL
  have hk2_comm : k ^ 2 * s.t = s.t * k ^ 2 := s3_comm_t_of_mem_L s (L.pow_mem hkL 2)
  have hz1V : k * s.fr.z * k⁻¹ ∈ cen s.fr.B := y52_conj_mem hH hk hzV
  have hz2V : k ^ 2 * s.fr.z * (k ^ 2)⁻¹ ∈ cen s.fr.B := by
    have h := y52_conj_mem hH hk hz1V
    rwa [y52_conj_sq k s.fr.z] at h
  obtain ⟨hz1ne1, hz2ne1⟩ := y52_orbit_ne_one hH hk hzV hz1
  obtain ⟨hz_ne_z1, hz_ne_z2, hz1_ne_z2⟩ := y52_orbit_ne hH hk hzV hz1
  have hconjV1 : y5a s * (k * s.fr.z * k⁻¹) * (y5a s)⁻¹ = s.fr.z * (k * s.fr.z * k⁻¹) :=
    y5a_conj_V hH _ hz1V hz1ne1 hz_ne_z1.symm
  have hconjV2 : y5a s * (k ^ 2 * s.fr.z * (k ^ 2)⁻¹) * (y5a s)⁻¹ =
      s.fr.z * (k ^ 2 * s.fr.z * (k ^ 2)⁻¹) :=
    y5a_conj_V hH _ hz2V hz2ne1 hz_ne_z2.symm
  have hprod := y52_prod_three hH hzV hz1V hz2V hz1 hz1ne1 hz2ne1 hz_ne_z1 hz_ne_z2 hz1_ne_z2
  have hz_eq : s.fr.z * (k * s.fr.z * k⁻¹) = k ^ 2 * s.fr.z * (k ^ 2)⁻¹ := by
    have hzinv : s.fr.z⁻¹ = s.fr.z :=
      inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hzsq)
    calc s.fr.z * (k * s.fr.z * k⁻¹)
        = (s.fr.z * (k * s.fr.z * k⁻¹) * (k ^ 2 * s.fr.z * (k ^ 2)⁻¹)) *
            (k ^ 2 * s.fr.z * (k ^ 2)⁻¹)⁻¹ := by group
      _ = 1 * (k ^ 2 * s.fr.z * (k ^ 2)⁻¹)⁻¹ := by rw [hprod]
      _ = (k ^ 2 * s.fr.z * (k ^ 2)⁻¹)⁻¹ := one_mul _
      _ = k ^ 2 * s.fr.z * (k ^ 2)⁻¹ := by
          rw [show (k ^ 2 * s.fr.z * (k ^ 2)⁻¹)⁻¹ = k ^ 2 * s.fr.z⁻¹ * (k ^ 2)⁻¹ by group,
            hzinv]
  have hz_eq2 : s.fr.z * (k ^ 2 * s.fr.z * (k ^ 2)⁻¹) = k * s.fr.z * k⁻¹ := by
    rw [← hz_eq, ← mul_assoc, ← pow_two, hzsq, one_mul]
  have hphi_lhs1 : f3phi s (y5a s * (k * y * k⁻¹) * (y5a s)⁻¹) =
      k ^ 2 * s.fr.z * (k ^ 2)⁻¹ := by
    rw [f3_phi_conj s hcomm_a (k * y * k⁻¹), f3_phi_conj s hk_comm y, hφ]
    exact hconjV1.trans hz_eq
  have hphi_rhs1 : f3phi s (k ^ 2 * y * (k ^ 2)⁻¹) = k ^ 2 * s.fr.z * (k ^ 2)⁻¹ := by
    rw [f3_phi_conj s hk2_comm y, hφ]
  have hphi_lhs2 : f3phi s (y5a s * (k ^ 2 * y * (k ^ 2)⁻¹) * (y5a s)⁻¹) =
      k * s.fr.z * k⁻¹ := by
    rw [f3_phi_conj s hcomm_a (k ^ 2 * y * (k ^ 2)⁻¹), f3_phi_conj s hk2_comm y, hφ]
    exact hconjV2.trans hz_eq2
  have hphi_rhs2 : f3phi s (k * y * k⁻¹) = k * s.fr.z * k⁻¹ := by
    rw [f3_phi_conj s hk_comm y, hφ]
  have hq1C : y5a s * (k * y * k⁻¹) * (y5a s)⁻¹ ∈ s.C₂ :=
    f3_C₂_normal hH (y5a s) haX (k * y * k⁻¹) hkyC
  have hq2C : y5a s * (k ^ 2 * y * (k ^ 2)⁻¹) * (y5a s)⁻¹ ∈ s.C₂ :=
    f3_C₂_normal hH (y5a s) haX (k ^ 2 * y * (k ^ 2)⁻¹) hk2yC
  exact ⟨y52_phi_cancel hH hq1C hk2yC (hphi_lhs1.trans hphi_rhs1.symm),
    y52_phi_cancel hH hq2C hkyC (hphi_lhs2.trans hphi_rhs2.symm)⟩

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f3_four_mul {G : Type} [Group G] {z t x y : G} (hzz : z * z = 1)
    (htt : t * t = 1) (hzt : t * z = z * t)
    (hx : x = 1 ∨ x = z ∨ x = t ∨ x = z * t)
    (hy : y = 1 ∨ y = z ∨ y = t ∨ y = z * t) :
    x * y = 1 ∨ x * y = z ∨ x * y = t ∨ x * y = z * t := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  · left; rw [one_mul]
  · right; left; rw [one_mul]
  · right; right; left; rw [one_mul]
  · right; right; right; rw [one_mul]
  · right; left; rw [mul_one]
  · left; rw [hzz]
  · right; right; right; rfl
  · right; right; left; rw [← mul_assoc, hzz, one_mul]
  · right; right; left; rw [mul_one]
  · right; right; right; rw [hzt]
  · left; rw [htt]
  · right; left; rw [← mul_assoc, hzt, mul_assoc, htt, mul_one]
  · right; right; right; rw [mul_one]
  · right; right; left; rw [mul_assoc, hzt, ← mul_assoc, hzz, one_mul]
  · right; left; rw [mul_assoc, htt, mul_one]
  · left
    calc (z * t) * (z * t) = z * ((t * z) * t) := by group
      _ = z * ((z * t) * t) := by rw [hzt]
      _ = z * (z * (t * t)) := by group
      _ = 1 := by rw [htt, mul_one, hzz]

private theorem f3_four_inv {G : Type} [Group G] {z t x : G} (hzz : z * z = 1)
    (htt : t * t = 1) (hzt : t * z = z * t)
    (hx : x = 1 ∨ x = z ∨ x = t ∨ x = z * t) :
    x⁻¹ = 1 ∨ x⁻¹ = z ∨ x⁻¹ = t ∨ x⁻¹ = z * t := by
  rcases hx with rfl | rfl | rfl | rfl
  · left; rw [inv_one]
  · right; left; rw [inv_eq_of_mul_eq_one_right hzz]
  · right; right; left; rw [inv_eq_of_mul_eq_one_right htt]
  · right; right; right
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right htt, hzt]

private theorem f3_mem_closure_pair {G : Type} [Group G] {w z v : G} (hw : w ^ 2 = 1)
    (hz : z ^ 2 = 1) (hc : w * z = z * w)
    (hv : v ∈ Subgroup.closure ({w, z} : Set G)) :
    v = 1 ∨ v = z ∨ v = w ∨ v = z * w := by
  have hww : w * w = 1 := by rwa [pow_two] at hw
  have hzz : z * z = 1 := by rwa [pow_two] at hz
  refine Subgroup.closure_induction (p := fun v _ => v = 1 ∨ v = z ∨ v = w ∨ v = z * w)
    ?_ ?_ ?_ ?_ hv
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · intro x y _ _ hx hy
    exact f3_four_mul hzz hww hc hx hy
  · intro x _ hx
    exact f3_four_inv hzz hww hc hx

private theorem f3_isCyclic_closure_pair_of_mem {G : Type} [Group G] {z a : G}
    (ha : a ∈ ({1, z} : Set G)) :
    IsCyclic ↥(Subgroup.closure ({a, z} : Set G)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  have hle : Subgroup.closure ({a, z} : Set G) ≤ Subgroup.zpowers z := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rcases ha with h1 | hz
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hz]; exact Subgroup.mem_zpowers _
    · exact Subgroup.mem_zpowers _
  exact Subgroup.isCyclic_of_le hle

private theorem f3_w0_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.fr.b₁ * s.fr.b₂) ^ 2 = 1 := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hc : Commute s.fr.b₁ s.fr.b₂ := commutatorElement_eq_one_iff_commute.mp hsrel.b1b2
  calc (s.fr.b₁ * s.fr.b₂) ^ 2 = s.fr.b₁ ^ 2 * s.fr.b₂ ^ 2 := hc.mul_pow 2
    _ = s.fr.z * s.fr.z := by rw [show s.fr.b₁ ^ 2 = s.fr.z from rfl, hsrel.b2_sq]
    _ = 1 := by rw [← pow_two, hsrel.z_sq]

private theorem f3_w0_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.fr.b₁ * s.fr.b₂) * s.fr.z = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  have hcenS : cen s.fr.S = s.fr.Z := hH.hLF.fact14.1.1
  have hzcenS : s.fr.z ∈ cen s.fr.S := hcenS.symm ▸ Subgroup.mem_zpowers s.fr.z
  have hzc : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) := (Subgroup.mem_inf.mp hzcenS).2
  have hzb1 : s.fr.b₁ * s.fr.z = s.fr.z * s.fr.b₁ :=
    Subgroup.mem_centralizer_iff.mp hzc s.fr.b₁ (Subgroup.subset_closure (by simp))
  have hzb2 : s.fr.b₂ * s.fr.z = s.fr.z * s.fr.b₂ :=
    Subgroup.mem_centralizer_iff.mp hzc s.fr.b₂ (Subgroup.subset_closure (by simp))
  calc s.fr.b₁ * s.fr.b₂ * s.fr.z = s.fr.b₁ * (s.fr.b₂ * s.fr.z) := by group
    _ = s.fr.b₁ * (s.fr.z * s.fr.b₂) := by rw [hzb2]
    _ = (s.fr.b₁ * s.fr.z) * s.fr.b₂ := by group
    _ = (s.fr.z * s.fr.b₁) * s.fr.b₂ := by rw [hzb1]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by group

private theorem f3_conj_mem_cen {G : Type} [Group G] {B : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) (hv : v ∈ cen B) :
    g * v * g⁻¹ ∈ cen B := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (B : Set G) := Subgroup.inv_mem _ hg
  rcases Subgroup.mem_inf.mp hv with ⟨hvB, hvC⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · simpa using (Subgroup.mem_normalizer_iff''.mp hginv v).mp hvB
  · rw [Subgroup.mem_centralizer_iff] at hvC ⊢
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B := (Subgroup.mem_normalizer_iff''.mp hg b).mp hb
    calc b * (g * v * g⁻¹) = g * ((g⁻¹ * b * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * b * g)) * g⁻¹ := by rw [hvC (g⁻¹ * b * g) hb']
      _ = (g * v * g⁻¹) * b := by group

theorem f3_zL_eq_bot {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : zL L = ⊥ := by
  have hle : zL L ≤ Subgroup.zpowers s.t := by
    intro x hx
    obtain ⟨y, hyc, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (y : G) ∈ centIn s.H L := by
      refine Subgroup.mem_inf.mpr ⟨s3_L_le_H s hH.hS y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨z, hz⟩)
    have hsup : (y : G) ∈ Subgroup.zpowers s.t ⊔ s.oddH := hH.h31.2.1 ▸ hmem
    rwa [f3_oddH_eq_bot hH.hS s, sup_bot_eq] at hsup
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle hx)
  have hxL : x ∈ L := by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  rw [← hk] at hxL
  rw [Subgroup.mem_bot]
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · have h2' : k % ((2 : ℕ) : ℤ) = 0 := h2
    rw [← hk, ← zpow_mod_orderOf s.t k, s.t_order, h2']; simp
  · exfalso
    have h2' : k % ((2 : ℕ) : ℤ) = 1 := h2
    apply s3_t_not_mem_L s hH.h31
    have htk : s.t ^ k = s.t := by rw [← zpow_mod_orderOf s.t k, s.t_order, h2']; simp
    rwa [htk] at hxL

theorem f3_centIn_H_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn s.H L = zpowers s.t := by
  rw [hH.h31.2.1, f3_oddH_eq_bot hH.hS s, sup_bot_eq]

theorem f3_B_le_L (s : Setting3 G L) : s.fr.B ≤ L :=
  (s3_B_le_S s).trans (s3_S_le_L s)

theorem f3_P_le_H (s : Setting3 G L) : f3P s ≤ s.H := by
  apply sup_le
  · intro b hb
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    exact s3_comm_t_of_mem_L s (f3_B_le_L s hb)
  · rw [Subgroup.zpowers_le, Setting3.H, Subgroup.mem_centralizer_singleton_iff]

theorem f3_P_le_cent_V (s : Setting3 G L) : f3P s ≤ centralizer (cen s.fr.B : Set G) := by
  apply sup_le
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 b hb).symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    exact s3_comm_t_of_mem_L s (f3_B_le_L s (s3_cenB_le_B s hv))

theorem f3_V_elems {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ w : G, w ∈ cen s.fr.B ∧ s.fr.z ∈ cen s.fr.B ∧ w ≠ 1 ∧ s.fr.z ≠ 1 ∧ w ≠ s.fr.z ∧
      w ^ 2 = 1 ∧ s.fr.z ^ 2 = 1 ∧ w * s.fr.z = s.fr.z * w ∧
      ∀ v ∈ cen s.fr.B, v = 1 ∨ v = s.fr.z ∨ v = w ∨ v = s.fr.z * w := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hcen : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  have hw0V : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have hzV : s.fr.z ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have hzsq : s.fr.z ^ 2 = 1 := hsrel.z_sq
  have hw0sq : (s.fr.b₁ * s.fr.b₂) ^ 2 = 1 := f3_w0_sq hH
  have hw0z : (s.fr.b₁ * s.fr.b₂) * s.fr.z = s.fr.z * (s.fr.b₁ * s.fr.b₂) := f3_w0_comm hH
  have hzne1 : s.fr.z ≠ 1 := by
    intro h
    have := s3_z_order s hA
    rw [h, orderOf_one] at this
    norm_num at this
  have hcyc : ¬ IsCyclic ↥(cen s.fr.B) := hH.hLF.fact14.2.2.1.2.2.2.1
  have hw0ne1 : s.fr.b₁ * s.fr.b₂ ≠ 1 := by
    intro h
    apply hcyc
    rw [hcen]
    exact f3_isCyclic_closure_pair_of_mem (z := s.fr.z) (a := s.fr.b₁ * s.fr.b₂) (by
      rw [h]; simp)
  have hw0nez : s.fr.b₁ * s.fr.b₂ ≠ s.fr.z := by
    intro h
    apply hcyc
    rw [hcen]
    exact f3_isCyclic_closure_pair_of_mem (z := s.fr.z) (a := s.fr.b₁ * s.fr.b₂) (by
      rw [h]; simp)
  have henum : ∀ v ∈ cen s.fr.B, v = 1 ∨ v = s.fr.z ∨ v = s.fr.b₁ * s.fr.b₂ ∨
      v = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
    intro v hv
    rw [hcen] at hv
    exact f3_mem_closure_pair (w := s.fr.b₁ * s.fr.b₂) (z := s.fr.z) hw0sq hzsq hw0z hv
  exact ⟨s.fr.b₁ * s.fr.b₂, hw0V, hzV, hw0ne1, hzne1, hw0nez, hw0sq, hzsq, hw0z, henum⟩

theorem f3_V_isE2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsE 2 ↥(cen s.fr.B) := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hcenB : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  have hElV : IsElemAbelian 2 (cen s.fr.B) := by
    rw [hcenB]
    refine IsElemAbelian.closure_of_commute (s := ({s.fr.b₁ * s.fr.b₂, s.fr.z} : Set G)) ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact f3_w0_comm hH
      · exact (f3_w0_comm hH).symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact f3_w0_sq hH
      · exact hsrel.z_sq
  have hEl : IsElemAbelian 2 (⊤ : Subgroup ↥(cen s.fr.B)) := by
    have h := IsElemAbelian.subgroupOf hElV (cen s.fr.B)
    rwa [Subgroup.subgroupOf_self] at h
  obtain ⟨w, hwV, hzV, hwne1, hzne1, hwnez, hwsq, hzsq, hwz, henum⟩ := f3_V_elems hH
  refine ⟨hEl, ?_⟩
  show (cen s.fr.B : Set G).ncard = 4
  have hset : (cen s.fr.B : Set G) = ({1, s.fr.z, w, s.fr.z * w} : Set G) := by
    ext v
    constructor
    · intro hv
      rcases henum v hv with rfl | rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact hzV
      · exact hwV
      · exact (cen s.fr.B).mul_mem hzV hwV
  have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hzsq
  have hzw_ne_one : s.fr.z * w ≠ 1 := by
    intro h
    apply hwnez
    calc w = s.fr.z * (s.fr.z * w) := by rw [← mul_assoc, hzz, one_mul]
      _ = s.fr.z * 1 := by rw [h]
      _ = s.fr.z := mul_one _
  have hz_ne_zw : s.fr.z ≠ s.fr.z * w := by
    intro h
    apply hwne1
    calc w = s.fr.z⁻¹ * (s.fr.z * w) := by group
      _ = s.fr.z⁻¹ * s.fr.z := by rw [← h]
      _ = 1 := inv_mul_cancel s.fr.z
  have hw_ne_zw : w ≠ s.fr.z * w := by
    intro h
    apply hzne1
    calc s.fr.z = (s.fr.z * w) * w⁻¹ := by group
      _ = w * w⁻¹ := by rw [← h]
      _ = 1 := by group
  have h1 : (1 : G) ∉ ({s.fr.z, w, s.fr.z * w} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzne1.symm, hwne1.symm, hzw_ne_one.symm⟩
  have h2 : s.fr.z ∉ ({w, s.fr.z * w} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hwnez.symm, hz_ne_zw⟩
  have h3 : w ∉ ({s.fr.z * w} : Set G) := by
    simpa only [Set.mem_singleton_iff] using hw_ne_zw
  rw [hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

theorem f3_centIn_L_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn L (cen s.fr.B) = s.fr.B := by
  have h3f : centIn L (cen s.fr.B) = zL L ⊔ s.fr.B := hH.hLF.fact18.2.1.2.2.2.2.2
  rw [h3f, f3_zL_eq_bot hH, bot_sup_eq]

theorem f3_mem_P {s : Setting3 G L} (p : G) (hp : p ∈ f3P s) :
    p ∈ s.fr.B ∨ ∃ b ∈ s.fr.B, p = b * s.t := by
  have htt : s.t * s.t = 1 := by rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  rw [show f3P s = Subgroup.closure ((s.fr.B : Set G) ∪ (Subgroup.zpowers s.t : Set G)) from
    Subgroup.sup_eq_closure _ _] at hp
  refine Subgroup.closure_induction (p := fun p _ => p ∈ s.fr.B ∨ ∃ b ∈ s.fr.B, p = b * s.t)
    ?_ ?_ ?_ ?_ hp
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rcases Int.emod_two_eq_zero_or_one n with h2 | h2
      · left
        have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
        rw [show s.t ^ n = 1 by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp]
        exact s.fr.B.one_mem
      · right
        have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
        exact ⟨1, s.fr.B.one_mem, by
          rw [show s.t ^ n = s.t by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp, one_mul]⟩
  · exact Or.inl s.fr.B.one_mem
  · intro x y _ _ hx hy
    rcases hx with hx | ⟨b, hb, rfl⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · exact Or.inl (s.fr.B.mul_mem hx hy)
      · exact Or.inr ⟨x * c, s.fr.B.mul_mem hx hc, by group⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · refine Or.inr ⟨b * y, s.fr.B.mul_mem hb hy, ?_⟩
        calc b * s.t * y = b * (s.t * y) := by group
          _ = b * (y * s.t) := by rw [← s3_comm_t_of_mem_L s (f3_B_le_L s hy)]
          _ = b * y * s.t := by group
      · refine Or.inl ?_
        rw [show b * s.t * (c * s.t) = b * c by
          calc b * s.t * (c * s.t) = b * (s.t * c) * s.t := by group
            _ = b * (c * s.t) * s.t := by rw [← s3_comm_t_of_mem_L s (f3_B_le_L s hc)]
            _ = b * c * (s.t * s.t) := by group
            _ = b * c := by rw [htt, mul_one]]
        exact s.fr.B.mul_mem hb hc
  · intro x _ hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · exact Or.inl (s.fr.B.inv_mem hx)
    · refine Or.inr ⟨b⁻¹, s.fr.B.inv_mem hb, ?_⟩
      have htb : s.t * b⁻¹ = b⁻¹ * s.t :=
        (s3_comm_t_of_mem_L s (f3_B_le_L s (s.fr.B.inv_mem hb))).symm
      calc (b * s.t)⁻¹ = s.t⁻¹ * b⁻¹ := mul_inv_rev b s.t
        _ = s.t * b⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
        _ = b⁻¹ * s.t := htb

theorem f3_P_inf_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3P s ⊓ L = s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases f3_mem_P x hx.1 with hxB | ⟨b, hb, rfl⟩
    · exact hxB
    · exfalso
      apply s3_t_not_mem_L s hH.h31
      have : s.t = b⁻¹ * (b * s.t) := by group
      rw [this]
      exact L.mul_mem (L.inv_mem (f3_B_le_L s hb)) hx.2
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx, f3_B_le_L s hx⟩

theorem f3_mem_P_not_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {p : G}
    (hp : p ∈ f3P s) (hpL : p ∉ L) : ∃ b ∈ s.fr.B, p = b * s.t := by
  rcases f3_mem_P p hp with h | h
  · exact absurd (f3_B_le_L s h) hpL
  · exact h

theorem f3_P_isPGroup (s : Setting3 G L) : IsPGroup 2 ↥(f3P s) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have ht : IsPGroup 2 ↥(Subgroup.zpowers s.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.t_order]; norm_num)
  have hN : s.fr.B ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hc : Commute b s.t := s3_comm_t_of_mem_L s (f3_B_le_L s hb)
    rw [(hc.zpow_right n).eq]
    group
  exact IsPGroup.to_sup_of_normal_right' hB ht hN

theorem f3_exists_tau {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ τ ∈ s.T, τ ∈ s.fr.S ∧ τ ∈ normalizer (s.fr.B : Set G) ∧
      ∀ w ∈ cen s.fr.B, w ≠ 1 → w ≠ s.fr.z → τ * w * τ⁻¹ = s.fr.z * w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : IsMaximalIn s.fr.S s.fr.B := hH.hLF.fact14.2.2.1.2.2.1
  obtain ⟨τ, hτS, hτBmem⟩ := SetLike.exists_of_lt hmax.1
  have hBS : s.fr.B ≤ s.fr.S := s3_B_le_S s
  have hcoatom : IsCoatom (s.fr.B.subgroupOf s.fr.S) := by
    rw [isCoatom_iff_ge_of_le]
    refine ⟨?_, ?_⟩
    · intro htop
      apply hmax.1.2
      intro x hx
      have : (⟨x, hx⟩ : ↥s.fr.S) ∈ s.fr.B.subgroupOf s.fr.S := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    · intro K hKne hBK
      by_contra hKB
      obtain ⟨k, hkK, hkB⟩ := SetLike.not_le_iff_exists.mp hKB
      let M : Subgroup G := K.map (Subgroup.subtype s.fr.S)
      have hMS : M ≤ s.fr.S := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact y.2
      have hBM : s.fr.B ≤ M := by
        intro b hb
        exact Subgroup.mem_map.mpr ⟨⟨b, hBS hb⟩, hBK (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
      have hkg : ((k : ↥s.fr.S) : G) ∈ M := Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
      have hkgB : ((k : ↥s.fr.S) : G) ∉ s.fr.B :=
        fun h => hkB (Subgroup.mem_subgroupOf.mpr h)
      have hlt : s.fr.B < M := lt_of_le_of_ne hBM (fun heq => hkgB (heq ▸ hkg))
      have hMtop : M = s.fr.S := hmax.2 M hlt hMS
      have hKM : M.subgroupOf s.fr.S = K := by
        rw [← Subgroup.comap_subtype]
        exact K.comap_map_eq_self_of_injective (Subtype.coe_injective)
      exact hKne (by rw [← hKM, hMtop, Subgroup.subgroupOf_self])
  haveI : Group.IsNilpotent ↥(s.fr.S) := (s3_isPGroup_S s).isNilpotent
  have hidx : (s.fr.B.subgroupOf s.fr.S).index = 2 :=
    (IsPGroup.isCoatom_iff_index_eq_prime (p := 2) (s3_isPGroup_S s)).mp hcoatom
  have hnormal : (s.fr.B.subgroupOf s.fr.S).Normal := Subgroup.normal_of_index_eq_two hidx
  have hBnorms : s.fr.S ≤ Subgroup.normalizer (s.fr.B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mp hnormal
  have hτNormB : τ ∈ Subgroup.normalizer (s.fr.B : Set G) := hBnorms hτS
  have hτz : τ * s.fr.z * τ⁻¹ = s.fr.z := by
    have hcenS : cen s.fr.S = s.fr.Z := hH.hLF.fact14.1.1
    have hzcenS : s.fr.z ∈ cen s.fr.S := hcenS.symm ▸ Subgroup.mem_zpowers s.fr.z
    have hcomm : τ * s.fr.z = s.fr.z * τ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzcenS).2 τ hτS
    rw [hcomm]; group
  obtain ⟨w0, hw0V, hzV, hw0ne1, hzne1, hw0nez, hw0sq, hzsq, hw0z, henum⟩ := f3_V_elems hH
  have hτw0 : τ * w0 * τ⁻¹ = s.fr.z * w0 := by
    have hmem : τ * w0 * τ⁻¹ ∈ cen s.fr.B := f3_conj_mem_cen hτNormB hw0V
    rcases henum (τ * w0 * τ⁻¹) hmem with h1 | hz | hw | hzw
    · exfalso
      have : w0 = 1 := by
        calc w0 = τ⁻¹ * (τ * w0 * τ⁻¹) * τ := by group
          _ = 1 := by rw [h1]; group
      exact hw0ne1 this
    · exfalso
      have hτz_inv : τ⁻¹ * s.fr.z * τ = s.fr.z := by
        have h1' : τ⁻¹ * (τ * s.fr.z * τ⁻¹) * τ = s.fr.z := by group
        rwa [hτz] at h1'
      have : w0 = s.fr.z := by
        calc w0 = τ⁻¹ * (τ * w0 * τ⁻¹) * τ := by group
          _ = τ⁻¹ * s.fr.z * τ := by rw [hz]
          _ = s.fr.z := hτz_inv
      exact hw0nez this
    · exfalso
      have hτz' : τ * s.fr.z = s.fr.z * τ := by
        calc τ * s.fr.z = (τ * s.fr.z * τ⁻¹) * τ := by group
          _ = s.fr.z * τ := by rw [hτz]
      have hτw' : τ * w0 = w0 * τ := by
        calc τ * w0 = (τ * w0 * τ⁻¹) * τ := by group
          _ = w0 * τ := by rw [hw]
      have hτcen : τ ∈ Subgroup.centralizer (cen s.fr.B : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases henum y hy with rfl | rfl | rfl | rfl
        · rw [one_mul, mul_one]
        · exact hτz'.symm
        · exact hτw'.symm
        · calc (s.fr.z * w0) * τ = s.fr.z * (w0 * τ) := by group
            _ = s.fr.z * (τ * w0) := by rw [hτw'.symm]
            _ = (s.fr.z * τ) * w0 := by group
            _ = (τ * s.fr.z) * w0 := by rw [hτz'.symm]
            _ = τ * (s.fr.z * w0) := by group
      have hτB : τ ∈ s.fr.B := by
        have hmem' : τ ∈ centIn L (cen s.fr.B) :=
          Subgroup.mem_inf.mpr ⟨s3_S_le_L s hτS, hτcen⟩
        rwa [f3_centIn_L_V hH] at hmem'
      exact hτBmem hτB
    · exact hzw
  refine ⟨τ, s3_S_le_T s hτS, hτS, hτNormB, ?_⟩
  intro v hv hv1 hvz
  rcases henum v hv with h1 | hz | hw | hzw
  · exact absurd h1 hv1
  · exact absurd hz hvz
  · rw [hw]; exact hτw0
  · rw [hzw]
    calc τ * (s.fr.z * w0) * τ⁻¹ = (τ * s.fr.z * τ⁻¹) * (τ * w0 * τ⁻¹) := by group
      _ = s.fr.z * (s.fr.z * w0) := by rw [hτz, hτw0]

end CFSG.OddStandard.HigherRank.YamadaG23

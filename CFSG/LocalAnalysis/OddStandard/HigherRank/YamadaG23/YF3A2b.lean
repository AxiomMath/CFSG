module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f3_sq_mul_eq_one {G : Type} [Group G] {h b z : G}
    (hbz : b * h = z * h * b) (hzsq : z ^ 2 = 1) (hb2 : b ^ 2 = z) (hh2 : h ^ 2 = 1)
    (hzh : h * z = z * h) : (h * b) ^ 2 = 1 := by
  rw [pow_two]
  calc h * b * (h * b)
      = h * (b * h) * b := by group
    _ = h * (z * h * b) * b := by rw [hbz]
    _ = h * z * h * (b * b) := by group
    _ = h * z * h * z := by rw [← pow_two, hb2]
    _ = z * h * h * z := by rw [hzh]
    _ = z * (h * h) * z := by group
    _ = 1 := by rw [← pow_two, hh2, mul_one, ← pow_two, hzsq]

theorem f3_closure_invols_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    closure {b : G | b ∈ s.fr.B ∧ b ^ 2 = 1} = s.fr.B := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  let Sg : Set G := {s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀}
  have hSg : Sg = ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G) := rfl
  have hB : s.fr.B = closure Sg := by
    rw [SFrame.B]
    rw [show centIn s.fr.S (closure {s.fr.b₁ * s.fr.b₂}) =
        centEl s.fr.S (s.fr.b₁ * s.fr.b₂) by
      rw [centIn, centEl, Subgroup.centralizer_closure]]
    rw [hSg]
    exact hH.hLF.fact12.2.2.2.1
  have hzcen : s.fr.z ∈ cen s.fr.S := by
    rw [s3_cen_S s hA]
    exact Subgroup.mem_zpowers s.fr.z
  have hzcentral : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) :=
    (Subgroup.mem_inf.mp hzcen).2
  have hzh : s.fr.h₀ * s.fr.z = s.fr.z * s.fr.h₀ :=
    Subgroup.mem_centralizer_iff.mp hzcentral s.fr.h₀ (Subgroup.subset_closure (by simp))
  have hc12 : Commute s.fr.a₁ s.fr.a₂ :=
    commutatorElement_eq_one_iff_commute.mp hsrel.a1a2
  have hsq_a1a2 : (s.fr.a₁ * s.fr.a₂) ^ 2 = 1 := by
    rw [hc12.mul_pow 2, hsrel.a1_sq, hsrel.a2_sq, ← pow_two, hsrel.z_sq]
  have hbz1 : s.fr.b₁ * s.fr.h₀ = s.fr.z * s.fr.h₀ * s.fr.b₁ := by
    have h1 : s.fr.b₁ * s.fr.h₀ * s.fr.b₁⁻¹ * s.fr.h₀⁻¹ = s.fr.z := by
      have := hsrel.b1h
      rwa [commutatorElement_def] at this
    calc s.fr.b₁ * s.fr.h₀
        = (s.fr.b₁ * s.fr.h₀ * s.fr.b₁⁻¹ * s.fr.h₀⁻¹) * (s.fr.h₀ * s.fr.b₁) := by group
      _ = s.fr.z * (s.fr.h₀ * s.fr.b₁) := by rw [h1]
      _ = s.fr.z * s.fr.h₀ * s.fr.b₁ := by group
  have hbz2 : s.fr.b₂ * s.fr.h₀ = s.fr.z * s.fr.h₀ * s.fr.b₂ := by
    have h1 : s.fr.b₂ * s.fr.h₀ * s.fr.b₂⁻¹ * s.fr.h₀⁻¹ = s.fr.z := by
      have := hsrel.b2h
      rwa [commutatorElement_def] at this
    calc s.fr.b₂ * s.fr.h₀
        = (s.fr.b₂ * s.fr.h₀ * s.fr.b₂⁻¹ * s.fr.h₀⁻¹) * (s.fr.h₀ * s.fr.b₂) := by group
      _ = s.fr.z * (s.fr.h₀ * s.fr.b₂) := by rw [h1]
      _ = s.fr.z * s.fr.h₀ * s.fr.b₂ := by group
  have hsq_h0b1 : (s.fr.h₀ * s.fr.b₁) ^ 2 = 1 :=
    f3_sq_mul_eq_one (h := s.fr.h₀) (b := s.fr.b₁) (z := s.fr.z) hbz1 hsrel.z_sq rfl
      hsrel.h0_sq hzh
  have hsq_h0b2 : (s.fr.h₀ * s.fr.b₂) ^ 2 = 1 :=
    f3_sq_mul_eq_one (h := s.fr.h₀) (b := s.fr.b₂) (z := s.fr.z) hbz2 hsrel.z_sq hsrel.b2_sq
      hsrel.h0_sq hzh
  rw [hB]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact hx.1
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    have hx' : x ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G) := hSg ▸ hx
    have hm_a1a2 : s.fr.a₁ * s.fr.a₂ ∈ closure Sg :=
      Subgroup.subset_closure (by rw [hSg]; simp)
    have hm_b1 : s.fr.b₁ ∈ closure Sg := Subgroup.subset_closure (by rw [hSg]; simp)
    have hm_b2 : s.fr.b₂ ∈ closure Sg := Subgroup.subset_closure (by rw [hSg]; simp)
    have hm_h0 : s.fr.h₀ ∈ closure Sg := Subgroup.subset_closure (by rw [hSg]; simp)
    have hm_h0b1 : s.fr.h₀ * s.fr.b₁ ∈ closure Sg := mul_mem hm_h0 hm_b1
    have hm_h0b2 : s.fr.h₀ * s.fr.b₂ ∈ closure Sg := mul_mem hm_h0 hm_b2
    have hinv_a1a2 : s.fr.a₁ * s.fr.a₂ ∈ closure {b : G | b ∈ closure Sg ∧ b ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hm_a1a2, hsq_a1a2⟩
    have hinv_h0 : s.fr.h₀ ∈ closure {b : G | b ∈ closure Sg ∧ b ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hm_h0, hsrel.h0_sq⟩
    have hinv_h0b1 : s.fr.h₀ * s.fr.b₁ ∈ closure {b : G | b ∈ closure Sg ∧ b ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hm_h0b1, hsq_h0b1⟩
    have hinv_h0b2 : s.fr.h₀ * s.fr.b₂ ∈ closure {b : G | b ∈ closure Sg ∧ b ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hm_h0b2, hsq_h0b2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact hinv_a1a2
    · have hb1eq : s.fr.b₁ = s.fr.h₀ * (s.fr.h₀ * s.fr.b₁) := by
        rw [← mul_assoc, ← pow_two, hsrel.h0_sq, one_mul]
      rw [hb1eq]
      exact mul_mem hinv_h0 hinv_h0b1
    · have hb2eq : s.fr.b₂ = s.fr.h₀ * (s.fr.h₀ * s.fr.b₂) := by
        rw [← mul_assoc, ← pow_two, hsrel.h0_sq, one_mul]
      rw [hb2eq]
      exact mul_mem hinv_h0 hinv_h0b2
    · exact hinv_h0

theorem f3_bt_conj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ b ∈ s.fr.B, b ^ 2 = 1 → ∃ g : G, g * s.t * g⁻¹ = b * s.t := by
  intro b hb hb2
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  by_cases hb1 : b = 1
  · exact ⟨1, by rw [hb1]; group⟩
  · have hbL : b ∈ L := f3_B_le_L s hb
    have hbord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
    have hzord : orderOf s.fr.z = 2 := s3_z_order s hA
    obtain ⟨l, hlL, hl⟩ :=
      s3_invol_conj hH.hS hH.hZ s (u := s.fr.z) (v := b) (s3_z_mem_L s) hzord hbL hbord
    have hzmem : s.fr.z ∈ cen s.fr.S := by
      rw [s3_cen_S s hA]
      exact Subgroup.mem_zpowers s.fr.z
    have hzt_mem : s.fr.z * s.t ∈ s.tCoset (cen s.fr.S) := ⟨s.fr.z, hzmem, rfl⟩
    have hzt_conj : s.fr.z * s.t ∈ conjClass e.T₁ s.t := by
      rw [hH.hDef.2.2]
      exact hzt_mem
    obtain ⟨x, -, hx⟩ := hzt_conj
    refine ⟨l * x, ?_⟩
    have hlt : Commute l s.t := s3_comm_t_of_mem_L s hlL
    have htl : s.t * l⁻¹ = l⁻¹ * s.t := hlt.symm.inv_right.eq
    calc (l * x) * s.t * (l * x)⁻¹
        = l * (x * s.t * x⁻¹) * l⁻¹ := by group
      _ = l * (s.fr.z * s.t) * l⁻¹ := by rw [← hx]
      _ = l * s.fr.z * (s.t * l⁻¹) := by group
      _ = l * s.fr.z * (l⁻¹ * s.t) := by rw [htl]
      _ = l * s.fr.z * l⁻¹ * s.t := by group
      _ = b * s.t := by rw [← hl]

private theorem f3_conj_invol_mem_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hx : x ∈ s.X) {b : G} (hb : b ∈ s.fr.B) (hb2 : b ^ 2 = 1) :
    x * b * x⁻¹ ∈ s.fr.B := by
  have hxP : x ∈ normalizer ((f3P s : Subgroup G) : Set G) := hx
  obtain ⟨v, hvV, hv⟩ := f3_tX_sub hH x hx
  have hvB : v ∈ s.fr.B := (Subgroup.mem_inf.mp hvV).1
  obtain ⟨g, hg⟩ := f3_bt_conj hH b hb hb2
  have hbtP : b * s.t ∈ f3P s :=
    mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hconjP : x * (b * s.t) * x⁻¹ ∈ f3P s :=
    (Subgroup.mem_set_normalizer_iff.mp hxP (b * s.t)).mp hbtP
  have hnotL : x * (b * s.t) * x⁻¹ ∉ L := by
    intro hmem
    refine hH.h31.2.2.1 (x * g) ?_
    rw [show (x * g) * s.t * (x * g)⁻¹ = x * (b * s.t) * x⁻¹ by rw [← hg]; group]
    exact hmem
  obtain ⟨b', hb'B, hb'⟩ := f3_mem_P_not_L hH hconjP hnotL
  have hcalc : x * b * x⁻¹ = b' * v⁻¹ := by
    calc x * b * x⁻¹
        = (x * (b * s.t) * x⁻¹) * (x * s.t * x⁻¹)⁻¹ := by group
      _ = (b' * s.t) * (v * s.t)⁻¹ := by rw [hb', hv]
      _ = b' * v⁻¹ := by group
  rw [hcalc]
  exact mul_mem hb'B (inv_mem hvB)

private theorem f3_conj_invols_closure {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {y : G} (hy : y ∈ s.X) :
    ∀ c ∈ closure {b : G | b ∈ s.fr.B ∧ b ^ 2 = 1}, y * c * y⁻¹ ∈ s.fr.B := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem b hb => exact f3_conj_invol_mem_B hH hy hb.1 hb.2
  | one => simpa using s.fr.B.one_mem
  | mul a b _ _ ha hb =>
      rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
      exact s.fr.B.mul_mem ha hb
  | inv a _ ha =>
      rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
      exact s.fr.B.inv_mem ha

theorem f3_X_le_normB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.X ≤ normalizer (s.fr.B : Set G) := by
  intro x hx
  have hB := f3_closure_invols_B hH
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact f3_conj_invols_closure hH hx b (hB.symm ▸ hb)
  · intro hb
    have hb' : b = x⁻¹ * (x * b * x⁻¹) * x := by group
    rw [hb']
    simpa using f3_conj_invols_closure hH (s.X.inv_mem hx) (x * b * x⁻¹) (hB.symm ▸ hb)

theorem f3_X_norm_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ v ∈ cen s.fr.B, x * v * x⁻¹ ∈ cen s.fr.B := by
  intro x hx v hv
  rw [cen, Subgroup.mem_inf] at hv ⊢
  obtain ⟨hvB, hvC⟩ := hv
  refine ⟨(Subgroup.mem_normalizer_iff.mp (f3_X_le_normB hH hx) v).mp hvB, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hxbx : x⁻¹ * b * x ∈ s.fr.B :=
    (Subgroup.mem_set_normalizer_iff''.mp (f3_X_le_normB hH hx) b).mp hb
  have hvcomm : (x⁻¹ * b * x) * v = v * (x⁻¹ * b * x) :=
    Subgroup.mem_centralizer_iff.mp hvC (x⁻¹ * b * x) hxbx
  calc b * (x * v * x⁻¹)
      = x * ((x⁻¹ * b * x) * v) * x⁻¹ := by group
    _ = x * (v * (x⁻¹ * b * x)) * x⁻¹ := by rw [hvcomm]
    _ = (x * v * x⁻¹) * b := by group

end CFSG.OddStandard.HigherRank.YamadaG23

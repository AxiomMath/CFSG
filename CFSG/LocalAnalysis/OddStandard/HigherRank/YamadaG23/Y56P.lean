module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem card_mul_card_le_sup_mul_inf (A B : Subgroup G) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  have e1 : A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
    rw [Subgroup.relIndex_mul_card]
  have e2 : A.relIndex (A ⊔ B) * Nat.card A = Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card A (A ⊔ B)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hne0 : A.relIndex (A ⊔ B) ≠ 0 := by
    intro h
    rw [h] at e2
    have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have hle : A.relIndex B ≤ A.relIndex (A ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_right hne0
  calc Nat.card A * Nat.card B = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by rw [e1]
    _ ≤ Nat.card A * (A.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ B)) := by gcongr
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [← e2]; ring

theorem y56_E_le_L (s : Setting3 G L) : s.fr.E ≤ L :=
  (s3_E_le_A s).trans (s3_A_le_L s)

theorem y56_t_comm_E (s : Setting3 G L) : ∀ f ∈ s.fr.E, f * s.t = s.t * f :=
  fun f hf => s3_comm_t_of_mem_L s (y56_E_le_L s hf)

theorem y56_E_isE3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsE 3 ↥s.fr.E := by
  have h14 := hH.hLF.fact14
  have hE_mem : s.fr.E ∈ maxElemAbelian (s.fr.A ⊓ s.fr.B) := by
    change (frameWith s 1).E ∈ maxElemAbelian ((frameWith s 1).A ⊓ (frameWith s 1).B)
    rw [h14.2.2.2.1.2.2.1]; simp
  have hE_el : IsElemAbelian 2 s.fr.E := hE_mem.2.1
  have hE_le : s.fr.E ≤ s.fr.A ⊓ s.fr.B := hE_mem.1
  have hsup : s.fr.E ⊔ s.fr.F = s.fr.A ⊓ s.fr.B := h14.2.2.2.1.1
  have hinf : s.fr.E ⊓ s.fr.F = cen s.fr.B := h14.2.2.2.1.2.2.2
  have hcardF : Nat.card ↥s.fr.F = 8 := by
    simpa using (s3_isE3_F hH.hS hH.hZ hH.hOut s).2
  have hcardX : Nat.card ↥(s.fr.A ⊓ s.fr.B) = 16 := by
    change Nat.card ↥((frameWith s 1).A ⊓ (frameWith s 1).B) = 16
    obtain ⟨eD⟩ := h14.2.2.2.1.2.1.2.2.2
    rw [Nat.card_congr eD.toEquiv, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
      DihedralGroup.card]
  have hcardV : Nat.card ↥(cen s.fr.B) = 4 := by
    simpa using (f3_V_isE2 hH).2
  have hineq := card_mul_card_le_sup_mul_inf (A := s.fr.E) (B := s.fr.F)
  rw [hsup, hinf, hcardX, hcardV, hcardF] at hineq
  have hle8 : Nat.card ↥s.fr.E ≤ 8 := by omega
  have hge4 : 4 ≤ Nat.card ↥s.fr.E := by
    have h4 : Nat.card ↥(s.fr.E ⊓ s.fr.F) ≤ Nat.card ↥s.fr.E :=
      Subgroup.card_le_of_le inf_le_left
    rwa [hinf, hcardV] at h4
  have hdvd : Nat.card ↥s.fr.E ∣ 16 := by
    rw [← hcardX]; exact Subgroup.card_dvd_of_le hE_le
  have hne4 : Nat.card ↥s.fr.E ≠ 4 := by
    intro h
    have hEq : s.fr.E ⊓ s.fr.F = s.fr.E := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [h, hinf, hcardV]
    have hleFE : s.fr.E ≤ s.fr.F := by rw [← hEq]; exact inf_le_right
    have hsupF : s.fr.E ⊔ s.fr.F = s.fr.F := sup_eq_right.mpr hleFE
    have hcontra : Nat.card ↥(s.fr.A ⊓ s.fr.B) = Nat.card ↥s.fr.F := by rw [← hsup, hsupF]
    rw [hcardX, hcardF] at hcontra
    norm_num at hcontra
  have hcardE : Nat.card ↥s.fr.E = 8 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num] at hdvd
    obtain ⟨k, hk, hNk⟩ := (Nat.dvd_prime_pow (p := 2) (m := 4) Nat.prime_two).mp hdvd
    rw [hNk] at hge4 hle8 hne4 ⊢
    have hk2 : 2 ≤ k := by
      by_contra h; push Not at h
      interval_cases k <;> norm_num at hge4
    have hk3 : k ≤ 3 := by
      by_contra h; push Not at h
      have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h16
      omega
    have hk_ne2 : k ≠ 2 := by
      intro h; rw [h] at hne4; norm_num at hne4
    have hk_eq : k = 3 := by omega
    rw [hk_eq]; norm_num
  refine ⟨?_, ?_⟩
  · have h := IsElemAbelian.subgroupOf hE_el s.fr.E
    rwa [Subgroup.subgroupOf_self] at h
  · show Nat.card ↥s.fr.E = 2 ^ 3
    rw [hcardE]; norm_num

theorem y56_E_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.E, f ^ 2 = 1 := by
  have hE_mem : s.fr.E ∈ maxElemAbelian (s.fr.A ⊓ s.fr.B) := by
    change (frameWith s 1).E ∈ maxElemAbelian ((frameWith s 1).A ⊓ (frameWith s 1).B)
    rw [hH.hLF.fact14.2.2.2.1.2.2.1]; simp
  exact (hE_mem.2.1).2

theorem y56_E_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.E, ∀ f' ∈ s.fr.E, f * f' = f' * f := by
  have hE_mem : s.fr.E ∈ maxElemAbelian (s.fr.A ⊓ s.fr.B) := by
    change (frameWith s 1).E ∈ maxElemAbelian ((frameWith s 1).A ⊓ (frameWith s 1).B)
    rw [hH.hLF.fact14.2.2.2.1.2.2.1]; simp
  haveI : IsMulCommutative ↥s.fr.E := (hE_mem.2.1).1
  intro f hf f' hf'
  exact congrArg Subtype.val (mul_comm' (⟨f, hf⟩ : ↥s.fr.E) ⟨f', hf'⟩)

theorem y56_E_le_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.E ≤ s.fr.B := by
  calc s.fr.E ≤ s.fr.E ⊔ s.fr.F := le_sup_left
    _ = s.fr.A ⊓ s.fr.B := hH.hLF.fact14.2.2.2.1.1
    _ ≤ s.fr.B := inf_le_right

theorem y56_V_le_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ s.fr.E := by
  calc cen s.fr.B = s.fr.E ⊓ s.fr.F := (hH.hLF.fact14.2.2.2.1.2.2.2).symm
    _ ≤ s.fr.E := inf_le_left

theorem y56_z_mem_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.z ∈ s.fr.E := by
  have h : (frameWith s 1).z ∈ cen ((frameWith s 1).B) := by
    rw [hH.hLF.fact14.2.2.1.1]
    exact Subgroup.subset_closure (by simp)
  exact y56_V_le_E hH h

theorem y56_v0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B ∧ s.fr.z ∈ cen s.fr.B ∧ s.fr.b₁ * s.fr.b₂ ≠ 1 ∧
      s.fr.z ≠ 1 ∧ s.fr.b₁ * s.fr.b₂ ≠ s.fr.z ∧
      ∀ v ∈ cen s.fr.B,
        v = 1 ∨ v = s.fr.z ∨ v = s.fr.b₁ * s.fr.b₂ ∨ v = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  obtain ⟨_, -, hzV, hwne1, hzne1, hwnez, -, hzsq, -, henum⟩ := f3_V_elems hH
  have hcen : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  have hw0V : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have hcyc : ¬ IsCyclic ↥(cen s.fr.B) := hH.hLF.fact14.2.2.1.2.2.2.1
  have hz2 : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hzsq
  have hw0ne1 : s.fr.b₁ * s.fr.b₂ ≠ 1 := by
    intro h1
    apply hcyc
    rw [hcen, h1]
    exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers s.fr.z) (by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers s.fr.z)
  have hw0nez : s.fr.b₁ * s.fr.b₂ ≠ s.fr.z := by
    intro h1
    apply hcyc
    rw [hcen, h1]
    exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers s.fr.z) (by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_zpowers s.fr.z
      · exact Subgroup.mem_zpowers s.fr.z)
  have hcases := henum (s.fr.b₁ * s.fr.b₂) hw0V
  refine ⟨hw0V, hzV, hw0ne1, hzne1, hw0nez, ?_⟩
  intro v hv
  rcases henum v hv with h1 | hz | hw | hzw
  · exact Or.inl h1
  · exact Or.inr (Or.inl hz)
  · rcases hcases with h | h | h | h
    · exact absurd h hw0ne1
    · exact absurd h hw0nez
    · exact Or.inr (Or.inr (Or.inl (hw.trans h.symm)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hw, h, ← mul_assoc, hz2, one_mul])))
  · rcases hcases with h | h | h | h
    · exact absurd h hw0ne1
    · exact absurd h hw0nez
    · exact Or.inr (Or.inr (Or.inr (by rw [hzw, h])))
    · exact Or.inr (Or.inr (Or.inl (by rw [hzw, h])))

theorem y56_mem_Q (s : Setting3 G L) {p : G} (hp : p ∈ e4Q s) :
    p ∈ s.fr.E ∨ ∃ f ∈ s.fr.E, p = f * s.t := by
  have htt : s.t * s.t = 1 := by rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  rw [show e4Q s = Subgroup.closure ((s.fr.E : Set G) ∪ (Subgroup.zpowers s.t : Set G)) from
    Subgroup.sup_eq_closure _ _] at hp
  refine Subgroup.closure_induction (p := fun p _ => p ∈ s.fr.E ∨ ∃ f ∈ s.fr.E, p = f * s.t)
    ?_ ?_ ?_ ?_ hp
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rcases Int.emod_two_eq_zero_or_one n with h2 | h2
      · left
        have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
        rw [show s.t ^ n = 1 by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp]
        exact s.fr.E.one_mem
      · right
        have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
        exact ⟨1, s.fr.E.one_mem, by
          rw [show s.t ^ n = s.t by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp,
            one_mul]⟩
  · exact Or.inl s.fr.E.one_mem
  · intro x y _ _ hx hy
    rcases hx with hx | ⟨b, hb, rfl⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · exact Or.inl (s.fr.E.mul_mem hx hy)
      · exact Or.inr ⟨x * c, s.fr.E.mul_mem hx hc, by group⟩
    · rcases hy with hy | ⟨c, hc, rfl⟩
      · refine Or.inr ⟨b * y, s.fr.E.mul_mem hb hy, ?_⟩
        calc b * s.t * y = b * (s.t * y) := by group
          _ = b * (y * s.t) := by rw [← s3_comm_t_of_mem_L s (y56_E_le_L s hy)]
          _ = b * y * s.t := by group
      · refine Or.inl ?_
        rw [show b * s.t * (c * s.t) = b * c by
          calc b * s.t * (c * s.t) = b * (s.t * c) * s.t := by group
            _ = b * (c * s.t) * s.t := by rw [← s3_comm_t_of_mem_L s (y56_E_le_L s hc)]
            _ = b * c * (s.t * s.t) := by group
            _ = b * c := by rw [htt, mul_one]]
        exact s.fr.E.mul_mem hb hc
  · intro x _ hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · exact Or.inl (s.fr.E.inv_mem hx)
    · refine Or.inr ⟨b⁻¹, s.fr.E.inv_mem hb, ?_⟩
      have htb : s.t * b⁻¹ = b⁻¹ * s.t :=
        (s3_comm_t_of_mem_L s (y56_E_le_L s (s.fr.E.inv_mem hb))).symm
      calc (b * s.t)⁻¹ = s.t⁻¹ * b⁻¹ := mul_inv_rev b s.t
        _ = s.t * b⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
        _ = b⁻¹ * s.t := htb

theorem y56_mem_Q_not_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {p : G}
    (hp : p ∈ e4Q s) (hpL : p ∉ L) : ∃ f ∈ s.fr.E, p = f * s.t := by
  rcases y56_mem_Q s hp with h | h
  · exact absurd (y56_E_le_L s h) hpL
  · exact h

theorem y56_tX_sub {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ e4X s, ∃ v ∈ s.fr.E, x * s.t * x⁻¹ = v * s.t := by
  intro x hx
  have hxP : x ∈ Subgroup.normalizer ((s.fr.E ⊔ zpowers s.t : Subgroup G) : Set G) := hx
  have hxtxP : x * s.t * x⁻¹ ∈ s.fr.E ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP s.t).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  exact y56_mem_Q_not_L hH hxtxP (hH.h31.2.2.1 x)

theorem y56_Q_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ q ∈ e4Q s, q ^ 2 = 1 := by
  have ht : s.t * s.t = 1 := by rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  intro q hq
  rcases y56_mem_Q s hq with hqE | ⟨f, hfE, rfl⟩
  · exact y56_E_sq hH q hqE
  · have hsq : (f * s.t) ^ 2 = (f ^ 2) * (s.t ^ 2) := by
      calc (f * s.t) ^ 2 = f * (s.t * f) * s.t := by rw [pow_two]; group
        _ = f * (f * s.t) * s.t := by rw [← y56_t_comm_E s f hfE]
        _ = (f ^ 2) * (s.t ^ 2) := by rw [pow_two, pow_two]; group
    rw [hsq, y56_E_sq hH f hfE, show s.t ^ 2 = 1 by rw [pow_two]; exact ht, one_mul]

theorem y56_ft_conj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.E, ∃ g : G, g * s.t * g⁻¹ = f * s.t := by
  intro f hf
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  by_cases hf1 : f = 1
  · exact ⟨1, by rw [hf1]; group⟩
  · have hfL : f ∈ L := y56_E_le_L s hf
    have hfsq : f ^ 2 = 1 := y56_E_sq hH f hf
    have hford : orderOf f = 2 := orderOf_eq_prime hfsq hf1
    have hzord : orderOf s.fr.z = 2 := s3_z_order s hA
    obtain ⟨l, hlL, hl⟩ :=
      s3_invol_conj hH.hS hH.hZ s (u := s.fr.z) (v := f) (s3_z_mem_L s) hzord hfL hford
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
      _ = f * s.t := by rw [← hl]

private theorem y56_conj_mem_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hx : x ∈ e4X s) : ∀ f ∈ s.fr.E, x * f * x⁻¹ ∈ s.fr.E := by
  intro f hf
  have hxP : x ∈ Subgroup.normalizer ((s.fr.E ⊔ zpowers s.t : Subgroup G) : Set G) := hx
  have hftP : f * s.t ∈ s.fr.E ⊔ zpowers s.t :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hf)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hftxP : x * (f * s.t) * x⁻¹ ∈ s.fr.E ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP (f * s.t)).mp hftP
  have hftx_notL : x * (f * s.t) * x⁻¹ ∉ L := by
    obtain ⟨g, hg⟩ := y56_ft_conj hH f hf
    intro hmem
    refine hH.h31.2.2.1 (x * g) ?_
    rw [show (x * g) * s.t * (x * g)⁻¹ = x * (f * s.t) * x⁻¹ by rw [← hg]; group]
    exact hmem
  obtain ⟨b₁, hb₁E, hb₁⟩ := y56_mem_Q_not_L hH hftxP hftx_notL
  have htxP : x * s.t * x⁻¹ ∈ s.fr.E ⊔ zpowers s.t :=
    (Subgroup.mem_set_normalizer_iff.mp hxP s.t).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  obtain ⟨b₂, hb₂E, hb₂⟩ := y56_mem_Q_not_L hH htxP (hH.h31.2.2.1 x)
  have hcalc : x * f * x⁻¹ = b₁ * b₂⁻¹ := by
    calc x * f * x⁻¹ = (x * (f * s.t) * x⁻¹) * (x * s.t * x⁻¹)⁻¹ := by group
      _ = (b₁ * s.t) * (b₂ * s.t)⁻¹ := by rw [hb₁, hb₂]
      _ = b₁ * b₂⁻¹ := by group
  rw [hcalc]
  exact s.fr.E.mul_mem hb₁E (s.fr.E.inv_mem hb₂E)

theorem y56_X_le_normE {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4X s ≤ normalizer (s.fr.E : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    exact y56_conj_mem_E hH hx f hf
  · intro hf
    have hmem := y56_conj_mem_E hH ((e4X s).inv_mem hx) (x * f * x⁻¹) hf
    rwa [show x⁻¹ * (x * f * x⁻¹) * (x⁻¹)⁻¹ = f by group] at hmem

end CFSG.OddStandard.HigherRank.YamadaG23

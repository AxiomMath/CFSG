module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Setup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Au
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Core

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_t_mem_A (t : G) (S L : Subgroup G) : t ∈ secA t S L :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem sec1011_B_le_A (t : G) (S L : Subgroup G) : secB S L ≤ secA t S L :=
  le_sup_left

@[expose] def sec1011_tA (t : G) (S L : Subgroup G) : ↥(secA t S L) :=
  ⟨t, sec1011_t_mem_A t S L⟩

@[expose] def sec1011_BA (t : G) (S L : Subgroup G) : Subgroup ↥(secA t S L) :=
  (secB S L).subgroupOf (secA t S L)

open Classical in
@[expose] noncomputable def sec1011_phiA (t : G) (S L : Subgroup G)
    (φ : (Fin 5 → ZMod 2) → G) (v : Fin 5 → ZMod 2) : ↥(secA t S L) :=
  if h : φ v ∈ secA t S L then ⟨φ v, h⟩ else 1

theorem sec1011_mem_BA {x : ↥(secA t S L)} : x ∈ sec1011_BA t S L ↔ (x : G) ∈ secB S L :=
  Iff.rfl

theorem sec1011_phi_mem_B (hs : Sec1011Setup t L S z φ) {v : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) : φ v ∈ secB S L := by
  exact (hs.hperm.2.2.1 (φ v)).2 ⟨v, hv, rfl⟩

theorem sec1011_phiA_coe (hs : Sec1011Setup t L S z φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    ((sec1011_phiA t S L φ v : ↥(secA t S L)) : G) = φ v := by
  have hmem : φ v ∈ secA t S L := sec1011_B_le_A t S L (sec1011_phi_mem_B hs hv)
  unfold sec1011_phiA
  rw [dif_pos hmem]

theorem sec1011_B_comm (hs : Sec1011Setup t L S z φ) :
    ∀ a ∈ secB S L, ∀ b ∈ secB S L, a * b = b * a := by
  intro a ha b hb
  obtain ⟨v, hv, rfl⟩ := (hs.hperm.2.2.1 a).1 ha
  obtain ⟨w, hw, rfl⟩ := (hs.hperm.2.2.1 b).1 hb
  rw [← hs.hperm.1 v w hv hw, ← hs.hperm.1 w v hw hv, add_comm v w]

theorem sec1011_B_t_comm (hs : Sec1011Setup t L S z φ) :
    ∀ b ∈ secB S L, b * t = t * b := by
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp hs.htC b (secB_le_L S L hb)

private lemma sec1011_ht2_mul (hs : Sec1011Setup t L S z φ) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [hs.ht2, pow_two] at h
  exact h

private lemma sec1011_ht_inv (hs : Sec1011Setup t L S z φ) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (sec1011_ht2_mul hs)

private lemma sec1011_tA_coe (t : G) (S L : Subgroup G) :
    ((sec1011_tA t S L : ↥(secA t S L)) : G) = t :=
  rfl

private def sec1011_decompSub (hs : Sec1011Setup t L S z φ) : Subgroup G where
  carrier := {x | ∃ b ∈ secB S L, x = b ∨ x = b * t}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨b1, hb1, hx1 | hx1⟩ := hx
    · obtain ⟨b2, hb2, hy1 | hy1⟩ := hy
      · exact ⟨b1 * b2, (secB S L).mul_mem hb1 hb2, Or.inl (by rw [hx1, hy1])⟩
      · exact ⟨b1 * b2, (secB S L).mul_mem hb1 hb2,
          Or.inr (by rw [hx1, hy1]; group)⟩
    · obtain ⟨b2, hb2, hy1 | hy1⟩ := hy
      · refine ⟨b1 * b2, (secB S L).mul_mem hb1 hb2, Or.inr ?_⟩
        rw [hx1, hy1]
        calc (b1 * t) * b2 = b1 * (t * b2) := by group
          _ = b1 * (b2 * t) := by rw [← sec1011_B_t_comm hs b2 hb2]
          _ = (b1 * b2) * t := by group
      · refine ⟨b1 * b2, (secB S L).mul_mem hb1 hb2, Or.inl ?_⟩
        rw [hx1, hy1]
        calc (b1 * t) * (b2 * t) = b1 * (t * b2) * t := by group
          _ = b1 * (b2 * t) * t := by rw [← sec1011_B_t_comm hs b2 hb2]
          _ = (b1 * b2) * (t * t) := by group
          _ = b1 * b2 := by rw [sec1011_ht2_mul hs, mul_one]
  one_mem' := ⟨1, (secB S L).one_mem, Or.inl rfl⟩
  inv_mem' := by
    intro x hx
    obtain ⟨b, hb, hx1 | hx1⟩ := hx
    · exact ⟨b⁻¹, (secB S L).inv_mem hb, Or.inl (by rw [hx1])⟩
    · refine ⟨b⁻¹, (secB S L).inv_mem hb, Or.inr ?_⟩
      rw [hx1, mul_inv_rev, sec1011_ht_inv hs]
      exact (sec1011_B_t_comm hs b⁻¹ ((secB S L).inv_mem hb)).symm

private lemma sec1011_A_decomp (hs : Sec1011Setup t L S z φ) :
    ∀ x ∈ secA t S L, ∃ b ∈ secB S L, x = b ∨ x = b * t := by
  have hBP : secB S L ≤ sec1011_decompSub hs := fun b hb => ⟨b, hb, Or.inl rfl⟩
  have htP : t ∈ sec1011_decompSub hs :=
    ⟨1, (secB S L).one_mem, Or.inr (by rw [one_mul])⟩
  have hA : secA t S L ≤ sec1011_decompSub hs :=
    sup_le hBP (Subgroup.zpowers_le.mpr htP)
  intro x hx
  exact hA hx

private lemma sec1011_conj_mul (hs : Sec1011Setup t L S z φ) {b1 b2 : G}
    (hb1 : b1 ∈ secB S L) : (b2 * t) * (b1 * t) = b2 * b1 := by
  calc (b2 * t) * (b1 * t) = b2 * (t * b1) * t := by group
    _ = b2 * (b1 * t) * t := by rw [← sec1011_B_t_comm hs b1 hb1]
    _ = (b2 * b1) * (t * t) := by group
    _ = b2 * b1 := by rw [sec1011_ht2_mul hs, mul_one]

private lemma sec1011_bt_comm_right (hs : Sec1011Setup t L S z φ) {b1 b2 : G}
    (hb1 : b1 ∈ secB S L) (hb2 : b2 ∈ secB S L) :
    b1 * (b2 * t) = (b2 * t) * b1 := by
  calc b1 * (b2 * t) = (b1 * b2) * t := by group
    _ = (b2 * b1) * t := by rw [sec1011_B_comm hs b1 hb1 b2 hb2]
    _ = b2 * (b1 * t) := by group
    _ = b2 * (t * b1) := by rw [sec1011_B_t_comm hs b1 hb1]
    _ = (b2 * t) * b1 := by group

private lemma sec1011_tb_comm_left (hs : Sec1011Setup t L S z φ) {b1 b2 : G}
    (hb1 : b1 ∈ secB S L) (hb2 : b2 ∈ secB S L) :
    (b1 * t) * b2 = b2 * (b1 * t) := by
  calc (b1 * t) * b2 = b1 * (t * b2) := by group
    _ = b1 * (b2 * t) := by rw [← sec1011_B_t_comm hs b2 hb2]
    _ = (b1 * b2) * t := by group
    _ = (b2 * b1) * t := by rw [sec1011_B_comm hs b1 hb1 b2 hb2]
    _ = b2 * (b1 * t) := by group

theorem sec1011_A_comm (hs : Sec1011Setup t L S z φ) :
    ∀ a ∈ secA t S L, ∀ b ∈ secA t S L, a * b = b * a := by
  intro a ha b hb
  obtain ⟨b1, hb1, h1⟩ := sec1011_A_decomp hs a ha
  obtain ⟨b2, hb2, h2⟩ := sec1011_A_decomp hs b hb
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]; exact sec1011_B_comm hs b1 hb1 b2 hb2
  · rw [h1, h2]; exact sec1011_bt_comm_right hs hb1 hb2
  · rw [h1, h2]; exact sec1011_tb_comm_left hs hb1 hb2
  · rw [h1, h2]
    calc (b1 * t) * (b2 * t) = b1 * b2 := sec1011_conj_mul hs hb2
      _ = b2 * b1 := sec1011_B_comm hs b1 hb1 b2 hb2
      _ = (b2 * t) * (b1 * t) := (sec1011_conj_mul hs hb1).symm

theorem sec1011_A_split (hs : Sec1011Setup t L S z φ) :
    ∀ a ∈ secA t S L, a ∈ secB S L ∨ t * a ∈ secB S L := by
  intro a ha
  obtain ⟨b, hb, rfl | rfl⟩ := sec1011_A_decomp hs a ha
  · exact Or.inl hb
  · right
    have heq : t * (b * t) = b := by
      calc t * (b * t) = (t * b) * t := by group
        _ = (b * t) * t := by rw [← sec1011_B_t_comm hs b hb]
        _ = b * (t * t) := by group
        _ = b := by rw [sec1011_ht2_mul hs, mul_one]
    rwa [heq]

theorem sec1011_t_not_mem_B (hs : Sec1011Setup t L S z φ) : t ∉ secB S L :=
  fun h => hs.htL (secB_le_L S L h)

theorem sec1011_core_of_setup (hs : Sec1011Setup t L S z φ) :
    Sec1011Core (sec1011_BA t S L) (sec1011_tA t S L) (secMstar t S L)
      (sec1011_phiA t S L φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact Subtype.ext (by simpa using sec1011_A_comm hs a a.2 b b.2)
  · apply Subtype.ext
    show t * t = 1
    exact sec1011_ht2_mul hs
  · intro h
    exact sec1011_t_not_mem_B hs (by simpa [sec1011_tA] using sec1011_mem_BA.mp h)
  · intro a
    rcases sec1011_A_split hs a a.2 with h | h
    · exact Or.inl (sec1011_mem_BA.mpr h)
    · refine Or.inr ?_
      rw [sec1011_mem_BA]
      simpa [sec1011_tA, sec1011_tA_coe t S L] using h
  · intro v w hv hw
    apply Subtype.ext
    rw [Subgroup.coe_mul, sec1011_phiA_coe hs (sec1011_isEvenVec_add hv hw),
      sec1011_phiA_coe hs hv, sec1011_phiA_coe hs hw]
    exact hs.hperm.1 v w hv hw
  · intro v w hv hw h
    apply hs.hperm.2.1 v w hv hw
    have h' : ((sec1011_phiA t S L φ v : ↥(secA t S L)) : G) =
        ((sec1011_phiA t S L φ w : ↥(secA t S L)) : G) := congrArg Subtype.val h
    rwa [sec1011_phiA_coe hs hv, sec1011_phiA_coe hs hw] at h'
  · intro x
    constructor
    · intro hx
      obtain ⟨v, hv, hφv⟩ := (hs.hperm.2.2.1 (x : G)).1 (sec1011_mem_BA.mp hx)
      exact ⟨v, hv, Subtype.ext (by rw [sec1011_phiA_coe hs hv]; exact hφv)⟩
    · rintro ⟨v, hv, rfl⟩
      rw [sec1011_mem_BA, sec1011_phiA_coe hs hv]
      exact sec1011_phi_mem_B hs hv
  · intro α hα b hb
    unfold secMstar at hα
    rw [sec1011_mem_BA] at hb ⊢
    obtain ⟨m, hmM, hmN, hαeq⟩ := sec1011_exists_conjAut hα
    rw [hαeq, sec1011_conjAut_apply]
    exact hs.hBM m hmM (b : G) hb
  · intro α hα
    unfold secMstar at hα
    obtain ⟨m, hmM, hmN, hαeq⟩ := sec1011_exists_conjAut hα
    rw [sec1011_mem_BA]
    have hmemA : m * t * m⁻¹ ∈ secA t S L := by
      have h := (α (sec1011_tA t S L)).2
      rw [hαeq, sec1011_conjAut_apply] at h
      exact h
    obtain ⟨b, hb, hbeq⟩ := hs.htB m⁻¹ (by simpa [inv_inv] using hmemA)
    have hbeq' : m * t * m⁻¹ = t * b := by simpa [inv_inv] using hbeq
    have hcoe : ((sec1011_tA t S L)⁻¹ * α (sec1011_tA t S L) :
        ↥(secA t S L)).1 = t⁻¹ * (m * t * m⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαeq, sec1011_conjAut_apply,
        sec1011_tA_coe t S L]
    rw [hcoe, hbeq', ← mul_assoc, inv_mul_cancel, one_mul]
    exact hb
  · intro σ hσ
    obtain ⟨h, hh, hact⟩ := hs.hperm.2.2.2.2 σ hσ
    have hhM : h ∈ secM t S L ⊓ L := by rw [hs.hML]; exact hh
    have hmM : h ∈ secM t S L := (Subgroup.mem_inf.mp hhM).1
    have hL : h ∈ L := (Subgroup.mem_inf.mp hhM).2
    have hmN : h ∈ normalizer (secA t S L : Set G) := hmM
    refine ⟨sec1011_conjAut (secA t S L) h hmN, ?_, ?_, ?_⟩
    · change sec1011_conjAut (secA t S L) h hmN ∈ autIn (secM t S L) (secA t S L)
      exact sec1011_conjAut_mem hmM hmN
    · apply Subtype.ext
      rw [sec1011_conjAut_apply, sec1011_tA_coe t S L]
      have hcomm : h * t = t * h := Subgroup.mem_centralizer_iff.mp hs.htC h hL
      rw [hcomm]
      exact mul_inv_cancel_right t h
    · intro v hv
      apply Subtype.ext
      rw [sec1011_conjAut_apply, sec1011_phiA_coe hs hv,
        sec1011_phiA_coe hs (isEvenVec_permVec σ hv)]
      exact hact v hv
  · obtain ⟨v, hv, hw, hz⟩ := hs.hz
    obtain ⟨m, hmM, hmt⟩ := hs.htz
    have hmN : m ∈ normalizer (secA t S L : Set G) := hmM
    refine ⟨v, hv, hw, sec1011_conjAut (secA t S L) m hmN, ?_, ?_⟩
    · change sec1011_conjAut (secA t S L) m hmN ∈ autIn (secM t S L) (secA t S L)
      exact sec1011_conjAut_mem hmM hmN
    · apply Subtype.ext
      rw [sec1011_conjAut_apply, Subgroup.coe_mul, sec1011_phiA_coe hs hv,
        sec1011_tA_coe t S L, ← hz]
      exact hmt

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79h
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79j

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L1 L2 J : Subgroup G}

private lemma mem_normalizer_commutator_self {A : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) : x ∈ normalizer (⁅A, A⁆ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  rw [Subgroup.map_commutator (f := (MulAut.conj x : G →* G)), hx]

private lemma exists_mul_of_mem_sup {A B M : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M)
    (hsup : A ⊔ B = M) (hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) {x : G} (hx : x ∈ M) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ closure ((A : Set G) ∪ (B : Set G)) := by
    rw [← Subgroup.sup_eq_closure, hsup]; exact hx
  refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, ∃ b ∈ B, y = a * b) ?_ ?_ ?_ ?_ hx'
  · rintro y (hyA | hyB)
    · exact ⟨y, hyA, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hyB, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro y z hy hz ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    simp only [mul_assoc]
    rw [← mul_assoc b1 a2 b2, hcomm b1 (hBM hb1) a2 (hAM ha2), mul_assoc]
  · rintro y hy ⟨a1, ha1, b1, hb1, rfl⟩
    refine ⟨a1⁻¹, A.inv_mem ha1, b1⁻¹, B.inv_mem hb1, ?_⟩
    rw [mul_inv_rev, hcomm b1⁻¹ (hBM (B.inv_mem hb1)) a1⁻¹ (hAM (A.inv_mem ha1))]

private lemma commutator_le_centIn {M L1 L2 : Subgroup G} (h : Gl3Pair M L1 L2)
    (hsup : centIn M L1 ⊔ centIn M L2 = M) : ⁅L1, M⁆ ≤ centIn M L2 := by
  haveI : IsMulCommutative M := h.elem.1
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hnorm : L1 ≤ normalizer (centIn M L2 : Set G) :=
    Gl3Pair.L2_le_normalizer_centIn h.symm (D := L2) le_rfl
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨b1, hb1, b2, hb2, hb_eq⟩ :=
    exists_mul_of_mem_sup (A := centIn M L1) (B := centIn M L2) inf_le_left inf_le_left hsup
      hcomm hb
  rw [hb_eq]
  have hb1c : ⁅a, b1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hb1.2 a ha)
  have hconj : a * b2 * a⁻¹ ∈ centIn M L2 :=
    (Subgroup.mem_normalizer_iff.mp (hnorm ha) b2).mp hb2
  have hu : ⁅a, b2⁆ ∈ centIn M L2 := by
    rw [commutatorElement_def]
    exact (centIn M L2).mul_mem hconj ((centIn M L2).inv_mem hb2)
  have hcomm' : b1 * ⁅a, b2⁆ = ⁅a, b2⁆ * b1 := setLike_mul_comm hb1.1 hu.1
  rw [commutatorElement_mul_right_eq_mul_conj, hb1c, one_mul, hcomm', mul_assoc, mul_inv_cancel,
    mul_one]
  exact hu

theorem y7c_comm_inf_eq
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2)
    (h : Gl3Pair M L1 L2) (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥)
    (hU1 : centIn M L1 ≠ ⊥) (hU2 : centIn M L2 ≠ ⊥) : ⁅L1, L1⁆ ⊓ M = centIn M L2 := by
  obtain ⟨hcardU1, hcardU2⟩ := y7c_cent_card h hJ hJM hU1 hU2
  have hsup : centIn M L1 ⊔ centIn M L2 = M := y7c_cent_sup h hJ hJM hU1 hU2
  have hinf : centIn M L1 ⊓ centIn M L2 = ⊥ := y7c_cent_inf hJ hJM
  haveI : IsMulCommutative M := h.elem.1
  have hcommM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hcomm : ⁅L1, M⁆ ≤ centIn M L2 := commutator_le_centIn h hsup
  have hL1norm : L1 ≤ normalizer (centIn M L2 : Set G) :=
    Gl3Pair.L2_le_normalizer_centIn h.symm (D := L2) le_rfl
  have hU2le : centIn M L2 ≤ ⁅L1, L1⁆ := y7c_cent_le_comm h hJ hJM hU1 hU2
  have hU2X0 : centIn M L2 ≤ ⁅L1, L1⁆ ⊓ M := le_inf hU2le inf_le_left
  have hschur : Nat.card ↥((⁅L1, L1⁆ ⊓ M) ⊔ centIn M L2)
      ≤ 2 * Nat.card ↥(centIn M L2) :=
    y7c_schur_gl3 hSM h.ext1 inf_le_left hL1norm hcomm
  have hX0le : Nat.card ↥(⁅L1, L1⁆ ⊓ M) ≤ 16 := by
    have h := hschur
    rw [sup_eq_left.mpr hU2X0, hcardU2] at h
    norm_num at h
    exact h
  have hX0mod : ⁅L1, L1⁆ ⊓ M = centIn M L2 ⊔ (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) := by
    refine le_antisymm ?_ (sup_le hU2X0 inf_le_left)
    intro x hx
    obtain ⟨u1, hu1, u2, hu2, hx_eq⟩ :=
      exists_mul_of_mem_sup (A := centIn M L1) (B := centIn M L2) inf_le_left inf_le_left hsup
        hcommM hx.2
    have hu2X0 : u2 ∈ ⁅L1, L1⁆ ⊓ M := hU2X0 hu2
    have hu1X0 : u1 ∈ ⁅L1, L1⁆ ⊓ M := by
      have h1 : u1 = x * u2⁻¹ := by rw [hx_eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [h1]
      exact (⁅L1, L1⁆ ⊓ M).mul_mem hx ((⁅L1, L1⁆ ⊓ M).inv_mem hu2X0)
    rw [hx_eq, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hu1X0, hu1⟩) hu2
  have hWcomm : ∀ a ∈ centIn M L2, ∀ b ∈ ⁅L1, L1⁆ ⊓ M ⊓ centIn M L1, a * b = b * a :=
    fun a ha b hb => setLike_mul_comm ha.1 hb.1.2
  have hWinf : centIn M L2 ⊓ (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_right)) ?_
    rw [inf_comm]
    exact hinf.le
  have hX0card : Nat.card ↥(⁅L1, L1⁆ ⊓ M)
      = Nat.card ↥(centIn M L2) * Nat.card ↥(⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) := by
    have hc := y7c_card_sup_of_commute hWcomm hWinf
    rwa [show centIn M L2 ⊔ (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = ⁅L1, L1⁆ ⊓ M
      from hX0mod.symm] at hc
  have hWle2 : Nat.card ↥(⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) ≤ 2 := by
    have h := hX0le
    rw [hX0card, hcardU2] at h
    omega
  have hL2norm : L2 ≤ normalizer (centIn M L1 : Set G) :=
    Gl3Pair.L2_le_normalizer_centIn h (D := L1) le_rfl
  have hX0norm : L2 ≤ normalizer ((⁅L1, L1⁆ ⊓ M : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := ⁅L1, L1⁆) (K := M)
      ⟨mem_normalizer_commutator_self (Gl3Pair.L1_le_normalizer_L2 h.symm hy),
        Gl3Pair.le_normalizer_M h.symm hy⟩
  have hWnorm : L2 ≤ normalizer ((⁅L1, L1⁆ ⊓ M ⊓ centIn M L1 : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := ⁅L1, L1⁆ ⊓ M) (K := centIn M L1)
      ⟨hX0norm hy, hL2norm hy⟩
  have hWcases : (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = ⊥
      ∨ (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = centIn M L1 :=
    y7c_cent_irred h.symm (by rwa [sup_comm]) hJM hU2 hU1 inf_le_right hWnorm
  have hWbot : (⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = ⊥ := by
    rcases hWcases with hW | hW
    · exact hW
    · exfalso
      have : Nat.card ↥(⁅L1, L1⁆ ⊓ M ⊓ centIn M L1) = 8 := by rw [hW, hcardU1]
      omega
  rw [hX0mod, hWbot, sup_bot_eq]

end CFSG.OddStandard.HigherRank.YamadaG23

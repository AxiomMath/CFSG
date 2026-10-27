module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Br0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_pow4_act {n : G} {B : Subgroup G} (hcube : ∀ b ∈ B, n ^ 3 * b * (n ^ 3)⁻¹ = b)
    {b : G} (hb : b ∈ B) : n ^ 4 * b * (n ^ 4)⁻¹ = n * b * n⁻¹ := by
  have h := hcube b hb
  calc n ^ 4 * b * (n ^ 4)⁻¹ = n * (n ^ 3 * b * (n ^ 3)⁻¹) * n⁻¹ := by group
    _ = n * b * n⁻¹ := by rw [h]

private theorem sec1011_pow12 {n : G} {B : Subgroup G}
    (hcube : ∀ b ∈ B, n ^ 3 * b * (n ^ 3)⁻¹ = b) {b : G} (hb : b ∈ B) :
    (n ^ 4) ^ 3 * b * ((n ^ 4) ^ 3)⁻¹ = b := by
  have hc : Commute (n ^ 3) b := by
    have h := hcube b hb
    exact mul_inv_eq_iff_eq_mul.mp h
  have h12 : Commute ((n ^ 3) ^ 4) b := hc.pow_left 4
  have heq : (n ^ 4) ^ 3 = (n ^ 3) ^ 4 := by rw [← pow_mul, ← pow_mul]
  rw [heq]
  exact mul_inv_eq_iff_eq_mul.mpr h12.eq

theorem sec1011_p2_lift (hs : Sec1011Setup t L S z φ)
    (h6 : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | a = sec1011_tA t S L ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧
        a = sec1011_tA t S L * sec1011_phiA t S L φ v})
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5))) [Finite G] :
    ∃ n1 ∈ secM t S L, ∃ n2 ∈ secM t S L,
      n1 * (t * φ sec1011_w0) * n1⁻¹ = t * φ sec1011_w0 ∧
      n2 * (t * φ sec1011_w0) * n2⁻¹ = t * φ sec1011_w0 ∧
      (∀ b ∈ secB S L, n1 ^ 4 * (n2 ^ 4 * b * (n2 ^ 4)⁻¹) * (n1 ^ 4)⁻¹ =
        n2 ^ 4 * (n1 ^ 4 * b * (n1 ^ 4)⁻¹) * (n2 ^ 4)⁻¹) ∧
      (∀ b ∈ secB S L, (n1 ^ 4) ^ 3 * b * ((n1 ^ 4) ^ 3)⁻¹ = b) ∧
      (∀ b ∈ secB S L, (n2 ^ 4) ^ 3 * b * ((n2 ^ 4) ^ 3)⁻¹ = b) ∧
      ∀ b ∈ secB S L, ∃ b1 ∈ secB S L, ∃ b2 ∈ secB S L,
        b = b1 * (n1 ^ 4 * b1 * (n1 ^ 4)⁻¹) * (b2 * (n2 ^ 4 * b2 * (n2 ^ 4)⁻¹)) := by
  have hcore := sec1011_core_of_setup hs
  have hA2 : Sec1011A2 (sec1011_BA t S L) (sec1011_tA t S L) (secMstar t S L)
      (sec1011_phiA t S L φ) := ⟨hcore, h6, sec1011_iso_of_107b h107b⟩
  obtain ⟨α1, hα1, α2, hα2, hf1, hf2, hcomm, hc1, hc2, hspan⟩ := sec1011_p2_abs hA2
  obtain ⟨n1, hn1M, hn1N, rfl⟩ := sec1011_exists_conjAut hα1
  obtain ⟨n2, hn2M, hn2N, rfl⟩ := sec1011_exists_conjAut hα2
  have hy0 : ((sec1011_tA t S L * sec1011_phiA t S L φ sec1011_w0 : ↥(secA t S L)) : G) =
      t * φ sec1011_w0 := by
    show t * ((sec1011_phiA t S L φ sec1011_w0 : ↥(secA t S L)) : G) = _
    rw [sec1011_phiA_coe hs sec1011_w0_even]
  have hfix : ∀ (n : G) (hn : n ∈ normalizer (secA t S L : Set G)),
      sec1011_conjAut (secA t S L) n hn (sec1011_tA t S L * sec1011_phiA t S L φ sec1011_w0) =
        sec1011_tA t S L * sec1011_phiA t S L φ sec1011_w0 →
      n * (t * φ sec1011_w0) * n⁻¹ = t * φ sec1011_w0 := by
    intro n hn h
    have h' := congrArg Subtype.val h
    rw [sec1011_conjAut_apply, hy0] at h'
    exact h'
  have hcube : ∀ (n : G) (hn : n ∈ normalizer (secA t S L : Set G)),
      sec1011_conjAut (secA t S L) n hn ^ 3 = 1 →
      ∀ b ∈ secB S L, n ^ 3 * b * (n ^ 3)⁻¹ = b := by
    intro n hn h b hb
    have h3 : sec1011_conjAut (secA t S L) (n ^ 3) ((normalizer (secA t S L : Set G)).pow_mem hn 3)
        = 1 := by
      rw [sec1011_conjAut_pow hn 3, h]
    have h' := congrArg Subtype.val
      (DFunLike.congr_fun h3 (⟨b, sec1011_B_le_A t S L hb⟩ : ↥(secA t S L)))
    rw [sec1011_conjAut_apply] at h'
    exact h'
  have hc1' := hcube n1 hn1N hc1
  have hc2' := hcube n2 hn2N hc2
  have hB1 : ∀ b ∈ secB S L, n1 * b * n1⁻¹ ∈ secB S L := fun b hb => hs.hBM n1 hn1M b hb
  have hB2 : ∀ b ∈ secB S L, n2 * b * n2⁻¹ ∈ secB S L := fun b hb => hs.hBM n2 hn2M b hb
  refine ⟨n1, hn1M, n2, hn2M, hfix n1 hn1N hf1, hfix n2 hn2N hf2, ?_, fun b hb => ?_,
    fun b hb => ?_, ?_⟩
  · intro b hb
    have hcm : ∀ b ∈ secB S L, n1 * (n2 * b * n2⁻¹) * n1⁻¹ = n2 * (n1 * b * n1⁻¹) * n2⁻¹ := by
      intro b hb
      have h' := congrArg Subtype.val
        (DFunLike.congr_fun hcomm (⟨b, sec1011_B_le_A t S L hb⟩ : ↥(secA t S L)))
      simp only [MulAut.mul_apply] at h'
      rw [sec1011_conjAut_apply, sec1011_conjAut_apply] at h'
      rw [sec1011_conjAut_apply, sec1011_conjAut_apply] at h'
      exact h'
    rw [sec1011_pow4_act hc2' hb, sec1011_pow4_act hc1' hb,
      sec1011_pow4_act hc1' (hB2 b hb), sec1011_pow4_act hc2' (hB1 b hb)]
    exact hcm b hb
  · exact sec1011_pow12 hc1' hb
  · exact sec1011_pow12 hc2' hb
  · intro b hb
    have hb' : (⟨b, sec1011_B_le_A t S L hb⟩ : ↥(secA t S L)) ∈ sec1011_BA t S L :=
      sec1011_mem_BA.mpr hb
    obtain ⟨b1, hb1, b2, hb2, hbeq⟩ := hspan _ hb'
    have h' := congrArg Subtype.val hbeq
    refine ⟨(b1 : G), sec1011_mem_BA.mp hb1, (b2 : G), sec1011_mem_BA.mp hb2, ?_⟩
    rw [sec1011_pow4_act hc1' (sec1011_mem_BA.mp hb1),
      sec1011_pow4_act hc2' (sec1011_mem_BA.mp hb2)]
    simp only [Subgroup.coe_mul] at h'
    rw [sec1011_conjAut_apply, sec1011_conjAut_apply] at h'
    exact h'

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourCentral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

open CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace EndGame

open SectionSix Involution Fusion

theorem false_of_dihedral_central {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    (P : Sylow 2 X) {n : ℕ} (hn : 2 ≤ n) (e : (P : Subgroup X) ≃* DihedralGroup (2 ^ (n - 1)))
    {z : X} (hz : z ∈ Subgroup.center X) (hz2 : orderOf z = 2) : False := by
  obtain ⟨-, -, -, -, hconj⟩ :=
    CFSG.Semidihedral.Principal.dihedral_derived_involutions_conjugate P hn ⟨e.symm⟩
  have hall := hconj hX.commutator_eq_top
  have hcentral : ∀ w : X, orderOf w = 2 → w = z := by
    intro w hw
    obtain ⟨c, hc⟩ := isConj_iff.mp (hall w z hw hz2)
    have hzc : c⁻¹ * z = z * c⁻¹ := Subgroup.mem_center_iff.mp hz c⁻¹
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [hc]
      _ = z := by rw [hzc]; group
  have hN : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Fact (1 < 2 ^ (n - 1)) := ⟨by omega⟩
  have hinv : ∀ i : ZMod (2 ^ (n - 1)), orderOf ((e.symm (DihedralGroup.sr i) : P) : X) = 2 := by
    intro i
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  apply (zero_ne_one : (0 : ZMod (2 ^ (n - 1))) ≠ 1)
  have h01 := (hcentral _ (hinv 0)).trans (hcentral _ (hinv 1)).symm
  have h01' : e.symm (DihedralGroup.sr 0) = e.symm (DihedralGroup.sr 1) := Subtype.ext h01
  have := e.symm.injective h01'
  simp at this

end EndGame

open SectionSix Involution Fusion EndGame

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem counterexample_false (hin : SectionSevenInputs) (hC : Counterexample G D r Abar) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hC.hyp
  have hr2 := hin.lemma_8_2 hC
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin r, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨SD, hSD⟩ := exists_isSylowOf 2 D
  have hDN : ∀ k, D ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G) := by
    intro k
    have : (Abar k).Normal := commuting_factors_normal Abar hyp.hcomm hyp.hgen k
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
      (preimage_normal D (Abar k))
  have hT : ∀ k, IsSylowOf 2 (SD ⊓ aschbacherThm5Preimage D (Abar k))
      (aschbacherThm5Preimage D (Abar k)) := fun k =>
    hSD.inf_of_le_normalizer (preimage_le D _) (hDN k)
  obtain ⟨S, hSDS⟩ := hSD.isPGroup.exists_le_sylow
  have hTS : ∀ k, SD ⊓ aschbacherThm5Preimage D (Abar k) ≤ S := fun k =>
    inf_le_left.trans hSDS
  have hcomm : ⁅SD ⊓ aschbacherThm5Preimage D (Abar i₀),
      SD ⊓ aschbacherThm5Preimage D (Abar i₁)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨hxS, hxA⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyS, hyA⟩ := Subgroup.mem_inf.mp hy
    have hxD : x ∈ D := preimage_le D _ hxA
    have hyD : y ∈ D := preimage_le D _ hyA
    set xd : D := ⟨x, hxD⟩
    set yd : D := ⟨y, hyD⟩
    have hq : QuotientGroup.mk' (aschbacherThm5OddCore D) (xd * yd * xd⁻¹ * yd⁻¹) = 1 := by
      have hxy := hyp.hcomm i₀ i₁ h01 _ ((mem_preimage_iff D _ xd).mp hxA) _
        ((mem_preimage_iff D _ yd).mp hyA)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    have hodd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) hq
    have hcS : x * y * x⁻¹ * y⁻¹ ∈ SD :=
      SD.mul_mem (SD.mul_mem (SD.mul_mem hxS hyS) (SD.inv_mem hxS)) (SD.inv_mem hyS)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hSD.isPGroup) ⟨_, hcS⟩
    rw [Subgroup.orderOf_mk] at hm
    have hcoe : ((xd * yd * xd⁻¹ * yd⁻¹ : D) : G) = x * y * x⁻¹ * y⁻¹ := rfl
    rw [← Subgroup.orderOf_coe, hcoe, hm] at hodd
    have hm0 : m = 0 := by
      by_contra h0
      exact (Nat.not_even_iff_odd.mpr (oddCore_odd D))
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 h0).trans hodd))
    rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
    rw [Subgroup.mem_bot, commutatorElement_def]
    exact hm
  have hrank : ∀ k, 2 ≤ CFSG.Open.pRank 2 (SD ⊓ aschbacherThm5Preimage D (Abar k)) := by
    intro k
    obtain ⟨Q, hQ⟩ := hT k
    rw [← hQ, AschbacherKnownGroup.Lemma38.pRank_sylow_map]
    exact lemma_8_3 hin hC k
  obtain ⟨hc1, hc2, hc3⟩ := lemma_8_4 hin hC h01 (hT i₀) (hT i₁) S (hTS i₀) (hTS i₁)
  rcases hin.lemma_3_4 S _ _ (hTS i₀) (hTS i₁) hcomm (hrank i₀) (hrank i₁) hc1 hc2 hc3 with
    h | h | h | ⟨-, hshape, hcard⟩
  · apply hC.proper
    rw [eq_top_iff, ← h]
    exact overlapClosure_le hC (hT i₀).le (hT i₁).le (hT i₀).isPGroup (hT i₁).isPGroup
  · exact false_of_sylow_le hyp h01 (hT i₀) (h.trans (hT i₁).le)
  · exact false_of_sylow_le hyp h01.symm (hT i₁) (h.trans (hT i₀).le)
  ·
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥((SD ⊓
      aschbacherThm5Preimage D (Abar i₀)) ⊓ (SD ⊓ aschbacherThm5Preimage D (Abar i₁)))) 2
      (by rw [hcard])
    have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz]
    obtain ⟨hz₀, hz₁⟩ := Subgroup.mem_inf.mp z.2
    have hzA₀ := (Subgroup.mem_inf.mp hz₀).2
    have hzA₁ := (Subgroup.mem_inf.mp hz₁).2
    have hzD : (z : G) ∈ D := preimage_le D _ hzA₀
    have hq₀ := (mem_preimage_iff D _ ⟨z, hzD⟩).mp hzA₀
    have hq₁ := (mem_preimage_iff D _ ⟨z, hzD⟩).mp hzA₁
    set zb : Abar i₀ := ⟨_, hq₀⟩
    have hzc : zb ∈ Subgroup.center (Abar i₀) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hyp.hcomm i₀ i₁ h01 y y.2 _ hq₁)
    have hzb2 : orderOf zb = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_mk_eq_two hz2
    have hperf : Group.IsPerfect (Abar i₀) := semisimple_perfect _ (hyp.hsemisimple i₀)
    obtain ⟨P, ⟨eP⟩, -⟩ := exists_sylow_image (Abar i₀) (hT i₀)
    rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact false_of_dihedral_central hperf P hn (eP.symm.trans e) hzc hzb2
    · exact SevenFour.semidihedral_perfect_no_central_involution hperf P hn
        ⟨eP.symm.trans e⟩ hzc hzb2

end CFSG.ComponentClassification.AschbacherTheorem5

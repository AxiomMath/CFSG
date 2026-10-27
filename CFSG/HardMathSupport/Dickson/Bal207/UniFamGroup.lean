module

public import CFSG.HardMathSupport.Dickson.Bal207.UniLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

variable {X : Type} [Group X] {K : Subgroup X} {S : Type} [Group S]
  (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)

theorem uni_mem_normalizer_of_map [Finite X] {J : Subgroup X} (hJK : J ≤ K) (hJ : ⁅J, J⁆ = J)
    {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hinv : ∀ s ∈ (J.comap K.subtype).map (uniMap e),
      uniAut e ⟨g, hg⟩ s ∈ (J.comap K.subtype).map (uniMap e)) :
    g ∈ Subgroup.normalizer (J : Set X) := by
  set J₀ : Subgroup ↥K := J.comap K.subtype with hJ₀
  have hJ₀map : J₀.map K.subtype = J :=
    Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hJ₀perf : ⁅J₀, J₀⁆ = J₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hJ₀map, hJ]
  set γ₀ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩ with hγ₀
  have h3 : J₀.map γ₀.toMonoidHom ≤ J₀ ⊔ Subgroup.center ↥K := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 : uniMap e (γ₀ j) ∈ J₀.map (uniMap e) := by
      rw [show uniMap e (γ₀ j) = uniAut e ⟨g, hg⟩ (uniMap e j) from (uniAut_uniMap e _ j).symm]
      exact hinv _ ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hj'e⟩ := h1
    have hz : j'⁻¹ * γ₀ j ∈ Subgroup.center ↥K := by
      rw [← uniMap_eq_one_iff e, map_mul, map_inv, hj'e, inv_mul_cancel]
    have hmem : j' * (j'⁻¹ * γ₀ j) ∈ J₀ ⊔ Subgroup.center ↥K := Subgroup.mul_mem_sup hj' hz
    rw [mul_inv_cancel_left] at hmem
    exact hmem
  have hPperf : ⁅J₀.map γ₀.toMonoidHom, J₀.map γ₀.toMonoidHom⁆ = J₀.map γ₀.toMonoidHom := by
    rw [← Subgroup.map_commutator, hJ₀perf]
  have h4 : J₀.map γ₀.toMonoidHom ≤ J₀ := le_of_perfect_of_le_sup_center hJ₀perf hPperf h3
  have h5 : J₀.map γ₀.toMonoidHom = J₀ :=
    Subgroup.eq_of_le_of_card_ge h4
      (Subgroup.card_map_of_injective (f := γ₀.toMonoidHom) γ₀.injective).ge
  apply mem_normalizer_of_map_conj_eq
  have hcomp : (MulAut.conj g).toMonoidHom.comp K.subtype = K.subtype.comp γ₀.toMonoidHom := by
    ext k
    rfl
  rw [← hJ₀map, Subgroup.map_map, hcomp, ← Subgroup.map_map, h5]

theorem uni_exists_comm_of_fixed [Finite X] {p : ℕ} (hp : p.Prime) {B J : Subgroup X}
    (hB : IsSCp p ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center ↥K)))
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hpJ : p ∣ Nat.card ↥J)
    (hmem : ∀ y : ↥K, y ^ p = 1 → uniMap e y ∈ (J.comap K.subtype).map (uniMap e) →
      (y : X) ∈ J)
    {s : S} (hs : s ∈ (J.comap K.subtype).map (uniMap e)) (hsp : s ^ p = 1)
    (hfix : ∀ (b : X) (hb : b ∈ B), uniAut e ⟨b, hBK hb⟩ s = s)
    (hsZ : (⟨s, hs⟩ : ↥((J.comap K.subtype).map (uniMap e))) ∉
      Subgroup.center ↥((J.comap K.subtype).map (uniMap e))) :
    ∃ y ∈ B, y ∈ J ∧ ∃ z ∈ J, ⁅y, z⁆ ∉ GLAPPrimeCoreOf p J := by
  obtain ⟨y, hyB, hyK, hyψ⟩ := uni_exists_mem_of_fixed hB hBK hZ e hsp hfix
  have hyp : (⟨y, hyK⟩ : ↥K) ^ p = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2.1.2 y hyB)
  have hyJ : y ∈ J := hmem ⟨y, hyK⟩ hyp (by rw [hyψ]; exact hs)
  have hyZ : (⟨y, hyJ⟩ : ↥J) ∉ Subgroup.center ↥J := by
    intro hc
    apply hsZ
    have h1 : uniRestr e hJK ⟨y, hyJ⟩ = ⟨s, hs⟩ := Subtype.ext hyψ
    rw [← h1, Subgroup.mem_center_iff]
    intro t
    obtain ⟨j, rfl⟩ := uniRestr_surjective e hJK t
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc j]
  obtain ⟨z, hzJ, hz⟩ := uni_exists_comm_not_mem_core hp hJ hpJ hyJ hyZ
  exact ⟨y, hyB, hyJ, z, hzJ, hz⟩

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end

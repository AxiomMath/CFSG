module

public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Red

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_inndiag_involution_of_klein (hF : L2Field F) (e : K ≃* L2 F)
    {B : Subgroup (MulAut K)} (hB4 : Nat.card ↥B = 4) (hBsq : ∀ b ∈ B, b ^ 2 = 1) :
    ∃ w ∈ B, w ≠ 1 ∧ w ∈ innDiagSub e := by
  obtain ⟨hcyc, ⟨ε⟩, -⟩ := ivk_1_2e F hF K e
  have hcycF : IsCyclic (F ≃+* F) := isCyclic_of_surjective ε.toMonoidHom ε.surjective
  let f : ↥B →* (F ≃+* F) := (fieldProj e).comp B.subtype
  have hcard := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card ↥f.range ≤ 2 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥f.range)
    have hg2 : g ^ 2 = 1 := by
      obtain ⟨b, hb⟩ := g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hb, ← map_pow]
      have : b ^ 2 = 1 := Subtype.ext (hBsq b b.2)
      rw [this, map_one]
      rfl
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  have hker : 2 ≤ Nat.card ↥f.ker := by
    have hpos : 0 < Nat.card ↥f.range := Nat.card_pos
    by_contra h
    have h1 : Nat.card ↥f.ker ≤ 1 := by omega
    have h2 : Nat.card ↥f.ker * Nat.card ↥f.range ≤ 1 * 2 := Nat.mul_le_mul h1 hrange
    omega
  have hne : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hker
    omega
  obtain ⟨⟨b, hb1⟩, hb2⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  refine ⟨b, b.2, fun h => hb2 ?_, (mem_innDiagSub_iff e b).2 hb1⟩
  exact Subtype.ext (Subtype.ext h)

theorem exists_equiv_pgl2_fixedSubgroup (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e)
    {y : MulAut K} (hy2 : y ^ 2 = 1) (hyD : y ∉ innDiagSub e) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ ^ 2 = Nat.card F ∧
      Nonempty (↥(fixedSubgroup K y) ≃* PGL2 F₀) := by
  have hyInn : y ∉ innAut K := fun h => hyD (innAut_le_innDiagSub e h)
  obtain ⟨g, hg, hyg⟩ := fieldAutHom_fieldProj_mul e y
  have hσ1 : fieldProj e y ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e y).2 h)
  have hσ2 : fieldProj e y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hσo : orderOf (fieldProj e y) = 2 := orderOf_eq_prime hσ2 hσ1
  have hf1 : fieldAutHom e (fieldProj e y) ≠ 1 := fun h =>
    hσ1 (fieldAutHom_injective e (h.trans (map_one _).symm))
  have hf2 : fieldAutHom e (fieldProj e y) ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hfo : orderOf (fieldAutHom e (fieldProj e y)) = 2 := orderOf_eq_prime hf2 hf1
  have hfF : fieldAutHom e (fieldProj e y) ∈ fieldAutSub e := ⟨_, rfl⟩
  have hfT : fieldAutHom e (fieldProj e y) ∈ (N.T : Subgroup (MulAut K)) := by
    have hP : IsPGroup 2 ↥(zpowers (fieldAutHom e (fieldProj e y))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo]; norm_num)
    have h1 := hP.inf_normalizer_sylow N.T
    have h2 : fieldAutHom e (fieldProj e y) ∈
        zpowers (fieldAutHom e (fieldProj e y)) ⊓ normalizer (N.T : Set (MulAut K)) :=
      ⟨mem_zpowers _, N.T_inv hfF⟩
    rw [h1] at h2
    exact h2.2
  have hyo : orderOf (g * fieldAutHom e (fieldProj e y)) = 2 := by
    rw [← hyg]
    exact orderOf_eq_prime hy2 (fun h => hyInn (by rw [h]; exact one_mem _))
  obtain ⟨a, -, hay⟩ := ivk_1_2h_c F hF K e N _ ⟨hfT, hfF⟩ hfo g hg hyo
  rw [← hyg] at hay
  obtain ⟨F₀, i1, i2, hF₀, ⟨φ⟩⟩ :=
    (ivk_1_4a F hF K e (fieldProj e y)).2.2 (by rw [hσo]; exact even_two)
  rw [hσo] at hF₀
  exact ⟨F₀, i1, i2, hF₀, ⟨(fixedSubgroupEquivOfConj hay).trans φ⟩⟩

theorem card_fixedSubgroup_outer (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e)
    {y : MulAut K} (hy2 : y ^ 2 = 1) (hyD : y ∉ innDiagSub e) :
    ∃ q₀ : ℕ, q₀ ^ 2 = Nat.card F ∧ Nat.card ↥(fixedSubgroup K y) = q₀ * (q₀ ^ 2 - 1) := by
  obtain ⟨F₀, _, _, hF₀, ⟨φ⟩⟩ := exists_equiv_pgl2_fixedSubgroup hF e N hy2 hyD
  exact ⟨Nat.card F₀, hF₀, by rw [Nat.card_congr φ.toEquiv, pgl2_card_formula]⟩

end Red

end CFSG.GH74.GLS.IVK.Proofs2

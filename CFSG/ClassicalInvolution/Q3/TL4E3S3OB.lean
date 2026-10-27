module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OQ8
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OSteps

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y}
  {R' T W : Subgroup Y}

namespace Ctx

variable (h : Ctx n R S t J u L Rd Sd S' R' T W)
include h

theorem core_le_centralizer_a : tightCore R ≤ Subgroup.centralizer ({u * t} : Set Y) := by
  intro x hx
  have hxu := Subgroup.mem_centralizer_singleton_iff.mp (h.frame.core_le_centralizer hx)
  have hxt : x * t * x⁻¹ = t :=
    h.frame.large.datum.isUniqueInvolution_core.conj_eq (conjSub_eq_self_of_mem hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (u * t) = (x * u) * t := by group
    _ = (u * x) * t := by rw [hxu]
    _ = u * (x * t * x⁻¹) * x := by group
    _ = u * t * x := by rw [hxt]

theorem exists_sqrt {s : Y} (hs : IsUniqueInvolution L s) :
    ∃ v ∈ L, v ∈ Subgroup.normalizer (tightCore R : Set Y) ∧ orderOf v = 4 ∧ v * v = s := by
  have hΩG := h.frame.large.datum.hypOmegaGen
  have hR3 := TightLargeHypR.typeRFam h.frame.large
  obtain ⟨-, -, U, hU, hUL, hUN⟩ := h.star
  obtain ⟨Ru, -, Lu, hLu, hRuLu, -, hUcyc, hRU, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  obtain ⟨eR⟩ := hR3.quat Lu hLu Ru hRuLu
  have eR2 : ↥Ru ≃* QuaternionGroup 2 := eR
  have h8 : Nat.card Ru = 8 := by
    rw [Nat.card_congr eR2.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hU4 : Nat.card U = 4 := by omega
  obtain ⟨g, hg⟩ := hUcyc.exists_generator
  have hgo : orderOf (g : Y) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hU4]
  refine ⟨g, hUL g.2, hUN g.2, hgo, ?_⟩
  have h4 := pow_orderOf_eq_one (g : Y)
  rw [hgo] at h4
  have hsq : (g : Y) * g * ((g : Y) * g) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rcases hs.unique ((g : Y) * g) (L.mul_mem (hUL g.2) (hUL g.2)) hsq with h1 | h1
  · exfalso
    have h2 : orderOf (g : Y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hgo] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)
  · exact h1

theorem exists_conj_sylow {s : Y} (hs : IsUniqueInvolution L s) :
    ∃ Q₀, IsSylow2In Q₀ (tightCore R) ∧ ∃ w₀ ∈ Q₀, w₀ * w₀ ≠ 1 ∧ w₀ ^ 4 = 1 ∧
      ∀ x ∈ Q₀, s * x * s⁻¹ = w₀ * x * w₀⁻¹ := by
  classical
  have hΩG := h.frame.large.datum.hypOmegaGen
  have hR3 := TightLargeHypR.typeRFam h.frame.large
  obtain ⟨v, hvL, hvN, hvo, hvs⟩ := h.exists_sqrt hs
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hvo]; norm_num)
  obtain ⟨Q₀, hQ₀, hQ₀N⟩ := exists_isSylow2In_normalized hv2 (Subgroup.zpowers_le.mpr hvN)
  have hvQ : conjSub v Q₀ = Q₀ := mem_normalizer_iff_conjSub_eq.mp (hQ₀N (Subgroup.mem_zpowers v))
  obtain ⟨e⟩ := hR3.quat _ (CoreAssembly.mem_conjClass_self _) Q₀ hQ₀
  have e2 : ↥Q₀ ≃* QuaternionGroup 2 := e
  let β : ↥Q₀ ≃* ↥Q₀ := ((MulAut.conj v).subgroupMap Q₀).trans (MulEquiv.subgroupCongr hvQ)
  have hβv : ∀ x : ↥Q₀, ((β x : ↥Q₀) : Y) = v * x * v⁻¹ := fun x => rfl
  let γ : QuaternionGroup 2 ≃* QuaternionGroup 2 := (e2.symm.trans β).trans e2
  have hγ : ∀ y, γ (γ y) = e2 (β (β (e2.symm y))) := fun y => by
    show e2 (β (e2.symm (e2 (β (e2.symm y))))) = _
    rw [MulEquiv.symm_apply_apply]
  have hv4 : v * v * (v * v) = 1 := by rw [hvs]; exact hs.sq
  have hββ : ∀ x : ↥Q₀, ((β (β x) : ↥Q₀) : Y) = s * x * s⁻¹ := fun x => by
    rw [hβv, hβv, ← hvs]
    group
  have h4 : ∀ y, γ (γ (γ (γ y))) = y := by
    intro y
    rw [hγ, hγ, MulEquiv.symm_apply_apply]
    rw [show β (β (β (β (e2.symm y)))) = e2.symm y from Subtype.ext (by
      rw [hββ, hββ, ← hvs]
      calc v * v * (v * v * ↑(e2.symm y) * (v * v)⁻¹) * (v * v)⁻¹ =
          (v * v * (v * v)) * ↑(e2.symm y) * (v * v * (v * v))⁻¹ := by group
        _ = ↑(e2.symm y) := by rw [hv4]; group)]
    exact MulEquiv.apply_symm_apply e2 y
  have h2 : ∃ y, γ (γ y) ≠ y := by
    by_contra hcon
    have hc : ∀ y, γ (γ y) = y := fun y => not_not.mp fun hy => hcon ⟨y, hy⟩
    apply h.notNbr
    have hQs : Q₀ ≤ Subgroup.centralizer ({s} : Set Y) := by
      intro x hx
      have h1 := hc (e2 ⟨x, hx⟩)
      rw [hγ, MulEquiv.symm_apply_apply] at h1
      have h3 : ((β (β ⟨x, hx⟩) : ↥Q₀) : Y) = x := congrArg Subtype.val (e2.injective h1)
      rw [hββ] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * s = (s * x * s⁻¹) * s := by rw [h3]
        _ = s * x := by group
    have hLΩ := h.star.1
    have hK₀L : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L :=
      ⟨CoreAssembly.mem_conjClass_self _, fun e => h.star.2.1 e.symm, Q₀,
        mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hQ₀, hQ₀.1,
        hQs.trans (hR3.tight L hLΩ s hs)⟩
    exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hLΩ (CoreAssembly.mem_conjClass_self _) hK₀L
  obtain ⟨g, hgg, hgx⟩ := q8_sq_inner γ h4 h2
  refine ⟨Q₀, hQ₀, (e2.symm g : Y), (e2.symm g).2, fun h1 => hgg ?_, ?_, fun x hx => ?_⟩
  · apply e2.symm.injective
    rw [map_mul, map_one]
    exact Subtype.ext h1
  · have h3 := congrArg (fun q => ((e2.symm q : ↥Q₀) : Y)) (q8_pow_four g)
    simpa only [map_pow, map_one, Subgroup.coe_pow, OneMemClass.coe_one] using h3
  · have h1 := hgx (e2 ⟨x, hx⟩)
    rw [hγ, MulEquiv.symm_apply_apply] at h1
    have h3 := congrArg (fun q => ((e2.symm q : ↥Q₀) : Y)) h1
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] at h3
    rw [← hββ ⟨x, hx⟩]
    exact h3

end Ctx

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4

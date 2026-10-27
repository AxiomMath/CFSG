module

public import CFSG.ClassicalInvolution.Q3.Q3T7M06
public import CFSG.ClassicalInvolution.Q3.Q3T7K02
public import CFSG.ClassicalInvolution.Q3.Q3T7EndF4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77

section Assembly


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem MinCex.ofMinCex3 (ob : EInputs) (c : Q3T7E.MinCex3 Ω K S R W H) :
    MinCex Ω K S R W H where
  stand := EStand.of_stand3 ob c.stand
  hyp := c.hyp
  proper := c.proper
  minimal := fun G _ _ hlt Ω' K' S' R' W' H' hst hH =>
    c.minimal G hlt Ω' K' S' R' W' H' hst.toStand3 hH

theorem e189Model3_proved : E189Model3 :=
  CFSG.ClassicalInvolution.Q3.Q3T7E9.e189ModelAt_three_all

theorem e18_6_proved : E18_6 :=
  AscE186.e18_6_of_wfree (fun _ _ _ _ _ _ _ _ _ c => c.hyp.cent)
    (fun _ _ _ _ _ _ _ _ _ c Gb _ _ hlt Ωb Kb Sb Rb Wb Hb hst ht hcn =>
      c.minimal Gb hlt Ωb Kb Sb Rb Wb Hb hst ⟨ht, hcn⟩)

theorem e18_7_proved : E18_7 :=
  e18_7 ⟨l6_7_proved, l6_9_proved, l6_11_proved, e18_6_proved⟩ e18_4C3

theorem e18_8z_proved : E18_8z :=
  e18_8z_of_e18_7 e18_7_proved

theorem e18_9_proved : E18_9 :=
  e18_9 (e18_3 l6_7_proved) e18_6_proved e18_7_proved (E189E4.of_e187 e18_4C3)
    (e189Sect_of_model e189Model3_proved)

theorem isClassicalMember3_of_isUniqueInvolution (hΩ : Q3T7M.HM Ω) (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : Q3.IsClassicalMember3 K z := by
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have h3 := hz'.toQ3 (by norm_num)
  have hz'2 : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [h3.orderOf_eq_two, pow_two] at this
  have : z' = z := (hz.unique z' h3.mem hz'2).resolve_left h3.ne_one
  rwa [this] at h3

theorem e18_endS3 (c : MinCex Ω K S R W H)
    (hF : ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥)
    {z : G} (hz : IsUniqueInvolution K z)
    (hSyl : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (h1 : FixesUniqueCoset z H)
    (h2S : ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
      z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) :
    False := by
  obtain ⟨F, hFn, hFs, hFnab, hFc⟩ := hF
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hK : Q3.IsClassicalMember3 K z :=
    isClassicalMember3_of_isUniqueInvolution c.stand.hyp c.stand.mem hz
  exact Q3T8.false_of_uniqueCoset_of_weakMember3_F hFs hFnab hFc c.proper hz2 h1
    (CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_mul_of_isSylow2In hz2 hSyl h2S) hK

theorem minCexFalse_proved : MinCexFalse := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz1, -⟩ := c.exists_centralizer_le
  obtain ⟨S', W', c', hSyl⟩ := c.exists_config_sylow_centralizer hz1
  obtain ⟨-, hF⟩ := e18_6_proved G Ω K S' R W' H c'
  have hzc : FixesUniqueCoset z H := e18_8z_proved G Ω K S' R W' H c' z hz1
  exact e18_endS3 c' hF hz1 hSyl hzc fun h h1 h2 h3 =>
    e18_9_proved G Ω K S' R W' H c' z hz1 h h1 h2 h3

theorem thmE3_proved (ob : EInputs) : Q3T7E.ThmEWithSylow3 :=
  Q3T7E.thmEWithSylow3_of_minCexFalse fun G _ _ Ω K S R W H c =>
    minCexFalse_proved G Ω K S R W H (MinCex.ofMinCex3 ob c)

theorem thmE3_of_qs3 (hQ : Q3.QuasisimpleConnected3) : Q3T7E.ThmEWithSylow3 :=
  thmE3_proved (EInputs.of_qs3 hQ)

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

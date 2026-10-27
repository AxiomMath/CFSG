module

public import CFSG.LargeExtraspecial.Asc611Defs
public import CFSG.LargeExtraspecial.AS35NLemmaZ
public import CFSG.LargeExtraspecial.AS35KFus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem two_pow_width_le_card_cqx {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) :
    2 ^ S.width ≤ Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h1 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
  have h2 := Submodule.finrank_mono (commSpace_le_fixSpace (S.rhoL_mul_self hxM hxx))
  have h3 := S.finrank_fixSpace_le hxM
  have h4 := S.finrank_Qt_eq_two_mul_width
  have hcard : Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) =
      2 * 2 ^ finrank (ZMod 2) (S.cqxSub x) := by
    rw [← S.clPre_cqxSub hxM, S.card_clPre, S.card_submodule]
  rw [hcard]
  calc 2 ^ S.width ≤ 2 ^ (finrank (ZMod 2) (S.cqxSub x) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ finrank (ZMod 2) (S.cqxSub x) := by rw [pow_succ, mul_comm]

omit [Finite G] in
theorem mem_Qa_iff_asc611 {g y : G} : y ∈ S.Qa g ↔ g⁻¹ * y * g ∈ S.QG := by
  rw [Qa_eq_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [mul_assoc] using hq
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [mul_assoc]⟩

end Setting

namespace S14

theorem aschbacherSixElevenFusionMStmt_of_unitaryCent
    (hU : AschbacherUnitaryCentStmt) :
    AschbacherSixElevenFusionMStmt := by
  intro G _ _ S _ hS h65 h69 h610 hQX hMX _ hA2 g hgM
  by_contra hgB
  obtain ⟨m, hm, ψ, hψ, hC⟩ := S.exists_unitary_model_BStab hS h65 h69 h610 hQX hMX hA2
  have hMX' : S.M ≤ S.BStab := S.M_le_BStab hS h69
  set a : S.BStab := ⟨g * S.z * g⁻¹, hMX' hgM⟩ with ha
  set U : Subgroup S.BStab := (S.Qa g).comap S.BStab.subtype with hUdef
  have hmemU : ∀ u : S.BStab, u ∈ U ↔ g⁻¹ * (u : G) * g ∈ S.QG := fun u => by
    rw [hUdef, mem_comap, Subgroup.coe_subtype, S.mem_Qa_iff_asc611]
  have hDB : ∀ l : (S.restrict S.BStab hQX hMX).zGen, ψ l ∈ DG m →
      ((l : S.BStab) : G) ∈ S.BSet := fun l hl =>
    S.mem_BSet_of_isConj_zL hS h69 hQX hMX ((hψ l).mpr hl)
  have ha2 : a * a = 1 := Subtype.ext (by
    simp only [ha, Subgroup.coe_mul, Subgroup.coe_one]
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
    group)
  have ha1 : a ≠ 1 := fun h => by
    have h1 : g * S.z * g⁻¹ = 1 := congrArg Subtype.val h
    apply S.z_ne_one
    calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have haL : ∀ l : (S.restrict S.BStab hQX hMX).zGen, (l : S.BStab) = a → ψ l ∉ DG m :=
      fun l hl hD => by
    have h1 := hDB l hD
    rw [hl] at h1
    exact hgB h1
  have hU2 : IsPGroup 2 U :=
    (S.conjBy g).isPGroup_QG.comap_of_injective S.BStab.subtype S.BStab.subtype_injective
  have haU : a ∈ U := by
    rw [hmemU, show g⁻¹ * (g * S.z * g⁻¹) * g = S.z by group]
    exact S.z_mem_QG
  have hcommQa : ∀ y : G, g⁻¹ * y * g ∈ S.QG → y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y := by
    intro y hy
    have h1 := S.z_comm_QG hy
    calc y * (g * S.z * g⁻¹) = g * ((g⁻¹ * y * g) * S.z) * g⁻¹ := by group
      _ = g * (S.z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * S.z * g⁻¹ * y := by group
  have hUC : U ≤ centralizer ({a} : Set S.BStab) := fun u hu => by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul, ha] using hcommQa _ ((hmemU u).mp hu))
  have hUN : ∀ c ∈ centralizer ({a} : Set S.BStab), ∀ u ∈ U, c * u * c⁻¹ ∈ U := by
    intro c hc u hu
    rw [mem_centralizer_singleton_iff] at hc
    have hc' : (c : G) * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * (c : G) := by
      have := congrArg Subtype.val hc
      simpa only [Subgroup.coe_mul, ha] using this
    have hcM : g⁻¹ * (c : G) * g ∈ S.M := by
      rw [S.mem_M_iff]
      calc g⁻¹ * (c : G) * g * S.z = g⁻¹ * ((c : G) * (g * S.z * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * S.z * g⁻¹ * (c : G)) * g := by rw [hc']
        _ = S.z * (g⁻¹ * (c : G) * g) := by group
    rw [hmemU]
    have h1 := S.conj_mem_QG hcM ((hmemU u).mp hu)
    rw [show g⁻¹ * ((c * u * c⁻¹ : S.BStab) : G) * g =
      g⁻¹ * (c : G) * g * (g⁻¹ * (u : G) * g) * (g⁻¹ * (c : G) * g)⁻¹ by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group]
    exact h1
  have hUL : ∀ l : (S.restrict S.BStab hQX hMX).zGen, (l : S.BStab) ∈ U → ψ l ∉ DG m := by
    intro l hlU hD
    have hB := hDB l hD
    obtain ⟨h, hh⟩ := isConj_iff.mp (S.isConj_of_mem_BAt hB)
    have hQ : (g⁻¹ * h) * S.z * (g⁻¹ * h)⁻¹ ∈ S.QG := by
      have h1 := (hmemU _).mp hlU
      rw [← hh] at h1
      rwa [show (g⁻¹ * h) * S.z * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * S.z * h⁻¹) * g by group]
    have h2 := hS.weak _ hQ
    have h3 : h * S.z * h⁻¹ = g * S.z * g⁻¹ := by
      calc h * S.z * h⁻¹ = g * ((g⁻¹ * h) * S.z * (g⁻¹ * h)⁻¹) * g⁻¹ := by group
        _ = g * S.z * g⁻¹ := by rw [h2]
    rw [← hh, h3] at hB
    exact hgB hB
  have hle := hU S.BStab (S.restrict S.BStab hQX hMX).zGen
    (S.restrict S.BStab hQX hMX).zGen_normal m hm ψ hC a ha2 ha1 haL U hU2 haU hUC hUN hUL
  have hxM : g⁻¹ * S.z * g ∈ S.M := by
    rw [S.mem_M_iff]
    have h1 := S.mem_M_iff.mp hgM
    calc g⁻¹ * S.z * g * S.z = g⁻¹ * (S.z * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * S.z) * g := by rw [h1]
      _ = S.z * (g⁻¹ * S.z * g) := by group
  have hxx : g⁻¹ * S.z * g * (g⁻¹ * S.z * g) = 1 := by
    rw [show g⁻¹ * S.z * g * (g⁻¹ * S.z * g) = g⁻¹ * (S.z * S.z) * g by group, S.z_mul_z]
    group
  have hcard := S.two_pow_width_le_card_cqx hxM hxx
  have hconjM : ∀ y : G, y ∈ centralizer ({g⁻¹ * S.z * g} : Set G) → g * y * g⁻¹ ∈ S.M := by
    intro y hy
    rw [S.mem_M_iff]
    have h1 := mem_centralizer_singleton_iff.mp hy
    calc g * y * g⁻¹ * S.z = g * (y * (g⁻¹ * S.z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * S.z * g) * y) * g⁻¹ := by rw [h1]
      _ = S.z * (g * y * g⁻¹) := by group
  let f : ↥(S.QG ⊓ centralizer ({g⁻¹ * S.z * g} : Set G)) → U := fun y =>
    ⟨⟨g * (y : G) * g⁻¹, hMX' (hconjM _ (mem_inf.mp y.2).2)⟩, by
      rw [hmemU, show g⁻¹ * (g * (y : G) * g⁻¹) * g = (y : G) by group]
      exact (mem_inf.mp y.2).1⟩
  have hf : Function.Injective f := by
    intro y y' h
    have h1 := congrArg (fun u : U => ((u : S.BStab) : G)) h
    simp only [f] at h1
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have h16 : 2 ^ 4 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) h65.four_le_width
  have := Nat.card_le_card_of_injective f hf
  omega

end S14

end CFSG.LargeExtraspecial

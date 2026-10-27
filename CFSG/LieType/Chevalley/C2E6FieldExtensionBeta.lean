module

public import CFSG.LieType.Chevalley.C2E6StandardBetaStar
public import CFSG.LieType.Chevalley.GraphFixedIntrinsicPairs

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def betaG :
    MulAut stdGroup where
  toFun g := ⟨betaGL (g : ModGL Tag.E6 K), betaGL_mem_stdGroup g.2⟩
  invFun g := ⟨betaGL (g : ModGL Tag.E6 K), betaGL_mem_stdGroup g.2⟩
  left_inv g := Subtype.ext (betaGL_betaGL g)
  right_inv g := Subtype.ext (betaGL_betaGL g)
  map_mul' g h := Subtype.ext (map_mul betaGL (g : ModGL Tag.E6 K) h)

theorem coe_betaG_apply
    (g : stdGroup) :
    ((betaG g : stdGroup) : ModGL Tag.E6 K) = betaGL g :=
  rfl

theorem betaG_betaG
    (g : stdGroup) : betaG (betaG g) = g :=
  Subtype.ext (betaGL_betaGL g)

theorem betaG_mul_self :
    betaG * betaG = 1 :=
  MulEquiv.ext fun g => betaG_betaG g

theorem betaGL_rootDiagUnit_eq_sq (c : Fin Tag.E6.rank → Kˣ) :
    betaGL (rootDiagUnit Tag.E6 c) = rootDiagUnit Tag.E6 c ^ 2 := by
  rw [betaGL_rootDiagUnit, rootDiagUnit_pow]
  congr 1

theorem betaGL_fixedTorusGen
    : betaGL fixedTorusGen = fixedTorusGen ^ 2 := by
  rw [fixedTorusGen, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul,
    betaGL_rootDiagUnit_eq_sq]

theorem betaGL_fixedTorusGen_ne
    : betaGL fixedTorusGen ≠ fixedTorusGen := by
  rw [betaGL_fixedTorusGen, pow_two]
  intro h
  exact fixedTorusGen_ne_one (mul_eq_left.mp h)

abbrev torusGenG
    : stdGroup := ⟨fixedTorusGen, fixedTorusGen_mem_stdGroup⟩

theorem betaG_ne_one :
    betaG ≠ 1 := fun h =>
  betaGL_fixedTorusGen_ne (congrArg Subtype.val (MulEquiv.congr_fun h torusGenG))

theorem orderOf_betaG :
    orderOf betaG = 2 :=
  orderOf_eq_prime (by rw [pow_two, betaG_mul_self]) betaG_ne_one

theorem mem_normalizer_of_conj
    {g : stdGroup} {S : Subgroup (ModGL Tag.E6 K)} (hSG : S ≤ stdGroup)
    (hS : ∀ {x}, x ∈ S → betaGL x ∈ S)
    (hβ : ∀ x : stdGroup, betaGL (x : ModGL Tag.E6 K) = g * x * (g : ModGL Tag.E6 K)⁻¹) :
    (g : ModGL Tag.E6 K) ∈ Subgroup.normalizer (S : Set (ModGL Tag.E6 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [← hβ ⟨u, hSG hu⟩]
    exact hS hu
  · intro hu
    have hu' : u ∈ stdGroup := by
      have := mul_mem (mul_mem (inv_mem g.2) (hSG hu)) g.2
      rwa [show (g : ModGL Tag.E6 K)⁻¹ * (g * u * (g : ModGL Tag.E6 K)⁻¹) * g = u by group]
        at this
    have e : betaGL ((g : ModGL Tag.E6 K) * u * (g : ModGL Tag.E6 K)⁻¹) = u := by
      rw [← hβ ⟨u, hu'⟩, betaGL_betaGL]
    rw [← e]
    exact hS hu

theorem stdBorel_inf_opposite :
    stdBorel ⊓ graphFixedOppositeBorel TwistTag.E6 K barHom = stdTorus := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  rw [graphFixedOppositeBorel, ← map_conj_graphFixedRootBorel hmax barHom_surjective]
  exact graphFixedRootBorel_inf_map_conj hmax

theorem betaG_ne_conj
    (g : stdGroup) : betaG ≠ MulAut.conj g := by
  intro h
  have hβ : ∀ x : stdGroup, betaGL (x : ModGL Tag.E6 K) = g * x * (g : ModGL Tag.E6 K)⁻¹ :=
    fun x => congrArg Subtype.val (MulEquiv.congr_fun h x)
  have hU := mem_normalizer_of_conj (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
    betaGL_mem_stdUnipotent0 hβ
  have hV := mem_normalizer_of_conj (graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _)
    betaGL_mem_negUnipotent0 hβ
  have hB : (g : ModGL Tag.E6 K) ∈ stdBorel :=
    (graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent barHom_surjective).le ⟨g.2, hU⟩
  have hBm : (g : ModGL Tag.E6 K) ∈ graphFixedOppositeBorel TwistTag.E6 K barHom :=
    (graphFixedRootGroup_inf_normalizer_graphFixedNegUnipotent barHom_surjective).le ⟨g.2, hV⟩
  have hH : (g : ModGL Tag.E6 K) ∈ Subgroup.zpowers fixedTorusGen := by
    rw [← stdTorus0_eq_zpowers, stdTorus0_eq_stdTorus, ← stdBorel_inf_opposite]
    exact ⟨hB, hBm⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hH
  have hc : (g : ModGL Tag.E6 K) * fixedTorusGen * (g : ModGL Tag.E6 K)⁻¹ = fixedTorusGen := by
    rw [← hk, (Commute.zpow_left (Commute.refl fixedTorusGen) k).eq, mul_inv_cancel_right]
  exact betaGL_fixedTorusGen_ne ((hβ torusGenG).trans hc)

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension

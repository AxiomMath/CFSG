module

public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.CGT.PushingUpLit.BHS.NatQuot
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization Pointwise

theorem mem_centralizer_subgroupOf_iff' {Γ : Type*} [Group Γ] {B X : Subgroup Γ} (hBX : B ≤ X)
    (x : X) : x ∈ Subgroup.centralizer ((B.subgroupOf X : Subgroup X) : Set X) ↔
      (x : Γ) ∈ Subgroup.centralizer (B : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hBX hb⟩ hb)
  · intro h b hb
    exact Subtype.ext (h b hb)

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_natQuotSetting_of_isMinParabolic2 {P T V : Subgroup Γ} (hmin : IsMinParabolic2 T P)
    (hVP : V ≤ P) (hVe : IsElemAbelian 2 V) (hVn : P ≤ Subgroup.normalizer (V : Set Γ))
    (α : ↥P →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf P)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (g : ↥P) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (P : Set Γ)).subgroupOf V) :
    ∃ (M : Subgroup ↥P) (ρ : ↥P →* Gamma F),
      (∀ x, ((ρ x : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (α x)) ∧
      IsNatQuotSetting (T.subgroupOf P) M (V.subgroupOf P) ρ
        (β.comp (Subgroup.subgroupOfEquivOfLe hVP).toMonoidHom) := by
  classical
  obtain ⟨hsyl, hnn, K, hTK, hKP, hK⟩ := hmin
  have hTP : T ≤ P := hsyl.1
  have hVn' : (V.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mpr hVn
  have hVe' : IsElemAbelian 2 (V.subgroupOf P) := by
    refine ⟨GammaExtra.isMulCommutative_iff_forall.mpr fun a ha b hb => ?_, fun x hx => ?_⟩
    · exact Subtype.ext (GammaExtra.isMulCommutative_iff_forall.mp hVe.1 _
        (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
    · exact Subtype.ext (by simpa using hVe.2 _ (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨K.subgroupOf P, ?_⟩
  obtain ⟨ρ, hρ, hset⟩ := exists_natQuotSetting_of_sl2 (R := T.subgroupOf P)
    (M := K.subgroupOf P) (V := V.subgroupOf P) (H := ↥P) (F := F)
    (by
      refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm, ?_⟩
      show ¬ 2 ∣ (T.subgroupOf P).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hsyl.2.2)
    (fun hn => hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hTP).mp hn))
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hTK (Subgroup.mem_subgroupOf.mp hx)))
    (by
      refine lt_top_iff_ne_top.mpr fun h => ?_
      have hPK : P ≤ K := fun x hx =>
        Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥P) ∈ K.subgroupOf P by rw [h]; trivial)
      exact absurd hPK (not_le_of_gt hKP))
    (by
      intro Y hTY hY
      have hTY' : T ≤ Y.map P.subtype := by
        have := Subgroup.map_mono (f := P.subtype) hTY
        rwa [Subgroup.map_subgroupOf_eq_of_le hTP] at this
      have hYP : Y.map P.subtype < P := by
        refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun h => ?_
        apply (lt_top_iff_ne_top.mp hY)
        refine top_unique fun x _ => ?_
        have hx : (x : Γ) ∈ Y.map P.subtype := by rw [h]; exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr (hK _ hTY' hYP ⟨y, hy, rfl⟩))
    hVe' hVn' α hα
    (by
      ext x
      rw [MonoidHom.mem_ker, ← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf,
        mem_centralizer_subgroupOf_iff' hVP])
    (β.comp (Subgroup.subgroupOfEquivOfLe hVP).toMonoidHom)
    (hβ.comp (Subgroup.subgroupOfEquivOfLe hVP).surjective)
    (fun h v v' hv' => hβe h (Subgroup.subgroupOfEquivOfLe hVP v)
      (Subgroup.subgroupOfEquivOfLe hVP v') (by simpa using congrArg Subtype.val hv'))
    (by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have h1 : (β.comp (Subgroup.subgroupOfEquivOfLe hVP).toMonoidHom) v = 1 ↔
          Subgroup.subgroupOfEquivOfLe hVP v ∈ β.ker := Iff.rfl
      rw [h1, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
        Subgroup.mem_center_iff]
      constructor
      · intro hv g
        exact Subtype.ext (by simpa using hv (g : Γ) g.2)
      · intro hv g hg
        exact congrArg Subtype.val (hv ⟨g, hg⟩))
  exact ⟨ρ, hρ, hset⟩

end CFSG.CGT.PushingUpLit.BHS

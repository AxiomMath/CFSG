module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowTranslations
public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowParabolic
import CFSG.Quasithin.Vol2.Ch6Semilinear
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowNormalizer

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.Quasithin.H13

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_semilinear_action_of_standard_row
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  let ι : (Fin 2 → F) → G := fun v =>
    ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F (-(v 1)) 0 (v 0))
  N ≤ Subgroup.normalizer (E : Set G) ∧
  ∃ α : N →* ↥(CFSG.LieType.ChevTwo.OppCl.semilinGroup F (Fin 2 → F)),
    (∀ n : N, ∀ v : Fin 2 → F,
      ι ((α n : Equiv.Perm (Fin 2 → F)) v) =
        (n : G) * ι v * (n : G)⁻¹) ∧
    α.ker = X.subgroupOf N := by
  classical
  obtain ⟨hNE, hreg, -⟩ :=
    regular_translations_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc t ht htC
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  let ι : (Fin 2 → F) → G := fun v =>
    ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F (-(v 1)) 0 (v 0))
  let V := Fin 2 → F
  let rowEquiv : Multiplicative V ≃* E := literalRowEquiv A e φ hφproj
  have hιrow : ∀ v : V, ι v = ((rowEquiv (Multiplicative.ofAdd v) : E) : G) := by
    intro v
    change A.subtype (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F
      (-(v 1)) 0 (v 0))) =
      ((literalRowEquiv A e φ hφproj (Multiplicative.ofAdd v) : E) : G)
    rw [literalRowEquiv_apply]
    simp
  have hι_inj : Function.Injective ι := by
    intro u v huv
    have hrow : rowEquiv (Multiplicative.ofAdd u) = rowEquiv (Multiplicative.ofAdd v) := by
      apply Subtype.ext
      simpa [hιrow u, hιrow v] using huv
    have hof := rowEquiv.injective hrow
    exact Multiplicative.ofAdd.injective hof
  have hι_mem : ∀ v : V, ι v ∈ E := by
    intro v
    rw [hιrow v]
    exact (rowEquiv (Multiplicative.ofAdd v)).2
  let normIncl : N →* Subgroup.normalizer (E : Set G) := Subgroup.inclusion hNE
  let actE : N →* MulAut E := (Subgroup.normalizerMonoidHom (E : Subgroup G)).comp normIncl
  let actV : N →* MulAut (Multiplicative V) :=
    (MulAut.congr rowEquiv.symm).toMonoidHom.comp actE
  let rowAct : N →* Equiv.Perm V :=
    { toFun := fun n =>
        { toFun := fun v => Multiplicative.toAdd (actV n (Multiplicative.ofAdd v))
          invFun := fun v => Multiplicative.toAdd ((actV n).symm (Multiplicative.ofAdd v))
          left_inv := by
            intro v
            simp
          right_inv := by
            intro v
            simp }
      map_one' := by
        ext v
        simp
      map_mul' := by
        intro n m
        ext v
        simp [map_mul] }
  have hrowAct_apply : ∀ (n : N) (v : V),
      ι (rowAct n v) = (n : G) * ι v * (n : G)⁻¹ := by
    intro n v
    rw [hιrow (rowAct n v), hιrow v]
    have hof : Multiplicative.ofAdd (rowAct n v) = actV n (Multiplicative.ofAdd v) := by
      simp [rowAct]
    rw [hof]
    have hactV : ∀ w : Multiplicative V,
        rowEquiv (actV n w) = (actE n) (rowEquiv w) := by
      intro w
      simp [actV, MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hactV]
    change ((Subgroup.normalizerMonoidHom (E : Subgroup G)) (normIncl n)
      (rowEquiv (Multiplicative.ofAdd v)) : G) =
        (n : G) * (rowEquiv (Multiplicative.ofAdd v) : G) * (n : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [normIncl]
  have hrowAct_add : ∀ (n : N) (u v : V),
      rowAct n (u + v) = rowAct n u + rowAct n v := by
    intro n u v
    change Multiplicative.toAdd (actV n (Multiplicative.ofAdd (u + v))) =
      Multiplicative.toAdd (actV n (Multiplicative.ofAdd u)) +
        Multiplicative.toAdd (actV n (Multiplicative.ofAdd v))
    rw [show Multiplicative.ofAdd (u + v) =
      Multiplicative.ofAdd u * Multiplicative.ofAdd v from rfl, map_mul, toAdd_mul]
  have hrowAct_eq_one_of_mem_centralizer : ∀ (g : N),
      (g : G) ∈ Subgroup.centralizer (E : Set G) → rowAct g = 1 := by
    intro g hg
    apply Equiv.ext
    intro v
    apply hι_inj
    rw [hrowAct_apply g v]
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (ι v) (hι_mem v)
    rw [← hcomm]
    simp
  have hEcomm : IsMulCommutative E := by
    have hrange : IsMulCommutative (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F) := by
      rw [← rowSLHom_range F]
      exact Subgroup.range_isMulCommutative (rowSLHom F)
    simpa [E] using
      Subgroup.map_isMulCommutative (H := CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F)
        (f := ρ)
  have hE_le_centralizer : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEcomm
  have hE_le_A : E ≤ A := by
    rintro _ ⟨u, -, rfl⟩
    exact (φ u).2
  have hE_comm_t : E ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp htC x (hE_le_A hx))
  have hE_mem_normalizer_t : E ≤ Subgroup.normalizer
      ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hE_comm_t hx)
    exact (Commute.zpow_right hcomm k).eq.symm
  have hE_mem_N : E ≤ N := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup E (Subgroup.zpowers t)
      ⟨Subgroup.le_normalizer hx, hE_mem_normalizer_t hx⟩
  have hlev_mem_normalizer_E : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈
        Subgroup.normalizer (E : Set G) := by
    intro B
    have hmap : ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈
        (Subgroup.normalizer
          (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F :
            Set (Matrix.SpecialLinearGroup (Fin 3) F))).map ρ :=
      Subgroup.mem_map_of_mem ρ (leviOne_mem_normalizer_unipOne B)
    exact Subgroup.le_normalizer_map
      (H := CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F) ρ hmap
  have hlev_comm_t : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) * t =
        t * ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) := by
    intro B
    exact Subgroup.mem_centralizer_iff.mp htC _
      (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B)).2
  have hlev_mem_N : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) ∈ N := by
    intro B
    refine Subgroup.inf_normalizer_le_normalizer_sup E (Subgroup.zpowers t) ⟨
      hlev_mem_normalizer_E B, ?_⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hlev_comm_t B) k).eq.symm
  let L : Subgroup G :=
    (ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)).range
  have hL_mem_normalizer_E : L ≤ Subgroup.normalizer (E : Set G) := by
    rintro _ ⟨B, rfl⟩
    exact hlev_mem_normalizer_E B
  have hL_mem_N : L ≤ N := by
    rintro _ ⟨B, rfl⟩
    exact hlev_mem_N B
  have hrowAct_levi_apply : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) F) (v : V),
      rowAct ⟨ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B),
        hlev_mem_N B⟩ v =
        (B : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
    intro B v
    apply hι_inj
    rw [hrowAct_apply]
    have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 3) F => ρ z)
      (leviOne_conj_rowSLHom B (Multiplicative.ofAdd v))
    have hιrowSL : ∀ w : V, ι w =
        ρ (rowSLHom F (Multiplicative.ofAdd w)) := by
      intro w
      simp [ι, rowSLHom]
    calc ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B) * ι v *
          (ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B))⁻¹
        = ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B *
            rowSLHom F (Multiplicative.ofAdd v) *
            (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B)⁻¹) := by
            rw [hιrowSL, map_mul, map_mul, map_inv]
      _ = ρ (rowSLHom F (Multiplicative.ofAdd
            ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v))) := by
            simpa using h
      _ = ι ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := (hιrowSL _).symm
  let rowAdd (n : N) : V ≃+ V :=
    { toEquiv := rowAct n, map_add' := hrowAct_add n }
  have hrowAdd_congr : ∀ {n m : N}, rowAct n = rowAct m → rowAdd n = rowAdd m := by
    intro n m h
    apply AddEquiv.ext
    intro v
    exact congrArg (fun p : Equiv.Perm V => p v) h
  have hcorrect : ∀ n : N, ∃ cN : N, rowAct cN = rowAct n ∧
      (cN : G) ∈ Subgroup.normalizer (A : Set G) ∧
      (cN : G) ∈ Subgroup.normalizer (E : Set G) := by
    intro n
    have hntJ : (n : G) * t * (n : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp n.2 t).mp
        (show t ∈ J from mem_sup_right (Subgroup.mem_zpowers t))
    have hconj : IsConj t ((n : G) * t * (n : G)⁻¹) := isConj_iff.mpr ⟨n, rfl⟩
    obtain ⟨x, hxX, hxt⟩ := hreg.exists_conj ((n : G) * t * (n : G)⁻¹) hntJ hconj
    have hxN : (x : G) ∈ N := hxX.1
    have hxC : (x : G) ∈ Subgroup.centralizer (E : Set G) := hxX.2
    let xN : N := ⟨(x : G), hxN⟩
    let cN : N := xN⁻¹ * n
    have hcN : (cN : G) ∈ N := cN.2
    have hcE : (cN : G) ∈ Subgroup.normalizer (E : Set G) := hNE hcN
    have hc_conj_t : (cN : G) * t * (cN : G)⁻¹ = t := by
      dsimp [cN, xN]
      calc ((x : G)⁻¹ * (n : G)) * t * ((x : G)⁻¹ * (n : G))⁻¹
          = (x : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) * (x : G) := by group
        _ = (x : G)⁻¹ * ((x : G) * t * (x : G)⁻¹) * (x : G) := by rw [← hxt]
        _ = t := by group
    have hct : (cN : G) * t = t * (cN : G) := by
      calc (cN : G) * t = ((cN : G) * t * (cN : G)⁻¹) * (cN : G) := by group
        _ = t * (cN : G) := by rw [hc_conj_t]
    have hcA : (cN : G) ∈ Subgroup.normalizer (A : Set G) :=
      hA.mem_normalizer_of_commute htC ht hct
    have hrowAct_x : rowAct xN = 1 := hrowAct_eq_one_of_mem_centralizer xN hxC
    have hrowAct_cN : rowAct cN = rowAct n := by
      calc rowAct cN = (rowAct xN)⁻¹ * rowAct n := by
            rw [show cN = xN⁻¹ * n from rfl, map_mul, map_inv]
        _ = rowAct n := by rw [hrowAct_x]; simp
    exact ⟨cN, hrowAct_cN, hcA, hcE⟩
  have hnormN : ∀ n : N, NormalizesSL2 (rowAdd n) := by
    intro n
    obtain ⟨cN, hrowAct_cN, hcA, hcE⟩ := hcorrect n
    have hnorm_c : NormalizesSL2 (rowAdd cN) := by
      intro A2
      let ℓN : N := ⟨ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F A2),
        hlev_mem_N A2⟩
      let g : G := (cN : G) * (ℓN : G) * (cN : G)⁻¹
      have hgN : g ∈ N := N.mul_mem (N.mul_mem cN.2 ℓN.2) (N.inv_mem cN.2)
      let gN : N := ⟨g, hgN⟩
      have hmem : g ∈ E ⊔ L := by
        have hle := map_levi_conj_le_row_sup_levi_of_mem_normalizers
          (A := A) (e := e) (φ := φ) (hφsurj := hφsurj) (hφproj := hφproj)
        have harg : (MulAut.conj (cN : G)) (ℓN : G) ∈
            L.map (MulAut.conj (cN : G)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ ⟨A2, rfl⟩
        have hout := hle (cN : G) hcA hcE
        simpa [g, L, ℓN, MulAut.conj_apply] using hout harg
      have hmemMul : g ∈ (↑(E ⊔ L) : Set G) := hmem
      rw [Subgroup.coe_mul_of_right_le_normalizer_left E L hL_mem_normalizer_E] at hmemMul
      obtain ⟨e', he', l', hl', hg_eq⟩ := hmemMul
      have he'N : e' ∈ N := hE_mem_N he'
      have hl'N : l' ∈ N := hL_mem_N hl'
      let eN : N := ⟨e', he'N⟩
      have hrow_e : rowAct eN = 1 :=
        hrowAct_eq_one_of_mem_centralizer eN (hE_le_centralizer he')
      obtain ⟨B2, rfl⟩ := hl'
      let lN : N := ⟨ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B2),
        hlev_mem_N B2⟩
      have hrow_gN : rowAct gN = rowAct lN := by
        rw [show gN = eN * lN from Subtype.ext hg_eq.symm, map_mul, hrow_e, one_mul]
      refine ⟨B2, fun v => ?_⟩
      calc (rowAdd cN) ((A2 : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
          = rowAct cN ((A2 : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := rfl
        _ = rowAct cN (rowAct ℓN v) := by rw [hrowAct_levi_apply A2 v]
        _ = rowAct (cN * ℓN) v := by rw [map_mul, Equiv.Perm.mul_apply]
        _ = rowAct (gN * cN) v := by
              have h : cN * ℓN = gN * cN := by
                apply Subtype.ext
                dsimp [gN, g, ℓN]
                group
              rw [h]
        _ = rowAct gN (rowAct cN v) := by rw [map_mul, Equiv.Perm.mul_apply]
        _ = rowAct lN (rowAct cN v) := by rw [hrow_gN]
        _ = (B2 : Matrix (Fin 2) (Fin 2) F) *ᵥ (rowAct cN v) := by
              rw [hrowAct_levi_apply B2]
    have hrowAdd_eq : rowAdd cN = rowAdd n := hrowAdd_congr hrowAct_cN
    simpa [hrowAdd_eq] using hnorm_c
  have hsemilin : ∀ n : N, rowAct n ∈
      CFSG.LieType.ChevTwo.OppCl.semilinGroup F V := by
    intro n
    refine ⟨hrowAct_add n, ?_⟩
    exact NormalizesSL2.exists_semilinear (hnormN n)
  let α : N →* ↥(CFSG.LieType.ChevTwo.OppCl.semilinGroup F V) :=
    { toFun := fun n => ⟨rowAct n, hsemilin n⟩
      map_one' := Subtype.ext (map_one rowAct)
      map_mul' := fun n m => Subtype.ext (map_mul rowAct n m) }
  refine ⟨hNE, α, ?_, ?_⟩
  · intro n v
    exact hrowAct_apply n v
  · ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      have hfix : rowAct n = 1 := by
        have := congrArg (fun z : ↥(CFSG.LieType.ChevTwo.OppCl.semilinGroup F V) =>
          (z : Equiv.Perm V)) hn
        simpa [α] using this
      refine ⟨n.2, ?_⟩
      change (n : G) ∈ Subgroup.centralizer (E : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨w, hw⟩ := rowEquiv.surjective ⟨e, he⟩
      let v : V := Multiplicative.toAdd w
      have hwv : rowEquiv (Multiplicative.ofAdd v) = ⟨e, he⟩ := by
        simpa [v] using hw
      have hιe : ι v = e := by
        rw [hιrow v, hwv]
      have hveq : rowAct n v = v := by rw [hfix]; rfl
      have hconj := hrowAct_apply n v
      rw [hveq, hιe] at hconj
      calc e * (n : G) = ((n : G) * e * (n : G)⁻¹) * (n : G) := by
            conv_lhs => rw [hconj]
        _ = (n : G) * e := by group
    · intro hn
      have hcent : (n : G) ∈ Subgroup.centralizer (E : Set G) := hn.2
      apply Subtype.ext
      apply Equiv.ext
      intro v
      change rowAct n v = v
      apply hι_inj
      rw [hrowAct_apply n v]
      have hcomm := Subgroup.mem_centralizer_iff.mp hcent (ι v) (hι_mem v)
      rw [← hcomm]
      group

end CFSG.ComponentClassification.GS79bSec5

end

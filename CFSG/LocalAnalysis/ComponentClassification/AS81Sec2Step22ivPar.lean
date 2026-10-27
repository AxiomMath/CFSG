module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivAutA
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivLevi
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open LinearFlag CFSG.LieType.Chevalley
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def sec2L (A E : Subgroup G) : Subgroup G :=
  ⁅A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)⁆

omit [Finite G] in
theorem sec2L_le (A E : Subgroup G) :
    sec2L A E ≤ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
  commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_cover_projRad_zero_one (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ c : L34Cover ↥A, ∃ φ : ↥A →* projectiveSL 3 c.k, Function.Surjective φ ∧
      φ.ker = center ↥A ∧ ((E ⊓ A).subgroupOf A).map φ = projRad c.k 0 ∧
      ((F ⊓ A).subgroupOf A).map φ = projRad c.k 1 ∧
      (((E ⊔ F) ⊓ A).subgroupOf A).map φ ≤
        normalizer (projRad c.k 0 : Set (projectiveSL 3 c.k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨cv⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have : CharP cv.k 2 := charP_two_of_card cv.card_k
  have hO := oddCore_le_center hq.1 hq.2
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨-, hT₀, -⟩ := sylow_sup_structure hRA hF.sylowR.isPGroup hF.sylow
  obtain ⟨S, hS⟩ := hT₀
  obtain ⟨φ, hφs, hφk, hφS⟩ := cv.exists_std hO S
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hSsub : ((E ⊔ F) ⊓ A).subgroupOf A = S := by
    rw [← hS]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hS2 : IsPGroup 2 (S : Subgroup ↥A) := S.2
  have hrad : ∀ X : Subgroup G, X ≤ (E ⊔ F) ⊓ A → IsElemAbelian 2 X → Nat.card X = 16 →
      X.subgroupOf A ≤ S ∧ ((X.subgroupOf A).map φ = projRad cv.k 0 ∨
        (X.subgroupOf A).map φ = projRad cv.k 1) := by
    intro X hXT hX hX16
    have hX₀S : X.subgroupOf A ≤ S := fun x hx => hSsub ▸ (hXT (mem_subgroupOf.mp hx))
    refine ⟨hX₀S, eq_projRad_of_le_projUnip cv.card_k (hφS ▸ map_mono hX₀S) ?_ ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by
        simpa using hX.2 _ (mem_subgroupOf.mp hx)), map_one]
    · rw [card_map_of_isPGroup φ hkerodd (hS2.to_le hX₀S), ← hX16]
      exact Nat.card_congr (subgroupOfEquivOfLe (hXT.trans inf_le_right)).toEquiv
  obtain ⟨hES, hE⟩ := hrad (E ⊓ A) (inf_le_inf_right A le_sup_left)
    (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) (card_inf_left hF hodd)
  obtain ⟨hFS, hF'⟩ := hrad (F ⊓ A) (inf_le_inf_right A le_sup_right)
    (AS76b.IsElemAbelian.mono hF.elemF inf_le_left) (card_inf_left hF.symm hodd)
  have hne : ((E ⊓ A).subgroupOf A).map φ ≠ ((F ⊓ A).subgroupOf A).map φ := by
    intro h
    have hle : ∀ {X Y : Subgroup G}, X.subgroupOf A ≤ S → Y.subgroupOf A ≤ S →
        (X.subgroupOf A).map φ = (Y.subgroupOf A).map φ → X ⊓ A ≤ Y := by
      intro X Y hX hY hXY x hx
      have hxX : (⟨x, hx.2⟩ : ↥A) ∈ X.subgroupOf A := mem_subgroupOf.mpr hx.1
      obtain ⟨y, hy, hyx⟩ := (hXY ▸ mem_map_of_mem φ hxX)
      have hyx' := eq_of_map_eq_of_isPGroup φ hkerodd hS2 (hY hy) (hX hxX) hyx
      have hyY : ((y : ↥A) : G) ∈ Y := mem_subgroupOf.mp hy
      rw [hyx'] at hyY
      exact hyY
    have h1 : E ⊓ A ≤ F ⊓ A := fun x hx => hle hES hFS h ⟨hx, hx.2⟩
    have h2 : F ⊓ A ≤ E ⊓ A := fun x hx => hle hFS hES h.symm ⟨hx, hx.2⟩
    have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
    have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
    exact hF.ne (by rw [hEeq, hFeq, le_antisymm h1 h2])
  rcases hE with hE0 | hE1
  · rcases hF' with hF0 | hF1
    · exact absurd (hE0.trans hF0.symm) hne
    · refine ⟨cv, φ, hφs, hφk, hE0, hF1, ?_⟩
      rw [hSsub, hφS]
      exact projUnip_le_normalizer_projRad 0
  · rcases hF' with hF0 | hF1
    · refine ⟨cv, Sec2Aut.radSwap.toMonoidHom.comp φ,
        Sec2Aut.radSwap.surjective.comp hφs, ?_, ?_, ?_, ?_⟩
      · ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφk]
      · rw [← Subgroup.map_map, hE1, Sec2Aut.map_projRad_one_radSwap]
      · rw [← Subgroup.map_map, hF0, Sec2Aut.map_projRad_zero_radSwap]
      · rw [← Subgroup.map_map, hSsub, hφS]
        calc (projUnip cv.k).map (Sec2Aut.radSwap : MulAut (projectiveSL 3 cv.k)).toMonoidHom
            ≤ (normalizer (projRad cv.k 1 : Set (projectiveSL 3 cv.k))).map
                (Sec2Aut.radSwap : MulAut (projectiveSL 3 cv.k)).toMonoidHom :=
              map_mono (projUnip_le_normalizer_projRad 1)
          _ = normalizer (((projRad cv.k 1).map
                (Sec2Aut.radSwap : MulAut (projectiveSL 3 cv.k)).toMonoidHom :
                  Subgroup (projectiveSL 3 cv.k)) : Set (projectiveSL 3 cv.k)) :=
              map_equiv_normalizer_eq _ _
          _ = normalizer (projRad cv.k 0 : Set (projectiveSL 3 cv.k)) := by
              rw [Sec2Aut.map_projRad_one_radSwap]
    · exact absurd (hE1.trans hF1.symm) hne

theorem sec2P_inf_eq (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    sec2P E ⊓ A = E ⊓ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPU := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  refine le_antisymm (fun x hx => ⟨?_, hx.2⟩) (le_inf (inf_le_left.trans hEP) inf_le_right)
  have hxC : x ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
    have h1 : a * x = x * a := mem_centralizer_iff.mp (hPU hx.1) a ha
    have h2 : r * x = x * r := (mem_centralizer_iff.mp (hRA hr) x hx.2).symm
    calc a * r * x = a * (r * x) := by group
      _ = a * (x * r) := by rw [h2]
      _ = x * (a * r) := by rw [← mul_assoc, h1, mul_assoc]
  obtain ⟨n, hn⟩ := (Sec2.isPGroup_sec2P E) ⟨x, hx.1⟩
  exact hCE x hxC n (by simpa using congrArg Subtype.val hn)

theorem map_inf_normalizer_eq (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A)))
    {k : Type} [Field k] {φ : ↥A →* projectiveSL 3 k} (hφs : Function.Surjective φ)
    (hφk : φ.ker = center ↥A) (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) :
    ((A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf A).map φ =
      normalizer (projRad k 0 : Set (projectiveSL 3 k)) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) := mem_subgroupOf.mp ha
    rw [← hφU]
    refine mem_normalizer_of_conj_mem ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨a * u * a⁻¹, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (mem_normalizer_iff.mp ha'.2 _).mp (mem_subgroupOf.mp hu)
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨a⁻¹ * u * a, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := (mem_normalizer_iff.mp (inv_mem ha'.2) _).mp (mem_subgroupOf.mp hu)
      simpa using this
  · obtain ⟨a, rfl⟩ := hφs x
    exact ⟨a, mem_subgroupOf.mpr (mem_normalizer_of_map_mem hF hodd hφk hφU hx), rfl⟩

omit [Finite G] in
theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

omit [Finite G] in
theorem commutator_subgroupOf_eq {A H : Subgroup G} (hHA : H ≤ A) :
    (⁅H, H⁆).subgroupOf A = ⁅H.subgroupOf A, H.subgroupOf A⁆ := by
  apply map_injective A.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hHA,
    inf_eq_left.mpr ((commutator_le_self' H).trans hHA)]

omit [Finite G] in
theorem mem_normalizer_commutator {H : Subgroup G} {x : G} (hx : x ∈ normalizer (H : Set G)) :
    x ∈ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, mem_normalizer_iff_map_conj_eq.mp hx]

theorem map_sec2L (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A))) {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = 4) {φ : ↥A →* projectiveSL 3 k}
    (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) :
    ((sec2L A E).subgroupOf A).map φ = normalizer (projRad k 0 : Set (projectiveSL 3 k)) := by
  rw [sec2L, commutator_subgroupOf_eq inf_le_left, map_commutator,
    map_inf_normalizer_eq hF hodd hφs hφk hφU, Sec2Aut.commutator_normalizer_projRad_zero hk]

theorem commutator_sec2L (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : ⁅sec2L A E, sec2L A E⁆ = sec2L A E := by
  obtain ⟨c, φ, hφs, hφk, hφU, -, -⟩ := exists_cover_projRad_zero_one hF hL hodd
  set H := A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) with hH
  refine le_antisymm (commutator_le_self' _) ?_
  have hle : H.subgroupOf A ≤ (sec2L A E).subgroupOf A ⊔ center ↥A := by
    rw [← hφk, ← comap_map_eq, map_sec2L hF hodd c.card_k hφs hφk hφU,
      ← map_inf_normalizer_eq hF hodd hφs hφk hφU]
    exact le_comap_map _ _
  have hcomm : ⁅H.subgroupOf A, H.subgroupOf A⁆ ≤
      ⁅(sec2L A E).subgroupOf A, (sec2L A E).subgroupOf A⁆ := by
    refine commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := mem_sup_of_normal_right.mp (hle ha)
    obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := mem_sup_of_normal_right.mp (hle hb)
    have h1 : ⁅l₁ * z₁, l₂ * z₂⁆ = ⁅l₁, l₂⁆ := by
      have c1 := mem_center_iff.mp hz₁
      have c2 := mem_center_iff.mp hz₂
      have k1 : z₁ * (l₂ * z₂) * z₁⁻¹ = l₂ * z₂ := by rw [← c1, mul_inv_cancel_right]
      have k2 : z₂ * l₁⁻¹ * z₂⁻¹ = l₁⁻¹ := by rw [← c2, mul_inv_cancel_right]
      calc ⁅l₁ * z₁, l₂ * z₂⁆ = l₁ * (z₁ * (l₂ * z₂) * z₁⁻¹) * l₁⁻¹ * (l₂ * z₂)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = l₁ * l₂ * (z₂ * l₁⁻¹ * z₂⁻¹) * l₂⁻¹ := by rw [k1]; group
        _ = ⁅l₁, l₂⁆ := by rw [k2, commutatorElement_def]
    rw [h1]
    exact commutator_mem_commutator hl₁ hl₂
  have hfin : (sec2L A E).subgroupOf A ≤ (⁅sec2L A E, sec2L A E⁆).subgroupOf A := by
    rw [commutator_subgroupOf_eq ((sec2L_le A E).trans inf_le_left)]
    calc (sec2L A E).subgroupOf A = ⁅H.subgroupOf A, H.subgroupOf A⁆ :=
          commutator_subgroupOf_eq inf_le_left
      _ ≤ _ := hcomm
  intro x hx
  have hxA : x ∈ A := ((sec2L_le A E).trans inf_le_left) hx
  exact mem_subgroupOf.mp (hfin (mem_subgroupOf.mpr hx : (⟨x, hxA⟩ : ↥A) ∈ _))

theorem le_sec2L_of_map_le (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A)))
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) {φ : ↥A →* projectiveSL 3 k}
    (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) {X : Subgroup G} (hXA : X ≤ A)
    (hX : IsPGroup 2 X)
    (hXφ : (X.subgroupOf A).map φ ≤ normalizer (projRad k 0 : Set (projectiveSL 3 k))) :
    X ≤ sec2L A E := by
  intro x hx
  have hxL : (⟨x, hXA hx⟩ : ↥A) ∈ (sec2L A E).subgroupOf A ⊔ center ↥A := by
    rw [← hφk, ← comap_map_eq, map_sec2L hF hodd hk hφs hφk hφU, mem_comap]
    exact hXφ ⟨_, mem_subgroupOf.mpr hx, rfl⟩
  have hZ : center ↥A ≤ centralizer (((sec2L A E).subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    fun z hz => mem_centralizer_iff.mpr fun l _ => mem_center_iff.mp hz l
  obtain ⟨n, hn⟩ := hX ⟨x, hx⟩
  have hx2 : (⟨x, hXA hx⟩ : ↥A) ^ 2 ^ n = 1 := Subtype.ext (by
    simpa using congrArg Subtype.val hn)
  exact mem_subgroupOf.mp (mem_of_mem_sup_of_pow_two hodd hZ hxL hx2)

theorem sup_inf_le_sec2L (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : (E ⊔ F) ⊓ A ≤ sec2L A E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, φ, hφs, hφk, hφU, -, hφS⟩ := exists_cover_projRad_zero_one hF hL hodd
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨-, hT₀, -⟩ := sylow_sup_structure hRA hF.sylowR.isPGroup hF.sylow
  exact le_sec2L_of_map_le hF hodd c.card_k hφs hφk hφU inf_le_right hT₀.isPGroup hφS

end Frame

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y))

include h11 hE16 hF hL hodd hyA hyE hyU hy3

theorem sec2W_inf_eq : sec2W A E y ⊓ A = E ⊓ A := by
  obtain ⟨-, hUW, hWP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  refine le_antisymm ?_ (le_inf hUW inf_le_right)
  rw [← sec2P_inf_eq h11 hE16 hF hL hodd]
  exact inf_le_inf_right A hWP

theorem mem_normalizer_sec2L {x : G} (hxA : x ∈ normalizer (A : Set G))
    (hxW : x ∈ normalizer (sec2W A E y : Set G)) : x ∈ normalizer (sec2L A E : Set G) := by
  have hxU : x ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    have := inf_normalizer_le_normalizer_inf ⟨hxW, hxA⟩
    rwa [sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3] at this
  exact mem_normalizer_commutator (inf_normalizer_le_normalizer_inf ⟨hxA, le_normalizer hxU⟩)

variable (hW : IsElemAbelian 2 (sec2W A E y))
include hW

theorem inf_normalizer_le_normalizer_sec2W :
    A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ normalizer (sec2W A E y : Set G) := by
  intro a ha
  have haE := mem_normalizer_of_mem_normalizer_inf hF ha.1 ha.2
  exact normalizer_sec2P_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
    (Sec2.normalizer_le_normalizer_sec2P E haE)

theorem sec2L_le_normalizer_sec2W : sec2L A E ≤ normalizer (sec2W A E y : Set G) :=
  (sec2L_le A E).trans (inf_normalizer_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW)

end Wsec

end CFSG.ComponentClassification.AS81

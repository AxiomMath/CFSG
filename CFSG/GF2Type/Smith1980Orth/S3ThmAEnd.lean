module

public import CFSG.GF2Type.Smith1980Orth.S3ThmAProp
public import CFSG.GF2Type.Smith1980Orth.S3ThmACount
public import CFSG.GF2Type.Smith1980Orth.S3ThmALin
import Mathlib.FieldTheory.Finite.GaloisField

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_clPre_map {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (S : Setting G) (ι : V →ₗ[ZMod 2] S.Qt)
    (hι : Function.Injective ι) (P₀ : Submodule (ZMod 2) V) :
    Nat.card (S.clPre (P₀.map ι)) = 2 * 2 ^ finrank (ZMod 2) P₀ := by
  have h0 : Nat.card (S.clPre (P₀.map ι)) = ((S.clPre (P₀.map ι) : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h1 : ((S.clPre (P₀.map ι) : Subgroup G) : Set G) =
      {x : G | x ∈ S.QG ∧ S.cl x ∈ ((P₀.map ι : Submodule (ZMod 2) S.Qt) : Set S.Qt)} := rfl
  have h3 : ((P₀.map ι : Submodule (ZMod 2) S.Qt) : Set S.Qt).ncard =
      Nat.card (P₀.map ι : Submodule (ZMod 2) S.Qt) :=
    (Nat.card_coe_set_eq _).symm
  have h4 : Nat.card (P₀.map ι : Submodule (ZMod 2) S.Qt) = 2 ^ finrank (ZMod 2) P₀ := by
    rw [← FiniteField.pow_finrank_eq_natCard 2]
    congr 1
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ι hι P₀)).symm
  rw [h0, h1, ncard_cl_preimage, h3, h4]

namespace S2Data

section Rel

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

structure BadData (k : G) : Prop where
  bad : Bad S k
  hxC : S.ρ ⟨k * S.z * k⁻¹, bad.mem_M⟩ ∈ D.Cbar
  half : 2 * finrank (ZMod 2) (commSpace (ρV ⟨_, hxC⟩)) = S.width
  fix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))
  dl : S.QG ⊓ S.Qa k = ⊥ ∨ (¬ IsConj S.z (k * S.z * k⁻¹ * S.z) ∧ ∃ p : Vt S D.g D.t,
    p ∈ commSpace (ρV ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
    ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p))
  lfix : ∀ a ∈ S.Lbar k, ∃ ha : a ∈ D.Cbar,
    ∀ v ∈ commSpace (ρV ⟨_, hxC⟩), ρV ⟨a, ha⟩ v = v

theorem card_Dl_le_four_of_R1 {k : G} (hxQ : k * S.z * k⁻¹ ∉ S.QG) {p : Vt S D.g D.t}
    (hΔ : ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) :
    Nat.card (S.QG ⊓ S.Qa k : Subgroup G) ≤ 4 := by
  let f : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] S.Qt :=
    (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) ∘ₗ
      LinearMap.prodMap (LinearMap.toSpanSingleton (ZMod 2) _ p)
        (LinearMap.toSpanSingleton (ZMod 2) _ p)
  have hle : S.clSub (S.QG ⊓ S.Qa k) ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨α, β, rfl⟩ := (hΔ v).mp hv
    exact ⟨(α, β), rfl⟩
  have hfr : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa k)) ≤ 2 := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    rw [Module.finrank_prod, Module.finrank_self]
  rw [← SMK.card_clSub_Dl S hxQ, ← FiniteField.pow_finrank_eq_natCard 2]
  calc 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa k)) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) hfr
    _ = 4 := by norm_num

end Rel

section Full

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem false_of_badData_six {k : G} (H : D.BadData k) (hw : S.width = 6)
    (hR1 : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z) ∧ ∃ p : Vt S D.g D.t,
      p ∈ commSpace (ρV ⟨_, H.hxC⟩) ∧ D.QV p = 1 ∧
      ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) :
    False := by
  obtain ⟨hxz, p, -, -, hΔ⟩ := hR1
  have hxM := H.bad.mem_M
  have hxQ := H.bad.not_mem_QG
  have hPP := D.orthogonal_commSpace_eq (rho_conj_mul_self S hxM) H.half
  have hm : finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) = 3 := by
    have := H.half
    omega
  have hL := D.card_le_of_fix hPP H.lfix
  rw [hm] at hL
  have hL0 := SMK.card_L0_ge_succ S hxM hxQ hxz
  rw [hw] at hL0
  have hmul := S.card_Lbar_mul k
  have hΔ4 := D.card_Dl_le_four_of_R1 hxQ hΔ
  have h16 : Nat.card (S.Lbar k) ≤ 16 := by
    have e : 2 ^ (Nat.choose 3 2 + min 3 1) = 16 := by decide
    rwa [e] at hL
  have : Nat.card (S.L0 k) ≤ 64 := by
    rw [← hmul]
    calc Nat.card (S.Lbar k) * Nat.card (S.QG ⊓ S.Qa k : Subgroup G) ≤ 16 * 4 :=
          Nat.mul_le_mul h16 hΔ4
      _ = 64 := by norm_num
  have : (2 : ℕ) ^ (6 + 1) = 128 := by norm_num
  omega

theorem BadData.exists_subgroup {j : G} (H : D.BadData j) :
    ∃ B : Subgroup G, B ≤ S.QG ∧
      2 ^ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) ≤ Nat.card B ∧
      (∀ y ∈ B, y * (j * S.z * j⁻¹) = (j * S.z * j⁻¹) * y) ∧
      (∀ y ∈ B, y ≠ 1 → y = S.z ∨ ∃ a ∈ commSpace (ρV ⟨_, H.hxC⟩), a ≠ 0 ∧ D.QV a = 0 ∧
        S.cl y = D.coord (a, 0)) := by
  have hxM := H.bad.mem_M
  have hcc : ((⟨_, H.hxC⟩ : D.Cbar) : S.O) * (⟨_, H.hxC⟩ : D.Cbar) = 1 :=
    rho_conj_mul_self S hxM
  have htt : ρV ⟨_, H.hxC⟩ * ρV ⟨_, H.hxC⟩ = 1 := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, D.resC_resC_apply hcc]
    rfl
  have hiso : ∀ a ∈ commSpace (ρV ⟨_, H.hxC⟩), ∀ b ∈ commSpace (ρV ⟨_, H.hxC⟩),
      polar D.QV a b = 0 :=
    fun a ha b hb => polar_commSpace_eq_zero (D.resC_mem_orthogonalGroup _) htt ha hb
  obtain ⟨P₀, hP₀, hP₀s, hP₀d⟩ := exists_singular_subspace D.QV hiso
  obtain ⟨ι, hι⟩ : ∃ ι : Vt S D.g D.t →ₗ[ZMod 2] S.Qt, ∀ a, ι a = D.coord (a, 0) :=
    ⟨(D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) ∘ₗ
      LinearMap.inl (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t), fun a => rfl⟩
  have hιinj : Function.Injective ι := fun a b e => by
    rw [hι, hι] at e
    exact (Prod.mk.inj (D.coord.injective e)).1
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) S.Qt, W = P₀.map ι := ⟨_, rfl⟩
  have hmemW : ∀ y ∈ S.clPre W, y ∈ S.QG ∧ ∃ a ∈ P₀, S.cl y = D.coord (a, 0) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hyW : S.cl y ∈ W := hy.2
    rw [hW] at hyW
    obtain ⟨a, ha, hya⟩ := Submodule.mem_map.mp hyW
    exact ⟨a, ha, by rw [← hya, hι]⟩
  refine ⟨S.clPre W, S.clPre_le_QG W, ?_, ?_, ?_⟩
  ·
    rw [hW, card_clPre_map S ι hιinj P₀]
    calc 2 ^ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) ≤ 2 ^ (finrank (ZMod 2) P₀ + 1) :=
          Nat.pow_le_pow_right (by norm_num) hP₀d
      _ = 2 * 2 ^ finrank (ZMod 2) P₀ := by ring
  ·
    intro y hy
    obtain ⟨hyQ, a, ha, hya⟩ := hmemW y hy
    have hmem : S.cl y ∈ S.fixQt (j * S.z * j⁻¹) := by
      rw [S.fixQt_of_mem hxM, hya]
      refine commSpace_le_fixSpace (by rw [← Subgroup.coe_mul, hcc]; rfl) ?_
      exact (D.mem_commSpace_iff_coord_of_mem_Cbar H.hxC).mpr
        ⟨a, 0, hP₀ ha, Submodule.zero_mem _, rfl⟩
    rw [H.fix] at hmem
    obtain ⟨u, hu, huQ, hcl⟩ := S.mem_clSub_iff.mp hmem
    have hux : u * (j * S.z * j⁻¹) = (j * S.z * j⁻¹) * u :=
      mem_centralizer_singleton_iff.mp hu.2
    have hzx : S.z * (j * S.z * j⁻¹) = (j * S.z * j⁻¹) * S.z := (S.z_comm hxM).symm
    rcases (S.cl_eq_cl_iff huQ hyQ).mp hcl with e | e
    · rw [e]
      exact hux
    · rw [e, mul_assoc, hzx, ← mul_assoc, hux, mul_assoc]
  ·
    intro y hy hy1
    obtain ⟨hyQ, a, ha, hya⟩ := hmemW y hy
    by_cases ha0 : a = 0
    · left
      rw [ha0, Prod.mk_zero_zero, map_zero] at hya
      rcases (S.cl_eq_zero_iff hyQ).mp hya with h | h
      · exact absurd h hy1
      · exact h
    · exact Or.inr ⟨a, hP₀ ha, ha0, hP₀s a ha, hya⟩

theorem BadData.finrank_eq {k j : G} (H : D.BadData k) (HY : D.BadData j) :
    finrank (ZMod 2) (commSpace (ρV ⟨_, HY.hxC⟩)) =
      finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) := by
  have e1 := HY.half
  have e2 := H.half
  omega

theorem _root_.CFSG.GF2Type.Smith1980Orth.Bad.of_conjBy_conjBy {S : Setting G} {k h : G}
    (hP : Bad ((S.conjBy k).conjBy h) (k⁻¹ * h⁻¹)) : Bad S (h * k) := by
  have h1 : Bad (S.conjBy (h * k)) (k⁻¹ * h⁻¹) := Bad.of_z_eq (by
    show h * (k * S.z * k⁻¹) * h⁻¹ = h * k * S.z * (h * k)⁻¹
    group) hP
  rw [← mul_inv_rev] at h1
  exact Bad.of_symm h1

theorem BadData.prop_hyp {k : G} (D' : S2Data (S.conjBy k)) (H' : D'.BadData k⁻¹)
    (hw6 : 6 ≤ S.width) (hcase : S.QG ⊓ S.Qa k = ⊥ ∨ 8 ≤ S.width) :
    ((S.conjBy k).QG ⊓ (S.conjBy k).Qa k⁻¹ = ⊥ ∧ 6 ≤ (S.conjBy k).width) ∨
      (∃ p : Vt (S.conjBy k) D'.g D'.t,
        p ∈ commSpace (D'.resC ⟨_, H'.hxC⟩) ∧ D'.QV p = 1 ∧
        (∀ v : (S.conjBy k).Qt,
          v ∈ (S.conjBy k).clSub ((S.conjBy k).QG ⊓ (S.conjBy k).Qa k⁻¹) ↔
            ∃ α β : ZMod 2, v = D'.coord (α • p, β • p)) ∧ 8 ≤ (S.conjBy k).width) := by
  have hwk : (S.conjBy k).width = S.width := S.width_conjBy k
  have h6 : 6 ≤ (S.conjBy k).width := by rw [hwk]; exact hw6
  have hΔeq : (S.conjBy k).QG ⊓ (S.conjBy k).Qa k⁻¹ = S.QG ⊓ S.Qa k := by
    rw [Bad.conjBy_Qa_inv]
    exact inf_comm _ _
  rcases hcase with h | h
  · exact Or.inl ⟨hΔeq.trans h, h6⟩
  · rcases H'.dl with h' | ⟨-, p', hp'P, hp'Q, hp'Δ⟩
    · exact Or.inl ⟨h', h6⟩
    · exact Or.inr ⟨p', hp'P, hp'Q, hp'Δ, by rw [hwk]; exact h⟩

theorem BadData.finrank_of_conj (hw6 : 6 ≤ S.width)
    (hHalf : ∀ (T : Setting G) (DT : S2Data T) (j : G), Bad T j →
      Nonempty (S2Data (T.conjBy j)) → DT.BadData j)
    (hS2a : ∀ g : G, Nonempty (S2Data (S.conjBy g)))
    (hS2b : ∀ g h : G, Nonempty (S2Data ((S.conjBy g).conjBy h)))
    {k : G} (H : D.BadData k) (D' : S2Data (S.conjBy k)) (H' : D'.BadData k⁻¹)
    (hcase : S.QG ⊓ S.Qa k = ⊥ ∨ 8 ≤ S.width) {y : G} (hyQ : y ∈ (S.conjBy k).QG)
    (hyM : y ∈ S.M) (hyc : IsConj (S.conjBy k).z y) {a : Vt (S.conjBy k) D'.g D'.t}
    (haP : a ∈ commSpace (D'.resC ⟨_, H'.hxC⟩)) (ha0 : a ≠ 0)
    (has : D'.QV a = 0) (hcl : (S.conjBy k).cl y = D'.coord (a, 0))
    (hyC : S.ρ ⟨y, hyM⟩ ∈ D.Cbar) :
    finrank (ZMod 2) (commSpace (ρV ⟨_, hyC⟩)) =
      finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) := by
  obtain ⟨h, hh⟩ := isConj_iff.mp hyc
  obtain ⟨Da⟩ := hS2b k h
  have hP := D'.bad_conjBy_of_bad H.bad.symm H'.hxC H'.half H'.fix (H'.prop_hyp D' hw6 hcase)
    (by rw [hh]; exact hyQ) haP ha0 has (by rw [hh]; exact hcl) Da
  have HY := hHalf S D (h * k) (Bad.of_conjBy_conjBy hP) (hS2a (h * k))
  have e : (⟨S.ρ ⟨y, hyM⟩, hyC⟩ : D.Cbar) = ⟨_, HY.hxC⟩ := by
    refine Subtype.ext (congrArg S.ρ (Subtype.ext ?_))
    show y = h * k * S.z * (h * k)⁻¹
    rw [← hh]
    show h * (k * S.z * k⁻¹) * h⁻¹ = h * k * S.z * (h * k)⁻¹
    group
  rw [e]
  exact S2Data.BadData.finrank_eq D H HY

theorem exists_hom_of_le {k : G} (H : D.BadData k) {B : Subgroup G} (hBM : B ≤ S.M)
    (hBL : ∀ y (hy : y ∈ B), S.ρ ⟨y, hBM hy⟩ ∈ S.Lbar k)
    (hBQ1 : ∀ y ∈ B, y ∈ S.QG → y = 1) :
    ∃ φ : B →* (Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t), Function.Injective φ ∧
      ∀ y : B, ∃ hyC : S.ρ ⟨y, hBM y.2⟩ ∈ D.Cbar, φ y = ρV ⟨_, hyC⟩ := by
  choose hC _ using H.lfix
  let ψ : B →* D.Cbar :=
    (S.ρ.comp (Subgroup.inclusion hBM)).codRestrict D.Cbar (fun y => hC _ (hBL y y.2))
  refine ⟨(ρV).comp ψ, ?_, fun y => ⟨hC _ (hBL y y.2), rfl⟩⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : ψ y = 1 := D.resC_injective (hy.trans (map_one _).symm)
  have h2 : S.ρ ⟨y, hBM y.2⟩ = 1 := congrArg Subtype.val h1
  exact Subtype.ext (hBQ1 y y.2 ((S.ρ_eq_one_iff _).mp h2))

theorem BadData.exists_B {k : G} (H : D.BadData k) (D' : S2Data (S.conjBy k))
    (H' : D'.BadData k⁻¹) :
    ∃ B : Subgroup G, B ≤ S.Qa k ∧ B ≤ S.M ∧
      2 ^ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) ≤ Nat.card B ∧
      (∀ y ∈ B, y ≠ 1 → IsConj (S.conjBy k).z y) ∧ (∀ y ∈ B, y ∈ S.QG → y = 1) ∧
      (∀ y ∈ B, y ≠ 1 → y = k * S.z * k⁻¹ ∨
        ∃ a ∈ commSpace (D'.resC ⟨_, H'.hxC⟩), a ≠ 0 ∧
          D'.QV a = 0 ∧ (S.conjBy k).cl y = D'.coord (a, 0)) := by
  obtain ⟨B, hBQ, hBcard, hBcomm, hBform⟩ := S2Data.BadData.exists_subgroup D' H'
  have hzz : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ = S.z := by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group
  have hBM : B ≤ S.M := fun y hy => by
    have := hBcomm y hy
    rw [hzz] at this
    exact mem_centralizer_singleton_iff.mpr this
  have hBconj : ∀ y ∈ B, y ≠ 1 → IsConj (S.conjBy k).z y := fun y hy hy1 => by
    rcases hBform y hy hy1 with h | ⟨a, -, ha0, has, hcl⟩
    · rw [h]
    · have hyz : y ≠ (S.conjBy k).z := by
        intro e
        rw [e, (S.conjBy k).cl_z] at hcl
        have h0 : D'.coord (a, 0) = D'.coord (0, 0) := by
          rw [← hcl, Prod.mk_zero_zero, map_zero]
        exact ha0 (Prod.mk.inj (D'.coord.injective h0)).1
      exact (D'.isConj_z_iff_coord (hBQ hy) hyz).mpr ⟨a, ha0, has, Or.inl hcl⟩
  have hBQ1 : ∀ y ∈ B, y ∈ S.QG → y = 1 := fun y hy hyQ => by
    by_contra hy1
    exact H.bad.not_mem ((S.isConj_conjBy_z_iff k).mp (hBconj y hy hy1)) ⟨hyQ, hBQ hy⟩
  have hm' : finrank (ZMod 2)
      (commSpace (D'.resC ⟨_, H'.hxC⟩)) =
        finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) := by
    have e1 := H'.half
    have e2 := H.half
    rw [S.width_conjBy k] at e1
    omega
  refine ⟨B, hBQ, hBM, hm' ▸ hBcard, hBconj, hBQ1, hBform⟩

theorem BadData.commSpace_eq_of_mem (hw6 : 6 ≤ S.width)
    (hHalf : ∀ (T : Setting G) (DT : S2Data T) (j : G), Bad T j →
      Nonempty (S2Data (T.conjBy j)) → DT.BadData j)
    (hS2a : ∀ g : G, Nonempty (S2Data (S.conjBy g)))
    (hS2b : ∀ g h : G, Nonempty (S2Data ((S.conjBy g).conjBy h)))
    {k : G} (H : D.BadData k) (D' : S2Data (S.conjBy k)) (H' : D'.BadData k⁻¹)
    (hcase : S.QG ⊓ S.Qa k = ⊥ ∨ 8 ≤ S.width) {y : G} (hyQ : y ∈ (S.conjBy k).QG)
    (hyM : y ∈ S.M) (hyc : IsConj (S.conjBy k).z y)
    (hform : y = k * S.z * k⁻¹ ∨
      ∃ a ∈ commSpace (D'.resC ⟨_, H'.hxC⟩), a ≠ 0 ∧
        D'.QV a = 0 ∧ (S.conjBy k).cl y = D'.coord (a, 0))
    (hyC : S.ρ ⟨y, hyM⟩ ∈ D.Cbar)
    (hfix : ∀ v ∈ commSpace (ρV ⟨_, H.hxC⟩), ρV ⟨_, hyC⟩ v = v) :
    commSpace (ρV ⟨_, hyC⟩) = commSpace (ρV ⟨_, H.hxC⟩) := by
  have hPP := D.orthogonal_commSpace_eq (rho_conj_mul_self S H.bad.mem_M) H.half
  have hle : commSpace (ρV ⟨_, hyC⟩) ≤ commSpace (ρV ⟨_, H.hxC⟩) := by
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    have := SMK.sub_mem_orthogonal (D.resC_mem_orthogonalGroup ⟨_, hyC⟩) hfix u
    rwa [hPP] at this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rcases hform with h | ⟨a, haP, ha0, has, hcl⟩
  · have e' : (⟨S.ρ ⟨y, hyM⟩, hyC⟩ : D.Cbar) = ⟨_, H.hxC⟩ :=
      Subtype.ext (congrArg S.ρ (Subtype.ext h))
    rw [e']
  · exact S2Data.BadData.finrank_of_conj D hw6 hHalf hS2a hS2b H D' H' hcase hyQ hyM hyc haP ha0
      has hcl hyC

theorem BadData.exists_image (hw6 : 6 ≤ S.width)
    (hHalf : ∀ (T : Setting G) (DT : S2Data T) (j : G), Bad T j →
      Nonempty (S2Data (T.conjBy j)) → DT.BadData j)
    (hS2a : ∀ g : G, Nonempty (S2Data (S.conjBy g)))
    (hS2b : ∀ g h : G, Nonempty (S2Data ((S.conjBy g).conjBy h)))
    {k : G} (H : D.BadData k) (D' : S2Data (S.conjBy k)) (H' : D'.BadData k⁻¹)
    (hcase : S.QG ⊓ S.Qa k = ⊥ ∨ 8 ≤ S.width) :
    ∃ A : Subgroup (Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t),
      2 ^ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) ≤ Nat.card A ∧
      (∀ e ∈ A, ∀ v, D.QV (e v) = D.QV v) ∧
      (∀ e ∈ A, ∀ p ∈ commSpace (ρV ⟨_, H.hxC⟩), e p = p) ∧
      (∀ e ∈ A, e ≠ 1 → commSpace e = commSpace (ρV ⟨_, H.hxC⟩)) := by
  obtain ⟨B, hBQ, hBM, hBcard, hBconj, hBQ1, hBform⟩ := S2Data.BadData.exists_B D H D' H'
  have hBL : ∀ y (hy : y ∈ B), S.ρ ⟨y, hBM hy⟩ ∈ S.Lbar k := fun y hy =>
    ⟨⟨y, hBM hy⟩, mem_subgroupOf.mpr ⟨hBQ hy, hBM hy⟩, rfl⟩
  obtain ⟨φ, hφinj, hφ⟩ := D.exists_hom_of_le H hBM hBL hBQ1
  have hPP := D.orthogonal_commSpace_eq (rho_conj_mul_self S H.bad.mem_M) H.half
  have hrange : ∀ e ∈ φ.range, ∃ y : B, ∃ hyC : S.ρ ⟨y, hBM y.2⟩ ∈ D.Cbar,
      e = ρV ⟨_, hyC⟩ := by
    rintro e ⟨y, hey⟩
    obtain ⟨hyC, e1⟩ := hφ y
    exact ⟨y, hyC, hey.symm.trans e1⟩
  have hAP : ∀ e ∈ φ.range, ∀ p ∈ commSpace (ρV ⟨_, H.hxC⟩), e p = p := by
    intro e he p hp
    obtain ⟨y, hyC, rfl⟩ := hrange e he
    obtain ⟨hyC', hfix⟩ := H.lfix _ (hBL y y.2)
    exact hfix p hp
  refine ⟨φ.range, ?_, ?_, hAP, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact hBcard
  · intro e he v
    obtain ⟨y, hyC, rfl⟩ := hrange e he
    exact D.QV_resC _ v
  · intro e he hne
    obtain ⟨y, hyC, rfl⟩ := hrange e he
    have hy1 : (y : G) ≠ 1 := by
      intro h
      apply hne
      have : (⟨S.ρ ⟨y, hBM y.2⟩, hyC⟩ : D.Cbar) = 1 := Subtype.ext (by
        show S.ρ ⟨y, hBM y.2⟩ = 1
        rw [show (⟨y, hBM y.2⟩ : S.M) = 1 from Subtype.ext h, map_one])
      rw [this, map_one]
    obtain ⟨hyC', hfix⟩ := H.lfix _ (hBL y y.2)
    exact S2Data.BadData.commSpace_eq_of_mem D hw6 hHalf hS2a hS2b H D' H' hcase (hBQ y.2)
      (hBM y.2) (hBconj y y.2 hy1) (hBform y y.2 hy1) hyC hfix

include D in
theorem false_of_bad (hw6 : 6 ≤ S.width)
    (hHalf : ∀ (T : Setting G) (DT : S2Data T) (j : G), Bad T j →
      Nonempty (S2Data (T.conjBy j)) → DT.BadData j)
    (hS2a : ∀ g : G, Nonempty (S2Data (S.conjBy g)))
    (hS2b : ∀ g h : G, Nonempty (S2Data ((S.conjBy g).conjBy h)))
    {k : G} (hbad : Bad S k) : False := by
  obtain ⟨D'⟩ := hS2a k
  have H := hHalf S D k hbad (hS2a k)
  have H' := hHalf (S.conjBy k) D' k⁻¹ hbad.symm (hS2b k k⁻¹)
  by_cases hcase : S.QG ⊓ S.Qa k = ⊥ ∨ 8 ≤ S.width
  swap
  · push Not at hcase
    obtain ⟨hne, hlt⟩ := hcase
    have hw : S.width = 6 := by
      obtain ⟨r, hr⟩ := D.even_finrank_Vt
      rw [D.finrank_Vt] at hr
      omega
    rcases H.dl with h | h
    · exact hne h
    · exact D.false_of_badData_six H hw h
  obtain ⟨A, hAcard, hAQ, hAP, hfull⟩ :=
    S2Data.BadData.exists_image D hw6 hHalf hS2a hS2b H D' H' hcase
  have hPP := D.orthogonal_commSpace_eq (rho_conj_mul_self S hbad.mem_M) H.half
  have h2 : 2 ≤ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) := by
    have := H.half
    have := D.four_le
    omega
  have hA := card_le_of_commSpace_eq D.QV_nondegenerate hPP h2 A hAQ hAP hfull
  have hlt : 2 ^ (finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) - 1) <
      2 ^ finrank (ZMod 2) (commSpace (ρV ⟨_, H.hxC⟩)) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end Full

end S2Data

end CFSG.GF2Type.Smith1980Orth

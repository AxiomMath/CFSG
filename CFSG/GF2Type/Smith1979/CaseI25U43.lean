module

public import CFSG.GF2Type.Smith1979.CaseI25Weights
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.NineCover
public import CFSG.Open.StatedSUFieldChange

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case25

open CFSG.LieType.Multipliers.U43 (F9 X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
open CFSG.Assembly.LowTwoRank Matrix

namespace U43Weights

abbrev T4 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

abbrev A4 : Type := Multiplicative T4

inductive Gen
  | g1 | g2 | g3 | g4
  deriving DecidableEq

instance : Fintype Gen where
  elems := {.g1, .g2, .g3, .g4}
  complete x := by cases x <;> simp

@[expose] def levMat : Gen → Matrix (Fin 4) (Fin 4) F9
  | .g1 => !![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 2⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩;
    ⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]
  | .g2 => !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨0, 2⟩;
    ⟨0, 2⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨2, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨1, 0⟩]
  | .g3 => !![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 2⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩;
    ⟨2, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨2, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]
  | .g4 => !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, 2⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 2⟩;
    ⟨0, 2⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨1, 0⟩]

theorem det_levMat : ∀ k : Gen, (levMat k).det = 1 := by decide +kernel

theorem levMat_unitary : ∀ k : Gen, ((levMat k).map (· ^ 3))ᵀ * levMat k = 1 := by
  decide +kernel

@[expose] noncomputable def levSU (k : Gen) : StatedSU 4 3 F9 :=
  toSU (levMat k) (det_levMat k) (levMat_unitary k)

@[expose] noncomputable def levBar (k : Gen) : X₀ := QuotientGroup.mk (levSU k)

@[expose] def dot4 (f c : T4) : ZMod 3 :=
  f.1 * c.1 + f.2.1 * c.2.1 + f.2.2.1 * c.2.2.1 + f.2.2.2 * c.2.2.2

@[expose] def mulT (r₀ r₁ r₂ r₃ c : T4) : T4 :=
  (dot4 r₀ c, dot4 r₁ c, dot4 r₂ c, dot4 r₃ c)

@[expose] def vecMulT (r₀ r₁ r₂ r₃ f : T4) : T4 :=
  (f.1 * r₀.1 + f.2.1 * r₁.1 + f.2.2.1 * r₂.1 + f.2.2.2 * r₃.1,
    f.1 * r₀.2.1 + f.2.1 * r₁.2.1 + f.2.2.1 * r₂.2.1 + f.2.2.2 * r₃.2.1,
    f.1 * r₀.2.2.1 + f.2.1 * r₁.2.2.1 + f.2.2.1 * r₂.2.2.1 + f.2.2.2 * r₃.2.2.1,
    f.1 * r₀.2.2.2 + f.2.1 * r₁.2.2.2 + f.2.2.1 * r₂.2.2.2 + f.2.2.2 * r₃.2.2.2)

theorem dot4_mulT (f r₀ r₁ r₂ r₃ c : T4) :
    dot4 f (mulT r₀ r₁ r₂ r₃ c) = dot4 (vecMulT r₀ r₁ r₂ r₃ f) c := by
  simp only [dot4, mulT, vecMulT]
  ring

@[expose] def mAct : Gen → T4 → T4
  | .g1 => mulT (1, 1, 0, 2) (0, 1, 0, 0) (0, 0, 1, 0) (0, 1, 0, 1)
  | .g2 => mulT (1, 1, 1, 0) (0, 1, 0, 0) (0, 2, 1, 0) (0, 0, 0, 1)
  | .g3 => mulT (1, 0, 0, 0) (1, 1, 0, 2) (0, 0, 1, 0) (1, 0, 0, 1)
  | .g4 => mulT (1, 0, 0, 0) (1, 1, 2, 0) (1, 0, 1, 0) (0, 0, 0, 1)

@[expose] def nAct : Gen → T4 → T4
  | .g1 => mulT (1, 1, 0, 1) (0, 1, 0, 0) (0, 0, 1, 0) (0, 2, 0, 1)
  | .g2 => mulT (1, 1, 2, 0) (0, 1, 0, 0) (0, 1, 1, 0) (0, 0, 0, 1)
  | .g3 => mulT (1, 0, 0, 0) (1, 1, 0, 1) (0, 0, 1, 0) (2, 0, 0, 1)
  | .g4 => mulT (1, 0, 0, 0) (1, 1, 1, 0) (2, 0, 1, 0) (0, 0, 0, 1)

@[expose] def tAct : Gen → T4 → T4
  | .g1 => vecMulT (1, 1, 0, 1) (0, 1, 0, 0) (0, 0, 1, 0) (0, 2, 0, 1)
  | .g2 => vecMulT (1, 1, 2, 0) (0, 1, 0, 0) (0, 1, 1, 0) (0, 0, 0, 1)
  | .g3 => vecMulT (1, 0, 0, 0) (1, 1, 0, 1) (0, 0, 1, 0) (2, 0, 0, 1)
  | .g4 => vecMulT (1, 0, 0, 0) (1, 1, 1, 0) (2, 0, 1, 0) (0, 0, 0, 1)

theorem nAct_mAct : ∀ (k : Gen) (c : T4), nAct k (mAct k c) = c := by decide +kernel

theorem mAct_nAct : ∀ (k : Gen) (c : T4), mAct k (nAct k c) = c := by decide +kernel

theorem dot4_add (f c c' : T4) : dot4 f (c + c') = dot4 f c + dot4 f c' := by
  simp only [dot4, Prod.fst_add, Prod.snd_add]
  ring

theorem dot4_neg (f c : T4) : dot4 f (-c) = -dot4 f c := by
  simp only [dot4, Prod.fst_neg, Prod.snd_neg]
  ring

theorem dot4_zero_right (f : T4) : dot4 f 0 = 0 := by
  simp [dot4]

theorem dot4_zero_left (c : T4) : dot4 0 c = 0 := by
  simp [dot4]

theorem mulT_add (r₀ r₁ r₂ r₃ x y : T4) :
    mulT r₀ r₁ r₂ r₃ (x + y) = mulT r₀ r₁ r₂ r₃ x + mulT r₀ r₁ r₂ r₃ y := by
  simp only [mulT, dot4_add, Prod.mk_add_mk]

theorem mAct_add (k : Gen) (x y : T4) : mAct k (x + y) = mAct k x + mAct k y := by
  cases k <;> exact mulT_add _ _ _ _ _ _

theorem dot4_nAct (k : Gen) (f c : T4) : dot4 f (nAct k c) = dot4 (tAct k f) c := by
  cases k <;> exact dot4_mulT _ _ _ _ _ _

@[expose] def sg (k : Gen) : A4 ≃* A4 where
  toFun x := Multiplicative.ofAdd (mAct k x.toAdd)
  invFun x := Multiplicative.ofAdd (nAct k x.toAdd)
  left_inv x := by simp [nAct_mAct]
  right_inv x := by simp [mAct_nAct]
  map_mul' x y := by simp [mAct_add]

theorem levMat_mul_rmat_e1 : ∀ k : Gen, levMat k * rmat 1 0 0 0 =
    rmat (mAct k (1, 0, 0, 0)).1 (mAct k (1, 0, 0, 0)).2.1 (mAct k (1, 0, 0, 0)).2.2.1
      (mAct k (1, 0, 0, 0)).2.2.2 * levMat k := by
  decide +kernel

theorem levMat_mul_rmat_e2 : ∀ k : Gen, levMat k * rmat 0 1 0 0 =
    rmat (mAct k (0, 1, 0, 0)).1 (mAct k (0, 1, 0, 0)).2.1 (mAct k (0, 1, 0, 0)).2.2.1
      (mAct k (0, 1, 0, 0)).2.2.2 * levMat k := by
  decide +kernel

theorem levMat_mul_rmat_e3 : ∀ k : Gen, levMat k * rmat 0 0 1 0 =
    rmat (mAct k (0, 0, 1, 0)).1 (mAct k (0, 0, 1, 0)).2.1 (mAct k (0, 0, 1, 0)).2.2.1
      (mAct k (0, 0, 1, 0)).2.2.2 * levMat k := by
  decide +kernel

theorem levMat_mul_rmat_e4 : ∀ k : Gen, levMat k * rmat 0 0 0 1 =
    rmat (mAct k (0, 0, 0, 1)).1 (mAct k (0, 0, 0, 1)).2.1 (mAct k (0, 0, 0, 1)).2.2.1
      (mAct k (0, 0, 0, 1)).2.2.2 * levMat k := by
  decide +kernel

theorem levBar_conj_of_mat (k : Gen) (x : T4)
    (h : levMat k * rmat x.1 x.2.1 x.2.2.1 x.2.2.2 =
      rmat (mAct k x).1 (mAct k x).2.1 (mAct k x).2.2.1 (mAct k x).2.2.2 * levMat k) :
    levBar k * thetaBar (Multiplicative.ofAdd x) * (levBar k)⁻¹ =
      thetaBar (sg k (Multiplicative.ofAdd x)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg QuotientGroup.mk (ext_matrix h)

theorem hom_ext_A4 {G : Type*} [Group G] {φ ψ : A4 →* G}
    (h1 : φ (Multiplicative.ofAdd (1, 0, 0, 0)) = ψ (Multiplicative.ofAdd (1, 0, 0, 0)))
    (h2 : φ (Multiplicative.ofAdd (0, 1, 0, 0)) = ψ (Multiplicative.ofAdd (0, 1, 0, 0)))
    (h3 : φ (Multiplicative.ofAdd (0, 0, 1, 0)) = ψ (Multiplicative.ofAdd (0, 0, 1, 0)))
    (h4 : φ (Multiplicative.ofAdd (0, 0, 0, 1)) = ψ (Multiplicative.ofAdd (0, 0, 0, 1))) :
    φ = ψ := by
  refine MonoidHom.ext fun x => ?_
  rw [eq_gen_mul x]
  simp only [map_mul, map_pow, h1, h2, h3, h4]

theorem levBar_conj (k : Gen) (x : A4) :
    levBar k * thetaBar x * (levBar k)⁻¹ = thetaBar (sg k x) := by
  have h : (MulAut.conj (levBar k)).toMonoidHom.comp thetaBar = thetaBar.comp (sg k).toMonoidHom :=
    hom_ext_A4
      (levBar_conj_of_mat k (1, 0, 0, 0) (levMat_mul_rmat_e1 k))
      (levBar_conj_of_mat k (0, 1, 0, 0) (levMat_mul_rmat_e2 k))
      (levBar_conj_of_mat k (0, 0, 1, 0) (levMat_mul_rmat_e3 k))
      (levBar_conj_of_mat k (0, 0, 0, 1) (levMat_mul_rmat_e4 k))
  exact DFunLike.congr_fun h x

@[expose] noncomputable def levWord : List Gen → X₀
  | [] => 1
  | k :: w => levBar k * levWord w

@[expose] def sw : List Gen → (A4 ≃* A4)
  | [] => MulEquiv.refl _
  | k :: w => (sw w).trans (sg k)

theorem levWord_conj : ∀ (w : List Gen) (x : A4),
    levWord w * thetaBar x * (levWord w)⁻¹ = thetaBar (sw w x)
  | [], x => by simp [levWord, sw]
  | k :: w, x => by
    show levBar k * levWord w * thetaBar x * (levBar k * levWord w)⁻¹ =
      thetaBar (sg k (sw w x))
    rw [← levBar_conj k (sw w x), ← levWord_conj w x]
    group

@[expose] def kerF (f : T4) : Subgroup A4 where
  carrier := {x | dot4 f x.toAdd = 0}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, toAdd_mul] at hx hy ⊢
    rw [dot4_add, hx, hy, zero_add]
  one_mem' := by simp [dot4]
  inv_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, toAdd_inv] at hx ⊢
    rw [dot4_neg, hx, neg_zero]

theorem mem_kerF (f : T4) (x : A4) : x ∈ kerF f ↔ dot4 f x.toAdd = 0 := Iff.rfl

@[expose] def lead4 (f : T4) : ZMod 3 :=
  if f.1 ≠ 0 then f.1 else if f.2.1 ≠ 0 then f.2.1 else if f.2.2.1 ≠ 0 then f.2.2.1 else f.2.2.2

@[expose] def nrm (f : T4) : T4 :=
  (lead4 f * f.1, lead4 f * f.2.1, lead4 f * f.2.2.1, lead4 f * f.2.2.2)

theorem nrm_nrm : ∀ f : T4, nrm (nrm f) = nrm f := by decide +kernel

theorem eq_zero_of_nrm_eq_zero : ∀ f : T4, nrm f = 0 → f = 0 := by decide +kernel

theorem eq_zero_of_lead4_eq_zero : ∀ f : T4, lead4 f = 0 → f = 0 := by decide +kernel

theorem mul_eq_zero_iff_zmod3 : ∀ s y : ZMod 3, s ≠ 0 → (s * y = 0 ↔ y = 0) := by decide +kernel

theorem dot4_nrm (f c : T4) : dot4 (nrm f) c = lead4 f * dot4 f c := by
  simp only [dot4, nrm]
  ring

theorem kerF_nrm (f : T4) : kerF (nrm f) = kerF f := by
  ext x
  rw [mem_kerF, mem_kerF, dot4_nrm]
  by_cases h : lead4 f = 0
  · have hf := eq_zero_of_lead4_eq_zero f h
    rw [h, hf, zero_mul]
    simp [dot4]
  · exact mul_eq_zero_iff_zmod3 _ _ h

@[expose] def stepF (k : Gen) (f : T4) : T4 := nrm (tAct k f)

theorem map_kerF (k : Gen) (g : T4) :
    (kerF g).map (sg k).toMonoidHom = kerF (tAct k g) := by
  rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.map_equiv_eq_comap_symm]
  ext x
  show dot4 g (nAct k x.toAdd) = 0 ↔ dot4 (tAct k g) x.toAdd = 0
  rw [dot4_nAct]

@[expose] def reach (f : T4) : ℕ → Finset T4
  | 0 => {f}
  | n + 1 => reach f n ∪ (reach f n).biUnion fun g => Finset.univ.image fun k => stepF k g

theorem reach_sound (f : T4) : ∀ (n : ℕ) (g : T4), g ∈ reach f n →
    ∃ w : List Gen, (kerF f).map (sw w).toMonoidHom = kerF g
  | 0, g, hg => by
    rw [reach, Finset.mem_singleton] at hg
    subst hg
    exact ⟨[], by simp [sw]⟩
  | n + 1, g, hg => by
    rw [reach, Finset.mem_union, Finset.mem_biUnion] at hg
    rcases hg with hg | ⟨g', hg', hg''⟩
    · exact reach_sound f n g hg
    · rw [Finset.mem_image] at hg''
      obtain ⟨k, -, rfl⟩ := hg''
      obtain ⟨w, hw⟩ := reach_sound f n g' hg'
      refine ⟨k :: w, ?_⟩
      have hs : (sw (k :: w)).toMonoidHom = (sg k).toMonoidHom.comp (sw w).toMonoidHom := rfl
      rw [hs, ← Subgroup.map_map, hw, map_kerF, stepF, kerF_nrm]

theorem reach_nrm (f : T4) (hf : nrm f = f) : ∀ (n : ℕ) (g : T4), g ∈ reach f n → nrm g = g
  | 0, g, hg => by
    rw [reach, Finset.mem_singleton] at hg
    rw [hg]
    exact hf
  | n + 1, g, hg => by
    rw [reach, Finset.mem_union, Finset.mem_biUnion] at hg
    rcases hg with hg | ⟨g', hg', hg''⟩
    · exact reach_nrm f hf n g hg
    · rw [Finset.mem_image] at hg''
      obtain ⟨k, -, rfl⟩ := hg''
      exact nrm_nrm _

set_option synthInstance.maxSize 512 in
theorem eq_of_nrm_of_dot4 : ∀ f g : T4, nrm f = f → nrm g = g → f ≠ g →
    ∃ c : T4, ¬ (dot4 f c = 0 ↔ dot4 g c = 0) := by
  decide +kernel

theorem kerF_injOn_reach (f : T4) (hf : nrm f = f) (n : ℕ) :
    Set.InjOn kerF (reach f n : Set T4) := by
  intro g hg g' hg' h
  by_contra hne
  obtain ⟨c, hc⟩ := eq_of_nrm_of_dot4 g g' (reach_nrm f hf n g hg) (reach_nrm f hf n g' hg') hne
  have h' := SetLike.ext_iff.mp h (Multiplicative.ofAdd c)
  exact hc (by simpa [mem_kerF] using h')

theorem ten_le_card_reach : ∀ f : T4, nrm f = f → f ≠ 0 → 10 ≤ (reach f 3).card := by
  decide +kernel

theorem exists_functional {H : Subgroup A4} (hH : H.index = 3) :
    ∃ f : T4, f ≠ 0 ∧ H = kerF f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (A4 ⧸ H) = 3 := hH
  have hcard' : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)
  let e : A4 ⧸ H ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hcard hcard'
  let χ : A4 →* Multiplicative (ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' H)
  have hχ : ∀ x : A4, χ x = 1 ↔ x ∈ H := fun x => by
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let f : T4 := ((χ (Multiplicative.ofAdd (1, 0, 0, 0))).toAdd,
    (χ (Multiplicative.ofAdd (0, 1, 0, 0))).toAdd, (χ (Multiplicative.ofAdd (0, 0, 1, 0))).toAdd,
    (χ (Multiplicative.ofAdd (0, 0, 0, 1))).toAdd)
  have hf : ∀ x : A4, (χ x).toAdd = dot4 f x.toAdd := by
    intro x
    conv_lhs => rw [eq_gen_mul x]
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp only [dot4, f]
    ring
  refine ⟨f, ?_, ?_⟩
  · intro h0
    have hall : ∀ x : A4, x ∈ H := fun x => by
      rw [← hχ, ← toAdd_eq_zero, hf x, h0]
      exact dot4_zero_left x.toAdd
    have htop : H = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hH
    omega
  · ext x
    rw [← hχ, mem_kerF, ← toAdd_eq_zero, hf x]

theorem card_reach_le_ncard_orbit (f : T4) (hf : nrm f = f) (n : ℕ) :
    (reach f n).card ≤
      (Set.range fun w : List Gen => (kerF f).map (sw w).toMonoidHom).ncard := by
  have h := Set.ncard_le_ncard_of_injOn (s := (reach f n : Set T4))
    (t := Set.range fun w : List Gen => (kerF f).map (sw w).toMonoidHom) kerF
    (fun g hg => reach_sound f n g hg) (kerF_injOn_reach f hf n) (Set.toFinite _)
  rwa [Set.ncard_coe_finset] at h

theorem ten_le_ncard_orbit (H : Subgroup A4) (hH : H.index = 3) :
    10 ≤ (Set.range fun w : List Gen => H.map (sw w).toMonoidHom).ncard := by
  obtain ⟨f, hf0, hHf⟩ := exists_functional hH
  have h := card_reach_le_ncard_orbit (nrm f) (nrm_nrm f) 3
  rw [kerF_nrm, ← hHf] at h
  exact (ten_le_card_reach (nrm f) (nrm_nrm f) fun h0 => hf0 (eq_zero_of_nrm_eq_zero f h0)).trans h

theorem false_of_faithful {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 12) (φ : X₀ →* (V ≃ₗ[ZMod 2] V))
    (hφ : Function.Injective φ) : False := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  let ρ : Representation (ZMod 2) A4 V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (φ.comp thetaBar)
  have hfaith : Function.Injective ρ := by
    intro x y hxy
    apply thetaBar_injective
    apply hφ
    exact LinearEquiv.ext fun v => LinearMap.congr_fun hxy v
  haveI : Nontrivial A4 := ⟨⟨Multiplicative.ofAdd (1, 0, 0, 0), 1, by decide⟩⟩
  have hβ : ∀ (w : List Gen) (a : A4) (v : V),
      ρ (sw w a) (φ (levWord w) v) = φ (levWord w) (ρ a v) := by
    intro w a v
    have h := levWord_conj w a
    rw [mul_inv_eq_iff_eq_mul] at h
    show φ (thetaBar (sw w a)) (φ (levWord w) v) = φ (levWord w) (φ (thetaBar a) v)
    rw [← LinearEquiv.mul_apply, ← map_mul, ← h, map_mul, LinearEquiv.mul_apply]
  have h := LemmaW.two_mul_le_finrank ρ pow_three_eq_one_gen hfaith (fun w => φ (levWord w)) sw
    hβ (m := 10) ten_le_ncard_orbit
  omega

theorem nonempty_mulEquiv_X₀_of_stated {E : Type} [Group E]
    (h : CFSG.Open.StatedClassicalModel E .PSU 4 3 1) : Nonempty (E ≃* X₀) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]
    norm_num
  exact ⟨e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (3 ^ 1))⟩

end U43Weights

theorem u43NoFaithfulTwelve : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V],
    Module.finrank (ZMod 2) V = 12 → ∀ (E : Subgroup (V ≃ₗ[ZMod 2] V)),
      CFSG.Open.StatedClassicalModel E .PSU 4 3 1 → False := by
  intro V _ _ hV E hE
  obtain ⟨e⟩ := U43Weights.nonempty_mulEquiv_X₀_of_stated hE
  exact U43Weights.false_of_faithful hV (E.subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective)

end CFSG.GF2Type.Smith1979.Case25

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JWr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma sec128_even_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

private lemma sec128_even_add {u v : Fin 5 → ZMod 2} (hu : IsEvenVec u) (hv : IsEvenVec v) :
    IsEvenVec (u + v) := by
  unfold IsEvenVec at hu hv ⊢
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hu, hv, add_zero]

private lemma sec128_coord_zero {V : Type} [Group V] {V1 : Subgroup V}
    {φ : (Fin 5 → ZMod 2) → V} (hc : Sec128Coord V1 φ) : φ 0 = 1 := by
  have h : φ 0 = φ 0 * φ 0 := by
    simpa using hc.mul 0 0 sec128_even_zero sec128_even_zero
  have h2 : φ 0 * 1 = φ 0 * φ 0 := by rw [mul_one]; exact h
  have : (1 : V) = φ 0 := mul_left_cancel h2
  exact this.symm

private lemma sec128_coord_inj {V : Type} [Group V] {V1 : Subgroup V}
    {φ : (Fin 5 → ZMod 2) → V} (hc : Sec128Coord V1 φ) (hsq : ∀ x : V, x * x = 1)
    {u v : Fin 5 → ZMod 2} (hu : IsEvenVec u) (hv : IsEvenVec v) (h : φ u = φ v) :
    u = v := by
  have h1 : φ (u + v) = 1 := by
    rw [hc.mul u v hu hv, h]
    exact hsq (φ v)
  have hzero : u + v = 0 := hc.inj (u + v) (sec128_even_add hu hv) h1
  funext i
  have hi : u i + v i = 0 := by
    simpa using congrFun hzero i
  rw [(add_eq_zero_iff_eq_neg).mp hi, ZMod.neg_eq_self_mod_two]

theorem sec128_V_gen {G : Type} [Group G] {V : Subgroup G}
    {Vq : Multiplicative (ZMod 2) → Subgroup ↥V}
    {φ : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) → ↥V}
    (hcoord : ∀ q, Sec128Coord (Vq q) (φ q))
    (hsup : Vq 1 ⊔ Vq (Multiplicative.ofAdd 1) = ⊤) :
    Subgroup.closure {x : ↥V | ∃ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2),
      IsEvenVec w ∧ φ q w = x} = ⊤ := by
  rw [eq_top_iff, ← hsup]
  refine sup_le ?_ ?_
  · intro x hx
    rcases (hcoord 1).surj x hx with ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨1, w, hw, rfl⟩
  · intro x hx
    rcases (hcoord (Multiplicative.ofAdd 1)).surj x hx with ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨Multiplicative.ofAdd 1, w, hw, rfl⟩

theorem sec128_V_coord_hom {G : Type} [Group G] {V : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) {D B : Subgroup G} (hBD : B ≤ D)
    {φ₀ : (Fin 5 → ZMod 2) → G}
    (hP : IsPermModuleVia IsEvenVec φ₀ B D (alternatingGroup (Fin 5)))
    {Vq : Multiplicative (ZMod 2) → Subgroup ↥V}
    {φ : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) → ↥V}
    (hcoord : ∀ q, Sec128Coord (Vq q) (φ q))
    (hsup : Vq 1 ⊔ Vq (Multiplicative.ofAdd 1) = ⊤)
    (hinf : Vq 1 ⊓ Vq (Multiplicative.ofAdd 1) = ⊥) :
    ∃ ι : ↥V →* WrZ2 ↥D, Function.Injective ι ∧
      (∀ v : ↥V, (ι v).right = 1 ∧ ∀ q, ((ι v).left q : G) ∈ B) ∧
      (∀ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2), IsEvenVec w →
        (ι (φ q w)).right = 1 ∧
          ∀ q', ((ι (φ q w)).left q' : G) = if q' = q then φ₀ w else 1) ∧
      ∀ a : Multiplicative (ZMod 2) → ↥D, (∀ q, (a q : G) ∈ B) → ∃ v : ↥V, ι v = ⟨a, 1⟩ := by
  classical
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with
      mul_comm := fun a b => hV.1.is_comm.comm a b }
  have hsq : ∀ x : ↥V, x * x = 1 := by
    intro x
    apply Subtype.ext
    simpa [pow_two] using hV.2 (x : G) x.2
  have hg : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  have hphi0 : φ₀ 0 = 1 := by
    have h : φ₀ 0 = φ₀ 0 * φ₀ 0 := by
      simpa using hP.1 0 0 sec128_even_zero sec128_even_zero
    have h2 : φ₀ 0 * 1 = φ₀ 0 * φ₀ 0 := by rw [mul_one]; exact h
    have : (1 : G) = φ₀ 0 := mul_left_cancel h2
    exact this.symm
  have hex : ∀ x : ↥V, ∃ u : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2),
      (∀ q, IsEvenVec (u q)) ∧
        x = φ 1 (u 1) * φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) := by
    intro x
    have hx : x ∈ Vq 1 ⊔ Vq (Multiplicative.ofAdd 1) := by
      rw [hsup]; exact Subgroup.mem_top x
    rcases Subgroup.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    rcases (hcoord 1).surj y hy with ⟨u₁, hu₁, hu₁eq⟩
    rcases (hcoord (Multiplicative.ofAdd 1)).surj z hz with ⟨u₂, hu₂, hu₂eq⟩
    refine ⟨fun q => if q = 1 then u₁ else u₂, ?_, ?_⟩
    · intro q
      by_cases hq : q = 1
      · simp [hq, hu₁]
      · simp [hq, hu₂]
    · dsimp only
      rw [if_pos rfl, if_neg hg, hu₁eq, hu₂eq]
      exact hyz.symm
  let coord : ↥V → Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) :=
    fun x => Classical.choose (hex x)
  have coord_spec : ∀ x : ↥V, (∀ q, IsEvenVec (coord x q)) ∧
      x = φ 1 (coord x 1) * φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)) :=
    fun x => Classical.choose_spec (hex x)
  have coord_unique : ∀ (x : ↥V) (u : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2)),
      (∀ q, IsEvenVec (u q)) →
      x = φ 1 (u 1) * φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) →
      coord x = u := by
    intro x u hu hxu
    have hx := coord_spec x
    have habs : φ 1 (coord x 1) * φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)) =
        φ 1 (u 1) * φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) := by
      rw [← hx.2, hxu]
    have heq : (φ 1 (u 1))⁻¹ * φ 1 (coord x 1) =
        φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) *
          (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul]
      calc φ 1 (coord x 1)
          = φ 1 (coord x 1) * 1 := (mul_one _).symm
        _ = φ 1 (coord x 1) *
              (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)) *
                (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹) := by
              rw [mul_inv_cancel]
        _ = (φ 1 (coord x 1) * φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1))) *
              (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹ := by
              rw [mul_assoc]
        _ = (φ 1 (u 1) * φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1))) *
              (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹ := by
              rw [habs]
        _ = φ 1 (u 1) * (φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) *
              (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹) := by
              rw [mul_assoc]
    have hp1 : (φ 1 (u 1))⁻¹ * φ 1 (coord x 1) = 1 := by
      have hmem : (φ 1 (u 1))⁻¹ * φ 1 (coord x 1) ∈
          Vq 1 ⊓ Vq (Multiplicative.ofAdd 1) := by
        refine ⟨?_, ?_⟩
        · exact (Vq 1).mul_mem ((Vq 1).inv_mem ((hcoord 1).mem (u 1) (hu 1)))
            ((hcoord 1).mem (coord x 1) (hx.1 1))
        · rw [heq]
          exact (Vq (Multiplicative.ofAdd 1)).mul_mem
            ((hcoord (Multiplicative.ofAdd 1)).mem (u (Multiplicative.ofAdd 1))
              (hu (Multiplicative.ofAdd 1)))
            ((Vq (Multiplicative.ofAdd 1)).inv_mem
              ((hcoord (Multiplicative.ofAdd 1)).mem (coord x (Multiplicative.ofAdd 1))
                (hx.1 (Multiplicative.ofAdd 1))))
      rwa [hinf, Subgroup.mem_bot] at hmem
    have hleft : φ 1 (coord x 1) = φ 1 (u 1) := (inv_mul_eq_one.mp hp1).symm
    have hq1 : φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) *
        (φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)))⁻¹ = 1 := by
      rw [← heq]; exact hp1
    have hright : φ (Multiplicative.ofAdd 1) (coord x (Multiplicative.ofAdd 1)) =
        φ (Multiplicative.ofAdd 1) (u (Multiplicative.ofAdd 1)) :=
      (mul_inv_eq_one.mp hq1).symm
    have h1 : coord x 1 = u 1 := sec128_coord_inj (hcoord 1) hsq (hx.1 1) (hu 1) hleft
    have h2 : coord x (Multiplicative.ofAdd 1) = u (Multiplicative.ofAdd 1) :=
      sec128_coord_inj (hcoord (Multiplicative.ofAdd 1)) hsq (hx.1 _) (hu _) hright
    funext r
    rcases sec12W_two_pts r with rfl | rfl
    · exact h1
    · exact h2
  have coord_add : ∀ x y : ↥V, coord (x * y) = coord x + coord y := by
    intro x y
    have hx := coord_spec x
    have hy := coord_spec y
    refine coord_unique (x * y) (coord x + coord y) (fun q => sec128_even_add (hx.1 q) (hy.1 q)) ?_
    have e1 := (hcoord 1).mul (coord x 1) (coord y 1) (hx.1 1) (hy.1 1)
    have eg := (hcoord (Multiplicative.ofAdd 1)).mul (coord x (Multiplicative.ofAdd 1))
      (coord y (Multiplicative.ofAdd 1)) (hx.1 _) (hy.1 _)
    conv_lhs => rw [hx.2, hy.2]
    rw [mul_mul_mul_comm, ← e1, ← eg]
    rfl
  have coord_one : coord 1 = 0 := by
    refine coord_unique 1 (fun _ => 0) (fun _ => sec128_even_zero) ?_
    simp [sec128_coord_zero (hcoord 1), sec128_coord_zero (hcoord (Multiplicative.ofAdd 1))]
  have coord_eq_zero : ∀ x : ↥V, coord x = 0 → x = 1 := by
    intro x hx0
    have hx := coord_spec x
    rw [hx0] at hx
    simpa [sec128_coord_zero (hcoord 1), sec128_coord_zero (hcoord (Multiplicative.ofAdd 1))]
      using hx.2
  have coord_phi : ∀ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2), IsEvenVec w →
      coord (φ q w) = fun r => if r = q then w else 0 := by
    intro q w hw
    refine coord_unique (φ q w) (fun r => if r = q then w else 0) (fun r => ?_) ?_
    · by_cases hr : r = q
      · simp [hr, hw]
      · simp [hr, sec128_even_zero]
    · rcases sec12W_two_pts q with rfl | rfl
      · simp [hg, sec128_coord_zero (hcoord (Multiplicative.ofAdd 1))]
      · simp [hg, hg.symm, sec128_coord_zero (hcoord 1)]
  let bfun : ↥V → Multiplicative (ZMod 2) → ↥D := fun x q =>
    ⟨φ₀ (coord x q), hBD ((hP.2.2.1 (φ₀ (coord x q))).mpr
      ⟨coord x q, (coord_spec x).1 q, rfl⟩)⟩
  have bfun_one : bfun 1 = 1 := by
    funext q
    apply Subtype.ext
    change φ₀ (coord 1 q) = (1 : G)
    rw [coord_one]
    exact hphi0
  have bfun_mul : ∀ x y, bfun (x * y) = bfun x * bfun y := by
    intro x y
    funext q
    apply Subtype.ext
    change φ₀ (coord (x * y) q) = φ₀ (coord x q) * φ₀ (coord y q)
    rw [coord_add]
    simpa only [Pi.add_apply] using
      hP.1 (coord x q) (coord y q) ((coord_spec x).1 q) ((coord_spec y).1 q)
  let F : ↥V → WrZ2 ↥D := fun x => sec128WrBase (bfun x)
  let ι : ↥V →* WrZ2 ↥D :=
    { toFun := F
      map_one' := by
        change sec128WrBase (bfun 1) = 1
        rw [bfun_one]
        rfl
      map_mul' := by
        intro x y
        change sec128WrBase (bfun (x * y)) = sec128WrBase (bfun x) * sec128WrBase (bfun y)
        rw [bfun_mul, sec128WrBase_mul] }
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hleft : ∀ q, coord x q = coord y q := by
      intro q
      refine hP.2.1 (coord x q) (coord y q) ((coord_spec x).1 q) ((coord_spec y).1 q) ?_
      have hq : ((ι x).left q : G) = ((ι y).left q : G) :=
        congrArg (fun z : WrZ2 ↥D => ((z.left q : ↥D) : G)) hxy
      change φ₀ (coord x q) = φ₀ (coord y q)
      exact hq
    have hc : coord x = coord y := funext hleft
    rw [(coord_spec x).2, (coord_spec y).2, hc]
  · intro v
    refine ⟨rfl, fun q => ?_⟩
    change φ₀ (coord v q) ∈ B
    exact (hP.2.2.1 (φ₀ (coord v q))).mpr ⟨coord v q, (coord_spec v).1 q, rfl⟩
  · intro q w hw
    refine ⟨rfl, fun q' => ?_⟩
    have hcw := coord_phi q w hw
    change φ₀ (coord (φ q w) q') = if q' = q then φ₀ w else 1
    rw [hcw]
    by_cases hq : q' = q <;> simp [hq, hphi0]
  · intro a ha
    have hw : ∀ q : Multiplicative (ZMod 2), ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧
        φ₀ v = (a q : G) := fun q => (hP.2.2.1 (a q : G)).mp (ha q)
    choose w hw_even hw_eq using hw
    refine ⟨φ 1 (w 1) * φ (Multiplicative.ofAdd 1) (w (Multiplicative.ofAdd 1)), ?_⟩
    have hco : coord (φ 1 (w 1) * φ (Multiplicative.ofAdd 1) (w (Multiplicative.ofAdd 1))) = w :=
      coord_unique _ w hw_even rfl
    apply RegularWreathProduct.ext
    · funext q
      apply Subtype.ext
      change φ₀ (coord (φ 1 (w 1) * φ (Multiplicative.ofAdd 1) (w (Multiplicative.ofAdd 1))) q) =
        (a q : G)
      rw [hco]
      exact hw_eq q
    · rfl

end CFSG.OddStandard.SmallF3.Omega

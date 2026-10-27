module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I131

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def indL (L : Subgroup G) (t : ↥(Subgroup.normalizer (L : Set G))) : ↥L ≃* ↥L where
  toFun l := ⟨(t : G) * l * (t : G)⁻¹, (Subgroup.mem_normalizer_iff.1 t.2 l).1 l.2⟩
  invFun l := ⟨(t : G)⁻¹ * l * (t : G), (Subgroup.mem_normalizer_iff''.1 t.2 l).1 l.2⟩
  left_inv l := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv l := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' l m := by
    apply Subtype.ext
    simp [mul_assoc]

@[simp] theorem indL_apply (L : Subgroup G) (t : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    ((indL L t l : ↥L) : G) = (t : G) * (l : G) * (t : G)⁻¹ :=
  rfl

@[expose] def psiL (L : Subgroup G) : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥L where
  toFun t := indL L t
  map_one' := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    simp [indL_apply]
  map_mul' s t := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    simp [indL_apply, mul_assoc, MulAut.mul_apply]

theorem congr_mk_apply {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (e : H ≃* H)
    (he : N.map (MulEquiv.toMonoidHom e) = N) (h : H) :
    QuotientGroup.congr N N e he (QuotientGroup.mk h) = QuotientGroup.mk (e h) :=
  rfl

@[expose] def quotAut {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {K : Type*} [Group K]
    (ψ : K →* MulAut H) (hψ : ∀ k, N.map (MulEquiv.toMonoidHom (ψ k)) = N) :
    K →* MulAut (H ⧸ N) where
  toFun k := QuotientGroup.congr N N (ψ k) (hψ k)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    show QuotientGroup.congr N N (ψ 1) (hψ 1) (QuotientGroup.mk h) =
      (1 : MulAut (H ⧸ N)) (QuotientGroup.mk h)
    rw [congr_mk_apply, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' k k' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    show QuotientGroup.congr N N (ψ (k * k')) (hψ (k * k')) (QuotientGroup.mk h) =
      (QuotientGroup.congr N N (ψ k) (hψ k) * QuotientGroup.congr N N (ψ k') (hψ k'))
        (QuotientGroup.mk h)
    rw [MulAut.mul_apply, congr_mk_apply, congr_mk_apply, congr_mk_apply, map_mul,
      MulAut.mul_apply]

theorem quotAut_mk {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {K : Type*} [Group K]
    (ψ : K →* MulAut H) (hψ : ∀ k, N.map (MulEquiv.toMonoidHom (ψ k)) = N) (k : K) (h : H) :
    quotAut N ψ hψ k (QuotientGroup.mk h) = QuotientGroup.mk (ψ k h) :=
  congr_mk_apply N (ψ k) (hψ k) h

theorem map_glaPPrimeCore_indL (p : ℕ) [Fact p.Prime] (L : Subgroup G)
    (t : ↥(Subgroup.normalizer (L : Set G))) :
    (GLAPPrimeCore p ↥L).map (MulEquiv.toMonoidHom (indL L t)) ≤ GLAPPrimeCore p ↥L :=
  CFSG.map_pPrimeCore_le (MulEquiv.toMonoidHom (indL L t)) (indL L t).surjective

theorem map_glaPPrimeCore_indL_eq (p : ℕ) [Fact p.Prime] (L : Subgroup G)
    (t : ↥(Subgroup.normalizer (L : Set G))) :
    (GLAPPrimeCore p ↥L).map (MulEquiv.toMonoidHom (indL L t)) = GLAPPrimeCore p ↥L := by
  apply le_antisymm (map_glaPPrimeCore_indL p L t)
  intro x hx
  let t' : ↥(Subgroup.normalizer (L : Set G)) := ⟨(t : G)⁻¹, Subgroup.inv_mem _ t.2⟩
  have hx' : indL L t' x ∈ GLAPPrimeCore p ↥L :=
    map_glaPPrimeCore_indL p L t' ⟨x, hx, rfl⟩
  refine ⟨indL L t' x, hx', ?_⟩
  apply Subtype.ext
  simp [indL_apply, t', mul_assoc]

@[expose] def indQ (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (PQuot p L) :=
  quotAut (GLAPPrimeCore p ↥L) (psiL L) (fun t => map_glaPPrimeCore_indL_eq p L t)

theorem indQ_mk (p : ℕ) [Fact p.Prime] (L : Subgroup G) (t : ↥(Subgroup.normalizer (L : Set G)))
    (x : ↥L) : indQ p L t (QuotientGroup.mk x) = QuotientGroup.mk (indL L t x) :=
  quotAut_mk _ _ _ t x

theorem map_center_indQ (p : ℕ) [Fact p.Prime] (L : Subgroup G)
    (t : ↥(Subgroup.normalizer (L : Set G))) :
    (Subgroup.center (PQuot p L)).map (MulEquiv.toMonoidHom (indQ p L t)) =
      Subgroup.center (PQuot p L) :=
  Subgroup.map_center_eq (indQ p L t)

@[expose] def indS (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (PSimple p L) :=
  quotAut (Subgroup.center (PQuot p L)) (indQ p L) (fun t => map_center_indQ p L t)

theorem indS_mk (p : ℕ) [Fact p.Prime] (L : Subgroup G) (t : ↥(Subgroup.normalizer (L : Set G)))
    (x : ↥L) :
    indS p L t (QuotientGroup.mk (QuotientGroup.mk x)) =
      QuotientGroup.mk (QuotientGroup.mk (indL L t x)) := by
  unfold indS
  rw [quotAut_mk, indQ_mk]

@[expose] def piS (p : ℕ) [Fact p.Prime] (L : Subgroup G) : ↥L →* PSimple p L :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))

theorem piS_apply (p : ℕ) [Fact p.Prime] (L : Subgroup G) (x : ↥L) :
    piS p L x = QuotientGroup.mk (QuotientGroup.mk x) :=
  rfl

theorem indS_piS (p : ℕ) [Fact p.Prime] (L : Subgroup G) (t : ↥(Subgroup.normalizer (L : Set G)))
    (x : ↥L) : indS p L t (piS p L x) = piS p L (indL L t x) :=
  indS_mk p L t x

theorem glaPPrimeCoreOf_eq_map (p : ℕ) (L : Subgroup G) :
    GLAPPrimeCoreOf p L = (GLAPPrimeCore p ↥L).map L.subtype :=
  rfl

theorem centMod_of_indS_eq_one (p : ℕ) [Fact p.Prime] {L : Subgroup G}
    (hperf : commutator (PQuot p L) = ⊤) (t : ↥(Subgroup.normalizer (L : Set G)))
    (ht : indS p L t = 1) : (t : G) ∈ centModSubgroup p L := by
  have hβc : ∀ x : PQuot p L, (indQ p L t x)⁻¹ * x ∈ Subgroup.center (PQuot p L) := by
    intro x
    have h1 : indS p L t (QuotientGroup.mk x) = QuotientGroup.mk (indQ p L t x) := by
      unfold indS
      exact quotAut_mk _ _ _ t x
    have h2 : indS p L t (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [ht, MulAut.one_apply]
    rw [h1] at h2
    exact QuotientGroup.eq.1 h2
  let F : PQuot p L →* ↥(Subgroup.center (PQuot p L)) :=
    MonoidHom.mk' (fun x => (⟨(indQ p L t x)⁻¹ * x, hβc x⟩ : ↥(Subgroup.center (PQuot p L))))
      (by
        intro x y
        apply Subtype.ext
        show (indQ p L t (x * y))⁻¹ * (x * y) = ((indQ p L t x)⁻¹ * x) * ((indQ p L t y)⁻¹ * y)
        rw [map_mul]
        have hc := Subgroup.mem_center_iff.1 (hβc x) ((indQ p L t y)⁻¹)
        calc (indQ p L t x * indQ p L t y)⁻¹ * (x * y)
            = (indQ p L t y)⁻¹ * ((indQ p L t x)⁻¹ * x) * y := by group
          _ = ((indQ p L t x)⁻¹ * x) * (indQ p L t y)⁻¹ * y := by rw [hc]
          _ = ((indQ p L t x)⁻¹ * x) * ((indQ p L t y)⁻¹ * y) := by group)
  have hker : commutator (PQuot p L) ≤ F.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 ?_
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (hβc a) ((indQ p L t b)⁻¹ * b)).symm
  have htop : (⊤ : Subgroup (PQuot p L)) ≤ F.ker := hperf ▸ hker
  have hβid : ∀ x : PQuot p L, indQ p L t x = x := by
    intro x
    have hx := (MonoidHom.mem_ker).1 (htop (Subgroup.mem_top x))
    have hx' : (indQ p L t x)⁻¹ * x = 1 := congrArg Subtype.val hx
    exact inv_mul_eq_one.1 hx'
  rw [mem_centModSubgroup]
  refine ⟨t.2, fun l hl => ?_⟩
  let x : ↥L := ⟨l, hl⟩
  have hxβ : indQ p L t (QuotientGroup.mk x) = QuotientGroup.mk x := hβid _
  rw [indQ_mk] at hxβ
  have hu : (indL L t x)⁻¹ * x ∈ GLAPPrimeCore p ↥L := QuotientGroup.eq.1 hxβ
  have key : ⁅l, (t : G)⁆ = ((x * ((indL L t x)⁻¹ * x) * x⁻¹ : ↥L) : G) := by
    simp [indL_apply, commutatorElement_def, mul_assoc, mul_inv_rev, x]
  rw [key, glaPPrimeCoreOf_eq_map]
  exact Subgroup.mem_map.2 ⟨_, (GLAPPrimeCore.normal p ↥L).conj_mem _ hu x, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.I131

end

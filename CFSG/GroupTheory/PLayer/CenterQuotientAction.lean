module

public import CFSG.GroupTheory.PLayer.CentralQuotient
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupTheory.NormalizerConjFixedPoints

public section

namespace CFSG

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {Y : Type} [Group Y]

@[expose] noncomputable def normalizerConjAutOfMem (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) : MulAut ↥K :=
  (Subgroup.normalizerMonoidHom (H := K)) (Subgroup.inclusion hBN b)

@[expose] noncomputable def normalizerToCenterQuotientAut (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) :
    ↥B →* MulAut (↥K ⧸ Subgroup.center ↥K) where
  toFun b :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K)
      ((Subgroup.normalizerMonoidHom (H := K)) (Subgroup.inclusion hBN b))
      (Subgroup.map_center_eq _)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk]
      simp
  map_mul' b c := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk]
      simp

theorem normalizerConjAutOfMem_comp_mk (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) (k : ↥K) :
    (QuotientGroup.mk' (Subgroup.center ↥K)) (normalizerConjAutOfMem K B hBN b k) =
      normalizerToCenterQuotientAut K B hBN b
        ((QuotientGroup.mk' (Subgroup.center ↥K)) k) :=
  rfl

theorem normalizerToCenterQuotientAut_eq_one_iff {K : Subgroup Y}
    (hperf : Group.IsPerfect ↥K) {B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) :
    normalizerToCenterQuotientAut K B hBN b = 1 ↔
      (b : Y) ∈ B ⊓ Subgroup.centralizer (K : Set Y) := by
  constructor
  · intro h
    have hβ1 : normalizerConjAutOfMem K B hBN b = 1 := by
      have hcentral : ∀ k : ↥K,
          k⁻¹ * (normalizerConjAutOfMem K B hBN b) k ∈ Subgroup.center ↥K := by
        intro k
        have h2 : (QuotientGroup.mk' (Subgroup.center ↥K))
            ((normalizerConjAutOfMem K B hBN b) k) =
            (QuotientGroup.mk' (Subgroup.center ↥K)) k := by
          have := congrArg (fun φ : MulAut (↥K ⧸ Subgroup.center ↥K) =>
            φ ((QuotientGroup.mk' (Subgroup.center ↥K)) k)) h
          simpa only [normalizerConjAutOfMem_comp_mk, MulAut.one_apply] using this
        exact QuotientGroup.eq.mp h2.symm
      let z : ↥K →* ↥K :=
        { toFun := fun k => k⁻¹ * (normalizerConjAutOfMem K B hBN b) k
          map_one' := by simp
          map_mul' := fun s t => by
            have ht := Subgroup.mem_center_iff.mp (hcentral s)
            calc (s * t)⁻¹ * (normalizerConjAutOfMem K B hBN b) (s * t)
                = t⁻¹ * (s⁻¹ * (normalizerConjAutOfMem K B hBN b) s) *
                    (normalizerConjAutOfMem K B hBN b) t := by
                    rw [map_mul]; group
              _ = s⁻¹ * (normalizerConjAutOfMem K B hBN b) s *
                    (t⁻¹ * (normalizerConjAutOfMem K B hBN b) t) := by
                    rw [ht t⁻¹]; group }
      have hcomm : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ ≤ z.ker := by
        rw [Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have hab := Subgroup.mem_center_iff.mp (hcentral a) (z b)
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hab.symm
      have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ :=
        Group.IsPerfect.commutator_eq_top
      rw [htop] at hcomm
      refine MulEquiv.ext fun s => ?_
      have hs : z s = 1 := hcomm (Subgroup.mem_top s)
      change s⁻¹ * (normalizerConjAutOfMem K B hBN b) s = 1 at hs
      rw [MulAut.one_apply]
      exact (inv_mul_eq_one.mp hs).symm
    have hβk : ∀ k : ↥K, normalizerConjAutOfMem K B hBN b k = k := by
      intro k
      rw [hβ1]
      rfl
    have hbK : (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h4 : (b : Y) * k * (b : Y)⁻¹ = k := by
        have := congrArg (fun w : ↥K => (w : Y)) (hβk ⟨k, hk⟩)
        simpa [normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
      have h5 : (b : Y) * k = k * (b : Y) := by
        rwa [mul_inv_eq_iff_eq_mul] at h4
      exact h5.symm
    exact Subgroup.mem_inf.2 ⟨b.2, hbK⟩
  · rintro ⟨-, hbC⟩
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hβ : normalizerConjAutOfMem K B hBN b k = k := by
        apply Subtype.ext
        change ((Subgroup.normalizerMonoidHom (H := K))
          (Subgroup.inclusion hBN b) k : Y) = (k : Y)
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        show (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y)
        rw [(Subgroup.mem_centralizer_iff.1 hbC (k : Y) k.2).symm, mul_inv_cancel_right]
      change (normalizerToCenterQuotientAut K B hBN) b
        ((QuotientGroup.mk' (Subgroup.center ↥K)) k) =
          (1 : MulAut (↥K ⧸ Subgroup.center ↥K))
            ((QuotientGroup.mk' (Subgroup.center ↥K)) k)
      rw [← normalizerConjAutOfMem_comp_mk, hβ]
      rfl

theorem ker_normalizerToCenterQuotientAut {K : Subgroup Y}
    (hperf : Group.IsPerfect ↥K) {B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) :
    (normalizerToCenterQuotientAut K B hBN).ker =
      (B ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, normalizerToCenterQuotientAut_eq_one_iff hperf hBN b,
    Subgroup.mem_subgroupOf]

theorem card_range_normalizerToCenterQuotientAut {K : Subgroup Y}
    (hperf : Group.IsPerfect ↥K) {B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) :
    Nat.card (normalizerToCenterQuotientAut K B hBN).range =
      (B ⊓ Subgroup.centralizer (K : Set Y)).relIndex B := by
  rw [← Subgroup.index_ker (normalizerToCenterQuotientAut K B hBN),
    ker_normalizerToCenterQuotientAut hperf hBN]
  rfl

theorem glaPLayer_map_eq_of_injective {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {p : ℕ} (hp : p.Prime)
    (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    (GLAPLayer p X).map f = GLAPLayer p (X.map f) :=
  CFSG.glaPLayer_map_eq_of_ker_le_center (p := p) hp f (fun y hy x _ => by
    have hy1 : y = 1 := hf (by simpa using hy.2)
    rw [hy1, mul_one, one_mul]) (X := X)

theorem glaPLayer_fixSubgroup_map_eq [Finite Y] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup Y} (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) :
    (GLAPLayer p (fixSubgroup (normalizerConjAutOfMem K B hBN b))).map K.subtype =
      GLAPLayer p (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) := by
  have hsub : (fixSubgroup (normalizerConjAutOfMem K B hBN b)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    rw [show normalizerConjAutOfMem K B hBN b =
        (Subgroup.normalizerMonoidHom (H := K)) ⟨(b : Y), hBN b.2⟩ from rfl]
    exact CFSG.map_eqLocus_normalizerMonoidHom K (hBN b.2)
  rw [← hsub]
  exact glaPLayer_map_eq_of_injective hp K.subtype K.subtype_injective _

theorem glaPLayer_inf_centralizer_eq_bot_iff [Finite Y] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup Y} (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) :
    GLAPLayer p (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) = ⊥ ↔
      GLAPLayer p (fixSubgroup (normalizerToCenterQuotientAut K B hBN b)) = ⊥ := by
  set π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  set β : MulAut ↥K := normalizerConjAutOfMem K B hBN b
  set ψ : MulAut (↥K ⧸ Subgroup.center ↥K) := normalizerToCenterQuotientAut K B hBN b
  have hY : (GLAPLayer p (fixSubgroup β)).map K.subtype =
      GLAPLayer p (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) :=
    glaPLayer_fixSubgroup_map_eq (p := p) hp hBN b
  have hQ : (GLAPLayer p (fixSubgroup β)).map π =
      GLAPLayer p (fixSubgroup ψ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_glaPLayer_fixSubgroup_eq π
      (by rw [show π.ker = Subgroup.center ↥K from QuotientGroup.ker_mk' _]) β ψ
      (fun k => normalizerConjAutOfMem_comp_mk K B hBN b k)
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)) hp
  have hβY : GLAPLayer p (fixSubgroup β) = ⊥ ↔
      GLAPLayer p (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) = ⊥ := by
    rw [← hY]
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).symm
  have hβQ : GLAPLayer p (fixSubgroup β) = ⊥ ↔ GLAPLayer p (fixSubgroup ψ) = ⊥ := by
    have hker : π.ker ≤ Subgroup.center ↥K := by
      rw [show π.ker = Subgroup.center ↥K from QuotientGroup.ker_mk' _]
    have hc : ∀ y ∈ fixSubgroup β ⊓ π.ker, ∀ x ∈ fixSubgroup β, x * y = y * x := by
      intro y hy x _
      exact Subgroup.mem_center_iff.1 (hker hy.2) x
    have hmap : GLAPLayer p (Subgroup.map π (fixSubgroup β)) =
        GLAPLayer p (fixSubgroup ψ) := by
      rw [← CFSG.glaPLayer_map_eq_of_ker_le_center (p := p) hp π hc
        (X := fixSubgroup β)]
      exact hQ
    have hne : GLAPLayer p (fixSubgroup β) ≠ ⊥ ↔
        GLAPLayer p (fixSubgroup ψ) ≠ ⊥ := by
      have h := CFSG.glaPLayer_ne_bot_iff_map_ne_bot (p := p) hp π hc
        (X := fixSubgroup β)
      rwa [hmap] at h
    exact not_iff_not.mp hne
  exact hβY.symm.trans hβQ

end CFSG

end

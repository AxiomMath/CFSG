module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAmb
public import CFSG.CGT.PushingUpLit.CGT6.EmbeddingNodes
public import CFSG.CGT.PushingUpLit.SixThreeShort

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Yu

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

@[expose] def yuProj : ↥(yuHol Y) →* ↥Y where
  toFun x := ⟨x.1.right, x.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def yuSec : ↥Y →* ↥(yuHol Y) where
  toFun α := ⟨⟨1, (α : MulAut V)⟩, one_mem _, α.2⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (SemidirectProduct.ext (by simp) rfl)

@[expose] def yuInc : ↥(commV Y) →* ↥(yuHol Y) where
  toFun u := ⟨⟨(u : V), 1⟩, u.2, one_mem _⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (SemidirectProduct.ext (by simp) (by simp))

@[simp] theorem yuProj_sec (α : ↥Y) : yuProj Y (yuSec Y α) = α := rfl

@[simp] theorem yuProj_inc (u : ↥(commV Y)) : yuProj Y (yuInc Y u) = 1 := rfl

theorem yuProj_surjective : Function.Surjective (yuProj Y) := fun α => ⟨yuSec Y α, rfl⟩

theorem yuInc_injective : Function.Injective (yuInc Y) := fun _ _ h =>
  Subtype.ext (congrArg (fun x : ↥(yuHol Y) => x.1.left) h)

theorem yuSec_injective : Function.Injective (yuSec Y) := fun _ _ h =>
  Subtype.ext (congrArg (fun x : ↥(yuHol Y) => x.1.right) h)

theorem mem_ker_yuProj {x : ↥(yuHol Y)} : x ∈ (yuProj Y).ker ↔ x.1.right = 1 := by
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem ker_yuProj : (yuProj Y).ker = (yuInc Y).range := by
  ext x
  rw [mem_ker_yuProj, MonoidHom.mem_range]
  constructor
  · intro h
    exact ⟨⟨x.1.left, x.2.1⟩,
      Subtype.ext (SemidirectProduct.ext (by simp [yuInc]) (by simp [yuInc, h]))⟩
  · rintro ⟨u, rfl⟩
    rfl

theorem yu_eq_inc_mul_sec (x : ↥(yuHol Y)) :
    x = yuInc Y ⟨x.1.left, x.2.1⟩ * yuSec Y ⟨x.1.right, x.2.2⟩ :=
  Subtype.ext (SemidirectProduct.ext (by simp [yuInc, yuSec]) (by simp [yuInc, yuSec]))

theorem apply_mem_commV_self {α : MulAut V} (hα : α ∈ Y) {u : V} (hu : u ∈ commV Y) :
    α u ∈ commV Y :=
  G6.apply_mem_commV (fun _ hx => Y.mul_mem (Y.mul_mem hα hx) (Y.inv_mem hα)) hu

theorem conj_yuInc (x : ↥(yuHol Y)) (u : ↥(commV Y)) :
    x * yuInc Y u * x⁻¹ = yuInc Y ⟨x.1.right u, apply_mem_commV_self Y x.2.2 u.2⟩ := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · simp only [yuInc, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      MonoidHom.id_apply, mul_one]
    rw [MulAut.apply_inv_self, mul_comm (x.1.left), mul_assoc, mul_inv_cancel, mul_one]
  · simp [yuInc]

theorem comm_yuInc_yuSec (α : ↥Y) (u : ↥(commV Y)) :
    ⁅yuInc Y u, yuSec Y α⁆ = yuInc Y ⟨(u : V) * (α : MulAut V) (u : V)⁻¹,
      mul_mem u.2 (apply_mem_commV_self Y α.2 (inv_mem u.2))⟩ := by
  have h := conj_yuInc Y (yuSec Y α) u⁻¹
  calc ⁅yuInc Y u, yuSec Y α⁆
      = yuInc Y u * (yuSec Y α * (yuInc Y u)⁻¹ * (yuSec Y α)⁻¹) := by
        rw [commutatorElement_def]
        group
    _ = yuInc Y u * yuInc Y ⟨(α : MulAut V) (u : V)⁻¹,
          apply_mem_commV_self Y α.2 (inv_mem u.2)⟩ := by
        rw [← map_inv (yuInc Y) u, h]
        rfl
    _ = _ := by
        rw [← map_mul]
        rfl

theorem yuInc_comm (u w : ↥(commV Y)) : yuInc Y u * yuInc Y w = yuInc Y w * yuInc Y u := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem yuInc_sq (hV : ∀ v : V, v ^ 2 = 1) (u : ↥(commV Y)) : yuInc Y u ^ 2 = 1 := by
  rw [← map_pow]
  have : u ^ 2 = 1 := Subtype.ext (by simpa using hV (u : V))
  rw [this, map_one]

end Yu

section Amb

variable {G : Type} [Group G] (V : Subgroup G) [V.Normal] (A : Subgroup G)

@[expose] noncomputable def rhoA : ↥A →* ↥(autOn A V) :=
  ((ambRho V).comp A.subtype).codRestrict (autOn A V) fun x => by
    rw [← map_ambRho V A]
    exact ⟨x, x.2, rfl⟩

theorem rhoA_surjective : Function.Surjective (rhoA V A) := by
  rintro ⟨x, hx⟩
  rw [← map_ambRho V A] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨⟨g, hg⟩, rfl⟩

theorem mem_ker_rhoA {a : ↥A} :
    a ∈ (rhoA V A).ker ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker, ← ker_ambRho V, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

@[expose] def KTwo : Prop := ∀ a : ↥A, a ∈ (rhoA V A).ker → ∃ k : ℕ, a ^ 2 ^ k = 1

variable {V A}

theorem kTwo_of_isPGroup (h : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G))) :
    KTwo V A := by
  intro a ha
  rw [mem_ker_rhoA] at ha
  obtain ⟨k, hk⟩ := h ⟨(a : G), a.2, ha⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem kTwo_of_le_oTwoIn (h : A ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn A) : KTwo V A := by
  refine kTwo_of_isPGroup ?_
  exact (SixThree.isPGroup_oTwoIn A).to_le h

theorem ker_rhoA_le_pCore (hK : KTwo V A) : (rhoA V A).ker ≤ pCore 2 ↥A := by
  have hp : IsPGroup 2 ↥(rhoA V A).ker := fun g => by
    obtain ⟨k, hk⟩ := hK g g.2
    exact ⟨k, Subtype.ext hk⟩
  exact le_sSup ⟨inferInstance, hp⟩

end Amb

section Phi

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
  (A : Subgroup G)

@[expose] noncomputable def projPhi : ↥(yuHolOf hV (autOn A V)) →* ↥(autOn A V) :=
  @yuProj ↥V (commGroupOfElemAbelian hV) (autOn A V)

@[expose] noncomputable def secPhi : ↥(autOn A V) →* ↥(yuHolOf hV (autOn A V)) :=
  @yuSec ↥V (commGroupOfElemAbelian hV) (autOn A V)

@[expose] noncomputable def incPhi : ↥(commOn hV A) →* ↥(yuHolOf hV (autOn A V)) :=
  @yuInc ↥V (commGroupOfElemAbelian hV) (autOn A V)

@[expose] noncomputable def sigPhi : ↥A →* ↥(yuHolOf hV (autOn A V)) :=
  (secPhi hV A).comp (rhoA V A)

omit [V.Normal] in
theorem projPhi_surjective : Function.Surjective (projPhi hV A) :=
  @yuProj_surjective ↥V (commGroupOfElemAbelian hV) (autOn A V)

omit [V.Normal] in
theorem ker_projPhi : (projPhi hV A).ker = (incPhi hV A).range :=
  @ker_yuProj ↥V (commGroupOfElemAbelian hV) (autOn A V)

omit [V.Normal] in
theorem sq_eq_one_of_mem_ker_projPhi {x : ↥(yuHolOf hV (autOn A V))}
    (hx : x ∈ (projPhi hV A).ker) : x ^ 2 = 1 := by
  rw [ker_projPhi hV A] at hx
  obtain ⟨u, rfl⟩ := hx
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  exact @yuInc_sq ↥V (commGroupOfElemAbelian hV) (autOn A V) hV2 u

theorem pCore_phi (hK : KTwo V A) :
    pCore 2 ↥(yuHolOf hV (autOn A V)) =
      ((pCore 2 ↥A).map (rhoA V A)).comap (projPhi hV A) := by
  apply le_antisymm
  · set P := pCore 2 ↥(yuHolOf hV (autOn A V)) with hP
    have hPn : P.Normal := inferInstance
    have hP2 : IsPGroup 2 ↥P := pCore_isPGroup (p := 2) (G := ↥(yuHolOf hV (autOn A V)))
    set S : Subgroup ↥(autOn A V) := P.map (projPhi hV A) with hS
    have hSn : S.Normal := hPn.map _ (projPhi_surjective hV A)
    have hS2 : IsPGroup 2 ↥S := hP2.map _
    have hNn : (S.comap (rhoA V A)).Normal := hSn.comap _
    have hN2 : IsPGroup 2 ↥(S.comap (rhoA V A)) := by
      rintro ⟨a, ha⟩
      obtain ⟨k₁, hk₁⟩ := hS2 ⟨rhoA V A a, ha⟩
      have h1 : rhoA V A (a ^ 2 ^ k₁) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk₁
      obtain ⟨k₂, hk₂⟩ := hK _ (MonoidHom.mem_ker.mpr h1)
      exact ⟨k₁ + k₂, Subtype.ext (by simpa [pow_add, pow_mul] using hk₂)⟩
    have hNle : S.comap (rhoA V A) ≤ pCore 2 ↥A := le_sSup ⟨hNn, hN2⟩
    intro x hx
    obtain ⟨a, ha⟩ := rhoA_surjective V A (projPhi hV A x)
    have hxS : projPhi hV A x ∈ S := ⟨x, hx, rfl⟩
    rw [← ha] at hxS
    exact ⟨a, hNle hxS, ha⟩
  · set N := ((pCore 2 ↥A).map (rhoA V A)).comap (projPhi hV A) with hN
    have hNn : N.Normal :=
      (Subgroup.Normal.map (inferInstance : (pCore 2 ↥A).Normal) _
        (rhoA_surjective V A)).comap _
    have hN2 : IsPGroup 2 ↥N := by
      rintro ⟨x, hx⟩
      obtain ⟨q, hq, hqx⟩ := hx
      obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := ↥A) ⟨q, hq⟩
      have h1 : projPhi hV A (x ^ 2 ^ k) = 1 := by
        rw [map_pow, ← hqx, ← map_pow]
        have : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
        rw [this, map_one]
      have h2 := sq_eq_one_of_mem_ker_projPhi hV A (MonoidHom.mem_ker.mpr h1)
      refine ⟨k + 1, Subtype.ext ?_⟩
      have h3 : x ^ 2 ^ (k + 1) = 1 := by
        rw [pow_succ, pow_mul]
        exact h2
      exact h3
    exact le_sSup ⟨hNn, hN2⟩

@[expose] noncomputable def lamHat (hK : KTwo V A) : ↥(autOn A V) →* ↥A ⧸ pCore 2 ↥A :=
  (rhoA V A).liftOfSurjective (rhoA_surjective V A)
    ⟨QuotientGroup.mk' (pCore 2 ↥A), fun a ha => by
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ker_rhoA_le_pCore hK ha⟩

theorem lamHat_rhoA (hK : KTwo V A) (a : ↥A) :
    lamHat A hK (rhoA V A a) = (a : ↥A ⧸ pCore 2 ↥A) :=
  MonoidHom.liftOfRightInverse_comp_apply (rhoA V A) _ _ ⟨QuotientGroup.mk' (pCore 2 ↥A), _⟩ a

theorem lamHat_surjective (hK : KTwo V A) : Function.Surjective (lamHat A hK) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨rhoA V A a, lamHat_rhoA A hK a⟩

@[expose] noncomputable def lamPhi (hK : KTwo V A) :
    ↥(yuHolOf hV (autOn A V)) →* ↥A ⧸ pCore 2 ↥A :=
  (lamHat A hK).comp (projPhi hV A)

theorem lamPhi_sigPhi (hK : KTwo V A) (a : ↥A) :
    lamPhi hV A hK (sigPhi hV A a) = (a : ↥A ⧸ pCore 2 ↥A) :=
  lamHat_rhoA A hK a

theorem lamPhi_surjective (hK : KTwo V A) : Function.Surjective (lamPhi hV A hK) :=
  (lamHat_surjective A hK).comp (projPhi_surjective hV A)

theorem ker_lamPhi (hK : KTwo V A) : (lamPhi hV A hK).ker = pCore 2 ↥(yuHolOf hV (autOn A V)) := by
  rw [pCore_phi hV A hK]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := rhoA_surjective V A (projPhi hV A x)
    have h1 : lamHat A hK (rhoA V A a) = 1 := by rw [ha]; exact h
    rw [lamHat_rhoA A hK a, QuotientGroup.eq_one_iff] at h1
    exact ⟨a, h1, ha⟩
  · rintro ⟨q, hq, hqx⟩
    show lamHat A hK (projPhi hV A x) = 1
    rw [← hqx, lamHat_rhoA A hK q, QuotientGroup.eq_one_iff]
    exact hq

@[expose] noncomputable def ePhi (hK : KTwo V A) :
    (↥(yuHolOf hV (autOn A V)) ⧸ pCore 2 ↥(yuHolOf hV (autOn A V))) ≃*
      (↥A ⧸ pCore 2 ↥A) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_lamPhi hV A hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (lamPhi_surjective hV A hK))

theorem ePhi_mk (hK : KTwo V A) (x : ↥(yuHolOf hV (autOn A V))) :
    ePhi hV A hK (x : ↥(yuHolOf hV (autOn A V)) ⧸ pCore 2 ↥(yuHolOf hV (autOn A V))) =
      lamPhi hV A hK x := rfl

end Phi

end CFSG.CGT.PushingUpLit.CGT6

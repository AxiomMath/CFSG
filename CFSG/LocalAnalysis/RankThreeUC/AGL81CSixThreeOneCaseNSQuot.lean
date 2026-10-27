module

public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneAltFive
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialThirtyTwoFive
import CFSG.RankThree.PartOne.S9.QD32.AutCount
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open scoped commutatorElement

private theorem closure_a_xa_quaternion :
    Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} : Set (QuaternionGroup 2)) =
      ⊤ := by
  rw [eq_top_iff]
  rintro w -
  rcases w with k | k
  · have h : QuaternionGroup.a 1 ^ k.val = (QuaternionGroup.a k : QuaternionGroup 2) := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [← h]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · have h : QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ k.val =
        (QuaternionGroup.xa k : QuaternionGroup 2) := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

private theorem closure_sr_dihedral :
    Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup 4)) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  rcases w with k | k
  · have h : (DihedralGroup.r 1 : DihedralGroup 4) ^ k.val = DihedralGroup.r k := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [← h, show (DihedralGroup.r 1 : DihedralGroup 4) =
      DihedralGroup.sr 0 * DihedralGroup.sr 1 from by decide]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) _
  · have h : DihedralGroup.sr 0 * (DihedralGroup.r 1 : DihedralGroup 4) ^ k.val =
        DihedralGroup.sr k := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, DihedralGroup.sr_mul_r, zero_add]
    rw [← h, show (DihedralGroup.r 1 : DihedralGroup 4) =
      DihedralGroup.sr 0 * DihedralGroup.sr 1 from by decide]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) _)

private theorem eq_of_ne_one_of_card_two {A : Type*} [Group A] (h : Nat.card A = 2) {a b : A}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : A)).mp h
  rw [hc a ha, hc b hb]

private theorem isQ8D8Type_sq_mem_inf {X : Type} [Group X] {Q E : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} (hcardQE : Nat.card ↥(Q ⊓ E) = 2) :
    ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X) * ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X) ∈
      Q ⊓ E := by
  classical
  let xQ : ↥Q := eQ.symm (QuaternionGroup.a 1)
  let wQ : ↥Q := eQ.symm (QuaternionGroup.a 2)
  have hsq : xQ * xQ = wQ := by
    have h : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
        QuaternionGroup.a 2 := by decide
    calc xQ * xQ = eQ.symm (QuaternionGroup.a 1) * eQ.symm (QuaternionGroup.a 1) := rfl
      _ = eQ.symm (QuaternionGroup.a 1 * QuaternionGroup.a 1) := (eQ.symm.map_mul _ _).symm
      _ = eQ.symm (QuaternionGroup.a 2) := by rw [h]
      _ = wQ := rfl
  have hQinv : ∀ w : ↥Q, w * w = 1 → w = 1 ∨ w = wQ := by
    intro w hw
    have hw' : eQ w * eQ w = 1 := by rw [← map_mul, hw, map_one]
    rcases (by decide : ∀ v : QuaternionGroup 2, v * v = 1 → v = 1 ∨
      v = QuaternionGroup.a 2) (eQ w) hw' with h | h
    · left; apply eQ.injective; rw [h, map_one]
    · right; apply eQ.injective; simpa [wQ] using h
  obtain ⟨w, hw1, hwuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Q ⊓ E))).mp hcardQE
  have hw2 : w * w = 1 := by
    by_contra hne
    have h : w * w = w := hwuniq (w * w) hne
    have h1 : w = 1 := by
      have h2 := congrArg (fun z : ↥(Q ⊓ E) => z * w⁻¹) h
      simpa [mul_assoc] using h2
    exact hw1 h1
  have hw_ne : (w : X) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwQ : (⟨(w : X), (Subgroup.mem_inf.mp w.2).1⟩ : ↥Q) = wQ := by
    have hw2' : (⟨(w : X), (Subgroup.mem_inf.mp w.2).1⟩ : ↥Q) *
        ⟨(w : X), (Subgroup.mem_inf.mp w.2).1⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact congrArg Subtype.val hw2
    rcases hQinv _ hw2' with h | h
    · exact absurd (Subtype.ext_iff.mp h) hw_ne
    · exact h
  show (xQ : X) * xQ ∈ Q ⊓ E
  have hxe : (xQ : X) * xQ = (w : X) := by
    rw [show (xQ : X) * xQ = ((xQ * xQ : ↥Q) : X) from (Subgroup.coe_mul Q xQ xQ).symm, hsq]
    exact (congrArg Subtype.val hwQ).symm
  rw [hxe]
  exact w.2

private theorem isQ8D8Type_sq_ne_one {X : Type} [Group X] {Q : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} {x : ↥Q} (hx : eQ x = QuaternionGroup.a 1) :
    (x : X) * (x : X) ≠ 1 := by
  intro h
  have hx1 : x * x = 1 := Subtype.ext h
  have h1 : eQ x * eQ x = 1 := by rw [← map_mul, hx1, map_one]
  rw [hx, show QuaternionGroup.a 1 * QuaternionGroup.a 1 = QuaternionGroup.a 2 from by decide]
    at h1
  exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) h1

private theorem isQ8D8Type_sq_sq {X : Type} [Group X] {Q : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} {x : ↥Q} (hx : eQ x = QuaternionGroup.a 1) :
    ((x : X) * (x : X)) * ((x : X) * (x : X)) = 1 := by
  have h : (x * x) * (x * x) = 1 := by
    apply eQ.injective
    rw [map_mul, map_mul, map_one, hx,
      show (QuaternionGroup.a 1 * QuaternionGroup.a 1) *
        (QuaternionGroup.a 1 * QuaternionGroup.a 1) = 1 from by decide]
  exact congrArg Subtype.val h

private theorem isQ8D8Type_sq_center_E {X : Type} [Group X] {Q E : Subgroup X}
    {x : ↥Q} (hcomm : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q)
    (hzE : (x : X) * (x : X) ∈ E) :
    (⟨(x : X) * (x : X), hzE⟩ : ↥E) ∈ Subgroup.center ↥E := by
  rw [Subgroup.mem_center_iff]
  intro e
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (hcomm ((x : X) * (x : X)) (Q.mul_mem x.2 x.2) (e : X) e.2).symm

private theorem isQ8D8Type_center_E_card {X : Type} [Group X] {E : Subgroup X}
    (eE : ↥E ≃* DihedralGroup 4) : Nat.card ↥(Subgroup.center ↥E) = 2 := by
  have hr2ord : orderOf (DihedralGroup.r 2) = 2 :=
    orderOf_eq_prime (by rw [pow_two, show (DihedralGroup.r 2 : DihedralGroup 4) *
      DihedralGroup.r 2 = 1 from by decide]) (by decide)
  have h : Subgroup.center (DihedralGroup 4) = Subgroup.zpowers (DihedralGroup.r 2) := by
    ext w
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.mem_zpowers_of_orderOf_eq_two hr2ord]
    exact (by decide : ∀ w : DihedralGroup 4, w ∈ Subgroup.center (DihedralGroup 4) ↔
      w = 1 ∨ w = DihedralGroup.r 2) w
  rw [Nat.card_congr (Subgroup.centerCongr eE).toEquiv, h, Nat.card_zpowers, hr2ord]

private theorem isQ8D8Type_commutator_uv {X : Type} [Group X] {Q E : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} {eE : ↥E ≃* DihedralGroup 4}
    (hcomm : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) {x : ↥Q} {u v : ↥E}
    (hx : eQ x = QuaternionGroup.a 1) (hu : eE u = DihedralGroup.sr 0)
    (hv : eE v = DihedralGroup.sr 1) (hzE : (x : X) * (x : X) ∈ E) :
    ⁅(u : X), (v : X)⁆ = (x : X) * (x : X) := by
  classical
  have hz_centerE : (⟨(x : X) * (x : X), hzE⟩ : ↥E) ∈ Subgroup.center ↥E :=
    isQ8D8Type_sq_center_E (X := X) (Q := Q) (E := E) hcomm hzE
  have huv_mem : ⁅(u : X), (v : X)⁆ ∈ E := by
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem u.2 v.2) (E.inv_mem u.2)) (E.inv_mem v.2)
  have huv_map : eE ⟨⁅(u : X), (v : X)⁆, huv_mem⟩ = DihedralGroup.r 2 := by
    have hcoe : (⟨⁅(u : X), (v : X)⁆, huv_mem⟩ : ↥E) = ⁅u, v⁆ := by
      apply Subtype.ext
      rfl
    rw [hcoe]
    have hmap : eE (⁅u, v⁆ : ↥E) = ⁅eE u, eE v⁆ := map_commutatorElement eE u v
    rw [hmap, show eE u = (DihedralGroup.sr 0 : DihedralGroup 4) from hu,
      show eE v = (DihedralGroup.sr 1 : DihedralGroup 4) from hv]
    exact (by decide : ⁅(DihedralGroup.sr 0 : DihedralGroup 4),
      (DihedralGroup.sr 1 : DihedralGroup 4)⁆ = (DihedralGroup.r 2 : DihedralGroup 4))
  have huv_centerE : (⟨⁅(u : X), (v : X)⁆, huv_mem⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro e
    apply eE.injective
    rw [map_mul, map_mul, huv_map]
    exact (by decide : ∀ z : DihedralGroup 4,
      z * DihedralGroup.r 2 = DihedralGroup.r 2 * z) (eE e)
  have huv_ne : ⁅(u : X), (v : X)⁆ ≠ 1 := by
    intro h
    have h1 : (⟨⁅(u : X), (v : X)⁆, huv_mem⟩ : ↥E) = 1 := Subtype.ext h
    rw [h1, map_one] at huv_map
    exact (by decide : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1) huv_map.symm
  have huv_eq : (⟨(x : X) * (x : X), hzE⟩ : ↥E) =
      (⟨⁅(u : X), (v : X)⁆, huv_mem⟩ : ↥E) := by
    exact congrArg Subtype.val
      (eq_of_ne_one_of_card_two (A := ↥(Subgroup.center ↥E))
        (isQ8D8Type_center_E_card (X := X) (E := E) eE)
        (a := ⟨⟨(x : X) * (x : X), hzE⟩, hz_centerE⟩)
        (b := ⟨⟨⁅(u : X), (v : X)⁆, huv_mem⟩, huv_centerE⟩)
        (fun hh => isQ8D8Type_sq_ne_one (X := X) (Q := Q) (eQ := eQ) hx
          (congrArg Subtype.val (congrArg Subtype.val hh)))
        (fun hh => huv_ne (congrArg Subtype.val (congrArg Subtype.val hh))))
  exact (congrArg Subtype.val huv_eq).symm

private theorem isQ8D8Type_sq_center {X : Type} [Group X] {Q E : Subgroup X} {x : ↥Q}
    (hcomm : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) (hsup : Q ⊔ E = ⊤)
    (hzE : (x : X) * (x : X) ∈ E) : ((x : X) * (x : X)) ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hQc : Q ≤ Subgroup.centralizer ({(x : X) * (x : X)} : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm q hq ((x : X) * (x : X)) hzE
  have hEc : E ≤ Subgroup.centralizer ({(x : X) * (x : X)} : Set X) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm ((x : X) * (x : X)) (Q.mul_mem x.2 x.2) e he).symm
  have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({(x : X) * (x : X)} : Set X) := by
    rw [← hsup]
    exact sup_le hQc hEc
  have hg := htop (Subgroup.mem_top g)
  rwa [Subgroup.mem_centralizer_singleton_iff] at hg

private theorem isQ8D8Type_relations {X : Type} [Group X] {Q E : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} {eE : ↥E ≃* DihedralGroup 4}
    (hcomm : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q) (hsup : Q ⊔ E = ⊤)
    (hcardQE : Nat.card ↥(Q ⊓ E) = 2) {x y : ↥Q} {u v : ↥E}
    (hx : eQ x = QuaternionGroup.a 1) (hy : eQ y = QuaternionGroup.xa 0)
    (hu : eE u = DihedralGroup.sr 0) (hv : eE v = DihedralGroup.sr 1)
    (hzE : (x : X) * (x : X) ∈ E) :
    ((x : X) * (x : X)) ∈ Subgroup.center X ∧
      ((x : X) * (x : X)) * ((x : X) * (x : X)) = 1 ∧
      (y : X) * (y : X) = (x : X) * (x : X) ∧ (u : X) * (u : X) = 1 ∧
      (v : X) * (v : X) = 1 ∧ ⁅(x : X), (y : X)⁆ = (x : X) * (x : X) ∧
      ⁅(u : X), (v : X)⁆ = (x : X) * (x : X) ∧ ⁅(x : X), (u : X)⁆ = 1 ∧
      ⁅(x : X), (v : X)⁆ = 1 ∧ ⁅(y : X), (u : X)⁆ = 1 ∧ ⁅(y : X), (v : X)⁆ = 1 := by
  classical
  have hsq : (y : X) * (y : X) = (x : X) * (x : X) := by
    have h : y * y = x * x := by
      apply eQ.injective
      rw [map_mul, map_mul, hx, hy,
        show QuaternionGroup.a 1 * QuaternionGroup.a 1 =
          QuaternionGroup.xa 0 * QuaternionGroup.xa 0 from by decide]
    exact congrArg Subtype.val h
  have hcom : ⁅(x : X), (y : X)⁆ = (x : X) * (x : X) := by
    have h : ⁅x, y⁆ = x * x := by
      apply eQ.injective
      rw [map_commutatorElement, map_mul, hx, hy]
      exact (by decide : ⁅(QuaternionGroup.a 1 : QuaternionGroup 2),
        (QuaternionGroup.xa 0 : QuaternionGroup 2)⁆ =
          QuaternionGroup.a 1 * QuaternionGroup.a 1)
    have hcoe : ⁅(x : X), (y : X)⁆ = ((⁅x, y⁆ : ↥Q) : X) := by
      rw [commutatorElement_def, commutatorElement_def]
      rfl
    rw [hcoe, h, Subgroup.coe_mul]
  have hzu : (u : X) * (u : X) = 1 := by
    have h : u * u = 1 := by
      apply eE.injective
      rw [map_mul, map_one, hu,
        show DihedralGroup.sr 0 * DihedralGroup.sr 0 = 1 from by decide]
    exact congrArg Subtype.val h
  have hzv : (v : X) * (v : X) = 1 := by
    have h : v * v = 1 := by
      apply eE.injective
      rw [map_mul, map_one, hv,
        show DihedralGroup.sr 1 * DihedralGroup.sr 1 = 1 from by decide]
    exact congrArg Subtype.val h
  refine ⟨isQ8D8Type_sq_center (X := X) (Q := Q) (E := E) hcomm hsup hzE,
    isQ8D8Type_sq_sq (X := X) (Q := Q) (eQ := eQ) hx, hsq, hzu, hzv, hcom,
    isQ8D8Type_commutator_uv (X := X) (Q := Q) (E := E) hcomm hx hu hv hzE, ?_, ?_, ?_, ?_⟩
  · exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x x.2 u u.2)
  · exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x x.2 v v.2)
  · exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm y y.2 u u.2)
  · exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm y y.2 v v.2)

private theorem isQ8D8Type_closure {X : Type} [Group X] {Q E : Subgroup X}
    {eQ : ↥Q ≃* QuaternionGroup 2} {eE : ↥E ≃* DihedralGroup 4} (hsup : Q ⊔ E = ⊤)
    {x y : ↥Q} {u v : ↥E} (hx : eQ x = QuaternionGroup.a 1)
    (hy : eQ y = QuaternionGroup.xa 0) (hu : eE u = DihedralGroup.sr 0)
    (hv : eE v = DihedralGroup.sr 1) :
    Subgroup.closure ({(x : X), (y : X), (u : X), (v : X)} : Set X) = ⊤ := by
  classical
  set K : Subgroup X := Subgroup.closure ({(x : X), (y : X), (u : X), (v : X)} : Set X)
    with hK
  have hxK : (x : X) ∈ K := Subgroup.subset_closure (by simp)
  have hyK : (y : X) ∈ K := Subgroup.subset_closure (by simp)
  have huK : (u : X) ∈ K := Subgroup.subset_closure (by simp)
  have hvK : (v : X) ∈ K := Subgroup.subset_closure (by simp)
  have hKQ : Q ≤ K := by
    have hsub : K.subgroupOf Q = ⊤ := by
      apply Subgroup.map_injective (f := eQ.toMonoidHom) eQ.injective
      rw [Subgroup.map_top_of_surjective _ eQ.surjective, eq_top_iff, ← closure_a_xa_quaternion]
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact ⟨x, Subgroup.mem_subgroupOf.mpr hxK, hx⟩
      · exact ⟨y, Subgroup.mem_subgroupOf.mpr hyK, hy⟩
    intro q hq
    exact Subgroup.mem_subgroupOf.mp (hsub ▸ Subgroup.mem_top (⟨q, hq⟩ : ↥Q))
  have hKE : E ≤ K := by
    have hsub : K.subgroupOf E = ⊤ := by
      apply Subgroup.map_injective (f := eE.toMonoidHom) eE.injective
      rw [Subgroup.map_top_of_surjective _ eE.surjective, eq_top_iff, ← closure_sr_dihedral]
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact ⟨u, Subgroup.mem_subgroupOf.mpr huK, hu⟩
      · exact ⟨v, Subgroup.mem_subgroupOf.mpr hvK, hv⟩
    intro e he
    exact Subgroup.mem_subgroupOf.mp (hsub ▸ Subgroup.mem_top (⟨e, he⟩ : ↥E))
  exact top_unique (by rw [← hsup]; exact sup_le hKQ hKE)

theorem nonempty_mulEquiv_QD32_of_isQ8D8Type {X : Type} [Group X] (hX : IsQ8D8Type X)
    (hcard : Nat.card X = 32) : Nonempty (X ≃* CFSG.RankThree.GroupTheory.QD32) := by
  classical
  obtain ⟨Q, E, ⟨eQ⟩, ⟨eE⟩, hcomm, hsup, hcardQE⟩ := hX
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hzE : ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X) *
      ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X) ∈ E :=
    (Subgroup.mem_inf.mp (isQ8D8Type_sq_mem_inf (eQ := eQ) hcardQE)).2
  have hrel := isQ8D8Type_relations (eQ := eQ) (eE := eE) hcomm hsup hcardQE
    (x := eQ.symm (QuaternionGroup.a 1)) (y := eQ.symm (QuaternionGroup.xa 0))
    (u := eE.symm (DihedralGroup.sr 0)) (v := eE.symm (DihedralGroup.sr 1))
    (eQ.apply_symm_apply _) (eQ.apply_symm_apply _) (eE.apply_symm_apply _)
    (eE.apply_symm_apply _) hzE
  obtain ⟨hzc, hzz, hy2, hu2, hv2, hxy, huv, hxu, hxv, hyu, hyv⟩ := hrel
  have hgen := isQ8D8Type_closure (eQ := eQ) (eE := eE) hsup
    (x := eQ.symm (QuaternionGroup.a 1)) (y := eQ.symm (QuaternionGroup.xa 0))
    (u := eE.symm (DihedralGroup.sr 0)) (v := eE.symm (DihedralGroup.sr 1))
    (eQ.apply_symm_apply _) (eQ.apply_symm_apply _) (eE.apply_symm_apply _)
    (eE.apply_symm_apply _)
  obtain ⟨e, -, -, -, -⟩ := CFSG.RankThree.GroupTheory.SteinbergBM.exists_qd32_mulEquiv
    hcard (x := ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X))
    (y := ((eQ.symm (QuaternionGroup.xa 0) : ↥Q) : X))
    (u := ((eE.symm (DihedralGroup.sr 0) : ↥E) : X))
    (v := ((eE.symm (DihedralGroup.sr 1) : ↥E) : X))
    (z := ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X) *
      ((eQ.symm (QuaternionGroup.a 1) : ↥Q) : X))
    hzc hzz rfl hy2 hu2 hv2 hxy huv hxu hxv hyu hyv hgen
  exact ⟨e.symm⟩

private theorem card_ker_conjNormal_le_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))}
    (hC : ∀ g : ↥G, (∀ q ∈ CFSG.pCore 2 ↥G, g * q = q * g) →
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 ∨ (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1) :
    Nat.card ↥(MulAut.conjNormal (G := ↥G) (H := CFSG.pCore 2 ↥G)).ker ≤ 2 := by
  classical
  let φ : ↥G →* MulAut ↥(CFSG.pCore 2 ↥G) := MulAut.conjNormal
  haveI : Finite ↥G := inferInstance
  have hcomm_ker : ∀ u : ↥φ.ker, ∀ q ∈ CFSG.pCore 2 ↥G, (u : ↥G) * q = q * (u : ↥G) := by
    intro u q hq
    have h1 : (φ (u : ↥G)) ⟨q, hq⟩ = ⟨q, hq⟩ := by
      rw [show φ (u : ↥G) = 1 from MonoidHom.mem_ker.mp u.2]
      exact MulAut.one_apply _ _
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc (u : ↥G) * q = ((u : ↥G) * q * (u : ↥G)⁻¹) * (u : ↥G) := by group
      _ = q * (u : ↥G) := by rw [h2]
  have hinj : Function.Injective (fun u : ↥φ.ker =>
      if ((u : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 then (0 : Fin 2) else 1) := by
    intro a b hab
    change (if ((a : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 then (0 : Fin 2) else 1) =
      (if ((b : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 then (0 : Fin 2) else 1) at hab
    have ha := hC (a : ↥G) (hcomm_ker a)
    have hb := hC (b : ↥G) (hcomm_ker b)
    apply Subtype.ext
    by_cases h1 : ((a : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1
    · have hb1 : ((b : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 := by
        by_contra hb2
        rw [if_pos h1, if_neg hb2] at hab
        exact absurd hab (by decide)
      exact Subtype.val_injective (h1.trans hb1.symm)
    · have ha1 : ((a : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 := ha.resolve_left h1
      by_cases hb1 : ((b : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1
      · rw [if_pos hb1, if_neg h1] at hab
        exact absurd hab (by decide)
      · have hb2 : ((b : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 := hb.resolve_left hb1
        exact Subtype.val_injective (ha1.trans hb2.symm)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

private theorem dvd_card_of_pCore_two_isQ8D8Type [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod 5))
    (hQ : IsQ8D8Type ↥(CFSG.pCore 2 ↥G)) (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 32)
    (hC : ∀ g : ↥G, (∀ q ∈ CFSG.pCore 2 ↥G, g * q = q * g) →
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 ∨ (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1) :
    Nat.card ↥G ∣ 2 ^ 7 * 3 * 5 := by
  classical
  haveI : Finite ↥G := inferInstance
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQcard : Nat.card ↥Q = 32 := hcard
  have hQis : IsQ8D8Type ↥Q := hQ
  have hdvd_sp : Nat.card ↥G ∣ 2 ^ 7 * 3 ^ 2 * 5 ^ 4 * 13 := by
    have h := Subgroup.card_dvd_of_le hGS
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, Nat.card_zmod] at h
    have h' : 5 ^ 4 * ((5 ^ 2 - 1) * (5 ^ 4 - 1)) = 2 ^ 7 * 3 ^ 2 * 5 ^ 4 * 13 := by
      norm_num
    rwa [h'] at h
  let φ : ↥G →* MulAut ↥Q := MulAut.conjNormal
  have hker_le : Nat.card ↥φ.ker ≤ 2 := card_ker_conjNormal_le_two hC
  have hdvd_ker : Nat.card ↥φ.ker ∣ 2 := by
    have hpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    rcases (by omega : Nat.card ↥φ.ker = 1 ∨ Nat.card ↥φ.ker = 2) with h | h <;>
      rw [h] <;> norm_num
  have hdvd_range : Nat.card ↥φ.range ∣ 2 ^ 7 * 3 * 5 := by
    have h1 : Nat.card ↥φ.range ∣ Nat.card (MulAut ↥Q) := Subgroup.card_subgroup_dvd_card _
    obtain ⟨e⟩ := nonempty_mulEquiv_QD32_of_isQ8D8Type hQis hQcard
    refine h1.trans ?_
    rw [show Nat.card (MulAut ↥Q) =
      Nat.card (MulAut CFSG.RankThree.GroupTheory.QD32) from
      Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.RankThree.PartOne.QD32Facts.card_mulAut_QD32_dvd
  have hcardG : Nat.card ↥G = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hdvd1 : Nat.card ↥G ∣ 2 ^ 8 * 3 * 5 := by
    rw [hcardG]
    calc Nat.card ↥φ.range * Nat.card ↥φ.ker ∣ (2 ^ 7 * 3 * 5) * 2 :=
          Nat.mul_dvd_mul hdvd_range hdvd_ker
      _ = 2 ^ 8 * 3 * 5 := by norm_num
  have h := Nat.dvd_gcd hdvd1 hdvd_sp
  rwa [show Nat.gcd (2 ^ 8 * 3 * 5) (2 ^ 7 * 3 ^ 2 * 5 ^ 4 * 13) =
    2 ^ 7 * 3 * 5 from by norm_num] at h

private theorem dvd_card_quot_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))}
    (hdvdG : Nat.card ↥G ∣ 2 ^ 7 * 3 * 5)
    (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 32) :
    Nat.card (↥G ⧸ CFSG.pCore 2 ↥G) ∣ 60 := by
  classical
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQcard : Nat.card ↥Q = 32 := hcard
  obtain ⟨c, hc⟩ := hdvdG
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
  have h' : Nat.card ↥G = Nat.card (↥G ⧸ Q) * 32 := by rw [h, hQcard]
  rw [h'] at hc
  refine ⟨c, ?_⟩
  have h2 : (Nat.card (↥G ⧸ Q) * c) * 32 = 60 * 32 := by
    calc (Nat.card (↥G ⧸ Q) * c) * 32 = (Nat.card (↥G ⧸ Q) * 32) * c := by ring
      _ = 1920 := hc.symm
      _ = 60 * 32 := by norm_num
  exact (Nat.mul_right_cancel (by norm_num : (0:ℕ) < 32) h2).symm

private theorem closure_orderOf_five_quot_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hdvd_quot : Nat.card (↥G ⧸ CFSG.pCore 2 ↥G) ∣ 60) :
    Subgroup.closure {y : ↥G ⧸ CFSG.pCore 2 ↥G | orderOf y = 5} = ⊤ := by
  classical
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hgenG : Subgroup.closure {x : ↥G | ∃ k : ℕ, orderOf x = 5 ^ k} = ⊤ := by
    have h := oPPrimeHull_top_of_eq (p := 5) (G := GL (Fin 2 ⊕ Fin 2) (ZMod 5))
      (H := G) hG
    simpa [oPPrimeHull] using h
  let f : ↥G →* (↥G ⧸ Q) := QuotientGroup.mk' Q
  have himg : Subgroup.closure (f '' {x : ↥G | ∃ k : ℕ, orderOf x = 5 ^ k}) = ⊤ := by
    rw [← MonoidHom.map_closure, hgenG]
    exact Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q)
  rw [eq_top_iff, ← himg]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨x, ⟨k, hk⟩, rfl⟩
  have h5 : orderOf (f x) ∣ 5 ^ k := by
    have h := orderOf_map_dvd f x
    rwa [hk] at h
  have h60 : orderOf (f x) ∣ 60 := (orderOf_dvd_natCard (f x)).trans hdvd_quot
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp h5
  have hj : j ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ j := by omega
    have h25 : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 h2
    have h26 : 5 ^ 2 ∣ orderOf (f x) := by rwa [hjeq]
    have : 5 ^ 2 ∣ 60 := h26.trans h60
    norm_num at this
  rcases (by omega : j = 0 ∨ j = 1) with h | h
  · have h1 : f x = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hjeq, h]
      norm_num
    rw [h1]
    exact (Subgroup.closure {y : ↥G ⧸ Q | orderOf y = 5}).one_mem
  · have h1 : orderOf (f x) = 5 := by
      rw [hjeq, h]
      norm_num
    exact Subgroup.subset_closure h1

private theorem nontrivial_quot_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))}
    (hG : oPPrimeHull 5 G = G) (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 32) :
    Nontrivial (↥G ⧸ CFSG.pCore 2 ↥G) := by
  classical
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQcard : Nat.card ↥Q = 32 := hcard
  haveI : Finite ↥G := inferInstance
  by_contra h
  haveI : Subsingleton (↥G ⧸ Q) := not_nontrivial_iff_subsingleton.mp h
  have hgenG : Subgroup.closure {x : ↥G | ∃ k : ℕ, orderOf x = 5 ^ k} = ⊤ := by
    have h := oPPrimeHull_top_of_eq (p := 5) (G := GL (Fin 2 ⊕ Fin 2) (ZMod 5))
      (H := G) hG
    simpa [oPPrimeHull] using h
  have hQtop : Q = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hcardG32 : Nat.card ↥G = 32 := by
    rw [← hQcard, hQtop, Subgroup.card_top]
  have hall : ∀ x : ↥G, (∃ k : ℕ, orderOf x = 5 ^ k) → x = 1 := by
    rintro x ⟨k, hk⟩
    have h2dvd : orderOf x ∣ 32 := by
      simpa only [← hcardG32] using orderOf_dvd_natCard x
    have h5dvd : orderOf x ∣ 5 ^ k := by rw [← hk]
    have hcop : Nat.Coprime 32 (5 ^ k) := (by decide : Nat.Coprime 32 5).pow_right k
    have hd : orderOf x ∣ Nat.gcd 32 (5 ^ k) := Nat.dvd_gcd h2dvd h5dvd
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hbot : (⊤ : Subgroup ↥G) = ⊥ := by
    rw [← hgenG, eq_bot_iff]
    intro y hy
    exact (Subgroup.closure_le (⊥ : Subgroup ↥G)).mpr (fun z hz => by
      simpa using hall z hz) hy
  have h1 : Nat.card ↥G = 1 := by
    have h3 : Nat.card ↥(⊤ : Subgroup ↥G) = Nat.card ↥(⊥ : Subgroup ↥G) := by rw [hbot]
    rwa [Subgroup.card_top, Subgroup.card_bot] at h3
  omega

private theorem bijective_quot_of_inf_eq_bot_of_sup_eq_top {H : Type} [Group H]
    {Q K : Subgroup H} [Q.Normal] [K.Normal] (hinf : Q ⊓ K = ⊥) (hsup : Q ⊔ K = ⊤) :
    Function.Bijective ((QuotientGroup.mk' K).comp Q.subtype) := by
  constructor
  · intro a b hab
    have h1 : (a : H)⁻¹ * b ∈ K := QuotientGroup.eq.mp hab
    have h2 : (a : H)⁻¹ * b ∈ Q := Q.mul_mem (Q.inv_mem a.2) b.2
    have h3 : (a : H)⁻¹ * b = 1 := by
      have h4 : (a : H)⁻¹ * b ∈ Q ⊓ K := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hinf] at h4
      simpa using h4
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hg : g ∈ Q ⊔ K := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨q, hq, k, hk, hqk⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Q) (t := K)).mp hg
    refine ⟨⟨q, hq⟩, ?_⟩
    have hkg : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    calc (QuotientGroup.mk' K) q = (QuotientGroup.mk' K) q * (QuotientGroup.mk' K) k := by
          rw [hkg, mul_one]
      _ = (QuotientGroup.mk' K) (q * k) := (map_mul _ _ _).symm
      _ = (QuotientGroup.mk' K) g := by rw [hqk]

private theorem not_exists_normal_complement_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 32) :
    ¬ ∃ K : Subgroup ↥G, K.Normal ∧ CFSG.pCore 2 ↥G ⊓ K = ⊥ ∧
      CFSG.pCore 2 ↥G ⊔ K = ⊤ := by
  classical
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQcard : Nat.card ↥Q = 32 := hcard
  haveI : Finite ↥G := inferInstance
  have hgenG : Subgroup.closure {x : ↥G | ∃ k : ℕ, orderOf x = 5 ^ k} = ⊤ := by
    have h := oPPrimeHull_top_of_eq (p := 5) (G := GL (Fin 2 ⊕ Fin 2) (ZMod 5))
      (H := G) hG
    simpa [oPPrimeHull] using h
  rintro ⟨K, hKn, hinf, hsupK⟩
  haveI : Q.Normal := CFSG.pCore_normal
  haveI : K.Normal := hKn
  let fK : ↥Q →* (↥G ⧸ K) := (QuotientGroup.mk' K).comp Q.subtype
  have hfbij : Function.Bijective fK :=
    bijective_quot_of_inf_eq_bot_of_sup_eq_top hinf hsupK
  have hcardK : Nat.card (↥G ⧸ K) = 32 := by
    rw [← hQcard]
    exact (Nat.card_congr (MulEquiv.ofBijective fK hfbij).toEquiv).symm
  have hmemK : ∀ x : ↥G, (∃ k : ℕ, orderOf x = 5 ^ k) → x ∈ K := by
    rintro x ⟨k, hk⟩
    have h5 : orderOf ((QuotientGroup.mk' K) x) ∣ 5 ^ k := by
      have h := orderOf_map_dvd (QuotientGroup.mk' K) x
      rwa [hk] at h
    have h2dvd : orderOf ((QuotientGroup.mk' K) x) ∣ 32 := by
      rw [← hcardK]; exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 32 (5 ^ k) := (by decide : Nat.Coprime 32 5).pow_right k
    have hd : orderOf ((QuotientGroup.mk' K) x) ∣ Nat.gcd 32 (5 ^ k) :=
      Nat.dvd_gcd h2dvd h5
    rw [hcop.gcd_eq_one] at hd
    have h1 : (QuotientGroup.mk' K) x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subgroup.closure {y : ↥G | ∃ k : ℕ, orderOf y = 5 ^ k} := by
      rw [hgenG]; exact Subgroup.mem_top x
    exact (Subgroup.closure_le _).mpr (fun y hy => hmemK y hy) hx
  have hQbot : Q = ⊥ := by
    rw [← hinf, hKtop, inf_top_eq]
  have h1 : Nat.card ↥Q = 1 := by rw [hQbot, Subgroup.card_bot]
  omega

theorem isExtNotation_of_pCore_two_isQ8D8Type {p : ℕ} [Fact p.Prime] (hp : p = 5)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : oPPrimeHull p G = G) (hQ : IsQ8D8Type ↥(CFSG.pCore 2 ↥G))
    (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 32)
    (hC : ∀ g : ↥G, (∀ q ∈ CFSG.pCore 2 ↥G, g * q = q * g) →
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod p)) = 1 ∨ (g : GL (Fin 2 ⊕ Fin 2) (ZMod p)) = -1) :
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
        (fun B _ => IsQ8D8Type B) ↥G ∨
      IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) ↥G := by
  subst hp
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQcard : Nat.card ↥Q = 32 := hcard
  have hQis : IsQ8D8Type ↥Q := hQ
  have hQnormal : Q.Normal := CFSG.pCore_normal
  haveI : Finite ↥G := inferInstance
  have hdvdG : Nat.card ↥G ∣ 2 ^ 7 * 3 * 5 :=
    dvd_card_of_pCore_two_isQ8D8Type hGS hQ hcard hC
  have hdvd_quot : Nat.card (↥G ⧸ Q) ∣ 60 := dvd_card_quot_pCore_two hdvdG hcard
  have hgenQuot : Subgroup.closure {y : ↥G ⧸ Q | orderOf y = 5} = ⊤ :=
    closure_orderOf_five_quot_pCore_two hG hdvd_quot
  have hntriv : Nontrivial (↥G ⧸ Q) := nontrivial_quot_pCore_two hG hcard
  have hcompl : ¬ ∃ K : Subgroup ↥G, K.Normal ∧ Q ⊓ K = ⊥ ∧ Q ⊔ K = ⊤ :=
    not_exists_normal_complement_pCore_two hG hcard
  haveI := hntriv
  rcases alt_five_or_card_five hdvd_quot hgenQuot with h | h
  · exact Or.inl ⟨Q, hQnormal, hQis, h, hcompl⟩
  · exact Or.inr ⟨Q, hQnormal, hQis, h, hcompl⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

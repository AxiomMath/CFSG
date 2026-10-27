module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1211Cyc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input312

open scoped commutatorElement

section Abstract

variable {P : Type*} [Group P]

local instance centerCommGroup : CommGroup (Subgroup.center P) :=
  { (inferInstance : Group (Subgroup.center P)) with mul_comm := fun a b => mul_comm' a b }

theorem commutatorElement_mul_right_of_comm {G : Type*} [Group G] {q x y : G}
    (h : x * ⁅q, y⁆ = ⁅q, y⁆ * x) : ⁅q, x * y⁆ = ⁅q, x⁆ * ⁅q, y⁆ := by
  calc ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅q, x⁆ * ⁅q, y⁆ := by rw [h, mul_inv_cancel_right]

theorem commutatorElement_mul_left_of_comm {G : Type*} [Group G] {q q' x : G}
    (h : q * ⁅q', x⁆ = ⁅q', x⁆ * q) (h' : ⁅q, x⁆ * ⁅q', x⁆ = ⁅q', x⁆ * ⁅q, x⁆) :
    ⁅q * q', x⁆ = ⁅q, x⁆ * ⁅q', x⁆ := by
  calc ⁅q * q', x⁆ = (q * ⁅q', x⁆ * q⁻¹) * ⁅q, x⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅q', x⁆ * ⁅q, x⁆ := by rw [h, mul_inv_cancel_right]
    _ = ⁅q, x⁆ * ⁅q', x⁆ := h'.symm

def commHom (hc : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) (q : P) :
    P →* Subgroup.center P where
  toFun x := ⟨⁅q, x⁆, hc q x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext
    (commutatorElement_mul_right_of_comm ((Subgroup.mem_center_iff.1 (hc q y)) x))

def commHomHom (hc : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) :
    P →* (P →* Subgroup.center P) :=
  MonoidHom.mk' (commHom hc) fun q q' => by
    ext x
    exact commutatorElement_mul_left_of_comm ((Subgroup.mem_center_iff.1 (hc q' x)) q)
      ((Subgroup.mem_center_iff.1 (hc q' x)) ⁅q, x⁆)

theorem ker_commHomHom (hc : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) :
    (commHomHom hc).ker = Subgroup.center P := by
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 : ⁅q, x⁆ = 1 := congrArg Subtype.val (DFunLike.congr_fun h x)
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  · intro h
    ext x
    exact commutatorElement_eq_one_iff_mul_comm.2 (h x).symm

theorem card_range_commHomHom (hc : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P)
    (hP : Nat.card P = 3 ^ 5) (hZ : Nat.card (Subgroup.center P) = 3) :
    Nat.card (commHomHom hc).range = 81 := by
  have h1 := Subgroup.card_mul_index (commHomHom hc).ker
  rw [Subgroup.index_ker, ker_commHomHom, hZ, hP] at h1
  omega

theorem card_hom (hP : Nat.card P = 3 ^ 5) (hexp : ∀ x : P, x ^ 3 = 1)
    (hder : commutator P = Subgroup.center P) (hZ : Nat.card (Subgroup.center P) = 3) :
    Nat.card (P →* Subgroup.center P) = 81 := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hKcyc : IsCyclic (Subgroup.center P) := isCyclic_of_prime_card hZ
  haveI h3 : HasEnoughRootsOfUnity (Subgroup.center P) 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center P)
    have hord : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
    refine ⟨⟨g, ?_⟩, ?_⟩
    · have := IsPrimitiveRoot.orderOf g
      rwa [hord] at this
    · haveI : IsCyclic (Subgroup.center P)ˣ :=
        isCyclic_of_surjective (toUnits : Subgroup.center P ≃* (Subgroup.center P)ˣ)
          toUnits.surjective
      infer_instance
  have hA3 : ∀ a : Abelianization P, a ^ 3 = 1 := by
    intro a
    refine QuotientGroup.induction_on a (fun z => ?_)
    show Abelianization.of z ^ 3 = 1
    rw [← map_pow, hexp, map_one]
  haveI : HasEnoughRootsOfUnity (Subgroup.center P) (Monoid.exponent (Abelianization P)) :=
    HasEnoughRootsOfUnity.of_dvd _ (Monoid.exponent_dvd_of_forall_pow_eq_one hA3)
  have h1 := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Abelianization P)
    (Subgroup.center P)
  have h2 : Nat.card (P →* Subgroup.center P) =
      Nat.card (Abelianization P →* (Subgroup.center P)ˣ) :=
    Nat.card_congr ((MulEquiv.monoidHomCongrRightEquiv toUnits).trans Abelianization.lift)
  have h4 : Nat.card (Abelianization P) = 81 := by
    have h5 : Nat.card (Abelianization P) = (commutator P).index := rfl
    have h6 := Subgroup.card_mul_index (Subgroup.center P)
    rw [h5, hder]
    rw [hZ, hP] at h6
    omega
  rw [h2, h1, h4]

theorem exists_commutator_eq (hP : Nat.card P = 3 ^ 5) (hexp : ∀ x : P, x ^ 3 = 1)
    (hder : commutator P = Subgroup.center P) (hZ : Nat.card (Subgroup.center P) = 3)
    (φ : P → P) (hφc : ∀ x, φ x ∈ Subgroup.center P) (hφm : ∀ x y, φ (x * y) = φ x * φ y) :
    ∃ q : P, ∀ x, φ x = ⁅q, x⁆ := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hc : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P := fun x y => by
    rw [← hder, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hhom : Nat.card (P →* Subgroup.center P) = 81 := card_hom hP hexp hder hZ
  have hrange := card_range_commHomHom hc hP hZ
  haveI : Finite (P →* Subgroup.center P) :=
    Nat.finite_of_card_ne_zero (by rw [hhom]; norm_num)
  have htop : (commHomHom hc).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hrange, hhom])
  let f : P →* Subgroup.center P :=
    MonoidHom.mk' (fun x => ⟨φ x, hφc x⟩) fun x y => Subtype.ext (hφm x y)
  have hf : f ∈ (commHomHom hc).range := by
    rw [htop]
    exact Subgroup.mem_top f
  obtain ⟨q, hq⟩ := hf
  exact ⟨q, fun x => (congrArg Subtype.val (DFunLike.congr_fun hq x)).symm⟩

end Abstract

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211

theorem input31_2_three_holds : Input31_2_three := by
  intro G _ R Q _ _ _ hQ hcomm r hr
  obtain ⟨hcard, hexp, hder, hZ⟩ := hQ
  have hZQ : centerOf Q ≤ Q := Subgroup.map_subtype_le _
  have hcr : ∀ x ∈ Q, ⁅r, x⁆ ∈ centerOf Q := fun x hx =>
    hcomm (Subgroup.commutator_mem_commutator hr hx)
  have hmemQ : ∀ x : ↥Q, ⁅r, (x : G)⁆ ∈ Q := fun x => hZQ (hcr x x.2)
  let φ : ↥Q → ↥Q := fun x => ⟨⁅r, (x : G)⁆, hmemQ x⟩
  have hφc : ∀ x, φ x ∈ Subgroup.center ↥Q := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (((mem_centerOf_iff' Q _).1 (hcr x x.2)).2 g g.2)
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    refine Subtype.ext ?_
    exact commutatorElement_mul_right_of_comm
      (((mem_centerOf_iff' Q _).1 (hcr y y.2)).2 (x : G) x.2)
  have hexp' : ∀ x : ↥Q, x ^ 3 = 1 := fun x => Subtype.ext (hexp x x.2)
  have hder' : commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_subtype_commutator, hder]
    rfl
  have hZ' : Nat.card (Subgroup.center ↥Q) = 3 :=
    (Subgroup.card_map_of_injective (K := Subgroup.center ↥Q) (f := Q.subtype)
      Q.subtype_injective).symm.trans hZ
  obtain ⟨q, hq⟩ := exists_commutator_eq hcard hexp' hder' hZ' φ hφc hφm
  have hq' : ∀ x ∈ Q, ⁅r, x⁆ = ⁅(q : G), x⁆ := fun x hx => congrArg Subtype.val (hq ⟨x, hx⟩)
  have hcent : (q : G)⁻¹ * r ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have e : ⁅r, h⁆ = ⁅(q : G), h⁆ := hq' h hh
    simp only [commutatorElement_def] at e
    have e' : r * h * r⁻¹ = (q : G) * h * (q : G)⁻¹ := mul_right_cancel e
    calc h * ((q : G)⁻¹ * r) = (q : G)⁻¹ * ((q : G) * h * (q : G)⁻¹) * r := by group
      _ = (q : G)⁻¹ * (r * h * r⁻¹) * r := by rw [e']
      _ = (q : G)⁻¹ * r * h := by group
  have hmem : (q : G) * ((q : G)⁻¹ * r) ∈ Q ⊔ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left q.2) (Subgroup.mem_sup_right hcent)
  have hrq : (q : G) * ((q : G)⁻¹ * r) = r := by group
  rwa [hrq] at hmem

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input312

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open Lemma1211

theorem lemma1211_of_inputs''
    (h129 : Lemma129PrintedStatement) (h1210 : Lemma1210Statement)
    (hα : Claim1211_alpha) (hR3 : Claim1211_R3)
    (hm3 : Claim1211_m3) (hTI : Claim1211_TI) (hOM : Claim1211_OM) :
    Lemma1211Statement :=
  lemma1211_of_inputs' Input312.input31_2_three_holds h129 h1210 hα hR3 hm3 hTI hOM

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

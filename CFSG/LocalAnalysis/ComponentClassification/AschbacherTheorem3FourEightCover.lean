module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightLocal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]

theorem card_le_of_conj_mem {P Z : Subgroup X} {s : X}
    (h : ∀ p ∈ P, s⁻¹ * (p * s * p⁻¹) ∈ Z) :
    Nat.card P ≤ Nat.card Z *
      Nat.card (Subgroup.centralizer ({s} : Set X) ⊓ P : Subgroup X) := by
  set K := Subgroup.centralizer ({s} : Set X) with hK
  set C : Subgroup P := K.subgroupOf P with hC
  have hmemK : ∀ c : X, c ∈ K ↔ c * s = s * c := fun c => by
    rw [hK, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  let F : P → Z := fun p => ⟨s⁻¹ * ((p : X) * s * (p : X)⁻¹), h p p.2⟩
  have hF : ∀ a b : P, F a = F b ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [hC, Subgroup.mem_subgroupOf, hmemK]
    simp only [F, Subtype.mk.injEq, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hab
      have h1 : (a : X) * s * (a : X)⁻¹ = (b : X) * s * (b : X)⁻¹ := mul_left_cancel hab
      calc (a : X)⁻¹ * b * s = (a : X)⁻¹ * ((b : X) * s * (b : X)⁻¹) * b := by group
        _ = (a : X)⁻¹ * ((a : X) * s * (a : X)⁻¹) * b := by rw [h1]
        _ = s * ((a : X)⁻¹ * b) := by group
    · intro hab
      congr 1
      calc (a : X) * s * (a : X)⁻¹
          = (a : X) * (((a : X)⁻¹ * b) * s) * ((a : X)⁻¹ * b)⁻¹ * (a : X)⁻¹ := by
            rw [hab]; group
        _ = (b : X) * s * (b : X)⁻¹ := by group
  let f : P ⧸ C → Z := Quotient.lift F (by
    intro a b hab
    exact (hF a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        exact (hF a b).mp hab
  have h1 := Nat.card_le_card_of_injective f hf
  rw [← Subgroup.index_eq_card] at h1
  have h2 := Subgroup.relIndex_mul_card K P
  rw [Subgroup.relIndex] at h2
  rw [← h2]
  exact Nat.mul_le_mul_right _ h1

variable {G T S Q H : Subgroup X} {g y : X}

theorem comm_mem_Z_of_mem_W (e : Elem47 G T S Q H g y) {a b : X}
    (ha : a ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g))
    (hb : b ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
    a⁻¹ * (b⁻¹ * a * b) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  rw [← e.commutator_eq]
  have h := Subgroup.commutator_mem_commutator
    (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ hb)
  simpa [commutatorElement_def, mul_assoc] using h

theorem comm_mem_R (e : Elem47 G T S Q H g y) {x t : X} (hxS : x ∈ S) (hxG : x ∈ G)
    (ht : t ∈ T) :
    x⁻¹ * (t⁻¹ * x * t) ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G := by
  have htW : t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
  refine ⟨?_, ?_⟩
  · have h1 : x⁻¹ * t⁻¹ * x ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
      have := (Subgroup.mem_normalizer_iff.mp (S_le_normalizer_W e (S.inv_mem hxS)) t⁻¹).mp
        (Subgroup.inv_mem _ htW)
      simpa using this
    have h2 := Subgroup.mul_mem _ h1 htW
    simpa [mul_assoc] using h2
  · have htG : t⁻¹ * x * t ∈ G := by
      have := (Subgroup.mem_normalizer_iff.mp
        (e.hyp45.frame.le_normalizer (T.inv_mem ht)) x).mp hxG
      simpa using this
    exact G.mul_mem (G.inv_mem hxG) htG

theorem M_comm' (e : Elem47 G T S Q H g y) {a b : X} (ha : a ∈ T ⊔ rightConjugate T g)
    (hb : b ∈ T ⊔ rightConjugate T g) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (e.M_comm hb) a ha

theorem eq_one_of_comm_mem_Z (e : Elem47 G T S Q H g y) {w s : X} (hwS : w ∈ S)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hs : s ∈ T)
    (hc : w⁻¹ * (s⁻¹ * w * s) ∈ (T ⊔ rightConjugate T g) ⊓ G) : s = 1 := by
  by_contra hs1
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  have hsW : s ∈ W := Subgroup.mem_sup_right (Subgroup.mem_sup_left hs)
  have hsM : s ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left hs
  have hall : ∀ p ∈ S ⊓ G, p⁻¹ * (s⁻¹ * p * s) ∈ Z := by
    rintro p ⟨hpS, hpG⟩
    by_cases hpW : p ∈ W
    · exact comm_mem_Z_of_mem_W e hpW hsW
    ·
      have hr : w⁻¹ * p ∈ W := by
        have h3 := mul_inv_mem_W e (S.inv_mem hpS) (S.inv_mem hwS)
          (fun h => hpW (by simpa using Subgroup.inv_mem _ h))
          (fun h => hwW (by simpa using Subgroup.inv_mem _ h))
        simpa using h3
      set r := w⁻¹ * p with hrdef
      have hpr : p = w * r := by rw [hrdef]; group
      have hcr := comm_mem_Z_of_mem_W e hr hsW
      have hcom : (w⁻¹ * (s⁻¹ * w * s)) * r = r * (w⁻¹ * (s⁻¹ * w * s)) := e.Z_comm hc hr
      have key : p⁻¹ * (s⁻¹ * p * s) = (w⁻¹ * (s⁻¹ * w * s)) * (r⁻¹ * (s⁻¹ * r * s)) := by
        calc p⁻¹ * (s⁻¹ * p * s)
            = r⁻¹ * ((w⁻¹ * (s⁻¹ * w * s)) * r) * (r⁻¹ * (s⁻¹ * r * s)) := by
              rw [hpr]; group
          _ = r⁻¹ * (r * (w⁻¹ * (s⁻¹ * w * s))) * (r⁻¹ * (s⁻¹ * r * s)) := by rw [hcom]
          _ = (w⁻¹ * (s⁻¹ * w * s)) * (r⁻¹ * (s⁻¹ * r * s)) := by group
      rw [key]
      exact Z.mul_mem hc hcr
  have hconj : ∀ p ∈ S ⊓ G, s⁻¹ * (p * s * p⁻¹) ∈ Z := by
    intro p hp
    have h1 := Z.inv_mem (hall p⁻¹ ((S ⊓ G).inv_mem hp))
    convert h1 using 1
    group
  have hle := card_le_of_conj_mem hconj
  have hC : Subgroup.centralizer ({s} : Set X) ⊓ (S ⊓ G) = Z := by
    rw [inf_comm]
    exact inf_centralizer_eq_Z e hs hs1
  rw [hC, card_SG e, e.card_Z] at hle
  have hpos : 0 < Nat.card T := Nat.card_pos
  nlinarith

theorem exists_conj_eq_mul (e : Elem47 G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {r : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    ∃ t ∈ T, ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, t⁻¹ * w * t = w * r * z := by
  set R := (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G with hRdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  have hZR : Z ≤ R := inf_le_inf_right G le_sup_right
  set Z' : Subgroup R := Z.subgroupOf R with hZ'
  let φ : T → R ⧸ Z' := fun t =>
    (QuotientGroup.mk (⟨w⁻¹ * ((t : X)⁻¹ * w * t), comm_mem_R e hwS hwG t.2⟩ : R) : R ⧸ Z')
  have hφ : Function.Injective φ := by
    intro a b hab
    simp only [φ] at hab
    rw [QuotientGroup.eq, hZ', Subgroup.mem_subgroupOf] at hab
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab
    have hconj : (a : X) * ((w⁻¹ * ((a : X)⁻¹ * w * a))⁻¹ * (w⁻¹ * ((b : X)⁻¹ * w * b))) *
        (a : X)⁻¹ ∈ Z := by
      have haM : (a : X) ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left a.2
      have hzM : (w⁻¹ * ((a : X)⁻¹ * w * a))⁻¹ * (w⁻¹ * ((b : X)⁻¹ * w * b)) ∈
          T ⊔ rightConjugate T g := hab.1
      rw [M_comm' e haM hzM]
      simpa [mul_assoc] using hab
    have heq : (a : X) * ((w⁻¹ * ((a : X)⁻¹ * w * a))⁻¹ * (w⁻¹ * ((b : X)⁻¹ * w * b))) *
        (a : X)⁻¹ = w⁻¹ * (((b : X) * (a : X)⁻¹)⁻¹ * w * ((b : X) * (a : X)⁻¹)) := by group
    rw [heq] at hconj
    have h1 := eq_one_of_comm_mem_Z e hwS hwW (T.mul_mem b.2 (T.inv_mem a.2)) hconj
    exact Subtype.ext (by rw [mul_inv_eq_one] at h1; exact h1.symm)
  have hcard : Nat.card T = Nat.card (R ⧸ Z') := by
    rw [← Subgroup.index_eq_card]
    have h1 := Subgroup.relIndex_mul_card Z R
    rw [inf_eq_left.mpr hZR, card_R e, e.card_Z] at h1
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [Subgroup.relIndex] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  have hsurj : Function.Surjective φ := by
    have : Finite (R ⧸ Z') := inferInstance
    exact (Function.Injective.bijective_of_nat_card_le hφ hcard.ge).2
  obtain ⟨t, ht⟩ := hsurj (QuotientGroup.mk (⟨r, hr⟩ : R))
  simp only [φ] at ht
  rw [QuotientGroup.eq, hZ', Subgroup.mem_subgroupOf] at ht
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at ht
  refine ⟨t, t.2, ((w⁻¹ * ((t : X)⁻¹ * w * t))⁻¹ * r)⁻¹, Z.inv_mem ht, ?_⟩
  group

theorem sq_Z (e : Elem47 G T S Q H g y) {z : X} (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) :
    z ^ 2 = 1 :=
  e.sq_M z hz.1

theorem conj_mem_Z (e : Elem47 G T S Q H g y) {x z : X} (hx : x ∈ S)
    (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) : x⁻¹ * z * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (S_le_normalizer_Z e hx)) z).mp hz
  rwa [inv_inv] at this

theorem comm_mul (e : Elem47 G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {r r' : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
    (hr' : r' ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    (r * r')⁻¹ * (w⁻¹ * (r * r') * w) =
      (r⁻¹ * (w⁻¹ * r * w)) * (r'⁻¹ * (w⁻¹ * r' * w)) := by
  have hc := comm_mem_Z_of_mem_G e hwS hwG hwW hr.1 hr.2
  have hcr : (r⁻¹ * (w⁻¹ * r * w)) * r'⁻¹ = r'⁻¹ * (r⁻¹ * (w⁻¹ * r * w)) :=
    e.Z_comm hc (Subgroup.inv_mem _ hr'.1)
  calc (r * r')⁻¹ * (w⁻¹ * (r * r') * w)
      = r'⁻¹ * (r⁻¹ * (w⁻¹ * r * w)) * (w⁻¹ * r' * w) := by group
    _ = (r⁻¹ * (w⁻¹ * r * w)) * r'⁻¹ * (w⁻¹ * r' * w) := by rw [hcr]
    _ = (r⁻¹ * (w⁻¹ * r * w)) * (r'⁻¹ * (w⁻¹ * r' * w)) := by group

omit [Finite X] in
theorem conj_comm_eq {w r : X} (hw2 : w ^ 2 = 1) (hc2 : (r⁻¹ * (w⁻¹ * r * w)) ^ 2 = 1) :
    w⁻¹ * (r⁻¹ * (w⁻¹ * r * w)) * w = r⁻¹ * (w⁻¹ * r * w) := by
  have hw' : w⁻¹ = w := Elem47.inv_eq_of_sq hw2
  have hc' := Elem47.inv_eq_of_sq hc2
  have e1 : w⁻¹ * (r⁻¹ * (w⁻¹ * r * w)) * w = w⁻¹ * r⁻¹ * w⁻¹ * r * (w * w) := by group
  have e2 : w * w = 1 := by rw [← pow_two, hw2]
  have e3 : w⁻¹ * r⁻¹ * w⁻¹ * r = (r⁻¹ * (w⁻¹ * r * w))⁻¹ := by
    have e4 : (r⁻¹ * (w⁻¹ * r * w))⁻¹ = w⁻¹ * r⁻¹ * w * r := by group
    rw [e4, hw']
  rw [e1, e2, mul_one, e3, hc']

theorem sq_mul_comm_eq (e : Elem47 G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1) {r : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, r ^ 2 * (r⁻¹ * (w⁻¹ * r * w)) = z * (w⁻¹ * z * w) := by
  obtain ⟨t, -, z, hz, htw⟩ := exists_conj_eq_mul e hwS hwG hwW hr
  refine ⟨z, hz, ?_⟩
  have hw' : w⁻¹ = w := Elem47.inv_eq_of_sq hw2
  have hc : r⁻¹ * (w⁻¹ * r * w) ∈ (T ⊔ rightConjugate T g) ⊓ G :=
    comm_mem_Z_of_mem_G e hwS hwG hwW hr.1 hr.2
  have hb : w⁻¹ * z * w ∈ (T ⊔ rightConjugate T g) ⊓ G := conj_mem_Z e hwS hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = r⁻¹ * (w⁻¹ * r * w) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = w⁻¹ * z * w := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  rw [← hbdef] at hb ⊢
  have hsq : w * r * z * (w * r * z) = 1 := by
    have h1 : (t⁻¹ * w * t) ^ 2 = t⁻¹ * w ^ 2 * t := by rw [pow_two, pow_two]; group
    rw [hw2, htw] at h1
    rw [← pow_two, h1]
    group
  have hcr : c * r = r * c := e.Z_comm hc hr.1
  have hbr : b * r = r * b := e.Z_comm hb hr.1
  have hzb : z * b = b * z := M_comm' e hz.1 hb.1
  have h2 : r ^ 2 * c * (b * z) = 1 := by
    calc r ^ 2 * c * (b * z) = r * (r * c) * b * z := by rw [pow_two]; simp only [mul_assoc]
      _ = r * (c * r) * b * z := by rw [hcr]
      _ = r * c * (r * b) * z := by simp only [mul_assoc]
      _ = r * c * (b * r) * z := by rw [hbr]
      _ = w⁻¹ * r * z * w * r * z := by rw [hcdef, hbdef]; group
      _ = w * r * z * (w * r * z) := by rw [hw']; group
      _ = 1 := hsq
  have h3 : r ^ 2 * c = (b * z)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc] at h2 ⊢; exact h2)
  rw [h3, mul_inv_rev, Elem47.inv_eq_of_sq (sq_Z e hz), Elem47.inv_eq_of_sq (sq_Z e hb), hzb]

theorem conj_eq_inv_of_centralizes (e : Elem47 G T S Q H g y) {w : X} (hwS : w ∈ S)
    (hwG : w ∈ G) (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwZ : ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, w⁻¹ * z * w = z) {r : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    w⁻¹ * r * w = r⁻¹ := by
  obtain ⟨z, hz, h⟩ := sq_mul_comm_eq e hwS hwG hwW hw2 hr
  rw [hwZ z hz, ← pow_two, sq_Z e hz] at h
  have h1 : r⁻¹ * (w⁻¹ * r * w) = (r ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
  calc w⁻¹ * r * w = r * (r⁻¹ * (w⁻¹ * r * w)) := by group
    _ = r⁻¹ := by rw [h1]; group

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight

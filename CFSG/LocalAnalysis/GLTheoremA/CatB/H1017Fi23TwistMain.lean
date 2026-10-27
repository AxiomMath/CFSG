module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistPair
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistFi22
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TwistHyp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore

section General

variable {G : Type} [Group G]

private theorem map_conj_inv_le {h u : G} {D : Subgroup G}
    (hD : D ≤ Subgroup.centralizer ({h * u * h⁻¹} : Set G)) :
    D.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.centralizer ({u} : Set G) := by
  have := map_conj_le_centralizer_singleton h⁻¹ hD
  rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at this

private theorem card_map_conj (g : G) (D : Subgroup G) :
    Nat.card (D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

private theorem le_centralizer_of_map_inv {u t : G} {D : Subgroup G}
    (h : D.map (MulAut.conj u⁻¹).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G)) :
    D ≤ Subgroup.centralizer ({u * t * u⁻¹} : Set G) := by
  intro x hx
  have h1 : u⁻¹ * x * u * t = t * (u⁻¹ * x * u) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (h ⟨x, hx, rfl⟩)
    simpa [MulAut.conj_apply] using this
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (u * t * u⁻¹) = u * (u⁻¹ * x * u * t) * u⁻¹ := by group
    _ = u * (t * (u⁻¹ * x * u)) * u⁻¹ := by rw [h1]
    _ = u * t * u⁻¹ * x := by group

private theorem isPGroup_of_elem {D : Subgroup G} (hD : IsElemAbelian 3 D) : IsPGroup 3 D :=
  fun g => ⟨1, Subtype.ext (by simpa using hD.2 g g.2)⟩

private theorem le_centralizer_of_hyper [Finite G] {E D : Subgroup G} (hDE : D ≤ E)
    (hE : Nat.card E = 243) (hD : Nat.card D = 81) {a : G} (haE : a ∈ E) (haD : a ∉ D) {z : G}
    (hDz : D ≤ Subgroup.centralizer ({z} : Set G))
    (haz : a ∈ Subgroup.centralizer ({z} : Set G)) : E ≤ Subgroup.centralizer ({z} : Set G) := by
  have hle : D ⊔ Subgroup.zpowers a ≤ E := sup_le hDE ((Subgroup.zpowers_le).2 haE)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : D ≤ D ⊔ Subgroup.zpowers a)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  rw [hD] at hk
  rw [hE, hk] at hm
  have hkm : k * m = 3 := by
    have h1 : 81 * (k * m) = 243 := by rw [← mul_assoc]; exact hm.symm
    omega
  have hk3 : k = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 ⟨m, hkm.symm⟩ with h | h
    · refine absurd ?_ haD
      have heq : D = D ⊔ Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    · exact h
  have heq : D ⊔ Subgroup.zpowers a = E := Subgroup.eq_of_le_of_card_ge hle (by omega)
  rw [← heq]
  exact sup_le hDz ((Subgroup.zpowers_le).2 haz)

end General

private theorem le_factors
    {A : Subgroup J} (hA : IsElemAbelian 3 A) {u : J}
    (h : A ≤ Subgroup.centralizer ({u * (d * d1) * u⁻¹} : Set J)) :
    A ≤ Subgroup.centralizer ({u * d * u⁻¹} : Set J) ∧
      A ≤ Subgroup.centralizer ({u * d1 * u⁻¹} : Set J) := by
  have h2 := le_centralizer_d_d1 (isElemAbelian_map' (MulAut.conj u⁻¹).toMonoidHom hA)
    (map_conj_inv_le h)
  exact ⟨le_centralizer_of_map_inv (h2.trans inf_le_left),
    le_centralizer_of_map_inv (h2.trans inf_le_right)⟩


theorem not_twoB_pair (hB : FactB) {D : Subgroup J} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 81) {v w : J} (hv : IsConj (d * d1) v) (hw : IsConj (d * d1) w)
    (hvw : v ≠ w) (hcomm : v * w = w * v) (hDv : D ≤ Subgroup.centralizer ({v} : Set J))
    (hDw : D ≤ Subgroup.centralizer ({w} : Set J)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQH, hQ, h3, -⟩ := hB
  obtain ⟨h, hh⟩ := isConj_iff.1 hv
  have hh' : h * (d * d1) * h⁻¹ = v := hh
  subst hh'
  have hD1 : IsElemAbelian 3 (D.map (MulAut.conj h⁻¹).toMonoidHom) := isElemAbelian_map' _ hD
  obtain ⟨g, hgH, hg⟩ := exists_conj_into_of_card hQH
    (by rw [hQ, factorization_centralizer_d_d1]; norm_num)
    (le_centralizer_d_d1 hD1 (map_conj_inv_le hDv)) (isPGroup_of_elem hD1)
  set A := (D.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom with hA
  have hAe : IsElemAbelian 3 A := isElemAbelian_map' _ hD1
  have hAc : Nat.card A = 81 := by rw [hA, card_map_conj, card_map_conj, hc]
  have hgd : g * d * g⁻¹ = d := by
    rw [(Subgroup.mem_centralizer_singleton_iff (G := J)).1 (Subgroup.mem_inf.1 hgH).1,
      mul_inv_cancel_right]
  have hgd1 : g * d1 * g⁻¹ = d1 := by
    rw [(Subgroup.mem_centralizer_singleton_iff (G := J)).1 (Subgroup.mem_inf.1 hgH).2,
      mul_inv_cancel_right]
  have hkv : g * h⁻¹ * (h * (d * d1) * h⁻¹) * (g * h⁻¹)⁻¹ = d * d1 := by
    calc g * h⁻¹ * (h * (d * d1) * h⁻¹) * (g * h⁻¹)⁻¹ = g * d * g⁻¹ * (g * d1 * g⁻¹) := by
          group
      _ = d * d1 := by rw [hgd, hgd1]
  have hAw : A ≤ Subgroup.centralizer ({g * (h⁻¹ * w * h⁻¹⁻¹) * g⁻¹} : Set J) :=
    map_conj_le_centralizer_singleton g (map_conj_le_centralizer_singleton h⁻¹ hDw)
  rw [show g * (h⁻¹ * w * h⁻¹⁻¹) * g⁻¹ = g * h⁻¹ * w * (g * h⁻¹)⁻¹ by group] at hAw
  have hw' : IsConj w (g * h⁻¹ * w * (g * h⁻¹)⁻¹) := isConj_iff.2 ⟨g * h⁻¹, rfl⟩
  obtain ⟨u, hu0⟩ := isConj_iff.1 (hw.trans hw')
  have hu : u * (d * d1) * u⁻¹ = g * h⁻¹ * w * (g * h⁻¹)⁻¹ := hu0
  rw [← hu] at hAw
  obtain ⟨hAx, hAy⟩ := le_factors hAe hAw
  obtain ⟨⟨p, hp⟩, hpx⟩ := (isConj_d_iff _).1 (isConj_iff.2 ⟨u, rfl⟩ : IsConj d (u * d * u⁻¹))
  obtain ⟨⟨q, hq⟩, hqy⟩ := (isConj_d_iff _).1
    ((d1_mem_localClass.1 : IsConj d d1).trans (isConj_iff.2 ⟨u, rfl⟩))
  simp only at hpx hqy
  have hxy : u * d * u⁻¹ * (u * d1 * u⁻¹) = u * (d * d1) * u⁻¹ := by group
  have hyx : u * d1 * u⁻¹ * (u * d * u⁻¹) = u * (d * d1) * u⁻¹ := by
    rw [← d1_commute]; group
  have hpq : p ≠ q := by
    rintro rfl
    have e : u * d * u⁻¹ = u * d1 * u⁻¹ := hpx.symm.trans hqy
    exact d1_mem_localClass.2.1 (mul_left_cancel (mul_right_cancel e)).symm
  have hcomm' : u * (d * d1) * u⁻¹ * (d * d1) = d * d1 * (u * (d * d1) * u⁻¹) := by
    rw [hu, ← hkv]
    calc g * h⁻¹ * w * (g * h⁻¹)⁻¹ * (g * h⁻¹ * (h * (d * d1) * h⁻¹) * (g * h⁻¹)⁻¹) =
        g * h⁻¹ * (w * (h * (d * d1) * h⁻¹)) * (g * h⁻¹)⁻¹ := by group
      _ = g * h⁻¹ * ((h * (d * d1) * h⁻¹) * w) * (g * h⁻¹)⁻¹ := by rw [hcomm]
      _ = g * h⁻¹ * (h * (d * d1) * h⁻¹) * (g * h⁻¹)⁻¹ * (g * h⁻¹ * w * (g * h⁻¹)⁻¹) := by
          group
  have key := h3 A hg hAe hAc p hp q hq hpq (by rw [hpx]; exact hAx) (by rw [hqy]; exact hAy)
    (by rw [hpx, hqy, hxy, hyx]) (by rw [hpx, hqy, hxy]; exact hcomm')
  have hwv : g * h⁻¹ * w * (g * h⁻¹)⁻¹ = d * d1 := by
    rw [← hu, ← hxy]
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hpx, ← hqy, conjPt_zero]; rfl
    · rw [← hpx, ← hqy, conjPt_zero, show conjPt 1 = d1 from rfl]
      exact d1_commute
  apply hvw
  have e := hwv.trans hkv.symm
  exact (mul_left_cancel (mul_right_cancel e)).symm

theorem hyper_cent
    (h22 : I1017FiTwoTwoTwist) (hB : FactB) (hC : FactC)
    (E D : Subgroup J) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 5) (hDE : D ≤ E)
    (hDc : Nat.card D = 3 ^ (5 - 1)) (T : Subgroup J) (hT : IsPGroup 2 T)
    (hTD : T ≤ Subgroup.centralizer (D : Set J)) (hET : E ≤ Subgroup.normalizer (T : Set J)) :
    ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  have hEc' : Nat.card E = 243 := by rw [hEc]; norm_num
  have hDc' : Nat.card D = 81 := by rw [hDc]; norm_num
  have hD : IsElemAbelian 3 D := CFSG.Open.IsElemAbelian.mono hE hDE
  have hE4 : 3 ^ 4 ≤ Nat.card E := by rw [hEc']; norm_num
  have of_twoC : ∀ z : J, IsConj t2 z → D ≤ Subgroup.centralizer ({z} : Set J) →
      ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := fun z hz hDz e he t ht =>
    (Subgroup.mem_centralizer_iff (G := J)).1
      (le_centralizer_of_closed hE hDE hET hT (closed_of_twoC hB hC hD hDc' hz hDz)
        ⟨ht, hTD ht⟩) e he
  by_cases hT1 : T = ⊥
  · intro e he t ht
    rw [hT1, Subgroup.mem_bot] at ht
    rw [ht, mul_one, one_mul]
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E, a ∉ D := by
    by_contra hne
    have hED : E ≤ D := fun x hx => by
      by_contra hxD
      exact hne ⟨x, hx, hxD⟩
    have := Subgroup.card_le_of_le hED
    omega
  have hZT : ∀ z ∈ T ⊓ Subgroup.centralizer (T : Set J),
      T ≤ Subgroup.centralizer ({z} : Set J) := fun z hz t ht =>
    (Subgroup.mem_centralizer_singleton_iff (G := J)).2
      ((Subgroup.mem_centralizer_iff (G := J)).1 hz.2 t ht)
  have hZD : ∀ z ∈ T ⊓ Subgroup.centralizer (T : Set J),
      D ≤ Subgroup.centralizer ({z} : Set J) := fun z hz δ hδ =>
    (Subgroup.mem_centralizer_singleton_iff (G := J)).2
      ((Subgroup.mem_centralizer_iff (G := J)).1 (hTD hz.1) δ hδ)
  have hinv : ∀ z : J, orderOf z = 2 → z ^ 2 = 1 ∧ z ≠ 1 := fun z hz =>
    ⟨by rw [← hz]; exact pow_orderOf_eq_one z, fun h1 => by rw [h1, orderOf_one] at hz; omega⟩
  rcases exists_central_involution_split hT hT1 (hE.2 a haE) (hET haE) with
    ⟨z, hzZ, hz2, haz⟩ | ⟨v, hvZ, hv2, hav, hvvv⟩
  · have hEz := le_centralizer_of_hyper hDE hEc' hDc' haE haD (hZD z hzZ)
      ((Subgroup.mem_centralizer_singleton_iff (G := J)).2 haz)
    rcases involution_cover z (hinv z hz2).1 (hinv z hz2).2 with h | h | h
    · exact twoA_transfer h22 hE hE4 hT hET h hEz (hZT z hzZ)
    · exact twoB_transfer h22 hE hE4 hT hET h hEz (hZT z hzZ)
    · exact of_twoC z h (hZD z hzZ)
  have hv'Z := conj_mem_centerInf_of_normalizer (hET haE) hvZ
  have hcomm : v * (a * v * a⁻¹) = a * v * a⁻¹ * v :=
    ((Subgroup.mem_centralizer_iff (G := J)).1 hvZ.2 _ hv'Z.1).symm
  rcases involution_cover v (hinv v hv2).1 (hinv v hv2).2 with h | h | h
  ·
    exfalso
    have hvv : v * v = 1 := by rw [← pow_two]; exact (hinv v hv2).1
    have hv'v' : a * v * a⁻¹ * (a * v * a⁻¹) = 1 := by
      calc a * v * a⁻¹ * (a * v * a⁻¹) = a * (v * v) * a⁻¹ := by group
        _ = 1 := by rw [hvv, mul_one, mul_inv_cancel]
    have hvvv' : v * (a * v * a⁻¹) * (a ^ 2 * v * (a ^ 2)⁻¹) = 1 := hvvv
    have hww : v * (a * v * a⁻¹) * (v * (a * v * a⁻¹)) = 1 := by
      calc v * (a * v * a⁻¹) * (v * (a * v * a⁻¹)) =
          v * (a * v * a⁻¹ * v) * (a * v * a⁻¹) := by group
        _ = v * (v * (a * v * a⁻¹)) * (a * v * a⁻¹) := by rw [← hcomm]
        _ = v * v * (a * v * a⁻¹ * (a * v * a⁻¹)) := by group
        _ = 1 := by rw [hvv, hv'v', one_mul]
    have hv'' : a ^ 2 * v * (a ^ 2)⁻¹ = v * (a * v * a⁻¹) :=
      mul_left_cancel (hvvv'.trans hww.symm)
    have hA : IsConj d (v * (a * v * a⁻¹)) := by
      rw [← hv'']; exact conj_mem_D23 (a ^ 2) v h
    have hB' := isConj_d_mul_d1_of_mem h ⟨conj_mem_D23 a v h, hav, hcomm.symm⟩
    exact not_isConj_d_d_mul_d1 (hA.trans hB'.symm)
  · exact (not_twoB_pair hB hD hDc' h (h.trans (isConj_iff.2 ⟨a, rfl⟩)) (fun e => hav e.symm)
      hcomm (hZD v hvZ) (hZD _ hv'Z)).elim
  · exact of_twoC v h (hZD v hvZ)

theorem i1017FiTwoThreeTwist_of_facts
    (h22 : I1017FiTwoTwoTwist) (hB : FactB) (hC : FactC) :
    I1017FiTwoThreeTwist := by
  obtain ⟨b⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Fi23 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi23).Group) := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have hX : Nonempty (↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group) := ⟨fi23EquivJ.symm.trans b⟩
  refine @noTwistRank_of_model .Fi23 5 ↥J inferInstance hX ?_
  intro E hE hcard T hT hET
  refine noTwist_of_hyperCent (r := 5) (by norm_num) ?_ E hE hcard T hT hET
  intro E' D hE' hEc hDE hDc T' hT' hTD hET'
  exact hyper_cent h22 hB hC E' D hE' hEc hDE hDc T' hT' hTD hET'

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist

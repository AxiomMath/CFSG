module

public import CFSG.ClassicalInvolution.Q3.TL4SepThmAB
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
public import CFSG.ClassicalInvolution.Q3.TL3DichThmB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isCyclic_of_comm (hd : TightDatum R S t) {X : Subgroup Y} (hXR : X ≤ R)
    (hX2 : IsPGroup 2 ↥X) (hXc : ∀ q ∈ X, ∀ q' ∈ X, q * q' = q' * q) : IsCyclic ↥X := by
  let : CommGroup ↥X :=
    { (inferInstance : Group ↥X) with mul_comm := fun x y => Subtype.ext (hXc x x.2 y y.2) }
  refine CFSG.ComponentClassification.FooteLit.isCyclic_of_unique_involution hX2 ?_
  intro x y hx hy
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  by_cases hy1 : y = 1
  · exact Or.inr (Or.inl hy1)
  refine Or.inr (Or.inr (Subtype.ext ?_))
  have hox : orderOf (x : Y) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx hx1
  have hoy : orderOf (y : Y) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy hy1
  rw [hd.eq_of_orderOf_eq_two (hXR x.2) hox, hd.eq_of_orderOf_eq_two (hXR y.2) hoy]

theorem false_of_inner_R (hd : TightDatum R S t) (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) (hnc : ¬ ∀ x ∈ A, x * t = t * x) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := t_mul_t hd
  have hrR : r ∈ R := hd.S₀_le hrS
  have hrt : r * t = t * r := mul_t_comm_of_mem_R hd hrR
  obtain ⟨a, haA, e, he, hae⟩ := hd.exists_inner hA hrS hrA
  have hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹ := by
    intro x hx
    rw [hae, mul_inv_rev]
    calc a * e * x * (e⁻¹ * a⁻¹) = a * (e * x) * e⁻¹ * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [← he x hx]; group
  have ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a) := by
    intro y hy
    have h1 : t * (t * y * t⁻¹) * t⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by
      rw [hta y hy, hta _ (A.mul_mem (A.mul_mem haA hy) (A.inv_mem haA))]
    have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [ht2]; group
    rw [h2] at h1
    calc a * a * y = a * (a * y * a⁻¹) * a⁻¹ * (a * a) := by group
      _ = y * (a * a) := by rw [← h1]
  have hanc : ∃ y ∈ A, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro x hx
    have h1 : t * x * t⁻¹ = x := by rw [hta x hx, hcon x hx]; group
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  have hZ2 := TightA.isPGroup_center_component hO hA
  have htwin : ∀ w ∈ A, (∀ y ∈ A, (w * a * w⁻¹ * a⁻¹) * y = y * (w * a * w⁻¹ * a⁻¹)) →
      w * a = a * w := fun w hw hc =>
    hd.no_twin hO hE2 hA hrS hrr hrA haA hta ha2 hw hc
  set CA : Subgroup Y := A ⊓ Subgroup.centralizer ({t} : Set Y) with hCA
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (P := CA) (T := ⊥) IsPGroup.of_bot bot_le
  have hCAa : CA = A ⊓ Subgroup.centralizer ({a} : Set Y) := by
    ext x
    simp only [hCA, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxt⟩
      refine ⟨hx, ?_⟩
      have h1 : a * x * a⁻¹ = x := by rw [← hta x hx, ← hxt]; group
      calc x * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨hx, hxa⟩
      refine ⟨hx, ?_⟩
      have h1 : t * x * t⁻¹ = x := by rw [hta x hx, ← hxa]; group
      calc x * t = t * x * t⁻¹ * t := by rw [h1]
        _ = t * x := by group
  have hV : IsSylow2In V₀ (A ⊓ Subgroup.centralizer ({a} : Set Y)) := hCAa ▸ hV₀
  have hV0A : V₀ ≤ A := hV₀.1.trans inf_le_left
  have hV0t : ∀ x ∈ V₀, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV₀.1 hx).2
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hAB : ∀ x ∈ A, ∀ y ∈ conjSub r A, Commute x y := fun x hx y hy =>
    comm_of_ne hA hAr hrA.symm hx hy
  have htA : t ∉ A := by
    intro htA
    have htB : t ∈ conjSub r A := by
      have := conj_mem_conjSub (n := r) htA
      rwa [hrt, mul_inv_cancel_right] at this
    exact hnc fun x hx => (hAB x hx t htB).eq
  have htB : t ∉ conjSub r A := by
    intro htB
    apply htA
    rw [mem_conjSub_iff] at htB
    have e1 : r⁻¹ * t * r = t := by rw [mul_assoc, ← hrt]; group
    rwa [e1] at htB
  set W : Subgroup Y := V₀ ⊔ conjSub r V₀ with hW
  have hVrc : V₀ ≤ Subgroup.normalizer (conjSub r V₀ : Set Y) := by
    intro x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    refine conjSub_eq_of_mem_of_commutes (K := V₀) hx fun u hu v hv => ?_
    exact comm_of_ne hA hAr hrA.symm (hV0A hu) (conjSub_mono hV0A hv)
  have hVrc' : conjSub r V₀ ≤ Subgroup.normalizer (V₀ : Set Y) := by
    intro x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    refine conjSub_eq_of_mem_of_commutes (K := conjSub r V₀) hx fun u hu v hv => ?_
    exact comm_of_ne hAr hA hrA (conjSub_mono hV0A hu) (hV0A hv)
  have hW2 : IsPGroup 2 ↥W := IsPGroup.to_sup_of_normal_right' hV₀.2.1 (hV₀.2.1.map _) hVrc
  have hdec : ∀ q ∈ W, ∃ qa ∈ V₀, ∃ qb ∈ conjSub r V₀, qa * qb = q := by
    intro q hq
    rw [← SetLike.mem_coe, hW, Subgroup.coe_mul_of_right_le_normalizer_left V₀ _ hVrc'] at hq
    exact hq
  have hVrt : ∀ y ∈ conjSub r V₀, y * t = t * y := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hc : Commute (r * (r⁻¹ * y * r) * r⁻¹) t :=
      (Commute.mul_left hrt (hV0t _ hy)).mul_left (Commute.inv_left hrt)
    have e1 : r * (r⁻¹ * y * r) * r⁻¹ = y := by group
    rw [e1] at hc
    exact hc.eq
  set X : Subgroup Y := W ⊓ R with hX
  have hXc : ∀ q ∈ X, ∀ q' ∈ X, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨qa, hqa, qb, hqb, rfl⟩ := hdec q hq.1
    obtain ⟨qa', hqa', qb', hqb', rfl⟩ := hdec q' hq'.1
    have hqaA := hV0A hqa
    have hqaA' := hV0A hqa'
    have hqbB : qb ∈ conjSub r A := conjSub_mono hV0A hqb
    have hqbB' : qb' ∈ conjSub r A := conjSub_mono hV0A hqb'
    have hcA : qa * qa' * qa⁻¹ * qa'⁻¹ ∈ R := by
      have h1 := hd.comm_mem (hV0t qa hqa) hq'.2
      have e1 := comm_mul_mul_eq (Commute.one_right qa) (hAB _ hqaA _ hqbB')
        (Commute.one_right qa') (hAB _ hqaA' _ hqbB')
      simp only [mul_one, inv_one, one_mul, mul_inv_cancel] at e1
      rwa [e1] at h1
    have hcB : qb * qb' * qb⁻¹ * qb'⁻¹ ∈ R := by
      have h1 := hd.comm_mem (hVrt qb hqb) hq'.2
      have e1 := comm_mul_mul_eq (Commute.one_left qb) (Commute.one_left qb')
        (hAB _ hqaA' _ hqbB) (hAB _ hqaA' _ hqbB')
      simp only [one_mul, mul_one, inv_one, mul_inv_cancel] at e1
      rwa [e1] at h1
    have hoA : Odd (orderOf (qa * qa' * qa⁻¹ * qa'⁻¹)) := odd_orderOf_of_not_mem hd htA hcA
      (A.mul_mem (A.mul_mem (A.mul_mem hqaA hqaA') (A.inv_mem hqaA)) (A.inv_mem hqaA'))
    have hoB : Odd (orderOf (qb * qb' * qb⁻¹ * qb'⁻¹)) := odd_orderOf_of_not_mem hd htB hcB
      ((conjSub r A).mul_mem ((conjSub r A).mul_mem ((conjSub r A).mul_mem hqbB hqbB')
        ((conjSub r A).inv_mem hqbB)) ((conjSub r A).inv_mem hqbB'))
    have hcomm : Commute (qa * qa' * qa⁻¹ * qa'⁻¹) (qb * qb' * qb⁻¹ * qb'⁻¹) :=
      hAB _ (A.mul_mem (A.mul_mem (A.mul_mem hqaA hqaA') (A.inv_mem hqaA)) (A.inv_mem hqaA'))
        _ ((conjSub r A).mul_mem ((conjSub r A).mul_mem ((conjSub r A).mul_mem hqbB hqbB')
          ((conjSub r A).inv_mem hqbB)) ((conjSub r A).inv_mem hqbB'))
    have heq := comm_mul_mul_eq (hAB _ hqaA _ hqbB) (hAB _ hqaA _ hqbB') (hAB _ hqaA' _ hqbB)
      (hAB _ hqaA' _ hqbB')
    set c := qa * qb * (qa' * qb') * (qa * qb)⁻¹ * (qa' * qb')⁻¹ with hc
    have hodd : Odd (orderOf c) := by
      rw [heq]
      exact Odd.of_dvd_nat (hoA.mul hoB) (hcomm.orderOf_mul_dvd_mul_orderOf)
    have hcW : c ∈ W := by
      have hqW : qa * qb ∈ W := hq.1
      have hqW' : qa' * qb' ∈ W := hq'.1
      exact W.mul_mem (W.mul_mem (W.mul_mem hqW hqW') (W.inv_mem hqW)) (W.inv_mem hqW')
    have hc1 : c = 1 := eq_one_of_isPGroup_of_mem_odd (A := Subgroup.zpowers c)
      (by rw [Nat.card_zpowers]; exact hodd) (Subgroup.mem_zpowers c)
      (hW2.to_le (Subgroup.zpowers_le.mpr hcW))
    calc qa * qb * (qa' * qb') = c * (qa' * qb' * (qa * qb)) := by rw [hc]; group
      _ = qa' * qb' * (qa * qb) := by rw [hc1, one_mul]
  have hXcyc : IsCyclic ↥X := isCyclic_of_comm hd inf_le_right (hW2.to_le inf_le_left) hXc
  have hcov : ∀ x ∈ V₀, ∃ ξ ∈ X, ∀ y ∈ A, ξ * y * ξ⁻¹ = x * y * x⁻¹ := by
    intro x hx
    have hacts : ∀ y ∈ A, x * r * x⁻¹ * r⁻¹ * y * (x * r * x⁻¹ * r⁻¹)⁻¹ = x * y * x⁻¹ := by
      intro y hy
      have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem (hV0A hx))
      have hc := comm_of_ne hAr hA hrA hu hy
      calc x * r * x⁻¹ * r⁻¹ * y * (x * r * x⁻¹ * r⁻¹)⁻¹
          = x * ((r * x⁻¹ * r⁻¹) * y) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hc]; group
    have hxW : x ∈ W := Subgroup.mem_sup_left hx
    have hrxW : r * x⁻¹ * r⁻¹ ∈ W :=
      Subgroup.mem_sup_right (conj_mem_conjSub (V₀.inv_mem hx))
    have hxrW : x * r * x⁻¹ * r⁻¹ ∈ W := by
      have := W.mul_mem hxW hrxW
      rwa [show x * (r * x⁻¹ * r⁻¹) = x * r * x⁻¹ * r⁻¹ by group] at this
    exact ⟨x * r * x⁻¹ * r⁻¹, ⟨hxrW, hd.comm_mem (hV0t x hx) hrR⟩, hacts⟩
  exact TightA.false_of_cyclic_cover hA.1 hZ2 haA hanc ha2 htwin hV hXcyc hcov

theorem conjSub_component_eq_R (hd : TightDatum R S t) (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) :
    conjSub s A = A := by
  by_contra hsA
  have htA := conjSub_t_eq_R hd hA
  obtain ⟨s', hs', hss, hs'A⟩ := exists_sq_of_conjSub_ne hd hs hsA
  by_cases hc : ∀ x ∈ A, x * t = t * x
  · exact hd.not_centralizes hA hs' hs'A hc
  · exact false_of_inner_R hd hO hE2 hA hs' hss hs'A hc

end CFSG.ClassicalInvolution.Q3.TL4

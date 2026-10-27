module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyThrSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyAtlas

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

namespace SAFyThrE

section Abstract

variable {E Q : Type*} [Group E] [Group Q]

theorem sq_eq_one_of_mem_center (hZ : Nat.card (center E) = 2) {z : E} (hz : z ∈ center E) :
    z ^ 2 = 1 := by
  have h : (⟨z, hz⟩ : center E) ^ 2 = 1 := by
    rw [← hZ]
    exact pow_card_eq_one'
  exact congrArg Subtype.val h

theorem eq_of_order_three (φ : E →* Q) (hker : φ.ker = center E)
    (hZ : Nat.card (center E) = 2) {a b : E} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (h : φ a = φ b) : a = b := by
  have hz : b⁻¹ * a ∈ center E := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hz2 : (b⁻¹ * a) ^ 2 = 1 := sq_eq_one_of_mem_center hZ hz
  have hcomm : Commute b (b⁻¹ * a) := Subgroup.mem_center_iff.mp hz b
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hab : a = b * (b⁻¹ * a) := by group
  have h1 : (b⁻¹ * a) = 1 := by
    calc b⁻¹ * a = (b⁻¹ * a) ^ 3 := by rw [pow_succ, hz2, one_mul]
      _ = 1 := by
          have : a ^ 3 = b ^ 3 * (b⁻¹ * a) ^ 3 := by
            conv_lhs => rw [hab]
            exact hcomm.mul_pow 3
          rw [ha3, hb3, one_mul] at this
          exact this.symm
  rw [hab, h1, mul_one]

theorem orderOf_map_eq_three (φ : E →* Q) (hker : φ.ker = center E)
    (hZ : Nat.card (center E) = 2) {a : E} (ha : orderOf a = 3) : orderOf (φ a) = 3 := by
  have hdvd : orderOf (φ a) ∣ 3 := by
    rw [← ha]
    exact orderOf_map_dvd φ a
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exfalso
    have h1 : φ a = 1 := orderOf_eq_one_iff.1 h
    have hz : a ∈ center E := by
      rw [← hker]
      exact h1
    have h2 : a ^ 2 = 1 := sq_eq_one_of_mem_center hZ hz
    have h3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    have : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [h2, h3]; group
    rw [this, orderOf_one] at ha
    omega
  · exact h

theorem card_centralizer_le [Finite E] [Finite Q] (φ : E →* Q) (hker : φ.ker = center E)
    (hZ : Nat.card (center E) = 2) (a : E) :
    Nat.card (centralizer ({a} : Set E)) ≤ 2 * Nat.card (centralizer ({φ a} : Set Q)) := by
  set C := centralizer ({a} : Set E) with hC
  set f : C →* Q := φ.comp C.subtype with hf
  have hrange : f.range ≤ centralizer ({φ a} : Set Q) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.1 c.2
    simp only [hf, MonoidHom.comp_apply, coe_subtype]
    rw [← map_mul, ← map_mul, hc]
  have hkerle : Nat.card f.ker ≤ 2 := by
    rw [← hZ]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : C) : E), ?_⟩ : center E)) ?_
    · rw [← hker, MonoidHom.mem_ker]
      exact x.2
    · intro x y hxy
      have h := congrArg (fun z : center E => (z : E)) hxy
      exact Subtype.ext (Subtype.ext h)
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ Nat.card (centralizer ({φ a} : Set Q)) :=
    Subgroup.card_le_of_le hrange
  rw [← h1]
  calc Nat.card f.ker * Nat.card f.range ≤ 2 * Nat.card (centralizer ({φ a} : Set Q)) :=
        Nat.mul_le_mul hkerle h2

theorem card_centralizer_subtype_le {M : Type*} [Group M] [Finite M] (P : Subgroup M) (x : P) :
    Nat.card (centralizer ({x} : Set P)) ≤
      Nat.card ↥(centralizer ({(x : M)} : Set M) ⊓ P) := by
  refine Nat.card_le_card_of_injective
    (fun c => ⟨((c : P) : M), Subgroup.mem_inf.2 ⟨?_, (c : P).2⟩⟩) ?_
  · rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2)
  · intro c d h
    have h' := congrArg (fun z : ↥(centralizer ({(x : M)} : Set M) ⊓ P) => (z : M)) h
    exact Subtype.ext (Subtype.ext h')

end Abstract

end SAFyThrE

section HS


theorem hsThreeClass : HSThreeClass := by
  intro E _ _ _ hZ hq
  obtain ⟨ψ⟩ := hq
  have ψ' : E ⧸ center E ≃* NativeSporadic.HS := ψ
  let f : E ⧸ center E ≃* hs100P := ψ'.trans hs100Equiv
  let φ : E →* hs100P := f.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hsurj : Function.Surjective φ := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center E := by
    ext x
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  obtain ⟨hconj, hcent⟩ := hs100_order_three
  have hord : ∀ {a : E}, orderOf a = 3 → orderOf ((φ a : hs100P) : Equiv.Perm (Fin 100)) = 3 := by
    intro a ha
    rw [Subgroup.orderOf_coe]
    exact SAFyThrE.orderOf_map_eq_three φ hker hZ ha
  refine ⟨fun a b ha hb => ?_, fun a ha => ?_⟩
  · obtain ⟨g, hg, hgab⟩ := hconj _ (φ a).2 _ (φ b).2 (hord ha) (hord hb)
    obtain ⟨e, he⟩ := hsurj ⟨g, hg⟩
    refine ⟨e, SAFyThrE.eq_of_order_three φ hker hZ (a := e * a * e⁻¹) (b := b) ?_ hb ?_⟩
    · rw [← ha]
      exact (MulEquiv.orderOf_eq (MulAut.conj e) a)
    · apply Subtype.ext
      rw [map_mul, map_mul, map_inv, he]
      simpa using hgab
  · have h1 := SAFyThrE.card_centralizer_le φ hker hZ a
    have h2 := (SAFyThrE.card_centralizer_subtype_le hs100P (φ a)).trans
      (hcent _ (φ a).2 (hord ha))
    omega

end HS

end CFSG.EvenSporadicStandard.TwoHS

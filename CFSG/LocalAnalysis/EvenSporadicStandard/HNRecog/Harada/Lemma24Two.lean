module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24PUniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Bridge

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a : G}

private lemma coordElt_injective {ι : Elem2 6 →* G} (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

theorem card_two_subgroup_le [Finite G] {t z z₁ : G} (h : Setting24 ι a) (hD3 : HData3 G t z z₁)
    (ht : coordElt ι tv = t) (hat : a ∈ centralizer ({t} : Set G)) (ha3 : orderOf a = 3)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) :
    ∀ R : Subgroup G, R ≤ centralizer ({a} : Set G) → IsPGroup 2 R → Nat.card R ≤ 64 := by
  classical
  have hcoordinj : Function.Injective (coordElt ι) := coordElt_injective h.inj
  have hτ : ∀ (g x : G), IsConj t x → IsConj t (g * x * g⁻¹) := by
    intro g x hx
    rw [isConj_iff] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    exact ⟨g * c, by rw [← hc]; group⟩
  have hP2 : IsPGroup 2 (P24 ι a) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.iff_card.mpr ⟨6, by rw [card_P24 h]; norm_num⟩
  have hEab : IsMulCommutative ↥(E24 ι a) := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    obtain ⟨v, -, hv⟩ := (mem_E24_iff h).mp x.2
    obtain ⟨w, -, hw⟩ := (mem_E24_iff h).mp y.2
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [hv, hw, ← coordElt_add, ← coordElt_add, add_comm]
  have hT : Set.ncard {x : G | x ∈ E24 ι a ∧ IsConj t x} = 10 := by
    have hset : {x : G | x ∈ E24 ι a ∧ IsConj t x}
        = coordElt ι '' {v : V6 | v ∈ Fix3 ∧ qp v = 1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨v, hvF, hxv⟩ := (mem_E24_iff h).mp hx.1
        refine ⟨v, ⟨hvF, ?_⟩, hxv.symm⟩
        rw [hxv] at hx
        exact (hconj v).mp hx.2
      · rintro ⟨v, ⟨hvF, hvqp⟩, hvx⟩
        refine ⟨(mem_E24_iff h).mpr ⟨v, hvF, hvx.symm⟩, ?_⟩
        rw [← hvx]
        exact (hconj v).mpr hvqp
    rw [hset, Set.ncard_image_of_injective _ hcoordinj]
    have hset2 : {v : V6 | v ∈ Fix3 ∧ qp v = 1}
        = ((Fix3.filter fun v => qp v = 1 : Finset V6) : Set V6) := by
      ext v
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    rw [hset2, Set.ncard_coe_finset, card_Fix3_qp_one]
  have hmove : ∀ x ∈ E24 ι a, IsConj t x → ∃ p ∈ P24 ι a, p * x * p⁻¹ ≠ x := by
    intro x hxE hxEx
    obtain ⟨v, hvF, hxv⟩ := (mem_E24_iff h).mp hxE
    have hv1 : qp v = 1 := by
      rw [hxv] at hxEx
      exact (hconj v).mp hxEx
    have hne : uV v ≠ v ∨ wV v ≠ v := by
      by_contra hcon
      push_neg at hcon
      have hq0 := Fix3_Vg_fixed_qp_zero v hvF hcon.1 hcon.2
      rw [hv1] at hq0
      exact one_ne_zero hq0
    rw [hxv]
    rcases hne with hne | hne
    · obtain ⟨p, hpP, hpind⟩ := exists_lift_P24 h (mem_Vg_iff.mpr (Or.inr (Or.inl rfl)))
      refine ⟨p, hpP, ?_⟩
      intro hcon
      rw [hpind v] at hcon
      exact hne (coordElt_injective h.inj hcon)
    · obtain ⟨p, hpP, hpind⟩ :=
        exists_lift_P24 h (mem_Vg_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
      refine ⟨p, hpP, ?_⟩
      intro hcon
      rw [hpind v] at hcon
      exact hne (coordElt_injective h.inj hcon)
  have h32 : ∀ x ∈ E24 ι a, IsConj t x → ∀ R : Subgroup G,
      R ≤ centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) → IsPGroup 2 R →
      Nat.card R ≤ 32 := by
    intro x hxE hx R hR hR2
    exact card_le_32_of_isConj hD3 hat ha3 hx
      (Subgroup.mem_centralizer_singleton_iff.mp hxE.2) hR hR2
  exact card_le_of_sylow_data (τ := fun x => IsConj t x) (P := P24 ι a) (E := E24 ι a)
    hτ inf_le_right hP2 (card_P24 h) E24_le_P24 hEab (card_E24 h)
    (fun B hB hBab hBcard => E24_unique h hB hBab hBcard) hT hmove h32

end CFSG.EvenSporadicStandard.HNRecog.Harada

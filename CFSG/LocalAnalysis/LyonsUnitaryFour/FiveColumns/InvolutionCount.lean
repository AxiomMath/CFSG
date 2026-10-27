module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

variable {G : Type*} [Group G] [Fintype G]

theorem exists_conj_mem_of_isConj_involution (S : Sylow 2 G) {Z : Subgroup G}
    (hinvZ : ∀ x ∈ (S : Subgroup G), x * x = 1 → x ∈ Z) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {z : G} (hz : z * z = 1) (x : H) (hx : IsConj (x : G) z) :
    ∃ c : H, ((c * x * c⁻¹ : H) : G) ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : (x : G) * x = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    have : (x : G) = g⁻¹ * z * g := by rw [← hg]; group
    rw [this]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz]; group
  obtain ⟨c, hc, hcS⟩ := exists_conj_mem_sylow_of_le S hSH x.2 ⟨1, by rw [pow_one, pow_two, hxx]⟩
  refine ⟨⟨c, hc⟩, ?_⟩
  apply hinvZ _ (by simpa using hcS)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc c * x * c⁻¹ * (c * x * c⁻¹) = c * ((x : G) * x) * c⁻¹ := by group
    _ = 1 := by rw [hxx]; group

theorem card_isConj_image_mul_card_centralizer (S : Sylow 2 G) {Z : Subgroup G}
    (hinvZ : ∀ x ∈ (S : Subgroup G), x * x = 1 → x ∈ Z) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hZS : Z ≤ (S : Subgroup G)) {L : Type*} [Group L]
    (π : H →* L) (hcentral : ∀ v (hv : v ∈ Z), π ⟨v, hSH (hZS hv)⟩ ∈ Subgroup.center L)
    (hinj : ∀ v (hv : v ∈ Z) v' (hv' : v' ∈ Z),
      π ⟨v, hSH (hZS hv)⟩ = π ⟨v', hSH (hZS hv')⟩ → v = v')
    {z : G} (hz : z * z = 1)
    (hall : ∀ v ∈ Z, v ≠ 1 → IsConj v z) {v : G} (hv : v ∈ Z) (hv1 : v ≠ 1) :
    (Finset.univ.filter fun x : H => IsConj (x : G) z ∧ π x = π ⟨v, hSH (hZS hv)⟩).card *
        Nat.card (Subgroup.centralizer ({(⟨v, hSH (hZS hv)⟩ : H)} : Set H)) = Nat.card H := by
  have hcen0 := hcentral v hv
  have hinj0 := hinj
  generalize hv' : (⟨v, hSH (hZS hv)⟩ : H) = v' at hcen0 ⊢
  have hcv : ∀ g : L, g * π v' = π v' * g := Subgroup.mem_center_iff.mp hcen0
  have hv'val : (v' : G) = v := by rw [← hv']
  have hset : (Finset.univ.filter fun x : H => IsConj (x : G) z ∧ π x = π v') =
      Finset.univ.filter fun x : H => IsConj x v' := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxz, hπx⟩
      obtain ⟨c, hc⟩ := exists_conj_mem_of_isConj_involution S hinvZ hSH hz x hxz
      have hπu : π (c * x * c⁻¹) = π v' := by
        rw [map_mul, map_mul, hπx, map_inv, hcv, mul_inv_cancel_right]
      have huv : ((c * x * c⁻¹ : H) : G) = v := by
        apply hinj0 _ hc v hv
        rw [hv']
        exact hπu
      have hux : c * x * c⁻¹ = v' := Subtype.ext (huv.trans hv'val.symm)
      exact isConj_iff.mpr ⟨c, hux⟩
    · intro hxv
      obtain ⟨c, hc⟩ := isConj_iff.mp hxv
      refine ⟨?_, ?_⟩
      · refine (isConj_iff.mpr ⟨(c : G), ?_⟩).trans (hall v hv hv1)
        have := congrArg Subtype.val hc
        simpa [hv'val] using this
      · have hx : x = c⁻¹ * v' * c := by rw [← hc]; group
        calc π x = (π c)⁻¹ * π v' * π c := by rw [hx, map_mul, map_mul, map_inv]
          _ = (π c)⁻¹ * (π c * π v') := by rw [hcv (π c), mul_assoc]
          _ = π v' := by group
  rw [hset]
  have hclass := card_conjClass_mul_card_centralizer v'
  rw [← hclass]
  congr 1
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
    ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

omit [Fintype G] in
theorem card_centralizer_subgroup_eq {H : Subgroup G} {v : G} (hv : v ∈ H) :
    Nat.card (Subgroup.centralizer ({(⟨v, hv⟩ : H)} : Set H)) =
      Nat.card (H ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) := by
  refine Nat.card_congr ⟨fun c => ⟨c.1.1, c.1.2, ?_⟩, fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩, ?_, ?_⟩
  · have := Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  · have := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext this)
  · intro c; rfl
  · intro c; rfl

end CFSG.LyonsUnitaryFour

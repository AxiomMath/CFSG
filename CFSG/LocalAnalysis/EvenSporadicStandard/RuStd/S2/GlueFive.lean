module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueSyl
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Cen
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueCen
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.ThreeLocal

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

@[expose] def fCen (d : PartThreeData G L t) : CenG d.r :=
  ⟨d.f, mem_centralizer_singleton_iff.2 d.fr_comm⟩

omit [Finite G] in
theorem card_centralizer_conj (c x : G) :
    Nat.card (centralizer ({c * x * c⁻¹} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have h := card_centralizer_conj_image c ({x} : Set G)
  rwa [Set.image_singleton] at h

theorem f_nine_of (d : PartThreeData G L t) :
    ¬ 9 ∣ Nat.card (centralizer ({fCen d} : Set (CenG d.r))) := by
  intro h9
  have h := (card_cen_dvd d.r (fCen d))
  have h2 : Nat.card (centralizer ({d.f} : Set G)) = 877800 := d.card_Γ
  have h3 : Nat.card (centralizer ({(fCen d : G)} : Set G)) = 877800 := h2
  rw [h3] at h
  exact absurd (h9.trans h) (by norm_num)

theorem f_five_of (d : PartThreeData G L t) :
    25 ∣ Nat.card (centralizer ({fCen d} : Set (CenG d.r))) ∧
      ¬ 125 ∣ Nat.card (centralizer ({fCen d} : Set (CenG d.r))) := by
  have hdvd := card_cen_dvd d.r (fCen d)
  have h3 : Nat.card (centralizer ({(fCen d : G)} : Set G)) = 877800 := d.card_Γ
  rw [h3] at hdvd
  refine ⟨?_, fun h => absurd (h.trans hdvd) (by norm_num)⟩
  have h25 := d.five_dvd
  have e : Nat.card (centralizer ({fCen d} : Set (CenG d.r))) =
      Nat.card (centralizer ({d.f} : Set G) ⊓ centralizer ({d.r} : Set G) : Subgroup G) := by
    rw [card_cen_eq, inf_comm]
    rfl
  rw [e]
  exact h25

theorem exists_conj_F₁ (d : PartThreeData G L t) {Q : Subgroup G}
    (hQC : Q ≤ centralizer ({d.f} : Set G)) (hQ : IsPGroup 5 Q) :
    ∃ c ∈ centralizer ({d.f} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ d.F₁ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine exists_conj_le_sylow (p := 5) d.F₁_le_C ?_ hQC hQ
  rw [d.F₁_card, d.card_Γ, factorization_five]
  norm_num

theorem orderOf_five_of_mem_F₁ (d : PartThreeData G L t) (h5 : RuFiveFacts L) {y : G}
    (hy : y ∈ d.F₁) (hy1 : y ≠ 1) : orderOf y = 5 := by
  have hyL : y ∈ L := d.F₁_le_L hy
  have hdvd : orderOf y ∣ 5 ^ 2 := by
    have := Subgroup.orderOf_dvd_natCard d.F₁ hy
    rwa [d.F₁_card] at this
  have hp : IsPGroup 5 (zpowers (⟨y, hyL⟩ : L)) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk]; exact hdvd)
  have h5y : y ^ 5 = 1 := congrArg Subtype.val (h5.exp5 _ hp)
  have hd5 : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one h5y
  rcases (Nat.dvd_prime Nat.prime_five).1 hd5 with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hy1
  · exact h

theorem card_cen_of_typeA (d : PartThreeData G L t) (h5 : RuFiveFacts L) {y : G} (hyL : y ∈ L)
    (hy5 : orderOf y = 5) (hA : Nat.card (centralizer ({(⟨y, hyL⟩ : L)} : Set L)) = 300) :
    Nat.card (centralizer ({y} : Set G)) = 877800 := by
  have hfL5 : orderOf (⟨d.f, d.f_mem⟩ : L) = 5 := by rw [Subgroup.orderOf_mk]; exact d.f_ord
  have hyL5 : orderOf (⟨y, hyL⟩ : L) = 5 := by rw [Subgroup.orderOf_mk]; exact hy5
  obtain ⟨c, k, hck⟩ := h5.conjA ⟨d.f, d.f_mem⟩ ⟨y, hyL⟩ hfL5 hyL5 d.f_typeA hA
  have hck' : (c : G) * d.f * (c : G)⁻¹ = y ^ k := by
    simpa using congrArg Subtype.val hck
  have hord : orderOf (y ^ k) = 5 := by
    rw [← hck']
    rw [← d.f_ord]
    exact (SemiconjBy.orderOf_eq (c : G) (show SemiconjBy (c : G) d.f ((c : G) * d.f * (c : G)⁻¹)
      from by simp [SemiconjBy, mul_assoc])).symm
  have hz : zpowers (y ^ k) = zpowers y := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact zpowers_le.2 (Subgroup.pow_mem _ (mem_zpowers y) k)
    · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hy5]
  have hcen : centralizer ({y ^ k} : Set G) = centralizer ({y} : Set G) := by
    apply centralizer_eq_of_closure_eq
    rw [← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hz]
  rw [← hcen, ← hck', card_centralizer_conj]
  exact d.card_Γ

theorem conj_typeB (d : PartThreeData G L t) (h5 : RuFiveFacts L) {x c : G}
    (hx1 : x ≠ 1) (hy : c * x * c⁻¹ ∈ d.F₁) (hx9 : 9 ∣ Nat.card (centralizer ({x} : Set G))) :
    ∃ hyL : c * x * c⁻¹ ∈ L, orderOf (c * x * c⁻¹) = 5 ∧
      Nat.card (centralizer ({(⟨c * x * c⁻¹, hyL⟩ : L)} : Set L)) = 1000 := by
  have hy1 : c * x * c⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hy5 := orderOf_five_of_mem_F₁ d h5 hy hy1
  have hyL : c * x * c⁻¹ ∈ L := d.F₁_le_L hy
  refine ⟨hyL, hy5, ?_⟩
  have hyL5 : orderOf (⟨c * x * c⁻¹, hyL⟩ : L) = 5 := by rw [Subgroup.orderOf_mk]; exact hy5
  rcases h5.typeAB _ hyL5 with ⟨hA, -⟩ | ⟨hB, -⟩
  · exfalso
    have h1 := card_cen_of_typeA d h5 hyL hy5 hA
    rw [card_centralizer_conj] at h1
    rw [h1] at hx9
    exact absurd hx9 (by norm_num)
  · exact hB

end CFSG.EvenSporadicStandard.RuStd.S2.Glue

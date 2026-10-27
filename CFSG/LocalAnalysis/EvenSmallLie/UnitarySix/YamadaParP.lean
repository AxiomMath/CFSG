module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParN1

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup CFSG.ABGLocalTools

theorem card_SL4 : Nat.card SL4 = 987033600 := by
  rw [Matrix.card_SL_field]
  have : Fintype.card CFSG.Fischer.F4 = 4 := rfl
  simp only [this, Fin.prod_univ_four]
  norm_num

theorem exists_isSylowOf_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q X : Subgroup G} (hQ : IsPGroup p Q) (hQX : Q ≤ X) :
    ∃ T : Subgroup G, IsSylowOf p T X ∧ Q ≤ T := by
  have hQ' : IsPGroup p (Q.subgroupOf X) := hQ.comap_subtype
  obtain ⟨T', hT'⟩ := hQ'.exists_le_sylow
  refine ⟨(T' : Subgroup X).map X.subtype, ⟨T', rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQX hq⟩, hT' (show (⟨q, hQX hq⟩ : X) ∈ Q.subgroupOf X from hq), rfl⟩

theorem isPGroup_of_card_pow {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (h : Nat.card H = 2 ^ n) : IsPGroup 2 H := IsPGroup.of_card h

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] [Finite G] {t : G} (ht : t * t = 1) :
    IsPGroup 2 (zpowers t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := (orderOf t).factorization 2) ?_
  rw [Nat.card_zpowers]
  have hd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, ht])
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1 <;> rw [h1] <;> norm_num

theorem mem_normalizer_inf {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← mem_normalizer_iff.mp hH, ← mem_normalizer_iff.mp hK]

theorem nOne_eq_sup {G : Type*} [Group G] {D₁ K₁ D₂ S P : Subgroup G} {w₂ w₃ : G}
    (hw₂ : w₂ ∈ K₁) (hw₃ : w₃ ∈ K₁) (hK : K₁ ≤ S ⊔ zpowers w₂ ⊔ zpowers w₃)
    (hP : P ≤ nOne D₁ K₁ D₂) (hSP : S ≤ P) (hD₁P : D₁ ≤ P) (hD₂P : D₂ ≤ P) :
    nOne D₁ K₁ D₂ = P ⊔ zpowers w₂ ⊔ zpowers w₃ := by
  have hK₁ : K₁ ≤ nOne D₁ K₁ D₂ := le_sup_right.trans le_sup_left
  refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (sup_le (sup_le hP ?_) ?_)
  · exact hD₁P.trans (le_sup_left.trans le_sup_left)
  · exact hK.trans (sup_le_sup_right (sup_le_sup_right hSP _) _)
  · exact hD₂P.trans (le_sup_left.trans le_sup_left)
  · exact (zpowers_le.mpr hw₂).trans hK₁
  · exact (zpowers_le.mpr hw₃).trans hK₁

section Card

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}

theorem Y13Hyp.card_quot [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    Nat.card (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) = 987033600 ∨
      Nat.card (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) = 25920 ^ 2 := by
  have : Fact (ElemSec D₁ V₁) := ⟨h.sec⟩
  have : (D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.D₁_le_nOne).mpr h.nOne_le_normalizer
  obtain ⟨fV, hfV⟩ := h.exists_fV
  obtain ⟨-, ⟨ψ, -⟩ | ⟨ψ, -⟩⟩ := (h.r3Hyp fV hfV).main
  · left
    rw [← Nat.card_congr ψ.toEquiv, card_SL4]
  · right
    rw [← Nat.card_congr ψ.toEquiv, Nat.card_prod, card_SU42b, sq]

theorem Y13Hyp.card_nOne [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    Nat.card (nOne D₁ K₁ D₂) = 2 ^ 30 * 240975 ∨ Nat.card (nOne D₁ K₁ D₂) = 2 ^ 30 * 164025 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (D₁.subgroupOf (nOne D₁ K₁ D₂)),
    card_subgroupOf_of_le h.D₁_le_nOne, h.card_D₁]
  rcases h.card_quot with h1 | h1 <;> rw [h1] <;> norm_num

theorem Y13Hyp.factorization_card_nOne [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    (Nat.card (nOne D₁ K₁ D₂)).factorization 2 = 30 := by
  have key : ∀ m : ℕ, ¬ 2 ∣ m → (2 ^ 30 * m).factorization 2 = 30 := fun m hm => by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
    rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm]
  rcases h.card_nOne with h1 | h1 <;> rw [h1] <;> exact key _ (by norm_num)

end Card

section Sylow

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}

theorem Y13Hyp.nOne_le_centralizer (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    nOne D₁ K₁ D₂ ≤ centralizer (V₁ : Set G) := by
  refine sup_le (sup_le (fun x hx => ?_) (fun k hk => ?_)) (fun d hd => ?_) <;>
    rw [Subgroup.mem_centralizer_iff] <;> intro v hv
  · exact h.sec.central v hv x hx
  · have := h.K₁_cent k hk v hv
    calc v * k = (k * v * k⁻¹) * k := by rw [this]
      _ = k * v := by group
  · exact h.D₂_comm v (h.V₁_le_D₂ hv) d hd

theorem Y13Hyp.inf_centralizer [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    nOne D₁ K₁ D₂ ⊓ centralizer ({t} : Set G) = K₁ ⊔ A₁ :=
  (h.main CFSG.Fischer.F4 card_F4).2.2.2.2.1

theorem Y13Hyp.exists_sylow [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) {L S : Subgroup G}
    (hSL : IsSylowOf 2 S L) (hK₁L : K₁ ≤ L) (hA₁S : A₁ ≤ S) (hSK : S ≤ K₁ ⊔ A₁)
    (hSD₂ : S ≤ normalizer (D₂ : Set G)) :
    ∃ P : Subgroup G, P ≤ nOne D₁ K₁ D₂ ∧ IsSylowOf 2 P (nOne D₁ K₁ D₂) ∧
      Nat.card P = 2 ^ 30 ∧ P ⊓ centralizer ({t} : Set G) = S ∧ S ≤ P ∧ D₁ ≤ P ∧ D₂ ≤ P ∧
      V₁ ≤ centralizer (P : Set G) ∧ t ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₁ := nOne D₁ K₁ D₂
  have hKA : K₁ ⊔ A₁ ≤ N₁ := sup_le h.K₁_le_nOne (h.A₁_le.trans h.D₁_le_nOne)
  have hKAt : K₁ ⊔ A₁ ≤ centralizer ({t} : Set G) := by
    rw [← h.inf_centralizer]; exact inf_le_right
  have hSN : S ≤ N₁ := hSK.trans hKA
  have hS2 : IsPGroup 2 S := hSL.isPGroup
  have hQ₁ : IsPGroup 2 (S ⊔ D₂ : Subgroup G) :=
    hS2.to_sup_of_normal_right' (isPGroup_of_card_pow h.card_D₂) hSD₂
  have hQ₂ : IsPGroup 2 (S ⊔ D₂ ⊔ D₁ : Subgroup G) :=
    hQ₁.to_sup_of_normal_right' (isPGroup_of_card_pow h.card_D₁)
      (sup_le (hSN.trans h.nOne_le_normalizer) h.D₂_norm)
  have htS : t ∈ normalizer (S : Set G) := mem_normalizer_of_conj_eq fun x hx => by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKAt (hSK hx))
    rw [← this, mul_inv_cancel_right]
  have htQ : t ∈ normalizer ((S ⊔ D₂ ⊔ D₁ : Subgroup G) : Set G) :=
    mem_normalizer_sup' (mem_normalizer_sup' htS h.t_D₂) h.t_D₁
  have hQ : IsPGroup 2 (S ⊔ D₂ ⊔ D₁ ⊔ zpowers t : Subgroup G) :=
    hQ₂.to_sup_of_normal_left' (isPGroup_zpowers_of_sq h.t_sq) ((zpowers_le).mpr htQ)
  have hQX : (S ⊔ D₂ ⊔ D₁ ⊔ zpowers t : Subgroup G) ≤ N₁ ⊔ zpowers t :=
    sup_le_sup_right (sup_le (sup_le hSN h.D₂_le_nOne) h.D₁_le_nOne) _
  obtain ⟨T, hT, hQT⟩ := exists_isSylowOf_le hQ hQX
  have hXN : N₁ ⊔ zpowers t ≤ normalizer (N₁ : Set G) :=
    sup_le le_normalizer ((zpowers_le).mpr h.t_mem_normalizer)
  have hP := hT.inf_of_le_normalizer le_sup_left hXN
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have htT : t ∈ T := hQT (Subgroup.mem_sup_right (mem_zpowers t))
  have hST : S ≤ T := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hQT))
  have hD₂T : D₂ ≤ T := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans hQT))
  have hD₁T : D₁ ≤ T := le_sup_right.trans (le_sup_left.trans hQT)
  refine ⟨T ⊓ N₁, inf_le_right, hP, ?_, ?_, le_inf hST hSN, le_inf hD₁T h.D₁_le_nOne,
    le_inf hD₂T h.D₂_le_nOne, ?_, mem_normalizer_inf
      (Subgroup.le_normalizer htT) h.t_mem_normalizer⟩
  · rw [hP.card_eq, h.factorization_card_nOne]
  · refine hSL.eq_of_le (le_inf (le_inf hST hSN) (hSK.trans hKAt)) ?_ ?_
    · intro x hx
      have hx' : x ∈ N₁ ⊓ centralizer ({t} : Set G) := ⟨hx.1.2, hx.2⟩
      rw [h.inf_centralizer] at hx'
      exact sup_le hK₁L (hA₁S.trans hSL.le) hx'
    · exact hT2.to_le (inf_le_left.trans inf_le_left)
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h.nOne_le_centralizer hx.2) v hv).symm

end Sylow

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Alg

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup

variable {G : Type*} [Group G]

private theorem exists_conj_mem_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime] {w : G}
    (hw : orderOf w = p) {A : Subgroup G} (hA : ¬ p ∣ A.index) : ∃ y : G, y⁻¹ * w * y ∈ A := by
  have hW : IsPGroup p (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  obtain ⟨t, ht⟩ := hW.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ A) hA
  induction t using QuotientGroup.induction_on with
  | H y =>
    refine ⟨y, ?_⟩
    have h : (↑(w * y) : G ⧸ A) = ↑y := ht ⟨w, mem_zpowers w⟩
    have h1 := QuotientGroup.eq.1 h
    have e : y⁻¹ * w * y = ((w * y)⁻¹ * y)⁻¹ := by group
    rw [e]
    exact A.inv_mem h1

theorem commutator_zpowers_le {Q₀ : Subgroup G} {x : G} (hx : x ∈ normalizer (Q₀ : Set G)) :
    ⁅Q₀, zpowers x⁆ ≤ Q₀ :=
  le_normalizer_iff_commutator_le_left.1 (zpowers_le.2 hx)

private theorem exists_conj_mem_zpowers_of_index_twenty [Finite G] {M Q₀ : Subgroup G}
    (hQM : Q₀ ≤ M) (hN : M ≤ normalizer (Q₀ : Set G)) (hQ2 : IsPGroup 2 Q₀) {x : G}
    (hxM : x ∈ M) (hx : orderOf x = 5) (hcard : Nat.card M = 20 * Nat.card Q₀) {m : G}
    (hm : m ∈ M) :
    ∃ y ∈ (Q₀ ⊔ zpowers x : Subgroup G), y⁻¹ * (m * x * m⁻¹) * y ∈ zpowers x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA5 : Nat.card (zpowers x) = 5 := by rw [Nat.card_zpowers, hx]
  have hAp : IsPGroup 5 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [hA5, pow_one])
  have hdisj : Disjoint Q₀ (zpowers x) := hQ2.disjoint_of_coprime hAp (by norm_num)
  have hAnorm : zpowers x ≤ normalizer (Q₀ : Set G) := zpowers_le.2 (hN hxM)
  have hxY : x ∈ (Q₀ ⊔ zpowers x : Subgroup G) := mem_sup_right (mem_zpowers x)
  have hYcard : Nat.card (Q₀ ⊔ zpowers x : Subgroup G) = Nat.card Q₀ * 5 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q₀ (zpowers x) hAnorm
      hdisj, hA5]
  have hYM : Q₀ ⊔ zpowers x ≤ M := sup_le hQM (zpowers_le.2 hxM)
  have hQpos : 0 < Nat.card Q₀ := Nat.card_pos
  have hidx : (Q₀ ⊔ zpowers x).relIndex M ≤ 4 := by
    have h := relIndex_mul_card (Q₀ ⊔ zpowers x) M
    rw [inf_eq_left.2 hYM, hYcard, hcard] at h
    have h' : ((Q₀ ⊔ zpowers x).relIndex M * 5) * Nat.card Q₀ = 20 * Nat.card Q₀ := by
      rw [← h, mul_assoc, mul_comm 5]
    have := Nat.eq_of_mul_eq_mul_right hQpos h'
    omega
  have hz : m * x * m⁻¹ ∈ (Q₀ ⊔ zpowers x : Subgroup G) := by
    have h := conj_mem_of_index_le_four hx hYM (le_normalizer hxY) (le_normalizer hxM) hidx
      (g := m⁻¹) (by
        rw [inv_inv]
        exact M.mul_mem hm (M.mul_mem (M.mul_mem hxM (M.inv_mem hm)) (M.inv_mem hxM)))
    have e : m * x * m⁻¹ = (m⁻¹⁻¹ * (x * m⁻¹ * x⁻¹)) * x := by group
    rw [e]
    exact mul_mem h hxY
  have hnd : ¬ 5 ∣ (zpowers x).relIndex (Q₀ ⊔ zpowers x) := by
    have h := relIndex_mul_card (zpowers x) (Q₀ ⊔ zpowers x)
    rw [inf_eq_left.2 le_sup_right, hA5, hYcard] at h
    have h' := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 5) h
    rw [h']
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ2
    rw [ha]
    intro hd
    have := Nat.le_of_dvd (by positivity) (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
    omega
  have hw : orderOf (⟨m * x * m⁻¹, hz⟩ : ↥(Q₀ ⊔ zpowers x)) = 5 := by
    rw [Subgroup.orderOf_mk]
    have h := (MulAut.conj m).orderOf_eq x
    rw [MulAut.conj_apply] at h
    rw [h, hx]
  obtain ⟨y, hy⟩ := exists_conj_mem_of_not_dvd_index hw hnd
  exact ⟨y, y.2, mem_subgroupOf.1 hy⟩

theorem normalizer_commutator_of_index_twenty [Finite G] {M Q₀ : Subgroup G}
    (hQM : Q₀ ≤ M) (hN : M ≤ normalizer (Q₀ : Set G)) (hQ2 : IsPGroup 2 Q₀) {x : G}
    (hxM : x ∈ M) (hx : orderOf x = 5) (hcard : Nat.card M = 20 * Nat.card Q₀) :
    M ≤ normalizer ((⁅Q₀, zpowers x⁆ : Subgroup G) : Set G) := by
  have hYM : Q₀ ⊔ zpowers x ≤ M := sup_le hQM (zpowers_le.2 hxM)
  have hnormC : Q₀ ⊔ zpowers x ≤ normalizer ((⁅Q₀, zpowers x⁆ : Subgroup G) : Set G) :=
    sup_le (normalizer_commutator_ge_left Q₀ (zpowers x))
      (normalizer_commutator_ge_right Q₀ (zpowers x))
  have key : ∀ m ∈ M, ∀ c ∈ (⁅Q₀, zpowers x⁆ : Subgroup G),
      m * c * m⁻¹ ∈ (⁅Q₀, zpowers x⁆ : Subgroup G) := by
    intro m hm c hc
    obtain ⟨y, hyY, hy⟩ := exists_conj_mem_zpowers_of_index_twenty hQM hN hQ2 hxM hx hcard hm
    have h1 : (⁅Q₀, zpowers x⁆ : Subgroup G).map (MulAut.conj m : G →* G) =
        ⁅Q₀, zpowers (m * x * m⁻¹)⁆ := by
      rw [map_commutator, mem_normalizer_iff_map_conj_eq.1 (hN hm), MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]
    have h2 : ⁅Q₀, zpowers (m * x * m⁻¹)⁆ ≤
        (⁅Q₀, zpowers x⁆ : Subgroup G).map (MulAut.conj y : G →* G) := by
      refine commutator_le_map_commutator ?_ ?_
      · exact (mem_normalizer_iff_map_conj_eq.1 (hN (hYM hyY))).ge
      · rw [zpowers_le]
        refine ⟨y⁻¹ * (m * x * m⁻¹) * y, hy, ?_⟩
        simp [MulAut.conj_apply]
        group
    have h3 : (⁅Q₀, zpowers x⁆ : Subgroup G).map (MulAut.conj y : G →* G) =
        ⁅Q₀, zpowers x⁆ := mem_normalizer_iff_map_conj_eq.1 (hnormC hyY)
    have h4 : m * c * m⁻¹ ∈ (⁅Q₀, zpowers x⁆ : Subgroup G).map (MulAut.conj m : G →* G) :=
      ⟨c, hc, by simp [MulAut.conj_apply]⟩
    rw [h1] at h4
    have h5 := h2 h4
    rwa [h3] at h5
  intro m hm
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key m hm c hc, fun hc => ?_⟩
  have h := key m⁻¹ (M.inv_mem hm) _ hc
  have e : m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c := by group
  rwa [e] at h

theorem exists_mul_normalizer_of_index_twenty [Finite G] {M Q₀ : Subgroup G}
    (hQM : Q₀ ≤ M) (hN : M ≤ normalizer (Q₀ : Set G)) (hQ2 : IsPGroup 2 Q₀) {x : G}
    (hxM : x ∈ M) (hx : orderOf x = 5) (hcard : Nat.card M = 20 * Nat.card Q₀) {m : G}
    (hm : m ∈ M) :
    ∃ q ∈ Q₀, ∃ n ∈ M, n ∈ normalizer ((zpowers x : Subgroup G) : Set G) ∧ m = q * n := by
  obtain ⟨y, hyY, hy⟩ := exists_conj_mem_zpowers_of_index_twenty hQM hN hQ2 hxM hx hcard hm
  have hAnorm : zpowers x ≤ normalizer (Q₀ : Set G) := zpowers_le.2 (hN hxM)
  obtain ⟨q, hq, a, ha, rfl⟩ :=
    (Set.ext_iff.1 (coe_mul_of_right_le_normalizer_left Q₀ (zpowers x) hAnorm) y).1 hyY
  have hnx : q⁻¹ * m * x * (q⁻¹ * m)⁻¹ ∈ zpowers x := by
    have h1 : a * ((q * a)⁻¹ * (m * x * m⁻¹) * (q * a)) * a⁻¹ ∈ zpowers x :=
      mul_mem (mul_mem ha hy) (inv_mem ha)
    have e : a * ((q * a)⁻¹ * (m * x * m⁻¹) * (q * a)) * a⁻¹ = q⁻¹ * m * x * (q⁻¹ * m)⁻¹ := by
      group
    rwa [e] at h1
  have hmap : (zpowers x).map (MulAut.conj (q⁻¹ * m) : G →* G) = zpowers x := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj (q⁻¹ * m)).injective).ge
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact hnx
  exact ⟨q, hq, q⁻¹ * m, M.mul_mem (M.inv_mem (hQM hq)) hm, mem_normalizer_iff_map_conj_eq.2 hmap,
    by group⟩

end CFSG.LocalAnalysis.EvenBN.Tits.S56

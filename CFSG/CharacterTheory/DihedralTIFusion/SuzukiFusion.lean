module

public import CFSG.CharacterTheory.DihedralTIFusion.SuzukiTransport
public import CFSG.CharacterTheory.DihedralTIFusion.ClassSquareKernel

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

variable {E : Type*} [Group E]

theorem centralizer_zpowers_eq (w : E) :
    Subgroup.centralizer (Subgroup.zpowers w : Set E) = Subgroup.centralizer ({w} : Set E) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h w (Subgroup.mem_zpowers w)).symm
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right h k).eq.symm

theorem mem_normalizer_zpowers_of_inv_conj {a w : E} (ha : a⁻¹ * w * a = w⁻¹) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers w : Set E) := by
  have hw : w = a * w⁻¹ * a⁻¹ := by
    rw [← ha]
    group
  have ha' : a * w * a⁻¹ = w⁻¹ := by
    calc a * w * a⁻¹ = (a * w⁻¹ * a⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [← hw]
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, ha']
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers w)) k
  · intro hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hn' : n = (a⁻¹ * w * a⁻¹⁻¹) ^ k := by
      rw [conj_zpow, hk]
      group
    rw [hn', inv_inv, ha]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers w)) k

theorem suzuki_odd_cyclic_dihedral_involution_fusion {E : Type*} [Group E] [Finite E]
    {W : Subgroup E} (hWcyclic : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hWcard : 3 ≤ Nat.card W) {u : E} (huW : u ∉ W) (hu : orderOf u = 2)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hcentralizer : ∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ →
      Subgroup.centralizer (W₀ : Set E) = W)
    (hnormalizer : ∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ →
      Subgroup.normalizer (W₀ : Set E) = W ⊔ Subgroup.zpowers u)
    (hnormal : ∀ K : Subgroup E, K.Normal → K ≠ ⊥ → u ∈ K) :
    (∀ t : E, orderOf t = 2 → IsConj t u) ∧
      ∃! c : ConjClasses E, ∃ t : E, orderOf t = 2 ∧ ConjClasses.mk t = c := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hWne : W ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot W).mp (by omega)
  have hzW : ∀ w ∈ W, w ≠ 1 → Subgroup.zpowers w ≤ W ∧ Subgroup.zpowers w ≠ ⊥ :=
    fun w hw hw1 => ⟨Subgroup.zpowers_le.mpr hw, fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)⟩
  have hC1 : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set E) = W := fun w hw hw1 => by
    rw [← centralizer_zpowers_eq]
    exact hcentralizer _ (hzW w hw hw1).1 (hzW w hw hw1).2
  obtain ⟨V, U, _, _, _, _, _, _, ρ, σ, hρ, hσ, hdeg, hsupp, w₀, hw₀W, hw₀⟩ :=
    exists_degree_gap_representations hWcyclic hWodd hWcard hC1 hu huW hinvert
      (hnormalizer W le_rfl hWne)
  have horder : ∀ {x y : E}, IsConj x y → orderOf x = orderOf y := fun ⟨_, hc⟩ =>
    SemiconjBy.orderOf_eq _ hc
  have hsq : ∀ {x : E}, orderOf x = 2 → x * x = 1 := fun hx => by
    rw [← pow_two, ← hx]
    exact pow_orderOf_eq_one _
  have hne1 : ∀ {x : E}, orderOf x = 2 → x ≠ 1 := fun hx h => by
    rw [h, orderOf_one] at hx
    omega
  have hfusion : ∀ t : E, orderOf t = 2 → IsConj t u := by
    intro t ht
    by_contra hnot
    have hαt : ρ.character t - σ.character t - 1 = 0 := by
      apply hsupp
      intro hmem
      obtain ⟨a, ha⟩ := mem_iUnion_conj_image_iff.mp hmem
      have hord : orderOf (a * t * a⁻¹) = 2 := (horder (isConj_iff.mpr ⟨a, rfl⟩)).symm.trans ht
      exact hne1 hord (eq_one_of_mul_self_eq_one_of_odd hWodd ha.1 (hsq hord))
    have hαC : ∀ x y : E, IsConj t x → IsConj t y →
        ρ.character (x * y) - σ.character (x * y) - 1 = 0 := by
      intro x y hx hy
      apply hsupp
      intro hmem
      obtain ⟨g, hg⟩ := mem_iUnion_conj_image_iff.mp hmem
      have hta : IsConj t (g * x * g⁻¹) := hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
      have htb : IsConj t (g * y * g⁻¹) := hy.trans (isConj_iff.mpr ⟨g, rfl⟩)
      set a := g * x * g⁻¹ with ha
      set b := g * y * g⁻¹ with hb
      have ha2 : a * a = 1 := hsq ((horder hta).symm.trans ht)
      have hb2 : b * b = 1 := hsq ((horder htb).symm.trans ht)
      have hab : g * (x * y) * g⁻¹ = a * b := by
        rw [ha, hb]
        group
      have hwW : a * b ∈ W := hab ▸ hg.1
      have hw1 : a * b ≠ 1 := hab ▸ hg.2
      have hinv : a⁻¹ * (a * b) * a = (a * b)⁻¹ := by
        calc a⁻¹ * (a * b) * a = b * a := by group
          _ = b⁻¹ * a⁻¹ := by
            rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
          _ = (a * b)⁻¹ := (mul_inv_rev a b).symm
      have haN := mem_normalizer_zpowers_of_inv_conj hinv
      rw [hnormalizer _ (hzW _ hwW hw1).1 (hzW _ hwW hw1).2] at haN
      rcases (mem_sup_zpowers_iff hu2 hinvert a).mp haN with haW | hauW
      · exact hne1 ((horder hta).symm.trans ht)
          (eq_one_of_mul_self_eq_one_of_odd hWodd haW ha2)
      · obtain ⟨d, -, hd⟩ := exists_conj_eq_of_mul_mem hWodd hu2 hinvert hauW
        exact hnot (hta.trans (isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv]; exact hd⟩).symm)
    have hker := involution_class_square_degree_gap_kernel ρ σ hρ hσ hdeg ht hαt hαC
    have hKne : ρ.ker ⊓ σ.ker ≠ ⊥ := fun h => by
      rw [h, Subgroup.mem_bot] at hker
      exact hne1 ht hker
    have huK := hnormal _ inferInstance hKne
    have hsquares : ∀ c ∈ W, c⁻¹ * c⁻¹ ∈ ρ.ker ⊓ σ.ker := by
      intro c hc
      have h : c⁻¹ * c⁻¹ = (c⁻¹ * u⁻¹ * c) * u := by
        calc c⁻¹ * c⁻¹ = c⁻¹ * (u⁻¹ * c * u) := by rw [hinvert c hc]
          _ = (c⁻¹ * u⁻¹ * c) * u := by group
      rw [h]
      exact Subgroup.mul_mem _
        (Subgroup.Normal.conj_mem' inferInstance _ (Subgroup.inv_mem _ huK) c) huK
    have hWK : ∀ w ∈ W, w ∈ ρ.ker ⊓ σ.ker := by
      intro w hw
      obtain ⟨v, hv, hvv⟩ := exists_mul_self_eq_of_odd hWodd (W.inv_mem hw)
      have hwv : w = v⁻¹ * v⁻¹ := by rw [← mul_inv_rev, hvv, inv_inv]
      rw [hwv]
      exact hsquares v hv
    obtain ⟨hρw, hσw⟩ := Subgroup.mem_inf.mp (hWK w₀ hw₀W)
    apply hw₀
    have hρ1 : ρ.character w₀ = ρ.character 1 := by
      change LinearMap.trace ℂ V (ρ w₀) = LinearMap.trace ℂ V (ρ 1)
      rw [MonoidHom.mem_ker.mp hρw, map_one ρ]
    have hσ1 : σ.character w₀ = σ.character 1 := by
      change LinearMap.trace ℂ U (σ w₀) = LinearMap.trace ℂ U (σ 1)
      rw [MonoidHom.mem_ker.mp hσw, map_one σ]
    rw [hρ1, hσ1, hdeg]
    ring
  refine ⟨hfusion, ConjClasses.mk u, ⟨u, hu, rfl⟩, ?_⟩
  rintro c ⟨t, ht, rfl⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hfusion t ht)

end CFSG.DihedralTIFusion

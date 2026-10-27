module

public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
public import CFSG.CharacterTheory.Semidihedral.Local.PowerFusionTransfer
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem image_quarter_isConj_inv (n : ℕ) (hn : 4 ≤ n) {S : Type*} [Group S]
    (f : SemidihedralGroup n ≃* S) :
    f (s n) * f (r n) ^ (2 ^ (n - 1) / 4) * (f (s n))⁻¹ = (f (r n) ^ (2 ^ (n - 1) / 4))⁻¹ := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  rw [image_quarter_eq hn f, s_eq_element n hn3, ← map_inv, ← map_mul, ← map_mul, ← map_inv,
    conjugate_rotation_by_reflection, element_rotation_inv, twist_mul_quarter hn]

theorem mem_dihedral_of_sq_eq_one (n : ℕ) (hn : 4 ≤ n) {S : Type*} [Group S]
    (f : SemidihedralGroup n ≃* S) (u : S) (hu : u ^ 2 = 1) :
    u ∈ Subgroup.closure {f (r n) ^ 2, f (s n)} := by
  by_cases h1 : u = 1
  · rw [h1]
    exact Subgroup.one_mem _
  · exact supplied_involution_in_dihedral n hn f u (orderOf_eq_prime hu h1)

theorem semidihedral_derived_order_four_conjugate [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let m := 2 ^ (n - 1)
    let v : G := ((r ^ (m / 4) : S) : G)
    orderOf v = 4 ∧
    (∀ t : G, t ∈ commutator G → orderOf t = 4 → IsConj t v) ∧
    (commutator G = ⊤ → ∀ t : G, orderOf t = 4 ↔ IsConj t v) := by
  intro r m v
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  set D : Subgroup S := Subgroup.closure {f (CFSG.Semidihedral.r n) ^ 2, f (s n)} with hDdef
  have hDidx : D.index = 2 := (supplied_index_two n hn f D).mpr (Or.inr (Or.inl rfl))
  have : D.Normal := Subgroup.normal_of_index_eq_two hDidx
  have : IsCyclic (S ⧸ D) := isCyclic_of_prime_card (p := 2) hDidx
  have : IsMulCommutative (S ⧸ D) := IsCyclic.isMulCommutative
  have hv4 : orderOf v = 4 := by
    change orderOf ((f (CFSG.Semidihedral.r n) ^ (2 ^ (n - 1) / 4) : S) : G) = 4
    rw [Subgroup.orderOf_coe, image_quarter_eq hn f, equiv_orderOf, rotation_order_four_iff n hn]
    exact Or.inl rfl
  have hvinv : IsConj v⁻¹ v := by
    refine isConj_iff.mpr ⟨((f (s n) : S) : G), ?_⟩
    have h := congrArg Subtype.val (image_quarter_isConj_inv n hn f)
    change ((f (s n) : S) : G) * v * ((f (s n) : S) : G)⁻¹ = v⁻¹ at h
    calc ((f (s n) : S) : G) * v⁻¹ * ((f (s n) : S) : G)⁻¹ =
        (((f (s n) : S) : G) * v * ((f (s n) : S) : G)⁻¹)⁻¹ := by group
      _ = v := by rw [h, inv_inv]
  have hmain : ∀ t : G, t ∈ commutator G → orderOf t = 4 → IsConj t v := by
    intro t htD ht4
    have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ht4]; norm_num)
    obtain ⟨y, hty⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow S t hpt
    have hy4 : orderOf y = 4 := by
      rw [← Subgroup.orderOf_coe, ← conjugate_orderOf_eq hty, ht4]
    have hyG : (y : G) ∈ commutator G := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hty
      rw [← hc]
      exact Subgroup.Normal.conj_mem inferInstance t htD c
    have hexists : ∃ (g : G) (h : g⁻¹ * (y : G) * g ∈ (S : Subgroup G)),
        (⟨g⁻¹ * (y : G) * g, h⟩ : S) ∈ D := by
      by_contra hnone
      have hnone' : ∀ (g : G) (h : g⁻¹ * (y : G) * g ∈ (S : Subgroup G)),
          (⟨g⁻¹ * (y : G) * g, h⟩ : S) ∉ D := fun g h hD => hnone ⟨g, h, hD⟩
      have hyD : y ∉ D := by
        have h := hnone' 1 (by simp only [inv_one, one_mul, mul_one]; exact y.2)
        simpa only [inv_one, one_mul, mul_one] using h
      have hsq : ∀ u : S, u ^ 2 = 1 → u ∈ D := mem_dihedral_of_sq_eq_one n hn f
      have hy2 : y ^ 4 = 1 := by rw [← hy4, pow_orderOf_eq_one]
      have hfus : ∀ (k : ℕ) (g : G) (h : g⁻¹ * (y : G) ^ k * g ∈ (S : Subgroup G)),
          (QuotientGroup.mk' D ⟨g⁻¹ * (y : G) ^ k * g, h⟩ : S ⧸ D) =
            QuotientGroup.mk' D (y ^ k) := by
        intro k g h
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          Subgroup.mul_mem_iff_of_index_two hDidx, inv_mem_iff]
        have hk : y ^ k = y ^ (k % 4) := by rw [← hy4, pow_mod_orderOf]
        have hk' : (y : G) ^ k = ((y ^ (k % 4) : S) : G) := by rw [← hk, Subgroup.coe_pow]
        have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
        have hconjsq : ∀ (u : S) (hu : g⁻¹ * (u : G) * g ∈ (S : Subgroup G)), u ^ 2 = 1 →
            (⟨g⁻¹ * (u : G) * g, hu⟩ : S) ∈ D := by
          intro u hu hu2
          apply hsq
          apply Subtype.ext
          change (g⁻¹ * (u : G) * g) ^ 2 = 1
          rw [sq, show g⁻¹ * (u : G) * g * (g⁻¹ * (u : G) * g) = g⁻¹ * ((u : G) * u) * g by
            group, ← sq, ← Subgroup.coe_pow, hu2, Subgroup.coe_one, mul_one, inv_mul_cancel]
        have hcongr : ∀ (a b : G) (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G)),
            a = b → ((⟨a, ha⟩ : S) ∈ D ↔ (⟨b, hb⟩ : S) ∈ D) := by
          rintro a b ha hb rfl
          exact Iff.rfl
        rw [hk]
        interval_cases h4 : k % 4
        · rw [pow_zero]
          simp only [hk', pow_zero, Subgroup.coe_one, mul_one, inv_mul_cancel]
          exact ⟨fun _ => D.one_mem, fun _ => D.one_mem⟩
        · rw [pow_one]
          have hk1 : (y : G) ^ k = (y : G) := by rw [hk', pow_one]
          rw [hcongr _ (g⁻¹ * (y : G) * g) h (by rw [← hk1]; exact h) (by rw [hk1])]
          exact ⟨fun h' => absurd h' (hnone' g _), fun h' => absurd h' hyD⟩
        · have hy22 : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul, hy2]
          have hk2 : (y : G) ^ k = ((y ^ 2 : S) : G) := hk'
          rw [hcongr _ (g⁻¹ * ((y ^ 2 : S) : G) * g) h (by rw [← hk2]; exact h) (by rw [hk2])]
          exact ⟨fun _ => hsq _ hy22, fun _ => hconjsq _ _ hy22⟩
        · have hy3 : y ^ 3 = y⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy2]
          have hk3 : (y : G) ^ k = (y : G)⁻¹ := by rw [hk', hy3, Subgroup.coe_inv]
          have hmem : g⁻¹ * (y : G)⁻¹ * g ∈ (S : Subgroup G) := by rw [← hk3]; exact h
          rw [hy3, hcongr _ (g⁻¹ * (y : G)⁻¹ * g) h hmem (by rw [hk3]), inv_mem_iff]
          constructor
          · intro h'
            have hinv : (⟨g⁻¹ * (y : G)⁻¹ * g, hmem⟩ : S)⁻¹ ∈ D := D.inv_mem h'
            have hinv' : (⟨g⁻¹ * (y : G)⁻¹ * g, hmem⟩ : S)⁻¹ =
                ⟨g⁻¹ * (y : G) * g, by
                  have h' := (S : Subgroup G).inv_mem hmem
                  simp only [mul_inv_rev, inv_inv, mul_assoc] at h' ⊢
                  exact h'⟩ := by
              apply Subtype.ext
              change (g⁻¹ * (y : G)⁻¹ * g)⁻¹ = g⁻¹ * (y : G) * g
              group
            exact absurd (hinv' ▸ hinv) (hnone' g _)
          · intro h'
            exact absurd h' hyD
      obtain ⟨-, hTy, -⟩ := power_fusion_transfer_detection S D y hyD hfus
      exact hTy (Abelianization.commutator_subset_ker _ hyG)
    obtain ⟨g, hgS, hgD⟩ := hexists
    have hconj : IsConj (y : G) (g⁻¹ * (y : G) * g) :=
      isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
    have hw4 : orderOf (⟨g⁻¹ * (y : G) * g, hgS⟩ : S) = 4 := by
      rw [Subgroup.orderOf_mk, ← conjugate_orderOf_eq hconj, Subgroup.orderOf_coe, hy4]
    rcases (supplied_dihedral_order_four n hn f _ hgD).mp hw4 with hw | hw
    · refine hty.trans (hconj.trans ?_)
      rw [show g⁻¹ * (y : G) * g = ((⟨g⁻¹ * (y : G) * g, hgS⟩ : S) : G) from rfl, hw]
      exact IsConj.refl _
    · refine hty.trans (hconj.trans ?_)
      rw [show g⁻¹ * (y : G) * g = ((⟨g⁻¹ * (y : G) * g, hgS⟩ : S) : G) from rfl, hw,
        zpow_neg, zpow_natCast, Subgroup.coe_inv]
      exact hvinv
  refine ⟨hv4, hmain, fun hperf t => ⟨fun ht => hmain t (hperf ▸ Subgroup.mem_top t) ht,
    fun h => (conjugate_orderOf_eq h).trans hv4⟩⟩

end CFSG.Semidihedral.Local

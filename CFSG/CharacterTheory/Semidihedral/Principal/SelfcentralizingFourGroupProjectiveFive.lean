module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoA5
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

theorem simple_selfcentralizing_four_group_involution_centralizer_forces_projective_five
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hS : IsKleinFour (S : Subgroup G)) (t : G) (htS : t ∈ (S : Subgroup G))
    (ht1 : t ≠ 1) (hC : Subgroup.centralizer {t} = (S : Subgroup G)) :
    Nat.card G = 60 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 5 1 := by
  have hcomm : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · have hc := (commutator_eq_bot_iff G).mp h
      obtain ⟨x, y, hxy⟩ := hnonab
      exact (hxy (hc.is_comm.comm x y)).elim
    · exact h
  have hScomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_exponent_two hS.exponent_two ⟨x, hx⟩ ⟨y, hy⟩)
  have hSsq : ∀ x ∈ (S : Subgroup G), x ^ 2 = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (S : Subgroup G))
    rw [hS.exponent_two] at h
    exact congrArg Subtype.val h
  have ht2 : t ^ 2 = 1 := hSsq t htS
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hzt : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hto]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h2 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hzcard : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hto]
  have hzS : Subgroup.zpowers t ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr htS
  obtain ⟨s, hsS, hsz⟩ : ∃ s ∈ (S : Subgroup G), s ∉ Subgroup.zpowers t := by
    by_contra! hall
    have hle : (S : Subgroup G) ≤ Subgroup.zpowers t := fun x hx => hall x hx
    have h := Subgroup.card_le_of_le hle
    rw [hzcard, hS.card_four] at h
    norm_num at h
  have hs1 : s ≠ 1 := fun h => hsz (h ▸ Subgroup.one_mem _)
  have hs2 : s ^ 2 = 1 := hSsq s hsS
  have hjoin : (S : Subgroup G) = Subgroup.zpowers t ⊔ Subgroup.zpowers s := by
    have hle : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ (S : Subgroup G) :=
      sup_le hzS (Subgroup.zpowers_le.mpr hsS)
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hS.card_four]
    have hdvd : Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) ∣ 4 :=
      hS.card_four ▸ Subgroup.card_dvd_of_le hle
    have h2 : 2 ∣ Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) :=
      hzcard ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) ≠ 2 := by
      intro h
      have heq : Subgroup.zpowers t = Subgroup.zpowers t ⊔ Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hzcard])
      exact hsz (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) <;> omega
  have hdisj : ∀ g : G, g ∉ (S : Subgroup G) →
      Disjoint (Subgroup.zpowers t) ((Subgroup.zpowers t).conjBy g) := by
    intro g hg
    rw [Subgroup.disjoint_def]
    intro x hx hxg
    rcases hzt x hx with hx1 | hxt
    · exact hx1
    · exfalso
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      rw [hxt] at hyx
      rcases hzt y hy with hy1 | hyt
      · apply ht1
        rw [← hyx, hy1]
        group
      · apply hg
        rw [← hC, Subgroup.mem_centralizer_singleton_iff]
        rw [hyt] at hyx
        calc g * t = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [hyx]
  have hinv : ∀ u : G, BenderSuzuki.PFAppendixIII.IsInvolution u → ∃ g : G, g * u * g⁻¹ = t := by
    intro u hu
    have hD : Nonempty (DihedralGroup 2 ≃* (S : Subgroup G)) := IsKleinFour.nonempty_mulEquiv
    obtain ⟨-, -, -, -, hall⟩ := dihedral_derived_involutions_conjugate S (le_refl 2) hD
    exact isConj_iff.mp (hall hcomm u t (orderOf_eq_prime hu.2 hu.1) hto)
  let h : CFSG.GorensteinWalter.BrauerSuzukiWallHypotheses G :=
    { t := t
      K := Subgroup.zpowers t
      H := (S : Subgroup G)
      s := s
      t_involution := ⟨ht1, ht2⟩
      t_mem_K := Subgroup.mem_zpowers t
      H_eq_centralizer := hC.symm
      K_commutative := inferInstance
      s_involution := ⟨hs1, hs2⟩
      s_not_mem_K := hsz
      H_eq_join := hjoin
      fixed_subgroup_eq := by
        refine inf_eq_left.mpr (Subgroup.zpowers_le.mpr ?_)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hScomm t htS s hsS
      s_inverts_K := by
        intro x hx
        have hxS := hzS hx
        rw [hScomm s hsS x hxS, mul_assoc, mul_inv_cancel, mul_one]
        rw [eq_inv_iff_mul_eq_one, ← sq]
        exact hSsq x hxS
      conjugate_disjoint := hdisj
      involutions_conjugate := hinv }
  have hk : Nat.card h.K = 2 := hzcard
  have hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤ := by
    intro htop
    have hn : (S : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S : Subgroup G) with hb | ht
    · apply ht1
      rw [← Subgroup.mem_bot, ← hb]
      exact htS
    · obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      exact hScomm a (ht ▸ Subgroup.mem_top a) b (ht ▸ Subgroup.mem_top b)
  obtain ⟨e⟩ := h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hk hNne
  have h60 : Nat.card G = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨h60, ⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact ⟨e.trans e5.symm⟩

end CFSG.Semidihedral.Principal

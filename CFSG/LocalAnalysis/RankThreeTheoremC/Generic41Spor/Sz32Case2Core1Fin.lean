module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

section

variable {Y : Type} [Group Y] [Finite Y]

theorem szh1_exists_pow_coprime {G : Type} [Group G] [Finite G] (g : G) :
    ∃ a : ℕ, Nat.Coprime (orderOf (g ^ 5 ^ a)) 5 := by
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 5 (by norm_num)
  refine ⟨a, ?_⟩
  have hdvd : orderOf (g ^ 5 ^ a) ∣ b := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hab]
    exact pow_orderOf_eq_one g
  exact Nat.Coprime.coprime_dvd_left hdvd
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hb).symm

theorem szh1_index_pow {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (hK : ∀ g : G, Nat.Coprime (orderOf g) 5 → g ∈ K) : ∃ k : ℕ, K.index = 5 ^ k := by
  have hp : IsPGroup 5 (G ⧸ K) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨a, ha⟩ := szh1_exists_pow_coprime g
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hK _ ha
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [Subgroup.index_eq_card]; exact hn⟩

theorem szh1_commute_aux {Q : Type} [Group Q] {a b : Q} (hab : Commute b a) (i j : ℤ) :
    Commute (a ^ i) (a ^ j) ∧ Commute (a ^ i) (b * a ^ j) ∧ Commute (b * a ^ i) (a ^ j) ∧
      Commute (b * a ^ i) (b * a ^ j) := by
  have h1 : Commute (a ^ i) (a ^ j) := (Commute.refl a).zpow_zpow i j
  have h2 : Commute (a ^ i) b := (hab.symm).zpow_left i
  have h3 : Commute b (a ^ j) := hab.zpow_right j
  refine ⟨h1, h2.mul_right h1, h3.mul_left h1, ?_⟩
  exact ((Commute.refl b).mul_left h2).mul_right (h3.mul_left h1)

theorem szh1_exists_sq_normal {Y Q : Type} [Group Y] [Group Q] (π : Y →* Q)
    (hc : ∀ g g' : Y, Commute (π g) (π g')) :
    ∃ M : Subgroup Y, M.Normal ∧ ∀ g, g ∈ M ↔ π g ^ 2 = 1 := by
  refine ⟨{ carrier := {g | π g ^ 2 = 1}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ⟨?_⟩, fun g => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, (hc a b).mul_pow, ha, hb, one_mul]
  · simp
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, inv_pow, ha, inv_one]
  · intro n hn g
    have hn' : π n ^ 2 = 1 := hn
    show π (g * n * g⁻¹) ^ 2 = 1
    rw [map_mul, map_mul, map_inv, conj_pow, hn']
    simp

theorem szh1_final_contra
    (hperf : ∀ N : Subgroup Y, N.Normal → (∃ k : ℕ, N.index = 5 ^ k) → N = ⊤)
    {H W : Subgroup Y} [H.Normal] [W.Normal] (hWH : W ≤ H)
    (hW5 : ∀ g ∈ H, Nat.Coprime (orderOf g) 5 → g ∈ W)
    {t y : Y} (ht2 : t * t ∈ H) (htY : ∀ g : Y, g ∈ H ∨ t⁻¹ * g ∈ H)
    (hy : y ∈ H) (y5 : y ^ 5 = 1) (hyW : y ∉ W) (hH : H = W ⊔ Subgroup.zpowers y)
    (hcomm : t * y * t⁻¹ * y⁻¹ ∈ W) : False := by
  let π : Y →* Y ⧸ W := QuotientGroup.mk' W
  have hπ1 : ∀ g : Y, π g = 1 ↔ g ∈ W := fun g => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hHmap : ∀ h ∈ H, ∃ j : ℤ, π h = π y ^ j := by
    intro h hh
    have h1 : π h ∈ H.map π := Subgroup.mem_map_of_mem π hh
    have h2 : H.map π = Subgroup.zpowers (π y) := by
      rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers]
      have : W.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [this, bot_sup_eq]
    rw [h2] at h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact ⟨j, hj.symm⟩
  have hty : Commute (π t) (π y) := by
    have h1 : π (t * y * t⁻¹ * y⁻¹) = 1 := (hπ1 _).2 hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_commute.1 h1
  have hall : ∀ g : Y, ∃ j : ℤ, π g = π y ^ j ∨ π g = π t * π y ^ j := by
    intro g
    rcases htY g with hg | hg
    · obtain ⟨j, hj⟩ := hHmap g hg
      exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := hHmap _ hg
      refine ⟨j, Or.inr ?_⟩
      rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul] at hj
      exact hj
  have hcomm_all : ∀ g g' : Y, Commute (π g) (π g') := by
    intro g g'
    obtain ⟨i, hi⟩ := hall g
    obtain ⟨j, hj⟩ := hall g'
    obtain ⟨c1, c2, c3, c4⟩ := szh1_commute_aux hty i j
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj]
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  obtain ⟨M, hMn, hM⟩ := szh1_exists_sq_normal π hcomm_all
  have hMgen : ∀ g : Y, Nat.Coprime (orderOf g) 5 → g ∈ M := by
    intro g hg
    rw [hM]
    rcases htY g with hgH | hgH
    · have hgW : g ∈ W := hW5 g hgH hg
      rw [(hπ1 g).2 hgW]
      exact one_pow 2
    · have h1 : g * g ∈ H := by
        have e : g * g = (t * (t⁻¹ * g) * t⁻¹) * (t * t) * (t⁻¹ * g) := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hgH t) ht2) hgH
      have h2 : Nat.Coprime (orderOf (g * g)) 5 := by
        refine Nat.Coprime.coprime_dvd_left ?_ hg
        rw [← sq]
        exact orderOf_pow_dvd 2
      have hgg : g * g ∈ W := hW5 _ h1 h2
      rw [sq, ← map_mul]
      exact (hπ1 _).2 hgg
  have hNM : Subgroup.normalClosure {g : Y | Nat.Coprime (orderOf g) 5} ≤ M :=
    Subgroup.normalClosure_le_normal (fun g hg => hMgen g hg)
  have hNtop : Subgroup.normalClosure {g : Y | Nat.Coprime (orderOf g) 5} = ⊤ := by
    apply hperf _ inferInstance
    apply szh1_index_pow
    intro g hg
    exact Subgroup.subset_normalClosure hg
  have hyM : y ∈ M := hNM (hNtop ▸ Subgroup.mem_top y)
  rw [hM] at hyM
  have h5 : π y ^ 5 = 1 := by rw [← map_pow, y5, map_one]
  have hy1 : π y = 1 := by
    have e : π y = (π y ^ 5) * ((π y ^ 2)⁻¹) ^ 2 := by group
    rw [e, h5, hyM]
    simp
  exact hyW ((hπ1 y).1 hy1)

theorem szh1_H_eq_sup {H W : Subgroup Y} [W.Normal] (hWH : W ≤ H)
    (hW5 : ∀ g ∈ H, Nat.Coprime (orderOf g) 5 → g ∈ W)
    (S : Sylow 5 Y) (hSH : (S : Subgroup Y) ≤ H) : H = (S : Subgroup Y) ⊔ W := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hW : ∃ k : ℕ, W.relIndex H = 5 ^ k := by
    apply szh1_index_pow (G := H) (W.subgroupOf H)
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hW5 g g.2
    rwa [Subgroup.orderOf_coe]
  obtain ⟨k, hk⟩ := hW
  have hXH : (S : Subgroup Y) ⊔ W ≤ H := sup_le hSH hWH
  have h1 : ((S : Subgroup Y) ⊔ W).relIndex H ∣ W.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : ((S : Subgroup Y) ⊔ W).relIndex H ∣ (S : Subgroup Y).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have h3 : ¬ 5 ∣ (S : Subgroup Y).relIndex H := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSH))
  rw [hk] at h1
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h1
  have hj0 : j = 0 := by
    by_contra hne
    apply h3
    refine dvd_trans ?_ h2
    rw [hjeq]
    exact dvd_pow_self 5 hne
  have hone : ((S : Subgroup Y) ⊔ W).relIndex H = 1 := by rw [hjeq, hj0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hXH

end

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

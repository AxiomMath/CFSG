module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Main

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Product

variable {G : Type*} [Group G]

theorem centreTwo_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : Unc25G2.CentreTwo A) (hB : Unc25G2.CentreTwo B) : Unc25G2.CentreTwo (A ⊔ B) := by
  intro u hu huc
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hu
  have haA : ∀ w ∈ A, w * a = a * w := by
    intro w hw
    have h1 := huc w (Subgroup.mem_sup_left hw)
    have hbw : b * w = w * b := (hc w hw b hb).symm
    have : w * a * b = a * w * b := by
      calc w * a * b = w * (a * b) := by rw [mul_assoc]
        _ = (a * b) * w := h1
        _ = a * (b * w) := by rw [mul_assoc]
        _ = a * (w * b) := by rw [hbw]
        _ = a * w * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hbB : ∀ w ∈ B, w * b = b * w := by
    intro w hw
    have h1 := huc w (Subgroup.mem_sup_right hw)
    have haw : a * w = w * a := hc a ha w hw
    have : a * (w * b) = a * (b * w) := by
      calc a * (w * b) = (a * w) * b := by rw [mul_assoc]
        _ = (w * a) * b := by rw [haw]
        _ = w * (a * b) := by rw [mul_assoc]
        _ = (a * b) * w := h1
        _ = a * (b * w) := by rw [mul_assoc]
    exact mul_left_cancel this
  obtain ⟨i, hi⟩ := hA a ha haA
  obtain ⟨j, hj⟩ := hB b hb hbB
  exact Unc25G2.exists_pow_two_pow_eq_one_mul (hc a ha b hb) hi hj

end Product

section Inner

variable {G : Type} [Group G]

theorem inducesInner_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {z : G} (hA : Ch1.InducesInner z A) (hB : Ch1.InducesInner z B) :
    Ch1.InducesInner z (A ⊔ B) := by
  obtain ⟨l, hl, hlact⟩ := hA
  obtain ⟨l', hl', hlact'⟩ := hB
  refine ⟨l * l', Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hl'), ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hx
  have hA' : z⁻¹ * a * z = (l * l')⁻¹ * a * (l * l') := by
    rw [hlact a ha]
    have h1 : l' * (l⁻¹ * a * l) = (l⁻¹ * a * l) * l' :=
      (hc _ (A.mul_mem (A.mul_mem (A.inv_mem hl) ha) hl) _ hl').symm
    calc l⁻¹ * a * l = l'⁻¹ * (l' * (l⁻¹ * a * l)) := by group
      _ = l'⁻¹ * ((l⁻¹ * a * l) * l') := by rw [h1]
      _ = (l * l')⁻¹ * a * (l * l') := by group
  have hB' : z⁻¹ * b * z = (l * l')⁻¹ * b * (l * l') := by
    rw [hlact' b hb]
    have h1 : l * b = b * l := hc l hl b hb
    have h2 : l⁻¹ * b * l = b := by
      calc l⁻¹ * b * l = l⁻¹ * (b * l) := by group
        _ = l⁻¹ * (l * b) := by rw [← h1]
        _ = b := by group
    calc l'⁻¹ * b * l' = l'⁻¹ * (l⁻¹ * b * l) * l' := by rw [h2]
      _ = (l * l')⁻¹ * b * (l * l') := by group
  calc z⁻¹ * (a * b) * z = (z⁻¹ * a * z) * (z⁻¹ * b * z) := by group
    _ = ((l * l')⁻¹ * a * (l * l')) * ((l * l')⁻¹ * b * (l * l')) := by rw [hA', hB']
    _ = (l * l')⁻¹ * (a * b) * (l * l') := by group

end Inner

section Conj

variable {G : Type*} [Group G]

theorem conjugate_le_sup {K S : Subgroup G} {s : G} (hs : s ∈ S) :
    CFSG.conjugate K s ≤ K ⊔ S := by
  intro x hx
  have hx' : s * x * s⁻¹ ∈ K := BenderBranch.mem_conjugate_iff.mp hx
  have h : x = s⁻¹ * (s * x * s⁻¹) * s := by group
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (S.inv_mem hs))
    (Subgroup.mem_sup_left hx')) (Subgroup.mem_sup_right hs)

end Conj

section Rank

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem false_of_three_conjugates (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) {g₁ g₂ : G} (hg₁ : g₁ ∈ H) (hg₂ : g₂ ∈ H)
    (h₁ : CFSG.conjugate K g₁ ≠ K) (h₂ : CFSG.conjugate K g₂ ≠ K)
    (h₁₂ : CFSG.conjugate K g₁ ≠ CFSG.conjugate K g₂) : False := by
  have hK₁ : IsComponentIn (CFSG.conjugate K g₁) H := Unc25G2.isComponentIn_conjugate hK hg₁
  have hK₂ : IsComponentIn (CFSG.conjugate K g₂) H := Unc25G2.isComponentIn_conjugate hK hg₂
  have c₁ : ⁅K, CFSG.conjugate K g₁⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hK hK₁).resolve_left fun h => h₁ h.symm
  have c₂ : ⁅K, CFSG.conjugate K g₂⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hK hK₂).resolve_left fun h => h₂ h.symm
  have c₁₂ : ⁅CFSG.conjugate K g₁, CFSG.conjugate K g₂⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hK₁ hK₂).resolve_left h₁₂
  obtain ⟨p, hp, hp2, hpd⟩ := Unc25G2.exists_odd_prime_dvd_card hK
  have hd₁ : p ∣ Nat.card (CFSG.conjugate K g₁) := by rwa [BenderBranch.card_conjugate]
  have hd₂ : p ∣ Nat.card (CFSG.conjugate K g₂) := by rwa [BenderBranch.card_conjugate]
  have hcen₀ : Unc25G2.CentreTwo K := ht.centreTwo hs hK (hinn K hK)
  have hcen₁ : Unc25G2.CentreTwo (CFSG.conjugate K g₁) := ht.centreTwo hs hK₁ (hinn _ hK₁)
  have hZ₀ : ∀ x ∈ K, (∀ y ∈ K, y * x = x * y) → x ^ p = 1 → x = 1 := by
    intro x hx hxc hxp
    obtain ⟨k, hk⟩ := hcen₀ x hx hxc
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
  have hZ₁ : ∀ x ∈ CFSG.conjugate K g₁, (∀ y ∈ CFSG.conjugate K g₁, y * x = x * y) →
      x ^ p = 1 → x = 1 := by
    intro x hx hxc hxp
    obtain ⟨k, hk⟩ := hcen₁ x hx hxc
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
  obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_cube_of_commuting hp c₁ c₂ c₁₂
    hZ₀ hZ₁ hpd hd₁ hd₂
  have hEH : E ≤ H := hEle.trans (sup_le (sup_le hK.1 hK₁.1) hK₂.1)
  exact Unc25G2.false_of_isElemAbelian_card_cube hs.setting.qtke.2.2 ht.gamma0.isGamma.1 hEH hp
    hp2 hE hEcard

theorem conjugate_dichotomy (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) {g₀ : G} (hg₀ : g₀ ∈ H) (h₀ : CFSG.conjugate K g₀ ≠ K) :
    ∀ g ∈ H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K g₀ := by
  intro g hg
  by_cases h1 : CFSG.conjugate K g = K
  · exact Or.inl h1
  · by_cases h2 : CFSG.conjugate K g = CFSG.conjugate K g₀
    · exact Or.inr h2
    · exact (false_of_three_conjugates hs ht hinn hK hg hg₀ h1 h₀ h2).elim

theorem exists_mem_conjugate_ne (ht : Tuple25 T M H S z) {K : Subgroup G} {g₀ : G} (hg₀ : g₀ ∈ H)
    (h₀ : CFSG.conjugate K g₀ ≠ K)
    (hd : ∀ g ∈ H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K g₀) :
    ∃ s ∈ S, CFSG.conjugate K s ≠ K := by
  by_contra hcon
  push Not at hcon
  set N' : Subgroup H := (Subgroup.normalizer (K : Set G)).subgroupOf H with hN'
  have hSN : S.subgroupOf H ≤ N' := by
    intro s hs
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp (hcon (s : G) hs)
  have hdvd : N'.index ∣ (S.subgroupOf H).index := Subgroup.index_dvd_of_le hSN
  have hodd : ¬ 2 ∣ N'.index := fun h => ht.sylow.2.2 (h.trans hdvd)
  have hmemN : ∀ b : H, b ∈ N' ↔ CFSG.conjugate K (b : G) = K := fun b =>
    (BenderBranch.conjugate_eq_iff_mem_normalizer (H := K) (g := (b : G))).symm
  have hmemN2 : ∀ b : H, b * ⟨g₀, hg₀⟩ ∈ N' ↔ CFSG.conjugate (CFSG.conjugate K (b : G)) g₀ = K :=
    fun b => by
      rw [hmemN, show ((b * ⟨g₀, hg₀⟩ : H) : G) = (b : G) * g₀ from rfl,
        BenderBranch.conjugate_conjugate]
  have h2 : N'.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g₀, hg₀⟩, fun b => ?_⟩
    rcases hd (b : G) b.2 with hb | hb
    ·
      have hbN : b ∈ N' := (hmemN b).mpr hb
      have hbaN : b * ⟨g₀, hg₀⟩ ∉ N' := by
        rw [hmemN2, hb]
        exact h₀
      exact Or.inr ⟨hbN, hbaN⟩
    ·
      have hbN : b ∉ N' := by
        rw [hmemN, hb]
        exact h₀
      have hbaN : b * ⟨g₀, hg₀⟩ ∈ N' := by
        rw [hmemN2, hb, BenderBranch.conjugate_conjugate]
        rcases hd (g₀ * g₀) (H.mul_mem hg₀ hg₀) with h | h
        · exact h
        · exfalso
          rw [← BenderBranch.conjugate_conjugate] at h
          exact h₀ (BenderBranch.conjugate_inj.mp h)
      exact Or.inl ⟨hbaN, hbN⟩
  exact hodd ⟨1, by omega⟩

end Rank

section Shape

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem dShape (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) :
    conjJoin H K ≤ K ⊔ S ∧ Unc25G2.CentreTwo (conjJoin H K) ∧
      Ch1.InducesInner z (conjJoin H K) := by
  by_cases hall : ∀ g ∈ H, CFSG.conjugate K g = K
  · have hD : conjJoin H K = K := by
      refine le_antisymm (iSup_le fun g => ?_) (le_conjJoin_self H K)
      have := hall (g : G)⁻¹ (H.inv_mem g.2)
      simp only [CFSG.conjugate, inv_inv] at this
      exact this.le
    rw [hD]
    exact ⟨le_sup_left, ht.centreTwo hs hK (hinn K hK), hinn K hK⟩
  · push Not at hall
    obtain ⟨g₀, hg₀, h₀⟩ := hall
    obtain ⟨s, hsS, hs'⟩ := exists_mem_conjugate_ne ht hg₀ h₀
      (conjugate_dichotomy hs ht hinn hK hg₀ h₀)
    have hsH : s ∈ H := ht.le_H hsS
    have hd := conjugate_dichotomy hs ht hinn hK hsH hs'
    have hK'c : IsComponentIn (CFSG.conjugate K s) H := Unc25G2.isComponentIn_conjugate hK hsH
    have hcomm : ⁅K, CFSG.conjugate K s⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hK hK'c).resolve_left fun h => hs' h.symm
    have hc : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K s, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hD : conjJoin H K = K ⊔ CFSG.conjugate K s := by
      refine le_antisymm (iSup_le fun g => ?_) (sup_le (le_conjJoin_self H K) ?_)
      · have := hd (g : G)⁻¹ (H.inv_mem g.2)
        simp only [CFSG.conjugate, inv_inv] at this ⊢
        rcases this with h | h
        · exact h.le.trans le_sup_left
        · exact h.le.trans le_sup_right
      · exact map_conj_le_conjJoin H K ⟨s⁻¹, H.inv_mem hsH⟩
    rw [hD]
    exact ⟨sup_le le_sup_left (conjugate_le_sup hsS),
      centreTwo_sup_of_commute hc (ht.centreTwo hs hK (hinn K hK))
        (ht.centreTwo hs hK'c (hinn _ hK'c)),
      inducesInner_sup_of_commute hc (hinn K hK) (hinn _ hK'c)⟩

end Shape

end CFSG.QuasithinUnique.Fin253

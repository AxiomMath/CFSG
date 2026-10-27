module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23G0
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Local
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Setting
import CFSG.Quasithin.Vol2.Ch5Sec2M23Gamma

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

variable {G : Type} [Group G]

@[expose] def M23Fusion3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      ∀ b x : G, b ∈ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H → x ∈ M ⊓ centralizerModO2 L →
        orderOf b = 3 → orderOf x = 3 → ∃ c : G, c * b * c⁻¹ = x

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_involutions_m23_of_F4
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4)
    (h515 : Stmt5_2_15_F4) {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T) :
    ∃ s t : G, s ∈ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ∧
      s ∉ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H ∧ t ∈ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H ∧
      t ∉ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ∧ s * s = 1 ∧ t * t = 1 ∧
      orderOf (s * t) ≤ 3 := by
  obtain ⟨M2, π, hS⟩ := hset G T M L V H B D L₂ n hyp hM23
  have hα := hM23.1
  obtain ⟨b, s1, s2, hb1, hb2, hs11, hs12, hs22, hs21, hb3, hs1s1, hs2s2, hs1b, hs2b⟩ :=
    exists_elements_of_isAmalgamOfGroup hα
  have hG1M : L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ≤ M :=
    sup_le (sup_le hyp.L_le (inf_le_right.trans hyp.L_le))
      (inf_le_left.trans (hyp.notation59.1.1.trans inf_le_left))
  have hbM : b ∈ M := hG1M hb1

  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hX, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ M ⊓ centralizerModO2 L)
    IsPGroup.of_bot
  obtain ⟨hNM, K, _, _, hK, ⟨Ψ⟩⟩ := h515 G T M L V H B D L₂ n M2 π hyp hM23 hS X hX
  have hXM : X ≤ M := hX.le.trans inf_le_left
  have hXMN : X ≤ M ⊓ Subgroup.normalizer (X : Set G) := le_inf hXM Subgroup.le_normalizer

  have hcardX : Nat.card X ≤ 3 := by
    have h := card_le_three_of_mulEquiv Ψ hK
      (Y := X.subgroupOf (M ⊓ Subgroup.normalizer (X : Set G)))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXMN).mpr inf_le_right)
      (fun y hy => by
        obtain ⟨k, hk⟩ := hX.isPGroup ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
        refine ⟨k, Subtype.ext ?_⟩
        have := congrArg Subtype.val hk
        simpa using this)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXMN).toEquiv] at h
  have hXne : X ≠ ⊥ := by
    intro hXb
    have h1 : Subgroup.normalizer (X : Set G) = ⊤ := by
      rw [hXb]
      exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
    exact ne_top_of_hyp5_0_1 hyp.toHyp5_0_1 (eq_top_iff.mpr (h1 ▸ hNM))
  have hcard3 : Nat.card X = 3 := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hX.isPGroup
    have hne1 : Nat.card X ≠ 1 := fun h1 => hXne (Subgroup.card_eq_one.mp h1)
    have he1 : e ≤ 1 := by
      by_contra hlt
      have h9 : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← he] at h9
      omega
    interval_cases e
    · exact absurd (by rw [he, pow_zero]) hne1
    · rw [he, pow_one]

  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := hcard3 ▸ Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h
  have hXeq : Subgroup.zpowers x = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
      (by rw [hcard3, Nat.card_zpowers, hx3])

  obtain ⟨c, hc⟩ := hfus G T M L V H B D L₂ n hyp hM23 b x hb2 (hX.le hxX) hb3 hx3
  have hconj : ∀ s : G, s * b * s⁻¹ = b⁻¹ → (c * s * c⁻¹) * x * (c * s * c⁻¹)⁻¹ = x⁻¹ := by
    intro s hs
    rw [← hc]
    calc c * s * c⁻¹ * (c * b * c⁻¹) * (c * s * c⁻¹)⁻¹ = c * (s * b * s⁻¹) * c⁻¹ := by group
      _ = (c * b * c⁻¹)⁻¹ := by rw [hs]; group
  have hsq : ∀ s : G, s * s = 1 → (c * s * c⁻¹) * (c * s * c⁻¹) = 1 := by
    intro s hs
    calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = 1 := by rw [hs]; group
  set N := M ⊓ Subgroup.normalizer (X : Set G) with hNdef
  have hmemN : ∀ s : G, s * x * s⁻¹ = x⁻¹ → s ∈ N := by
    intro s hs
    have hsN : s ∈ Subgroup.normalizer (X : Set G) := by
      rw [← hXeq]
      exact mem_normalizer_zpowers_of_conj_eq_inv hs
    exact Subgroup.mem_inf.mpr ⟨hNM hsN, hsN⟩
  have hxN : x ∈ N := hXMN hxX
  have hs1N := hmemN _ (hconj s1 hs1b)
  have hs2N := hmemN _ (hconj s2 hs2b)

  obtain ⟨j, hj⟩ := exists_orderOf_mul_le_three_of_mulEquiv Ψ hK (x := ⟨x, hxN⟩)
    (s := ⟨_, hs1N⟩) (t := ⟨_, hs2N⟩) (by rw [Subgroup.orderOf_mk, hx3])
    (fun h => by
      have hh : (h : G) * x * (h : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp h.2).2 x).mp hxX
      rw [← hXeq] at hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
    (Subtype.ext (hsq s1 hs1s1)) (Subtype.ext (hsq s2 hs2s2)) (Subtype.ext (hconj s1 hs1b))
    (Subtype.ext (hconj s2 hs2b))
  have hj' : orderOf (b ^ j * s1 * s2) ≤ 3 := by
    have e : ((⟨x, hxN⟩ ^ j * ⟨_, hs1N⟩ * ⟨_, hs2N⟩ : ↥N) : G) =
        c * (b ^ j * s1 * s2) * c⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [← hc, conj_pow]
      group
    have hsc : SemiconjBy c (b ^ j * s1 * s2) (c * (b ^ j * s1 * s2) * c⁻¹) := by
      unfold SemiconjBy
      group
    rw [← Subgroup.orderOf_coe, e, ← hsc.orderOf_eq] at hj
    exact hj

  have hbj1 : b ^ j * s1 ∈ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hb1 j) hs11
  have hbj2 : b ^ j * s1 ∉ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H := fun h => hs12 (by
    have h' := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb2 j)) h
    rwa [inv_mul_cancel_left] at h')
  have hbjsq : (b ^ j * s1) * (b ^ j * s1) = 1 := by
    have h1 : s1 * b ^ j * s1⁻¹ = (b ^ j)⁻¹ := by rw [← conj_pow, hs1b, inv_pow]
    calc b ^ j * s1 * (b ^ j * s1) = b ^ j * (s1 * b ^ j * s1⁻¹) * (s1 * s1) := by group
      _ = 1 := by rw [h1, hs1s1]; group
  exact ⟨_, _, hbj1, hbj2, hs22, hs21, hbjsq, hs2s2, hj'⟩

theorem lieModel_m23G0_of_F4
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4) (h515 : Stmt5_2_15_F4)
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) : LieModel ↥(m23G0 M L H B D) .PSL 3 2 2 := by
  obtain ⟨s, t, hs1, hs2, ht2, ht1, hss, htt, hst⟩ :=
    exists_involutions_m23_of_F4 hset hfus h515 hyp hM23
  exact lieModel_sup_of_isAmalgamOfGroup hM23.1 hs1 hs2 ht2 ht1 hss htt hst

end CFSG.Quasithin.H13

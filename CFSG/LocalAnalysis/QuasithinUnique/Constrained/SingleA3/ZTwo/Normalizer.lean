module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Involutions

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c) {z : G} (hd : D8Data R U (conjSubgroup U x) z)

include h hd

theorem conj_zpowers_y : conjSubgroup (zpowers y) x = zpowers (z * y) := by
  unfold conjSubgroup
  rw [MonoidHom.map_zpowers]
  congr 1
  have := h.y_conj hd
  simpa [MulAut.conj_apply] using this

theorem conj_Q : conjSubgroup (U ⊔ zpowers y) x = conjSubgroup U x ⊔ zpowers y := by
  rw [A3Dich.conjSubgroup_sup, h.conj_zpowers_y hd]
  have hz2 : z * z = 1 := by simpa [pow_two] using hd.z_sq
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    exact (conjSubgroup U x ⊔ zpowers y).mul_mem (Subgroup.mem_sup_left hd.z_mem_V)
      (Subgroup.mem_sup_right (mem_zpowers y))
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have e : z * (z * y) = y := by rw [← mul_assoc, hz2, one_mul]
    have : z * (z * y) ∈ conjSubgroup U x ⊔ zpowers (z * y) :=
      (conjSubgroup U x ⊔ zpowers (z * y)).mul_mem (Subgroup.mem_sup_left hd.z_mem_V)
        (Subgroup.mem_sup_right (mem_zpowers _))
    rwa [e] at this

theorem mem_S_or_mul {n : G} (hn : n ∈ T) (hnS : n ∈ normalizer (S : Set G)) :
    n ∈ S ∨ ∃ s ∈ S, n = x * s := by
  have hQS : U ⊔ zpowers y ≤ S := sup_le h.U_le h.zpowers_y_le_S
  have hE : conjSubgroup (U ⊔ zpowers y) n ≤ S := A3Dich.conjSubgroup_le_of_le hQS hnS
  have hcard : Nat.card (conjSubgroup (U ⊔ zpowers y) n) = 8 := by
    rw [A3Dich.card_conjSubgroup, h.card_Q]
  have hexp := exp_conjSubgroup (h.exp_sup_zpowers_y h.U_le h.U_exp) n
  rcases h.eq_Q_or_Q' hd hE hcard hexp with e | e
  · left
    exact h.N_Q n hn (conjSubgroup_eq_iff_mem_normalizer.mp e)
  · right
    rw [← h.conj_Q hd] at e
    have hq : conjSubgroup (U ⊔ zpowers y) (n * x⁻¹) = U ⊔ zpowers y := by
      rw [← conjSubgroup_conjSubgroup, e, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    have hmem : n * x⁻¹ ∈ S := h.N_Q (n * x⁻¹) (T.mul_mem hn (T.inv_mem h.x_mem))
      (conjSubgroup_eq_iff_mem_normalizer.mp hq)
    refine ⟨x⁻¹ * (n * x⁻¹) * x, h.conj_inv_mem hmem, ?_⟩
    group

theorem elem_le_S {E : Subgroup G} (hET : E ≤ T) (hEN : E ≤ normalizer (S : Set G))
    (hE8 : Nat.card E = 8) (hexp : ∀ g ∈ E, g ^ 2 = 1) : E ≤ S := by
  classical
  by_contra hnot
  obtain ⟨e, heE, heS⟩ : ∃ e ∈ E, e ∉ S := by
    by_contra hcon
    exact hnot fun g hg => by_contra fun hgS => hcon ⟨g, hg, hgS⟩
  obtain ⟨s₀, hs₀, hes⟩ := (h.mem_S_or_mul hd (hET heE) (hEN heE)).resolve_left heS
  subst hes
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => comm_of_exp_two hexp ha hb
  have he2 : (x * s₀) ^ 2 = 1 := hexp _ heE
  have hsub : ∀ f ∈ E, f = 1 ∨ f = z ∨ f = x * s₀ ∨ f = x * s₀ * z := by
    intro f hf
    by_cases hfS : f ∈ S
    · have hc : (x * s₀)⁻¹ * f * (x * s₀) = f := conj_eq_of_comm (hEc _ heE f hf)
      rcases h.comm_involution hd hs₀ hfS (hexp f hf) hc with e1 | e1
      · exact Or.inl e1
      · exact Or.inr (Or.inl e1)
    · obtain ⟨s₁, hs₁, hfx⟩ := (h.mem_S_or_mul hd (hET hf) (hEN hf)).resolve_left hfS
      have hef : x * s₀ * f ∈ S := by
        rw [hfx]
        have e1 : x * s₀ * (x * s₁) = x ^ 2 * (x⁻¹ * s₀ * x) * s₁ := by group
        rw [e1]
        exact S.mul_mem (S.mul_mem h.x_sq_mem (h.conj_inv_mem hs₀)) hs₁
      have hmem : x * s₀ * f ∈ E := E.mul_mem heE hf
      have hc : (x * s₀)⁻¹ * (x * s₀ * f) * (x * s₀) = x * s₀ * f :=
        conj_eq_of_comm (hEc _ heE _ hmem)
      rcases h.comm_involution hd hs₀ hef (hexp _ hmem) hc with e1 | e1
      ·
        right; right; left
        have hinv : (x * s₀)⁻¹ = x * s₀ := inv_eq_self_of_sq_eq_one he2
        calc f = (x * s₀)⁻¹ * (x * s₀ * f) := by group
          _ = x * s₀ := by rw [e1, mul_one, hinv]
      · right; right; right
        have hinv : (x * s₀)⁻¹ = x * s₀ := inv_eq_self_of_sq_eq_one he2
        calc f = (x * s₀)⁻¹ * (x * s₀ * f) := by group
          _ = x * s₀ * z := by rw [e1, hinv]
  have hsub' : (E : Set G) ⊆ ↑({1, z, x * s₀, x * s₀ * z} : Finset G) := by
    intro f hf
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hsub f hf
  have hcard4 : Nat.card E ≤ 4 :=
    calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ (↑({1, z, x * s₀, x * s₀ * z} : Finset G) : Set G).ncard := Set.ncard_le_ncard hsub'
      _ = ({1, z, x * s₀, x * s₀ * z} : Finset G).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  omega

omit hd in
theorem S_eq_Q_sup_Q' : S = (U ⊔ zpowers y) ⊔ (conjSubgroup U x ⊔ zpowers y) := by
  apply le_antisymm
  · rw [h.S_eq, h.R_eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_left le_sup_right
  · exact sup_le (sup_le h.U_le h.zpowers_y_le_S) (sup_le h.U'_le h.zpowers_y_le_S)

theorem T_le_normalizer_S : ∀ t ∈ T, t ∈ normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t, htT, htN⟩ := hcon
  have hne : T ⊓ normalizer (S : Set G) ≠ T := by
    intro e
    have : t ∈ T ⊓ normalizer (S : Set G) := by rw [e]; exact htT
    exact htN this.2
  obtain ⟨n, hn, hnM⟩ := exists_mem_inf_normalizer_of_ne (p := 2) h.isPGroup_T inf_le_left hne
  have hSM : S ≤ T ⊓ normalizer (S : Set G) := le_inf h.S_le Subgroup.le_normalizer
  have hnM₀ : conjSubgroup (T ⊓ normalizer (S : Set G)) n = T ⊓ normalizer (S : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hn.2
  have key : ∀ A : Subgroup G, A ≤ S → Nat.card A = 8 → (∀ a ∈ A, a ^ 2 = 1) →
      conjSubgroup A n ≤ S := by
    intro A hAS hA8 hAexp
    have h1 : conjSubgroup A n ≤ T ⊓ normalizer (S : Set G) := by
      rw [← hnM₀]
      exact Subgroup.map_mono (hAS.trans hSM)
    exact h.elem_le_S hd (h1.trans inf_le_left) (h1.trans inf_le_right)
      (by rw [A3Dich.card_conjSubgroup, hA8]) (exp_conjSubgroup hAexp n)
  have hQ := key (U ⊔ zpowers y) (sup_le h.U_le h.zpowers_y_le_S) h.card_Q
    (h.exp_sup_zpowers_y h.U_le h.U_exp)
  have hQ' := key (conjSubgroup U x ⊔ zpowers y) (sup_le h.U'_le h.zpowers_y_le_S) h.card_Q'
    (h.exp_sup_zpowers_y h.U'_le h.U'_exp)
  have hSn : conjSubgroup S n ≤ S := by
    have e1 : conjSubgroup S n = conjSubgroup (U ⊔ zpowers y) n ⊔
        conjSubgroup (conjSubgroup U x ⊔ zpowers y) n := by
      conv_lhs => rw [h.S_eq_Q_sup_Q']
      exact A3Dich.conjSubgroup_sup _ _ _
    rw [e1]
    exact sup_le hQ hQ'
  exact hnM ⟨hn.1, mem_normalizer_of_conjSubgroup_le hSn⟩

theorem T_decomp {t : G} (ht : t ∈ T) : t ∈ S ∨ ∃ s ∈ S, t = x * s :=
  h.mem_S_or_mul hd ht (h.T_le_normalizer_S hd t ht)

theorem T_norm_R : T ≤ normalizer (R : Set G) := by
  intro t ht
  rcases h.T_decomp hd ht with hts | ⟨s, hs, rfl⟩
  · exact h.S_norm_R hts
  · exact (normalizer (R : Set G)).mul_mem h.x_norm_R (h.S_norm_R hs)

theorem relIndex_S_T : S.relIndex T = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, h.x_mem⟩, fun b => ?_⟩
  obtain ⟨b, hb⟩ := b
  rcases h.T_decomp hd hb with hbS | ⟨s, hs, rfl⟩
  · right
    refine ⟨Subgroup.mem_subgroupOf.mpr hbS, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    intro hmem
    apply h.x_not_mem
    have : b⁻¹ * (b * x) ∈ S := S.mul_mem (S.inv_mem hbS) hmem
    simpa using this
  · left
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      show x * s * x ∈ S
      have e : x * s * x = x ^ 2 * (x⁻¹ * s * x) := by group
      rw [e]
      exact S.mul_mem h.x_sq_mem (h.conj_inv_mem hs)
    · rw [Subgroup.mem_subgroupOf]
      intro hmem
      apply h.x_not_mem
      have : (x * s) * s⁻¹ ∈ S := S.mul_mem hmem (S.inv_mem hs)
      simpa using this

theorem relIndex_R_T : R.relIndex T = 4 := by
  have h1 : R.relIndex S = 2 := by
    have := A3Gen.card_eq_card_mul_relIndex' h.R_le
    rw [h.card_S, h.card_R] at this
    omega
  have := Subgroup.relIndex_mul_relIndex R S T h.R_le h.S_le
  rw [h1, h.relIndex_S_T hd] at this
  omega

theorem commutator_T_le_R : ⁅T, T⁆ ≤ R := by
  classical
  have hN : (R.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer (h.T_norm_R hd)
  have hcard : Nat.card (T ⧸ R.subgroupOf T) = 2 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    exact h.relIndex_R_T hd
  have hcomm : IsMulCommutative (T ⧸ R.subgroupOf T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := R.subgroupOf T)).mp hcomm
  rw [commutator_def, Subgroup.commutator_le] at h1
  exact Subgroup.mem_subgroupOf.mp (h1 ⟨a, ha⟩ (Subgroup.mem_top _) ⟨b, hb⟩ (Subgroup.mem_top _))

end ZTwoConfig

end CFSG.QuasithinUnique

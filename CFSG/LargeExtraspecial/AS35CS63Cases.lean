module

public import CFSG.LargeExtraspecial.AS35CHyp
public import CFSG.LargeExtraspecial.AS35CS63Bar
public import CFSG.LargeExtraspecial.AS35CS63Star
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld

namespace S63

variable {X : Type} [Group X]

theorem eq_one_of_mul_self_of_odd [Finite X] {K : Subgroup X} (hodd : Odd (Nat.card K)) {g : X}
    (hg : g ∈ K) (hgg : g * g = 1) : g = 1 := by
  have h1 : orderOf g ∣ Nat.card K := by
    simpa using orderOf_dvd_natCard (⟨g, hg⟩ : K)
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  have hcop : Nat.Coprime (Nat.card K) 2 := Nat.coprime_two_right.mpr hodd
  have h3 : orderOf g ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem false_of_oddCore [Finite X] {ζ : X} (hζ2 : ζ * ζ = 1) {τ : X}
    (hτ : τ ∈ CorB.conjCent ζ) (hne : τ ≠ ζ) {K : Subgroup X}
    (hKU : K ≤ normalClosure ({ζ} : Set X))
    (hKn : (K.subgroupOf (normalClosure ({ζ} : Set X))).Normal) (hodd : Odd (Nat.card K))
    (hU : normalClosure ({ζ} : Set X) = K ⊔ zpowers ζ) : False := by
  have hζU : ζ ∈ normalClosure ({ζ} : Set X) := subset_normalClosure (Set.mem_singleton ζ)
  have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
  have hconj : ∀ k ∈ K, ζ * k * ζ⁻¹ ∈ K := by
    intro k hk
    have h1 := hKn.conj_mem ⟨k, hKU hk⟩ (by rwa [mem_subgroupOf]) ⟨ζ, hζU⟩
    rwa [mem_subgroupOf] at h1
  have hc' : ∀ k ∈ K, ζ * k * ζ ∈ K := fun k hk => by simpa [hζi] using hconj k hk
  have e1 : ∀ u v : X, u * v * ζ = (u * ζ) * (ζ * v * ζ) := fun u v => by
    calc u * v * ζ = u * (ζ * ζ) * v * ζ := by rw [hζ2, mul_one]
      _ = (u * ζ) * (ζ * v * ζ) := by group
  have e2 : ∀ u v : X, u * v = (u * ζ) * (ζ * (v * ζ) * ζ) := fun u v => by
    calc u * v = u * (ζ * ζ) * v * (ζ * ζ) := by rw [hζ2, mul_one, mul_one]
      _ = (u * ζ) * (ζ * (v * ζ) * ζ) := by group
  have e3 : ∀ u : X, ζ * (u * ζ)⁻¹ * ζ = u⁻¹ * ζ := fun u => by
    calc ζ * (u * ζ)⁻¹ * ζ = ζ * ζ⁻¹ * u⁻¹ * ζ := by group
      _ = u⁻¹ * ζ := by group
  let S₀ : Subgroup X :=
    { carrier := {u | u ∈ K ∨ u * ζ ∈ K}
      mul_mem' := by
        rintro u v (hu | hu) (hv | hv)
        · exact Or.inl (mul_mem hu hv)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hu hv)
        · exact Or.inr (by rw [e1]; exact mul_mem hu (hc' v hv))
        · exact Or.inl (by rw [e2]; exact mul_mem hu (hc' _ hv))
      one_mem' := Or.inl K.one_mem
      inv_mem' := by
        rintro u (hu | hu)
        · exact Or.inl (inv_mem hu)
        · exact Or.inr (by rw [← e3]; exact hc' _ (inv_mem hu)) }
  have hle : K ⊔ zpowers ζ ≤ S₀ := by
    refine sup_le (fun k hk => Or.inl hk) ?_
    rw [zpowers_le]
    exact Or.inr (by rw [hζ2]; exact K.one_mem)
  have hτU : τ ∈ normalClosure ({ζ} : Set X) := mem_normalClosure_of_isConj hτ.2
  rw [hU] at hτU
  obtain ⟨k, hk⟩ := isConj_iff.mp hτ.2
  have hττ : τ * τ = 1 := by
    rw [← hk]
    calc k * ζ * k⁻¹ * (k * ζ * k⁻¹) = k * (ζ * ζ) * k⁻¹ := by group
      _ = 1 := by rw [hζ2]; group
  have hζ1 : ζ ≠ 1 := fun h => hne (by rw [← hk, h]; group)
  rcases hle hτU with h | h
  · exact hζ1 (by
      have := eq_one_of_mul_self_of_odd hodd h hττ
      rw [← hk] at this
      calc ζ = k⁻¹ * (k * ζ * k⁻¹) * k := by group
        _ = 1 := by rw [this]; group)
  · apply hne
    have h1 : (τ * ζ) * (τ * ζ) = 1 := by
      calc (τ * ζ) * (τ * ζ) = τ * (ζ * τ) * ζ := by group
        _ = τ * (τ * ζ) * ζ := by rw [← hτ.1]
        _ = (τ * τ) * (ζ * ζ) := by group
        _ = 1 := by rw [hττ, hζ2, one_mul]
    have h2 := eq_one_of_mul_self_of_odd hodd h h1
    calc τ = τ * ζ * ζ⁻¹ := by group
      _ = ζ := by rw [h2, one_mul, hζi]

theorem eq_one_of_mem_ZU {ζ : X} (hζ : ζ ∈ ZU ζ)
    (y : ↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X))) : y = 1 := by
  have hn : (ZU ζ).Normal := ⟨fun n hn g => conj_mem_ZU hn g⟩
  have hle : normalClosure ({ζ} : Set X) ≤ ZU ζ :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr hζ)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨_, hc⟩ := mem_ZU_iff.mp (hle u.2)
  exact hc

theorem not_mem_ZU_of_hyp {ζ : X}
    {D : Set (↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X)))}
    (hH : Timmesfeld.Hyp (↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X)))
      D) : ζ ∉ ZU ζ := by
  intro hζ
  obtain ⟨d, -, e, -, hde⟩ := hH.nondeg
  rw [eq_one_of_mem_ZU hζ (d * e), orderOf_one] at hde
  exact absurd hde (by norm_num)

theorem exists_rootSet_ne [Finite X] {D : Set X} (hD : ∀ d ∈ D, orderOf d = 2) {d : X}
    (hd : d ∈ D) {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card (rootGroup D d) = 2 ^ f) :
    ∃ e ∈ rootSet D d, e ≠ d := by
  by_contra h
  push Not at h
  have hle : rootGroup D d ≤ zpowers d := by
    rw [rootGroup, closure_le]
    intro e he
    rw [h e he]
    exact mem_zpowers d
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers, hD d hd] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

namespace Six

variable {G : Type} [Group G] {S : Setting G} (K : Six S)

theorem zInOTwo_of_elemAb [Finite G]
    (h : ∀ x ∈ normalClosure ({K.zeta} : Set (Cbar K.t)),
      ∀ y ∈ normalClosure ({K.zeta} : Set (Cbar K.t)), x * y = y * x ∧ x * x = 1) :
    S.ZInOTwo K.t := by
  set Ub := normalClosure ({K.zeta} : Set (Cbar K.t)) with hUb
  have hU2 : IsPGroup 2 Ub := by
    intro u
    exact ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, pow_two]
      exact (h u u.2 u u.2).2)⟩
  have hker : IsPGroup 2 (piC K.t).ker := by
    intro u
    refine ⟨1, Subtype.ext ?_⟩
    have h1 := (piC_eq_one_iff K.ht2).mp (MonoidHom.mem_ker.mp u.2)
    rw [pow_one, Subgroup.coe_pow, pow_two]
    apply Subtype.ext
    rcases h1 with h1 | h1 <;> simp only [Subgroup.coe_mul, h1, Subgroup.coe_one, mul_one]
    exact K.ht2
  set P := Ub.comap (piC K.t) with hP
  have hP2 : IsPGroup 2 P := hU2.comap_of_ker_isPGroup _ hker
  set P' := P.map (centralizer ({K.t} : Set G)).subtype with hP'
  refine S.zInOTwo_of_le (P := P') (map_subtype_le P) ?_ (hP2.map _) ?_
  · rintro c hc _ ⟨p, hp, rfl⟩
    refine ⟨⟨c, hc⟩ * p * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    change piC K.t (⟨c, hc⟩ * p * ⟨c, hc⟩⁻¹) ∈ Ub
    rw [map_mul, map_mul, map_inv]
    exact normalClosure_normal.conj_mem _ hp _
  · exact ⟨K.zC, subset_normalClosure (Set.mem_singleton _), rfl⟩

end Six

end S63

end CFSG.LargeExtraspecial

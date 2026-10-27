module

public import CFSG.Open.Catalog
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem wreath_card_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  simp

theorem wreath_zmod_three_cube (z : Multiplicative (ZMod 3)) : z * z * z = 1 := by
  revert z
  decide

theorem wreath_zmod_three_orbit (q x y : Multiplicative (ZMod 3)) (hq : q ≠ 1) :
    y = x ∨ y = q⁻¹ * x ∨ y = q⁻¹ * (q⁻¹ * x) := by
  revert q x y
  decide

theorem wreath_left_mul_of_right_eq_one {D Q : Type*} [Group D] [Group Q] {a b : D ≀ᵣ Q}
    (ha : a.right = 1) : (a * b).left = a.left * b.left := by
  rw [RegularWreathProduct.mul_left, ha]
  simp

theorem wreath_ker_isElemAbelian :
    IsElemAbelian 3 (RegularWreathProduct.rightHom :
      Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_, fun x hx => ?_⟩
  · have ha' : a.right = 1 := ha
    have hb' : b.right = 1 := hb
    refine RegularWreathProduct.ext ?_ ?_
    · rw [wreath_left_mul_of_right_eq_one ha', wreath_left_mul_of_right_eq_one hb']
      exact mul_comm _ _
    · simp [ha', hb']
  · have hx' : x.right = 1 := hx
    have h2 : (x * x).right = 1 := by simp [hx']
    refine RegularWreathProduct.ext ?_ ?_
    · rw [pow_succ, pow_succ, pow_one, wreath_left_mul_of_right_eq_one h2,
        wreath_left_mul_of_right_eq_one hx']
      funext z
      simpa using wreath_zmod_three_cube (x.left z)
    · simp [pow_succ, hx']

theorem wreath_card_ker :
    Nat.card (RegularWreathProduct.rightHom :
      Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker = 27 := by
  have hsurj : Function.Surjective (RegularWreathProduct.rightHom :
      Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)) :=
    fun q => ⟨RegularWreathProduct.inl q, RegularWreathProduct.fun_id q⟩
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [RegularWreathProduct.card, wreath_card_zmod_three] at h
  omega

theorem wreath_left_const_of_commute {g k : W₃} (hg : g.right ≠ 1) (hk : k.right = 1)
    (h : k * g = g * k) (x y : Multiplicative (ZMod 3)) : k.left x = k.left y := by
  have hshift : ∀ z, k.left z = k.left (g.right⁻¹ * z) := by
    intro z
    have hz := congrFun (congrArg RegularWreathProduct.left h) z
    rw [wreath_left_mul_of_right_eq_one hk, RegularWreathProduct.mul_left] at hz
    have hz' : k.left z * g.left z = g.left z * k.left (g.right⁻¹ * z) := hz
    exact mul_right_cancel (hz'.trans (mul_comm _ _))
  rcases wreath_zmod_three_orbit g.right x y hg with rfl | rfl | rfl
  · rfl
  · exact hshift x
  · exact (hshift x).trans (hshift (g.right⁻¹ * x))

theorem wreath_card_le_nine_of_not_le_ker {X : Subgroup (Multiplicative (ZMod 3) ≀ᵣ
      Multiplicative (ZMod 3))}
    (hX : IsMulCommutative X)
    (hXA : ¬ X ≤ (RegularWreathProduct.rightHom : Multiplicative (ZMod 3) ≀ᵣ
      Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker) : Nat.card X ≤ 9 := by
  obtain ⟨g, hgX, hgA⟩ := IsConcreteLE.not_le_iff_exists.mp hXA
  have hg : g.right ≠ 1 := hgA
  let φ : X →* Multiplicative (ZMod 3) := RegularWreathProduct.rightHom.comp X.subtype
  have hinj : Function.Injective (fun k : φ.ker => ((k : X) : W₃).left 1) := by
    intro k₁ k₂ hk
    have hk₁ : ((k₁ : X) : W₃).right = 1 := k₁.2
    have hk₂ : ((k₂ : X) : W₃).right = 1 := k₂.2
    have hc₁ := wreath_left_const_of_commute hg hk₁ (setLike_mul_comm (k₁ : X).2 hgX)
    have hc₂ := wreath_left_const_of_commute hg hk₂ (setLike_mul_comm (k₂ : X).2 hgX)
    refine Subtype.ext (Subtype.ext (RegularWreathProduct.ext ?_ (hk₁.trans hk₂.symm)))
    funext z
    exact (hc₁ z 1).trans (hk.trans (hc₂ 1 z))
  have hker : Nat.card φ.ker ≤ 3 :=
    (Nat.card_le_card_of_injective _ hinj).trans wreath_card_zmod_three.le
  have hrange : Nat.card φ.range ≤ 3 :=
    (Subgroup.card_le_card_group _).trans wreath_card_zmod_three.le
  calc Nat.card X = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hrange

theorem thompsonSubgroup_le_map_ker {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    thompsonSubgroup P ≤ (RegularWreathProduct.rightHom : Multiplicative (ZMod 3) ≀ᵣ
      Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker.map
        (P.subtype.comp e.symm.toMonoidHom) := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  have hιsurj : ∀ b ∈ P, ∃ w, ι w = b := fun b hb => ⟨e ⟨b, hb⟩, by simp [ι]⟩
  let A₀ : Subgroup W₃ := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  have hA₀c : IsMulCommutative A₀ := wreath_ker_isElemAbelian.1
  let A₁ : Subgroup G := A₀.map ι
  have hA₁P : A₁ ≤ P := by
    rintro _ ⟨a, _, rfl⟩
    exact hιP a
  have hA₁c : IsMulCommutative A₁ := Subgroup.map_isMulCommutative A₀ ι
  have hA₁card : Nat.card A₁ = 27 :=
    (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker
  have hcomap_card : ∀ B : Subgroup G, B ≤ P → Nat.card (B.comap ι) = Nat.card B := by
    intro B hB
    have hrange : B ≤ ι.range := fun b hb => hιsurj b (hB hb)
    calc Nat.card (B.comap ι) = Nat.card ((B.comap ι).map ι) :=
          (Subgroup.card_map_of_injective hιinj).symm
      _ = Nat.card B := by rw [Subgroup.map_comap_eq_self hrange]
  have hbound : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ 27 := by
    intro B hBP hB
    have := Subgroup.comap_injective_isMulCommutative B hιinj
    rw [← hcomap_card B hBP]
    by_cases hle : B.comap ι ≤ A₀
    · rw [← wreath_card_ker]
      exact Subgroup.card_le_of_le hle
    · have := wreath_card_le_nine_of_not_le_ker (X := B.comap ι) inferInstance hle
      omega
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  refine iSup_le fun A => iSup_le fun hAP => iSup_le fun hAc => iSup_le fun hAmax => ?_
  have h27 : Nat.card A = 27 :=
    le_antisymm (hbound A hAP hAc) (hA₁card ▸ hAmax A₁ hA₁P hA₁c)
  have := Subgroup.comap_injective_isMulCommutative A hιinj
  have hAle : A.comap ι ≤ A₀ := by
    by_contra hnle
    have := wreath_card_le_nine_of_not_le_ker (X := A.comap ι) inferInstance hnle
    rw [hcomap_card A hAP, h27] at this
    omega
  have hAeq : A.comap ι = A₀ :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hcomap_card A hAP, h27, wreath_card_ker])
  intro a ha
  obtain ⟨w, hw⟩ := hιsurj a (hAP ha)
  have hwA : w ∈ A₀ := by
    rw [← hAeq]
    show ι w ∈ A
    rw [hw]
    exact ha
  exact ⟨w, hwA, hw⟩

theorem exists_orderOf_eq_three_not_mem_thompsonSubgroup {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    ∃ y ∈ P, orderOf y = 3 ∧ y ∉ thompsonSubgroup P := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  let c : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
  have hc1 : c ≠ 1 := by decide
  have hc3 : c ^ 3 = 1 := by decide
  let σ : W₃ := RegularWreathProduct.inl c
  have hσ1 : σ ≠ 1 := fun h => hc1 (by simpa [σ] using congrArg RegularWreathProduct.right h)
  have hσ3 : σ ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  refine ⟨ι σ, (e.symm σ).2, ?_, fun hy => ?_⟩
  · rw [orderOf_injective ι hιinj, orderOf_eq_prime hσ3 hσ1]
  · obtain ⟨a, ha, haσ⟩ := thompsonSubgroup_le_map_ker e hy
    obtain rfl : a = σ := hιinj haσ
    exact hc1 (by simpa [σ] using ha)

theorem three_le_pRank_inf_centralizer_of_mem_thompsonSubgroup {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    {y : G} (hy : y ∈ thompsonSubgroup P) :
    3 ≤ CFSG.Open.pRank 3 (P ⊓ centralizer ({y} : Set G)) := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  let A₀ : Subgroup W₃ := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  have hA₀c : IsMulCommutative A₀ := wreath_ker_isElemAbelian.1
  let A₁ : Subgroup G := A₀.map ι
  have hA₁P : A₁ ≤ P := by
    rintro _ ⟨a, _, rfl⟩
    exact hιP a
  have hA₁c : IsMulCommutative A₁ := Subgroup.map_isMulCommutative A₀ ι
  have hA₁cube : ∀ x ∈ A₁, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, wreath_ker_isElemAbelian.2 a ha, map_one]
  have hA₁card : Nat.card A₁ = 27 :=
    (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker
  have hyA : y ∈ A₁ := thompsonSubgroup_le_map_ker e hy
  have hle : A₁ ≤ P ⊓ centralizer ({y} : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hA₁P ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact setLike_mul_comm ha hyA
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove 3 (by norm_num) _)
    ⟨A₁, hle, ⟨hA₁c, hA₁cube⟩, by rw [hA₁card]; norm_num⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

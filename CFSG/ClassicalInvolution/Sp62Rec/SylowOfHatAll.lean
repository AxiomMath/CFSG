module

public import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHat

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open
open scoped Pointwise


theorem card_sylow_of_hat {G : Type} [Group G] [Finite G] {E B : Subgroup G}
    (φ : ↥B →* ↥Hhat) (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn E).subgroupOf B) (T : Sylow 2 G)
    (hTB : (T : Subgroup G) ≤ B) : Nat.card (T : Subgroup G) = 512 := by
  obtain ⟨T₀, hT₀B, -, hcard, ⟨P₀, hP₀⟩, -⟩ := exists_sylow_of_hat φ hφ hker
  have h1 := Sylow.card_eq_multiplicity (T.subtype hTB)
  have h2 := Sylow.card_eq_multiplicity P₀
  rw [Sylow.coe_subtype] at h1
  rw [hP₀] at h2
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, h1, ← h2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀B).toEquiv, hcard]

theorem exists_conj_of_hat {G : Type} [Group G] [Finite G] {E B : Subgroup G}
    (φ : ↥B →* ↥Hhat) (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn E).subgroupOf B) {T : Subgroup G} (hTB : T ≤ B)
    (hT : Nat.card T = 512) :
    ∃ h : ↥Hhat,
      (T.subgroupOf B).map φ = (S0.subgroupOf Hhat).map (MulAut.conj h).toMonoidHom ∧
      ∃ θ : ↥T ≃* ↥S0,
        (∀ x (hx : x ∈ T) (hxB : x ∈ B), (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) =
          ((h⁻¹ * φ ⟨x, hxB⟩ * h : ↥Hhat) : StatedSp 3 (ZMod 2))) ∧
        ∃ A : Subgroup G, A ≤ T ∧ IsE64 A ∧
          (∀ x (hx : x ∈ T), x ∈ A ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0) ∧
          (A.subgroupOf T).map θ.toMonoidHom = A0.subgroupOf S0 ∧
          ∀ A' : Subgroup G, A' ≤ T → IsE64 A' → A' = A := by
  have hkodd : Odd (Nat.card φ.ker) := by
    rw [hker, ← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.card_dvd_of_le inf_le_left)
  have hcardTB : Nat.card (T.subgroupOf B) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, hT]
  obtain ⟨f₁, hf₁def⟩ : ∃ f : ↥T →* ↥Hhat,
      ∀ x (hx : x ∈ T) (hxB : x ∈ B), f ⟨x, hx⟩ = φ ⟨x, hxB⟩ :=
    ⟨φ.comp (Subgroup.inclusion hTB), fun _ _ _ => rfl⟩
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_one f₁).mpr fun a ha => ?_
    have hcop : Nat.Coprime (Nat.card (T.subgroupOf B)) (Nat.card φ.ker) := by
      rw [hcardTB, show (512 : ℕ) = 2 ^ 9 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hkodd)
    have hdis := Subgroup.disjoint_of_coprime_natCard hcop
    have hmem : (⟨a, hTB a.2⟩ : ↥B) ∈ T.subgroupOf B := a.2
    have hker' : (⟨a, hTB a.2⟩ : ↥B) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact (hf₁def a a.2 (hTB a.2)).symm.trans ha
    have h1 := Subgroup.disjoint_def.mp hdis hmem hker'
    exact Subtype.ext (congrArg (Subtype.val : ↥B → G) h1)
  have hU : (T.subgroupOf B).map φ = f₁.range := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, hf₁def b hb b.2⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨t, hTB t.2⟩, t.2, (hf₁def t t.2 (hTB t.2)).symm⟩
  have hcardU : Nat.card ((T.subgroupOf B).map φ) = 512 := by
    rw [hU, ← hT]
    exact Nat.card_congr (MonoidHom.ofInjective hf₁).toEquiv.symm
  have hcardS : Nat.card (S0.subgroupOf Hhat) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, card_S0]
  haveI : Finite ↥Hhat := Nat.finite_of_card_ne_zero (by rw [card_Hhat]; norm_num)
  have hidx : ∀ K : Subgroup ↥Hhat, Nat.card K = 512 → ¬ 2 ∣ K.index := by
    intro K hK h2
    have h := Subgroup.card_mul_index K
    rw [hK, card_Hhat] at h
    omega
  have hS2 : IsPGroup 2 (S0.subgroupOf Hhat) :=
    IsPGroup.of_card (n := 9) (by rw [hcardS]; norm_num)
  have hU2 : IsPGroup 2 ((T.subgroupOf B).map φ) :=
    IsPGroup.of_card (n := 9) (by rw [hcardU]; norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Hhat (hS2.toSylow (hidx _ hcardS))
    (hU2.toSylow (hidx _ hcardU))
  have hUeq : (T.subgroupOf B).map φ = MulAut.conj h • S0.subgroupOf Hhat := by
    have := congrArg (fun P : Sylow 2 ↥Hhat => (P : Subgroup ↥Hhat)) hh
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this.symm
  have hconj : ∀ y : ↥Hhat,
      y ∈ (T.subgroupOf B).map φ ↔ ∃ s ∈ S0.subgroupOf Hhat, h * s * h⁻¹ = y := by
    intro y
    rw [hUeq, Subgroup.mem_smul_pointwise_iff_exists]
    simp only [MulAut.smul_def, MulAut.conj_apply]
  have hmap : (T.subgroupOf B).map φ = (S0.subgroupOf Hhat).map (MulAut.conj h).toMonoidHom := by
    ext y
    rw [hconj, Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨θ', hθ'def⟩ : ∃ g : ↥T →* StatedSp 3 (ZMod 2),
      ∀ t, g t = ((h⁻¹ * f₁ t * h : ↥Hhat) : StatedSp 3 (ZMod 2)) := by
    refine ⟨Hhat.subtype.comp ((MulAut.conj h⁻¹).toMonoidHom.comp f₁), fun t => ?_⟩
    change ((MulAut.conj h⁻¹ (f₁ t) : ↥Hhat) : StatedSp 3 (ZMod 2)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hθ' : Function.Injective θ' := by
    intro a b hab
    rw [hθ'def, hθ'def] at hab
    exact hf₁ (mul_left_cancel (mul_right_cancel (Subtype.ext hab)))
  have hrange : θ'.range = S0 := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨s, hs, hst⟩ := (hconj (f₁ t)).mp (hU ▸ MonoidHom.mem_range.mpr ⟨t, rfl⟩)
      rw [hθ'def, ← hst, show h⁻¹ * (h * s * h⁻¹) * h = s by group]
      exact Subgroup.mem_subgroupOf.mp hs
    · intro hy
      obtain ⟨s, rfl, hsS⟩ : ∃ s : ↥Hhat, (s : StatedSp 3 (ZMod 2)) = y ∧ s ∈ S0.subgroupOf Hhat :=
        ⟨⟨y, S0_le_Hhat hy⟩, rfl, Subgroup.mem_subgroupOf.mpr hy⟩
      obtain ⟨b, hb, hbs⟩ := (hconj (h * s * h⁻¹)).mpr ⟨s, hsS, rfl⟩
      have ht : f₁ ⟨b, hb⟩ = h * s * h⁻¹ := (hf₁def b hb b.2).trans hbs
      exact ⟨⟨b, hb⟩, by rw [hθ'def, ht, show h⁻¹ * (h * s * h⁻¹) * h = s by group]⟩
  obtain ⟨θ, hθ⟩ : ∃ e : ↥T ≃* ↥S0, ∀ t, (e t : StatedSp 3 (ZMod 2)) = θ' t :=
    ⟨(MonoidHom.ofInjective hθ').trans (MulEquiv.subgroupCongr hrange), fun _ => rfl⟩
  have hA0f : A0 ≤ θ'.range := hrange ▸ A0_le_S0
  have hAE : IsE64 ((A0.comap θ').map T.subtype) :=
    isE64_map_of_injective T.subtype_injective (isE64_comap_of_injective hθ' isE64_A0 hA0f)
  have hmem : ∀ x (hx : x ∈ T),
      x ∈ (A0.comap θ').map T.subtype ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0 := by
    intro x hx
    rw [hθ]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hxA
      exact ⟨⟨x, hx⟩, hxA, rfl⟩
  refine ⟨h, hmap, θ, fun x hx hxB => ?_, (A0.comap θ').map T.subtype, Subgroup.map_subtype_le _,
    hAE, hmem, ?_, fun A' hA'T hA' => ?_⟩
  · rw [hθ, hθ'def, hf₁def x hx hxB]
  ·
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hmem a a.2).mp ha
    · intro hy
      obtain ⟨a, rfl⟩ := θ.surjective y
      exact ⟨a, (hmem a a.2).mpr hy, rfl⟩
  ·
    have hA'' : IsE64 (A'.comap T.subtype) :=
      isE64_comap_of_injective T.subtype_injective hA' (by rw [Subgroup.range_subtype]; exact hA'T)
    have himg := eq_A0_of_isE64 _ (by rw [← hrange]; exact Subgroup.map_le_range θ' _)
      (isE64_map_of_injective hθ' hA'')
    have hle : A' ≤ (A0.comap θ').map T.subtype := by
      intro x hx
      refine ⟨⟨x, hA'T hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← himg]
      exact ⟨⟨x, hA'T hx⟩, hx, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAE.2.2, hA'.2.2])

end CFSG.ClassicalInvolution.Sp62Rec

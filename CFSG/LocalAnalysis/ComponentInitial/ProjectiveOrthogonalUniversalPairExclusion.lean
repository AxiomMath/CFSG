module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponent
public import CFSG.LocalAnalysis.ComponentInitial.OddProjectivePairExclusion

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

open Module Subgroup CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.OddProjectivePair
open TauCeti.QuadraticMap (orthogonalGroup)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace OrthogonalPair

theorem eq_of_isCompl {A W : Submodule K V} (hAW : IsCompl A W) {x y : orthogonalGroup Q}
    (hA : ∀ a ∈ A, (x : V ≃ₗ[K] V) a = (y : V ≃ₗ[K] V) a)
    (hW : ∀ w ∈ W, (x : V ≃ₗ[K] V) w = (y : V ≃ₗ[K] V) w) : x = y := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (hAW.sup_eq_top ▸ Submodule.mem_top : v ∈ A ⊔ W)
  rw [map_add, map_add, hA a ha, hW w hw]

theorem apply_mem_of_fix {A W : Submodule K V} (hAW : IsCompl A W)
    (horth : ∀ a ∈ A, ∀ w ∈ W, Q.polarBilin a w = 0)
    (hWnd : (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate) {x : orthogonalGroup Q}
    (hx : ∀ w ∈ W, (x : V ≃ₗ[K] V) w = w) {a : V} (ha : a ∈ A) : (x : V ≃ₗ[K] V) a ∈ A := by
  obtain ⟨a', ha', w', hw', hxa⟩ :=
    Submodule.mem_sup.1 (hAW.sup_eq_top ▸ Submodule.mem_top : (x : V ≃ₗ[K] V) a ∈ A ⊔ W)
  have hw0 : (⟨w', hw'⟩ : W) = 0 := hWnd.1 _ fun w => by
    change Q.polarBilin w' w = 0
    have h1 := polarBilin_map_of_mem x.2 a w
    rw [hx w w.2, ← hxa, map_add, LinearMap.add_apply, horth a' ha' w w.2, zero_add,
      horth a ha w w.2] at h1
    exact h1
  have hw'0 : w' = 0 := congrArg Subtype.val hw0
  rw [← hxa, hw'0, add_zero]
  exact ha'

theorem exists_eigen_of_ne_pm {S : V →ₗ[K] V} (hS2 : ∀ v, S (S v) = v)
    {A : Submodule K V} (hSA : ∀ a ∈ A, S a ∈ A) (hneg : ¬ ∀ a ∈ A, S a = -a)
    (hpos : ¬ ∀ a ∈ A, S a = a) :
    (∃ v ∈ A, v ≠ 0 ∧ S v = v) ∧ ∃ v ∈ A, v ≠ 0 ∧ S v = -v := by
  push Not at hneg hpos
  obtain ⟨a, ha, hSa⟩ := hneg
  obtain ⟨b, hb, hSb⟩ := hpos
  refine ⟨⟨a + S a, A.add_mem ha (hSA a ha), fun h0 => hSa ?_, ?_⟩,
    ⟨b - S b, A.sub_mem hb (hSA b hb), fun h0 => hSb (sub_eq_zero.1 h0).symm, ?_⟩⟩
  · exact eq_neg_of_add_eq_zero_right h0
  · rw [map_add, hS2, add_comm]
  · rw [map_sub, hS2, neg_sub]

theorem exists_elemAbelian_subgroupOf {D : Type*} [Group D] {B C V₀ : Subgroup D} (hBC : B ≤ C)
    (hV₀ : V₀ ≤ B) (hV₀e : CFSG.IsElementaryAbelian 2 V₀) (hV₀c : Nat.card V₀ = 4) :
    ∃ E : Subgroup C, E ≤ B.subgroupOf C ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  refine ⟨V₀.subgroupOf C, fun x hx => Subgroup.mem_subgroupOf.2 (hV₀ hx), ⟨⟨⟨fun x y =>
    Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · have := hV₀e.toIsMulCommutative
    have h := (isMulCommutative_iff.mp this) ⟨((x : C) : D), x.2⟩ ⟨((y : C) : D), y.2⟩
    have h2 : ((x : C) : D) * ((y : C) : D) = ((y : C) : D) * ((x : C) : D) :=
      congrArg (Subtype.val : V₀ → D) h
    exact h2
  · have := hV₀e
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₀) _ hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hV₀.trans hBC)).toEquiv, hV₀c]

end OrthogonalPair

open OrthogonalPair

theorem odd_projective_orthogonal_commuting_universal_pair_exclusion {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V]
    (hd : 5 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate) :
    ¬ ∃ B₁ B₂ : Subgroup (orthogonalGroup Q ⧸ orthSigns Q),
      CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧ ⁅B₁, B₂⁆ = ⊥ ∧
      (∃ V₁ : Subgroup (orthogonalGroup Q ⧸ orthSigns Q), V₁ ≤ B₁ ∧
        CFSG.IsElementaryAbelian 2 V₁ ∧ Nat.card V₁ = 4) ∧
      (∃ V₂ : Subgroup (orthogonalGroup Q ⧸ orthSigns Q), V₂ ≤ B₂ ∧
        CFSG.IsElementaryAbelian 2 V₂ ∧ Nat.card V₂ = 4) ∧
      (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁
        (centralizer ({t} : Set (orthogonalGroup Q ⧸ orthSigns Q)))) ∧
      (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂
        (centralizer ({s} : Set (orthogonalGroup Q ⧸ orthSigns Q)))) := by
  rintro ⟨B₁, B₂, hq₁, hq₂, hcomm, ⟨V₁, hV₁, hV₁e, hV₁c⟩, ⟨V₂, hV₂, hV₂e, hV₂c⟩, h₁, h₂⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  set π := QuotientGroup.mk' (orthSigns Q) with hπ
  have hB₁p := commutator_eq_self_of_isQuasisimple hq₁
  have hB₂p := commutator_eq_self_of_isQuasisimple hq₂
  have hB₁ne := ne_bot_of_card_eq_four hV₁ hV₁c
  have hB₂ne := ne_bot_of_card_eq_four hV₂ hV₂c
  have hB₁B₂ : B₁ ≤ centralizer (B₂ : Set (orthogonalGroup Q ⧸ orthSigns Q)) :=
    commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hB₂B₁ : B₂ ≤ centralizer (B₁ : Set (orthogonalGroup Q ⧸ orthSigns Q)) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hcomm)
  set B₁hat := ⁅B₁.comap π, B₁.comap π⁆ with hB₁hat
  set B₂hat := ⁅B₂.comap π, B₂.comap π⁆ with hB₂hat
  have hmk₁ : ∀ g ∈ B₁hat, π g ∈ B₁ := fun g hg => commutator_le_self (B₁.comap π) hg
  have hneg : ∀ v : V, -v = v → v = 0 := by
    intro v hv
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hv]
      exact neg_add_cancel v
    exact (smul_eq_zero.1 h2v).resolve_left htwo
  obtain ⟨t, htV, -, -, ht1, -, -⟩ := exists_ne_one_ne_one_ne hV₂c
  have ht2 : t ^ 2 = 1 := by
    have := hV₂e
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₂) t htV
  have htB₂ : t ∈ B₂ := hV₂ htV
  obtain ⟨T, hT⟩ := QuotientGroup.mk'_surjective (orthSigns Q) t
  have hC₁ := h₁ t htB₂ (orderOf_eq_prime ht2 ht1)
  have hBcomp₁ := (isComponentOf_iff_isComponent_subgroupOf hC₁.1).1 hC₁
  have hmap₁ : ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype :
      Subgroup (orthogonalGroup Q ⧸ orthSigns Q)) = B₁ := map_subgroupOf_eq_of_le hC₁.1
  obtain ⟨hTT, hP, hM, horth, hndP, hndM, A, W, hAW, hfixW, -, ⟨e, he⟩, -, -, hfixA⟩ :=
    odd_projective_orthogonal_local_component_eigenspace_fixed_space hp hp2 hf hK hd hQ
      (orderOf_eq_prime ht2 ht1) hT hBcomp₁
      (exists_elemAbelian_subgroupOf hC₁.1 hV₁ hV₁e hV₁c) (R := B₂)
      (by rw [hmap₁]; exact hB₂B₁) hB₂ne hB₂p
  rw [hmap₁] at hfixW
  have hTT' : ∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = v := fun v =>
    LinearEquiv.congr_fun (congrArg Subtype.val hTT) v
  have hTT'' : (T : V ≃ₗ[K] V).toLinearMap * (T : V ≃ₗ[K] V).toLinearMap = 1 :=
    LinearMap.ext hTT'
  have hcompl := UnitaryHigher.isCompl_ker_sub_one_ker_add_one htwo hTT''
  have hAWc : IsCompl A W := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcompl
    · exact hcompl.symm
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hM
    · exact hP
  have hAWo : ∀ a ∈ A, ∀ w ∈ W, Q.polarBilin a w = 0 := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact horth
    · intro a ha w hw
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
        ← QuadraticMap.polarBilin_apply_apply]
      exact horth w hw a ha
  have hWnd : (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hndM
    · exact hndP
  obtain ⟨v, hv, v', hv', hv1, hv'1, hvv'⟩ := exists_ne_one_ne_one_ne hV₁c
  have hsq : ∀ w ∈ V₁, w * w = 1 := fun w hw => by
    have := hV₁e
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₁) w hw
  have hlift : ∀ w ∈ V₁, ∃ x : orthogonalGroup Q, x ∈ B₁hat ∧ π x = w ∧ x * x = 1 := by
    intro w hw
    set y : B₁.subgroupOf (centralizer {t}) :=
      ⟨⟨w, hC₁.1 (hV₁ hw)⟩, by rw [mem_subgroupOf]; exact hV₁ hw⟩
    refine ⟨(e.symm y : orthogonalGroup Q), ?_, ?_, ?_⟩
    · have hK' : ⁅((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π,
          ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π⁆ =
          B₁hat := by rw [hmap₁]
      exact (Subgroup.ext_iff.1 hK' _).1 (e.symm y).2
    · rw [← he, MulEquiv.apply_symm_apply]
    · have hy : y * y = 1 := Subtype.ext (Subtype.ext (hsq w hw))
      rw [← Subgroup.coe_mul, ← map_mul, hy, map_one, Subgroup.coe_one]
  obtain ⟨x, hxB, hxv, hx2⟩ := hlift v hv
  obtain ⟨x', hx'B, hx'v, hx'2⟩ := hlift v' hv'
  have hxx' : x ≠ x' := fun h0 => hvv' (by rw [← hxv, ← hx'v, h0])
  have hx1 : x ≠ 1 := fun h1 => hv1 (by rw [← hxv, h1, map_one])
  have hx'1 : x' ≠ 1 := fun h1 => hv'1 (by rw [← hx'v, h1, map_one])
  have hgood : ∀ y : orthogonalGroup Q, y ∈ B₁hat → y ≠ 1 →
      ¬ ∀ a ∈ A, (y : V ≃ₗ[K] V) a = a := fun y hy hy1 hyA =>
    hy1 (eq_of_isCompl hAWc (fun a ha => hyA a ha) fun w hw => hfixW y hy w hw)
  obtain ⟨S, hSB, hS2, hS1, hSneg⟩ : ∃ S : orthogonalGroup Q, S ∈ B₁hat ∧ S * S = 1 ∧ S ≠ 1 ∧
      ¬ ∀ a ∈ A, (S : V ≃ₗ[K] V) a = -a := by
    by_cases hxA : ∀ a ∈ A, (x : V ≃ₗ[K] V) a = -a
    · refine ⟨x', hx'B, hx'2, hx'1, fun hx'A => hxx' ?_⟩
      exact eq_of_isCompl hAWc (fun a ha => by rw [hxA a ha, hx'A a ha])
        fun w hw => by rw [hfixW x hxB w hw, hfixW x' hx'B w hw]
    · exact ⟨x, hxB, hx2, hx1, hxA⟩
  have hS2' : ∀ v, (S : V ≃ₗ[K] V) ((S : V ≃ₗ[K] V) v) = v := fun v =>
    LinearEquiv.congr_fun (congrArg Subtype.val hS2) v
  have hSA : ∀ a ∈ A, (S : V ≃ₗ[K] V) a ∈ A := fun a ha =>
    apply_mem_of_fix hAWc hAWo hWnd (hfixW S hSB) ha
  obtain ⟨⟨vp, hvpA, hvp0, hvp⟩, ⟨vm, hvmA, hvm0, hvm⟩⟩ :=
    exists_eigen_of_ne_pm (S := (S : V ≃ₗ[K] V).toLinearMap) hS2' hSA hSneg (hgood S hSB hS1)
  set s := π S with hsdef
  have hsB₁ : s ∈ B₁ := hmk₁ S hSB
  have hs2 : s ^ 2 = 1 := by rw [hsdef, ← map_pow, sq, hS2, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    exact hS1 (eq_one_of_mem_orthSigns htwo ((QuotientGroup.eq_one_iff S).1 h1) hW0
      (hfixW S hSB))
  have hC₂ := h₂ s hsB₁ (orderOf_eq_prime hs2 hs1)
  have hBcomp₂ := (isComponentOf_iff_isComponent_subgroupOf hC₂.1).1 hC₂
  have hmap₂ : ((B₂.subgroupOf (centralizer {s})).map (centralizer {s}).subtype :
      Subgroup (orthogonalGroup Q ⧸ orthSigns Q)) = B₂ := map_subgroupOf_eq_of_le hC₂.1
  obtain ⟨-, -, -, -, -, -, A', W', hA'W', -, -, -, -, hfixset, -⟩ :=
    odd_projective_orthogonal_local_component_eigenspace_fixed_space hp hp2 hf hK hd hQ
      (orderOf_eq_prime hs2 hs1) hsdef.symm hBcomp₂
      (exists_elemAbelian_subgroupOf hC₂.1 hV₂ hV₂e hV₂c) (R := B₁)
      (by rw [hmap₂]; exact hB₁B₂) hB₁ne hB₁p
  rw [hmap₂] at hfixset
  have hAfix : ∀ a ∈ A, a ∈ W' := fun a ha => by
    rw [← SetLike.mem_coe, ← hfixset]
    exact fun g hg => hfixA g hg a ha
  rcases hA'W' with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · have h1 := LinearMap.mem_ker.1 (hAfix vp hvpA)
    rw [LinearMap.add_apply, Module.End.one_apply] at h1
    change (S : V ≃ₗ[K] V) vp + vp = 0 at h1
    have h2 : (S : V ≃ₗ[K] V) vp = vp := hvp
    rw [h2] at h1
    exact hvp0 ((smul_eq_zero.1 (by rw [two_smul]; exact h1 : (2 : K) • vp = 0)).resolve_left
      htwo)
  · have h1 := LinearMap.mem_ker.1 (hAfix vm hvmA)
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    have h2 : (S : V ≃ₗ[K] V) vm = -vm := hvm
    change (S : V ≃ₗ[K] V) vm = vm at h1
    rw [h2] at h1
    exact hvm0 (hneg vm h1)

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

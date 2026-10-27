module

public import CFSG.LargeExtraspecial.S63BD4
public import CFSG.LargeExtraspecial.S63DSchurGroup
public import CFSG.LargeExtraspecial.S63DSchurAt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification
open scoped commutatorElement

namespace S63

namespace SmithConf

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}
variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

omit [Finite X] in
theorem comm_zeta_of_piU_comm {u : ↥(normalClosure ({ζ} : Set X))}
    (hc : piU ζ u * piU ζ (zetaU ζ) = piU ζ (zetaU ζ) * piU ζ u) : (u : X) * ζ = ζ * u := by
  obtain ⟨u', hu', hu'ζ⟩ := hC.exists_lift_of_comm hs hc
  have hw : u'⁻¹ * u ∈ center ↥(normalClosure ({ζ} : Set X)) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hu'
    exact hu'
  have hwζ : ζ * ((u' : X)⁻¹ * u) = (u' : X)⁻¹ * u * ζ :=
    congrArg Subtype.val (mem_center_iff.mp hw (zetaU ζ))
  calc (u : X) * ζ = u' * ((u' : X)⁻¹ * u * ζ) := by group
    _ = u' * (ζ * ((u' : X)⁻¹ * u)) := by rw [hwζ]
    _ = (u' * ζ) * (u' : X)⁻¹ * u := by group
    _ = ζ * u := by rw [hu'ζ]; group

omit [Finite X] hs in
theorem mem_normalizer_comap {u : ↥(normalClosure ({ζ} : Set X))} (hu : (u : X) * ζ = ζ * u) :
    u ∈ normalizer (F.comap (normalClosure ({ζ} : Set X)).subtype : Set _) := by
  have hc : (u : X) ∈ centralizer ({ζ} : Set X) := mem_centralizer_singleton_iff.mpr hu
  rw [mem_normalizer_iff]
  intro h
  simp only [mem_comap, coe_subtype, coe_mul, coe_inv]
  constructor
  · exact hC.hyp.conj_mem _ hc _
  · intro hh
    have := hC.hyp.conj_mem _ (inv_mem hc) _ hh
    rwa [show (u : X)⁻¹ * ((u : X) * h * (u : X)⁻¹) * (u : X)⁻¹⁻¹ = h by group] at this

omit [Finite X] in
theorem eq_one_of_mem_comap_center (hFU : F ≤ normalClosure ({ζ} : Set X))
    {v : ↥(normalClosure ({ζ} : Set X))}
    (hvF : v ∈ F.comap (normalClosure ({ζ} : Set X)).subtype)
    (hvZ : v ∈ center ↥(normalClosure ({ζ} : Set X))) : v = 1 := by
  have hvF' : (v : X) ∈ F := hvF
  have hcF : (⟨v, hvF'⟩ : F) ∈ center F := mem_center_iff.mpr fun g => Subtype.ext (by
    have := congrArg Subtype.val (mem_center_iff.mp hvZ ⟨g, hFU g.2⟩)
    exact this)
  rcases (hC.mem_center_F_iff hvF').mp hcF with h | h
  · exact Subtype.ext h
  · have hZ : (v : X) ∈ ZU ζ := ⟨v, hvZ, rfl⟩
    rw [h] at hZ
    exact absurd hZ (not_mem_ZU_of_simple hs)

theorem center_eq_bot_of_split (hFU : F ≤ normalClosure ({ζ} : Set X))
    (hsplit : D42SplitAt (UZ ζ) (piU ζ (zetaU ζ)))
    (hadm : AdmAt (piU ζ (zetaU ζ)) (iota (F := F) hs).range) :
    center ↥(normalClosure ({ζ} : Set X)) = ⊥ := by
  have hperf : commutator ↥(normalClosure ({ζ} : Set X)) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (hC.perfect hs))
  have hker : ∀ g : ↥(normalClosure ({ζ} : Set X)), piU ζ g = 1 →
      g ∈ center ↥(normalClosure ({ζ} : Set X)) := fun g hg => by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  obtain ⟨x₁', x₂', x₃', y', hc1, hc2, hc3, c12, c13, c23, r1, r2, r3, hodd⟩ := hsplit _ hadm
  obtain ⟨x₁, rfl⟩ := piU_surjective ζ x₁'
  obtain ⟨y, rfl⟩ := piU_surjective ζ y'
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, y * x₁ * y⁻¹ = x₂ := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ x₃, y * x₂ * y⁻¹ = x₃ := ⟨_, rfl⟩
  have e₂ : piU ζ x₂ = x₂' := by rw [← hx₂, map_mul, map_mul, map_inv, r1]
  have e₃ : piU ζ x₃ = x₃' := by rw [← hx₃, map_mul, map_mul, map_inv, e₂, r2]
  subst e₂ e₃
  have hcomm : ∀ {a b : ↥(normalClosure ({ζ} : Set X))}, Commute (piU ζ a) (piU ζ b) →
      ⁅a, b⁆ ∈ center ↥(normalClosure ({ζ} : Set X)) := fun h => hker _ (by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h.eq)
  have hrel : y * x₃ * y⁻¹ * (x₂ * x₁)⁻¹ ∈ center ↥(normalClosure ({ζ} : Set X)) :=
    hker _ (by simp only [map_mul, map_inv]; rw [r3, mul_inv_cancel])
  obtain ⟨e12, e13, e23⟩ := commutator_eq_one_of_cube hx₂ hx₃ (hcomm c12) (hcomm c13)
    (hcomm c23) hrel
  set S : Set ↥(normalClosure ({ζ} : Set X)) :=
    (center ↥(normalClosure ({ζ} : Set X)) : Set _) ∪ {x₁, x₂, x₃}
  have hxc : ∀ a ∈ ({x₁, x₂, x₃} : Set ↥(normalClosure ({ζ} : Set X))),
      ∀ b ∈ ({x₁, x₂, x₃} : Set ↥(normalClosure ({ζ} : Set X))), Commute a b := by
    have h12 := commutatorElement_eq_one_iff_mul_comm.mp e12
    have h13 := commutatorElement_eq_one_iff_mul_comm.mp e13
    have h23 := commutatorElement_eq_one_iff_mul_comm.mp e23
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl)
    all_goals first
      | exact Commute.refl _
      | exact h12
      | exact h13
      | exact h23
      | exact h12.symm
      | exact h13.symm
      | exact h23.symm
  have hSc : S.Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha
    · exact (mem_center_iff.mp ha b).symm
    · rcases hb with hb | hb
      · exact mem_center_iff.mp hb a
      · exact hxc a ha b hb
  have hA : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
    have := isMulCommutative_closure hSc
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : closure S) ⟨b, hb⟩)
  have hAB : closure S ≤ normalizer (F.comap (normalClosure ({ζ} : Set X)).subtype : Set _) := by
    rw [closure_le]
    rintro a (ha | ha)
    · rw [SetLike.mem_coe, mem_normalizer_iff]
      intro h
      rw [← mem_center_iff.mp ha h, mul_inv_cancel_right]
    · refine hC.mem_normalizer_comap (hC.comm_zeta_of_piU_comm hs ?_)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact mem_centralizer_singleton_iff.mp hc1
      · exact mem_centralizer_singleton_iff.mp hc2
      · exact mem_centralizer_singleton_iff.mp hc3
  set T := F.comap (normalClosure ({ζ} : Set X)).subtype ⊔ closure S
  have hTF : ⁅T, T⁆ ≤ F.comap (normalClosure ({ζ} : Set X)).subtype :=
    commutator_le.mpr fun g hg h hh => commutator_mem_of_le_normalizer hA hAB hg hh
  have hZT : center ↥(normalClosure ({ζ} : Set X)) ≤ T :=
    fun z hz => mem_sup_right (subset_closure (Or.inl hz))
  have hindex : Odd T.index := by
    have hle : (iota (F := F) hs).range ⊔
        closure ({piU ζ x₁, piU ζ x₂, piU ζ x₃} : Set (UZ ζ)) ≤ T.map (piU ζ) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨f, rfl⟩
        have hfU := hFU (Finn_le ζ F f.2)
        rw [iota_of_mem_U hs f hfU]
        exact mem_map_of_mem _ (mem_sup_left (show ⟨(f : X), hfU⟩ ∈
          F.comap (normalClosure ({ζ} : Set X)).subtype from Finn_le ζ F f.2))
      · rw [closure_le]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        have hx : ∀ x ∈ ({x₁, x₂, x₃} : Set ↥(normalClosure ({ζ} : Set X))), x ∈ T :=
          fun x hx => mem_sup_right (subset_closure (Or.inr hx))
        rcases ha with rfl | rfl | rfl
        · exact mem_map_of_mem _ (hx _ (by simp))
        · exact mem_map_of_mem _ (hx _ (by simp))
        · exact mem_map_of_mem _ (hx _ (by simp))
    have hdvd := index_dvd_of_le hle
    rw [index_map_eq _ (piU_surjective ζ) (by rw [QuotientGroup.ker_mk']; exact hZT)] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hpow : ∀ z ∈ center ↥(normalClosure ({ζ} : Set X)), z ^ T.index = 1 := fun z hz =>
    hC.eq_one_of_mem_comap_center hs hFU (hTF (pow_index_mem_commutator hperf T hz))
      (pow_mem hz _)
  have hoddZ : Odd (Nat.card (center ↥(normalClosure ({ζ} : Set X)))) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hdvd : orderOf (z : ↥(normalClosure ({ζ} : Set X))) ∣ T.index :=
      orderOf_dvd_of_pow_eq_one (hpow z z.2)
    rw [Subgroup.orderOf_coe, hz] at hdvd
    exact (Nat.not_even_iff_odd.mpr hindex) (even_iff_two_dvd.mpr hdvd)
  have hZU : ZU ζ = ⊥ := hC.hyp.oddCore (ZU ζ) ⟨fun w hw k => conj_mem_ZU hw k⟩ (by
    rw [ZU, card_map_of_injective (normalClosure ({ζ} : Set X)).subtype_injective]
    exact hoddZ)
  rwa [ZU, map_eq_bot_iff_of_injective _ (normalClosure ({ζ} : Set X)).subtype_injective] at hZU

end SmithConf

theorem smith58Input_of_split (hD : D42CentInput) (hS : D42SplitInput) : Smith58Input := by
  intro X _ _ ζ F hC hD4
  have hs : IsSimpleGroup (UZ ζ) := Timmesfeld.isSimpleGroup_of_lieModel hD4
  have hFeq := hC.Finn_eq_of_odd (odd_card_outer_of_trialityD4 hD4)
  obtain ⟨hNC, hNn, hN2, hsN, hcardN⟩ := hC.iota_range_props hs
  have hcen : ∀ n ∈ (SmithConf.iota (F := F) hs).range,
      (∀ m ∈ (SmithConf.iota (F := F) hs).range, n * m = m * n) →
        n = 1 ∨ n = piU ζ (zetaU ζ) := by
    rintro _ ⟨f, rfl⟩ hc
    have hfc : ∀ g ∈ F, (f : X) * g = g * f := by
      intro g hg
      have hg' : g ∈ Finn ζ F := by rw [hFeq]; exact hg
      have h1 := hc _ ⟨⟨g, hg'⟩, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hC.iota_injective hs h1)
    have hζF : ζ ∈ Finn ζ F := hC.zeta_mem_Finn
    rcases hC.eq_one_or_eq_of_forall_comm (Finn_le ζ F f.2) hfc with h | h
    · left
      rw [show f = 1 from Subtype.ext h, map_one]
    · right
      rw [show f = ⟨ζ, hζF⟩ from Subtype.ext h]
      exact SmithConf.iota_of_mem_U hs ⟨ζ, hζF⟩ (zetaU ζ).2
  have h32 : 2 ^ 5 ≤ Nat.card (SmithConf.iota (F := F) hs).range := by
    rw [hcardN, hFeq]
    exact hC.hyp.width
  have hs2 : orderOf (piU ζ (zetaU ζ)) = 2 := hC.orderOf_piU hs (IsConj.refl ζ)
  obtain ⟨hNle, hCN⟩ := hD (UZ ζ) hD4 _ hs2 _ hNC hNn hN2 hsN hcen h32
  have hFU := hC.le_normalClosure_of_le_sup hs hFeq hNle
  exact hC.false_of_centralizer_le hs hFU hCN
    (hC.center_eq_bot_of_split hs hFU (hS _ hD4 _ hs2) ⟨hNC, hNn, hN2, hsN, hcen, h32⟩)

end S63

end CFSG.LargeExtraspecial

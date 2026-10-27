module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndData

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem datum_mem_delta {a : Fin r} (d : DeltaDatum D Abar a) :
    rightConjugate (Subgroup.normalizer (D : Set G)) d.g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) :=
  ⟨d.g, rfl, d.ne, d.U, d.four⟩

omit [Finite G] in
theorem card_sup_of_inf_eq_bot {M X : Subgroup G} (hX : X ≤ Subgroup.normalizer (M : Set G))
    (h : M ⊓ X = ⊥) : Nat.card (M ⊔ X : Subgroup G) = Nat.card M * Nat.card X := by
  have h1 := Subgroup.relIndex_mul_card M (M ⊔ X)
  rw [inf_eq_left.mpr le_sup_left, AschbacherTheorem3.relIndex_sup_of_le_normalizer hX] at h1
  have h2 := Subgroup.relIndex_mul_card M X
  rw [h, Subgroup.card_bot, mul_one] at h2
  rw [← h1, h2, mul_comm]

theorem mem_normalizer_of_involution (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    {x : G} (hxA : x ∈ aschbacherThm5Preimage D (Abar a))
    (hxH : x ∈ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) (hx2 : x ^ 2 = 1) :
    x ∈ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :=
  involution_mem_normalizer_conj hloc hC hr (datum_mem_delta d) hxA hxH hx2

theorem mem_of_rightConjugate_eq (hC : Counterexample G D r Abar) {x : G}
    (hx : rightConjugate (Subgroup.normalizer (D : Set G)) x = Subgroup.normalizer (D : Set G)) :
    x ∈ Subgroup.normalizer (D : Set G) := by
  have hr : 0 < r := hC.hyp.hr
  refine hC.hyp.hii ⟨0, hr⟩ x (aschbacherThm5Preimage D (Abar ⟨0, hr⟩)) ?_ ?_
  · change _ ≤ rightConjugate (Subgroup.normalizer (D : Set G)) x
    rw [hx]
    exact (preimage_le D _).trans Subgroup.le_normalizer
  · intro y hy
    exact ⟨y, hy, 1, (aschbacherThm5Core D).one_mem, (mul_one y).symm⟩

theorem rightConjugate_ne (hC : Counterexample G D r Abar) {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) :
    rightConjugate (Subgroup.normalizer (D : Set G)) x ≠ Subgroup.normalizer (D : Set G) :=
  fun h => hx (mem_of_rightConjugate_eq hC h)

theorem exists_ne_ne {E : Subgroup G} (hE : 4 ≤ Nat.card E) (x : G) :
    ∃ z ∈ E, z ≠ 1 ∧ z ≠ x := by
  by_contra h
  push Not at h
  have hsub : (E : Set G) ⊆ {1, x} := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · exact Or.inr (h z hz hz1)
  have h1 : Nat.card E ≤ 2 := by
    calc Nat.card E = Set.ncard (E : Set G) := Nat.card_coe_set_eq _
      _ ≤ Set.ncard ({1, x} : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Set.ncard ({x} : Set G) + 1 := Set.ncard_insert_le 1 {x}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem conj_le_normalizer (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hU4 : 4 ≤ Nat.card (AschbacherTheorem3.omegaOne d.T)) {c : G}
    (hc : c ∈ aschbacherThm5Preimage D (Abar a))
    (hH : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set L := rightConjugate A d.g with hLdef
  have hUL : U ≤ L := EndHyp.U_le_L
  have hUc : rightConjugate U c ≤ rightConjugate A (d.g * c) := by
    rw [← rightConjugate_mul]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hUL c
  have hcH : c ∈ H := (preimage_le D _).trans Subgroup.le_normalizer hc
  by_cases hcg : c ∈ rightConjugate H d.g
  ·
    intro x hx
    have hxD : x ∈ rightConjugate D d.g := by
      have h1 := hUc hx
      rw [← rightConjugate_mul] at h1
      have h2 : rightConjugate L c ≤ rightConjugate (rightConjugate D d.g) c :=
        AschbacherTheorem3.rightConjugate_le_rightConjugate
          (AschbacherTheorem3.rightConjugate_le_rightConjugate (preimage_le D _) d.g) c
      have h3 : rightConjugate (rightConjugate D d.g) c = rightConjugate D d.g := by
        rw [rightConjugate_eq_self_iff, ← AschbacherTheorem3.rightConjugate_normalizer]
        exact hcg
      rw [← h3]
      exact h2 h1
    have hDN : rightConjugate D d.g ≤ Subgroup.normalizer (L : Set G) := by
      rw [hLdef, ← AschbacherTheorem3.rightConjugate_normalizer]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate (le_normalizer_factor hC a) d.g
    exact hDN hxD
  ·
    have hUc2 : IsElemAbelian 2 (rightConjugate U c) :=
      isElemAbelian_rightConjugate (isElemAbelian_omegaOne hT) c
    have hcard : 4 ≤ Nat.card (rightConjugate U c) := by rw [rightConjugate_card]; exact hU4
    have hg₀ : d.g * c⁻¹ * d.g⁻¹ ∉ H := by
      intro h
      apply hcg
      rw [mem_rightConjugate_iff]
      have := H.inv_mem h
      simpa [mul_assoc] using this
    have hne : rightConjugate H (d.g * c⁻¹ * d.g⁻¹) ≠ H := rightConjugate_ne hC hg₀
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    obtain ⟨z, hz, hz1, hzx⟩ := exists_ne_ne hcard x
    have hx2 : x ^ 2 = 1 := hUc2.2 x hx
    have hz2 : z ^ 2 = 1 := hUc2.2 z hz
    have hxz : x * z = z * x := congrArg Subtype.val (hUc2.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    obtain ⟨hE4, hEel⟩ :=
      AschbacherTheorem3.exists_four_of_involutions hx2 hz2 hx1 hz1 (Ne.symm hzx) hxz
    set E := Subgroup.zpowers x ⊔ Subgroup.zpowers z with hEdef
    have hEU : E ≤ rightConjugate U c :=
      sup_le (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hz)
    set E' := rightConjugate E (d.g * c)⁻¹ with hE'def
    have hE'A : E' ≤ A := by
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate (hEU.trans hUc)
        (d.g * c)⁻¹
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    have hE'H : E' ≤ rightConjugate H (d.g * c⁻¹ * d.g⁻¹) := by
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate (hEU.trans hH)
        (d.g * c)⁻¹
      rw [rightConjugate_mul] at h1
      convert h1 using 2
      group
    have hE'el : IsElemAbelian 2 E' := isElemAbelian_rightConjugate hEel _
    have hE'4 : Nat.card E' = 4 := by rw [hE'def, rightConjugate_card, hE4]
    have hN := fourGroup_le_normalizer_conj hloc hC hne hE'A hE'H hE'el hE'4 a
    have hN' := AschbacherTheorem3.rightConjugate_le_rightConjugate hN (d.g * c)
    rw [hE'def, rightConjugate_mul, inv_mul_cancel, rightConjugate_one,
      AschbacherTheorem3.rightConjugate_normalizer, rightConjugate_mul] at hN'
    have hgg : d.g * c⁻¹ * d.g⁻¹ * (d.g * c) = d.g := by group
    rw [hgg] at hN'
    exact hN' (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem T_comm_W (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a) :
    ∀ t ∈ d.T, ∀ w ∈ d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G), t * w = w * t := by
  have hW : d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :=
    inf_le_inf_right _ d.sylowS.le
  refine commute_of_normalizers hC (datum_g_not_mem d) (P := d.S) d.sylowT.le hW
    d.sylowS.isPGroup ?_
  intro t ht w hw
  have h1 : t⁻¹ * w⁻¹ * t ∈ d.S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (d.invariant ht)) w⁻¹).mp
      (d.S.inv_mem hw.1)
    simpa [mul_assoc] using this
  exact d.S.mul_mem h1 hw.1

theorem conj_le_sup (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hU4 : 4 ≤ Nat.card (AschbacherTheorem3.omegaOne d.T)) {c : G}
    (hc : c ∈ aschbacherThm5Preimage D (Abar a))
    (hle : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      d.S ⊔ AschbacherTheorem3.omegaOne d.T)
    (hH : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set L := rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  have hN := conj_le_normalizer hloc hC d hT hU4 hc hH
  have hel := isElemAbelian_rightConjugate (isElemAbelian_omegaOne hT) c
  intro y hy
  have hy' : y ∈ ((U ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact hle hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U d.S EndHyp.U_le_normalizer_S] at hy'
  obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hy'
  have huL : u ∈ L := EndHyp.U_le_L hu
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := by
    have : s = u⁻¹ * (u * s) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer huL)) (hN hy)
  have hsW : s ∈ W := ⟨hs, hsN⟩
  have hus : u * s = s * u := T_comm_W hC d u (EndHyp.U_le_T hu) s hsW
  have hs2 : s ^ 2 = 1 := by
    have h1 := hel.2 _ hy
    have hu2 := (isElemAbelian_omegaOne hT).2 u hu
    have h2 : (u * s) ^ 2 = u ^ 2 * s ^ 2 := Commute.mul_pow hus 2
    rw [h2, hu2, one_mul] at h1
    exact h1
  exact Subgroup.mul_mem_sup hu (mem_omegaOne hsW hs2)

theorem card_le_of_conj (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hU4 : 4 ≤ Nat.card (AschbacherTheorem3.omegaOne d.T)) {b : G}
    (hb : b ∈ aschbacherThm5Preimage D (Abar a))
    (hbH : b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hle : rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
      d.S ⊔ AschbacherTheorem3.omegaOne d.T)
    (hH : rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    Nat.card (AschbacherTheorem3.omegaOne d.T) ≤
      Nat.card (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set V₁ := AschbacherTheorem3.omegaOne W with hV₁def
  have hUb := conj_le_sup hloc hC d hT hU4 hb hle hH
  have hV₁W : V₁ ≤ W := AschbacherTheorem3.omegaOne_le W
  have hUV : ∀ u ∈ U, ∀ v ∈ V₁, u * v = v * u := fun u hu v hv =>
    T_comm_W hC d u (EndHyp.U_le_T hu) v (hV₁W hv)
  have hUN : U ≤ Subgroup.normalizer (V₁ : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hUV u hu v hv).symm)
  have hUVcomm : IsMulCommutative (U ⊔ V₁ : Subgroup G) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hx : (x : G) ∈ ((U ⊔ V₁ : Subgroup G) : Set G) := x.2
    have hy : (y : G) ∈ ((U ⊔ V₁ : Subgroup G) : Set G) := y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U V₁ hUN] at hx hy
    obtain ⟨u₁, hu₁, v₁, hv₁, hx1⟩ := Set.mem_mul.mp hx
    obtain ⟨u₂, hu₂, v₂, hv₂, hy1⟩ := Set.mem_mul.mp hy
    change (x : G) * y = y * x
    rw [← hx1, ← hy1]
    have h12 : u₁ * u₂ = u₂ * u₁ :=
      congrArg Subtype.val ((isElemAbelian_omegaOne hT).1.is_comm.comm ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩)
    have hv12 : v₁ * v₂ = v₂ * v₁ := congrArg Subtype.val
      ((AschbacherTheorem3.isMulCommutative_of_le hV₁W hW).is_comm.comm ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩)
    have e1 := hUV u₂ hu₂ v₁ hv₁
    have e2 := hUV u₁ hu₁ v₂ hv₂
    calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by group
      _ = u₁ * (u₂ * v₁) * v₂ := by rw [e1]
      _ = (u₁ * u₂) * (v₁ * v₂) := by group
      _ = (u₂ * u₁) * (v₂ * v₁) := by rw [h12, hv12]
      _ = u₂ * (u₁ * v₂) * v₁ := by group
      _ = u₂ * (v₂ * u₁) * v₁ := by rw [e2]
      _ = u₂ * v₂ * (u₁ * v₁) := by group
  have hUUb : U ⊓ rightConjugate U b = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have ht2 := twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) ht.1
    have hs1 : d.g * t * d.g⁻¹ ∈ A := (mem_rightConjugate_iff _ _ _).mp (EndHyp.U_le_L ht.1)
    have hs2 : d.g * t * d.g⁻¹ ∈ rightConjugate A (d.g * b * d.g⁻¹) := by
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate
        (EndHyp.U_le_L (d := d)) b ht.2
      rw [rightConjugate_mul, mem_rightConjugate_iff] at h1
      rw [mem_rightConjugate_iff]
      have heq : d.g * b * d.g⁻¹ * (d.g * t * d.g⁻¹) * (d.g * b * d.g⁻¹)⁻¹ =
          d.g * b * t * (d.g * b)⁻¹ := by group
      rw [heq]
      exact h1
    have hgb : d.g * b * d.g⁻¹ ∉ Subgroup.normalizer (D : Set G) := fun h =>
      hbH ((mem_rightConjugate_iff _ _ _).mpr h)
    have h1 := eq_one_of_mem_inf_conj hC hgb (twoElt_conj ht2 d.g) hs1 hs2
    calc t = d.g⁻¹ * (d.g * t * d.g⁻¹) * d.g := by group
      _ = 1 := by rw [h1]; group
  have hUV1 : U ⊓ V₁ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have ht1 : t ∈ U ⊓ A := ⟨ht.1, d.sylowS.le (hV₁W ht.2).1⟩
    rwa [EndHyp.U_inf_A hC] at ht1
  have hUbN : rightConjugate U b ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
    exact congrArg Subtype.val (hUVcomm.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩
      ⟨x, hUb hx⟩)
  have h1 := card_sup_of_inf_eq_bot hUbN hUUb
  have h2 := card_sup_of_inf_eq_bot (M := U) (X := V₁) (fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hUV u hu v hv)) hUV1
  have h3 : Nat.card (U ⊔ rightConjugate U b : Subgroup G) ≤ Nat.card (U ⊔ V₁ : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hUb)
  rw [h1, h2, rightConjugate_card] at h3
  exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos

theorem four_le_card_U (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) :
    4 ≤ Nat.card (AschbacherTheorem3.omegaOne d.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, U₀, hU₀, hU₀L⟩ := hloc.lemma_6_7 hC (datum_mem_delta d) a
  have hU₀A := hloc.lemma_6_5_one hC d.ne hU₀ a
  obtain ⟨-, hel, h4, -⟩ := hU₀
  have hU₀2 : IsPGroup 2 U₀ := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf d.sylowT hU₀2
    (le_inf hU₀L hU₀A)
  have hle : rightConjugate U₀ c ≤ AschbacherTheorem3.omegaOne d.T := by
    intro x hx
    refine mem_omegaOne (hc hx) ?_
    exact (isElemAbelian_rightConjugate hel c).2 x hx
  calc 4 = Nat.card (rightConjugate U₀ c) := by rw [rightConjugate_card, h4]
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem exists_conj_of_not_le {a : Fin r} (d : DeltaDatum D Abar a)
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    ∃ b ∈ d.S, b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g ∧
      rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set S₀ := d.S ⊓ Hg with hS₀def
  set Q₀ := S₀ ⊔ d.T with hQ₀def
  set P := d.S ⊔ d.T with hPdef
  have hTHg : d.T ≤ Hg := (d.sylowT.le.trans inf_le_left).trans (conj_factor_le a d.g)
  have hQ₀H : Q₀ ≤ Hg := sup_le inf_le_right hTHg
  have hQ₀P : Q₀ ≤ P := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hP2 : IsPGroup 2 P := by
    rw [hPdef, sup_comm]
    exact IsPGroup.to_sup_of_normal_right' d.sylowT.isPGroup d.sylowS.isPGroup d.invariant
  have hne : Q₀ ≠ P := by
    intro h
    exact hSH (le_sup_left.trans (h ▸ hQ₀H))
  set M : Subgroup P := Q₀.subgroupOf P with hMdef
  have hMtop : M < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hM => hne (le_antisymm hQ₀P fun x hx => ?_)
    have hm : (⟨x, hx⟩ : P) ∈ M := hM ▸ Subgroup.mem_top _
    exact hm
  have : Group.IsNilpotent P := hP2.isNilpotent
  obtain ⟨y, hyN, hyM⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent M hMtop)
  have hyN' : (y : G) ∈ Subgroup.normalizer (Q₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzM : (⟨z, hQ₀P hz⟩ : P) ∈ M := hz
      have := (Subgroup.mem_normalizer_iff.mp hyN _).mp hzM
      exact this
    · intro hz
      have hzP : z ∈ P := by
        have h1 : z = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * y := by group
        rw [h1]
        exact P.mul_mem (P.mul_mem (P.inv_mem y.2) (hQ₀P hz)) y.2
      have hzM : (⟨(y : G) * z * (y : G)⁻¹, hQ₀P hz⟩ : P) ∈ M := hz
      have h2 := (Subgroup.mem_normalizer_iff.mp hyN ⟨z, hzP⟩).mpr (by
        have : y * ⟨z, hzP⟩ * y⁻¹ = (⟨(y : G) * z * (y : G)⁻¹, hQ₀P hz⟩ : P) := rfl
        rw [this]
        exact hzM)
      exact h2
  have hyQ : (y : G) ∉ Q₀ := hyM
  have hy' : (y : G) ∈ ((d.T ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right d.T d.S d.invariant] at hy'
  obtain ⟨t, ht, s, hs, hts⟩ := Set.mem_mul.mp hy'
  have htQ : t ∈ Q₀ := Subgroup.mem_sup_right ht
  have hsN : s ∈ Subgroup.normalizer (Q₀ : Set G) := by
    have : s = t⁻¹ * y := by rw [← hts]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer htQ)) hyN'
  have hsQ : s ∉ Q₀ := by
    intro h
    apply hyQ
    rw [← hts]
    exact Q₀.mul_mem htQ h
  have hsH : s ∉ Hg := fun h => hsQ (Subgroup.mem_sup_left ⟨hs, h⟩)
  refine ⟨s, hs, hsH, ?_⟩
  have h1 : rightConjugate (AschbacherTheorem3.omegaOne d.T) s ≤ rightConjugate Q₀ s :=
    AschbacherTheorem3.rightConjugate_le_rightConjugate
      ((AschbacherTheorem3.omegaOne_le _).trans le_sup_right) s
  rw [(rightConjugate_eq_self_iff Q₀ s).mpr hsN] at h1
  exact h1.trans hQ₀H

theorem endHyp_of_le (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hSH : d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.S) <
      Nat.card (AschbacherTheorem3.omegaOne d.T) *
        Nat.card (AschbacherTheorem3.omegaOne d.S ⊓ factorZStar D Abar a : Subgroup G)) :
    EndHyp d := by
  have hU4 := four_le_card_U hloc hC d
  have hVle : AschbacherTheorem3.omegaOne d.S ≤ d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) := by
    rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
    rintro x ⟨hxS, hx2⟩
    exact ⟨hxS, mem_normalizer_of_involution hloc hC hr d (d.sylowS.le hxS) (hSH hxS) hx2⟩
  refine ⟨hT, hVle, AschbacherTheorem3.isMulCommutative_of_le hVle hW, ?_, hcard⟩
  intro c hc hle
  have hH : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g :=
    hle.trans (sup_le hSH ((AschbacherTheorem3.omegaOne_le _).trans
      ((d.sylowT.le.trans inf_le_left).trans (conj_factor_le a d.g))))
  refine (conj_le_sup hloc hC d hT hU4 hc hle hH).trans (sup_le le_sup_left ?_)
  exact (AschbacherTheorem3.omegaOne_mono inf_le_left).trans le_sup_right

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5

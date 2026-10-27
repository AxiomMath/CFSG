module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwelve

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem le_of_le_normalizer {P K X₁ X₂ : Subgroup G} (𝒰 : Subgroup G → Prop)
    (hP2 : IsPGroup 2 P) (hUP : ∀ X, 𝒰 X → X ≤ P)
    (hinv : ∀ X, 𝒰 X → ∀ p ∈ P, 𝒰 (rightConjugate X p)) (hK : K = X₁ ⊔ X₂) (h₁ : 𝒰 X₁)
    (h₂ : 𝒰 X₂) (hnorm : ∀ X, 𝒰 X → X ≤ Subgroup.normalizer (K : Set G) → X ≤ K) :
    ∀ X, 𝒰 X → X ≤ K := by
  have hKP : K ≤ P := hK ▸ sup_le (hUP X₁ h₁) (hUP X₂ h₂)
  suffices hPN : P ≤ Subgroup.normalizer (K : Set G) from
    fun X hX => hnorm X hX ((hUP X hX).trans hPN)
  by_contra hcon
  set M : Subgroup P := (Subgroup.normalizer (K : Set G)).subgroupOf P with hMdef
  have hMtop : M < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hM => hcon fun x hx => ?_
    have hm : (⟨x, hx⟩ : P) ∈ M := hM ▸ Subgroup.mem_top _
    exact hm
  have : Group.IsNilpotent P := hP2.isNilpotent
  obtain ⟨y, hyN, hyM⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent M hMtop)
  have hyM' : (y : G) ∉ Subgroup.normalizer (K : Set G) := hyM
  have hconj : ∀ X : Subgroup G, X ≤ K → rightConjugate X y ≤ Subgroup.normalizer (K : Set G) := by
    intro X hXK z hz
    rw [mem_rightConjugate_iff] at hz
    have hzP : (y : G) * z * (y : G)⁻¹ ∈ P := hKP (hXK hz)
    have hzM : (⟨(y : G) * z * (y : G)⁻¹, hzP⟩ : P) ∈ M := by
      show (y : G) * z * (y : G)⁻¹ ∈ Subgroup.normalizer (K : Set G)
      exact Subgroup.le_normalizer (hXK hz)
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hzM
    have h2 : y⁻¹ * (⟨(y : G) * z * (y : G)⁻¹, hzP⟩ : P) * y⁻¹⁻¹ =
        ⟨z, by simpa [mul_assoc] using P.mul_mem (P.mul_mem (P.inv_mem y.2) hzP) y.2⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [h2] at h1
    exact h1
  have hX₁ := hnorm _ (hinv X₁ h₁ y y.2) (hconj X₁ (hK ▸ le_sup_left))
  have hX₂ := hnorm _ (hinv X₂ h₂ y y.2) (hconj X₂ (hK ▸ le_sup_right))
  have hKy : rightConjugate K y ≤ K := by
    rw [hK, rightConjugate, Subgroup.map_sup]
    exact sup_le (hK ▸ hX₁) (hK ▸ hX₂)
  apply hyM'
  rw [← rightConjugate_eq_self_iff]
  exact Subgroup.eq_of_le_of_card_ge hKy (by rw [rightConjugate_card])

@[expose] def conjFamily {a : Fin r} (d : DeltaDatum D Abar a) (X : Subgroup G) : Prop :=
  ∃ c ∈ aschbacherThm5Preimage D (Abar a),
    X = rightConjugate (AschbacherTheorem3.omegaOne d.T) c ∧
      X ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T

omit [Finite G] in
theorem conjFamily_rightConjugate {a : Fin r} (d : DeltaDatum D Abar a) {X : Subgroup G}
    (hX : conjFamily d X) {p : G} (hp : p ∈ d.S ⊔ AschbacherTheorem3.omegaOne d.T) :
    conjFamily d (rightConjugate X p) := by
  obtain ⟨c, hc, rfl, hle⟩ := hX
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  have hUA : U ≤ Subgroup.normalizer (A : Set G) := EndHyp.U_le_normalizer_A
  have hp' : p ∈ ((U ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact hp
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U d.S EndHyp.U_le_normalizer_S] at hp'
  obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hp'
  refine ⟨u⁻¹ * c * u * s, ?_, ?_, ?_⟩
  · have h1 : u⁻¹ * c * u ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hUA hu)) c).mp hc
      simpa [mul_assoc] using this
    exact A.mul_mem h1 (d.sylowS.le hs)
  · calc rightConjugate (rightConjugate U c) (u * s) = rightConjugate U (c * (u * s)) :=
          rightConjugate_mul _ _ _
      _ = rightConjugate (rightConjugate U u⁻¹) (c * (u * s)) := by
          rw [AschbacherTheorem3.rightConjugate_eq_of_mem (U.inv_mem hu)]
      _ = rightConjugate U (u⁻¹ * c * u * s) := by
          rw [rightConjugate_mul]
          congr 1
          group
  · have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hle (u * s)
    rwa [AschbacherTheorem3.rightConjugate_eq_of_mem hp] at h1

theorem U_inf_conj (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    {b : G} (hbH : b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    AschbacherTheorem3.omegaOne d.T ⊓ rightConjugate (AschbacherTheorem3.omegaOne d.T) b = ⊥ := by
  set A := aschbacherThm5Preimage D (Abar a)
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have ht2 := twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) ht.1
  have hs1 : d.g * t * d.g⁻¹ ∈ A := (mem_rightConjugate_iff _ _ _).mp (EndHyp.U_le_L ht.1)
  have hs2 : d.g * t * d.g⁻¹ ∈ rightConjugate A (d.g * b * d.g⁻¹) := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate (EndHyp.U_le_L (d := d)) b ht.2
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

theorem UV_comm (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G)) :
    IsMulCommutative (AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) :
        Subgroup G) := by
  set U := AschbacherTheorem3.omegaOne d.T
  set W := d.S ⊓ Subgroup.normalizer
    (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)
  set V₁ := AschbacherTheorem3.omegaOne W
  have hV₁W : V₁ ≤ W := AschbacherTheorem3.omegaOne_le W
  have hUV : ∀ u ∈ U, ∀ v ∈ V₁, u * v = v * u := fun u hu v hv =>
    T_comm_W hC d u (EndHyp.U_le_T hu) v (hV₁W hv)
  have hUN : U ≤ Subgroup.normalizer (V₁ : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hUV u hu v hv).symm)
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

theorem sup_conj_eq (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {b : G} (hbS : b ∈ d.S) (hbH : b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hbU : rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) =
    AschbacherTheorem3.omegaOne d.T ⊔ rightConjugate (AschbacherTheorem3.omegaOne d.T) b := by
  set U := AschbacherTheorem3.omegaOne d.T
  set W := d.S ⊓ Subgroup.normalizer
    (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)
  set V₁ := AschbacherTheorem3.omegaOne W
  have hU4 := four_le_card_U hloc hC d
  have hle : rightConjugate U b ≤ d.S ⊔ U := by
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hbS : b ∈ d.S ⊔ U)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b
  have hUb := conj_le_sup hloc hC d hT hU4 (d.sylowS.le hbS) hle hbU
  have hcomm := UV_comm hC d hT hW
  have hUbN : rightConjugate U b ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩ ⟨x, hUb hx⟩)
  have hV₁N : V₁ ≤ Subgroup.normalizer (U : Set G) := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩
      ⟨v, Subgroup.mem_sup_right hv⟩)
  have hUV1 : U ⊓ V₁ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have ht1 : t ∈ U ⊓ aschbacherThm5Preimage D (Abar a) :=
      ⟨ht.1, d.sylowS.le (AschbacherTheorem3.omegaOne_le W ht.2).1⟩
    rwa [EndHyp.U_inf_A hC] at ht1
  symm
  apply Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hUb)
  rw [card_sup_of_inf_eq_bot hUbN (U_inf_conj hC d hbH), card_sup_of_inf_eq_bot hV₁N hUV1,
    rightConjugate_card, hcard]

theorem exists_bad_element (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hfail : ¬ (AschbacherTheorem3.omegaOne d.S ≤ d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ∧
      ∀ c ∈ aschbacherThm5Preimage D (Abar a),
        rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
          d.S ⊔ AschbacherTheorem3.omegaOne d.T →
        rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
          AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
            Subgroup.normalizer
              (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))) :
    ∃ e ∈ d.S, e ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g ∧
      e ∈ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
        AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
            Set G) ∧
      e ^ 2 ∈ AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set L := rightConjugate A d.g with hLdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set V₁ := AschbacherTheorem3.omegaOne W with hV₁def
  set K := U ⊔ V₁ with hKdef
  have hU4 := four_le_card_U hloc hC d
  obtain ⟨b, hbS, hbH, hbU⟩ := exists_conj_of_not_le d hSH
  have hK : K = U ⊔ rightConjugate U b := sup_conj_eq hloc hC d hT hW hcard hbS hbH hbU
  have hcomm := UV_comm hC d hT hW
  have hUK : U ≤ Subgroup.normalizer (K : Set G) := le_sup_left.trans Subgroup.le_normalizer
  have hbFam : conjFamily d (rightConjugate U b) := by
    refine ⟨b, d.sylowS.le hbS, rfl, ?_⟩
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hbS : b ∈ d.S ⊔ U)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b
  have hUFam : conjFamily d U :=
    ⟨1, A.one_mem, by rw [rightConjugate_one], le_sup_right⟩
  have hP2 : IsPGroup 2 (d.S ⊔ U : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' (d.sylowT.isPGroup.to_le EndHyp.U_le_T)
      d.sylowS.isPGroup EndHyp.U_le_normalizer_S
  have hmemH : ∀ X, conjFamily d X → X ≤ Hg → X ≤ K := by
    rintro X ⟨c, hc, rfl, hle⟩ hH
    exact conj_le_sup hloc hC d hT hU4 hc hle hH
  by_cases hw : ∀ X, conjFamily d X → X ≤ K
  ·
    have hΩ : ¬ AschbacherTheorem3.omegaOne d.S ≤ W := by
      intro hΩ
      apply hfail
      refine ⟨hΩ, fun c hc hle => ?_⟩
      exact hw _ ⟨c, hc, rfl, hle⟩
    rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le] at hΩ
    simp only [Set.not_subset] at hΩ
    obtain ⟨s, ⟨hsS, hs2⟩, hsW⟩ := hΩ
    have hsH : s ∉ Hg := by
      intro h
      exact hsW ⟨hsS, mem_normalizer_of_involution hloc hC hr d (d.sylowS.le hsS) h hs2⟩
    refine ⟨s, hsS, hsH, ?_, by rw [hs2]; exact K.one_mem⟩
    rw [← rightConjugate_eq_self_iff]
    apply Subgroup.eq_of_le_of_card_ge _ (by rw [rightConjugate_card])
    have hsP : s ∈ d.S ⊔ U := Subgroup.mem_sup_left hsS
    rw [hK, rightConjugate, Subgroup.map_sup]
    refine sup_le (hK ▸ hw _ (conjFamily_rightConjugate d hUFam hsP))
      (hK ▸ hw _ (conjFamily_rightConjugate d hbFam hsP))
  ·
    have hex : ∃ X, conjFamily d X ∧ X ≤ Subgroup.normalizer (K : Set G) ∧ ¬ X ≤ K := by
      by_contra hne
      push Not at hne
      exact hw (le_of_le_normalizer (conjFamily d) hP2 (fun X hX => hX.choose_spec.2.2)
        (fun X hX p hp => conjFamily_rightConjugate d hX hp) hK hUFam hbFam hne)
    obtain ⟨X, hX, hXN, hXK⟩ := hex
    have hXH : ¬ X ≤ Hg := fun h => hXK (hmemH X hX h)
    obtain ⟨c, hc, rfl, hle⟩ := hX
    obtain ⟨x₀, hx₀, hx₀H⟩ := Set.not_subset.mp hXH
    have hx₀2 : x₀ ^ 2 = 1 :=
      (isElemAbelian_rightConjugate (isElemAbelian_omegaOne hT) c).2 x₀ hx₀
    have hx₀' : x₀ ∈ ((U ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact hle hx₀
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U d.S EndHyp.U_le_normalizer_S] at hx₀'
    obtain ⟨u₀, hu₀, e, he, hue⟩ := Set.mem_mul.mp hx₀'
    have hu₀H : u₀ ∈ Hg :=
      (EndHyp.U_le_L hu₀ : u₀ ∈ L) |> fun h => conj_factor_le a d.g h
    have heH : e ∉ Hg := by
      intro h
      apply hx₀H
      rw [← hue]
      exact Hg.mul_mem hu₀H h
    have heN : e ∈ Subgroup.normalizer (K : Set G) := by
      have : e = u₀⁻¹ * x₀ := by rw [← hue]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUK hu₀)) (hXN hx₀)
    refine ⟨e, he, heH, heN, ?_⟩
    have h1 : e * u₀ * e = u₀⁻¹ := by
      rw [← hue] at hx₀2
      have : u₀ * e * (u₀ * e) = 1 := by rw [← sq]; exact hx₀2
      calc e * u₀ * e = u₀⁻¹ * (u₀ * e * (u₀ * e)) := by group
        _ = u₀⁻¹ := by rw [this, mul_one]
    have h2 : e ^ 2 = u₀⁻¹ * (e⁻¹ * u₀⁻¹ * e) := by
      calc e ^ 2 = (e * u₀ * e) * (e⁻¹ * u₀⁻¹ * e) := by rw [sq]; group
        _ = u₀⁻¹ * (e⁻¹ * u₀⁻¹ * e) := by rw [h1]
    rw [h2]
    have hu₀K : u₀⁻¹ ∈ K := K.inv_mem (Subgroup.mem_sup_left hu₀)
    refine K.mul_mem hu₀K ?_
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heN) u₀⁻¹).mp hu₀K
    simpa using this

theorem mem_omegaOne_W_of_mem_sup (hC : Counterexample G D r Abar) {a : Fin r}
    (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    {x : G} (hx : x ∈ AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hxS : x ∈ d.S) :
    x ∈ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  set U := AschbacherTheorem3.omegaOne d.T
  set V₁ := AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
  have hcomm := UV_comm hC d hT hW
  have hUN : U ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨v, Subgroup.mem_sup_right hv⟩
      ⟨u, Subgroup.mem_sup_left hu⟩)
  have hx' : x ∈ ((U ⊔ V₁ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U V₁ hUN] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have hvS : v ∈ d.S := (AschbacherTheorem3.omegaOne_le _ hv).1
  have huS : u ∈ d.S := by
    have : u = (u * v) * v⁻¹ := by group
    rw [this]
    exact d.S.mul_mem hxS (d.S.inv_mem hvS)
  have hu1 : u ∈ U ⊓ aschbacherThm5Preimage D (Abar a) := ⟨hu, d.sylowS.le huS⟩
  rw [EndHyp.U_inf_A hC, Subgroup.mem_bot] at hu1
  rw [hu1, one_mul]
  exact hv

theorem bad_element_props (hC : Counterexample G D r Abar) {a : Fin r}
    (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {e : G} (heS : e ∈ d.S) (heH : e ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (heN : e ∈ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
        AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
            Set G))
    (he2 : e ^ 2 ∈ AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    (∀ u ∈ AschbacherTheorem3.omegaOne d.T, e⁻¹ * u * e = u → u = 1) ∧
    (∀ v ∈ AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)),
      ∃ u ∈ AschbacherTheorem3.omegaOne d.T, u⁻¹ * (e⁻¹ * u * e) = v) ∧
    (∀ v ∈ AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)),
      e * v = v * e) := by
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V₁ := AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
    with hV₁def
  set K := U ⊔ V₁ with hKdef
  have hcomm := UV_comm hC d hT hW
  have hKc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hconjK : ∀ x ∈ K, e⁻¹ * x * e ∈ K := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heN) x).mp hx
    simpa using this
  have hinj : ∀ u ∈ U, e⁻¹ * u * e = u → u = 1 := by
    intro u hu hue
    have h1 : u ∈ U ⊓ rightConjugate U e := by
      refine ⟨hu, ?_⟩
      rw [← hue]
      exact AschbacherTheorem3.conj_mem_rightConjugate hu e
    rwa [U_inf_conj hC d heH, Subgroup.mem_bot] at h1
  have hmem : ∀ u ∈ U, u⁻¹ * (e⁻¹ * u * e) ∈ V₁ := by
    intro u hu
    refine mem_omegaOne_W_of_mem_sup hC d hT hW (K.mul_mem (K.inv_mem (Subgroup.mem_sup_left hu))
      (hconjK u (Subgroup.mem_sup_left hu))) ?_
    have h1 : u⁻¹ * e⁻¹ * u ∈ d.S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
        (EndHyp.U_le_normalizer_S hu)) e⁻¹).mp (d.S.inv_mem heS)
      simpa [mul_assoc] using this
    have : u⁻¹ * (e⁻¹ * u * e) = (u⁻¹ * e⁻¹ * u) * e := by group
    rw [this]
    exact d.S.mul_mem h1 heS
  set f : U → V₁ := fun u => ⟨(u : G)⁻¹ * (e⁻¹ * u * e), hmem u u.2⟩ with hfdef
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (e⁻¹ * x * e) = (y : G)⁻¹ * (e⁻¹ * y * e) := congrArg Subtype.val hxy
    set w := (y : G) * (x : G)⁻¹ with hwdef
    have hwU : w ∈ U := U.mul_mem y.2 (U.inv_mem x.2)
    have hw : e⁻¹ * w * e = w := by
      have hax := hconjK x (Subgroup.mem_sup_left x.2)
      have hay := hconjK y (Subgroup.mem_sup_left y.2)
      have hc1 := hKc _ (K.inv_mem (Subgroup.mem_sup_left x.2)) _ hax
      have hc2 := hKc _ (K.inv_mem (Subgroup.mem_sup_left y.2)) _ hay
      have hc3 := hKc _ (Subgroup.mem_sup_left y.2) _ (K.inv_mem hax)
      have hc4 := hKc _ (Subgroup.mem_sup_left x.2) _ hay
      calc e⁻¹ * w * e = (e⁻¹ * y * e) * (e⁻¹ * x * e)⁻¹ := by rw [hwdef]; group
        _ = w := by
          rw [hwdef]
          have h2 : (e⁻¹ * y * e) = (y : G) * ((x : G)⁻¹ * (e⁻¹ * x * e)) := by
            rw [h1]; group
          rw [h2]
          group
    have := hinj w hwU hw
    apply Subtype.ext
    have h3 : (y : G) = x := by
      calc (y : G) = w * x := by rw [hwdef]; group
        _ = x := by rw [this, one_mul]
    exact h3.symm
  have hfbij := hfinj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  have hsurj : ∀ v ∈ V₁, ∃ u ∈ U, u⁻¹ * (e⁻¹ * u * e) = v := by
    intro v hv
    obtain ⟨u, hu⟩ := hfbij.2 ⟨v, hv⟩
    exact ⟨u, u.2, congrArg Subtype.val hu⟩
  refine ⟨hinj, hsurj, ?_⟩
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hsurj v hv
  have huK : u ∈ K := Subgroup.mem_sup_left hu
  have hau := hconjK u huK
  have he2u : e⁻¹ * (e⁻¹ * u * e) * e = u := by
    have h1 : (e ^ 2)⁻¹ * u * e ^ 2 = u := by
      rw [hKc _ (K.inv_mem he2) _ huK]
      group
    calc e⁻¹ * (e⁻¹ * u * e) * e = (e ^ 2)⁻¹ * u * e ^ 2 := by rw [sq]; group
      _ = u := h1
  have hv2 : (u⁻¹ * (e⁻¹ * u * e)) ^ 2 = 1 :=
    (isElemAbelian_omegaOne hW).2 _ (hmem u hu)
  have h1 : e⁻¹ * (u⁻¹ * (e⁻¹ * u * e)) * e = (u⁻¹ * (e⁻¹ * u * e))⁻¹ := by
    have step1 : e⁻¹ * (u⁻¹ * (e⁻¹ * u * e)) * e =
        (e⁻¹ * u * e)⁻¹ * (e⁻¹ * (e⁻¹ * u * e) * e) := by group
    rw [step1, he2u]
    group
  have h2 : (u⁻¹ * (e⁻¹ * u * e))⁻¹ = u⁻¹ * (e⁻¹ * u * e) := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hv2]
  rw [h2] at h1
  calc e * (u⁻¹ * (e⁻¹ * u * e)) = e * (e⁻¹ * (u⁻¹ * (e⁻¹ * u * e)) * e) := by rw [h1]
    _ = u⁻¹ * (e⁻¹ * u * e) * e := by group

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5

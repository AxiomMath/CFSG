module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Defs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D13

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def rotFour (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {C | IsCyclic C ∧ Nat.card C = 4 ∧
    ∃ L ∈ Ω, ∃ T V : Subgroup G, IsSylowOf 2 T L ∧ IsDihedralRot V T ∧ C ≤ V}

theorem rotFour_conj (hΩ : Assumption41 Ω) {C : Subgroup G} (hC : C ∈ rotFour Ω) (g : G) :
    AschbacherTightEmbedding.rightConjugate C g ∈ rotFour Ω := by
  obtain ⟨hc, h4, L, hL, T, V, hT, hV, hCV⟩ := hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, by rw [rightConjugate_card]; exact h4, _, hΩ.conj_mem L hL g, _, _,
    isSylowOf_rightConjugate hT g, hV.rightConjugate g, rightConjugate_le_rightConjugate hCV g⟩
  exact isCyclic_of_surjective ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap C)
    ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap_surjective C)

theorem zpowers_eq_of_mem_of_card_four {C : Subgroup G} (h4 : Nat.card C = 4) {x : G}
    (hx : x ∈ C) (hx1 : x ≠ 1) (hxx : x * x ≠ 1) : zpowers x = C := by
  apply eq_of_le_of_card_ge ((zpowers_le).mpr hx)
  rw [h4, Nat.card_zpowers]
  have hdvd : orderOf x ∣ 4 := by
    rw [← h4]
    have := orderOf_dvd_natCard (⟨x, hx⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have h2 : orderOf x ≠ 2 := fun h => hxx (by
    have := pow_orderOf_eq_one x
    rwa [h, pow_two] at this)
  have : orderOf x ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hd] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

omit [Finite G] in
theorem mul_mul_eq_one_of_card_four {C : Subgroup G} (h4 : Nat.card C = 4) {x : G}
    (hx : x ∈ C) : x * x * (x * x) = 1 := by
  have h1 : (⟨x, hx⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, h4] at h2
  have h3 : x ^ 4 = 1 := by simpa using h2
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at h3
  exact h3

theorem mem_gammaSet_of_mem_sec4W (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {x : G} (hx : IsZInv Ω x) (hxW : x ∈ sec4W Ω S) : x ∈ L26.gammaSet S (rotFour Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hL, T₀, V₀, hT₀, hV₀, hxV₀, hx1, hxx⟩ := hx
  obtain ⟨T, V, hT, hV, hxV, -, hVW⟩ :=
    exists_isSylowOf_le_normalizer_of_mem hΩ hS hL hT₀ hV₀ hxV₀ hx1 hxx hxW
  obtain ⟨v, hvV, hvx⟩ := hV.exists_sq_of_mul_self hxV hxx
  have hv4 : orderOf v = 4 := by
    have hdvd : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one (by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ← hvx, hxx])
    have h2 : ¬ orderOf v ∣ 2 := fun h => hx1 (by
      have := orderOf_dvd_iff_pow_eq_one.mp h
      rw [pow_two] at this
      rw [hvx, this])
    have : orderOf v ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact absurd (by rw [h]; exact one_dvd 2) h2
    · exact absurd (by rw [h]) h2
    · exact h
  refine ⟨hx1, zpowers v, ⟨⟨⟨v, mem_zpowers v⟩, ?_⟩, by rw [Nat.card_zpowers, hv4], L, hL, T, V,
    hT, hV, (zpowers_le).mpr hvV⟩, ((zpowers_le).mpr hvV).trans (hVW.trans (sec4W_le S)), ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨k, Subtype.ext (by simp)⟩
  · rw [hvx]
    exact mul_mem (mem_zpowers v) (mem_zpowers v)

theorem exists_involution_of_mem_rotFour {C : Subgroup G} (hC : C ∈ rotFour Ω) :
    ∃ y ∈ C, IsZInv Ω y ∧ ∀ x ∈ C, x * x = 1 ∨ x * x = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h4, L, hL, T, V, hT, hV, hCV⟩ := hC
  obtain ⟨⟨y, hyC⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [h4]; norm_num)
  rw [Subgroup.orderOf_mk] at hy
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  have hyy : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  obtain ⟨z, -, -, -, hzuniq, -⟩ := hV.exists_involution
  have hyz : y = z := (hzuniq y (hCV hyC) hyy).resolve_left hy1
  refine ⟨y, hyC, ⟨L, hL, T, V, hT, hV, hCV hyC, hy1, hyy⟩, fun x hx => ?_⟩
  by_cases hxx : x * x = 1
  · exact Or.inl hxx
  · right
    have h1 := mul_mul_eq_one_of_card_four h4 hx
    rw [hyz]
    exact (hzuniq _ (hCV (mul_mem hx hx)) h1).resolve_left hxx

theorem le_sec4W_of_mem_rotFour (hΩ : Assumption41 Ω)
    (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤)
    (hZ2 : ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S : Set G) → x ∈ sec4W Ω S)
    {C : Subgroup G} (hC : C ∈ rotFour Ω) (hCS : C ≤ S) : C ≤ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyC, hyZ, -⟩ := exists_involution_of_mem_rotFour hC
  obtain ⟨-, -, L, hL, T, V, hT, hV, hCV⟩ := hC
  have hSN : S ≤ normalizer (sec4W Ω S : Set G) := le_normalizer_sec4W hΩ.conj_mem S
  have hyW := hZ2 y hyZ (hSN (hCS hyC))
  have hy1 : y ≠ 1 := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hyZ; exact h
  have hyy : y * y = 1 := by obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hyZ; exact h
  obtain ⟨T₁, -, hT₁, -, -, hT₁W, -⟩ :=
    exists_isSylowOf_le_normalizer_of_mem hΩ hS hL hT hV (hCV hyC) hy1 hyy hyW
  intro x hx
  exact mem_sec4W_of_mem_omegaD hΩ hnil hS ⟨hL, T₁, hT₁, hT₁W⟩ hT hV (hCV hx) (hSN (hCS hx))

theorem MinCounter.false_of_fourGroup (h27 : L26.Asc76Lemma27) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K)
    (hZ2 : ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S : Set G) → x ∈ sec4W Ω S)
    {a b : G} (haW : a ∈ sec4W Ω S) (haZ : IsZInv Ω a) (hbW : b ∈ sec4W Ω S) (hbZ : IsZInv Ω b)
    (hab : a ≠ b) (habZ : IsZInv Ω (a * b)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  set Δ := rotFour Ω with hΔdef
  have hSN : S ≤ normalizer (W : Set G) := le_normalizer_sec4W hΩ.conj_mem S
  obtain ⟨K₁, hK₁, hall⟩ := hM.single
  obtain ⟨K₀, hK₀⟩ := exists_mem_omegaD hΩ hS hK₁
  have hX := sSup_dStarComp_ne_top_of_not_conn hΩ hM.single hdis hK₀.1
  have hCeq := hM.dStarComp_eq_omegaD hK₀ hX
  have hΔ : ∀ T ∈ Δ, IsCyclic T ∧ Nat.card T = 4 := fun T hT => ⟨hT.1, hT.2.1⟩
  have hΔc : ∀ T ∈ Δ, ∀ g : G, AschbacherTightEmbedding.rightConjugate T g ∈ Δ :=
    fun T hT g => rotFour_conj hΩ hT g
  have hstrong : CFSG.Open.fusionStronglyClosed (L26.gammaSet S Δ) S := by
    rintro x ⟨hx1, C, hC, hCS, hxC⟩ g hgS
    by_cases hxx : x * x = 1
    · have hxZ : IsZInv Ω x := by
        obtain ⟨-, -, L, hL, T, V, hT, hV, hCV⟩ := hC
        exact ⟨L, hL, T, V, hT, hV, hCV hxC, hx1, hxx⟩
      exact mem_gammaSet_of_mem_sec4W hΩ hS (hxZ.conj hΩ g) (hZ2 _ (hxZ.conj hΩ g) (hSN hgS))
    · refine ⟨fun h => hx1 ?_, _, hΔc C hC g, ?_, ?_⟩
      · calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      · rw [← zpowers_eq_of_mem_of_card_four hC.2.1 hxC hx1 hxx]
        intro y hy
        rw [mem_rightConjugate_iff] at hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        have e : y = (g⁻¹ * x * g) ^ k := by
          have h1 := conj_zpow (a := g⁻¹) (b := x) (i := k)
          rw [inv_inv] at h1
          rw [h1, hk]
          group
        rw [e]
        exact zpow_mem hgS k
      · exact conj_mem_rightConjugate hxC g
  have hcomm : ∀ T₁ ∈ Δ, ∀ T₂ ∈ Δ, T₁ ≤ S → T₂ ≤ S → T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥ := by
    intro T₁ hT₁ T₂ hT₂ hT₁S hT₂S _
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact sec4W_mul_comm hΩ hS (le_sec4W_of_mem_rotFour hΩ hM.twoNil hS hZ2 hT₂ hT₂S hy)
      (le_sec4W_of_mem_rotFour hΩ hM.twoNil hS hZ2 hT₁ hT₁S hx)
  have haa : a * a = 1 := by obtain ⟨-, -, -, -, -, -, -, -, h⟩ := haZ; exact h
  have hbb : b * b = 1 := by obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hbZ; exact h
  have ha1 : a ≠ 1 := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := haZ; exact h
  have hb1 : b ≠ 1 := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hbZ; exact h
  have habc : a * b = b * a := sec4W_mul_comm hΩ hS haW hbW
  have hfour : ∃ V : Subgroup G, Nat.card V = 4 ∧ CFSG.Open.IsElemAbelian 2 V ∧
      ∀ v ∈ V, v ≠ 1 → v ∈ L26.gammaSet S Δ := by
    refine ⟨Sec4.fourGroup a b haa hbb habc, card_fourGroup haa hbb habc ha1 hb1 hab,
      isElemAbelian_fourGroup haa hbb habc, fun v hv hv1 => ?_⟩
    rcases (mem_fourGroup).mp hv with h | h | h | h
    · exact absurd h hv1
    · rw [h]; exact mem_gammaSet_of_mem_sec4W hΩ hS haZ haW
    · rw [h]; exact mem_gammaSet_of_mem_sec4W hΩ hS hbZ hbW
    · rw [h]; exact mem_gammaSet_of_mem_sec4W hΩ hS habZ (mul_mem haW hbW)
  have htop := h27 G S Δ hS hΔ hΔc hstrong hcomm hfour
  have hmemD : ∀ x ∈ L26.gammaSet S Δ, ∃ L ∈ omegaD Ω W, x ∈ L ∧ ∃ C : Subgroup G,
      Nat.card C = 4 ∧ x ∈ C ∧ C ≤ L := by
    rintro x ⟨-, C, hC, hCS, hxC⟩
    obtain ⟨y, hyC, hyZ, -⟩ := exists_involution_of_mem_rotFour hC
    have h4 := hC.2.1
    obtain ⟨-, -, L, hL, T, V, hT, hV, hCV⟩ := hC
    have hyW := hZ2 y hyZ (hSN (hCS hyC))
    have hy1 : y ≠ 1 := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hyZ; exact h
    have hyy : y * y = 1 := by obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hyZ; exact h
    obtain ⟨T₁, -, hT₁, -, -, hT₁W, -⟩ :=
      exists_isSylowOf_le_normalizer_of_mem hΩ hS hL hT hV (hCV hyC) hy1 hyy hyW
    have hCL : C ≤ L := hCV.trans (hV.le.trans hT.le)
    exact ⟨L, ⟨hL, T₁, hT₁, hT₁W⟩, hCL hxC, C, h4, hxC, hCL⟩
  have hH : L26.fusionGen (L26.gammaSet S Δ) ≤ setStab (dStarComp Ω K₀) := by
    refine (closure_le _).mpr ?_
    rintro g ⟨x, hx, hgx⟩
    obtain ⟨L, hLD, hxL, C, hC4, hxC, -⟩ := hmemD x hx
    obtain ⟨L₂, hL₂D, hgxL₂, -⟩ := hmemD _ hgx
    have hx1 : x ≠ 1 := hx.1
    have hLC : L ∈ dStarComp Ω K₀ := by rw [hCeq]; exact hLD
    have hL₂C : L₂ ∈ dStarComp Ω K₀ := by rw [hCeq]; exact hL₂D
    have hx4 := mul_mul_eq_one_of_card_four hC4 hxC
    obtain ⟨w, hwL, hwL₂, hw1, hww⟩ : ∃ w : G,
        w ∈ AschbacherTightEmbedding.rightConjugate L g ∧ w ∈ L₂ ∧ w ≠ 1 ∧ w * w = 1 := by
      by_cases hxx : x * x = 1
      · refine ⟨g⁻¹ * x * g, conj_mem_rightConjugate hxL g, hgxL₂, fun h => hx1 ?_, ?_⟩
        · calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; group
        · calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
            _ = 1 := by rw [hxx]; group
      · refine ⟨g⁻¹ * (x * x) * g, conj_mem_rightConjugate (mul_mem hxL hxL) g, ?_,
          fun h => hxx ?_, ?_⟩
        · have := mul_mem hgxL₂ hgxL₂
          have e : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
          rwa [e] at this
        · calc x * x = g * (g⁻¹ * (x * x) * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; group
        · calc g⁻¹ * (x * x) * g * (g⁻¹ * (x * x) * g) = g⁻¹ * (x * x * (x * x)) * g := by group
            _ = 1 := by rw [hx4]; group
    have hLg : AschbacherTightEmbedding.rightConjugate L g = L₂ :=
      eq_of_mem_of_mem hΩ (hΩ.conj_mem L hLD.1 g) hL₂D.1 hwL hwL₂ hw1 hww
    have hgL : AschbacherTightEmbedding.rightConjugate L g ∈ dStarComp Ω L := by
      rw [hLg, dStarComp_eq_of_mem hLC]
      exact hL₂C
    have := mem_setStab_dStarComp hΩ hgL
    rwa [dStarComp_eq_of_mem hLC] at this
  have hstab : setStab (dStarComp Ω K₀) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact hH
  have hallC : ∀ L ∈ Ω, L ∈ dStarComp Ω K₀ := by
    intro L hL
    obtain ⟨g, rfl⟩ := hall L hL
    obtain ⟨a, ha⟩ := hall K₀ hK₀.1
    have h1 := (hstab ▸ mem_top (a⁻¹ * g) : a⁻¹ * g ∈ setStab (dStarComp Ω K₀)) K₀
    have h2 := h1.mp Relation.ReflTransGen.refl
    have e : AschbacherTightEmbedding.rightConjugate K₀ (a⁻¹ * g) =
        AschbacherTightEmbedding.rightConjugate K₁ g := by
      rw [ha, rightConjugate_mul, mul_inv_cancel_left]
    rwa [e] at h2
  obtain ⟨K, hK, J, hJ, hJK⟩ := hdis
  exact hJK (Relation.ReflTransGen.trans (reflTransGen_dStarAdj_symm (hallC K hK)) (hallC J hJ))

end CFSG.ComponentClassification.Asc76.Sec4

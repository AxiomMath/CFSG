module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbLines

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.AS81.Qbar CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

namespace IIbSyl

theorem no_normal_complement : ∀ (x₁ x₂ : ZMod 2 × ZMod 2) (b₁ b₂ : Bool),
    cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) ≠ 1 → cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) ≠ z0 →
    cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) ≠ 1 → cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) ≠ z0 →
    cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) ≠ cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) →
    cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) ≠ z0 →
    ∃ s ∈ [t, ss, c1, a, sigma, vv],
      s * cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * s⁻¹ ≠ 1 ∧
      s * cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * s⁻¹ ≠ cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) ∧
      s * cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * s⁻¹ ≠ cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) ∧
      s * cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * s⁻¹ ≠
        cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) := by
  decide +kernel

theorem witness : ∀ y : IIbSyl, chi y = 1 → (∀ x, y ≠ vElt x 0 ∧ y ≠ c1 * vElt x 0) →
    ∃ (x : ZMod 2 × ZMod 2) (b c : Bool),
      ((cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0)) *
          (cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0)) = 1 ∨
        (cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0)) *
          (cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0)) = z0) ∧
      ∀ x', cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0) ≠
          vElt x' 0 ∧
        cond c (y * sigma * y⁻¹ * sigma⁻¹) y * cond b (c1 * vElt x 0) (vElt x 0) ≠
          c1 * vElt x' 0 := by
  decide +kernel

theorem chi_c1 : chi c1 = 1 := by decide

theorem c1_ne_vElt : ∀ x : ZMod 2 × ZMod 2, c1 ≠ vElt x 0 := by decide +kernel

theorem E1_sq : ∀ (x : ZMod 2 × ZMod 2) (b : Bool),
    cond b (c1 * vElt x 0) (vElt x 0) * cond b (c1 * vElt x 0) (vElt x 0) = 1 := by
  decide +kernel

theorem vElt_c1 : ∀ x : ZMod 2 × ZMod 2, vElt x 0 * c1 = c1 * vElt x 0 := by decide +kernel

theorem E1_comm : ∀ (x₁ x₂ : ZMod 2 × ZMod 2) (b₁ b₂ : Bool),
    cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) * cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) =
      cond b₂ (c1 * vElt x₂ 0) (vElt x₂ 0) * cond b₁ (c1 * vElt x₁ 0) (vElt x₁ 0) := by
  decide +kernel

end IIbSyl

namespace IIbStep5Gold

variable {Y : Type} [Group Y] [Finite Y]

theorem component_cases
    (Sb : Sylow 2 Y) {A : Subgroup Y} (hO : goldschmidtOddCore Y = ⊥)
    (hAS : A ≤ Sb) (hA8 : Nat.card A = 8) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAO : CFSG.Open.pCore 2 Y ≤ A)
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 Sb)
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x)
    {a₀ : Y} (ha₀A : a₀ ∈ A) (ha₀1 : a₀ ≠ 1) (ha₀c : ∀ y : Y, y * a₀ = a₀ * y)
    (K : ComponentIndex Y) :
    (∀ φ : MulAut Y, A.map φ.toMonoidHom = A → K.1.map φ.toMonoidHom = K.1) ∧
    ((a₀ ∈ K.1 ∧ A ≤ K.1 ∧
        (∀ u ∈ (Sb : Subgroup Y) ⊓ K.1, u * u = 1 ∨ u * u = a₀ → u ∈ A) ∧
        ¬ ((Sb : Subgroup Y) ⊓ K.1 ≤ A)) ∨
      (a₀ ∉ K.1 ∧ Nat.card (A ⊓ K.1 : Subgroup Y) = 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have h1 := hA2 _ (mul_mem ha hb)
    have h2 := hA2 a ha
    have h3 := hA2 b hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3, one_mul, mul_one]
  set Φ := conjAutOn K.1 A (le_normalizer_of_inducesOmega1 Sb (hind K)) with hΦ
  have hW4 : 4 ≤ Nat.card Φ.range := four_le_card_range Sb K.2 (htype K) (hind K)
  have hker : ∀ a : A, a ∈ Φ.ker ↔ (a : Y) ∈ centralizer (K.1 : Set Y) := by
    intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      rw [mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun e : MulAut K.1 => ((e ⟨y, hy⟩ : K.1) : Y)) h1
      simp only [hΦ, conjAutOn_apply, MulAut.one_apply] at h2
      calc y * a = (a * y * (a : Y)⁻¹) * a := by rw [h2]
        _ = a * y := by group
    · intro h1
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hΦ, conjAutOn_apply, MulAut.one_apply, ← mem_centralizer_iff.mp h1 y y.2]
      group
  have hcardA : Nat.card A = Nat.card Φ.range * Nat.card Φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hker2 : Nat.card Φ.ker ≤ 2 := by
    rw [hA8] at hcardA
    by_contra h
    push Not at h
    have : 4 * 3 ≤ Nat.card Φ.range * Nat.card Φ.ker := Nat.mul_le_mul hW4 h
    omega
  have hCA : ∀ c ∈ A, c ∈ centralizer (K.1 : Set Y) → c = 1 ∨ c = a₀ := by
    intro c hc hcK
    by_contra hne
    push Not at hne
    have ha₀K : (⟨a₀, ha₀A⟩ : A) ∈ Φ.ker :=
      (hker _).mpr (mem_centralizer_iff.mpr fun y _ => ha₀c y)
    have hcK' : (⟨c, hc⟩ : A) ∈ Φ.ker := (hker _).mpr hcK
    have h3 : 3 ≤ Nat.card Φ.ker := by
      classical
      have hs : ({1, ⟨⟨a₀, ha₀A⟩, ha₀K⟩, ⟨⟨c, hc⟩, hcK'⟩} : Finset Φ.ker).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h1
          apply hne.2
          have := congrArg (fun x : Φ.ker => ((x : A) : Y)) h1
          exact this.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨fun h1 => ha₀1 ?_, fun h1 => hne.1 ?_⟩
          · have := congrArg (fun x : Φ.ker => ((x : A) : Y)) h1
            exact this.symm
          · have := congrArg (fun x : Φ.ker => ((x : A) : Y)) h1
            exact this.symm
      have := Fintype.ofFinite Φ.ker
      rw [← hs, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    omega
  have hcov : ∀ b ∈ A, ∃ x ∈ A ⊓ K.1, b * x⁻¹ ∈ centralizer (K.1 : Set Y) := by
    intro b hb
    obtain ⟨x, hx, hbx⟩ := hcover K b hb
    refine ⟨x, hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := hbx y hy
    calc y * (b * x⁻¹) = b * (b⁻¹ * y * b) * x⁻¹ := by group
      _ = b * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
      _ = b * x⁻¹ * y := by group
  have hZ : ∀ ζ : K.1, ζ ∈ center K.1 → (ζ : Y) = 1 ∨ (ζ : Y) = a₀ := by
    intro ζ hζ
    have hK' : IsComponentOf K.1 ⊤ := (CFSG.isComponent_iff_open K.1).mp K.2
    refine hCA _ (hAO (center_component_le_pCore hO hK' hζ))
      (mem_centralizer_iff.mpr fun y hy => ?_)
    simpa using congrArg Subtype.val ((mem_center_iff.mp hζ) ⟨y, hy⟩)
  have hcomm : ∀ L : ComponentIndex Y, L ≠ K → ∀ x ∈ L.1, x ∈ centralizer (K.1 : Set Y) :=
    fun L hLK x hx => mem_centralizer_iff.mpr fun y hy =>
      ((componentIndex_commute hLK) x y hx hy).symm
  have hK' : IsComponentOf K.1 ⊤ := (CFSG.isComponent_iff_open K.1).mp K.2
  have hfix : (A ≤ K.1 ∨ (a₀ ∉ K.1 ∧ Nat.card (A ⊓ K.1 : Subgroup Y) = 4)) →
      ∀ φ : MulAut Y, A.map φ.toMonoidHom = A → K.1.map φ.toMonoidHom = K.1 := by
    intro hcase φ hφA
    by_contra hne
    set L : ComponentIndex Y := ⟨K.1.map φ.toMonoidHom, isComponent_map_mulEquiv φ K.2⟩
    have hLK : L ≠ K := fun h1 => hne (congrArg Subtype.val h1)
    rcases hcase with hAK | ⟨ha₀K, h4⟩
    ·
      have hAL : A ≤ L.1 := by
        rw [← hφA]
        exact map_mono hAK
      have : Nat.card Φ.ker = 8 := by
        rw [← hA8]
        refine Nat.card_congr (Equiv.ofBijective (fun a => (a : A)) ⟨Subtype.val_injective, ?_⟩)
        intro a
        exact ⟨⟨a, (hker a).mpr (hcomm L hLK a (hAL a.2))⟩, rfl⟩
      omega
    ·
      set D := A ⊓ K.1 with hD
      set D' := A ⊓ L.1 with hD'
      have hD'eq : D' = D.map φ.toMonoidHom := by
        rw [hD', hD, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, hφA]
      have h4' : Nat.card D' = 4 := by
        rw [hD'eq, card_map_of_injective φ.injective, h4]
      have hdisj : D ⊓ D' = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨hxA, hxK⟩, ⟨-, hxL⟩⟩
        rcases hCA x hxA (hcomm L hLK x hxL) with h1 | h1
        · exact h1 ▸ one_mem _
        · exact absurd (h1 ▸ hxK) ha₀K
      have hN : D' ≤ normalizer (D : Set Y) := fun x hx => mem_normalizer_iff.mpr fun y => by
        have hxA : x ∈ A := (mem_inf.mp hx).1
        constructor
        · intro hy
          rw [hAab x hxA y (mem_inf.mp hy).1, mul_inv_cancel_right]
          exact hy
        · intro hy
          have h1 : x * y * x⁻¹ = y := by
            have hy' : y ∈ A := by
              have := mul_mem (mul_mem (inv_mem hxA) (mem_inf.mp hy).1) hxA
              rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
            rw [hAab x hxA y hy', mul_inv_cancel_right]
          rw [h1] at hy
          exact hy
      have h16 := AS76b.card_sup_eq_mul hN hdisj
      rw [h4, h4'] at h16
      have hle := Subgroup.card_le_of_le (sup_le (inf_le_left : D ≤ A) (inf_le_left : D' ≤ A))
      rw [h16, hA8] at hle
      omega
  by_cases ha₀K : a₀ ∈ K.1
  ·
    have hAK : A ≤ K.1 := by
      intro b hb
      obtain ⟨x, ⟨hxA, hxK⟩, hbx⟩ := hcov b hb
      rcases hCA _ (mul_mem hb (inv_mem hxA)) hbx with h1 | h1
      · rw [show b = b * x⁻¹ * x by group, h1, one_mul]
        exact hxK
      · rw [show b = b * x⁻¹ * x by group, h1]
        exact mul_mem ha₀K hxK
    have hroot : ∀ u ∈ (Sb : Subgroup Y) ⊓ K.1, u * u = 1 ∨ u * u = a₀ → u ∈ A := by
      intro u hu hu2
      have hu2' : u ^ 2 ∈ centralizer (K.1 : Set Y) := by
        rw [sq]
        rcases hu2 with h1 | h1 <;> rw [h1]
        · exact one_mem _
        · exact mem_centralizer_iff.mpr fun y _ => ha₀c y
      obtain ⟨b, hb, hbu⟩ := (hind K).2 u hu hu2'
      obtain ⟨x, ⟨hxA, hxK⟩, hxb⟩ := hcover K b hb
      have hux : u * x⁻¹ ∈ centralizer (K.1 : Set Y) := mem_centralizer_iff.mpr fun y hy => by
        have h1 := (hbu y hy).symm.trans (hxb y hy)
        calc y * (u * x⁻¹) = u * (u⁻¹ * y * u) * x⁻¹ := by group
          _ = u * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
          _ = u * x⁻¹ * y := by group
      have huxK : u * x⁻¹ ∈ K.1 := mul_mem hu.2 (inv_mem hxK)
      rcases hZ ⟨u * x⁻¹, huxK⟩ (mem_center_iff.mpr fun y => Subtype.ext
          (mem_centralizer_iff.mp hux y y.2)) with h1 | h1
      · rw [show u = u * x⁻¹ * x by group, show u * x⁻¹ = 1 from h1, one_mul]
        exact hxA
      · rw [show u = u * x⁻¹ * x by group, show u * x⁻¹ = a₀ from h1]
        exact mul_mem ha₀A hxA
    refine ⟨?_, Or.inl ⟨ha₀K, hAK, hroot, fun hSK => ?_⟩⟩
    · exact hfix (Or.inl hAK)
    ·
      have : Group.IsPerfect K.1 := ⟨hK'.2.2.1⟩
      obtain ⟨P, hP⟩ := isSylowOf_inf_component Sb K.2
      have ha₀P : (⟨a₀, ha₀K⟩ : K.1) ∈ (P : Subgroup K.1) := by
        have h1 : a₀ ∈ (P : Subgroup K.1).map K.1.subtype := by
          rw [hP]
          exact ⟨hAS ha₀A, ha₀K⟩
        obtain ⟨y, hy, hye⟩ := h1
        have hy' : y = ⟨a₀, ha₀K⟩ := Subtype.ext hye
        rwa [← hy']
      have hcent : ((⟨⟨a₀, ha₀K⟩, ha₀P⟩ : (P : Subgroup K.1)) : K.1) ∈ center K.1 :=
        mem_center_iff.mpr fun y => Subtype.ext (ha₀c y)
      have hmem := CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived P _ hcent
      have hPab : commutator (P : Subgroup K.1) = ⊥ := by
        rw [commutator_eq_bot_iff]
        refine ⟨⟨fun x y => ?_⟩⟩
        · apply Subtype.ext; apply Subtype.ext
          have hx : ((x : K.1) : Y) ∈ A := hSK (by
            have : ((x : K.1) : Y) ∈ (P : Subgroup K.1).map K.1.subtype := ⟨x, x.2, rfl⟩
            rwa [hP] at this)
          have hy : ((y : K.1) : Y) ∈ A := hSK (by
            have : ((y : K.1) : Y) ∈ (P : Subgroup K.1).map K.1.subtype := ⟨y, y.2, rfl⟩
            rwa [hP] at this)
          simpa using hAab _ hx _ hy
      rw [hPab, mem_bot] at hmem
      exact ha₀1 (congrArg (fun x : (P : Subgroup K.1) => ((x : K.1) : Y)) hmem)
  ·
    have hAK4 : Nat.card (A ⊓ K.1 : Subgroup Y) = 4 := by
      have hsurj : Function.Surjective (fun x : ↥(A ⊓ K.1) =>
          (⟨Φ ⟨x, x.2.1⟩, ⟨_, rfl⟩⟩ : Φ.range)) := by
        rintro ⟨_, ⟨b, rfl⟩⟩
        obtain ⟨x, hx, hbx⟩ := hcover K b b.2
        refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        exact (conjAutOn_eq_of_sameOn _ hbx).symm
      have hge := Nat.card_le_card_of_surjective _ hsurj
      have hdvd : Nat.card (A ⊓ K.1 : Subgroup Y) ∣ 8 :=
        hA8 ▸ Subgroup.card_dvd_of_le inf_le_left
      have hne : Nat.card (A ⊓ K.1 : Subgroup Y) ≠ 8 := fun h8 => ha₀K (by
        have := eq_of_le_of_card_ge (inf_le_left : A ⊓ K.1 ≤ A) (by rw [h8, hA8])
        have h1 : a₀ ∈ A ⊓ K.1 := by rw [this]; exact ha₀A
        exact h1.2)
      have hle8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card (A ⊓ K.1 : Subgroup Y) <;> omega
    exact ⟨hfix (Or.inr ⟨ha₀K, hAK4⟩), Or.inr ⟨ha₀K, hAK4⟩⟩

end IIbStep5Gold

namespace IIbData

variable {G : Type} [Group G] [Finite G] {A R T V₀ P : Subgroup G} {g t z₀ a σ c₁ : G}

theorem centralizer_le_normalizer_E₁
    (hGold : Asc76X.GoldschmidtTheoremA) (hS : Setting310 A R g T V₀)
    (hD : IIbData A R T V₀ P t z₀ a σ c₁) (hA : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁)
    (hO : AS76b.oddCoreIn (centralizer ({z₀} : Set G)) = ⊥) :
    centralizer ({z₀} : Set G) ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfinj, hfrange, hfS0, hfP, hfV0, hfR, hft, hfz, hfa, hfσ, hfc⟩ := hD.emb
  set C := centralizer ({z₀} : Set G) with hCdef
  set E₁ := V₀ ⊔ zpowers c₁ with hE₁def
  have hS₁C : P ⊔ zpowers t ≤ C := fun s hs => (mem_inf.mp (hD.S₁_le hS hs)).2
  have hE₁S₁ : E₁ ≤ P ⊔ zpowers t :=
    sup_le (hD.S₁_le_of_V₀ hS) (zpowers_le.mpr hD.c₁_mem_S₁)
  have hE₁C : E₁ ≤ C := hE₁S₁.trans hS₁C
  obtain ⟨T₀, hT₀⟩ := hD.sylow.of_le hS₁C le_top
  have hfS : ∀ y : IIbSyl, f y ∈ P ⊔ zpowers t := fun y => hfrange ▸ (⟨y, rfl⟩ : f y ∈ f.range)
  have hfV : ∀ x : ZMod 2 × ZMod 2, f (IIbSyl.vElt x 0) ∈ V₀ := fun x => by
    rw [← hfV0]
    exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩
  have hE₁f : ∀ e ∈ E₁, ∃ (x : ZMod 2 × ZMod 2) (b : Bool),
      e = f (cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) := by
    intro e he
    have hcN : zpowers c₁ ≤ normalizer (V₀ : Set G) :=
      zpowers_le.mpr ((mem_inf.mp (hD.S₁_le hS hD.c₁_mem_S₁)).1)
    obtain ⟨v, hv, b, hb, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hcN he
    obtain ⟨x, rfl⟩ : ∃ x : ZMod 2 × ZMod 2, f (IIbSyl.vElt x 0) = v := by
      rw [← hfV0] at hv
      obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hv
      exact ⟨Multiplicative.toAdd w, rfl⟩
    have hc2 : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, IIbSyl.c1_facts.2.1, map_one]
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hc2 hb with h1 | h1
    · exact ⟨x, false, by rw [h1, mul_one]; rfl⟩
    · refine ⟨x, true, ?_⟩
      rw [h1, ← hfc, ← map_mul, IIbSyl.vElt_c1 x]
      rfl
  have hfE₁ : ∀ (x : ZMod 2 × ZMod 2) (b : Bool),
      f (cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) ∈ E₁ := by
    intro x b
    cases b
    · exact mem_sup_left (hfV x)
    · change f (IIbSyl.c1 * IIbSyl.vElt x 0) ∈ E₁
      rw [map_mul, hfc]
      exact mul_mem (mem_sup_right (mem_zpowers c₁)) (mem_sup_left (hfV x))
  have hE₁ab : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₁, b₁, rfl⟩ := hE₁f x hx
    obtain ⟨x₂, b₂, rfl⟩ := hE₁f y hy
    rw [← map_mul, ← map_mul, IIbSyl.E1_comm]
  set Q' := E₁.subgroupOf C with hQ'
  have hmemT₀ : ∀ y : C, y ∈ (T₀ : Subgroup C) ↔ (y : G) ∈ P ⊔ zpowers t := by
    intro y
    constructor
    · intro hy
      rw [← hT₀]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hT₀] at hy
      obtain ⟨y', hy', he⟩ := hy
      rwa [← Subtype.ext he]
  have hQ'T : Q' ≤ (T₀ : Subgroup C) := fun x hx =>
    (hmemT₀ x).mpr (hE₁S₁ (mem_subgroupOf.mp hx))
  have hQab : IsMulCommutative Q' := ⟨⟨fun x y => Subtype.ext (Subtype.ext
    (hE₁ab _ (mem_subgroupOf.mp x.2) _ (mem_subgroupOf.mp y.2)))⟩⟩
  have hcl : fusionStronglyClosed (Q' : Set C) (T₀ : Subgroup C) := by
    rintro x hx h hh
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact hD.E₁_closed hS hA (mem_subgroupOf.mp hx) h.2 ((hmemT₀ _).mp hh)
  have hIH : IH (Nat.card C + 1) := fun Z _ _ _ =>
    coreStatement_iff.mp (coreStatement_of_goldschmidtTheoremA hGold) Z
  have hTsyl : fusionIsSylowIn 2 (T₀ : Subgroup C) ⊤ :=
    ⟨le_top, T₀.isPGroup', fun P' _ hP' hTP => T₀.is_maximal' hP' hTP⟩
  obtain ⟨hConc, -, -, hC3, -⟩ := N16_of N1 _ hIH C T₀ Q' ⊤ T₀ hQ'T hQab hcl hQ'T hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup C := normalClosureIn ⊤ Q' with hMdef
  have hMeq : M = normalClosure (Q' : Set C) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hQ'M : Q' ≤ M := by
    rw [hMeq]
    exact le_normalClosure
  have hOC : goldschmidtOddCore C = ⊥ :=
    (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hO
  have hOM : goldschmidtOddCore M = ⊥ := by
    have hn : (AS76b.oddCoreIn M).Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hMn]
      exact AS76b.normalizer_le_normalizer_oddCoreIn M
    have hle : AS76b.oddCoreIn M ≤ goldschmidtOddCore C :=
      le_sSup ⟨hn, AS76b.odd_card_oddCoreIn M⟩
    rw [hOC, le_bot_iff] at hle
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp hle
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hOM]
  suffices hgoal : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ by
    obtain ⟨ha, hb, -⟩ := hConc
    rw [hgoal, sup_bot_eq] at ha
    have hcl0 : closure {t' : ↥M ⧸ goldschmidtOddCore ↥M |
        t' ∈ ((T₀ : Subgroup C).subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore ↥M)) ⊓
          goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) ∧ t' ^ 2 = 1} = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro t' ⟨ht', -⟩
      rw [hgoal, inf_bot_eq] at ht'
      exact ht'
    rw [hcl0, sup_bot_eq, ha] at hb
    have hMQ : M ≤ Q' := by
      intro m hm
      have h1 : π ⟨m, hm⟩ ∈ (Q'.subgroupOf M).map π := by rw [hb]; exact mem_top _
      obtain ⟨q, hq, hqe⟩ := h1
      have hqm : q = ⟨m, hm⟩ := hπinj hqe
      have := mem_subgroupOf.mp hq
      rwa [hqm] at this
    have hQ'n : Q'.Normal := by
      have : Q' = M := le_antisymm hQ'M hMQ
      rw [this]
      exact hMn
    intro c hc
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have h1 := hQ'n.conj_mem ⟨e, hE₁C he⟩ (mem_subgroupOf.mpr he) ⟨c, hc⟩
      exact mem_subgroupOf.mp h1
    · intro he
      have h1 := hQ'n.conj_mem ⟨c * e * c⁻¹, hE₁C he⟩ (mem_subgroupOf.mpr he) ⟨c, hc⟩⁻¹
      rw [mem_subgroupOf] at h1
      simpa [mul_assoc] using h1
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T₀ hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (T₀ : Subgroup C).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hPM, subgroupOf_map_subtype]
  have hQ'PM : Q'.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun x hx => mem_subgroupOf.2 (hQ'T (mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf T₀ hcl hQ'M PM hQ'PM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (Q'.subgroupOf M) (goldschmidtOddCore M) hQ'PM hclM
  set Ab := (Q'.subgroupOf M).map π with hAb
  have hASbar : Ab ≤ Sbar := by
    rw [hSbar]
    exact map_mono hQ'PM
  have hAab : IsMulCommutative Ab := isMulCommutative_map (isMulCommutative_subgroupOf hQab M) π
  have hO' : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot M
  have hSbarT : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) = barOf M T₀ := by
    rw [hSbar, hPMeq]
    rfl
  have hopen : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), IsComponentOf K.1 ⊤ :=
    fun K => (CFSG.isComponent_iff_open K.1).mp K.2
  have htype : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M),
      goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K => hConc.2.2 K.1 (hopen K)
  have hind : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), InducesOmega1 Ab K.1 Sbar :=
    fun K => by
      rw [hSbarT]
      exact hC3 K.1 (hopen K)
  have hcover : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), ∀ a ∈ Ab, ∃ x ∈ Ab ⊓ K.1,
      ∀ y ∈ K.1, a⁻¹ * y * a = x⁻¹ * y * x :=
    fun K => N17_of N11b _ Sbar Ab K.1 hASbar hAab hclbar hO' (hopen K) (htype K) (hind K)
  have hAO : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ≤ Ab := by
    have h1 : Ab = _ := hConc.2.1
    rw [h1]
    exact le_sup_left
  have hc2 : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, IIbSyl.c1_facts.2.1, map_one]
  have hc1 : c₁ ≠ 1 := fun h1 => IIbSyl.c1_facts.2.2.1 (hfinj (by rw [hfc, h1, map_one]))
  have hE₁8 : Nat.card E₁ = 8 := by
    have hcN : zpowers c₁ ≤ normalizer (V₀ : Set G) :=
      zpowers_le.mpr ((mem_inf.mp (hD.S₁_le hS hD.c₁_mem_S₁)).1)
    have hdisj : V₀ ⊓ zpowers c₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyV, hyc⟩
      rcases eq_one_or_eq_of_mem_zpowers_of_sq hc2 hyc with h1 | h1
      · exact h1 ▸ one_mem _
      · exfalso
        rw [h1, ← hfV0] at hyV
        obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hyV
        exact IIbSyl.c1_ne_vElt _ (hfinj (hw.trans hfc.symm)).symm
    rw [hE₁def, AS76b.card_sup_eq_mul hcN hdisj, hS.card_V₀, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact hc2) hc1]
  have hA8 : Nat.card Ab = 8 := by
    rw [hAb, card_map_of_injective hπinj,
      Nat.card_congr (subgroupOfEquivOfLe hQ'M).toEquiv, hQ',
      Nat.card_congr (subgroupOfEquivOfLe hE₁C).toEquiv, hE₁8]
  have hA2 : ∀ x ∈ Ab, x * x = 1 := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_one π]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    obtain ⟨x, b, he⟩ := hE₁f _ (mem_subgroupOf.mp (mem_subgroupOf.mp hq))
    simp only [coe_mul, coe_one]
    rw [he, ← map_mul, IIbSyl.E1_sq, map_one]
  have hzC : z₀ ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hzE : z₀ ∈ E₁ := mem_sup_left hD.outer.z_mem
  have hzM : (⟨z₀, hzC⟩ : C) ∈ M := hQ'M (mem_subgroupOf.mpr hzE)
  set a₀ := π ⟨⟨z₀, hzC⟩, hzM⟩ with ha₀
  have ha₀A : a₀ ∈ Ab := ⟨⟨⟨z₀, hzC⟩, hzM⟩, mem_subgroupOf.mpr (mem_subgroupOf.mpr hzE), rfl⟩
  have ha₀1 : a₀ ≠ 1 := fun h1 => hD.outer.z_ne (by
    rw [ha₀, ← map_one π] at h1
    exact congrArg (fun m : M => ((m : C) : G)) (hπinj h1))
  have ha₀c : ∀ y : M ⧸ goldschmidtOddCore M, y * a₀ = a₀ * y := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore M) y
    rw [ha₀, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (m : C).2
  set pre : Subgroup (M ⧸ goldschmidtOddCore M) → Subgroup G :=
    fun L => ((L.comap π).map M.subtype).map C.subtype with hpre
  have hmempre : ∀ (L : Subgroup (M ⧸ goldschmidtOddCore M)) (m : M),
      ((m : C) : G) ∈ pre L ↔ π m ∈ L := by
    intro L m
    constructor
    · rintro ⟨_, ⟨m', hm', rfl⟩, he⟩
      have : m' = m := Subtype.ext (Subtype.ext he)
      rw [← this]
      exact hm'
    · intro h
      exact ⟨m, ⟨m, h, rfl⟩, rfl⟩
  have hpreM : ∀ (L : Subgroup (M ⧸ goldschmidtOddCore M)) (y : G), y ∈ pre L →
      ∃ m : M, ((m : C) : G) = y ∧ π m ∈ L := by
    rintro L y ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, rfl, hm⟩
  have hφA : ∀ (s : G) (hs : s ∈ P ⊔ zpowers t),
      Ab.map (Asc76X.conjQuot hMn ⟨s, hS₁C hs⟩).toMonoidHom = Ab := by
    intro s hs
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective
      (MulEquiv.injective _ : Function.Injective
        (Asc76X.conjQuot hMn ⟨s, hS₁C hs⟩).toMonoidHom)).ge
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨⟨⟨s, hS₁C hs⟩ * q * ⟨s, hS₁C hs⟩⁻¹, hMn.conj_mem q q.2 _⟩, ?_, rfl⟩
    show _ ∈ Q'.subgroupOf M
    rw [mem_subgroupOf, mem_subgroupOf]
    exact hD.conj_mem_E₁ hS hs (mem_subgroupOf.mp (mem_subgroupOf.mp hq))
  have hXC : ((rankTwoX A).subgroupOf C).Normal := by
    have : (rankTwoX A).Normal := normalClosure_normal
    exact this.subgroupOf C
  have hc₁X : c₁ ∈ rankTwoX A := by
    have h1 : c₁ ∈ (P ⊔ zpowers t) ⊓ rankTwoX A := by
      rw [← hfS0, ← hfc]
      exact mem_map_of_mem f (MonoidHom.mem_ker.mpr IIbSyl.chi_c1)
    exact h1.2
  have hE₁X : E₁ ≤ rankTwoX A :=
    sup_le (hS.V₀_le_A.trans le_normalClosure) (zpowers_le.mpr hc₁X)
  have hMX : ∀ m : M, ((m : C) : G) ∈ rankTwoX A := by
    intro m
    have hle : M ≤ (rankTwoX A).subgroupOf C := by
      rw [hMeq]
      exact normalClosure_le_normal fun q hq => mem_subgroupOf.mpr (hE₁X (mem_subgroupOf.mp hq))
    exact mem_subgroupOf.mp (hle m.2)
  by_contra hne
  obtain ⟨K₀, hK₀⟩ : ∃ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [goldschmidtLayer, sSup_eq_bot]
    intro K hK
    exact absurd hK (hcon K)
  have hK₀' : CFSG.IsComponent K₀ := (CFSG.isComponent_iff_open K₀).mpr hK₀
  obtain ⟨hinv, hcases⟩ :=
    IIbStep5Gold.component_cases Sbar hO' hASbar hA8 hA2 hAO htype hind hcover
    ha₀A ha₀1 ha₀c ⟨K₀, hK₀'⟩
  have hKs : ∀ (s : G) (hs : s ∈ P ⊔ zpowers t),
      K₀.map (Asc76X.conjQuot hMn ⟨s, hS₁C hs⟩).toMonoidHom = K₀ := fun s hs =>
    hinv _ (hφA s hs)
  have hpreN : ∀ L : Subgroup (M ⧸ goldschmidtOddCore M),
      (∀ (s : G) (hs : s ∈ P ⊔ zpowers t),
        L.map (Asc76X.conjQuot hMn ⟨s, hS₁C hs⟩).toMonoidHom = L) →
      ∀ s ∈ P ⊔ zpowers t, ∀ y ∈ pre L, s * y * s⁻¹ ∈ pre L := by
    intro L hL s hs y hy
    obtain ⟨m, rfl, hm⟩ := hpreM L y hy
    have hm' : (⟨s, hS₁C hs⟩ : C) * m * (⟨s, hS₁C hs⟩ : C)⁻¹ ∈ M := hMn.conj_mem m m.2 _
    have e : s * ((m : C) : G) * s⁻¹ = (((⟨_, hm'⟩ : M) : C) : G) := rfl
    rw [e, hmempre]
    have h1 : π ⟨_, hm'⟩ = Asc76X.conjQuot hMn ⟨s, hS₁C hs⟩ (π m) := rfl
    rw [h1, ← hL s hs]
    exact ⟨π m, hm, rfl⟩
  have hE₁pre : ∀ e ∈ E₁, e ∈ pre Ab := by
    intro e he
    have hq : (⟨e, hE₁C he⟩ : C) ∈ M := hQ'M (mem_subgroupOf.mpr he)
    exact (hmempre Ab ⟨_, hq⟩).mpr ⟨⟨_, hq⟩, mem_subgroupOf.mpr (mem_subgroupOf.mpr he), rfl⟩
  have hpreAb : ∀ y ∈ pre Ab, y ∈ E₁ := by
    intro y hy
    obtain ⟨m, rfl, ⟨q, hq, hqe⟩⟩ := hpreM Ab y hy
    rw [← hπinj hqe]
    exact mem_subgroupOf.mp (mem_subgroupOf.mp hq)
  have hpreS : ∀ m : M, ((m : C) : G) ∈ P ⊔ zpowers t → π m ∈ Sbar := by
    intro m hm
    show π m ∈ (Sbar : Subgroup (M ⧸ goldschmidtOddCore M))
    rw [hSbar]
    exact ⟨m, by rw [hPMeq]; exact mem_subgroupOf.mpr ((hmemT₀ _).mpr hm), rfl⟩
  have hsq : ∀ m : M, ((m : C) : G) * ((m : C) : G) = 1 ∨ ((m : C) : G) * ((m : C) : G) = z₀ →
      π m * π m = 1 ∨ π m * π m = a₀ := by
    intro m hm
    rcases hm with h | h
    · left
      rw [← map_mul, ← map_one π]
      congr 1
      apply Subtype.ext; apply Subtype.ext
      simpa using h
    · right
      rw [← map_mul, ha₀]
      congr 1
      apply Subtype.ext; apply Subtype.ext
      simpa using h
  rcases hcases with ⟨-, hAK, hroot, hnot⟩ | ⟨ha₀K, h4⟩
  ·
    have hE₁K : ∀ e ∈ E₁, e ∈ pre K₀ := fun e he => by
      obtain ⟨m, rfl, hm⟩ := hpreM Ab e (hE₁pre e he)
      exact (hmempre K₀ m).mpr (hAK hm)
    have hYroot : ∀ y ∈ pre K₀, y ∈ P ⊔ zpowers t → y * y = 1 ∨ y * y = z₀ → y ∈ E₁ := by
      intro y hy hyS hy2
      obtain ⟨m, rfl, hm⟩ := hpreM K₀ y hy
      exact hpreAb _ ((hmempre Ab m).mpr (hroot _ ⟨hpreS m hyS, hm⟩ (hsq m hy2)))
    obtain ⟨ū, hū, hūA⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    obtain ⟨hūS, hūK⟩ := mem_inf.mp hū
    rw [hSbar] at hūS
    obtain ⟨u, huPM, rfl⟩ := hūS
    have hUS : ((u : C) : G) ∈ P ⊔ zpowers t := by
      rw [hPMeq] at huPM
      exact (hmemT₀ _).mp (mem_subgroupOf.mp huPM)
    have hUY : ((u : C) : G) ∈ pre K₀ := (hmempre K₀ u).mpr hūK
    have hUE : ((u : C) : G) ∉ E₁ := fun h => hūA ((hmempre Ab u).mp (hE₁pre _ h))
    obtain ⟨y, hy⟩ : ((u : C) : G) ∈ f.range := hfrange ▸ hUS
    have hychi : IIbSyl.chi y = 1 := by
      have h1 : f y ∈ IIbSyl.S0.map f := by
        rw [hfS0, hy]
        exact ⟨hUS, hMX u⟩
      obtain ⟨y', hy', he⟩ := h1
      rw [← hfinj he]
      exact hy'
    have hyE : ∀ x, y ≠ IIbSyl.vElt x 0 ∧ y ≠ IIbSyl.c1 * IIbSyl.vElt x 0 := fun x =>
      ⟨fun h => hUE (by rw [← hy, h]; exact hfE₁ x false),
        fun h => hUE (by rw [← hy, h]; exact hfE₁ x true)⟩
    obtain ⟨x, b, c, hw2, hwE⟩ := IIbSyl.witness y hychi hyE
    have hσS : f IIbSyl.sigma ∈ P ⊔ zpowers t := hfS _
    have hwY : f (cond c (y * IIbSyl.sigma * y⁻¹ * IIbSyl.sigma⁻¹) y *
        cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) ∈ pre K₀ := by
      rw [map_mul]
      refine mul_mem ?_ (hE₁K _ (hfE₁ x b))
      cases c
      · rw [Bool.cond_false, hy]
        exact hUY
      · rw [Bool.cond_true, map_mul, map_mul, map_mul, map_inv, map_inv, hy,
          show ((u : C) : G) * f IIbSyl.sigma * ((u : C) : G)⁻¹ * (f IIbSyl.sigma)⁻¹ =
            ((u : C) : G) * (f IIbSyl.sigma * ((u : C) : G)⁻¹ * (f IIbSyl.sigma)⁻¹) by group]
        exact mul_mem hUY (hpreN K₀ hKs _ hσS _ (inv_mem hUY))
    have hw2' : f (cond c (y * IIbSyl.sigma * y⁻¹ * IIbSyl.sigma⁻¹) y *
          cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) *
        f (cond c (y * IIbSyl.sigma * y⁻¹ * IIbSyl.sigma⁻¹) y *
          cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) = 1 ∨
        f (cond c (y * IIbSyl.sigma * y⁻¹ * IIbSyl.sigma⁻¹) y *
          cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) *
        f (cond c (y * IIbSyl.sigma * y⁻¹ * IIbSyl.sigma⁻¹) y *
          cond b (IIbSyl.c1 * IIbSyl.vElt x 0) (IIbSyl.vElt x 0)) = z₀ := by
      rw [← map_mul, ← hfz]
      rcases hw2 with h | h
      · left; rw [h, map_one]
      · right; rw [h]
    have hwE₁ := hYroot _ hwY (hfS _) hw2'
    obtain ⟨x', b', he⟩ := hE₁f _ hwE₁
    have he' := hfinj he
    cases b'
    · exact (hwE x').1 he'
    · exact (hwE x').2 he'
  ·
    have hDinv := hpreN (Ab ⊓ K₀) (fun s hs => by
      rw [Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _), hφA s hs, hKs s hs])
    have hDE : ∀ y ∈ pre (Ab ⊓ K₀), y ∈ E₁ := fun y hy => by
      obtain ⟨m, rfl, hm⟩ := hpreM _ y hy
      exact hpreAb _ ((hmempre Ab m).mpr hm.1)
    have hD4 : Nat.card (pre (Ab ⊓ K₀)) = 4 := by
      have h1 := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective
        (goldschmidtOddCore M)) (Ab ⊓ K₀)
      have h2 : Nat.card ((Ab ⊓ K₀).comap π) = 4 := by
        have e : Nat.card (((Ab ⊓ K₀).comap π).map π) = Nat.card ((Ab ⊓ K₀).comap π) :=
          card_map_of_injective hπinj
        rw [h1] at e
        rw [← e]
        exact h4
      change Nat.card ((((Ab ⊓ K₀).comap π).map M.subtype).map C.subtype) = 4
      rw [card_map_of_injective C.subtype_injective, card_map_of_injective M.subtype_injective,
        h2]
    have hD2 : ∀ y ∈ pre (Ab ⊓ K₀), y * y = 1 := fun y hy => by
      obtain ⟨x, b, he⟩ := hE₁f y (hDE y hy)
      rw [he, ← map_mul, IIbSyl.E1_sq, map_one]
    have hzD : z₀ ∉ pre (Ab ⊓ K₀) := fun h => ha₀K (by
      have := (hmempre (Ab ⊓ K₀) ⟨⟨z₀, hzC⟩, hzM⟩).mp h
      exact this.2)
    obtain ⟨d₁, hd₁, hd₁1, -⟩ := exists_ne_one_ne hD4 hD2 (one_mem _)
    obtain ⟨d₂, hd₂, hd₂1, hd₂d₁⟩ := exists_ne_one_ne hD4 hD2 hd₁
    have hd₁₂ : d₁ * d₂ ∈ pre (Ab ⊓ K₀) := mul_mem hd₁ hd₂
    obtain ⟨x₁, b₁, rfl⟩ := hE₁f d₁ (hDE d₁ hd₁)
    obtain ⟨x₂, b₂, rfl⟩ := hE₁f _ (hDE _ hd₂)
    have hne1 : ∀ {m : IIbSyl}, f m ≠ 1 → m ≠ 1 := fun h he => h (by rw [he, map_one])
    have hnez : ∀ {m : IIbSyl}, f m ∈ pre (Ab ⊓ K₀) → m ≠ IIbSyl.z0 := fun h he =>
      hzD (by rw [← hfz, ← he]; exact h)
    obtain ⟨s, hsL, hs1, hs2, hs3, hs4⟩ := IIbSyl.no_normal_complement x₁ x₂ b₁ b₂
      (hne1 hd₁1) (hnez hd₁) (hne1 hd₂1) (hnez hd₂) (fun he => hd₂d₁ (by rw [he]))
      (fun he => hzD (by rw [← hfz, ← he, map_mul]; exact hd₁₂))
    have hsd := hDinv (f s) (hfS s) _ hd₁
    rw [← map_inv, ← map_mul, ← map_mul] at hsd
    rcases mem_four hD4 hD2 hd₁ hd₂ hd₁1 hd₂1 hd₂d₁.symm hsd with e | e | e | e
    · exact hs1 (hfinj (by rw [e, map_one]))
    · exact hs2 (hfinj e)
    · exact hs3 (hfinj e)
    · exact hs4 (hfinj (by rw [e, map_mul]))

end IIbData

end CFSG.ComponentClassification.RankTwoAltFive

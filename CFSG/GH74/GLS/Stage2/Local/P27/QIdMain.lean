module

public import CFSG.GH74.GLS.Stage2.Local.P27.QIdCore
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdTransport
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement

section Aux

theorem isL2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {P : ℕ → Prop}
    (h : IsL2 X P) : IsL2 Y P := by
  obtain ⟨F, _, _, hP, ⟨e'⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hP, ⟨e.symm.trans e'⟩⟩

theorem isSimpleGroup_of_isL2 {X : Type} [Group X] {q : ℕ} (hq3 : 3 < q)
    (h : IsL2 X (fun r => r = q)) : IsSimpleGroup X := by
  obtain ⟨F, _, _, hP, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by rw [hP]; omega
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans (L2.equivPSL F)).isSimpleGroup

theorem isL2_range_of_odd_ker {L K : Type} [Group L] [Finite L] [Group K] (f : L →* K)
    (hker : Odd (Nat.card f.ker)) (hO : ∀ o ∈ pPrimeCore 2 L, f o = 1) {P : ℕ → Prop}
    (h : IsL2 (L ⧸ pPrimeCore 2 L) P) : IsL2 ↥f.range P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : f.ker ≤ pPrimeCore 2 L := by
    have hn : f.ker.Normal := MonoidHom.normal_ker f
    exact le_sSup ⟨hn, Nat.coprime_two_left.2 hker⟩
  have hle' : pPrimeCore 2 L ≤ f.ker := fun o ho => hO o ho
  have heq : pPrimeCore 2 L = f.ker := le_antisymm hle' hle
  have e : (L ⧸ pPrimeCore 2 L) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivRange f)
  exact isL2_of_mulEquiv e h

theorem card_dvd_range_of_odd_ker {L K : Type} [Group L] [Finite L] [Group K] (f : L →* K)
    (hker : Odd (Nat.card f.ker)) : Nat.card (L ⧸ pPrimeCore 2 L) ∣ Nat.card ↥f.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : f.ker ≤ pPrimeCore 2 L := by
    have hn : f.ker.Normal := MonoidHom.normal_ker f
    exact le_sSup ⟨hn, Nat.coprime_two_left.2 hker⟩
  let g : (L ⧸ f.ker) →* (L ⧸ pPrimeCore 2 L) :=
    QuotientGroup.map f.ker (pPrimeCore 2 L) (MonoidHom.id L) (by simpa using hle)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(a : L ⧸ f.ker), rfl⟩
  have h1 := Subgroup.card_dvd_of_surjective hg
  have h2 : Nat.card (L ⧸ f.ker) = Nat.card ↥f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rwa [h2] at h1

theorem padicValNat_card_eq_quotient (L : Type) [Group L] [Finite L] :
    padicValNat 2 (Nat.card L) = padicValNat 2 (Nat.card (L ⧸ pPrimeCore 2 L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 L)
  have hodd : Odd (Nat.card (pPrimeCore 2 L)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := L))
  have h0 : padicValNat 2 (Nat.card (pPrimeCore 2 L)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by
      intro hd
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := hd
      omega)
  rw [h, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h0, add_zero]

theorem isSimpleGroup_of_hK {K : Type} [Group K]
    (hK : (∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (K ≃* L2 F)) ∨
      Nonempty (K ≃* alternatingGroup (Fin 7))) : IsSimpleGroup K := by
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h4 : 4 ≤ Nat.card F := by have := hF.2; omega
    have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (e.trans (L2.equivPSL F)).isSimpleGroup
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

end Aux

variable {X : Type} [Group X] [Finite X]

theorem qdich (Y M : Subgroup X) [Y.Normal] [M.Normal] (hM : Odd (Nat.card M)) (hMY : M ≤ Y)
    (hL : pLayer X 2 ≤ Y)
    {K : Type} [Group K] [Finite K]
    (hK : (∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (K ≃* L2 F)) ∨
      Nonempty (K ≃* alternatingGroup (Fin 7)))
    (θ : ↥Y →* K) (hθ : ∀ y : ↥Y, θ y = 1 ↔ (y : X) ∈ M)
    (ā : MulAut K) (hā : ā * ā = 1) (hθfix : ∀ y : ↥Y, ā (θ y) = θ y)
    (hlift : ∀ k : K, ā k = k → ∃ y : ↥Y, θ y = k)
    (ht : ∃ t ∈ pLayer X 2, orderOf t = 2)
    {q : ℕ} (hq : Odd q) (hq3 : 3 < q)
    (hIL2 : IsL2 (↥(pLayer X 2) ⧸ pPrimeCore 2 ↥(pLayer X 2)) (fun r => r = q)) :
    (IsL2 K (fun r => r = q) ∧
        padicValNat 2 (Nat.card K) = padicValNat 2 (Nat.card ↥(pLayer X 2))) ∨
      (padicValNat 2 (Nat.card K) = padicValNat 2 (Nat.card ↥(pLayer X 2)) + 1 ∧
        (IsL2 K (fun r => r = q ^ 2) ∨ (q = 5 ∧ Nonempty (K ≃* alternatingGroup (Fin 7))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup X := pLayer X 2 with hLdef
  let f : ↥L →* K := θ.comp (Subgroup.inclusion hL)
  set Iθ : Subgroup K := f.range with hIθ
  have hperfL : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect X)
  have hperf : ⁅Iθ, Iθ⁆ = Iθ := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)
  have hfix : ∀ g ∈ Iθ, ā g = g := by
    rintro _ ⟨l, rfl⟩
    exact hθfix _
  obtain ⟨t, htL, ht2⟩ := ht
  have hft1 : f ⟨t, htL⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨t, hL htL⟩ : ↥Y) ∈ θ.ker := h1
    have h3 : t ∈ M := (hθ _).1 h2
    have h4 : orderOf (⟨t, h3⟩ : ↥M) ∣ Nat.card ↥M := orderOf_dvd_natCard _
    have h5 : orderOf (⟨t, h3⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    rw [h5] at h4
    obtain ⟨k, hk⟩ := hM
    obtain ⟨m, hm⟩ := h4
    omega
  have hne : Iθ ≠ ⊥ := by
    intro h
    apply hft1
    have : f ⟨t, htL⟩ ∈ Iθ := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hft2 : orderOf (f ⟨t, htL⟩) = 2 := by
    have hd : orderOf (f ⟨t, htL⟩) ∣ orderOf (⟨t, htL⟩ : ↥L) := orderOf_map_dvd f _
    have h5 : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    rw [h5] at hd
    have := (Nat.dvd_prime Nat.prime_two).1 hd
    rcases this with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hft1
    · exact h
  have hrange : θ.range = fixedSubgroup K ā := by
    ext k
    constructor
    · rintro ⟨y, rfl⟩
      exact hθfix y
    · intro hk
      exact hlift k hk
  have LH : ∀ Ω : Subgroup K, Ω ≤ fixedSubgroup K ā →
      (Ω.subgroupOf (fixedSubgroup K ā)).Normal → IsQuasisimple ↥Ω → Ω ≤ Iθ := by
    intro Ω hΩC hΩn hΩq
    rw [← hrange] at hΩC hΩn
    have h := layer_transport Y M hM hMY hL θ hθ Ω hΩC hΩn hΩq
    refine h.trans ?_
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨l.1, hl⟩, rfl⟩
  have hker : Odd (Nat.card f.ker) := by
    have hle : f.ker.map L.subtype ≤ M := by
      rintro _ ⟨l, hl, rfl⟩
      exact (hθ ⟨l.1, hL l.2⟩).1 hl
    have hdvd : Nat.card f.ker ∣ Nat.card ↥M := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hM hdvd
  have hvL : padicValNat 2 (Nat.card ↥L) = padicValNat 2 (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) :=
    padicValNat_card_eq_quotient ↥L
  have hfO : IsSimpleGroup ↥Iθ → ∀ o ∈ pPrimeCore 2 ↥L, f o = 1 := by
    intro hs
    set S : Subgroup K := (pPrimeCore 2 ↥L).map f with hS
    have hSle : S ≤ Iθ := fun _ ⟨o, _, h⟩ => ⟨o, h⟩
    have hSn : (S.subgroupOf Iθ).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
      obtain ⟨l, hl⟩ : (g : K) ∈ f.range := g.2
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_map.2 ⟨l * o * l⁻¹, (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem o ho l, ?_⟩
      rw [map_mul, map_mul, map_inv, hoeq, hl]
      rfl
    have := hs
    have := hSn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf Iθ) with hb | ht'
    · intro o ho
      have : f o ∈ S := ⟨o, ho, rfl⟩
      have h2 : (⟨f o, hSle this⟩ : ↥Iθ) ∈ S.subgroupOf Iθ := this
      rw [hb, Subgroup.mem_bot] at h2
      exact congrArg Subtype.val h2
    · exfalso
      have hsurj : Function.Surjective ((f.domRestrict (pPrimeCore 2 ↥L)).codRestrict Iθ
          (fun o => ⟨o.1, rfl⟩)) := by
        intro g
        have : (g : K) ∈ S := by
          have h2 : g ∈ S.subgroupOf Iθ := by rw [ht']; trivial
          exact h2
        obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.1 this
        exact ⟨⟨o, ho⟩, Subtype.ext hoeq⟩
      have hd := Subgroup.card_dvd_of_surjective hsurj
      have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥L)) :=
        Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥L))
      have hoddI : Odd (Nat.card ↥Iθ) := Odd.of_dvd_nat hodd hd
      have h2d : orderOf (⟨f ⟨t, htL⟩, ⟨_, rfl⟩⟩ : ↥Iθ) ∣ Nat.card ↥Iθ := orderOf_dvd_natCard _
      have h5 : orderOf (⟨f ⟨t, htL⟩, ⟨_, rfl⟩⟩ : ↥Iθ) = 2 := by
        have := orderOf_injective Iθ.subtype Iθ.subtype_injective
          (⟨f ⟨t, htL⟩, ⟨_, rfl⟩⟩ : ↥Iθ)
        rw [← this]
        exact hft2
      rw [h5] at h2d
      obtain ⟨k, hk⟩ := hoddI
      obtain ⟨m, hm⟩ := h2d
      omega
  rcases qcore hK ā hā Iθ hperf hne hfix LH with
    ⟨-, hIθtop⟩ | ⟨-, q₀, hq₀odd, hq₀3, hKq₀, hIq₀⟩ | ⟨-, hA7, hdvd⟩
  ·
    left
    have hsK : IsSimpleGroup K := isSimpleGroup_of_hK hK
    have hsI : IsSimpleGroup ↥Iθ := by
      rw [hIθtop]
      exact (Subgroup.topEquiv (G := K)).isSimpleGroup
    have hL2I := isL2_range_of_odd_ker f hker (hfO hsI) hIL2
    have hL2K : IsL2 K (fun r => r = q) := by
      rw [← hIθ] at hL2I
      refine isL2_of_mulEquiv ?_ hL2I
      rw [hIθtop]
      exact Subgroup.topEquiv
    refine ⟨hL2K, ?_⟩
    rw [hvL, card_isL2 hq hL2K, card_isL2 hq hIL2]
  ·
    right
    have hsI : IsSimpleGroup ↥Iθ := isSimpleGroup_of_isL2 hq₀3 hIq₀
    have hL2I := isL2_range_of_odd_ker f hker (hfO hsI) hIL2
    have hqq : q₀ = q := isL2_odd_unique hq₀odd hq hIq₀ hL2I
    subst hqq
    refine ⟨?_, Or.inl hKq₀⟩
    rw [hvL]
    exact padicValNat_isL2_sq hq₀odd hKq₀ hIL2
  ·
    right
    have hd2 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card ↥Iθ := card_dvd_range_of_odd_ker f hker
    have hcardL2 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = q * (q ^ 2 - 1) / 2 := card_isL2 hq hIL2
    have hq5 : q = 5 := eq_five_of_isL2_dvd_sixty hq hq3 hIL2 (hd2.trans hdvd)
    subst hq5
    refine ⟨?_, Or.inr ⟨rfl, hA7⟩⟩
    obtain ⟨eA⟩ := hA7
    rw [Nat.card_congr eA.toEquiv, padicValNat_alternating_seven, hvL,
      padicValNat_isL2_five hIL2]

end CFSG.GH74.GLS.Stage2.Local.P27.QId

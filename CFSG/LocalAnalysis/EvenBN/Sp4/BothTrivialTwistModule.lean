module

public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.SL2Modules
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]

theorem eq_one_of_pow_two_pow_of_odd {H : Type*} [Group H] {g : H} {j : ℕ} (hg : g ^ 2 ^ j = 1)
    (hodd : Odd (orderOf g)) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hg
  obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hi : i = 0 := by
    by_contra hne
    rw [hi'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hi, pow_zero] at hi'
  exact orderOf_eq_one_iff.mp hi'

theorem natural_module_facts {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    {N X Z S₀ F₀ : Subgroup G}
    (hNX : N ≤ normalizer (X : Set G))
    (hX2 : ∀ x ∈ X, x * x = 1) (hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hZX : Z ≤ X) (hZc : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n)
    (hXcard : Nat.card X = Nat.card Z * (2 ^ m) ^ 2)
    (π : N →* SL(2, k)) (hπ : Function.Surjective π)
    (hπX : ∀ n : N, π n = 1 ↔ (n : G) ∈ X)
    (hS₀N : S₀ ≤ N) (hπS : ∀ n : N, (n : G) ∈ S₀ ↔ π n ∈ upperUnipotent k)
    (hZF : Z ≤ F₀) (hF₀X : F₀ ≤ X)
    (hF₀ : ∀ x ∈ X, x ∈ F₀ ↔ ∀ s ∈ S₀, s * x = x * s)
    (hF₀card : Nat.card F₀ = Nat.card Z * 2 ^ m) :
    (∀ n ∈ N, n ≠ 1 → Odd (orderOf n) → ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ Z → x ∈ Z) ∧
    (∀ s ∈ S₀, s ∉ X → ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Z → x ∈ F₀) ∧
    (∀ g ∈ N, (∀ f ∈ F₀, g * f * g⁻¹ * f⁻¹ ∈ Z) → g ∈ S₀) ∧
    (∀ n ∈ N, n ∉ X → Odd (orderOf n) → ∀ s ∈ S₀, n * s * n⁻¹ * s⁻¹ ∈ X → s ∈ X) ∧
    (3 ∣ 2 ^ m - 1 → ∃ ω ∈ N, ω ∈ normalizer (S₀ : Set G) ∧ ω ∉ X ∧ ω * ω * ω = 1) := by
  letI : CommGroup ↥X := { (inferInstance : Group ↥X) with
    mul_comm := fun a b => Subtype.ext (hXab a a.2 b b.2) }
  set Z' : Subgroup ↥X := Z.subgroupOf X with hZ'
  haveI hZ'n : Z'.Normal := Subgroup.normal_of_comm Z'
  have hXZ : X ≤ normalizer (Z : Set G) := fun x hx => by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hXab x hx z (hZX hz), mul_inv_cancel_right]
      exact hz
    · intro hz
      have hz' : z ∈ X := by
        have h1 : x * z * x⁻¹ ∈ X := hz |> fun h => hZX h
        have := mul_mem (mul_mem (inv_mem hx) h1) hx
        rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at this
      rw [hXab x hx z hz', mul_inv_cancel_right] at hz
      exact hz
  set ρY := CFSG.SL2MinimalFaithful.conjAction hNX with hρY
  have hkerX : π.ker ≤ ρY.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hnX : (n : G) ∈ X := (hπX n).mp hn
    ext x
    change (n : G) * x * (n : G)⁻¹ = x
    rw [hXab _ hnX x x.2, mul_inv_cancel_right]
  set ρX : SL(2, k) →* MulAut ↥X := MonoidHom.liftOfSurjective π hπ ⟨ρY, hkerX⟩ with hρXdef
  have hρX : ∀ (n : N) (x : X), ((ρX (π n) x : ↥X) : G) = (n : G) * x * (n : G)⁻¹ := by
    intro n x
    have := MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨ρY, hkerX⟩ n
    change ((((π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
      ⟨ρY, hkerX⟩) (π n)) x : ↥X) : G) = _
    rw [this]
    rfl
  have hZfix : ∀ (g : SL(2, k)), ∀ z ∈ Z', ρX g z = z := by
    intro g z hz
    obtain ⟨n, rfl⟩ := hπ g
    apply Subtype.ext
    rw [hρX]
    have hz' : (z : G) ∈ Z := hz
    rw [hZc n n.2 z hz', mul_inv_cancel_right]
  have hmapX : ∀ g, Z'.map (ρX g : ↥X →* ↥X) = Z' := by
    intro g
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change ρX g z ∈ Z'
      rw [hZfix g z hz]
      exact hz
    · intro z hz
      exact ⟨z, hz, hZfix g z hz⟩
  set ρ := CFSG.SL2MinimalFaithful.quotientAction ρX Z' hmapX with hρdef
  have hfix : ∀ (n : N) (x : X), ρ (π n) (x : ↥X ⧸ Z') = x ↔
      (n : G) * (x : G) * (n : G)⁻¹ * (x : G)⁻¹ ∈ Z := by
    intro n x
    rw [CFSG.SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq, mem_subgroupOf]
    change ((ρX (π n) x : ↥X) : G)⁻¹ * x ∈ Z ↔ _
    rw [hρX]
    exact CFSG.SL2MinimalFaithful.inv_mul_mem_iff hXZ x.2
  have hZ'card : Nat.card Z' = Nat.card Z := Nat.card_congr (subgroupOfEquivOfLe hZX).toEquiv
  have hAcard : Nat.card (↥X ⧸ Z') = (2 ^ m) ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hZ'card, hXcard, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hρne : ρ ≠ 1 := by
    intro h1
    have hδ : ∀ (g : SL(2, k)) (v : ↥X), v⁻¹ * ρX g v ∈
        CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρX ⊤ := by
      intro g v
      obtain ⟨n, rfl⟩ := hπ g
      have h2 : ρ (π n) (v : ↥X ⧸ Z') = v := by rw [h1]; rfl
      have h3 := (hfix n v).mp h2
      have h4 : v⁻¹ * ρX (π n) v ∈ Z' := by
        have hxn : (n : G) * v * (n : G)⁻¹ ∈ X := by
          rw [← hρX n v]
          exact (ρX (π n) v).2
        have e := hXab (v : G)⁻¹ (inv_mem v.2) _ hxn
        change (v : G)⁻¹ * ((ρX (π n) v : ↥X) : G) ∈ Z
        rw [hρX, e]
        exact h3
      intro g' _
      exact hZfix g' _ h4
    have h5 := CFSG.LocalAnalysis.EvenBN.U4.eq_one_of_forall_inv_mul_apply_mem
      (CFSG.LocalAnalysis.EvenBN.U4.exists_finset_card_four hk hm) ρX hδ
    have h6 : ∀ s ∈ S₀, ∀ x ∈ X, s * x = x * s := by
      intro s hs x hx
      have := hρX ⟨s, hS₀N hs⟩ ⟨x, hx⟩
      rw [h5, MonoidHom.one_apply, MulAut.one_apply] at this
      change x = s * x * s⁻¹ at this
      calc s * x = (s * x * s⁻¹) * s := by group
        _ = x * s := by rw [← this]
    have h7 : X ≤ F₀ := fun x hx => (hF₀ x hx).mpr fun s hs => h6 s hs x hx
    have h8 := Subgroup.card_le_of_le h7
    rw [hXcard, hF₀card] at h8
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    nlinarith
  set B := upperUnipotent k with hBdef
  set F' : Subgroup (↥X ⧸ Z') := (F₀.subgroupOf X).map (QuotientGroup.mk' Z') with hF'
  have hZF' : Z' ≤ F₀.subgroupOf X := fun z hz => hZF hz
  have hF'card : Nat.card F' = 2 ^ m := by
    have h := CFSG.SignalizerFunctorTheorem.McBride.card_map_mk'_mul_card hZF'
    rw [hZ'card, Nat.card_congr (subgroupOfEquivOfLe hF₀X).toEquiv, hF₀card, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hF'le : F' ≤ CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρ B := by
    rintro _ ⟨f, hf, rfl⟩ b hb
    obtain ⟨n, rfl⟩ := hπ b
    have hnS : (n : G) ∈ S₀ := (hπS n).mpr hb
    have hfF : (f : G) ∈ F₀ := hf
    rw [QuotientGroup.mk'_apply]
    refine (hfix n f).mpr ?_
    rw [(hF₀ f f.2).mp hfF n hnS, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hBle : 2 ^ m ≤ Nat.card
      (CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρ B) :=
    hF'card ▸ Subgroup.card_le_of_le hF'le
  obtain ⟨hD, hBcard, hinj, hcompl, htorus, hreg, htrans, hstabB, hsyl⟩ :=
    CFSG.LocalAnalysis.EvenBN.U4.gomi_natural_module hk hm hm3 hAcard ρ hρne hBle
  have hFix : F' = CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρ B :=
    Subgroup.eq_of_le_of_card_ge hF'le (by rw [hBcard, hF'card])
  have hBcardk : Nat.card B = Nat.card k := card_upperUnipotent k
  have hcls : ∀ (x : G) (hx : x ∈ X), ((⟨x, hx⟩ : ↥X) : ↥X ⧸ Z') = 1 ↔ x ∈ Z := fun x hx =>
    QuotientGroup.eq_one_iff (N := Z') ⟨x, hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro n hn hn1 hodd x hx hxZ
    by_contra hxnZ
    have hx1 : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ Z') ≠ 1 := fun h => hxnZ ((hcls x hx).mp h)
    have hfx := (hfix ⟨n, hn⟩ ⟨x, hx⟩).mpr hxZ
    obtain ⟨P, hP⟩ := hsyl _ hx1
    have hPn : π ⟨n, hn⟩ ∈ P := (hP _).mp hfx
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨π ⟨n, hn⟩, hPn⟩
    have hj' : (π ⟨n, hn⟩) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hodd' : Odd (orderOf (π ⟨n, hn⟩)) :=
      hodd.of_dvd_nat ((orderOf_map_dvd π ⟨n, hn⟩).trans (by rw [← Subgroup.orderOf_coe]))
    have h1 : π ⟨n, hn⟩ = 1 := eq_one_of_pow_two_pow_of_odd hj' hodd'
    have hnX : n ∈ X := (hπX ⟨n, hn⟩).mp h1
    have hnn : n ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hX2 n hnX
    exact hn1 (eq_one_of_pow_two_pow_of_odd hnn hodd)
  ·
    intro s hs hsX x hx hxZ
    by_cases hx1 : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ Z') = 1
    · exact hZF ((hcls x hx).mp hx1)
    · have hsN := hS₀N hs
      have hπs : π ⟨s, hsN⟩ ∈ B := (hπS ⟨s, hsN⟩).mp hs
      have hπs1 : π ⟨s, hsN⟩ ≠ 1 := fun h => hsX ((hπX _).mp h)
      have hfx := (hfix ⟨s, hsN⟩ ⟨x, hx⟩).mpr hxZ
      obtain ⟨P, hP⟩ := hsyl _ hx1
      have hPs : π ⟨s, hsN⟩ ∈ P := (hP _).mp hfx
      have hPcard : Nat.card P = Nat.card k :=
        CFSG.LocalAnalysis.EvenBN.Common.card_sylow_two_eq (MulEquiv.refl SL(2, k)) P
      have hPB : (P : Subgroup SL(2, k)) = B :=
        CFSG.LocalAnalysis.EvenBN.Common.eq_of_mem_of_card (X := ⊤) (S := (P : Subgroup _))
          (S' := B) Subgroup.topEquiv le_top le_top hPcard hBcardk hPs hπs hπs1
      have hxfix : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ Z') ∈
          CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρ B := by
        intro d hd
        have hdP : d ∈ (P : Subgroup SL(2, k)) := by rw [hPB]; exact hd
        exact (hP d).mpr hdP
      rw [← hFix] at hxfix
      obtain ⟨f, hf, hfx'⟩ := hxfix
      have hfx'' := QuotientGroup.eq.mp hfx'
      have hf' : (f : G) ∈ F₀ := hf
      have h1 : (f : G)⁻¹ * x ∈ Z := hfx''
      have := mul_mem hf' (hZF h1)
      rwa [mul_inv_cancel_left] at this
  ·
    intro g hg hgF
    obtain ⟨f, hf, hfZ⟩ : ∃ f ∈ F₀, f ∉ Z := by
      by_contra hcon
      push Not at hcon
      have h1 : F₀ ≤ Z := fun f hf => hcon f hf
      have h2 := Subgroup.card_le_of_le h1
      rw [hF₀card] at h2
      nlinarith [Nat.card_pos (α := Z)]
    have hfX := hF₀X hf
    have hf1 : ((⟨f, hfX⟩ : ↥X) : ↥X ⧸ Z') ≠ 1 := fun h => hfZ ((hcls f hfX).mp h)
    have hmem : ((⟨f, hfX⟩ : ↥X) : ↥X ⧸ Z') ∈
        CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.actionFixed ρ B := by
      rw [← hFix]
      exact ⟨⟨f, hfX⟩, hf, rfl⟩
    have hfx := (hfix ⟨g, hg⟩ ⟨f, hfX⟩).mpr (hgF f hf)
    exact (hπS ⟨g, hg⟩).mpr ((hstabB _ hmem hf1 (π ⟨g, hg⟩)).mp hfx)
  ·
    intro n hn hnX hodd s hs hcomm
    by_contra hsX
    have hsN := hS₀N hs
    have hπs : π ⟨s, hsN⟩ ∈ B := (hπS ⟨s, hsN⟩).mp hs
    have hπs1 : π ⟨s, hsN⟩ ≠ 1 := fun h => hsX ((hπX _).mp h)
    have hc : π ⟨n, hn⟩ ∈ centralizer ({π ⟨s, hsN⟩} : Set SL(2, k)) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : π (⟨n, hn⟩ * ⟨s, hsN⟩ * ⟨n, hn⟩⁻¹ * ⟨s, hsN⟩⁻¹) = 1 := (hπX _).mpr hcomm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : π ⟨n, hn⟩ * π ⟨s, hsN⟩ * (π ⟨n, hn⟩)⁻¹ = π ⟨s, hsN⟩ := mul_inv_eq_one.mp h1
      calc π ⟨n, hn⟩ * π ⟨s, hsN⟩
          = (π ⟨n, hn⟩ * π ⟨s, hsN⟩ * (π ⟨n, hn⟩)⁻¹) * π ⟨n, hn⟩ := by group
        _ = π ⟨s, hsN⟩ * π ⟨n, hn⟩ := by rw [h2]
    rw [CFSG.LocalAnalysis.EvenBN.Common.centralizer_eq_of_mem_of_card
      (by rw [hBcardk]) hπs hπs1] at hc
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff k).mp hc
    have h2 : (π ⟨n, hn⟩) ^ 2 ^ 1 = 1 := by
      rw [ht, pow_one, pow_two, upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero]
    have hodd' : Odd (orderOf (π ⟨n, hn⟩)) :=
      hodd.of_dvd_nat ((orderOf_map_dvd π ⟨n, hn⟩).trans (by rw [← Subgroup.orderOf_coe]))
    exact hnX ((hπX _).mp (eq_one_of_pow_two_pow_of_odd h2 hodd'))
  ·
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hunits : 3 ∣ Nat.card kˣ := by
      rw [Nat.card_units, hk]
      exact h3
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) 3 hunits
    set d : SL(2, k) := CFSG.Timmesfeld.ARS.NaturalModule.diagElt a with hd
    have ha3 : a * a * a = 1 := by
      have := pow_orderOf_eq_one a
      rw [ha] at this
      simpa [pow_succ] using this
    have hd3 : d * d * d = 1 := by
      rw [hd, CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt,
        CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt, ha3,
        CFSG.Timmesfeld.ARS.NaturalModule.diagElt_one]
    have hd1 : d ≠ 1 := by
      intro h
      have h1 : a = 1 := by
        have := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
        simp only [hd, CFSG.Timmesfeld.ARS.NaturalModule.coe_diagElt] at this
        exact Units.ext (by simpa using this)
      rw [h1, orderOf_one] at ha
      omega
    have hdB : ∀ b ∈ B, d * b * d⁻¹ ∈ B := by
      intro b hb
      obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).mp hb
      rw [hd, CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mul_upperElt, mul_assoc, mul_inv_cancel,
        mul_one]
      exact (mem_upperUnipotent_iff k).mpr ⟨_, rfl⟩
    obtain ⟨n₀, hn₀⟩ := hπ d
    have hn₀3 : π (n₀ ^ 3) = 1 := by rw [map_pow, hn₀, pow_three', hd3]
    have hn₀3X : ((n₀ ^ 3 : N) : G) ∈ X := (hπX _).mp hn₀3
    have hn₀6 : (n₀ : G) ^ 12 = 1 := by
      have h := hX2 _ hn₀3X
      rw [Subgroup.coe_pow] at h
      calc (n₀ : G) ^ 12 = (n₀ ^ 3 * n₀ ^ 3) ^ 2 := by group
        _ = 1 := by rw [h]; group
    have hπ4 : π (n₀ ^ 4) = d := by
      rw [map_pow, hn₀, pow_succ, pow_three', hd3, one_mul]
    have hω3 : (n₀ : G) ^ 4 * (n₀ : G) ^ 4 * (n₀ : G) ^ 4 = 1 := by
      rw [← hn₀6]; group
    have hconj : ∀ s ∈ S₀, (n₀ : G) ^ 4 * s * ((n₀ : G) ^ 4)⁻¹ ∈ S₀ := by
      intro s hs
      have hsN := hS₀N hs
      have hπs : π ⟨s, hsN⟩ ∈ B := (hπS ⟨s, hsN⟩).mp hs
      have hmem : (((n₀ ^ 4 : N) * ⟨s, hsN⟩ * (n₀ ^ 4 : N)⁻¹ : N) : G) ∈ S₀ := by
        rw [hπS]
        rw [map_mul, map_mul, map_inv, hπ4]
        exact hdB _ hπs
      simpa [Subgroup.coe_pow] using hmem
    refine ⟨(n₀ : G) ^ 4, pow_mem n₀.2 4, ?_, ?_, hω3⟩
    · rw [mem_normalizer_iff]
      intro s
      refine ⟨hconj s, fun hs' => ?_⟩
      have e : s = (n₀ : G) ^ 4 * ((n₀ : G) ^ 4 * ((n₀ : G) ^ 4 * s * ((n₀ : G) ^ 4)⁻¹) *
          ((n₀ : G) ^ 4)⁻¹) * ((n₀ : G) ^ 4)⁻¹ := by
        have h0 : (n₀ : G) ^ 4 * ((n₀ : G) ^ 4 * ((n₀ : G) ^ 4 * s * ((n₀ : G) ^ 4)⁻¹) *
            ((n₀ : G) ^ 4)⁻¹) * ((n₀ : G) ^ 4)⁻¹ =
            ((n₀ : G) ^ 4 * (n₀ : G) ^ 4 * (n₀ : G) ^ 4) * s *
              ((n₀ : G) ^ 4 * (n₀ : G) ^ 4 * (n₀ : G) ^ 4)⁻¹ := by group
        rw [h0, hω3]
        group
      rw [e]
      exact hconj _ (hconj _ hs')
    · intro hX
      have h1 : π (n₀ ^ 4) = 1 := (hπX _).mpr (by simpa [Subgroup.coe_pow] using hX)
      exact hd1 (hπ4 ▸ h1)

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

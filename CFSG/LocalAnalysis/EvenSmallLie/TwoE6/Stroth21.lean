module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21Local
public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21Aut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Open CFSG.Monster.B.TwoA.Amalgam
open CFSG.ComponentClassification.M12Cover.CyclicKernel

@[expose] def OddSquareTest :
    Prop :=
  ∀ u : commutator Eam, u * u = 1 → (u : Eam) ≠ 1 → (u : Eam) ≠ cE' →
    ¬ IsConj xhatEam (u : Eam) → ¬ IsConj (cE' * xhatEam) (u : Eam) →
    ∃ s ∈ closure {h : commutator Eam | h * u = u * h ∧ Odd (orderOf h)}, s * s = u

@[expose] def RootFourTest :
    Prop :=
  ∀ b : Eam, b * b = xhatEam ∨ b * b = cE' * xhatEam →
    ∃ h ∈ commutator Eam, h * xhatEam = xhatEam * h ∧ Odd (orderOf h) ∧ b * h ≠ h * b

section Generic

variable {E : Type*} [Group E] {D : Subgroup E} [D.Normal] {c x : E}

theorem false_of_rootFourTest_gen (hcc : ∀ y : E, y * c = c * y) (hc2 : c * c = 1)
    (hR : ∀ b : E, b * b = x ∨ b * b = c * x →
      ∃ h ∈ D, h * x = x * h ∧ Odd (orderOf h) ∧ b * h ≠ h * b)
    {U : D} {a b e : E} (ha : a = x ∨ a = c * x) (he : e * a * e⁻¹ = U)
    (hb2 : b * b = U ∨ b * b = c * U)
    (hbc : ∀ y : D, y * U = U * y → Odd (orderOf y) → b * y = y * b) : False := by
  have hconj : ∀ y : E, e⁻¹ * (e * y * e⁻¹) * e = y := fun y => by group
  have hb' : (e⁻¹ * b * e) * (e⁻¹ * b * e) = x ∨ (e⁻¹ * b * e) * (e⁻¹ * b * e) = c * x := by
    have hsq : (e⁻¹ * b * e) * (e⁻¹ * b * e) = e⁻¹ * (b * b) * e := by group
    have hce : e⁻¹ * c * e = c := by rw [hcc e⁻¹]; group
    have hcU : e⁻¹ * (c * (U : E)) * e = c * (e⁻¹ * U * e) := by
      calc e⁻¹ * (c * (U : E)) * e = (e⁻¹ * c * e) * (e⁻¹ * U * e) := by group
        _ = c * (e⁻¹ * U * e) := by rw [hce]
    have hUa : e⁻¹ * (U : E) * e = a := by rw [← he, hconj]
    rw [hsq]
    rcases hb2 with h | h <;> rcases ha with rfl | rfl
    · exact Or.inl (by rw [h, hUa])
    · exact Or.inr (by rw [h, hUa])
    · exact Or.inr (by rw [h, hcU, hUa])
    · exact Or.inl (by rw [h, hcU, hUa, ← mul_assoc, hc2, one_mul])
  obtain ⟨h, hhD, hhx, hho, hhb⟩ := hR _ hb'
  have hh'D : e * h * e⁻¹ ∈ D := ‹D.Normal›.conj_mem h hhD e
  have hha : h * a = a * h := by
    rcases ha with rfl | rfl
    · exact hhx
    · calc h * (c * x) = c * (h * x) := by rw [← mul_assoc, hcc]; group
        _ = c * (x * h) := by rw [hhx]
        _ = c * x * h := by group
  have hU : ((⟨e * h * e⁻¹, hh'D⟩ : D) : E) * U = U * ((⟨e * h * e⁻¹, hh'D⟩ : D) : E) := by
    show e * h * e⁻¹ * (U : E) = (U : E) * (e * h * e⁻¹)
    rw [← he]
    calc e * h * e⁻¹ * (e * a * e⁻¹) = e * (h * a) * e⁻¹ := by group
      _ = e * (a * h) * e⁻¹ := by rw [hha]
      _ = e * a * e⁻¹ * (e * h * e⁻¹) := by group
  have hodd : Odd (orderOf (⟨e * h * e⁻¹, hh'D⟩ : D)) := by
    rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hho
  have key : b * (e * h * e⁻¹) = e * h * e⁻¹ * b := hbc ⟨e * h * e⁻¹, hh'D⟩ (Subtype.ext hU) hodd
  apply hhb
  calc e⁻¹ * b * e * h = e⁻¹ * (b * (e * h * e⁻¹)) * e := by group
    _ = e⁻¹ * (e * h * e⁻¹ * b) * e := by rw [key]
    _ = h * (e⁻¹ * b * e) := by group

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [D.Normal] [Finite G] in
theorem iota_center_eq_gen (hZ : (center D).map D.subtype = zpowers c) (hc2 : orderOf c = 2)
    (ι : L ≃* D) {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1) : ((ι z : D) : E) = c := by
  have hmem : ι z ∈ center D := (CFSG.Monster.B.GSide.mem_center_iff_of_mulEquiv ι).1 hz
  have h2 : ((ι z : D) : E) ∈ (center D).map D.subtype := ⟨_, hmem, rfl⟩
  rw [hZ] at h2
  rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers hc2 h2 with h | h
  · exfalso
    apply hz1
    apply ι.injective
    rw [map_one]
    exact Subtype.ext h
  · exact h

theorem false_of_large_conj_inter_gen (hcc : ∀ y : E, y * c = c * y) (hc2 : orderOf c = 2)
    (hZD : (center D).map D.subtype = zpowers c) (hsqc : ∀ y : E, y * y ≠ c)
    (hAut : ∀ σ : MulAut D, ∃ b : E, ∀ y : D, ((σ y : D) : E) = b * y * b⁻¹)
    (hEq : ∀ a b : E, (∀ y : D, b * (y : E) * b⁻¹ = a * y * a⁻¹) → b = a ∨ b = c * a)
    (hS : ∀ u : D, u * u = 1 → (u : E) ≠ 1 → (u : E) ≠ c →
      ¬ IsConj x (u : E) → ¬ IsConj (c * x) (u : E) →
      ∃ s ∈ closure {h : D | h * u = u * h ∧ Odd (orderOf h)}, s * s = u)
    (hR : ∀ b : E, b * b = x ∨ b * b = c * x →
      ∃ h ∈ D, h * x = x * h ∧ Odd (orderOf h) ∧ b * h ≠ h * b)
    (hset : StandardSetting G L) (ι : L ≃* D) (hc : Nat.card (center L) = 2)
    (hsqL : ∀ a : L, a ^ 2 ∈ center L → a ^ 2 = 1)
    (hsq : ∀ σ : MulAut L, σ * σ ∈ (MulAut.conj : L →* MulAut L).range)
    {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1) {g : G} (hg : g ∉ normalizer (L : Set G))
    {P : Subgroup G}
    (hP : P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G))
    (hP2 : IsPGroup 2 P) (hPcard : 2 < Nat.card P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcc2 : c * c = 1 := by rw [← sq, ← hc2, pow_orderOf_eq_one]
  have hιz : ((ι z : D) : E) = c := iota_center_eq_gen hZD hc2 ι hz hz1
  set d : G := (z : G) with hd
  have hdo : orderOf d = 2 := by
    have hzc : orderOf (⟨z, hz⟩ : center L) = 2 := by
      refine orderOf_eq_prime ?_ (fun h => hz1 (congrArg Subtype.val h))
      rw [← hc]
      exact pow_card_eq_one'
    rw [Subgroup.orderOf_mk] at hzc
    rw [hd, Subgroup.orderOf_coe, hzc]
  have hdZ : d ∈ (center L).map L.subtype := ⟨z, hz, rfl⟩
  obtain ⟨hdK, hKcyc, hK2, -, hCN, -, -⟩ := std_center_facts hset hdo hdZ
  have hdL : ∀ s ∈ L, s * s ≠ d := by
    intro s hs hss
    apply hsqc ((ι ⟨s, hs⟩ : D) : E)
    rw [← coe_mul, ← map_mul, show (⟨s, hs⟩ : L) * ⟨s, hs⟩ = z from Subtype.ext hss, hιz]
  have hodd : ∀ y : G, y * d = d * y → Odd (orderOf y) → y ∈ L := by
    intro y hy hyo
    have hyN : y ∈ normalizer (L : Set G) := by
      rw [← hCN]
      exact mem_centralizer_singleton_iff.2 hy
    exact mem_of_odd_orderOf hsq hK2 hyN hyo
  set C' := (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom with hC'def
  have hC'cyc : IsCyclic C' := by
    have e : centralizer (L : Set G) ≃* C' :=
      (centralizer (L : Set G)).equivMapOfInjective _ (MulAut.conj g).injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hPcyc : IsCyclic P := by
    have := hC'cyc
    exact Subgroup.isCyclic_of_le (hP.trans inf_le_left)
  obtain ⟨w, hwP, hw4⟩ := exists_orderOf_eq_four_of_isCyclic hPcyc hP2 hPcard
  have hwC : w ∈ C' := (hP hwP).1
  have hwN : w ∈ normalizer (L : Set G) := (hP hwP).2
  set u := w * w with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, ← sq, orderOf_pow_of_dvd two_ne_zero (by rw [hw4]; norm_num), hw4]
  have hgdC : g * d * g⁻¹ ∈ C' :=
    ⟨d, hdK, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hgdo : orderOf (g * d * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hdo]
  have hug : u = g * d * g⁻¹ :=
    CFSG.ComponentClassification.M12Cover.CyclicKernel.eq_of_orderOf_eq_two_of_isCyclic hC'cyc
      (mul_mem hwC hwC) hgdC hu2 hgdo
  have huL : u ∈ L := by
    have hZeven : Even (Nat.card (center L)) := by rw [hc]; exact even_two
    refine mem_of_sq_eq_one_of_mem_sup_centralizer hKcyc hZeven hsqL
      (mul_self_mem_sup_centralizer hsq hwN) ?_
    rw [← hu2, pow_orderOf_eq_one]
  have hud : u ≠ d := by
    intro h
    apply hg
    rw [← hCN, mem_centralizer_singleton_iff]
    rw [hug] at h
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [h]
  have hcomm : ∀ h : G, h * u = u * h → Odd (orderOf h) → h * w = w * h := by
    intro h hh hho
    refine commute_of_odd_of_mem_cyclic hC'cyc hwC hw4 ?_ hho
    have h1 : g⁻¹ * h * g ∈ normalizer (L : Set G) := by
      rw [← hCN, mem_centralizer_singleton_iff]
      rw [hug] at hh
      calc g⁻¹ * h * g * d = g⁻¹ * (h * (g * d * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹ * h) * g := by rw [hh]
        _ = d * (g⁻¹ * h * g) := by group
    obtain ⟨k, hk, hkw⟩ := hwC
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkw
    refine ⟨g⁻¹ * h * g * k * (g⁻¹ * h * g)⁻¹, conj_mem_centralizer_of_mem_normalizer h1 hk, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hkw]
    group
  set τ := L.normalizerMonoidHom ⟨w, hwN⟩ with hτdef
  have hτ : ∀ y : L, ((τ y : L) : G) = w * y * w⁻¹ := fun y => rfl
  obtain ⟨b, hb⟩ := hAut (MulAut.congr ι τ)
  have hb' : ∀ y : L, ((ι (τ y) : D) : E) = b * (ι y : E) * b⁻¹ := by
    intro y
    have h := hb (ι y)
    rwa [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
  set uL : L := ⟨u, huL⟩ with huLdef
  set U : D := ι uL with hUdef
  have hb2 : b * b = (U : E) ∨ b * b = c * (U : E) := by
    apply hEq
    intro y
    obtain ⟨y₀, rfl⟩ := ι.surjective y
    have e1 : τ (τ y₀) = uL * y₀ * uL⁻¹ := by
      apply Subtype.ext
      show w * (w * (y₀ : G) * w⁻¹) * w⁻¹ = w * w * y₀ * (w * w)⁻¹
      group
    have e2 : ((ι (uL * y₀ * uL⁻¹) : D) : E) = (U : E) * (ι y₀ : E) * (U : E)⁻¹ := by
      rw [map_mul ι (uL * y₀) uL⁻¹, map_mul ι uL y₀, map_inv ι uL, coe_mul, coe_mul, coe_inv]
    calc b * b * ((ι y₀ : D) : E) * (b * b)⁻¹ = b * (b * (ι y₀ : E) * b⁻¹) * b⁻¹ := by group
      _ = b * ((ι (τ y₀) : D) : E) * b⁻¹ := by rw [hb' y₀]
      _ = ((ι (τ (τ y₀)) : D) : E) := (hb' (τ y₀)).symm
      _ = (U : E) * (ι y₀ : E) * (U : E)⁻¹ := by rw [e1, e2]
  have hbc : ∀ y : D, y * U = U * y → Odd (orderOf y) → b * y = y * b := by
    intro y hy hyo
    obtain ⟨y₀, rfl⟩ := ι.surjective y
    have h0 : y₀ * uL = uL * y₀ :=
      ι.injective (by rw [map_mul ι y₀ uL, map_mul ι uL y₀]; exact hy)
    have h1 : (y₀ : G) * u = u * y₀ := congrArg Subtype.val h0
    have h2 : Odd (orderOf (y₀ : G)) := by
      rwa [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ι]
    have h3 := hcomm _ h1 h2
    have h4 : τ y₀ = y₀ := by
      apply Subtype.ext
      rw [hτ]
      calc w * y₀ * w⁻¹ = y₀ * w * w⁻¹ := by rw [← h3]
        _ = y₀ := by group
    have h5 := hb' y₀
    rw [h4] at h5
    calc b * ((ι y₀ : D) : E) = b * (ι y₀ : E) * b⁻¹ * b := by group
      _ = (ι y₀ : E) * b := by rw [← h5]
  have hU2 : U * U = 1 := by
    have h : uL * uL = 1 := Subtype.ext (by
      show u * u = 1
      rw [← sq, ← hu2, pow_orderOf_eq_one])
    rw [hUdef, ← map_mul ι uL uL, h, map_one]
  have hU1 : (U : E) ≠ 1 := by
    intro h
    have h1 : uL = 1 := ι.injective (by rw [map_one]; exact Subtype.ext h)
    have h2 : u = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hUc : (U : E) ≠ c := by
    intro h
    apply hud
    have h1 : uL = z := ι.injective (Subtype.ext (h.trans hιz.symm))
    exact congrArg Subtype.val h1
  have hclass : IsConj x (U : E) ∨ IsConj (c * x) (U : E) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hss⟩ := hS U hU2 hU1 hUc hcon.1 hcon.2
    set ψ : D →* G := L.subtype.comp ι.symm.toMonoidHom with hψ
    have hψinj : Function.Injective ψ := L.subtype_injective.comp ι.symm.injective
    have hψU : ψ U = u := by
      rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hUdef, MulEquiv.symm_apply_apply]
      rfl
    have hψs : ψ s ∈ closure {h : G | h * (g * d * g⁻¹) = g * d * g⁻¹ * h ∧ Odd (orderOf h)} := by
      have h1 := mem_map_of_mem ψ hs
      rw [MonoidHom.map_closure] at h1
      refine closure_mono ?_ h1
      rintro _ ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hug, ← hψU, ← map_mul ψ h U, ← map_mul ψ U h, hh1]
      · rwa [orderOf_injective ψ hψinj]
    exact mul_self_ne_of_mem_closure_odd hdL hodd g hψs
      (by rw [← map_mul ψ s s, hss, hψU, hug])
  rcases hclass with hcl | hcl
  · obtain ⟨e, he⟩ := isConj_iff.1 hcl
    exact false_of_rootFourTest_gen hcc hcc2 hR (Or.inl rfl) he hb2 hbc
  · obtain ⟨e, he⟩ := isConj_iff.1 hcl
    exact false_of_rootFourTest_gen hcc hcc2 hR (Or.inr rfl) he hb2 hbc

end Generic

theorem stroth21_of_inputs
    (hS : OddSquareTest) (hR : RootFourTest) : Stroth21 := by
  intro G _ _ L hset hc hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := doubleCoverUnique L hset.standard.1 hc ((lieModel_twistedE6_two_iff _).1 hB)
  obtain ⟨z, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hc
  have hz1' : (z : L) ≠ 1 := fun h => hz1 (Subtype.ext h)
  set d : G := ((z : L) : G) with hd
  have hdo : orderOf d = 2 := by
    have hzc : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ hz1
      rw [← hc]
      exact pow_card_eq_one'
    rw [hd, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hdZ : d ∈ (center L).map L.subtype := ⟨z, z.2, rfl⟩
  obtain ⟨hdK, -, hK2, -, -, -, -⟩ := std_center_facts hset hdo hdZ
  suffices hcard : Nat.card (centralizer (L : Set G)) = 2 by
    have h1 : zpowers d = centralizer (L : Set G) :=
      eq_of_le_of_card_ge (zpowers_le.2 hdK) (by rw [hcard, Nat.card_zpowers, hdo])
    have h2 : zpowers d = (center L).map L.subtype :=
      eq_of_le_of_card_ge (zpowers_le.2 hdZ)
        (by rw [card_map_of_injective L.subtype_injective, hc, Nat.card_zpowers, hdo])
    rw [← h1, ← h2]
  by_contra hne
  obtain ⟨S, -⟩ := hset.cyclic
  have hS4 : 4 ≤ Nat.card S := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hK2
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at ha
      have : d ∈ (⊥ : Subgroup G) := ha ▸ hdK
      rw [mem_bot] at this
      rw [this, orderOf_one] at hdo
      exact absurd hdo (by norm_num)
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hne (by rw [ha, pow_one])
    rw [Sylow.card_eq_multiplicity, ha, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hsmall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact hset.false_of_forall_card_le_two
      (FoursGroupCondition.of_mulEquiv ι.symm fourGroupCondition_commutator_Eam) S hS4 hsmall
  · push Not at hsmall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hsmall
    exact false_of_large_conj_inter_gen Stroth21Aux.cE'_comm Stroth21Aux.orderOf_cE'_eq_two
      short_F4_derived_standard_perfect_cover.2.2.2.1 mul_self_ne_cE' exists_eq_conj_of_mulAut
      (fun a b h => eq_or_eq_of_conj_eq h) hS hR hset ι hc
      (sq_eq_one_of_sq_mem_center_of_mulEquiv ι) (mul_self_mem_range_conj_of_iota ι) z.2 hz1'
      hg hP hP2 hPcard

end CFSG.EvenSmallLie.TwoE6

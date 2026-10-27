module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.AGLEmbedding.ThreeFives

open Equiv Subgroup
open scoped commutatorElement

theorem exists_noncomm_of_simple {B : Type*} [Group B] (hB : IsSimpleGroup B)
    (h : 4 ∣ Nat.card B) : ∃ a b : B, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := hcomm }
  have := hB
  have hp : (Nat.card B).Prime := IsSimpleGroup.prime_card
  rcases Nat.Prime.eq_one_or_self_of_dvd hp 4 h with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by decide)

theorem inf_eq_bot_of_five {Q : Type*} [Group Q] {N B : Subgroup Q} (hN : N.Normal)
    (hB : IsSimpleGroup ↥B) (h5B : 5 ∣ Nat.card B) (h5N : ¬ 5 ∣ Nat.card N) : N ⊓ B = ⊥ := by
  have := hN.subgroupOf B
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥B) ∈ N.subgroupOf B := hx.1
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · exfalso
    have hBN : B ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : ↥B) ∈ N.subgroupOf B := h ▸ Subgroup.mem_top _
      exact this
    exact h5N (h5B.trans (Subgroup.card_dvd_of_le hBN))

@[expose] def SectionsOrderSixty {Y : Type*} [Group Y] (P O : Subgroup Y) : Prop :=
  ∀ U : Subgroup Y, U ≤ P → ∀ (V : Subgroup ↥U) [V.Normal], O.subgroupOf U ≤ V →
    IsSimpleGroup (↥U ⧸ V) → (∃ a b : ↥U ⧸ V, a * b ≠ b * a) → Nat.card (↥U ⧸ V) = 60

@[expose] def FiveSection {Y : Type*} [Group Y] (P O J : Subgroup Y) : Prop :=
  J ≤ P ∧ ∃ φ : ↥J →* alternatingGroup (Fin 5), Function.Surjective φ ∧
    ∀ x : ↥J, φ x = 1 ↔ (x : Y) ∈ O

theorem false_of_section {Y : Type*} [Group Y] {P O : Subgroup Y}
    (hsec : SectionsOrderSixty P O) {Q : Type*} [Group Q] (ψ : ↥P →* Q)
    (hψ : Function.Surjective ψ) (B : Subgroup Q) (hB : IsSimpleGroup ↥B)
    (hnc : ∃ a b : ↥B, a * b ≠ b * a) (hcard : Nat.card B ≠ 60)
    (hO : ∀ o : ↥P, (o : Y) ∈ O → ψ o ∈ B → ψ o = 1) : False := by
  set W : Subgroup ↥P := B.comap ψ with hW
  set U : Subgroup Y := W.map P.subtype with hU
  have hUP : U ≤ P := Subgroup.map_subtype_le W
  let eW : ↥W ≃* ↥U := Subgroup.equivMapOfInjective W P.subtype P.subtype_injective
  let θ : ↥U →* ↥B :=
    ((ψ.comp W.subtype).codRestrict B (fun w => w.2)).comp eW.symm.toMonoidHom
  have hθ_apply : ∀ x : ↥U, ((θ x : ↥B) : Q) = ψ ((eW.symm x : ↥W) : ↥P) := fun x => rfl
  have hcoe : ∀ w : ↥W, ((eW w : ↥U) : Y) = ((w : ↥P) : Y) := fun w => rfl
  have hθ : Function.Surjective θ := by
    intro b
    obtain ⟨p, hp⟩ := hψ (b : Q)
    have hpW : p ∈ W := by
      show ψ p ∈ B
      rw [hp]
      exact b.2
    refine ⟨eW ⟨p, hpW⟩, Subtype.ext ?_⟩
    rw [hθ_apply, MulEquiv.symm_apply_apply]
    exact hp
  have hV : O.subgroupOf U ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxO : ((x : ↥U) : Y) ∈ O := hx
    have hwx : (((eW.symm x : ↥W) : ↥P) : Y) = ((x : ↥U) : Y) := by
      have := hcoe (eW.symm x)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have h1 : ψ ((eW.symm x : ↥W) : ↥P) = 1 :=
      hO _ (hwx ▸ hxO) (eW.symm x).2
    exact Subtype.ext (by rw [hθ_apply, h1]; rfl)
  have e : ↥U ⧸ θ.ker ≃* ↥B := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  have hsimple : IsSimpleGroup (↥U ⧸ θ.ker) := by
    have := hB
    exact e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnc
  have hnc' : ∃ x y : ↥U ⧸ θ.ker, x * y ≠ y * x := by
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have h60 := hsec U hUP θ.ker hV hsimple hnc'
  exact hcard (by rw [← Nat.card_congr e.toEquiv]; exact h60)

section Specific

variable {Y : Type*} [Group Y]

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h
  have h120 : Nat.factorial 5 = 120 := by decide
  omega

theorem false_of_not_five_dvd {P O J : Subgroup Y} (hJ : FiveSection P O J)
    (h5 : ¬ 5 ∣ Nat.card P) : False := by
  obtain ⟨hJP, φ, hφ, -⟩ := hJ
  have h1 := Subgroup.card_dvd_of_surjective hφ
  rw [card_alternatingGroup_five] at h1
  exact h5 ((by norm_num : 5 ∣ 60).trans (h1.trans (Subgroup.card_dvd_of_le hJP)))

theorem normal_subgroupOf_of_le_normalizer {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) : (O.subgroupOf P).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hOP]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.mp (hN hk) h).mp hh

theorem card_map_subgroupOf_dvd {P O : Subgroup Y} (hOP : O ≤ P) {Q : Type*} [Group Q]
    (ψ : ↥P →* Q) : Nat.card ((O.subgroupOf P).map ψ) ∣ Nat.card O := by
  have h1 := Subgroup.card_map_dvd (O.subgroupOf P) ψ
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOP).toEquiv] at h1

theorem false_of_hom_simple {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (hsec : SectionsOrderSixty P O)
    {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q) (hnc : ∃ a b : Q, a * b ≠ b * a)
    (hcard : Nat.card Q ≠ 60) (ψ : ↥P →* Q) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) {J : Subgroup Y} (hJ : FiveSection P O J) : False := by
  have hnorm := normal_subgroupOf_of_le_normalizer hOP hN
  have hNn : ((O.subgroupOf P).map ψ).Normal := hnorm.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O.subgroupOf P).map ψ) with h | h
  · have htop : IsSimpleGroup ↥(⊤ : Subgroup Q) := by
      have := hQ
      exact Subgroup.topEquiv.isSimpleGroup
    refine false_of_section hsec ψ hψ ⊤ htop ?_ ?_ ?_
    · obtain ⟨a, b, hab⟩ := hnc
      exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h' => hab (congrArg Subtype.val h')⟩
    · rw [Subgroup.card_top]
      exact hcard
    · intro o ho _
      have : ψ o ∈ (O.subgroupOf P).map ψ := Subgroup.mem_map_of_mem ψ ho
      rw [h] at this
      exact this
  · obtain ⟨hJP, φ, hφ, hφk⟩ := hJ
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
      rw [card_alternatingGroup_five]
      norm_num
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨j, hj⟩ := hφ c
    set j' : ↥P := ⟨(j : Y), hJP j.2⟩ with hj'
    have hψj : ψ j' ∈ (O.subgroupOf P).map ψ := h ▸ Subgroup.mem_top _
    obtain ⟨o, ho, hoψ⟩ := hψj
    have hκ : o⁻¹ * j' ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hoψ, inv_mul_cancel]
    obtain ⟨a, ha⟩ := hker ⟨o⁻¹ * j', hκ⟩
    have hκa : (o⁻¹ * j') ^ 2 ^ a = 1 := congrArg Subtype.val ha
    let π := QuotientGroup.mk' (O.subgroupOf P)
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    have hπ : π (j' ^ 2 ^ a) = 1 := by
      have e1 : π j' = π (o⁻¹ * j') := by
        rw [map_mul, map_inv, hπo, inv_one, one_mul]
      rw [map_pow, e1, ← map_pow, hκa, map_one]
    have hmem : j' ^ 2 ^ a ∈ O.subgroupOf P := (QuotientGroup.eq_one_iff _).1 hπ
    have hx : ((j ^ 2 ^ a : ↥J) : Y) ∈ O := by
      have : ((j' ^ 2 ^ a : ↥P) : Y) ∈ O := hmem
      simpa [hj'] using this
    have h1 : φ (j ^ 2 ^ a) = 1 := (hφk _).2 hx
    rw [map_pow, hj] at h1
    have h2 : orderOf c ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
    rw [hc] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)

end Specific

section Alternating

variable {Y : Type*} [Group Y]

theorem alternating_facts {m : ℕ} (hm : 6 ≤ m) :
    IsSimpleGroup ↥(alternatingGroup (Fin m)) ∧ 4 ∣ Nat.card (alternatingGroup (Fin m)) ∧
      5 ∣ Nat.card (alternatingGroup (Fin m)) ∧ Nat.card (alternatingGroup (Fin m)) ≠ 60 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : 2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
    have := two_mul_nat_card_alternatingGroup (α := Fin m)
    rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  have h6 : (6 : ℕ).factorial ∣ m.factorial := Nat.factorial_dvd_factorial hm
  have h720 : (6 : ℕ).factorial = 720 := by decide
  refine ⟨alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ m)), ?_, ?_, ?_⟩
  · have h8 : 2 * 4 ∣ 2 * Nat.card (alternatingGroup (Fin m)) := by
      rw [hcard]
      exact (by rw [h720]; norm_num : 8 ∣ (6 : ℕ).factorial).trans h6
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8
  · have h5 : 5 ∣ 2 * Nat.card (alternatingGroup (Fin m)) := by
      rw [hcard]
      exact Nat.dvd_factorial (by norm_num) (by omega)
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 5 2) h5)
  · intro h60
    have := Nat.le_of_dvd (Nat.factorial_pos m) h6
    have hge : (6 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
    omega

theorem false_of_hom_sub {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (hsec : SectionsOrderSixty P O)
    (h5 : ¬ 5 ∣ Nat.card O) {Q : Type*} [Group Q] (ψ : ↥P →* Q) (hψ : Function.Surjective ψ)
    (B : Subgroup Q) (hB : IsSimpleGroup ↥B) (h4B : 4 ∣ Nat.card B) (h5B : 5 ∣ Nat.card B)
    (h60 : Nat.card B ≠ 60) : False := by
  have hnorm := normal_subgroupOf_of_le_normalizer hOP hN
  have hNn : ((O.subgroupOf P).map ψ).Normal := hnorm.map ψ hψ
  refine false_of_section hsec ψ hψ B hB (exists_noncomm_of_simple hB h4B) h60 ?_
  intro o ho hoB
  have h5N : ¬ 5 ∣ Nat.card ((O.subgroupOf P).map ψ) := fun h =>
    h5 (h.trans (card_map_subgroupOf_dvd hOP ψ))
  have hbot := inf_eq_bot_of_five hNn hB h5B h5N
  have : ψ o ∈ (O.subgroupOf P).map ψ ⊓ B := ⟨Subgroup.mem_map_of_mem ψ ho, hoB⟩
  rw [hbot] at this
  exact this

theorem false_of_hom_perm {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (hsec : SectionsOrderSixty P O)
    (h5 : ¬ 5 ∣ Nat.card O) {n : ℕ} (hn : 6 ≤ n) (ψ : ↥P →* Perm (Fin n))
    (hψ : Function.Surjective ψ) : False := by
  obtain ⟨hs, h4, h5A, h60⟩ := alternating_facts hn
  exact false_of_hom_sub hOP hN hsec h5 ψ hψ _ hs h4 h5A h60

theorem false_of_hom_perm_prod {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (hsec : SectionsOrderSixty P O)
    (h5 : ¬ 5 ∣ Nat.card O) {r m : ℕ} (hm : 6 ≤ m)
    (ψ : ↥P →* Perm (Fin r) × Perm (Fin m)) (hψ : Function.Surjective ψ) : False := by
  obtain ⟨hs, h4, h5A, h60⟩ := alternating_facts hm
  set B : Subgroup (Perm (Fin r) × Perm (Fin m)) :=
    (alternatingGroup (Fin m)).map (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m))) with hBdef
  have hinj : Function.Injective (MonoidHom.inr (Perm (Fin r)) (Perm (Fin m))) :=
    fun a b h => congrArg Prod.snd h
  let e : ↥(alternatingGroup (Fin m)) ≃* ↥B := Subgroup.equivMapOfInjective _ _ hinj
  have hBs : IsSimpleGroup ↥B := by
    have := hs
    exact e.symm.isSimpleGroup
  have hcardB : Nat.card B = Nat.card (alternatingGroup (Fin m)) :=
    (Nat.card_congr e.toEquiv).symm
  exact false_of_hom_sub hOP hN hsec h5 ψ hψ B hBs (hcardB ▸ h4) (hcardB ▸ h5A)
    (hcardB ▸ h60)

end Alternating

section Five

variable {Y : Type*} [Group Y]

theorem alt_five_simple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem center_perm_five :
    ∀ σ : Perm (Fin 5), (∀ τ : Perm (Fin 5), τ * σ * τ⁻¹ = σ) → σ = 1 := by
  decide +kernel

theorem map_eq_bot_perm_five {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (h5 : ¬ 5 ∣ Nat.card O)
    (ψ : ↥P →* Perm (Fin 5)) (hψ : Function.Surjective ψ) : (O.subgroupOf P).map ψ = ⊥ := by
  have hnorm := normal_subgroupOf_of_le_normalizer hOP hN
  have hNn : ((O.subgroupOf P).map ψ).Normal := hnorm.map ψ hψ
  have h5A : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [card_alternatingGroup_five]
    norm_num
  have h5N : ¬ 5 ∣ Nat.card ((O.subgroupOf P).map ψ) := fun h =>
    h5 (h.trans (card_map_subgroupOf_dvd hOP ψ))
  have hbot := inf_eq_bot_of_five hNn alt_five_simple h5A h5N
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply center_perm_five
  intro τ
  have hc1 : ⁅σ⁻¹, τ⁆ ∈ (O.subgroupOf P).map ψ := by
    have h1 : τ * σ * τ⁻¹ ∈ (O.subgroupOf P).map ψ := hNn.conj_mem σ hσ τ
    have : ⁅σ⁻¹, τ⁆ = σ⁻¹ * (τ * σ * τ⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ) h1
  have hc2 : ⁅σ⁻¹, τ⁆ ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hc3 : ⁅σ⁻¹, τ⁆ ∈ (O.subgroupOf P).map ψ ⊓ alternatingGroup (Fin 5) := ⟨hc1, hc2⟩
  rw [hbot, Subgroup.mem_bot, commutatorElement_def, inv_inv] at hc3
  calc τ * σ * τ⁻¹ = σ * (σ⁻¹ * τ * σ * τ⁻¹) := by group
    _ = σ := by rw [hc3, mul_one]

theorem range_eq_alternating {P O J : Subgroup Y} (hJ : FiveSection P O J)
    (ψ : ↥P →* Perm (Fin 5)) (hker : IsPGroup 2 ψ.ker)
    (hO : ∀ o : ↥P, (o : Y) ∈ O → ψ o = 1) :
    (ψ.comp (Subgroup.inclusion hJ.1)).range = alternatingGroup (Fin 5) := by
  obtain ⟨hJP, φ, hφ, hφk⟩ := hJ
  set ψJ := ψ.comp (Subgroup.inclusion hJP) with hψJ
  have hA := alt_five_simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3A : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [card_alternatingGroup_five]
    norm_num
  have ha : φ.ker ≤ ψJ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hO _ ((hφk x).1 hx)
  have hb : ψJ.ker ≤ φ.ker := by
    have hn : (ψJ.ker.map φ).Normal := (MonoidHom.normal_ker ψJ).map φ hφ
    rcases hA.eq_bot_or_eq_top_of_normal (ψJ.ker.map φ) with h | h
    · intro x hx
      have : φ x ∈ ψJ.ker.map φ := Subgroup.mem_map_of_mem φ hx
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3A
      have hcm : c ∈ ψJ.ker.map φ := h ▸ Subgroup.mem_top c
      obtain ⟨x, hx, hxc⟩ := hcm
      obtain ⟨a, ha'⟩ := hker ⟨Subgroup.inclusion hJP x, hx⟩
      have h1 : Subgroup.inclusion hJP (x ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha'
      have h2 : x ^ 2 ^ a = 1 := (Subgroup.inclusion_injective hJP) (by rw [h1, map_one])
      have h3 : c ^ 2 ^ a = 1 := by rw [← hxc, ← map_pow, h2, map_one]
      have h4 : orderOf c ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h3
      rw [hc] at h4
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4) (by norm_num)
  have hker_eq : ψJ.ker = φ.ker := le_antisymm hb ha
  let e : ↥ψJ.range ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientKerEquivRange ψJ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ))
  have hRs : IsSimpleGroup ↥ψJ.range := by
    have := hA
    exact e.isSimpleGroup
  have hRcard : Nat.card ψJ.range = 60 :=
    (Nat.card_congr e.toEquiv).trans card_alternatingGroup_five
  have hle : ψJ.range ≤ alternatingGroup (Fin 5) := by
    let s : ↥ψJ.range →* ℤˣ := Perm.sign.comp ψJ.range.subtype
    rcases hRs.eq_bot_or_eq_top_of_normal s.ker with h | h
    · exfalso
      have h3R : 3 ∣ Nat.card ψJ.range := by
        rw [hRcard]
        norm_num
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3R
      have h1 : orderOf (s c) ∣ 3 := hc ▸ orderOf_map_dvd s c
      have h2 : orderOf (s c) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_sq (s c))
      have h12 : orderOf (s c) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
      have hs1 : s c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h12))
      have : c ∈ s.ker := hs1
      rw [h, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hc
      omega
    · intro g hg
      have : (⟨g, hg⟩ : ↥ψJ.range) ∈ s.ker := h ▸ Subgroup.mem_top _
      exact Perm.mem_alternatingGroup.2 this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_alternatingGroup_five, hRcard])

theorem false_of_hom_perm_five {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (h5 : ¬ 5 ∣ Nat.card O)
    (ψ : ↥P →* Perm (Fin 5)) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    {J₀ J₁ : Subgroup Y} (h0 : FiveSection P O J₀) (h1 : FiveSection P O J₁)
    (hcomm : ⁅J₀, J₁⁆ ≤ O) : False := by
  have hbot := map_eq_bot_perm_five hOP hN h5 ψ hψ
  have hO : ∀ o : ↥P, (o : Y) ∈ O → ψ o = 1 := by
    intro o ho
    have : ψ o ∈ (O.subgroupOf P).map ψ := Subgroup.mem_map_of_mem ψ ho
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have e0 := range_eq_alternating h0 ψ hker hO
  have e1 := range_eq_alternating h1 ψ hker hO
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_simple alt_five_simple
    (by rw [card_alternatingGroup_five]; norm_num)
  have ha : (a : Perm (Fin 5)) ∈ (ψ.comp (Subgroup.inclusion h0.1)).range := by rw [e0]; exact a.2
  have hb : (b : Perm (Fin 5)) ∈ (ψ.comp (Subgroup.inclusion h1.1)).range := by rw [e1]; exact b.2
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have hxy : ⁅(x : Y), (y : Y)⁆ ∈ O := hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
  have hcx : ψ ⁅Subgroup.inclusion h0.1 x, Subgroup.inclusion h1.1 y⁆ = 1 :=
    hO _ (by rw [commutatorElement_def]; simpa [commutatorElement_def] using hxy)
  rw [map_commutatorElement] at hcx
  apply hab
  apply Subtype.ext
  have hx' : ψ (Subgroup.inclusion h0.1 x) = a := hx
  have hy' : ψ (Subgroup.inclusion h1.1 y) = b := hy
  rw [hx', hy'] at hcx
  have := commutatorElement_eq_one_iff_mul_comm.1 hcx
  simpa using this

theorem false_of_hom_perm_small [Finite Y] {P O J : Subgroup Y} (hJ : FiveSection P O J) {n : ℕ}
    (hn : n ≤ 4) (ψ : ↥P →* Perm (Fin n)) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine false_of_not_five_dvd hJ ?_
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hker
  have hcard := Subgroup.card_ker_mul_card_of_surjective hψ
  rw [ha, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hcard
  rw [← hcard]
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)
  · have : 5 ∣ (4 : ℕ).factorial := h.trans (Nat.factorial_dvd_factorial hn)
    revert this
    decide

end Five

end CFSG.AGLEmbedding.ThreeFives

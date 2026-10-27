module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv Subgroup

variable {Ω : Type*}

theorem exists_three_ne_of_four_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (h : 4 ≤ Fintype.card α) (x : α) :
    ∃ y z w : α, y ≠ x ∧ z ≠ x ∧ w ≠ x ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w := by
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x} : Finset α)) (t := Finset.univ)
    (by rw [Finset.card_univ, Finset.card_singleton]; omega)
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, y} : Finset α)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt (by omega))
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, y, z} : Finset α)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy hz hw
  exact ⟨y, z, w, hy, hz.1, hw.1, fun h => hz.2 h.symm, fun h => hw.2.1 h.symm,
    fun h => hw.2.2 h.symm⟩

theorem centralizer_subgroupOf_eq {G : Type*} [Group G] {L T : Subgroup G} (hLT : L ≤ T) :
    centralizer (L.subgroupOf T : Set T) = (centralizer (L : Set G)).subgroupOf T := by
  ext c
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    exact congrArg Subtype.val (h ⟨l, hLT hl⟩ (Subgroup.mem_subgroupOf.mpr hl))
  · intro h l hl
    exact Subtype.ext (h l (Subgroup.mem_subgroupOf.mp hl))

theorem card_subgroupOf_eq_card_inf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card ↥(K ⊓ H) := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

variable [DecidableEq Ω]

theorem commute_swap_of_apply_eq {z : Perm Ω} {a b : Ω} (ha : z a = a) (hb : z b = b) :
    Commute z (swap a b) := by
  have h : z * swap a b * z⁻¹ = swap a b := by rw [← swap_apply_apply, ha, hb]
  calc z * swap a b = z * swap a b * z⁻¹ * z := by group
    _ = swap a b * z := by rw [h]

theorem apply_mem_of_commute_three_cycle {c : Perm Ω} {x y z : Ω} (hzx : z ≠ x) (hzy : z ≠ y)
    (hc : c * (swap x y * swap x z) = swap x y * swap x z * c) :
    c x = x ∨ c x = y ∨ c x = z := by
  by_contra h
  simp only [not_or] at h
  have h1 := congrArg (fun g : Perm Ω => g x) hc
  simp only [Perm.mul_apply] at h1
  rw [swap_apply_left, swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne h.1 h.2.2,
    swap_apply_of_ne_of_ne h.1 h.2.1] at h1
  exact hzx (c.injective h1)

theorem three_cycle_fix_sign {p : Ω → Prop} [Fintype Ω] {x a b : Ω} (hx : p x) (ha : p a)
    (hb : p b) (hax : a ≠ x) (hbx : b ≠ x) :
    (∀ ω, ¬ p ω → (swap x a * swap x b) ω = ω) ∧ Perm.sign (swap x a * swap x b) = 1 := by
  refine ⟨fun ω hω => ?_, ?_⟩
  · have hωx : ω ≠ x := fun h => hω (h ▸ hx)
    have hωa : ω ≠ a := fun h => hω (h ▸ ha)
    have hωb : ω ≠ b := fun h => hω (h ▸ hb)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hωx hωb, swap_apply_of_ne_of_ne hωx hωa]
  · rw [map_mul, Perm.sign_swap (Ne.symm hax), Perm.sign_swap (Ne.symm hbx)]
    decide

theorem mem_centralizer_iff_forall_fixed [Fintype Ω] {p : Ω → Prop} [DecidablePred p]
    (hp : 4 ≤ Fintype.card (Subtype p)) {L : Subgroup (Perm Ω)}
    (hL : ∀ g, g ∈ L ↔ (∀ x, ¬ p x → g x = x) ∧ Perm.sign g = 1) {c : Perm Ω} :
    c ∈ centralizer (L : Set (Perm Ω)) ↔ ∀ x, p x → c x = x := by
  constructor
  · intro hc x hx
    obtain ⟨y, z, w, hyx, hzx, hwx, hyz, hyw, hzw⟩ := exists_three_ne_of_four_le_card hp ⟨x, hx⟩
    have hyx' : (y : Ω) ≠ x := fun h => hyx (Subtype.ext h)
    have hzx' : (z : Ω) ≠ x := fun h => hzx (Subtype.ext h)
    have hwx' : (w : Ω) ≠ x := fun h => hwx (Subtype.ext h)
    have hyz' : (y : Ω) ≠ z := fun h => hyz (Subtype.ext h)
    have hyw' : (y : Ω) ≠ w := fun h => hyw (Subtype.ext h)
    have hzw' : (z : Ω) ≠ w := fun h => hzw (Subtype.ext h)
    have hcomm : ∀ a b : Subtype p, (a : Ω) ≠ x → (b : Ω) ≠ x →
        c * (swap x a * swap x b) = swap x a * swap x b * c := fun a b hax hbx =>
      ((mem_centralizer_iff.mp hc) _ ((hL _).mpr (three_cycle_fix_sign hx a.2 b.2 hax hbx))).symm
    have h1 := apply_mem_of_commute_three_cycle hzx' (Ne.symm hyz') (hcomm y z hyx' hzx')
    have h2 := apply_mem_of_commute_three_cycle hwx' (Ne.symm hzw') (hcomm z w hzx' hwx')
    have h3 := apply_mem_of_commute_three_cycle hwx' (Ne.symm hyw') (hcomm y w hyx' hwx')
    rcases h1 with h1 | h1 | h1
    · exact h1
    · rcases h2 with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hyz'
      · exact absurd (h1.symm.trans h2) hyw'
    · rcases h3 with h3 | h3 | h3
      · exact h3
      · exact absurd (h1.symm.trans h3) (Ne.symm hyz')
      · exact absurd (h1.symm.trans h3) hzw'
  · intro hfix
    refine mem_centralizer_iff.mpr fun g hg => ?_
    obtain ⟨hgfix, -⟩ := (hL g).mp hg
    ext ω
    simp only [Perm.mul_apply]
    by_cases hω : p ω
    · rw [hfix ω hω, hfix (g ω) ((apply_iff_of_forall_not hgfix ω).mpr hω)]
    · have hcω : ¬ p (c ω) := by
        intro h
        have hcc : c (c ω) = c ω := hfix (c ω) h
        rw [c.injective hcc] at h
        exact hω h
      rw [hgfix ω hω, hgfix (c ω) hcω]

theorem natural_permutation_standard_core [Fintype Ω] {T : Subgroup (Perm Ω)}
    (hT : alternatingGroup Ω ≤ T) {σ : Perm Ω} (hσT : σ ∈ T) (hσ : orderOf σ = 2)
    {L : Subgroup (Perm Ω)}
    (hL : CFSG.Assembly.IsComponentOf L (T ⊓ centralizer ({σ} : Set (Perm Ω))))
    (heven : Even (Nat.card ↥(T ⊓ centralizer (L : Set (Perm Ω)))))
    (hnorm : ∀ g ∈ T, ∀ z ∈ T ⊓ centralizer (L : Set (Perm Ω)), orderOf z = 2 →
      g * z = z * g → ∀ c ∈ T ⊓ centralizer (L : Set (Perm Ω)),
        g * c * g⁻¹ ∈ T ⊓ centralizer (L : Set (Perm Ω))) :
    5 ≤ Nat.card {x // σ x = x} ∧
      L = (alternatingGroup {x // σ x = x}).map Perm.ofSubtype ∧
      T ⊓ centralizer (L : Set (Perm Ω)) =
        T ⊓ (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range ∧
      Xor
        (T = ⊤ ∧ Nat.card {x // σ x ≠ x} = 2 ∧
          ∃ a b : Ω, a ≠ b ∧ (∀ x, σ x ≠ x ↔ x = a ∨ x = b) ∧ σ = swap a b)
        (T = alternatingGroup Ω ∧ Nat.card {x // σ x ≠ x} = 4 ∧
          ∃ a b c d : Ω, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            (∀ x, σ x ≠ x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) ∧ σ = swap a b * swap c d) ∧
      (T = ⊤ → T ⊓ centralizer (L : Set (Perm Ω)) =
        (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range) ∧
      (T = alternatingGroup Ω → T ⊓ centralizer (L : Set (Perm Ω)) =
        (alternatingGroup {x // σ x ≠ x}).map Perm.ofSubtype) := by
  have hσσ : ∀ x, σ (σ x) = x := by
    have h2 : σ ^ 2 = 1 := by
      rw [← hσ]
      exact pow_orderOf_eq_one σ
    intro x
    rw [← Perm.mul_apply, ← sq, h2, Perm.one_apply]
  rw [LocalAnalysis.ComponentInitial.centralizer_singleton_eq_normalizer_zpowers hσ] at hL
  obtain ⟨hF5, hLeq⟩ :=
    LocalAnalysis.ComponentInitial.ordinary_permutation_local_component_fixed_support hT
      Nat.prime_two (zpowers_le.2 hσT)
      (LocalAnalysis.ComponentInitial.isPGroup_zpowers_of_orderOf_eq_two hσ) hL
  have hF : 5 ≤ Nat.card {x // σ x = x} := by
    rwa [← Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      LocalAnalysis.ComponentInitial.mem_fixedPoints_zpowers_iff)]
  have hLmem : ∀ g, g ∈ L ↔ (∀ x, ¬ σ x = x → g x = x) ∧ Perm.sign g = 1 := by
    intro g
    classical
    rw [hLeq, mem_map_ofSubtype_alternatingGroup_iff]
    simp only [LocalAnalysis.ComponentInitial.mem_fixedPoints_zpowers_iff]
  have hLalt : L = (alternatingGroup {x // σ x = x}).map Perm.ofSubtype := by
    ext g
    rw [hLmem, mem_map_ofSubtype_alternatingGroup_iff]
  have hF4 : 4 ≤ Fintype.card {x // σ x = x} := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have hCmem : ∀ c, c ∈ T ⊓ centralizer (L : Set (Perm Ω)) ↔
      c ∈ T ∧ ∀ x, σ x = x → c x = x := fun c => by
    rw [Subgroup.mem_inf, mem_centralizer_iff_forall_fixed hF4 hLmem]
  have hCeq : T ⊓ centralizer (L : Set (Perm Ω)) =
      T ⊓ (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range := by
    ext c
    rw [hCmem, Subgroup.mem_inf, mem_range_ofSubtype_iff]
    simp only [ne_eq, not_not]
  obtain ⟨eF⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 2) (β := {x // σ x = x})
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hx : σ (eF 0) = eF 0 := (eF 0).2
  have hy : σ (eF 1) = eF 1 := (eF 1).2
  have hxy : (eF 0 : Ω) ≠ eF 1 := fun h => absurd (eF.injective (Subtype.ext h)) (by decide)
  have hpresΔ : ∀ c ∈ T ⊓ centralizer (L : Set (Perm Ω)), ∀ u, σ u ≠ u → σ (c u) ≠ c u := by
    intro c hc u hu h
    have hcc : c (c u) = c u := ((hCmem c).mp hc).2 (c u) h
    rw [c.injective hcc] at h
    exact hu h
  have key : ∀ u, σ u ≠ u → ∀ z ∈ T ⊓ centralizer (L : Set (Perm Ω)), orderOf z = 2 →
      z u = u → ∀ c ∈ T ⊓ centralizer (L : Set (Perm Ω)), c u ≠ u → False := by
    intro u hu z hz hz2 hzu c hc hcu
    have hux : u ≠ eF 0 := fun h => hu (h ▸ hx)
    have huy : u ≠ eF 1 := fun h => hu (h ▸ hy)
    have hgT : swap u (eF 0) * swap u (eF 1) ∈ T := hT (by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hux, Perm.sign_swap huy]
      decide)
    have hzx : z (eF 0) = eF 0 := ((hCmem z).mp hz).2 _ hx
    have hzy : z (eF 1) = eF 1 := ((hCmem z).mp hz).2 _ hy
    have hgz : swap u (eF 0) * swap u (eF 1) * z = z * (swap u (eF 0) * swap u (eF 1)) :=
      ((commute_swap_of_apply_eq hzu hzx).mul_right (commute_swap_of_apply_eq hzu hzy)).eq.symm
    have hgc := hnorm _ hgT z hz hz2 hgz c hc
    have hgu : (swap u (eF 0) * swap u (eF 1)) u = eF 1 := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm huy) (Ne.symm hxy)]
    have hginv : (swap u (eF 0) * swap u (eF 1))⁻¹ (eF 1) = u :=
      Perm.inv_eq_iff_eq.mpr hgu.symm
    have hcuΔ : σ (c u) ≠ c u := hpresΔ c hc u hu
    have hcux : c u ≠ eF 0 := fun h => hcuΔ (h ▸ hx)
    have hcuy : c u ≠ eF 1 := fun h => hcuΔ (h ▸ hy)
    have hgcu : (swap u (eF 0) * swap u (eF 1)) (c u) = c u := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcu hcuy, swap_apply_of_ne_of_ne hcu hcux]
    have hfixy := ((hCmem _).mp hgc).2 _ hy
    rw [Perm.mul_apply, Perm.mul_apply, hginv, hgcu] at hfixy
    exact hcuy hfixy
  obtain ⟨u, hu⟩ : ∃ u, σ u ≠ u := by
    by_contra h
    push Not at h
    have h1 : σ = 1 := Equiv.ext h
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by decide)
  have hσu : σ (σ u) ≠ σ u := by
    rw [hσσ]
    exact Ne.symm hu
  have huσu : u ≠ σ u := Ne.symm hu
  have hm2 : 2 ≤ Nat.card {x // σ x ≠ x} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr
      ⟨⟨u, hu⟩, ⟨σ u, hσu⟩, fun h => huσu (congrArg Subtype.val h)⟩
  have hAne : alternatingGroup Ω ≠ ⊤ := alternatingGroup_ne_top huσu
  have hfixF : ∀ {a b : Ω}, σ a ≠ a → σ b ≠ b → ∀ x, σ x = x → swap a b x = x :=
    fun ha hb x hx => swap_apply_of_ne_of_ne (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))
  rcases eq_alternatingGroup_or_eq_top hT with hTA | hTtop
  ·
    have hCalt : T ⊓ centralizer (L : Set (Perm Ω)) =
        (alternatingGroup {x // σ x ≠ x}).map Perm.ofSubtype := by
      ext c
      rw [hCmem, hTA, mem_map_ofSubtype_alternatingGroup_iff, Perm.mem_alternatingGroup]
      simp only [ne_eq, not_not]
      exact and_comm
    have no5 : ∀ a v₁ v₂ v₃ v₄ : Ω, σ a ≠ a → σ v₁ ≠ v₁ → σ v₂ ≠ v₂ → σ v₃ ≠ v₃ →
        σ v₄ ≠ v₄ → a ≠ v₁ → a ≠ v₂ → a ≠ v₃ → a ≠ v₄ → v₁ ≠ v₂ → v₁ ≠ v₃ → v₁ ≠ v₄ →
        v₂ ≠ v₃ → v₂ ≠ v₄ → v₃ ≠ v₄ → False := by
      intro a v₁ v₂ v₃ v₄ ha h₁ h₂ h₃ h₄ ha₁ ha₂ ha₃ ha₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
      have hz : swap v₁ v₂ * swap v₃ v₄ ∈ T ⊓ centralizer (L : Set (Perm Ω)) := by
        refine (hCmem _).mpr ⟨hTA ▸ ?_, fun x hx => ?_⟩
        · rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap h₁₂, Perm.sign_swap h₃₄]
          decide
        · rw [Perm.mul_apply, hfixF h₃ h₄ x hx, hfixF h₁ h₂ x hx]
      have hz2 : orderOf (swap v₁ v₂ * swap v₃ v₄) = 2 :=
        LocalAnalysis.ComponentInitial.orderOf_swap_mul_swap h₁₂ h₁₃ h₁₄ h₂₃ h₂₄
      have hza : (swap v₁ v₂ * swap v₃ v₄) a = a := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha₃ ha₄, swap_apply_of_ne_of_ne ha₁ ha₂]
      have hc : swap a v₁ * swap a v₂ ∈ T ⊓ centralizer (L : Set (Perm Ω)) := by
        refine (hCmem _).mpr ⟨hTA ▸ ?_, fun x hx => ?_⟩
        · rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap ha₁, Perm.sign_swap ha₂]
          decide
        · rw [Perm.mul_apply, hfixF ha h₂ x hx, hfixF ha h₁ x hx]
      have hca : (swap a v₁ * swap a v₂) a ≠ a := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm ha₂) (Ne.symm h₁₂)]
        exact Ne.symm ha₂
      exact key a ha _ hz hz2 hza _ hc hca
    have hm4le : Nat.card {x // σ x ≠ x} ≤ 4 := by
      by_contra hlt
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 5) (β := {x // σ x ≠ x})
        (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
      have hne : ∀ i j : Fin 5, i ≠ j → (e i : Ω) ≠ e j := fun i j hij h =>
        hij (e.injective (Subtype.ext h))
      exact no5 (e 0) (e 1) (e 2) (e 3) (e 4) (e 0).2 (e 1).2 (e 2).2 (e 3).2 (e 4).2
        (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 0 4 (by decide))
        (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 1 4 (by decide)) (hne 2 3 (by decide))
        (hne 2 4 (by decide)) (hne 3 4 (by decide))
    have hm4 : Nat.card {x // σ x ≠ x} = 4 := by
      have : Nontrivial {x // σ x ≠ x} := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        omega
      have hcard := two_mul_card_alternatingGroup (α := {x // σ x ≠ x})
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcard
      rw [hCalt, card_map_ofSubtype_alternatingGroup] at heven
      by_contra hne
      have hm : Nat.card {x // σ x ≠ x} = 2 ∨ Nat.card {x // σ x ≠ x} = 3 := by omega
      rcases hm with hm | hm
      · rw [hm, show Nat.factorial 2 = 2 from rfl] at hcard
        have h1 : Nat.card (alternatingGroup {x // σ x ≠ x}) = 1 := by omega
        rw [h1] at heven
        exact absurd heven (by decide)
      · rw [hm, show Nat.factorial 3 = 6 from rfl] at hcard
        have h3 : Nat.card (alternatingGroup {x // σ x ≠ x}) = 3 := by omega
        rw [h3] at heven
        exact absurd heven (by decide)
    obtain ⟨⟨w, hwΔ⟩, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({⟨u, hu⟩, ⟨σ u, hσu⟩} : Finset {x // σ x ≠ x})) (t := Finset.univ)
      (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hm4]
        exact Finset.card_le_two.trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Subtype.mk.injEq] at hw
    have hwu : w ≠ u := hw.1
    have hwσu : w ≠ σ u := hw.2
    have hσw : σ (σ w) ≠ σ w := by
      rw [hσσ]
      exact Ne.symm hwΔ
    have hσwu : σ w ≠ u := fun h => hwσu (by rw [← h, hσσ])
    have hσwσu : σ w ≠ σ u := fun h => hwu (σ.injective h)
    have hwσw : w ≠ σ w := Ne.symm hwΔ
    have hsupp : ∀ x, σ x ≠ x ↔ x = u ∨ x = σ u ∨ x = w ∨ x = σ w := by
      intro x
      constructor
      · intro hx
        by_contra h
        simp only [not_or] at h
        exact no5 u (σ u) w (σ w) x hu hσu hwΔ hσw hx huσu (Ne.symm hwu) (Ne.symm hσwu)
          (Ne.symm h.1) (Ne.symm hwσu) (Ne.symm hσwσu) (Ne.symm h.2.1) hwσw (Ne.symm h.2.2.1)
          (Ne.symm h.2.2.2)
      · rintro (rfl | rfl | rfl | rfl)
        · exact hu
        · exact hσu
        · exact hwΔ
        · exact hσw
    have hσeq : σ = swap u (σ u) * swap w (σ w) := by
      ext x
      rw [Perm.mul_apply]
      by_cases hxu : x = u
      · subst hxu
        rw [swap_apply_of_ne_of_ne (Ne.symm hwu) (Ne.symm hσwu), swap_apply_left]
      by_cases hxσu : x = σ u
      · subst hxσu
        rw [swap_apply_of_ne_of_ne (Ne.symm hwσu) (Ne.symm hσwσu), swap_apply_right, hσσ]
      by_cases hxw : x = w
      · subst hxw
        rw [swap_apply_left, swap_apply_of_ne_of_ne hσwu hσwσu]
      by_cases hxσw : x = σ w
      · subst hxσw
        rw [swap_apply_right, swap_apply_of_ne_of_ne hwu hwσu, hσσ]
      have hσx : σ x = x := by
        by_contra hσx
        rcases (hsupp x).mp hσx with h | h | h | h
        · exact hxu h
        · exact hxσu h
        · exact hxw h
        · exact hxσw h
      rw [hσx, swap_apply_of_ne_of_ne hxw hxσw, swap_apply_of_ne_of_ne hxu hxσu]
    refine ⟨hF, hLalt, hCeq, xor_def.mpr (Or.inr ⟨⟨hTA, hm4, u, σ u, w, σ w, huσu,
      Ne.symm hwu, Ne.symm hσwu, Ne.symm hwσu, Ne.symm hσwσu, hwσw, hsupp, hσeq⟩,
      fun h => hAne (hTA.symm.trans h.1)⟩), fun h => absurd (hTA.symm.trans h) hAne,
      fun _ => hCalt⟩
  ·
    have hCsym : T ⊓ centralizer (L : Set (Perm Ω)) =
        (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range := by
      rw [hCeq, hTtop, top_inf_eq]
    have no3 : ∀ a v w : Ω, σ a ≠ a → σ v ≠ v → σ w ≠ w → a ≠ v → a ≠ w → v ≠ w → False := by
      intro a v w ha hv hw hav haw hvw
      have hz : swap v w ∈ T ⊓ centralizer (L : Set (Perm Ω)) :=
        (hCmem _).mpr ⟨hTtop ▸ Subgroup.mem_top _, fun x hx => hfixF hv hw x hx⟩
      have hz2 : orderOf (swap v w) = 2 := Perm.IsSwap.orderOf ⟨v, w, hvw, rfl⟩
      have hc : swap a v ∈ T ⊓ centralizer (L : Set (Perm Ω)) :=
        (hCmem _).mpr ⟨hTtop ▸ Subgroup.mem_top _, fun x hx => hfixF ha hv x hx⟩
      have hca : swap a v a ≠ a := by
        rw [swap_apply_left]
        exact Ne.symm hav
      exact key a ha _ hz hz2 (swap_apply_of_ne_of_ne hav haw) _ hc hca
    have hm2le : Nat.card {x // σ x ≠ x} ≤ 2 := by
      by_contra hlt
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := {x // σ x ≠ x})
        (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
      have hne : ∀ i j : Fin 3, i ≠ j → (e i : Ω) ≠ e j := fun i j hij h =>
        hij (e.injective (Subtype.ext h))
      exact no3 (e 0) (e 1) (e 2) (e 0).2 (e 1).2 (e 2).2 (hne 0 1 (by decide))
        (hne 0 2 (by decide)) (hne 1 2 (by decide))
    have hsupp : ∀ x, σ x ≠ x ↔ x = u ∨ x = σ u := by
      intro x
      constructor
      · intro hx
        by_contra h
        simp only [not_or] at h
        exact no3 u (σ u) x hu hσu hx huσu (Ne.symm h.1) (Ne.symm h.2)
      · rintro (rfl | rfl)
        · exact hu
        · exact hσu
    have hσeq : σ = swap u (σ u) := by
      ext x
      by_cases hxu : x = u
      · subst hxu
        rw [swap_apply_left]
      by_cases hxσu : x = σ u
      · subst hxσu
        rw [swap_apply_right, hσσ]
      have hσx : σ x = x := by
        by_contra hσx
        rcases (hsupp x).mp hσx with h | h
        · exact hxu h
        · exact hxσu h
      rw [hσx, swap_apply_of_ne_of_ne hxu hxσu]
    refine ⟨hF, hLalt, hCeq, xor_def.mpr (Or.inl ⟨⟨hTtop, le_antisymm hm2le hm2,
      u, σ u, huσu, hsupp, hσeq⟩, fun h => hAne (h.1.symm.trans hTtop)⟩), fun _ => hCsym,
      fun h => absurd (h.symm.trans hTtop) hAne⟩

theorem natural_permutation_standard_involution_fixed_support_size [Fintype Ω]
    {T : Subgroup (Perm Ω)} (hT : alternatingGroup Ω ≤ T) {σ : Perm Ω} (hσT : σ ∈ T)
    (hσ : orderOf σ = 2) {L : Subgroup (Perm Ω)}
    (hL : CFSG.Assembly.IsComponentOf L (T ⊓ centralizer ({σ} : Set (Perm Ω))))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup (L.subgroupOf T)) :
    5 ≤ Nat.card {x // σ x = x} ∧
      L = (alternatingGroup {x // σ x = x}).map Perm.ofSubtype ∧
      T ⊓ centralizer (L : Set (Perm Ω)) =
        T ⊓ (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range ∧
      Xor
        (T = ⊤ ∧ Nat.card {x // σ x ≠ x} = 2 ∧
          ∃ a b : Ω, a ≠ b ∧ (∀ x, σ x ≠ x ↔ x = a ∨ x = b) ∧ σ = swap a b)
        (T = alternatingGroup Ω ∧ Nat.card {x // σ x ≠ x} = 4 ∧
          ∃ a b c d : Ω, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            (∀ x, σ x ≠ x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) ∧ σ = swap a b * swap c d) ∧
      (T = ⊤ → T ⊓ centralizer (L : Set (Perm Ω)) =
        (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range) ∧
      (T = alternatingGroup Ω → T ⊓ centralizer (L : Set (Perm Ω)) =
        (alternatingGroup {x // σ x ≠ x}).map Perm.ofSubtype) := by
  have hLT : L ≤ T := hL.1.trans inf_le_left
  obtain ⟨-, heven, hodd, -, -⟩ := hstd
  have hmemC : ∀ k : T, k ∈ centralizer (L.subgroupOf T : Set T) ↔
      (k : Perm Ω) ∈ centralizer (L : Set (Perm Ω)) := fun k => by
    rw [centralizer_subgroupOf_eq hLT, Subgroup.mem_subgroupOf]
  refine natural_permutation_standard_core hT hσT hσ hL ?_ ?_
  · rwa [centralizer_subgroupOf_eq hLT, card_subgroupOf_eq_card_inf] at heven
  · intro g hg z hz hz2 hgz c hc
    have hgN : (⟨g, hg⟩ : T) ∈ normalizer (centralizer (L.subgroupOf T : Set T) : Set T) := by
      by_contra hgN
      have hodd' := hodd ⟨g, hg⟩ hgN
      have hzmem : (⟨z, hz.1⟩ : T) ∈ centralizer (L.subgroupOf T : Set T) ⊓
          (centralizer (L.subgroupOf T : Set T)).map (MulAut.conj (⟨g, hg⟩ : T)).toMonoidHom := by
        refine ⟨(hmemC _).mpr hz.2, ⟨⟨z, hz.1⟩, (hmemC _).mpr hz.2, ?_⟩⟩
        apply Subtype.ext
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv]
        rw [hgz, mul_inv_cancel_right]
      have hdvd := Subgroup.orderOf_dvd_natCard _ hzmem
      rw [← Subgroup.orderOf_coe, show ((⟨z, hz.1⟩ : T) : Perm Ω) = z from rfl, hz2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hdvd)
    have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨c, hc.1⟩).mp ((hmemC _).mpr hc.2)
    exact ⟨T.mul_mem (T.mul_mem hg hc.1) (T.inv_mem hg), (hmemC _).mp h⟩

theorem natural_permutation_standard_involution_fixed_support_size_shared [Fintype Ω]
    {T : Subgroup (Perm Ω)} (hT : alternatingGroup Ω ≤ T) {σ : Perm Ω} (hσT : σ ∈ T)
    (hσ : orderOf σ = 2) {L : Subgroup (Perm Ω)}
    (hLC : L ≤ T ⊓ centralizer ({σ} : Set (Perm Ω)))
    (hL : CFSG.IsComponent (L.subgroupOf (T ⊓ centralizer ({σ} : Set (Perm Ω)))))
    (hstd : CFSG.IsStandardSubgroup (L.subgroupOf T)) :
    5 ≤ Nat.card {x // σ x = x} ∧
      L = (alternatingGroup {x // σ x = x}).map Perm.ofSubtype ∧
      T ⊓ centralizer (L : Set (Perm Ω)) =
        T ⊓ (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range ∧
      Xor
        (T = ⊤ ∧ Nat.card {x // σ x ≠ x} = 2 ∧
          ∃ a b : Ω, a ≠ b ∧ (∀ x, σ x ≠ x ↔ x = a ∨ x = b) ∧ σ = swap a b)
        (T = alternatingGroup Ω ∧ Nat.card {x // σ x ≠ x} = 4 ∧
          ∃ a b c d : Ω, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            (∀ x, σ x ≠ x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) ∧ σ = swap a b * swap c d) ∧
      (T = ⊤ → T ⊓ centralizer (L : Set (Perm Ω)) =
        (Perm.ofSubtype : Perm {x // σ x ≠ x} →* Perm Ω).range) ∧
      (T = alternatingGroup Ω → T ⊓ centralizer (L : Set (Perm Ω)) =
        (alternatingGroup {x // σ x ≠ x}).map Perm.ofSubtype) := by
  have hL' := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLC).mpr hL
  have hLT : L ≤ T := hLC.trans inf_le_left
  obtain ⟨-, heven, hodd, -, -⟩ := hstd
  have hmemC : ∀ k : T, k ∈ centralizer (L.subgroupOf T : Set T) ↔
      (k : Perm Ω) ∈ centralizer (L : Set (Perm Ω)) := fun k => by
    rw [centralizer_subgroupOf_eq hLT, Subgroup.mem_subgroupOf]
  refine natural_permutation_standard_core hT hσT hσ hL' ?_ ?_
  · rwa [centralizer_subgroupOf_eq hLT, card_subgroupOf_eq_card_inf] at heven
  · intro g hg z hz hz2 hgz c hc
    have hgN : (⟨g, hg⟩ : T) ∈ normalizer (centralizer (L.subgroupOf T : Set T) : Set T) := by
      by_contra hgN
      have hodd' := hodd ⟨g, hg⟩ hgN
      have hzmem : (⟨z, hz.1⟩ : T) ∈ centralizer (L.subgroupOf T : Set T) ⊓
          CFSG.conjugate (centralizer (L.subgroupOf T : Set T)) ⟨g, hg⟩ := by
        refine ⟨(hmemC _).mpr hz.2, ⟨⟨z, hz.1⟩, (hmemC _).mpr hz.2, ?_⟩⟩
        apply Subtype.ext
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv, inv_inv]
        rw [mul_assoc, ← hgz, inv_mul_cancel_left]
      have hdvd := Subgroup.orderOf_dvd_natCard _ hzmem
      rw [← Subgroup.orderOf_coe, show ((⟨z, hz.1⟩ : T) : Perm Ω) = z from rfl, hz2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hdvd)
    have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨c, hc.1⟩).mp ((hmemC _).mpr hc.2)
    exact ⟨T.mul_mem (T.mul_mem hg hc.1) (T.inv_mem hg), (hmemC _).mp h⟩

end CFSG.ComponentClassification.SymmetricLocal

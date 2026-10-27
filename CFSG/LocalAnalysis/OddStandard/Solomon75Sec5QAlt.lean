module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS


namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem altFixOf_comm {σ g : Perm (Fin n)} (hg : g ∈ altFixOf σ) : g * σ = σ * g := by
  obtain ⟨hfix, -⟩ := hg
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  by_cases hx : σ x = x
  · rw [hx]
    by_contra hne
    have h1 : σ (g x) ≠ g x := fun e => hne e.symm
    have h2 : g (g x) = g x := hfix _ h1
    have h3 : g x = x := g.injective h2
    exact h1 (by rw [h3, hx])
  · have h1 : σ (σ x) ≠ σ x := fun e => hx (σ.injective e)
    rw [hfix x hx, hfix _ h1]

theorem altFixOf_le_alternatingGroup (σ : Perm (Fin n)) :
    altFixOf σ ≤ alternatingGroup (Fin n) :=
  fun _ hg => Perm.mem_alternatingGroup.2 hg.2

theorem closure_isThreeCycle_altFixOf (σ : Perm (Fin n)) :
    Subgroup.closure {c : Perm (Fin n) | c.IsThreeCycle ∧ c ∈ altFixOf σ} = altFixOf σ := by
  classical
  refine le_antisymm ((Subgroup.closure_le _).2 fun c hc => hc.2) fun g hg => ?_
  have hcomm : g * σ = σ * g := altFixOf_comm hg
  have h₁ : ∀ x, (σ (g x) = g x) ↔ (σ x = x) := by
    intro x
    have h : σ (g x) = g (σ x) := (congrArg (fun f => f x) hcomm).symm
    rw [h]
    exact g.injective.eq_iff
  have h₂ : ∀ x, g x ≠ x → σ x = x := fun x hx => by
    by_contra hσx
    exact hx (hg.1 x hσx)
  have hg' : ofSubtype (g.subtypePerm h₁ : Perm {x // σ x = x}) = g :=
    ofSubtype_subtypePerm h₁ h₂
  have hmem : (g.subtypePerm h₁ : Perm {x // σ x = x}) ∈
      Subgroup.closure {c : Perm {x // σ x = x} | c.IsThreeCycle} := by
    rw [closure_three_cycles_eq_alternating, Perm.mem_alternatingGroup, ← sign_ofSubtype, hg']
    exact hg.2
  have hmap := Subgroup.mem_map_of_mem
    (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)) hmem
  rw [MonoidHom.map_closure, hg'] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨?_, fun x hx => ofSubtype_apply_of_not_mem c hx, ?_⟩
  · unfold Equiv.Perm.IsThreeCycle at hc ⊢
    rw [cycleType_ofSubtype]
    exact hc
  · rw [sign_ofSubtype]
    exact hc.sign

theorem CoverSetup.Induces.exists_mem_fixSub_of_mem_altFixOf [Finite K] {C : CoverSetup n K}
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) {a : Perm (Fin n)}
    (ha : a ∈ altFixOf σ) : ∃ x ∈ fixSub α, C.ρ x = a := by
  refine h.exists_mem_fixSub_of_odd_generated (altFixOf_le_alternatingGroup σ)
    (fun q hq => altFixOf_comm hq) (closure_isThreeCycle_altFixOf σ) ?_ a ha
  intro g hg
  rw [hg.1.orderOf]
  decide

end AhatData

theorem alt_odd_normal_eq_bot_of_five_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Fintype.card Ω) {N : Subgroup (Perm Ω)} (hNA : N ≤ alternatingGroup Ω)
    (hn : ∀ a ∈ alternatingGroup Ω, ∀ y ∈ N, a * y * a⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hα : 5 ≤ Nat.card Ω := by rwa [Nat.card_eq_fintype_card]
  have := alternatingGroup.isSimpleGroup hα
  have hnorm : (N.subgroupOf (alternatingGroup Ω)).Normal :=
    ⟨fun y hy a => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simpa using hn a a.2 y hy⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup Ω)) with
    hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hbot.eq_bot_of_le hNA
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at htop
    have hAodd : Odd (Nat.card (alternatingGroup Ω)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le htop)
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have h2 := two_mul_nat_card_alternatingGroup (α := Ω)
    rw [Nat.card_perm] at h2
    have h24 : 24 ∣ 2 * Nat.card (alternatingGroup Ω) := by
      rw [h2]
      exact Nat.factorial_dvd_factorial (by omega : 4 ≤ Nat.card Ω)
    obtain ⟨k, hk⟩ := hAodd
    omega

theorem fin4_odd_key : ∀ g : Perm (Fin 4), g ^ 3 = 1 → g ≠ 1 → ∃ h : Perm (Fin 4),
    sign h = 1 ∧ (g⁻¹ * (h * g * h⁻¹)) ^ 2 = 1 ∧ g⁻¹ * (h * g * h⁻¹) ≠ 1 := by
  decide +kernel

theorem alt_odd_normal_eq_bot_of_card_four {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h4 : Fintype.card Ω = 4) {N : Subgroup (Perm Ω)}
    (hn : ∀ a ∈ alternatingGroup Ω, ∀ y ∈ N, a * y * a⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  obtain ⟨e⟩ : Nonempty (Ω ≃ Fin 4) := Fintype.card_eq.1 (by rw [h4, Fintype.card_fin])
  refine (Subgroup.eq_bot_iff_forall N).2 fun g hg => ?_
  by_contra hne
  have hodd' : Odd (orderOf g) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hg)
  have h24 : orderOf g ∣ 24 := by
    have := orderOf_dvd_natCard g
    rwa [Nat.card_perm, Nat.card_eq_fintype_card, h4] at this
  have h3 : orderOf g ∣ 3 := by
    have h24' : orderOf g ∣ 3 * 2 ^ 3 := by simpa using h24
    exact (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hodd')).dvd_of_dvd_mul_left h24'
  have hg3 : g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
  have hφg3 : e.permCongrHom g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hφg1 : e.permCongrHom g ≠ 1 := fun h =>
    hne ((map_eq_one_iff _ e.permCongrHom.injective).1 h)
  obtain ⟨h', hsign, h2, h1⟩ := fin4_odd_key _ hφg3 hφg1
  have hA : e.permCongrHom.symm h' ∈ alternatingGroup Ω := by
    rw [Perm.mem_alternatingGroup, Equiv.permCongrHom_symm, Equiv.permCongrHom_coe,
      sign_permCongr]
    exact hsign
  have hc : g⁻¹ * (e.permCongrHom.symm h' * g * (e.permCongrHom.symm h')⁻¹) ∈ N :=
    N.mul_mem (N.inv_mem hg) (hn _ hA g hg)
  have hφc : e.permCongrHom (g⁻¹ * (e.permCongrHom.symm h' * g * (e.permCongrHom.symm h')⁻¹)) =
      (e.permCongrHom g)⁻¹ * (h' * e.permCongrHom g * h'⁻¹) := by
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hc2 : (g⁻¹ * (e.permCongrHom.symm h' * g * (e.permCongrHom.symm h')⁻¹)) ^ 2 = 1 := by
    apply e.permCongrHom.injective
    rw [map_pow, hφc, map_one]
    exact h2
  have hc1 : g⁻¹ * (e.permCongrHom.symm h' * g * (e.permCongrHom.symm h')⁻¹) ≠ 1 :=
    fun hc1 => h1 (by rw [← hφc, hc1, map_one])
  have hord := orderOf_eq_prime hc2 hc1
  obtain ⟨m, hm⟩ := Subgroup.orderOf_dvd_natCard N hc
  obtain ⟨k, hk⟩ := hodd
  rw [hord] at hm
  omega

theorem alt_odd_normal_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h4 : 4 ≤ Fintype.card Ω)
    {N : Subgroup (Perm Ω)} (hNA : N ≤ alternatingGroup Ω)
    (hn : ∀ a ∈ alternatingGroup Ω, ∀ y ∈ N, a * y * a⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  rcases Nat.eq_or_lt_of_le h4 with h | h
  · exact alt_odd_normal_eq_bot_of_card_four h.symm hn hodd
  · exact alt_odd_normal_eq_bot_of_five_le h hNA hn hodd

theorem exists_ofSubtype_eq_of_mem_altFixOf {n : ℕ} {σ g : Perm (Fin n)}
    (hg : g ∈ AhatData.altFixOf σ) : ∃ c : Perm {x // σ x = x}, ofSubtype c = g := by
  have hcomm : g * σ = σ * g := AhatData.altFixOf_comm hg
  have h₁ : ∀ x, (σ (g x) = g x) ↔ (σ x = x) := by
    intro x
    have h : σ (g x) = g (σ x) := (congrArg (fun f => f x) hcomm).symm
    rw [h]
    exact g.injective.eq_iff
  have h₂ : ∀ x, g x ≠ x → σ x = x := fun x hx => by
    by_contra hσx
    exact hx (hg.1 x hσx)
  exact ⟨g.subtypePerm h₁, ofSubtype_subtypePerm h₁ h₂⟩

theorem altFixOf_odd_normal_eq_bot {n : ℕ} {σ : Perm (Fin n)}
    (hF : 4 ≤ (Finset.univ.filter fun i => σ i = i).card)
    {N : Subgroup (Perm (Fin n))} (hN : N ≤ AhatData.altFixOf σ)
    (hn : ∀ a ∈ AhatData.altFixOf σ, ∀ y ∈ N, a * y * a⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hinj : Function.Injective
      (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)) := ofSubtype_injective
  have hmem : ∀ c : Perm {x // σ x = x}, c ∈ alternatingGroup {x // σ x = x} →
      (ofSubtype c : Perm (Fin n)) ∈ AhatData.altFixOf σ := fun c hc =>
    ⟨fun x hx => ofSubtype_apply_of_not_mem c hx,
      by rw [sign_ofSubtype]; exact Perm.mem_alternatingGroup.1 hc⟩
  have h4 : 4 ≤ Fintype.card {x // σ x = x} := by rwa [Fintype.card_subtype]
  have hNA : N.comap (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)) ≤
      alternatingGroup {x // σ x = x} := by
    intro c hc
    have h := (hN (Subgroup.mem_comap.1 hc)).2
    rw [Perm.mem_alternatingGroup]
    rwa [sign_ofSubtype] at h
  have hn' : ∀ a ∈ alternatingGroup {x // σ x = x},
      ∀ y ∈ N.comap (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)),
        a * y * a⁻¹ ∈ N.comap (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)) := by
    intro a ha y hy
    rw [Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact hn _ (hmem a ha) _ hy
  have hrange : N ≤ (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)).range := fun g hg =>
    MonoidHom.mem_range.2 (exists_ofSubtype_eq_of_mem_altFixOf (hN hg))
  have hcard : Nat.card (N.comap (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n))) =
      Nat.card N := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hrange]
  have hbot := alt_odd_normal_eq_bot h4 hNA hn' (by rwa [hcard])
  refine (Subgroup.eq_bot_iff_forall N).2 fun y hy => ?_
  obtain ⟨c, rfl⟩ := exists_ofSubtype_eq_of_mem_altFixOf (hN hy)
  have hc : c ∈ N.comap (ofSubtype : Perm {x // σ x = x} →* Perm (Fin n)) := hy
  rw [hbot, Subgroup.mem_bot] at hc
  rw [hc, map_one]

theorem fixes_of_comm_altFixOf {n : ℕ} {σ s : Perm (Fin n)} (hσs : s * σ = σ * s)
    (hF : 4 ≤ (Finset.univ.filter fun i => σ i = i).card)
    (hcomm : ∀ a ∈ AhatData.altFixOf σ, a * s = s * a) : ∀ i, σ i = i → s i = i := by
  intro f hf
  by_contra hsf
  have hsmem : σ (s f) = s f := by
    have h := congrArg (fun p => p f) hσs
    simp only [Perm.mul_apply, hf] at h
    exact h.symm
  have hcard : 1 < (((Finset.univ.filter fun i => σ i = i).erase f).erase (s f)).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.filter fun i => σ i = i) (a := f)
    have h2 := Finset.pred_card_le_card_erase
      (s := (Finset.univ.filter fun i => σ i = i).erase f) (a := s f)
    omega
  obtain ⟨g, hg, k, hk, hgk⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hg hk
  obtain ⟨hgs, hgf, hσg⟩ := hg
  obtain ⟨hks, hkf, hσk⟩ := hk
  have haA : swap f g * swap g k ∈ AhatData.altFixOf σ := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hxf : x ≠ f := fun e => hx (by rw [e]; exact hf)
      have hxg : x ≠ g := fun e => hx (by rw [e]; exact hσg)
      have hxk : x ≠ k := fun e => hx (by rw [e]; exact hσk)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxg hxk, swap_apply_of_ne_of_ne hxf hxg]
    · rw [Perm.sign_mul, Perm.sign_swap (Ne.symm hgf), Perm.sign_swap hgk]
      decide
  have h := congrArg (fun p => p f) (hcomm _ haA)
  simp only [Perm.mul_apply] at h
  rw [swap_apply_of_ne_of_ne (Ne.symm hgs) (Ne.symm hks),
    swap_apply_of_ne_of_ne hsf (Ne.symm hgs),
    swap_apply_of_ne_of_ne (Ne.symm hgf) (Ne.symm hkf), swap_apply_left] at h
  exact hgf (s.injective h).symm

theorem eq_bot_of_normal_exp_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Fintype.card Ω) {W : Subgroup (Perm Ω)} (hWA : W ≤ alternatingGroup Ω)
    (hn : ∀ a ∈ alternatingGroup Ω, ∀ y ∈ W, a * y * a⁻¹ ∈ W)
    (hexp : ∀ y ∈ W, y * y = 1) : W = ⊥ := by
  have hsimple : IsSimpleGroup (alternatingGroup Ω) :=
    alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card])
  have hnorm : (W.subgroupOf (alternatingGroup Ω)).Normal := by
    refine ⟨fun y hy a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hn a a.2 y hy
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hWA hy⟩ : alternatingGroup Ω) ∈ W.subgroupOf (alternatingGroup Ω) := hy
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    obtain ⟨p, q, r, hpq, hpr, hqr⟩ := Fintype.two_lt_card_iff.1 (by omega : 2 < Fintype.card Ω)
    set c : Perm Ω := swap p q * swap q r with hc
    have hcA : c ∈ alternatingGroup Ω := by
      rw [Perm.mem_alternatingGroup, hc, Perm.sign_mul, Perm.sign_swap hpq, Perm.sign_swap hqr]
      decide
    have hcW : c ∈ W := by
      have : (⟨c, hcA⟩ : alternatingGroup Ω) ∈ W.subgroupOf (alternatingGroup Ω) := by
        rw [ht]; exact Subgroup.mem_top _
      exact this
    have h1 := hexp c hcW
    have h2 : (c * c) p = p := by rw [h1]; rfl
    have hcp : c p = q := by
      rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpr, swap_apply_left]
    have hcq : c q = r := by
      rw [hc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpr.symm hqr.symm]
    rw [Perm.mul_apply, hcp, hcq] at h2
    exact hpr h2.symm

end CFSG.OddStandard.Solomon75

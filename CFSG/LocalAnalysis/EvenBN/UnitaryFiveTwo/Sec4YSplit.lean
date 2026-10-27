module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YPrelim
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckLevi
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDAvg
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

@[expose] noncomputable def Data.Lev {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.pull levHom.range

@[expose] noncomputable def Data.E₂ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  ⁅d.Lev, d.U⁆

theorem le_normalizer_commutator_left' {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro a ha
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : ⁅H, K⁆ ≤ (⁅H, K⁆).comap (MulAut.conj a).toMonoidHom := by
    rw [commutator_le]
    intro b hb c hc
    change a * ⁅b, c⁆ * a⁻¹ ∈ ⁅H, K⁆
    have e : a * ⁅b, c⁆ * a⁻¹ = ⁅a * b, c⁆ * ⁅a, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (commutator_mem_commutator (mul_mem ha hb) hc)
      (inv_mem (commutator_mem_commutator ha hc))
  exact hle hy

theorem le_normalizer_commutator_right' {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    K ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [commutator_comm]
  exact le_normalizer_commutator_left' K H

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem Lev_le_L : d.Lev ≤ d.L := d.pull_le_L _

omit [Finite G] in
theorem exists_eq_levSU {l : G} (hl : l ∈ d.Lev) :
    ∃ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), l = d.ι (levSU A hA) := by
  obtain ⟨_, ⟨U, rfl⟩, rfl⟩ := hl
  exact ⟨_, _, congrArg d.ι (levHom_apply U)⟩

theorem Lev_comm_t (h : d.Hyp) {l : G} (hl : l ∈ d.Lev) : l * d.t = d.t * l :=
  comm_of_mem_centralizer h.t_mem (Lev_le_L hl)

theorem Lev_le_normalizer
    (h : d.Hyp) :
    d.Lev ≤ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := fun l hl => by
  obtain ⟨A, hA, rfl⟩ := exists_eq_levSU hl
  exact h.ι_mem_normalizer fun a ha => levSU_conj_mem_A₂sub A hA ha

omit [Finite G] in
theorem Lev_conj_mem_F {l f : G} (hl : l ∈ d.Lev) (hf : f ∈ d.F) : l * f * l⁻¹ ∈ d.F := by
  obtain ⟨A, hA, rfl⟩ := exists_eq_levSU hl
  obtain ⟨φ, hφ, rfl⟩ := hf
  rw [ι_conj]
  exact d.ι_mem_pull_iff.2 (levSU_conj_mem_Fsub A hA hφ)

omit [Finite G] in
theorem Lev_comm_e₂ {l : G} (hl : l ∈ d.Lev) : l * d.e₂ = d.e₂ * l := by
  obtain ⟨A, hA, rfl⟩ := exists_eq_levSU hl
  rw [Data.e₂, ← map_mul, ← map_mul, levSU_comm_e₂SU]

theorem Lev_le_normalizer_U
    (h : d.Hyp) : d.Lev ≤ normalizer (d.U : Set G) := by
  intro l hl
  have hlX : l ∈ normalizer ((d.withT d.F : Subgroup G) : Set G) := by
    rw [h.normalizer_withT_F_eq]
    exact h.Lev_le_normalizer hl
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxC, hxe⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨conj_mem_oTwo (X := normalizer ((d.withT d.F : Subgroup G) :
    Set G)) hlX hxC, mem_centralizer_singleton_iff.2 ?_⟩
  have hle := Lev_comm_e₂ hl
  have hxe' : x * d.e₂ = d.e₂ * x := mem_centralizer_singleton_iff.1 hxe
  calc l * x * l⁻¹ * d.e₂ = l * x * (l⁻¹ * d.e₂ * l) * l⁻¹ := by group
    _ = l * x * d.e₂ * l⁻¹ := by rw [show l⁻¹ * d.e₂ * l = d.e₂ by rw [mul_assoc, ← hle]; group]
    _ = l * d.e₂ * x * l⁻¹ := by rw [mul_assoc l x, hxe', ← mul_assoc]
    _ = d.e₂ * (l * x * l⁻¹) := by rw [hle]; group

omit [Finite G] in
theorem X₂_le_Lev : d.X₂ ≤ d.Lev := d.pull_mono X₂sub_le_levHom_range

omit [Finite G] in
theorem card_X₂ : Nat.card d.X₂ = 4 := by rw [Data.X₂, d.card_pull, card_X₂sub]

omit [Finite G] in
theorem card_Lev : Nat.card d.Lev = 180 := by rw [Data.Lev, d.card_pull, card_levHom_range]

omit [Finite G] in
theorem odd_relIndex_X₂_Lev : Odd (d.X₂.relIndex d.Lev) := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) d.X₂ d.Lev bot_le X₂_le_Lev
  rw [relIndex_bot_left, relIndex_bot_left, card_X₂, card_Lev] at h
  have : d.X₂.relIndex d.Lev = 45 := by omega
  rw [this]
  decide

theorem F_le_closure_conj (_h : d.Hyp) :
    d.F ≤ closure ((fun x => x * d.ι (x₁SU 0 1 zero_one_rel) * x⁻¹) '' (d.X₂ : Set G)) := by
  have hle := map_mono (f := d.ι) Fsub_le_closure_conj_x₁
  rw [MonoidHom.map_closure] at hle
  refine hle.trans (closure_mono ?_)
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  refine ⟨d.ι (x₂SU c), ⟨x₂SU c, x₂SU_mem c, rfl⟩, ?_⟩
  rw [conjX₁, map_mul, map_mul, map_inv]

theorem t_not_mem_E₂
    (h : d.Hyp) : d.t ∉ d.E₂ := by
  classical
  set f₀ := d.ι (x₁SU 0 1 zero_one_rel) with hf₀
  have hf₀F : f₀ ∈ d.F := d.ι_mem_pull_iff.2 (genFSU_mem 0)
  obtain ⟨d₀, hd₀, hd₀t⟩ := h.exists_U_crossed_eq hf₀F
  have hX₂U : ∀ x ∈ d.X₂, x ∈ normalizer (d.U : Set G) := fun x hx =>
    h.Lev_le_normalizer_U (X₂_le_Lev hx)
  have : Fintype (d.X₂ : Set G) := Fintype.ofFinite _
  set S : Finset G := (d.X₂ : Set G).toFinset.image (fun x => x * d₀ * x⁻¹) with hS
  have hSmem : ∀ s, s ∈ S ↔ ∃ x ∈ d.X₂, x * d₀ * x⁻¹ = s := by
    intro s
    simp [hS]
  have hSU : ∀ s ∈ S, s ∈ d.U := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := (hSmem s).1 hs
    exact (mem_normalizer_iff.1 (hX₂U x hx) d₀).1 hd₀
  set C := d.F ⊔ closure (S : Set G) with hC
  have hCU : C ≤ d.U := sup_le h.F_le_U ((closure_le _).2 fun s hs => hSU s hs)
  have hcardS : S.card ≤ 4 := by
    refine Finset.card_image_le.trans ?_
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact card_X₂.le
  have hcardC : Nat.card C ≤ 2 ^ 8 := by
    refine (card_sup_closure_le S (fun s hs => ?_) (fun s hs => h.U_sq (hSU s hs))
      (fun s hs s' hs' => ?_)).trans ?_
    · refine mem_normalizer_fintype fun f hf => ?_
      rw [h.U_comm_F (hSU s hs) hf, mul_inv_cancel_right]
      exact hf
    · have := h.commutator_U_mem_F (hSU s hs) (hSU s' hs')
      rwa [commutatorElement_def] at this
    · rw [d.card_F]
      calc 2 ^ 4 * 2 ^ S.card ≤ 2 ^ 4 * 2 ^ 4 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hcardS)
        _ = 2 ^ 8 := by norm_num
  have hcrC : ∀ a ∈ d.F, ∃ c ∈ C, c⁻¹ * d.t * c * d.t = a := by
    let R : Subgroup G :=
      { carrier := {b | ∃ c ∈ C, c⁻¹ * d.t * c * d.t = b}
        one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_mul_t]⟩
        mul_mem' := by
          rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
          refine ⟨p * q, mul_mem hp hq, ?_⟩
          exact crossed_mul h.t_mul_t (h.U_comm_F (hCU hq) (h.U_crossed_mem_F (hCU hp))).symm
        inv_mem' := by
          rintro _ ⟨p, hp, rfl⟩
          exact ⟨p⁻¹, inv_mem hp, crossed_inv h.t_mul_t
            (h.U_comm_F (hCU hp) (h.U_crossed_mem_F (hCU hp))).symm⟩ }
    have horb : (fun x => x * f₀ * x⁻¹) '' (d.X₂ : Set G) ⊆ R := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x * d₀ * x⁻¹, mem_sup_right (subset_closure ((hSmem _).2 ⟨x, hx, rfl⟩)), ?_⟩
      rw [crossed_conj (h.Lev_comm_t (X₂_le_Lev hx)), hd₀t]
    intro a ha
    exact ((closure_le R).2 horb) (h.F_le_closure_conj ha)
  have htC : d.t ∉ C := by
    intro htC
    have hcardeq := card_eq_of_crossed_onto h.t_mul_t
      (fun c hc => mem_centralizer_iff.2 fun f hf => (h.U_comm_F (hCU hc) hf).symm)
      (fun c hc => h.U_crossed_mem_F (hCU hc)) hcrC
    have hle : d.withT d.F ≤ C ⊓ centralizer ({d.t} : Set G) :=
      le_inf (sup_le le_sup_left (zpowers_le.2 htC)) h.withT_F_le_H
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card_withT_F] at h1
    rw [d.card_F] at hcardeq
    have : 2 ^ 9 ≤ Nat.card C := by rw [hcardeq]; nlinarith
    omega
  have htnorm : ∀ c ∈ C, d.t * c * d.t ∈ C := by
    intro c hc
    have e : d.t * c * d.t = c * (c⁻¹ * d.t * c * d.t) := by group
    rw [e]
    exact mul_mem hc (mem_sup_left (h.U_crossed_mem_F (hCU hc)))
  have hdich : ∀ x ∈ d.U, x ∉ C → d.t * x ∈ C := by
    intro x hx hxC
    obtain ⟨c, hc, hct⟩ := hcrC _ (h.U_crossed_mem_F hx)
    have hxc : x * c⁻¹ ∈ d.withT d.F := by
      rw [← h.U_inf_H]
      refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (hCU hc)), ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have e1 : x⁻¹ * d.t * x = c⁻¹ * d.t * c := mul_right_cancel hct.symm
      calc x * c⁻¹ * d.t = x * (c⁻¹ * d.t * c) * c⁻¹ := by group
        _ = x * (x⁻¹ * d.t * x) * c⁻¹ := by rw [e1]
        _ = d.t * (x * c⁻¹) := by group
    obtain ⟨f, hf, k, hk⟩ := h.exists_eq_mul_of_mem_withT_F hxc
    have hk' : d.t ^ k = d.t ^ (k % 2) := by
      rw [← zpow_mod_orderOf, h.t_two]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk', h0, zpow_zero, mul_one] at hk
      exact absurd (by
        have := mul_mem (mem_sup_left hf : f ∈ C) hc
        rwa [← hk, inv_mul_cancel_right] at this) hxC
    · rw [hk', h1, zpow_one] at hk
      have e : d.t * x = f * c := by
        have hx' : x = f * d.t * c := by rw [← hk]; group
        rw [hx', ← mul_assoc, ← mul_assoc, ← h.t_comm_F hf, mul_assoc f, h.t_mul_t, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hf) hc
  let f₁ : G → ZMod 2 := fun x => if x ∈ C then 0 else 1
  have hf₁ : ∀ x ∈ d.U, ∀ y ∈ d.U, f₁ (x * y) = f₁ x + f₁ y := by
    intro x hx y hy
    by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
    · simp [f₁, hxC, hyC, mul_mem hxC hyC]
    · have : x * y ∉ C := fun hm => hyC (by simpa using mul_mem (inv_mem hxC) hm)
      simp [f₁, hxC, hyC, this]
    · have : x * y ∉ C := fun hm => hxC (by simpa using mul_mem hm (inv_mem hyC))
      simp [f₁, hxC, hyC, this]
    · have hxt := hdich x hx hxC
      have hyt := hdich y hy hyC
      have : x * y ∈ C := by
        have e : x * y = (d.t * (d.t * x) * d.t) * (d.t * y) := by
          rw [show (d.t * (d.t * x) * d.t) * (d.t * y) = (d.t * d.t) * x * (d.t * d.t) * y by
            group, h.t_mul_t]
          group
        rw [e]
        exact mul_mem (htnorm _ hxt) hyt
      simp only [f₁, hxC, hyC, this, ite_true, ite_false]
      decide
  have hf₁X₂ : ∀ p ∈ d.X₂, ∀ x ∈ d.U, f₁ (p⁻¹ * x * p) = f₁ x := by
    intro p hp x _
    have hpC : p⁻¹ ∈ normalizer (C : Set G) := by
      refine mem_normalizer_fintype fun c hc => ?_
      have hle : C ≤ C.comap (MulAut.conj p⁻¹).toMonoidHom := by
        refine sup_le (fun a ha => ?_) ((closure_le _).2 fun s hs => ?_)
        · change p⁻¹ * a * p⁻¹⁻¹ ∈ C
          exact mem_sup_left (Lev_conj_mem_F (inv_mem (X₂_le_Lev hp)) ha)
        · change p⁻¹ * s * p⁻¹⁻¹ ∈ C
          obtain ⟨x, hx, rfl⟩ := (hSmem s).1 hs
          refine mem_sup_right (subset_closure ((hSmem _).2 ⟨p⁻¹ * x, mul_mem (inv_mem hp) hx,
            by group⟩))
      exact hle hc
    have hiff : p⁻¹ * x * p ∈ C ↔ x ∈ C := by
      have := mem_normalizer_iff.1 hpC x
      rw [inv_inv] at this
      exact this.symm
    simp only [f₁, hiff]
  obtain ⟨F', hF'add, hF'Λ, hF'fix⟩ := exists_invariant_of_odd_index odd_relIndex_X₂_Lev
    h.Lev_le_normalizer_U f₁ hf₁ hf₁X₂
  have hF't : F' d.t = 1 := by
    rw [hF'fix d.t h.t_mem_U fun l hl => h.Lev_comm_t hl]
    simp [f₁, htC]
  have hF'1 : F' 1 = 0 := by
    have := hF'add 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    have h2 : F' 1 + F' 1 = 0 := by
      generalize F' 1 = a
      fin_cases a <;> rfl
    rw [← this] at h2
    exact h2
  let K : Subgroup G :=
    { carrier := {x | x ∈ d.U ∧ F' x = 0}
      one_mem' := ⟨one_mem _, hF'1⟩
      mul_mem' := by
        rintro x y ⟨hx, hFx⟩ ⟨hy, hFy⟩
        exact ⟨mul_mem hx hy, by rw [hF'add x hx y hy, hFx, hFy, add_zero]⟩
      inv_mem' := by
        rintro x ⟨hx, hFx⟩
        refine ⟨inv_mem hx, ?_⟩
        have := hF'add x⁻¹ (inv_mem hx) x hx
        rw [inv_mul_cancel, hF'1, hFx, add_zero] at this
        exact this.symm }
  have hle : d.E₂ ≤ K := by
    rw [Data.E₂, commutator_le]
    intro l hl y hy
    have hly : l * y * l⁻¹ ∈ d.U := (mem_normalizer_iff.1 (h.Lev_le_normalizer_U hl) y).1 hy
    refine ⟨mul_mem hly (inv_mem hy), ?_⟩
    rw [commutatorElement_def, hF'add _ hly _ (inv_mem hy)]
    have h1 : F' (l * y * l⁻¹) = F' y := by
      have := hF'Λ l⁻¹ (inv_mem hl) y hy
      rwa [inv_inv] at this
    rw [h1, ← hF'add y hy y⁻¹ (inv_mem hy), mul_inv_cancel, hF'1]
  intro htE
  have := (hle htE).2
  rw [hF't] at this
  exact one_ne_zero this

theorem E₂_le_U
    (h : d.Hyp) : d.E₂ ≤ d.U := by
  rw [Data.E₂, commutator_le]
  intro l hl y hy
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (h.Lev_le_normalizer_U hl) y).1 hy) (inv_mem hy)

theorem commutator_Lev_F (_h : d.Hyp) : ⁅d.Lev, d.F⁆ = d.F := by
  have hle : ⁅d.Lev, d.F⁆ ≤ d.F := by
    rw [commutator_le]
    intro l hl f hf
    rw [commutatorElement_def]
    exact mul_mem (Lev_conj_mem_F hl hf) (inv_mem hf)
  set R : Subgroup SU52 := (⁅d.Lev, d.F⁆).comap d.ι with hR
  have hRF : R ≤ Fsub := fun α hα => d.ι_mem_pull_iff.1 (hle hα)
  have hRL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ R := by
    intro A hA r hr
    have hl : d.ι (levSU A hA) ∈ d.Lev :=
      ⟨levSU A hA, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne_zero, rfl⟩, rfl⟩
    change d.ι (levSU A hA * r * (levSU A hA)⁻¹) ∈ ⁅d.Lev, d.F⁆
    rw [← ι_conj]
    exact (mem_normalizer_iff.1 (le_normalizer_commutator_left' _ _ hl) _).1 hr
  have hne : x₂SU 1 * x₁SU 0 1 zero_one_rel * (x₂SU 1)⁻¹ * (x₁SU 0 1 zero_one_rel)⁻¹ ∈ R := by
    change d.ι _ ∈ ⁅d.Lev, d.F⁆
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def]
    exact commutator_mem_commutator (X₂_le_Lev ⟨_, x₂SU_mem 1, rfl⟩)
      (d.ι_mem_pull_iff.2 (genFSU_mem 0))
  have hne1 := conj_x₂_x₁_ne_one
  rcases eq_bot_or_eq_Fsub_or_eq_A₂sub (hRF.trans Fsub_le_A₂sub) hRL with hb | hF | hA
  · exact absurd ((mem_bot.1 (hb ▸ hne))) hne1
  · refine le_antisymm hle fun f hf => ?_
    obtain ⟨φ, hφ, rfl⟩ := hf
    exact (show φ ∈ R from hF ▸ hφ)
  · exfalso
    have := Subgroup.card_le_of_le (hA ▸ hRF)
    rw [card_A₂sub, card_Fsub] at this
    norm_num at this

theorem F_le_E₂ (h : d.Hyp) :
    d.F ≤ d.E₂ := by
  rw [← h.commutator_Lev_F]
  exact commutator_mono le_rfl h.F_le_U

theorem exists_E₂_crossed_eq
    (h : d.Hyp) {a : G} (ha : a ∈ d.F) :
    ∃ x ∈ d.E₂, x⁻¹ * d.t * x * d.t = a := by
  let R : Subgroup G :=
    { carrier := {b | ∃ x ∈ d.E₂, x⁻¹ * d.t * x * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_mul_t]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, crossed_mul h.t_mul_t
          (h.U_comm_F (h.E₂_le_U hq) (h.U_crossed_mem_F (h.E₂_le_U hp))).symm⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, crossed_inv h.t_mul_t
          (h.U_comm_F (h.E₂_le_U hp) (h.U_crossed_mem_F (h.E₂_le_U hp))).symm⟩ }
  have hle : ⁅d.Lev, d.F⁆ ≤ R := by
    rw [commutator_le]
    intro l hl f hf
    obtain ⟨u, hu, hut⟩ := h.exists_U_crossed_eq hf
    refine ⟨⁅l, u⁆, commutator_mem_commutator hl hu, ?_⟩
    have hlu : l * u * l⁻¹ ∈ d.U := (mem_normalizer_iff.1 (h.Lev_le_normalizer_U hl) u).1 hu
    rw [commutatorElement_def, crossed_mul h.t_mul_t
      (h.U_comm_F (inv_mem hu) (h.U_crossed_mem_F hlu)).symm, crossed_conj (h.Lev_comm_t hl),
      hut, crossed_inv h.t_mul_t (h.U_comm_F hu (h.U_crossed_mem_F hu)).symm, hut,
      commutatorElement_def]
  rw [h.commutator_Lev_F] at hle
  exact hle ha

theorem E₂_inf_H
    (h : d.Hyp) : d.E₂ ⊓ d.H = d.F := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.F_le_E₂ (h.F_le_L.trans h.L_le_H))
  obtain ⟨hxE, hxH⟩ := Subgroup.mem_inf.1 hx
  have hxZ : x ∈ d.withT d.F := by
    rw [← h.U_inf_H]
    exact Subgroup.mem_inf.2 ⟨h.E₂_le_U hxE, hxH⟩
  obtain ⟨f, hf, k, hk⟩ := h.exists_eq_mul_of_mem_withT_F hxZ
  have hk' : d.t ^ k = d.t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk, hk', h0, zpow_zero, mul_one]
    exact hf
  · exfalso
    rw [hk', h1, zpow_one] at hk
    apply h.t_not_mem_E₂
    have := mul_mem (inv_mem (h.F_le_E₂ hf)) hxE
    rwa [hk, inv_mul_cancel_left] at this

theorem card_E₂
    (h : d.Hyp) : Nat.card d.E₂ = 2 ^ 8 := by
  have := card_eq_of_crossed_onto h.t_mul_t
    (fun x hx => mem_centralizer_iff.2 fun f hf => (h.U_comm_F (h.E₂_le_U hx) hf).symm)
    (fun _ hy => h.U_crossed_mem_F (h.E₂_le_U hy)) fun _ hb => h.exists_E₂_crossed_eq hb
  rw [show (d.E₂ ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.F from h.E₂_inf_H,
    d.card_F] at this
  rw [this]
  norm_num

theorem sup_zpowers_E₂
    (h : d.Hyp) : d.E₂ ⊔ zpowers d.t = d.U := by
  refine le_antisymm (sup_le h.E₂_le_U (zpowers_le.2 h.t_mem_U)) fun x hx => ?_
  obtain ⟨e, he, het⟩ := h.exists_E₂_crossed_eq (h.U_crossed_mem_F hx)
  have hxe : x * e⁻¹ ∈ d.withT d.F := by
    rw [← h.U_inf_H]
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (h.E₂_le_U he)), ?_⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have e1 : x⁻¹ * d.t * x = e⁻¹ * d.t * e := mul_right_cancel het.symm
    calc x * e⁻¹ * d.t = x * (e⁻¹ * d.t * e) * e⁻¹ := by group
      _ = x * (x⁻¹ * d.t * x) * e⁻¹ := by rw [e1]
      _ = d.t * (x * e⁻¹) := by group
  obtain ⟨f, hf, k, hk⟩ := h.exists_eq_mul_of_mem_withT_F hxe
  have hx' : x = f * d.t ^ k * e := by rw [← hk]; group
  rw [hx', (Commute.zpow_right (h.t_comm_F hf) k).eq, mul_assoc]
  exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers _) k))
    (mem_sup_left (mul_mem (h.F_le_E₂ hf) he))

theorem le_normalizer_E₂
    (_h : d.Hyp) :
    d.Lev ≤ normalizer (d.E₂ : Set G) ∧ d.U ≤ normalizer (d.E₂ : Set G) :=
  ⟨le_normalizer_commutator_left' _ _, le_normalizer_commutator_right' _ _⟩

theorem sec4_6_E₂
    (h : d.Hyp) :
    d.F ≤ d.E₂ ∧ d.E₂ ≤ d.U ∧ d.t ∉ d.E₂ ∧ d.E₂ ⊔ zpowers d.t = d.U ∧ d.E₂ ⊓ d.H = d.F ∧
      Nat.card d.E₂ = 2 ^ 8 ∧ (∀ a ∈ d.F, ∃ x ∈ d.E₂, x⁻¹ * d.t * x = a * d.t) ∧
      d.Lev ≤ normalizer (d.E₂ : Set G) ∧ d.U ≤ normalizer (d.E₂ : Set G) := by
  refine ⟨h.F_le_E₂, h.E₂_le_U, h.t_not_mem_E₂, h.sup_zpowers_E₂, h.E₂_inf_H, h.card_E₂,
    fun a ha => ?_, h.le_normalizer_E₂.1, h.le_normalizer_E₂.2⟩
  obtain ⟨x, hx, e⟩ := h.exists_E₂_crossed_eq ha
  exact ⟨x, hx, by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

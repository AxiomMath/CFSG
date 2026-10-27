module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Ctx

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Ω : Type*} [Group Ω]

@[expose] def i224Tw (L F : Subgroup Ω) : Subgroup Ω where
  carrier := {x | x ∈ L ∧ ∀ f ∈ F, f * x * f⁻¹ * x⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set Ω)}
  mul_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨L.mul_mem hxL hyL, fun f hf => ?_⟩
    have hz := hy f hf
    have e : f * (x * y) * f⁻¹ * (x * y)⁻¹ =
        (f * x * f⁻¹ * x⁻¹) * (x * (f * y * f⁻¹ * y⁻¹) * x⁻¹) := by group
    have h2 : x * (f * y * f⁻¹ * y⁻¹) * x⁻¹ = f * y * f⁻¹ * y⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hz.2 x hxL
      calc x * (f * y * f⁻¹ * y⁻¹) * x⁻¹ = (x * (f * y * f⁻¹ * y⁻¹)) * x⁻¹ := rfl
        _ = ((f * y * f⁻¹ * y⁻¹) * x) * x⁻¹ := by rw [this]
        _ = f * y * f⁻¹ * y⁻¹ := by group
    rw [e, h2]
    exact (L ⊓ Subgroup.centralizer (L : Set Ω)).mul_mem (hx f hf) hz
  one_mem' := ⟨L.one_mem, fun f _ => by simpa using (L ⊓ Subgroup.centralizer (L : Set Ω)).one_mem⟩
  inv_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨L.inv_mem hxL, fun f hf => ?_⟩
    have hz := hx f hf
    have e : f * x⁻¹ * f⁻¹ * x⁻¹⁻¹ = x⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * x := by group
    have h2 : x⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * x = (f * x * f⁻¹ * x⁻¹)⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1
        ((L ⊓ Subgroup.centralizer (L : Set Ω)).inv_mem hz).2 x⁻¹ (L.inv_mem hxL)
      calc x⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * x = (x⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹) * x := rfl
        _ = ((f * x * f⁻¹ * x⁻¹)⁻¹ * x⁻¹) * x := by rw [this]
        _ = (f * x * f⁻¹ * x⁻¹)⁻¹ := by group
    rw [e, h2]
    exact (L ⊓ Subgroup.centralizer (L : Set Ω)).inv_mem hz

theorem mem_i224Tw {L F : Subgroup Ω} {x : Ω} :
    x ∈ i224Tw L F ↔
      x ∈ L ∧ ∀ f ∈ F, f * x * f⁻¹ * x⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set Ω) := Iff.rfl

structure I224CtxT (p : ℕ) (B L : Subgroup Ω) : Prop where
  hp3 : p = 3
  prime : p.Prime
  elem : CFSG.Open.IsElemAbelian p B
  quasi : CFSG.Open.IsQuasisimple ↥L
  dist : ∀ g ∈ B, ∀ g' ∈ B, i224Cj g L ≠ i224Cj g' L →
    ∀ x ∈ i224Cj g L, ∀ y ∈ i224Cj g' L, x * y = y * x
  index : Nat.card B = p * Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω))
  rel : ∀ c ∈ B, c ∉ Subgroup.normalizer (L : Set Ω) →
    ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Ω), z * (c * z * c⁻¹) * (c * c * z * c⁻¹ * c⁻¹) = 1
  gen : L ≤ ⨆ (F : Subgroup Ω)
    (_ : F ≤ B ⊓ Subgroup.normalizer (L : Set Ω) ∧
      Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) ≤ p * Nat.card F), i224Tw L F

variable {p : ℕ} {B L : Subgroup Ω}

theorem i224T_card_compl [Finite Ω] (hc : I224CtxT p B L) {R : Subgroup Ω}
    (hR : Nat.card B = Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) * Nat.card R) :
    Nat.card R = p := by
  have h := hc.index
  have hpos : 0 < Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) := Nat.card_pos
  have h2 : Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) * Nat.card R =
      Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) * p := by
    rw [← hR, h, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem i224_norm_elt_tw [Finite Ω] (hc : I224CtxT p B L) {R F : Subgroup Ω} (hRB : R ≤ B)
    (hRA : B ⊓ Subgroup.normalizer (L : Set Ω) ⊓ R = ⊥)
    (hFA : F ≤ B ⊓ Subgroup.normalizer (L : Set Ω))
    (hcard : Nat.card B ≤ p * (Nat.card F * Nat.card R)) (hRp : Nat.card R = p) {y : Ω}
    (hy : y ∈ i224Tw L F) :
    ∃ n ∈ i224W p B (i224K B L),
      (∀ g₀ ∈ R, ∃ z : Ω, (∀ u ∈ i224Cj g₀ L, u * z = z * u) ∧ n = (g₀ * y * g₀⁻¹) * z) ∧
      (∀ Y : Subgroup Ω, (∀ g ∈ R, ∀ y ∈ Y, ∀ u ∈ L, y * (g * u * g⁻¹) = (g * u * g⁻¹) * y) →
        ∀ y ∈ Y, y * n = n * y) := by
  classical
  have hp3 := hc.hp3
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hc.prime⟩
  have hyL : y ∈ L := hy.1
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => i224_elem_comm hc.elem hx hy
  haveI : IsCyclic ↥R := isCyclic_of_prime_card hRp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥R)
  obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (g : Ω) := ⟨_, rfl⟩
  have hcR : c ∈ R := hcdef ▸ g.2
  have hcB : c ∈ B := hRB hcR
  have hc3 : c ^ 3 = 1 := hc.elem.2 c hcB
  have hRord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hRp]
  have hcord : orderOf c = 3 := by
    rw [hcdef, Subgroup.orderOf_coe]
    exact hRord
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hcord
    exact absurd hcord (by norm_num)
  obtain ⟨d, hd⟩ : ∃ d : Ω, d = c * c := ⟨_, rfl⟩
  have hccc : c * c * c = 1 := (pow_three' c).symm.trans hc3
  have hdc : d * c = 1 := by rw [hd]; exact hccc
  have hcd : c * d = 1 := by rw [hd, ← mul_assoc]; exact hccc
  have hdinv : d⁻¹ = c := inv_eq_of_mul_eq_one_right hdc
  have hcinv : c⁻¹ = d := inv_eq_of_mul_eq_one_right hcd
  have hdR : d ∈ R := hd ▸ R.mul_mem hcR hcR
  have hd1 : d ≠ 1 := by
    intro h
    apply hc1
    have : c = c * d := by rw [h, mul_one]
    rw [this, hcd]
  have hdc' : d ≠ c := by
    intro h
    apply hc1
    have : d * c = c * c := by rw [h]
    have h2 : c * c = 1 := by rw [← this, hdc]
    have : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hcord] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  have hRelts : ∀ r ∈ R, r = 1 ∨ r = c ∨ r = d := by
    intro r hr
    have hr' : (⟨r, hr⟩ : ↥R) ∈ Subgroup.zpowers g := hg _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hr'
    have hk' : c ^ k = r := by rw [hcdef, ← SubgroupClass.coe_zpow, hk]
    have hmod : c ^ (k % 3) = r := by
      rw [← hk']
      have := zpow_mod_orderOf c k
      rw [hcord] at this
      exact_mod_cast this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · left; rw [← hmod, h]; simp
    · right; left; rw [← hmod, h]; simp
    · right; right; rw [← hmod, h, hd]; simp [pow_two]
  have hmemcj : ∀ g (x : Ω), x ∈ L → g * x * g⁻¹ ∈ i224Cj g L := fun g x hx => by
    rw [mem_i224Cj]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hx
  have hcomm : ∀ g ∈ R, ∀ g' ∈ R, g ≠ g' → ∀ x ∈ L, ∀ y ∈ L,
      (g * x * g⁻¹) * (g' * y * g'⁻¹) = (g' * y * g'⁻¹) * (g * x * g⁻¹) := by
    intro g hg g' hg' hne x hx y hy
    have hne' : i224Cj g L ≠ i224Cj g' L := by
      intro h
      have h1 := mem_normalizer_of_i224Cj_eq h
      have h2 : g⁻¹ * g' ∈ B ⊓ Subgroup.normalizer (L : Set Ω) ⊓ R :=
        ⟨⟨B.mul_mem (B.inv_mem (hRB hg)) (hRB hg'), h1⟩, R.mul_mem (R.inv_mem hg) hg'⟩
      rw [hRA, Subgroup.mem_bot] at h2
      exact hne (inv_mul_eq_one.1 h2)
    exact hc.dist g (hRB hg) g' (hRB hg') hne' _ (hmemcj g x hx) _ (hmemcj g' y hy)
  have h1c : (1 : Ω) ∈ R := R.one_mem
  have hne1c : (1 : Ω) ≠ c := fun h => hc1 h.symm
  have hne1d : (1 : Ω) ≠ d := fun h => hd1 h.symm
  have hcm : ∀ (g g' : Ω), g ∈ R → g' ∈ R → g ≠ g' → ∀ x ∈ L, ∀ y ∈ L,
      Commute (g * x * g⁻¹) (g' * y * g'⁻¹) := fun g g' hg hg' hne x hx y hy =>
    hcomm g hg g' hg' hne x hx y hy
  have hyc1 : Commute y (c * y * c⁻¹) := by
    simpa using hcm 1 c h1c hcR hne1c y hyL y hyL
  have hyd1 : Commute y (d * y * d⁻¹) := by
    simpa using hcm 1 d h1c hdR hne1d y hyL y hyL
  have hcd1 : Commute (c * y * c⁻¹) (d * y * d⁻¹) := hcm c d hcR hdR hdc'.symm y hyL y hyL
  obtain ⟨n, hn⟩ : ∃ n : Ω, n = y * (c * y * c⁻¹) * (d * y * d⁻¹) := ⟨_, rfl⟩
  have hu₀K : y ∈ i224K B L :=
    Subgroup.mem_iSup_of_mem (1 : Ω) (Subgroup.mem_iSup_of_mem B.one_mem
      (by simpa using hmemcj 1 y hyL))
  have hu₁K : c * y * c⁻¹ ∈ i224K B L :=
    Subgroup.mem_iSup_of_mem c (Subgroup.mem_iSup_of_mem hcB (hmemcj c y hyL))
  have hu₂K : d * y * d⁻¹ ∈ i224K B L :=
    Subgroup.mem_iSup_of_mem d (Subgroup.mem_iSup_of_mem (hRB hdR) (hmemcj d y hyL))
  have hnK : n ∈ i224K B L := by
    rw [hn]
    exact (i224K B L).mul_mem ((i224K B L).mul_mem hu₀K hu₁K) hu₂K
  have hFB : F ≤ B := hFA.trans inf_le_left
  have hFR : F ⊓ R = ⊥ := by
    rw [eq_bot_iff, ← hRA]
    exact inf_le_inf_right _ hFA
  have hcFR := i224_card_sup (P := F) (Q := R)
    (fun x hx y hy => hBc x (hFB hx) y (hRB hy)) hFR
  have hnc1 : c * n * c⁻¹ = n := by
    rw [hn]
    have e1 : c * (y * (c * y * c⁻¹) * (d * y * d⁻¹)) * c⁻¹ =
        (c * y * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹) * (c * (d * y * d⁻¹) * c⁻¹) := by group
    have e2 : c * (c * y * c⁻¹) * c⁻¹ = d * y * d⁻¹ := by
      calc c * (c * y * c⁻¹) * c⁻¹ = (c * c) * y * (c * c)⁻¹ := by group
        _ = d * y * d⁻¹ := by rw [hd]
    have e3 : c * (d * y * d⁻¹) * c⁻¹ = y := by
      calc c * (d * y * d⁻¹) * c⁻¹ = (c * d) * y * (c * d)⁻¹ := by group
        _ = y := by rw [hcd]; simp
    rw [e1, e2, e3]
    calc (c * y * c⁻¹) * (d * y * d⁻¹) * y = (c * y * c⁻¹) * ((d * y * d⁻¹) * y) := by group
      _ = (c * y * c⁻¹) * (y * (d * y * d⁻¹)) := by rw [hyd1.eq.symm]
      _ = ((c * y * c⁻¹) * y) * (d * y * d⁻¹) := by group
      _ = (y * (c * y * c⁻¹)) * (d * y * d⁻¹) := by rw [hyc1.eq.symm]
  have hnc : ∀ r ∈ R, r * n * r⁻¹ = n := by
    intro r hr
    rcases hRelts r hr with h | h | h
    · rw [h]; simp
    · rw [h]; exact hnc1
    · rw [h]
      have : d * n * d⁻¹ = n := by
        rw [hdinv]
        calc d * n * c = c⁻¹ * n * c := by rw [hcinv]
          _ = c⁻¹ * (c * n * c⁻¹) * c := by rw [hnc1]
          _ = n := by group
      exact this
  have hnF : ∀ f ∈ F, f * n * f⁻¹ = n := by
    intro f hf
    have hfB := hFB hf
    have hfc : f * c = c * f := hBc f hfB c hcB
    have hfd : f * d = d * f := hBc f hfB d (hRB hdR)
    obtain ⟨hζL, hζC⟩ := hy.2 f hf
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, ζ = f * y * f⁻¹ * y⁻¹ := ⟨_, rfl⟩
    rw [← hζ] at hζL hζC
    have hζy : f * y * f⁻¹ = ζ * y := by rw [hζ]; group
    have hcA : c ∉ Subgroup.normalizer (L : Set Ω) := by
      intro h
      have : c ∈ B ⊓ Subgroup.normalizer (L : Set Ω) ⊓ R := ⟨⟨hcB, h⟩, hcR⟩
      rw [hRA, Subgroup.mem_bot] at this
      exact hc1 this
    have hrel : ζ * (c * ζ * c⁻¹) * (d * ζ * d⁻¹) = 1 := by
      have := hc.rel c hcB hcA ζ ⟨hζL, hζC⟩
      have e : c * c * ζ * c⁻¹ * c⁻¹ = d * ζ * d⁻¹ := by rw [hd]; group
      rw [e] at this
      exact this
    have hf1 : f * (c * y * c⁻¹) * f⁻¹ = (c * ζ * c⁻¹) * (c * y * c⁻¹) := by
      calc f * (c * y * c⁻¹) * f⁻¹ = (f * c) * y * (f * c)⁻¹ := by group
        _ = (c * f) * y * (c * f)⁻¹ := by rw [hfc]
        _ = c * (f * y * f⁻¹) * c⁻¹ := by group
        _ = c * (ζ * y) * c⁻¹ := by rw [hζy]
        _ = (c * ζ * c⁻¹) * (c * y * c⁻¹) := by group
    have hf2 : f * (d * y * d⁻¹) * f⁻¹ = (d * ζ * d⁻¹) * (d * y * d⁻¹) := by
      calc f * (d * y * d⁻¹) * f⁻¹ = (f * d) * y * (f * d)⁻¹ := by group
        _ = (d * f) * y * (d * f)⁻¹ := by rw [hfd]
        _ = d * (f * y * f⁻¹) * d⁻¹ := by group
        _ = d * (ζ * y) * d⁻¹ := by rw [hζy]
        _ = (d * ζ * d⁻¹) * (d * y * d⁻¹) := by group
    have hζ1 : Commute y (c * ζ * c⁻¹) := by
      simpa using hcm 1 c h1c hcR hne1c y hyL ζ hζL
    have hζ2 : Commute y (d * ζ * d⁻¹) := by
      simpa using hcm 1 d h1c hdR hne1d y hyL ζ hζL
    have hζ12 : Commute (c * y * c⁻¹) (d * ζ * d⁻¹) := hcm c d hcR hdR hdc'.symm y hyL ζ hζL
    have hconj : f * n * f⁻¹ = (ζ * y) * ((c * ζ * c⁻¹) * (c * y * c⁻¹)) *
        ((d * ζ * d⁻¹) * (d * y * d⁻¹)) := by
      rw [hn, ← hζy, ← hf1, ← hf2]
      group
    have hreorder : (ζ * y) * ((c * ζ * c⁻¹) * (c * y * c⁻¹)) * ((d * ζ * d⁻¹) * (d * y * d⁻¹)) =
        (ζ * (c * ζ * c⁻¹) * (d * ζ * d⁻¹)) * (y * (c * y * c⁻¹) * (d * y * d⁻¹)) := by
      calc (ζ * y) * ((c * ζ * c⁻¹) * (c * y * c⁻¹)) * ((d * ζ * d⁻¹) * (d * y * d⁻¹))
          = ζ * (y * (c * ζ * c⁻¹)) * (c * y * c⁻¹) * ((d * ζ * d⁻¹) * (d * y * d⁻¹)) := by group
        _ = ζ * ((c * ζ * c⁻¹) * y) * (c * y * c⁻¹) * ((d * ζ * d⁻¹) * (d * y * d⁻¹)) := by
            rw [hζ1.eq]
        _ = ζ * (c * ζ * c⁻¹) * y * ((c * y * c⁻¹) * (d * ζ * d⁻¹)) * (d * y * d⁻¹) := by group
        _ = ζ * (c * ζ * c⁻¹) * y * ((d * ζ * d⁻¹) * (c * y * c⁻¹)) * (d * y * d⁻¹) := by
            rw [hζ12.eq]
        _ = ζ * (c * ζ * c⁻¹) * (y * (d * ζ * d⁻¹)) * (c * y * c⁻¹) * (d * y * d⁻¹) := by group
        _ = ζ * (c * ζ * c⁻¹) * ((d * ζ * d⁻¹) * y) * (c * y * c⁻¹) * (d * y * d⁻¹) := by
            rw [hζ2.eq]
        _ = (ζ * (c * ζ * c⁻¹) * (d * ζ * d⁻¹)) * (y * (c * y * c⁻¹) * (d * y * d⁻¹)) := by group
    rw [hconj, hreorder, hrel, one_mul, ← hn]
  have hnC : n ∈ Subgroup.centralizer ((F ⊔ R : Subgroup Ω) : Set Ω) := by
    have hle : F ⊔ R ≤ Subgroup.centralizer ({n} : Set Ω) := by
      refine sup_le (fun f hf => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hnF f hf
        calc f * n = (f * n * f⁻¹) * f := by group
          _ = n * f := by rw [this]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hnc r hr
        calc r * n = (r * n * r⁻¹) * r := by group
          _ = n * r := by rw [this]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hnW : n ∈ i224W 3 B (i224K B L) := by
    refine Subgroup.mem_iSup_of_mem (F ⊔ R) (Subgroup.mem_iSup_of_mem ⟨sup_le hFB hRB, ?_⟩
      ⟨hnK, hnC⟩)
    rw [hcFR]
    exact hcard
  refine ⟨n, hnW, fun g₀ hg₀ => ?_, fun Y hY y' hy' => ?_⟩
  · rcases hRelts g₀ hg₀ with h | h | h <;> rw [h]
    · refine ⟨(c * y * c⁻¹) * (d * y * d⁻¹), fun u hu => ?_, ?_⟩
      · have hu' : u ∈ L := by simpa using (mem_i224Cj.1 hu)
        have h1 : Commute u (c * y * c⁻¹) := by
          simpa using hcm 1 c h1c hcR hne1c u hu' y hyL
        have h2 : Commute u (d * y * d⁻¹) := by
          simpa using hcm 1 d h1c hdR hne1d u hu' y hyL
        exact (h1.mul_right h2).eq
      · rw [hn]; group
    · refine ⟨y * (d * y * d⁻¹), fun u hu => ?_, ?_⟩
      · have hu' : c⁻¹ * u * c ∈ L := mem_i224Cj.1 hu
        have e : u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        have h1 : Commute (c * (c⁻¹ * u * c) * c⁻¹) y := by
          have := hcm c 1 hcR h1c hne1c.symm (c⁻¹ * u * c) hu' y hyL
          simpa using this
        have h2 : Commute (c * (c⁻¹ * u * c) * c⁻¹) (d * y * d⁻¹) :=
          hcm c d hcR hdR hdc'.symm _ hu' y hyL
        rw [e]
        exact (h1.mul_right h2).eq
      · rw [hn]
        calc y * (c * y * c⁻¹) * (d * y * d⁻¹) = (c * y * c⁻¹) * y * (d * y * d⁻¹) := by
              rw [hyc1.eq]
          _ = (c * y * c⁻¹) * (y * (d * y * d⁻¹)) := by group
    · refine ⟨y * (c * y * c⁻¹), fun u hu => ?_, ?_⟩
      · have hu' : d⁻¹ * u * d ∈ L := mem_i224Cj.1 hu
        have e : u = d * (d⁻¹ * u * d) * d⁻¹ := by group
        have h1 : Commute (d * (d⁻¹ * u * d) * d⁻¹) y := by
          have := hcm d 1 hdR h1c hne1d.symm (d⁻¹ * u * d) hu' y hyL
          simpa using this
        have h2 : Commute (d * (d⁻¹ * u * d) * d⁻¹) (c * y * c⁻¹) :=
          hcm d c hdR hcR hdc' _ hu' y hyL
        rw [e]
        exact (h1.mul_right h2).eq
      · rw [hn]
        have h02 : Commute (y * (c * y * c⁻¹)) (d * y * d⁻¹) := hyd1.mul_left hcd1
        exact h02.eq
  · have hyY : ∀ g ∈ R, ∀ u ∈ L, y' * (g * u * g⁻¹) = (g * u * g⁻¹) * y' := fun g hg u hu =>
      hY g hg y' hy' u hu
    rw [hn]
    have h0 := hyY 1 h1c y hyL
    have h1 := hyY c hcR y hyL
    have h2 := hyY d hdR y hyL
    simp only [inv_one, one_mul, mul_one] at h0
    exact ((Commute.mul_right (Commute.mul_right h0 h1) h2)).eq

end CFSG.HardMathSupport.Solomon.Coordinator

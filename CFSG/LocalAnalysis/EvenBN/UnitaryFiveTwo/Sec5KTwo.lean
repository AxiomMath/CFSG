module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5K
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Fusion
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckC0
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44Std
public import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Open CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs SL44
open scoped MatrixGroups

section ActsOn

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def ActsOn (φ : SL(4, F4) ≃* K) (x : G) (β : MulAut SL(4, F4)) : Prop :=
  ∀ y : SL(4, F4), x * (φ y : G) * x⁻¹ = φ (β y)

@[expose] def IsGraphOn (K : Subgroup G) (x : G) : Prop :=
  ∃ (φ : SL(4, F4) ≃* K) (C : GL (Fin 4) F4), ActsOn φ x (stdSL 4 F4 C 1 1)

@[expose] def IsFieldOn (K : Subgroup G) (x : G) : Prop :=
  ∃ (φ : SL(4, F4) ≃* K) (C : GL (Fin 4) F4), ActsOn φ x (stdSL 4 F4 C barEquiv 0)

theorem ActsOn.eq {φ : SL(4, F4) ≃* K} {x : G} {β β' : MulAut SL(4, F4)}
    (h : ActsOn φ x β) (h' : ActsOn φ x β') : β = β' :=
  MulEquiv.ext fun y => φ.injective (Subtype.ext ((h y).symm.trans (h' y)))

theorem ActsOn.mul {φ : SL(4, F4) ≃* K} {x x' : G} {β β' : MulAut SL(4, F4)}
    (h : ActsOn φ x β) (h' : ActsOn φ x' β') : ActsOn φ (x * x') (β * β') := by
  intro y
  calc x * x' * (φ y : G) * (x * x')⁻¹ = x * (x' * (φ y : G) * x'⁻¹) * x⁻¹ := by group
    _ = x * (φ (β' y) : G) * x⁻¹ := by rw [h' y]
    _ = φ (β (β' y)) := h _

theorem ActsOn.one (φ : SL(4, F4) ≃* K) : ActsOn φ (1 : G) 1 := fun y => by
  rw [one_mul, inv_one, mul_one, MulAut.one_apply]

theorem exists_actsOn_stdSL (φ : SL(4, F4) ≃* K) {x : G} (hx : x ∈ normalizer (K : Set G)) :
    ∃ (A : GL (Fin 4) F4) (σ : F4 ≃+* F4) (ε : ℕ), ε ≤ 1 ∧ ActsOn φ x (stdSL 4 F4 A σ ε) := by
  have hker : φ.toMonoidHom.ker ≤ center SL(4, F4) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective]
    exact bot_le
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_stdSL_lift (n := 4) (by norm_num) φ.toMonoidHom
    φ.surjective hker hx
  exact ⟨A, σ, ε, hε, hA⟩

theorem exists_type (φ : SL(4, F4) ≃* K) {x : G} (hx : x ∈ normalizer (K : Set G)) :
    ∃ (A : GL (Fin 4) F4) (σ : F4 ≃+* F4) (ε : ℕ), ε ≤ 1 ∧
      ActsOn φ x (stdSL 4 F4 A σ ε) ∧ HasTrType (stdSL 4 F4 A σ ε) σ ε := by
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_actsOn_stdSL φ hx
  exact ⟨A, σ, ε, hε, hA, hasTrType_stdSL A σ hε⟩

theorem mod_two_le_one (n : ℕ) : n % 2 ≤ 1 :=
  Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num))

end ActsOn

section Layer

variable {G : Type} [Group G]

theorem mem_normalizer_layer {C : Subgroup G} {g : G} (hg : g ∈ normalizer (C : Set G)) :
    g ∈ normalizer (((genFittingLayer C).map C.subtype : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (C : Set G) → ∀ {x : G},
      x ∈ (genFittingLayer C).map C.subtype →
        g * x * g⁻¹ ∈ (genFittingLayer C).map C.subtype := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    set e := C.normalizerMonoidHom ⟨g, hg⟩
    have h1 : e y ∈ genFittingLayer C := by
      have h2 := CFSG.ComponentClassification.Layer.equiv_invariant e
      change e y ∈ CFSG.ComponentClassification.Layer.subgroup C
      rw [← h2]
      exact ⟨y, hy, rfl⟩
    exact ⟨e y, h1, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key hg, fun hx => ?_⟩
  have h3 := key (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h3

theorem mem_normalizer_centralizer_of_conj {a g : G}
    (h : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) :
    g ∈ normalizer (centralizer ({a} : Set G) : Set G) := by
  have hc : ∀ x : G, Commute x a ↔ Commute (g * x * g⁻¹) a := by
    intro x
    have e : ∀ y z : G, Commute y z ↔ Commute (g * y * g⁻¹) (g * z * g⁻¹) := fun y z =>
      ⟨fun hyz => hyz.map (MulAut.conj g).toMonoidHom, fun hyz => by
        have := hyz.map (MulAut.conj g⁻¹).toMonoidHom
        simpa [MulAut.conj_apply, mul_assoc] using this⟩
    rw [e x a]
    rcases h with h | h
    · rw [h]
    · rw [h]
      exact Commute.inv_right_iff
  rw [mem_normalizer_iff]
  intro x
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact hc x

end Layer

namespace Data

variable {G : Type} [Group G] (d : Data G)

@[expose] def K : Subgroup G :=
  (genFittingLayer (centralizer ({d.e₂} : Set G))).map (centralizer ({d.e₂} : Set G)).subtype

structure KLinear : Prop where
  centralizer_eq : d.K ⊓ d.H = d.K₃
  graphField : ∃ φ : SL(4, F4) ≃* d.K, ActsOn φ d.t
    (CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4)

theorem mem_normalizer_K {g : G} (hg : g ∈ normalizer (centralizer ({d.e₂} : Set G) : Set G)) :
    g ∈ normalizer (d.K : Set G) :=
  mem_normalizer_layer hg

theorem F_le_K₃ : d.F ≤ d.K₃ :=
  d.pull_mono (sup_le (sup_le (le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans <|
    le_sup_left.trans le_sup_left) (le_sup_right.trans <| le_sup_left.trans <|
      le_sup_left.trans le_sup_left)) (le_sup_right.trans <| le_sup_left.trans le_sup_left))

end Data

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem t_mem_normalizer_K (h : d.Hyp) : d.t ∈ normalizer (d.K : Set G) := by
  refine d.mem_normalizer_K (mem_normalizer_centralizer_of_conj (Or.inl ?_))
  have he : d.e₂ * d.t = d.t * d.e₂ := mem_centralizer_iff.1 h.t_mem d.e₂ (d.ι_mem _)
  rw [← he, mul_inv_cancel_right]

theorem mem_normalizer_K_of_act_fld (h : d.Hyp) {b : G} (hb : b ∈ d.H)
    (hf : h.act ⟨b, hb⟩ = fld) : b ∈ normalizer (d.K : Set G) := by
  refine d.mem_normalizer_K (mem_normalizer_centralizer_of_conj (Or.inr ?_))
  have := h.ι_act_apply ⟨b, hb⟩ e₂SU
  rw [hf, fld_e₂SU, map_inv] at this
  exact this.symm

theorem act_t (h : d.Hyp) : h.act ⟨d.t, h.t_mem_H⟩ = 1 :=
  (h.act_eq_one_iff _).2 h.t_mem

theorem exists_act_eq_fld (h : d.Hyp) (hH : ¬ d.H ≤ d.L ⊔ zpowers d.t) :
    ∃ b : G, ∃ hb : b ∈ d.H, h.act ⟨b, hb⟩ = fld := by
  obtain ⟨x, hxH, hxL⟩ : ∃ x ∈ d.H, x ∉ d.L ⊔ zpowers d.t := by
    by_contra hc
    exact hH fun x hx => by_contra fun hn => hc ⟨x, hx, hn⟩
  have hσ : UnitaryFiveTwo.fieldFactor (h.act ⟨x, hxH⟩) ≠ 1 := by
    intro h1
    obtain ⟨l, hl, c, hc, hx⟩ := (h.fieldFactor_eq_one_iff ⟨x, hxH⟩).1 h1
    rw [h.centralizer_inf_H_eq] at hc
    have hx' : x = l * c := hx
    exact hxL (hx' ▸ mul_mem (mem_sup_left hl) (mem_sup_right hc))
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fld hσ
  have hsH : d.ι s ∈ d.H := h.L_le_H (d.ι_mem s)
  refine ⟨(d.ι s)⁻¹ * x, mul_mem (inv_mem hsH) hxH, ?_⟩
  have e : (⟨(d.ι s)⁻¹ * x, mul_mem (inv_mem hsH) hxH⟩ : d.H) =
      (⟨d.ι s, hsH⟩ : d.H)⁻¹ * ⟨x, hxH⟩ := rfl
  rw [e, map_mul, map_inv, h.act_ι, hs, inv_mul_cancel_left]

theorem mul_self_eq_one_or_eq_t (h : d.Hyp) {b : G} (hb : b ∈ d.H)
    (hf : h.act ⟨b, hb⟩ = fld) : b * b = 1 ∨ b * b = d.t := by
  have hbb : h.act ⟨b * b, mul_mem hb hb⟩ = 1 := by
    have e : (⟨b * b, mul_mem hb hb⟩ : d.H) = ⟨b, hb⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, hf]
    exact MulEquiv.ext fun g => fld_fld g
  have hC : b * b ∈ centralizer (d.L : Set G) ⊓ d.H :=
    ⟨(h.act_eq_one_iff _).1 hbb, mul_mem hb hb⟩
  rw [h.centralizer_inf_H_eq] at hC
  exact CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two h.t_two hC

theorem false_of_inner (h : d.Hyp) (hK : d.KLinear) {φ : SL(4, F4) ≃* d.K}
    (hφ : ActsOn φ d.t (CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4)) {x : G}
    (hxH : x ∈ d.H) (hf : h.act ⟨x, hxH⟩ = fld) (hxx : x * x = 1) {A : GL (Fin 4) F4}
    (hA : ActsOn φ x (stdSL 4 F4 A 1 0)) : False := by
  set σ := CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4
  have hF4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have hββ : stdSL 4 F4 A 1 0 * stdSL 4 F4 A 1 0 = 1 :=
    (hA.mul hA).eq (by rw [hxx]; exact ActsOn.one φ)
  have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 4 F4 A ^ 2 = 1 := by
    have := congrArg (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.descendAut 4 F4) hββ
    rw [map_mul, descendAut_stdSL, map_one, map_one, mul_one, pow_zero, mul_one] at this
    rw [sq, this]
  obtain ⟨g, -, hgA⟩ := exists_conj_eq_stdSL (n := 4) (by norm_num) hF4 A h2
  rw [hgA] at hA
  have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hxH
  have hcomm : σ * MulAut.conj g = MulAut.conj g * σ :=
    (hφ.mul hA).eq (by rw [← hxt]; exact hA.mul hφ)
  have hσg : σ g = g := by
    have hc : g⁻¹ * σ g ∈ center SL(4, F4) := by
      rw [mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := σ.surjective z
      have e := DFunLike.congr_fun hcomm y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at e
      calc σ y * (g⁻¹ * σ g) = g⁻¹ * (g * σ y * g⁻¹) * σ g := by group
        _ = g⁻¹ * (σ g * σ y * (σ g)⁻¹) * σ g := by rw [e]
        _ = g⁻¹ * σ g * σ y := by group
    rw [center_SL_four_eq_bot hF4, mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  set k : G := (φ g : G) with hk
  have hkt : d.t * k * d.t⁻¹ = k := by rw [hφ g, hσg]
  have hkK₃ : k ∈ d.K₃ := by
    rw [← hK.centralizer_eq]
    refine ⟨(φ g).2, mem_centralizer_singleton_iff.2 ?_⟩
    calc k * d.t = d.t * k * d.t⁻¹ * d.t := by rw [hkt]
      _ = d.t * k := by group
  have hkL : k ∈ d.L := d.pull_le_L _ hkK₃
  have hkH : k ∈ d.H := h.L_le_H hkL
  have hcK : ∀ z ∈ d.K, k⁻¹ * x * z * (k⁻¹ * x)⁻¹ = z := by
    intro z hz
    obtain ⟨y, hy⟩ := φ.surjective ⟨z, hz⟩
    have hz' : z = (φ y : G) := by rw [hy]
    subst hz'
    have e := hA y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    calc k⁻¹ * x * (φ y : G) * (k⁻¹ * x)⁻¹ = k⁻¹ * (x * (φ y : G) * x⁻¹) * k := by group
      _ = k⁻¹ * ((φ g : G) * (φ y : G) * (φ g : G)⁻¹) * k := by rw [e]
      _ = (φ y : G) := by rw [← hk]; group
  have hcH : k⁻¹ * x ∈ d.H := mul_mem (inv_mem hkH) hxH
  have hact : h.act ⟨k⁻¹ * x, hcH⟩ = MulAut.conj (d.η ⟨k, hkL⟩)⁻¹ * fld := by
    have e : (⟨k⁻¹ * x, hcH⟩ : d.H) = (⟨k, hkH⟩ : d.H)⁻¹ * ⟨x, hxH⟩ := rfl
    rw [e, map_mul, map_inv, h.act_of_mem hkL, hf, map_inv]
  obtain ⟨z, hz, hne⟩ := exists_conj_mul_fld_ne (d.η ⟨k, hkL⟩)⁻¹
  apply hne
  rw [← hact]
  apply d.ι_injective
  rw [h.ι_act_apply]
  exact hcK _ (hK.centralizer_eq ▸ (d.F_le_K₃ ⟨z, hz, rfl⟩) |>.1)

theorem exists_graph_involution (h : d.Hyp) (hK : d.KLinear)
    (hH : ¬ d.H ≤ d.L ⊔ zpowers d.t) :
    ∃ a : G, ∃ ha : a ∈ d.H, a * a = 1 ∧ h.act ⟨a, ha⟩ = fld ∧ IsGraphOn d.K a ∧
      IsFieldOn d.K (d.t * a) := by
  obtain ⟨φ, hφ⟩ := hK.graphField
  obtain ⟨b, hbH, hbf⟩ := h.exists_act_eq_fld hH
  have hbN := h.mem_normalizer_K_of_act_fld hbH hbf
  have htN := h.t_mem_normalizer_K
  have htH := h.t_mem_H
  have hbt : b * d.t = d.t * b := mem_centralizer_singleton_iff.1 hbH
  obtain ⟨A, σ, ε, hε, hA, hτ⟩ := exists_type φ hbN
  have hτt := hasTrType_sigmaSL
  have hb1 : b * b = 1 := by
    rcases h.mul_self_eq_one_or_eq_t hbH hbf with hb1 | hbt'
    · exact hb1
    · exfalso
      have e := (hA.mul hA).eq (hbt' ▸ hφ)
      have hu := (hτ.mul hτ hε hε).unique (e ▸ hτt) (mod_two_le_one _) le_rfl
      omega
  have htbH : d.t * b ∈ d.H := mul_mem htH hbH
  have htbf : h.act ⟨d.t * b, htbH⟩ = fld := by
    have e : (⟨d.t * b, htbH⟩ : d.H) = ⟨d.t, htH⟩ * ⟨b, hbH⟩ := rfl
    rw [e, map_mul, h.act_t, one_mul, hbf]
  have htb1 : d.t * b * (d.t * b) = 1 := by
    calc d.t * b * (d.t * b) = d.t * (b * d.t) * b := by group
      _ = d.t * (d.t * b) * b := by rw [hbt]
      _ = d.t * d.t * (b * b) := by group
      _ = 1 := by rw [h.t_mul_t, hb1, mul_one]
  obtain ⟨A', σ', ε', hε', hA', hτ'⟩ := exists_type φ (mul_mem htN hbN)
  have e' := (hφ.mul hA).eq hA'
  have hτtb := (hτt.mul hτ le_rfl hε).unique (e' ▸ hτ') (mod_two_le_one _) hε'
  have hb_ne : ¬ (σ = 1 ∧ ε = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h.false_of_inner hK hφ hbH hbf hb1 hA
  have htb_ne : ¬ (σ' = 1 ∧ ε' = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h.false_of_inner hK hφ htbH htbf htb1 hA'
  obtain ⟨hσσ, hεε⟩ := hτtb
  rcases ringEquiv_eq_one_or_eq_barEquiv σ with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ hb_ne
  ·
    have hσ' : σ' = barEquiv := by rw [← hσσ, mul_one]
    subst hσ'
    have hε'0 : ε' = 0 := by omega
    subst hε'0
    exact ⟨b, hbH, hb1, hbf, ⟨φ, A, hA⟩, ⟨φ, A', hA'⟩⟩
  ·
    have hσ' : σ' = 1 := by rw [← hσσ, ringEquiv_mul_self]
    subst hσ'
    have hε'1 : ε' = 1 := by omega
    subst hε'1
    refine ⟨d.t * b, htbH, htb1, htbf, ⟨φ, A', hA'⟩, ⟨φ, A, ?_⟩⟩
    rw [← mul_assoc, h.t_mul_t, one_mul]
    exact hA
  · exfalso
    have hσ' : σ' = 1 := by rw [← hσσ, ringEquiv_mul_self]
    have hε'0 : ε' = 0 := by omega
    exact htb_ne ⟨hσ', hε'0⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3TypeN
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure YCtx (P V : Subgroup G) (y : G) : Prop where
  sq : y * y = 1
  yP : ∀ q ∈ P, y * q * y⁻¹ ∈ P
  yV : ∀ v ∈ V, y * v * y⁻¹ ∈ V
  moved : ∃ v ∈ V, y * v * y⁻¹ ≠ v

theorem card_cent_V [Finite G] {V : Subgroup G} {y : G} (hy : y * y = 1) (hV4 : Nat.card V = 4)
    (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hmoved : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    Nat.card ↥(V ⊓ centralizer ({y} : Set G)) = 2 := by
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨z, hzV, hz1, hzfix⟩ := exists_fixed_ne_one hy hV2 (by rw [hV4]; norm_num) hyV
  have hzC : z ∈ V ⊓ centralizer ({y} : Set G) := by
    refine ⟨hzV, ?_⟩
    show z ∈ centralizer ({y} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hzfix]
  have hgt : 1 < Nat.card ↥(V ⊓ centralizer ({y} : Set G)) := one_lt_card_of_ne_one hzC hz1
  have hdvd : Nat.card ↥(V ⊓ centralizer ({y} : Set G)) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ centralizer ({y} : Set G) ≤ V)
    rwa [hV4] at this
  obtain ⟨v, hvV, hv⟩ := hmoved
  have hne : V ⊓ centralizer ({y} : Set G) ≠ V := by
    intro h
    apply hv
    have : v ∈ V ⊓ centralizer ({y} : Set G) := by rw [h]; exact hvV
    have h2 := mem_centralizer_iff.1 this.2 y rfl
    calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [h2]
      _ = v := by group
  have hlt : V ⊓ centralizer ({y} : Set G) < V := lt_of_le_of_ne inf_le_left hne
  have h4 := Subgroup.card_lt_of_lt hlt
  rw [hV4] at h4
  have hne3 : Nat.card ↥(V ⊓ centralizer ({y} : Set G)) ≠ 3 := by
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  omega

theorem delta_mem' [Finite G] {P V : Subgroup G} (hsq : ∀ a ∈ P, a * a ∈ V) {y : G} (hy : y * y = 1)
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) {g : G} (hg : g ∈ P) :
    y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ * (y * g * y⁻¹ * g⁻¹)⁻¹ ∈ V := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hδ : (y * g * y⁻¹ * g⁻¹)⁻¹ ∈ P :=
    P.inv_mem (P.mul_mem (hyP g hg) (P.inv_mem hg))
  have h1 : y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = g * y⁻¹ * g⁻¹ * y⁻¹ := by
    calc y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = (y * y) * g * y⁻¹ * g⁻¹ * y⁻¹ := by group
      _ = g * y⁻¹ * g⁻¹ * y⁻¹ := by rw [hy, one_mul]
  have h2 : (y * g * y⁻¹ * g⁻¹)⁻¹ = g * y * g⁻¹ * y⁻¹ := by group
  have h3 : g * y⁻¹ * g⁻¹ * y⁻¹ = g * y * g⁻¹ * y⁻¹ := by rw [hyi]
  have e : y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ * (y * g * y⁻¹ * g⁻¹)⁻¹ =
      (y * g * y⁻¹ * g⁻¹)⁻¹ * (y * g * y⁻¹ * g⁻¹)⁻¹ := by
    rw [h1, h2, h3]
  rw [e]
  exact hsq _ hδ

theorem delta_conj {y : G} (hy : y * y = 1) (g : G) :
    y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = (y * g * y⁻¹ * g⁻¹)⁻¹ := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = g * y⁻¹ * g⁻¹ * y⁻¹ := by
    calc y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = (y * y) * g * y⁻¹ * g⁻¹ * y⁻¹ := by group
      _ = g * y⁻¹ * g⁻¹ * y⁻¹ := by rw [hy, one_mul]
  have h2 : (y * g * y⁻¹ * g⁻¹)⁻¹ = g * y * g⁻¹ * y⁻¹ := by group
  have h3 : g * y⁻¹ * g⁻¹ * y⁻¹ = g * y * g⁻¹ * y⁻¹ := by rw [hyi]
  rw [h1, h2, h3]

theorem delta_inj' [Finite G] {P V : Subgroup G} (hVc : ∀ v ∈ V, ∀ a ∈ P, v * a = a * v) {y : G}
    {a a' : G} (ha : a ∈ P)
    (h : (y * a * y⁻¹ * a⁻¹)⁻¹ * (y * a' * y⁻¹ * a'⁻¹) ∈ V) :
    y * (a⁻¹ * a') * y⁻¹ * (a⁻¹ * a')⁻¹ ∈ V := by
  obtain ⟨hh, hhdef⟩ : ∃ hh, hh = a⁻¹ * a' := ⟨_, rfl⟩
  have e : (y * a * y⁻¹ * a⁻¹)⁻¹ * (y * a' * y⁻¹ * a'⁻¹) =
      a * (y * hh * y⁻¹ * hh⁻¹) * a⁻¹ := by
    have : a' = a * hh := by rw [hhdef]; group
    rw [this]; group
  rw [e] at h
  have hcen : ∀ v ∈ V, a⁻¹ * v * a⁻¹⁻¹ = v := by
    intro v hv
    have h1 := hVc v hv a⁻¹ (P.inv_mem ha)
    calc a⁻¹ * v * a⁻¹⁻¹ = (v * a⁻¹) * a⁻¹⁻¹ := by rw [h1]
      _ = v := by group
  have h2 := hcen _ h
  have e2 : a⁻¹ * (a * (y * hh * y⁻¹ * hh⁻¹) * a⁻¹) * a⁻¹⁻¹ = y * hh * y⁻¹ * hh⁻¹ := by group
  rw [e2] at h2
  rw [← hhdef, h2]
  exact h

theorem F_card_ge_aux [Finite G] {P V F : Subgroup G} (hVP : V ≤ P) (hV4 : Nat.card V = 4)
    (hP64 : Nat.card P = 64) (hVc : ∀ v ∈ V, ∀ a ∈ P, v * a = a * v)
    (hsq : ∀ a ∈ P, a * a ∈ V) {y : G} (hy : y * y = 1) (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P)
    (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hFmem : ∀ g, g ∈ F ↔ g ∈ P ∧ y * g * y⁻¹ * g⁻¹ ∈ V) : 16 ≤ Nat.card F := by
  have hFP : F ≤ P := fun g hg => ((hFmem g).1 hg).1
  have hVF : V ≤ F := fun v hv =>
    (hFmem v).2 ⟨hVP hv, V.mul_mem (hyV v hv) (V.inv_mem hv)⟩
  have hδP : ∀ g ∈ P, y * g * y⁻¹ * g⁻¹ ∈ P := fun g hg =>
    P.mul_mem (hyP g hg) (P.inv_mem hg)
  have hδF : ∀ g ∈ P, y * g * y⁻¹ * g⁻¹ ∈ F := fun g hg =>
    (hFmem _).2 ⟨hδP g hg, delta_mem' hsq hy hyP hg⟩
  let F' : Subgroup ↥P := F.subgroupOf P
  let Ψ : (↥P ⧸ F') × ↥V → ↥F := fun p =>
    ⟨(y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹) * (p.2 : G),
      F.mul_mem (hδF _ p.1.out.2) (hVF p.2.2)⟩
  have hinj : Function.Injective Ψ := by
    intro p p' hpp
    have hG0 := congrArg Subtype.val hpp
    have hG : (y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹) * (p.2 : G) =
        (y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹) * (p'.2 : G) := hG0
    have hVmem : (y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹)⁻¹ *
        (y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹) ∈ V := by
      have e : (y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹)⁻¹ *
          (y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹) = (p.2 : G) * (p'.2 : G)⁻¹ := by
        have h' : y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹ =
            (y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹) * ((p.2 : G) * (p'.2 : G)⁻¹) := by
          calc y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹
              = ((y * (p'.1.out : G) * y⁻¹ * (p'.1.out : G)⁻¹) * (p'.2 : G)) * (p'.2 : G)⁻¹ := by
                group
            _ = ((y * (p.1.out : G) * y⁻¹ * (p.1.out : G)⁻¹) * (p.2 : G)) * (p'.2 : G)⁻¹ := by
                rw [hG]
            _ = _ := by group
        rw [h']; group
      rw [e]
      exact V.mul_mem p.2.2 (V.inv_mem p'.2.2)
    have hmem := delta_inj' hVc (y := y) p.1.out.2 hVmem
    have hF'mem : (p.1.out)⁻¹ * p'.1.out ∈ F' := by
      show (((p.1.out)⁻¹ * p'.1.out : ↥P) : G) ∈ F
      exact (hFmem _).2 ⟨(((p.1.out)⁻¹ * p'.1.out : ↥P)).2, hmem⟩
    have hq : p.1 = p'.1 := by
      have := (QuotientGroup.eq (s := F')).2 hF'mem
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    have hv : (p.2 : G) = (p'.2 : G) := by
      rw [hq] at hG
      exact mul_left_cancel hG
    exact Prod.ext hq (Subtype.ext hv)
  have hle := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, hV4] at hle
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup F'
  have hF'card : Nat.card ↥F' = Nat.card ↥F := Nat.card_congr (subgroupOfEquivOfLe hFP).toEquiv
  rw [hF'card, hP64] at hcard
  by_contra hlt
  have hlt' : Nat.card ↥F ≤ 15 := by omega
  nlinarith [Nat.card_pos (α := ↥F)]

theorem F_card_le_aux [Finite G] (h9 : IG_9_16) {P V F S : Subgroup G} (hVP : V ≤ P)
    (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) {y : G} (hY : YCtx P V y)
    (hFmem : ∀ g, g ∈ F ↔ g ∈ P ∧ y * g * y⁻¹ * g⁻¹ ∈ V) (hPS : P ≤ S) (hyS : y ∈ S)
    (hyP' : y ∉ P)
    (hSZ : ∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n)
    (hSy : Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16) : Nat.card F ≤ 16 := by
  have hZ0 := card_cent_V hY.sq hV4 hY.yV hY.moved
  have hN₀ : ∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ ∈ V ⊓ centralizer ({y} : Set G) := by
    intro s hs n hn
    rw [hSZ s hs n hn]
    exact hn
  have hZ0S : V ⊓ centralizer ({y} : Set G) ≤ S := fun n hn => hPS (hVP hn.1)
  have h9' := card_cenMod_le h9 hZ0S hN₀ hyS
  rw [hZ0] at h9'
  have hFK : F ≤ cenMod S (V ⊓ centralizer ({y} : Set G)) y hN₀ := by
    intro g hg
    obtain ⟨hgP, hgV⟩ := (hFmem g).1 hg
    refine ⟨hPS hgP, hgV, ?_⟩
    show y * g * y⁻¹ * g⁻¹ ∈ centralizer ({y} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := delta_conj hY.sq g
    have h2 : (y * g * y⁻¹ * g⁻¹)⁻¹ = y * g * y⁻¹ * g⁻¹ :=
      inv_eq_of_mul_eq_one_right (hVsq _ hgV)
    rw [h2] at h1
    calc y * (y * g * y⁻¹ * g⁻¹) = (y * (y * g * y⁻¹ * g⁻¹) * y⁻¹) * y := by group
      _ = (y * g * y⁻¹ * g⁻¹) * y := by rw [h1]
  have hyK : y ∈ cenMod S (V ⊓ centralizer ({y} : Set G)) y hN₀ := by
    refine ⟨hyS, ?_⟩
    have e : y * y * y⁻¹ * y⁻¹ = 1 := by group
    rw [e]
    exact (V ⊓ centralizer ({y} : Set G)).one_mem
  have hlt : F < cenMod S (V ⊓ centralizer ({y} : Set G)) y hN₀ := by
    refine lt_of_le_of_ne hFK ?_
    intro h
    apply hyP'
    have : y ∈ F := by rw [h]; exact hyK
    exact ((hFmem y).1 this).1
  have hc := Subgroup.card_lt_of_lt hlt
  have hd := Subgroup.card_dvd_of_le hFK
  obtain ⟨m, hm⟩ := hd
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hm2 : 2 ≤ m := by
    by_contra hlm
    have : m ≤ 1 := by omega
    have := Nat.mul_le_mul_left (Nat.card F) this
    omega
  have := Nat.mul_le_mul_left (Nat.card F) hm2
  omega

namespace NabFacts

variable {P V : Subgroup G} (hF : NabFacts P) (hVP : V ≤ P) (hV4 : Nat.card V = 4)
  (hVsq : ∀ v ∈ V, v * v = 1) (hVc : ∀ v ∈ V, ∀ a ∈ P, v * a = a * v)
  {y : G} (hY : YCtx P V y)
include hF hVP hV4 hVsq hVc hY

omit hF hVP hV4 hVsq hY in
theorem hMN [Finite G] : ∀ m ∈ P, ∀ n ∈ V, m * n * m⁻¹ ∈ V := by
  intro m hm n hn
  have h1 := hVc n hn m hm
  have : m * n * m⁻¹ = n := by
    calc m * n * m⁻¹ = (n * m) * m⁻¹ := by rw [h1]
      _ = n := by group
  rw [this]; exact hn

theorem chain [Finite G] (h9 : IG_9_16) {S : Subgroup G} (hPS : P ≤ S) (hyS : y ∈ S)
    (hyP' : y ∉ P) (hSZ : ∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n)
    (hSy : Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16) :
    ∃ Pi : ℕ → Subgroup G, Pi 0 = ⊥ ∧ Pi 2 = P ∧ ∀ i < 2, FreeSec2 y (Pi i) (Pi (i + 1)) := by
  have hsq : ∀ a ∈ P, a * a ∈ V := fun a ha => hF.sq_mem_V hVP hV4 hVsq hVc ha
  have hMN' := NabFacts.hMN hVc
  have hFmem : ∀ g, g ∈ cenMod P V y hMN' ↔ g ∈ P ∧ y * g * y⁻¹ * g⁻¹ ∈ V := fun g => Iff.rfl
  have hge := F_card_ge_aux hVP hV4 hF.card hVc hsq hY.sq hY.yP hY.yV hFmem
  have hle := F_card_le_aux h9 hVP hV4 hVsq hY hFmem hPS hyS hyP' hSZ hSy
  have hFc : Nat.card (cenMod P V y hMN') = 16 := le_antisymm hle hge
  refine ⟨fun i => match i with | 0 => ⊥ | 1 => V | _ => P, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  · show FreeSec2 y ⊥ V
    refine ⟨bot_le, ?_, ?_, ?_, hY.yV, ?_⟩
    · intro a ha b hb
      have : ⁅a, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hVc a ha b (hVP hb))
      rw [this]; exact (⊥ : Subgroup G).one_mem
    · intro a ha
      rw [hVsq a ha]; exact (⊥ : Subgroup G).one_mem
    · intro g hg
      rw [Subgroup.mem_bot] at hg ⊢
      rw [hg]; group
    · have hfix : Nat.card (fixSec y ⊥ V) = Nat.card ↥(V ⊓ centralizer ({y} : Set G)) := by
        refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => ?_))
        constructor
        · rintro ⟨hgV, hg1⟩
          refine ⟨hgV, ?_⟩
          show g ∈ centralizer ({y} : Set G)
          rw [mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          have h1 : y * g * y⁻¹ * g⁻¹ = 1 := (Subgroup.mem_bot).1 hg1
          calc y * g = (y * g * y⁻¹ * g⁻¹) * g * y := by group
            _ = g * y := by rw [h1]; group
        · rintro ⟨hgV, hgC⟩
          refine ⟨hgV, ?_⟩
          have h2 := mem_centralizer_iff.1 hgC y rfl
          rw [Subgroup.mem_bot]
          calc y * g * y⁻¹ * g⁻¹ = (g * y) * y⁻¹ * g⁻¹ := by rw [h2]
            _ = 1 := by group
      rw [hfix, card_cent_V hY.sq hV4 hY.yV hY.moved, hV4, Subgroup.card_bot]
      norm_num
  · show FreeSec2 y V P
    refine ⟨hVP, ?_, hsq, hY.yV, hY.yP, ?_⟩
    · intro a ha b hb
      exact hF.comm_mem_V hVP hV4 hVc ha hb
    · have hfix : Nat.card (fixSec y V P) = Nat.card (cenMod P V y hMN') :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
      rw [hfix, hFc, hF.card, hV4]
      norm_num

end NabFacts

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

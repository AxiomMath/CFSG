module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerYHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSCentralExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerComponentC3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerRankTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Struct

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78 Wreath
open scoped commutatorElement

@[expose] def HSInnerPartA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L →
    HSInductionA8 G → HSInductionHiS G →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) = L ⊔ zpowers t →
    ∀ (S : Subgroup G) (z n : G), HSFusionData L t S z n →
    ∀ E : Subgroup G, E ≤ L → z ∈ E → IsElemAbelian 2 E → Nat.card E = 16 →
      (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) →
      (∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e) →
      (∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e) →
    ∀ W : Subgroup G, W = I2.Opp2 (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) →
      W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) →
      (∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W) →
      E ≤ W → t ∉ W → IsElemAbelian 2 W → Nat.card W = 256 →
      Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040 →
      centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E →
    Nonempty (InnerD8ConfigC L t)

@[expose] def HSInnerB4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) = L ⊔ zpowers t →
    ∀ (S : Subgroup G) (z n : G), HSFusionData L t S z n →
    ∀ c : InnerD8ConfigC L t, c.rho.range = ⊤ →
    ∃ g : G, g * g = 1 ∧ g * c.u = c.u * g ∧ g * c.u₁ = c.u₁ * g ∧
      (∀ l ∈ c.L₁, g * l = l * g) ∧
      (∀ l ∈ c.L₁, g * (t * l * t⁻¹) * g⁻¹ ∈ conjSub t c.L₁) ∧
      (∀ a ∈ c.L₁, orderOf a = 3 → g * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * g) ∧
      Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)

section General

variable {G : Type} [Group G]

theorem asm_conj_conj {t : G} (ht : t * t = 1) (g : G) : t * (t * g * t) * t⁻¹ = g := by
  calc t * (t * g * t) * t⁻¹ = (t * t) * g * (t * t⁻¹) := by group
    _ = g := by rw [ht]; group

theorem asm_oddCore_eq_bot [Finite G] (hs : IsSimpleGroup G) {t : G} (ht : orderOf t = 2) :
    CFSG.oddCore G = ⊥ := by
  rw [oddCore_eq_bot_iff]
  intro N hN hodd
  have := hN
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have h1 : Nat.card N = Nat.card G := by rw [h, Subgroup.card_top]
    rw [h1] at hodd
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem asm_centralizer_ne_top (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) {u : G}
    (hu : u ≠ 1) : centralizer ({u} : Set G) ≠ ⊤ := by
  intro h
  have hc : ∀ g : G, g * u = u * g := fun g => by
    have : g ∈ centralizer ({u} : Set G) := h ▸ Subgroup.mem_top g
    exact mem_centralizer_singleton_iff.1 this
  have hu' : u ∈ center G := mem_center_iff.2 hc
  rcases hs.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
  · rw [h1, mem_bot] at hu'
    exact hu hu'
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have : b ∈ center G := h1 ▸ Subgroup.mem_top b
    exact (mem_center_iff.1 this a)

end General

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem asm_rho_base_one (c : InnerD8Config L t) (q : ↥c.P)
    (hq : (q : G) ∈ normalizer (c.L₁ : Set G)) (hc : ∀ k ∈ c.L₁, Commute (q : G) k) :
    c.rho q = base 1 (MulAut.congr c.eL₁ (conjAutOf c.L₁ (c.pair.tpt_mem_normalizer hq))) := by
  rw [InnerD8Config.rho_apply, c.pair.rho_of_normalizes q hq, mapEquiv_base,
    (conjAutOf_eq_one_iff c.L₁ hq).2 hc, map_one]

theorem asm_congr_mem_innR (c : InnerD8Config L t) (A : MulAut ↥c.L₁) :
    MulAut.congr c.eL₁ A ∈ innR ↔ ∃ l : ↥c.L₁, A = MulAut.conj l := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨c.eL₁.symm a, ?_⟩
    apply (MulAut.congr c.eL₁).injective
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact ha.symm
  · rintro ⟨l, rfl⟩
    exact ⟨c.eL₁ l, by rw [congr_conj]⟩

theorem asm_fix_iff (c : InnerD8Config L t) {w : G} (hn : w ∈ normalizer (c.L₁ : Set G))
    (y : ↥c.L₁) :
    MulAut.congr c.eL₁ (conjAutOf c.L₁ hn) (c.eL₁ y) = c.eL₁ y ↔ w * (y : G) * w⁻¹ = y := by
  show c.eL₁ (conjAutOf c.L₁ hn (c.eL₁.symm (c.eL₁ y))) = c.eL₁ y ↔ _
  rw [MulEquiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff, conjAutOf_apply]

theorem asm_sq (c : InnerD8Config L t) {w : G} (hn : w ∈ normalizer (c.L₁ : Set G))
    (hw : w * w = 1) :
    MulAut.congr c.eL₁ (conjAutOf c.L₁ hn) * MulAut.congr c.eL₁ (conjAutOf c.L₁ hn) = 1 := by
  rw [← map_mul, ← conjAutOf_mul c.L₁ hn hn, conjAutOf_congr c.L₁ hw (mul_mem hn hn) (one_mem _),
    conjAutOf_one, map_one]

theorem asm_conj_conj' {t : G} (ht : t * t = 1) (g : G) : t * (t * g * t⁻¹) * t = g := by
  calc t * (t * g * t⁻¹) * t = (t * t) * g * (t⁻¹ * t) := by group
    _ = g := by rw [ht]; group

theorem asm_not_inner (c : InnerD8Config L t) {g : G} (hgP : g ∈ c.P)
    (hgn : g ∈ normalizer (c.L₁ : Set G))
    (hgH : Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)) :
    MulAut.congr c.eL₁
      (conjAutOf c.L₁ (c.pair.tpt_mem_normalizer (p := ⟨g, hgP⟩) hgn)) ∉ innR := by
  intro hin
  obtain ⟨e⟩ := hgH
  have ht : t * t = 1 := c.pair.t_sq
  obtain ⟨l0, hl0⟩ := (asm_congr_mem_innR c _).1 hin
  have hl0' : ∀ y : ↥c.L₁, (t * g * t) * (y : G) * (t * g * t)⁻¹ = (l0 : G) * y * (l0 : G)⁻¹ := by
    intro y
    have := congrArg (fun f : MulAut ↥c.L₁ => ((f y : ↥c.L₁) : G)) hl0
    simpa [conjAutOf_apply, MulAut.conj_apply] using this
  have key : ∀ y ∈ c.L₁, g * (t * y * t⁻¹) * g⁻¹ =
      (t * l0 * t⁻¹) * (t * y * t⁻¹) * (t * l0 * t⁻¹)⁻¹ := by
    intro y hy
    have h1 : (t * g * t) * y * (t * g * t)⁻¹ = (l0 : G) * y * (l0 : G)⁻¹ := hl0' ⟨y, hy⟩
    have hg' : t * (t * g * t) * t⁻¹ = g := asm_conj_conj ht g
    calc g * (t * y * t⁻¹) * g⁻¹
        = (t * (t * g * t) * t⁻¹) * (t * y * t⁻¹) * (t * (t * g * t) * t⁻¹)⁻¹ := by rw [hg']
      _ = t * ((t * g * t) * y * (t * g * t)⁻¹) * t⁻¹ := by group
      _ = t * ((l0 : G) * y * (l0 : G)⁻¹) * t⁻¹ := by rw [h1]
      _ = _ := by group
  have hl'' : t * (l0 : G) * t⁻¹ ∈ conjSub t c.L₁ := ⟨(l0 : G), l0.2, rfl⟩
  have hcomm : g * (t * (l0 : G) * t⁻¹) = (t * (l0 : G) * t⁻¹) * g := by
    have h := key l0 l0.2
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [h]
    group
  have hzb : ∀ b ∈ conjSub t c.L₁, ((t * (l0 : G) * t⁻¹)⁻¹ * g) * b =
      b * ((t * (l0 : G) * t⁻¹)⁻¹ * g) := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.1 hb
    have h := key y hy
    rw [mul_inv_eq_iff_eq_mul] at h
    calc (t * (l0 : G) * t⁻¹)⁻¹ * g * (t * y * t⁻¹)
        = (t * (l0 : G) * t⁻¹)⁻¹ * (g * (t * y * t⁻¹)) := by group
      _ = (t * (l0 : G) * t⁻¹)⁻¹ * ((t * l0 * t⁻¹) * (t * y * t⁻¹) * (t * l0 * t⁻¹)⁻¹ * g) := by
        rw [h]
      _ = (t * y * t⁻¹) * ((t * (l0 : G) * t⁻¹)⁻¹ * g) := by group
  have hzg : ((t * (l0 : G) * t⁻¹)⁻¹ * g) * g = g * ((t * (l0 : G) * t⁻¹)⁻¹ * g) := by
    have h : g * (t * (l0 : G) * t⁻¹)⁻¹ = (t * (l0 : G) * t⁻¹)⁻¹ * g :=
      (Commute.inv_right (show Commute g (t * (l0 : G) * t⁻¹) from hcomm)).eq
    calc (t * (l0 : G) * t⁻¹)⁻¹ * g * g = (t * (l0 : G) * t⁻¹)⁻¹ * (g * g) := by group
      _ = g * (t * (l0 : G) * t⁻¹)⁻¹ * g := by rw [h]; group
      _ = _ := by group
  set H : Subgroup G := conjSub t c.L₁ ⊔ zpowers g with hH
  have hHz : H ≤ centralizer ({(t * (l0 : G) * t⁻¹)⁻¹ * g} : Set G) := by
    refine sup_le (fun b hb => mem_centralizer_singleton_iff.2 (hzb b hb).symm) ?_
    exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hzg.symm)
  have hzH : (t * (l0 : G) * t⁻¹)⁻¹ * g ∈ H :=
    mul_mem (inv_mem (mem_sup_left hl'')) (mem_sup_right (mem_zpowers g))
  have hez : e ⟨_, hzH⟩ = 1 := by
    apply pgl29_center_trivial
    intro q
    obtain ⟨h, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hHz h.2))
  have h1 : (⟨_, hzH⟩ : ↥H) = 1 := e.injective (hez.trans (map_one e).symm)
  have h2 : (t * (l0 : G) * t⁻¹)⁻¹ * g = 1 := congrArg Subtype.val h1
  have h3 : t * (l0 : G) * t⁻¹ = g := inv_mul_eq_one.1 h2
  have hle : H ≤ conjSub t c.L₁ :=
    sup_le le_rfl (zpowers_le.2 (h3 ▸ hl''))
  have hc1 := Subgroup.card_le_of_le hle
  have hc2 : Nat.card H = 720 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.QuasithinUnique.Out21.A6.card_pgl29
  have hc3 : Nat.card (conjSub t c.L₁) = 360 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact card_L₁ c
  omega

theorem asm_psiCrit (c : InnerD8ConfigC L t) (hρ : c.rho.range = ⊤)
    (hF1 : ∀ {α β : MulAut (alternatingGroup (Fin 6))}, α * α = 1 → β * β = 1 → α ∉ innR →
      β ∉ innR → (∃ a, orderOf a = 3 ∧ α a = a) → (∀ a, orderOf a = 3 → β a ≠ a) →
      α * β ∉ innR)
    {g : G} (hgg : g * g = 1) (hgu : g * c.u = c.u * g) (hgu₁ : g * c.u₁ = c.u₁ * g)
    (hgL : ∀ l ∈ c.L₁, g * l = l * g)
    (hg3 : ∀ a ∈ c.L₁, orderOf a = 3 → g * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * g)
    (hgH : Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)) :
    c.PsiCrit := by
  have ht : t * t = 1 := c.pair.t_sq
  have hkP : c.k ∈ c.P := c.mem_P_iff.2 c.k_comm_u
  let jP : ↥c.P := ⟨t * c.k * t⁻¹, mul_mem (mul_mem c.t_mem_P hkP) (inv_mem c.t_mem_P)⟩
  have hjc : ∀ l ∈ c.L₁, Commute (jP : G) l := by
    intro l hl
    show Commute (t * c.k * t⁻¹) l
    rw [commute_conj_iff]
    have := c.k_comm_L₁t l hl
    rw [c.pair.t_inv]
    rw [c.pair.t_inv] at this
    exact this
  have hjn : (jP : G) ∈ normalizer (c.L₁ : Set G) := mem_normalizer_of_forall_commute c.L₁ hjc
  have ejk : t * (jP : G) * t = c.k := asm_conj_conj' ht c.k
  have hjs : c.rho jP = base 1 (MulAut.congr c.eL₁ (conjAutOf c.L₁ c.k_norm)) := by
    rw [asm_rho_base_one c.toInnerD8Config jP hjn hjc, conjAutOf_congr c.L₁ ejk _ c.k_norm]
  have hs : MulAut.congr c.eL₁ (conjAutOf c.L₁ c.k_norm) ∉ innR := by
    intro h
    obtain ⟨l, hl⟩ := (asm_congr_mem_innR c.toInnerD8Config _).1 h
    exact c.k_outer l hl
  have hs2 : MulAut.congr c.eL₁ (conjAutOf c.L₁ c.k_norm) *
      MulAut.congr c.eL₁ (conjAutOf c.L₁ c.k_norm) = 1 :=
    asm_sq c.toInnerD8Config c.k_norm (sq_eq_one_of_orderOf_eq_two c.k_ord)
  have hsfix : ∃ a, orderOf a = 3 ∧
      MulAut.congr c.eL₁ (conjAutOf c.L₁ c.k_norm) a = a := by
    refine ⟨c.eL₁ ⟨c.x, c.x_mem⟩, c.orderOf_eL₁_x, ?_⟩
    refine (asm_fix_iff c.toInnerD8Config c.k_norm ⟨c.x, c.x_mem⟩).2 ?_
    exact mul_inv_eq_iff_eq_mul.2 (c.K₁_comm_x c.k c.k_mem)
  have hgP : g ∈ c.P := c.mem_P_iff.2 hgu
  let gP : ↥c.P := ⟨g, hgP⟩
  have hgc : ∀ l ∈ c.L₁, Commute (gP : G) l := fun l hl => hgL l hl
  have hgn : (gP : G) ∈ normalizer (c.L₁ : Set G) := mem_normalizer_of_forall_commute c.L₁ hgc
  have hgρ := asm_rho_base_one c.toInnerD8Config gP hgn hgc
  have hw : t * g * t ∈ normalizer (c.L₁ : Set G) := c.pair.tpt_mem_normalizer hgn
  have hp : MulAut.congr c.eL₁ (conjAutOf c.L₁ hw) ∉ innR := asm_not_inner c.toInnerD8Config hgP hgn hgH
  have hp2 : MulAut.congr c.eL₁ (conjAutOf c.L₁ hw) * MulAut.congr c.eL₁ (conjAutOf c.L₁ hw) = 1 := by
    refine asm_sq c.toInnerD8Config hw ?_
    calc t * g * t * (t * g * t) = t * (g * (t * t) * g) * t := by group
      _ = 1 := by rw [ht, mul_one, hgg, mul_one, ht]
  have hpmove : ∀ a, orderOf a = 3 → MulAut.congr c.eL₁ (conjAutOf c.L₁ hw) a ≠ a := by
    intro a ha heq
    obtain ⟨y, rfl⟩ := c.eL₁.surjective a
    have ho : orderOf (y : G) = 3 := by
      rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq c.eL₁]
      exact ha
    have h1 := (asm_fix_iff c.toInnerD8Config hw y).1 heq
    apply hg3 y y.2 ho
    have hg' : t * (t * g * t) * t⁻¹ = g := asm_conj_conj ht g
    have h2 : g * (t * (y : G) * t⁻¹) * g⁻¹ = t * (y : G) * t⁻¹ := by
      calc g * (t * (y : G) * t⁻¹) * g⁻¹
          = (t * (t * g * t) * t⁻¹) * (t * (y : G) * t⁻¹) * (t * (t * g * t) * t⁻¹)⁻¹ := by
            rw [hg']
        _ = t * ((t * g * t) * (y : G) * (t * g * t)⁻¹) * t⁻¹ := by group
        _ = t * (y : G) * t⁻¹ := by rw [h1]
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hsp := hF1 hs2 hp2 hs hp hsfix hpmove
  intro q
  exact c.toInnerD8Config.commute_u₁_iff hρ jP gP (c.u₁_comm_K₁t c.k c.k_mem).symm hgu₁ hjs hgρ
    hs hp hsp q

end Config

section Main

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem asm_core (hset : HSLemma21Setting G L) (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t)
    {S : Subgroup G} {z n : G} (hf : HSFusionData L t S z n) (c : InnerD8ConfigC L t)
    (hB4 : c.rho.range = ⊤ → ∃ g : G, g * g = 1 ∧ g * c.u = c.u * g ∧ g * c.u₁ = c.u₁ * g ∧
      (∀ l ∈ c.L₁, g * l = l * g) ∧
      (∀ l ∈ c.L₁, g * (t * l * t⁻¹) * g⁻¹ ∈ conjSub t c.L₁) ∧
      (∀ a ∈ c.L₁, orderOf a = 3 → g * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * g) ∧
      Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29))
    (hON : ONan77S5) (hIn : ONanInspection) (h15 : FS79Lemma15Sec G) (hKG : KGHS3)
    (hF1 : ∀ {α β : MulAut (alternatingGroup (Fin 6))}, α * α = 1 → β * β = 1 → α ∉ innR →
      β ∉ innR → (∃ a, orderOf a = 3 ∧ α a = a) → (∀ a, orderOf a = 3 → β a ≠ a) →
      α * β ∉ innR) :
    ∃ (x : G) (M : Subgroup G), orderOf x = 2 ∧ IsCompIn M (centralizer ({x} : Set G)) ∧
      IsSporadic ↥M .HS ∧ 2 ≤ Open.pRank 2 (centralizer (M : Set G)) ∧
      (Nat.card G).factorization 3 ≤ 4 := by
  have hL : IsSporadic ↥L .HS := hset.2.1
  have hρ : c.rho.range = ⊤ := c.toInnerD8Config.rho_surjective hL htL ht2 hin hf
  have h3 : (Nat.card G).factorization 3 = 4 :=
    c.toInnerD8Config.factorization_three_eq_four hL htL ht2 hin hf
  obtain ⟨g, hgg, hgu, hgu₁, hgL, -, hg3, hgH⟩ := hB4 hρ
  have hψ : c.PsiCrit := asm_psiCrit c hρ hF1 hgg hgu hgu₁ hgL hg3 hgH
  have hY : IsSporadic c.Yq .HS :=
    c.isSporadic_Yq hρ hψ (c.isKGroupCat_Yq hset.1) hON hIn g hgg hgu hgu₁ hgL hgH
  have hXJ : c.X3 ≤ c.Jc := (c.Zc_le_Jc).trans' le_sup_left
  have hu₁Zc : c.u₁ ∈ c.Zc := mem_sup_right (mem_zpowers _)
  have hcenJ : ∀ w ∈ c.Zc, ∀ h ∈ c.Jc, w * h = h * w := fun w hw h hh =>
    mem_centralizer_iff.1 hh w hw
  have : ((c.X3 ⊔ zpowers c.u₁).subgroupOf c.Jc).Normal := c.instNormalZcSubgroupOf
  have h2B : 2880 * 18 ∣ Nat.card ↥(c.Jc ⊓ centralizer ({c.u} : Set G)) := by
    have h51 : Nat.card ↥(c.Jc ⊓ centralizer ({c.u} : Set G)) = 51840 := by
      rw [inf_comm]
      exact c.toInnerD8Config.card_centralizer_X_sup_u₁ hρ hψ
        (fun α h => mem_inner_of_fix_centralizer c.orderOf_eL₁_x α h)
    rw [h51]
  obtain ⟨hMHS, hMZ⟩ := isSporadic_commutator_of_quotient_hs c.Jc c.X3 c.u₁ c.u hXJ
    (c.Zc_le_Jc hu₁Zc) c.u_mem_Jc (fun w hw h hh => hcenJ w (mem_sup_left hw) h hh)
    (fun h hh => (hcenJ c.u₁ hu₁Zc h hh)) c.X_card c.u₁_ord c.u₁_not_mem_X3 c.u_ord
    c.u_not_mem_Zc hY h2B
  have hZcard : Nat.card c.Zc = 18 := c.card_Zc
  have hJcard : Nat.card c.Jc = 44352000 * 18 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (c.Zc.subgroupOf c.Jc)
    rw [Nat.card_congr (subgroupOfEquivOfLe c.Zc_le_Jc).toEquiv, hZcard,
      card_eq_of_isSporadic_hs hY] at h1
    exact h1
  have hMcard : Nat.card (⁅c.Jc, c.Jc⁆ : Subgroup G) = 44352000 := card_eq_of_isSporadic_hs hMHS
  have hsup : Nat.card ↥(⁅c.Jc, c.Jc⁆ ⊔ c.Zc) = 44352000 * 18 := by
    rw [card_sup_of_cm (commutator_le_self' c.Jc) hMZ, hMcard, hZcard]
  have hMZJ : ⁅c.Jc, c.Jc⁆ ⊔ c.Zc = c.Jc :=
    Subgroup.eq_of_le_of_card_ge (sup_le (commutator_le_self' c.Jc) c.Zc_le_Jc)
      (by rw [hsup, hJcard])
  have hu : c.u ∈ ⁅c.Jc, c.Jc⁆ ⊔ c.Zc := by
    rw [hMZJ]
    exact c.u_mem_Jc
  have hC4 := c.toInnerD8Config.two_le_pRank_centralizer hρ hψ hMHS hMZ hu
  have hO : CFSG.oddCore G = ⊥ := asm_oddCore_eq_bot hset.1.simple ht2
  have hU : centralizer ({c.u₁} : Set G) ≠ ⊤ :=
    asm_centralizer_ne_top hset.1.simple hset.1.nonabelian c.u₁_ne_one
  have hAn : ∀ h ∈ centralizer ({c.u} : Set G) ⊓ centralizer ({c.u₁} : Set G),
      h ∈ normalizer ((conjSub t c.L₁ : Subgroup G) : Set G) := by
    rintro h ⟨hP, hC⟩
    have hhn : h ∈ normalizer (c.L₁ : Set G) := by
      rw [mem_normalizer_iff_map_eq]
      refine (c.pair.rho_mem_baseSubgroup_iff ⟨h, hP⟩).1 ?_
      have hb := (hψ ⟨h, hP⟩).1 (mem_centralizer_singleton_iff.1 hC)
      rw [mem_baseSubgroup_iff] at hb ⊢
      rw [← swapChar_mapEquiv (MulAut.congr c.eL₁), ← c.rho_apply]
      exact hb
    rw [mem_normalizer_iff_map_eq]
    exact c.pair.map_conj_conj_of_normalizes hP hhn
  have hAF : conjSub t c.L₁ ≤ centralizer ({c.u} : Set G) ⊓ centralizer ({c.u₁} : Set G) :=
    le_inf c.conjSub_le_centralizer_u fun b hb =>
      mem_centralizer_singleton_iff.2 (c.u₁_comm_L₁t hb)
  have hA : Nonempty (↥(conjSub t c.L₁) ≃* alternatingGroup (Fin 6)) :=
    ⟨(Subgroup.equivMapOfInjective c.L₁ (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm.trans c.eL₁⟩
  have hMJ : (⁅c.Jc, c.Jc⁆ : Subgroup G) ≤
      centralizer (c.X3 : Set G) ⊓ centralizer ({c.u₁} : Set G) := by
    rw [← centralizer_sup_zpowers]
    exact commutator_le_self' c.Jc
  have hC3 : IsCompIn (⁅c.Jc, c.Jc⁆ : Subgroup G) (centralizer ({c.u₁} : Set G)) :=
    isCompIn_of_balance h15 hO hKG hset.1.kProper h3.le c.u c.u₁ c.u_ord c.u₁_ord
      c.u₁_mul_u.symm c.u_ne_u₁ hU (conjSub t c.L₁) hA hAF hAn c.X3 c.X_card
      (fun a ha => c.X_cube ha) (fun a ha b hb => (c.comm_L₁_conj ha.1 hb).eq)
      (fun a ha => c.mem_P_iff.1 (c.pair.K_le ha.1)) (fun a ha => c.u₁_comm_L₁ ha.1)
      ⁅c.Jc, c.Jc⁆ hMHS hMJ
      (fun H hH hperf => by
        have hHJ : H ≤ c.Jc := by
          have := hH
          rw [← centralizer_sup_zpowers] at this
          exact this
        rw [← hperf]
        exact Subgroup.commutator_mono hHJ hHJ)
      c.conjSub_le_commutator
  exact ⟨c.u₁, ⁅c.Jc, c.Jc⁆, c.u₁_ord, hC3, hMHS, hC4, h3.le⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus

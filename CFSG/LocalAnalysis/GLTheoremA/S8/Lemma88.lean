module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

namespace L89

@[expose] def CfgIAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (x : G) (L : Subgroup G) (row : Row) (c : SporCfg G p x L row), orderOf x = p →
    GLAPComponent p (cx x) L → RowL row p L →
    GLAPComponent p (L ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D) ∧
      ∃ E : Subgroup G, E ≤ cfgI p L c.D ∧ IsElemAbelian p E ∧
        p ^ (row.rank - 1) * Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) ≤ Nat.card E

@[expose] def I301BAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (a y : G) (J Bs I K R0 : Subgroup G) (row : Row),
    orderOf a = p → CFSG.Open.IsKGroup ↥(cx a) → Odd (Nat.card (GLAPPrimeCoreOf p (cx a))) →
    GLAPComponent p (cx a) J → p = row.prime → catalogIs (PSimple p J) (sporIs row.name) →
    GLAIsBmax p Bs → Bs ≤ cx a → Nat.card Bs = p ^ row.rank → (∃ b ∈ Bs, b ≠ 1 ∧ CentMod p J b) →
    y ∈ Bs → GLAPComponent p (J ⊓ cx y) I → RowI row p I →
    R0 ≤ cx y → (IsExtraSpec2 R0 ∨ Nat.card R0 = 2) →
    (row = .ly ∨ LayerModCore p K (GLAPLayer p (cx a ⊓ cx y ⊓ Subgroup.centralizer (centerOf R0 : Set G)))) →
    K ⊔ Bs ≤ Subgroup.normalizer (R0 : Set G) → RowK row p K → Nat.card R0 = 2 ^ row.r0exp →
    ∀ R1 : Subgroup G, R1 ≤ cx a → IsPGroup 2 R1 → K ⊔ Bs ≤ Subgroup.normalizer (R1 : Set G) →
      R0 < R1 → IsExtraSpec2 R1

structure Inputs88 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  cfgI : CfgIAt G p
  i301B : I301BAt G p

section Elementary

variable {G : Type} [Group G]

theorem le_normalizer_inf' {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) : A ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 (hH hg) h,
    Subgroup.mem_normalizer_iff.1 (hK hg) h]

theorem le_normalizer_sup' {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) : A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  rw [Subgroup.map_sup]
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH hg)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK hg)
  unfold GLBConj at h1 h2
  rw [h1, h2]

theorem le_normalizer_commutator' {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  rw [Subgroup.map_commutator]
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH hg)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK hg)
  unfold GLBConj at h1 h2
  rw [h1, h2]

theorem le_normalizer_of_le_centralizer {A H : Subgroup G}
    (h : A ≤ Subgroup.centralizer (H : Set G)) : A ≤ Subgroup.normalizer (H : Set G) :=
  h.trans (Subgroup.centralizer_le_normalizer _)

theorem glaPLayer_le [Finite G] (p : ℕ) (H : Subgroup G) : GLAPLayer p H ≤ H :=
  sSup_le fun _ hJ => hJ.1

theorem isElemAbelian_sup {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) : IsElemAbelian p (A ⊔ B) := by
  have hcomm : ∀ x ∈ (A : Set G) ∪ B, ∀ y ∈ (A : Set G) ∪ B, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact isElemAbelian_commute hA hx hy
    · exact (Subgroup.mem_centralizer_iff.1 (hAB hx) y hy).symm
    · exact Subgroup.mem_centralizer_iff.1 (hAB hy) x hx
    · exact isElemAbelian_commute hB hx hy
  have hsup : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hc : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx y hy
    rw [hsup] at hx hy
    letI := Subgroup.closureCommGroupOfComm (k := (A : Set G) ∪ B) fun x hx y hy _ => hcomm x hx y hy
    have := mul_comm (⟨x, hx⟩ : Subgroup.closure ((A : Set G) ∪ B)) ⟨y, hy⟩
    exact congrArg Subtype.val this
  refine ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have hx' := hx
  rw [hsup] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA.2 y hy
    · exact hB.2 y hy
  | one => exact one_pow p
  | mul y z hy hz ihy ihz =>
    have hy' : y ∈ A ⊔ B := by rw [hsup]; exact hy
    have hz' : z ∈ A ⊔ B := by rw [hsup]; exact hz
    have hyz : Commute y z := hc y hy' z hz'
    rw [hyz.mul_pow, ihy hy', ihz hz', one_mul]
  | inv y hy ihy =>
    have hy' : y ∈ A ⊔ B := by rw [hsup]; exact hy
    rw [inv_pow, ihy hy', inv_one]

theorem mem_centerOf_iff {H : Subgroup G} {g : G} :
    g ∈ centerOf H ↔ g ∈ H ∧ ∀ h ∈ H, h * g = g * h := by
  unfold centerOf
  constructor
  · rintro ⟨⟨g', hg'⟩, hz, rfl⟩
    refine ⟨hg', fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_center_iff.2 fun h => Subtype.ext (hc h h.2), rfl⟩

theorem centerOf_eq_inf (H : Subgroup G) : centerOf H = H ⊓ Subgroup.centralizer (H : Set G) := by
  ext g
  simp only [mem_centerOf_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop}
    (e : Nonempty (S ≃* S')) (h : catalogIs S' Q) : catalogIs S Q := by
  obtain ⟨e⟩ := e
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem nonempty_mulEquiv_of_catalogIs_spor {S S' : Type} [Group S] [Group S']
    {s : TauCeti.SporadicName} (h : catalogIs S (sporIs s)) (h' : catalogIs S' (sporIs s)) :
    Nonempty (S ≃* S') := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  obtain ⟨i', hi', ⟨e'⟩⟩ := h'
  unfold sporIs at hi hi'
  subst hi hi'
  exact ⟨e.trans e'.symm⟩

theorem centMod_of_le_cx [Finite G] {p : ℕ} {J : Subgroup G} {a : G} (hJ : J ≤ cx a) :
    CentMod p J a := by
  have haJ : a ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJ hj)
  refine ⟨Subgroup.centralizer_le_normalizer _ haJ, ?_⟩
  have h : ⁅J, Subgroup.zpowers a⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, S3.centralizer_zpowers]
    exact hJ
  rw [h]
  exact bot_le

end Elementary

section Cfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem cfg_D_le_Bs (c : SporCfg G p x L row) : c.D ≤ c.Bs := c.hD.1

theorem cfg_Bs_le_centralizer_D (c : SporCfg G p x L row) :
    c.Bs ≤ Subgroup.centralizer (c.D : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact isElemAbelian_commute c.hBs.1 (c.hD.1 hd) hb

theorem cfg_Bs_le_cx_of_mem (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.Bs) : c.Bs ≤ cx a :=
  isElemAbelian_le_centralizer c.hBs.1 ha

theorem centralizer_le_cx_of_mem {D : Subgroup G} {a : G} (ha : a ∈ D) :
    Subgroup.centralizer (D : Set G) ≤ cx a :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha)

theorem cfg_I_le (c : SporCfg G p x L row) :
    cfgI p L c.D ≤ L ⊓ Subgroup.centralizer (c.D : Set G) := glaPLayer_le p _

theorem cfg_I_le_centralizer (c : SporCfg G p x L row) :
    cfgI p L c.D ≤ Subgroup.centralizer (c.D : Set G) := (cfg_I_le c).trans inf_le_right

theorem cfg_K_le (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ≤ cfgI p L c.D ⊓ cfgN x c.R := glaPLayer_le p _

theorem cfg_K_le_centralizer (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ≤ Subgroup.centralizer (c.D : Set G) :=
  (cfg_K_le c).trans (inf_le_left.trans (cfg_I_le_centralizer c))

theorem cfg_KB_le_N (c : SporCfg G p x L row) : cfgK p x L c.D c.R ⊔ c.Bs ≤ cfgN x c.R :=
  sup_le ((cfg_K_le c).trans inf_le_right) c.hBsN

theorem cfg_KB_le_centralizer_D (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.centralizer (c.D : Set G) :=
  sup_le (cfg_K_le_centralizer c) (cfg_Bs_le_centralizer_D c)

theorem cfg_KB_le_normalizer_R (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (c.R : Set G) :=
  (cfg_KB_le_N c).trans inf_le_right

theorem cfg_KB_le_cx (c : SporCfg G p x L row) : cfgK p x L c.D c.R ⊔ c.Bs ≤ cx x :=
  (cfg_KB_le_N c).trans inf_le_left

theorem cfg_R0_le_centralizer (c : SporCfg G p x L row) :
    cfgR0 c.R c.D ≤ Subgroup.centralizer (c.D : Set G) := inf_le_right

theorem cfg_KB_le_normalizer_R0 (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (cfgR0 c.R c.D : Set G) :=
  le_normalizer_inf' (cfg_KB_le_normalizer_R c)
    ((cfg_KB_le_centralizer_D c).trans Subgroup.le_normalizer)

theorem cfg_D_le_centralizer_D (c : SporCfg G p x L row) :
    c.D ≤ Subgroup.centralizer (c.D : Set G) :=
  (cfg_D_le_Bs c).trans (cfg_Bs_le_centralizer_D c)

end Cfg

section TwoGen

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem exists_not_mem_zpowers (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {a : G} (ha : a ∈ D) : ∃ y ∈ D, y ∉ Subgroup.zpowers a := by
  by_contra h
  push Not at h
  have hle : D ≤ Subgroup.zpowers a := fun y hy => h y hy
  have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h3 : orderOf a ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hD.2 a ha))
  have h4 : p < p ^ 2 := by
    rw [sq]
    exact lt_mul_self hp.one_lt
  have : p ^ 2 ≤ p := by rw [← hcard]; exact h1.trans h3
  exact absurd this (not_le.2 h4)

theorem le_sup_zpowers (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {a y : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hy : y ∈ D)
    (hya : y ∉ Subgroup.zpowers a) : D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers y := by
  have : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := fun h => hya (h ▸ Subgroup.one_mem _)
  have hoa : orderOf a = p := orderOf_eq_prime (hD.2 a ha) ha1
  have hoy : orderOf y = p := orderOf_eq_prime (hD.2 y hy) hy1
  have hAD : Subgroup.zpowers a ≤ D := (Subgroup.zpowers_le).2 ha
  have hYD : Subgroup.zpowers y ≤ D := (Subgroup.zpowers_le).2 hy
  have hYA : Subgroup.zpowers y ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    apply le_normalizer_of_le_centralizer
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact isElemAbelian_commute hD (hAD hh) (hYD hg)
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers y : Subgroup G) ∣ p := by
      rw [← hoy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
        (by rw [h, Nat.card_zpowers, hoy])
      have hmem : y ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers y := by
        rw [heq]; exact Subgroup.mem_zpowers y
      exact hya hmem.1
  have hsup : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hYA
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hoy] at h
    rw [h, sq]
  have heq := Subgroup.eq_of_le_of_card_ge (sup_le hAD hYD) (by rw [hsup, hcard])
  rw [heq]

theorem centralizer_eq_inf (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {a y : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hy : y ∈ D)
    (hya : y ∉ Subgroup.zpowers a) : Subgroup.centralizer (D : Set G) = cx a ⊓ cx y := by
  apply le_antisymm (le_inf (centralizer_le_cx_of_mem ha) (centralizer_le_cx_of_mem hy))
  have hDle := le_sup_zpowers hp hD hcard ha ha1 hy hya
  intro g hg
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ cx g := by
    apply sup_le
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hg.1).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hDle hd))

theorem zpowers_le_normalizer_of_le_cx {H : Subgroup G} {a : G} (hH : H ≤ cx a) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.zpowers_le]
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hH hh)

theorem coprime_card_of_two (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G} (hV : IsPGroup 2 V) :
    Nat.Coprime p (Nat.card V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem two_dvd_card_of_two {V : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    2 ∣ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hV1 (Subgroup.eq_bot_of_card_eq V hk)
  rw [hk]
  exact dvd_pow_self 2 hk0

end TwoGen

section Lemma88

variable {G : Type} [Group G] [Finite G] {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem rank_ID (hp : p.Prime) (c : SporCfg G p x L row) (hrank : 1 ≤ row.rank)
    (hE : ∃ E : Subgroup G, E ≤ cfgI p L c.D ∧ IsElemAbelian p E ∧
      p ^ (row.rank - 1) * Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) ≤ Nat.card E) :
    ∃ E : Subgroup G, E ≤ cfgI p L c.D ⊔ c.D ∧ IsElemAbelian p E ∧ Nat.card c.Bs < Nat.card E := by
  obtain ⟨E, hEI, hE, hbig⟩ := hE
  have hED : E ≤ Subgroup.centralizer (c.D : Set G) := hEI.trans (cfg_I_le_centralizer c)
  refine ⟨E ⊔ c.D, sup_le_sup_right hEI _, isElemAbelian_sup hE c.hD.2.1 hED, ?_⟩
  have hDE : c.D ≤ Subgroup.normalizer (E : Set G) := by
    apply le_normalizer_of_le_centralizer
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.1 (hED he) d hd).symm
  have h1 := card_sup_mul_card_inf_of_le_normalizer hDE
  have h2 : E ⊓ c.D ≤ E ⊓ centerOf (cfgI p L c.D) := by
    intro e he
    refine ⟨he.1, mem_centerOf_iff.2 ⟨hEI he.1, fun i hi => ?_⟩⟩
    exact (Subgroup.mem_centralizer_iff.1 (cfg_I_le_centralizer c hi) e he.2).symm
  have h3 : Nat.card (E ⊓ c.D : Subgroup G) ≤ Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) :=
    Subgroup.card_le_of_le h2
  rw [c.hD.2.2.1] at h1
  rw [c.hBsCard]
  have hpos : 0 < Nat.card (E ⊓ c.D : Subgroup G) := Nat.card_pos
  have hpow : p ^ (row.rank + 1) = p ^ (row.rank - 1) * p ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have key : p ^ (row.rank + 1) * Nat.card (E ⊓ c.D : Subgroup G) ≤
      Nat.card (E ⊔ c.D : Subgroup G) * Nat.card (E ⊓ c.D : Subgroup G) := by
    rw [h1, hpow]
    calc p ^ (row.rank - 1) * p ^ 2 * Nat.card (E ⊓ c.D : Subgroup G)
        = p ^ (row.rank - 1) * Nat.card (E ⊓ c.D : Subgroup G) * p ^ 2 := by ring
      _ ≤ p ^ (row.rank - 1) * Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) * p ^ 2 := by
          gcongr
      _ ≤ Nat.card E * p ^ 2 := by gcongr
  have h4 := Nat.le_of_mul_le_mul_right key hpos
  calc p ^ row.rank < p ^ (row.rank + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    _ ≤ _ := h4

theorem four_le_rank (row : Row) : 4 ≤ row.rank := by
  cases row <;> decide

theorem rank_ID' (hc : S8Ctx G p) (hcfg : CfgIAt G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) :
    ∃ E : Subgroup G, E ≤ cfgI p L c.D ⊔ c.D ∧ IsElemAbelian p E ∧ Nat.card c.Bs < Nat.card E :=
  rank_ID hc.ctx.prime c (le_trans (by norm_num) (four_le_rank row)) (hcfg x L row c hx hL hrow).2

theorem odd_core_a (hc : S8Ctx G p) (hcfg : CfgIAt G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {a : G}
    (ha : a ∈ c.D) : Odd (Nat.card (GLAPPrimeCoreOf p (cx a))) := by
  obtain ⟨E, hEID, hE, hbig⟩ := rank_ID' hc hcfg hx hL hrow c
  have hID : cfgI p L c.D ⊔ c.D ≤ cx a :=
    sup_le ((cfg_I_le_centralizer c).trans (centralizer_le_cx_of_mem ha))
      ((cfg_D_le_centralizer_D c).trans (centralizer_le_cx_of_mem ha))
  exact odd_core_of_big_rank hc.ctx.prime c.hBs (hEID.trans hID) hE hbig

theorem lemma88iii (hc : S8Ctx G p) (h301 : I301BAt G p) (hcfg : CfgIAt G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {a : G}
    (ha : a ∈ c.D) (ha1 : a ≠ 1) {J : Subgroup G} (hJ : GLAPComponent p (cx a) J)
    (hJL : Nonempty (PSimple p J ≃* PSimple p L))
    (hIJ : GLAPComponent p (J ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D))
    {R1 : Subgroup G} (hR1a : R1 ≤ cx a) (hR12 : IsPGroup 2 R1)
    (hR1n : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (R1 : Set G))
    (hR01 : cfgR0 c.R c.D < R1) : IsExtraSpec2 R1 := by
  have hp := hc.ctx.prime
  obtain ⟨hD1, hD2, hD3, hD4⟩ := c.hD
  obtain ⟨hpr, hBsc, hRI, hRK, hR0c⟩ := c.hData
  obtain ⟨y, hyD, hya⟩ := exists_not_mem_zpowers hp hD2 hD3 ha
  have hcen := centralizer_eq_inf hp hD2 hD3 ha ha1 hyD hya
  have : Fact p.Prime := ⟨hp⟩
  have hoa : orderOf a = p := orderOf_eq_prime (hD2.2 a ha) ha1
  have hJy : J ⊓ cx y = J ⊓ Subgroup.centralizer (c.D : Set G) := by
    rw [hcen, ← inf_assoc, inf_eq_left.2 hJ.1]
  refine h301 hp hc.ctx.odd a y J c.Bs (cfgI p L c.D) (cfgK p x L c.D c.R) (cfgR0 c.R c.D) row hoa
    (isKGroup_cx hc.ctx ha1) (odd_core_a hc hcfg hx hL hrow c ha) hJ hpr
    (catalogIs_of_mulEquiv hJL hrow.2.1) c.hBs (cfg_Bs_le_cx_of_mem c (hD1 ha)) hBsc
    ⟨a, hD1 ha, ha1, centMod_of_le_cx hJ.1⟩ (hD1 hyD) (hJy ▸ hIJ) hRI
    ((cfg_R0_le_centralizer c).trans (centralizer_le_cx_of_mem hyD)) c.hR0 ?_
    (cfg_KB_le_normalizer_R0 c) hRK hR0c R1 hR1a hR12 hR1n hR01
  rcases c.hK6 with h | h
  · exact Or.inl h
  · right
    rwa [hcen] at h

end Lemma88

end L89

end S8

end CFSG.LocalAnalysis.GLTheoremA

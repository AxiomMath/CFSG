module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AXV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionThmD
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9
public import CFSG.ClassicalInvolution.Q3.TL4Conn264O
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF
public import CFSG.ClassicalInvolution.Q3.TL3T39
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusE6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Y
public import CFSG.ClassicalInvolution.Q3.TL4Conn264D
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace AAE7

open CFSG.ClassicalInvolution.Q3.TC.Thin

section Gen

variable {G : Type} [Group G] [Finite G]

theorem comm_of_mk_comm {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    (hN : Odd (Nat.card N)) {k l : G} {a : ℕ} (hl : l ^ 2 ^ a = 1)
    (h : QuotientGroup.mk' N k * QuotientGroup.mk' N l =
      QuotientGroup.mk' N l * QuotientGroup.mk' N k) : k * l = l * k := by
  set c := l * k * l⁻¹ * k⁻¹ with hc
  have hcN : c ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    show QuotientGroup.mk' N c = 1
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
    group
  have hcen : ∀ j : ℕ, ∀ g : G, g * c ^ j = c ^ j * g := fun j g =>
    Subgroup.mem_center_iff.mp (hNc (N.pow_mem hcN j)) g
  have h1 : l * k * l⁻¹ = c * k := by rw [hc]; group
  have hpow : ∀ j : ℕ, l ^ j * k * (l ^ j)⁻¹ = c ^ j * k := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc l ^ (j + 1) * k * (l ^ (j + 1))⁻¹ = l * (l ^ j * k * (l ^ j)⁻¹) * l⁻¹ := by
            rw [pow_succ']
            group
        _ = l * c ^ j * (k * l⁻¹) := by rw [ih]; group
        _ = c ^ j * (l * k * l⁻¹) := by rw [hcen j l]; group
        _ = c ^ (j + 1) * k := by rw [h1, pow_succ]; group
  have hc2 : c ^ 2 ^ a = 1 := by
    have := hpow (2 ^ a)
    rw [hl, one_mul, inv_one, mul_one] at this
    exact mul_right_cancel (this.symm.trans (one_mul k).symm)
  have hodd : orderOf c ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨c, hcN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hco : Nat.Coprime (2 ^ a) (Nat.card N) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hN)
  have hc1 : c = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_of_pow_eq_one hc2) hodd)
  have h2 : l * k * l⁻¹ = k := by rw [h1, hc1, one_mul]
  calc k * l = l * k * l⁻¹ * l := by rw [h2]
    _ = l * k := by group

theorem eq_of_map_eq_central {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    (hN : Odd (Nat.card N)) {J J' : Subgroup G} (hJ : IsPGroup 2 J) (hJ' : IsPGroup 2 J')
    (h : J.map (QuotientGroup.mk' N) = J'.map (QuotientGroup.mk' N)) : J = J' := by
  have key : ∀ {A B : Subgroup G}, IsPGroup 2 A → IsPGroup 2 B →
      A.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) → A ≤ B := by
    intro A B hA hB hle x hx
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_map_of_mem _ hx)
    have hm : x⁻¹ * y ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      show QuotientGroup.mk' N (x⁻¹ * y) = 1
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hxy : x * y = y * x := by
      have h1 := Subgroup.mem_center_iff.mp (hNc hm) x
      have h2 : y = x⁻¹ * y * x := by rw [← h1]; group
      calc x * y = x * (x⁻¹ * y * x) := by rw [← h2]
        _ = y * x := by group
    have := OddQuot.eq_of_commute_of_mem hN (OddQuot.two_elt hA hx) (OddQuot.two_elt hB hy) hxy hm
    exact this ▸ hy
  exact le_antisymm (key hJ hJ' h.le) (key hJ' hJ h.ge)

end Gen

section Odd

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_of_mem_oddCoreOf {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ L ∈ Ω, IsPGroup 2 L) {X V : Subgroup Y} (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hV2 : IsPGroup 2 V) {P : Set (Subgroup Y)} (hPΩ : P ⊆ Ω) (hPX : ∀ L ∈ P, L ≤ X)
    (hinv : ∀ L ∈ P, ∀ x ∈ X, conjSub x L ∈ P)
    (hzV : ∀ L ∈ P, ∀ z : Y, IsUniqueInvolution L z → z ∈ V) (hgen : X ≤ pSpan P) :
    ∀ r ∈ oddCoreOf X, ∀ y ∈ X, r * y = y * r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := oddCoreOf X with hR
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [hR, oddCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hRn : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    rintro x hx _ ⟨r', hr', rfl⟩
    exact ⟨⟨x, hx⟩ * r' * ⟨x, hx⟩⁻¹,
      (classicalInvolutionOddCore_normal ↥X).conj_mem r' hr' ⟨x, hx⟩, rfl⟩
  have hR2 : ∀ c ∈ R, (∃ k : ℕ, c ^ 2 ^ k = 1) → c = 1 := by
    intro c hc ⟨k, hk⟩
    have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2' : orderOf c ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥R)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : Nat.Coprime (2 ^ k) (Nat.card R) := Nat.Coprime.pow_left k
      ((Nat.coprime_two_left).mpr hRodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2')
  have hcent : ∀ L ∈ P, ∀ r ∈ R, ∀ l ∈ L, r * l = l * r := by
    intro L hL r hr
    have hLΩ := hPΩ hL
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 L hLΩ
    have hzX : z ∈ X := hPX L hL hz.mem
    have hRz : ∀ s ∈ R, s * z = z * s := by
      intro s hs
      have hzV' := hzV L hL z hz
      set c := s * z * s⁻¹ * z⁻¹ with hc
      have hcR : c ∈ R := by
        have h1 : z * s⁻¹ * z⁻¹ ∈ R := hRn z hzX _ (R.inv_mem hs)
        have : c = s * (z * s⁻¹ * z⁻¹) := by rw [hc]; group
        rw [this]
        exact R.mul_mem hs h1
      have hcV : c ∈ V := V.mul_mem (hVn s (hRX hs) z hzV') (V.inv_mem hzV')
      obtain ⟨k, hk⟩ := hV2 ⟨c, hcV⟩
      have hc1 : c = 1 := hR2 c hcR ⟨k, by
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this⟩
      calc s * z = s * z * s⁻¹ * z⁻¹ * z * s := by group
        _ = z * s := by rw [← hc, hc1, one_mul]
    set O : Set (Subgroup Y) := {M | ∃ s ∈ R, conjSub s L = M} with hO
    have hOP : ∀ M ∈ O, M ∈ P := by
      rintro M ⟨s, hs, rfl⟩
      exact hinv L hL s (hRX hs)
    have hOz : ∀ M ∈ O, IsUniqueInvolution M z := by
      rintro M ⟨s, hs, rfl⟩
      have := hz.conj s
      have e : s * z * s⁻¹ = z := by rw [hRz s hs, mul_inv_cancel_right]
      rwa [e] at this
    have hT2 : IsPGroup 2 (pSpan O) := isPGroup_pSpan_of_comm
      (fun M hM => h2 M (hPΩ (hOP M hM)))
      fun M hM M' hM' hne => twin_comm hΩ h2 (hPΩ (hOP M hM)) (hPΩ (hOP M' hM')) hne
        (hOz M hM) (hOz M' hM')
    have hOR : ∀ s ∈ R, ∀ M ∈ O, conjSub s M ∈ O := by
      rintro s hs _ ⟨s', hs', rfl⟩
      exact ⟨s * s', R.mul_mem hs hs', by rw [conjSub_mul]⟩
    have hRT : ∀ s ∈ R, ∀ w ∈ pSpan O, s * w * s⁻¹ ∈ pSpan O := by
      intro s hs w hw
      have hR' : ∀ M ∈ O, conjSub s⁻¹ M ∈ O := fun M hM => hOR s⁻¹ (R.inv_mem hs) M hM
      exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_pSpan (hOR s hs) hR') w).mp hw
    have hLO : L ∈ O := ⟨1, R.one_mem, conjSub_one L⟩
    intro l hl
    have hlT : l ∈ pSpan O := le_pSpan hLO hl
    have hlX : l ∈ X := hPX L hL hl
    set c := r * l * r⁻¹ * l⁻¹ with hc
    have hcR : c ∈ R := by
      have h1 : l * r⁻¹ * l⁻¹ ∈ R := hRn l hlX _ (R.inv_mem hr)
      have : c = r * (l * r⁻¹ * l⁻¹) := by rw [hc]; group
      rw [this]
      exact R.mul_mem hr h1
    have hcT : c ∈ pSpan O := (pSpan O).mul_mem (hRT r hr l hlT) ((pSpan O).inv_mem hlT)
    obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
    have hc1 : c = 1 := hR2 c hcR ⟨k, by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this⟩
    calc r * l = r * l * r⁻¹ * l⁻¹ * l * r := by group
      _ = l * r := by rw [← hc, hc1, one_mul]
  intro r hr y hy
  have hle : pSpan P ≤ Subgroup.centralizer ({r} : Set Y) := pSpan_le fun L hL x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent L hL r hr x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen hy))).symm

end Odd

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem nonempty_aeIdent_of_restrict {Ω : Set (Subgroup Y)} {X : Subgroup Y}
    (hspan : pSpan {J | J ∈ Ω ∧ J ≤ X} = X) {m : ℕ} (I : AEIdent (restrictFamily Ω X) m) :
    Nonempty (AEIdent {J | J ∈ Ω ∧ J ≤ X} m) := by
  set P : Set (Subgroup Y) := {J | J ∈ Ω ∧ J ≤ X} with hP
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  suffices h : ∀ X' : Subgroup Y, pSpan P = X' → AEIdent (restrictFamily Ω X') m →
      Nonempty (AEIdent P m) from h X hspan I
  intro X' hX' I'
  subst hX'
  have hfam : restrictFamily Ω (pSpan P) = restrictFamily P (pSpan P) := by
    ext L'
    constructor
    · rintro ⟨L, hL, hLX', rfl⟩
      exact ⟨L, ⟨hL, hLX'.trans hspan.le⟩, hLX', rfl⟩
    · rintro ⟨L, hL, hLX', rfl⟩
      exact ⟨L, hL.1, hLX', rfl⟩
  have hmap : (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype = pSpan P := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun L hL => ?_)
    have h1 : L.subgroupOf (pSpan P) ≤ pSpan (restrictFamily P (pSpan P)) :=
      le_pSpan ⟨L, hL, hLX L hL, rfl⟩
    calc L = (L.subgroupOf (pSpan P)).map (pSpan P).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hLX L hL)).symm
      _ ≤ (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype := Subgroup.map_mono h1
  have hgen : pSpan (restrictFamily P (pSpan P)) = ⊤ := by
    apply Subgroup.map_injective (pSpan P).subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact ⟨AEIdent.ofRestrict hgen hLX (AEIdent.ofEq hfam I')⟩

theorem rLayer_le_centralizer' (Ω : Set (Subgroup Y)) (c : Y) :
    rLayer Ω c ≤ Subgroup.centralizer ({c} : Set Y) :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem E_le_X (R : Subgroup Y) (e b : Y) : rLayer (Om R) e ≤ p23XE R e b := le_sup_left

theorem Eb_le_X (R : Subgroup Y) (e b : Y) :
    conjSub b (rLayer (Om R) e) ≤ p23XE R e b := le_sup_right

end Lift

section Theta

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {e : Y}

theorem coreAt_eq_self' {c : Y} {J : Subgroup Y} (hc : J ≤ Subgroup.centralizer ({c} : Set Y))
    (h2 : IsPGroup 2 J) : TwinADescent.coreAt c J = J := by
  refine le_antisymm (TwinADescent.coreAt_le_left c J) ?_
  unfold TwinADescent.coreAt
  rw [inf_eq_left.mpr hc]
  exact le_tightCore_of_isPGroup le_rfl h2

@[expose] noncomputable def hullInc (R : Subgroup Y) (e : Y) : ↥(coreHull (Om R) e) →* Y :=
  (Subgroup.centralizer ({e} : Set Y)).subtype.comp (coreHull (Om R) e).subtype

theorem hullInc_injective (R : Subgroup Y) (e : Y) : Function.Injective (hullInc R e) :=
  (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)

theorem hullInc_mem (hΩ : HypOmegaGen (Om R)) (hc2 : IsPGroup 2 (Subgroup.zpowers e)) (b : Y)
    (h : ↥(coreHull (Om R) e)) : hullInc R e h ∈ p23XE R e b :=
  E_le_X R e b (TwinDisc.coreHull_map_le_rLayer hΩ hc2 ⟨_, h.2, rfl⟩)

@[expose] noncomputable def theta (hΩ : HypOmegaGen (Om R)) (hc2 : IsPGroup 2 (Subgroup.zpowers e))
    (b : Y) : ↥(coreHull (Om R) e) →* SecQuot (p23XE R e b) :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b))).comp
    ((hullInc R e).codRestrict (p23XE R e b) (hullInc_mem hΩ hc2 b))

end Theta

section Label

variable {G : Type} [Group G] {P : Set (Subgroup G)} {k : ℕ}

open Classical in
@[expose] noncomputable def labelOf (I : AEIdent P k) (L : Subgroup G) : Finset (Fin k) × Bool :=
  if h : ∃ p : Finset (Fin k) × Bool, ∃ hp : p.1.card = 4,
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar p.1 hp p.2 then Classical.choose h
  else (∅, true)

theorem labelOf_spec (I : AEIdent P k) {L : Subgroup G} (hL : L ∈ P) :
    ∃ hp : (labelOf I L).1.card = 4,
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar (labelOf I L).1 hp (labelOf I L).2 := by
  have hex : ∃ p : Finset (Fin k) × Bool, ∃ hp : p.1.card = 4,
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar p.1 hp p.2 := by
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨(α, b), h, hlab⟩
  rw [labelOf, dif_pos hex]
  exact Classical.choose_spec hex

theorem eq_of_memBar_eq_pair (hk : 5 ≤ k) {p q : Finset (Fin k) × Bool} (hp : p.1.card = 4)
    (hq : q.1.card = 4) (he : AE.memBar p.1 hp p.2 = AE.memBar q.1 hq q.2) : p = q := by
  obtain ⟨α, b⟩ := p
  obtain ⟨β, c⟩ := q
  dsimp only at hp hq he ⊢
  have h1 : α = β := AE.eq_of_memBar_eq' hk he
  subst h1
  cases b <;> cases c
  · rfl
  · exact absurd he.symm (AE.memBar_true_ne_false hk α hp)
  · exact absurd he (AE.memBar_true_ne_false hk α hp)
  · rfl

theorem memBar_congr {p q : Finset (Fin k) × Bool} (h : p = q) (hp : p.1.card = 4)
    (hq : q.1.card = 4) : AE.memBar p.1 hp p.2 = AE.memBar q.1 hq q.2 := by
  subst h
  rfl

theorem labelOf_eq (I : AEIdent P k) (hk : 5 ≤ k) {L : Subgroup G} (hL : L ∈ P)
    {α : Finset (Fin k)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) : labelOf I L = (α, b) := by
  obtain ⟨hp, hspec⟩ := labelOf_spec I hL
  exact eq_of_memBar_eq_pair (q := (α, b)) hk hp h (hspec.symm.trans hlab)

theorem map_eq_of_labelOf_eq (I : AEIdent P k) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (h : labelOf I L = labelOf I L') :
    (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ := by
  obtain ⟨hp, hspec⟩ := labelOf_spec I hL
  obtain ⟨hp', hspec'⟩ := labelOf_spec I hL'
  rw [hspec, hspec']
  exact memBar_congr h hp hp'

theorem ncard_labels (k : ℕ) :
    {p : Finset (Fin k) × Bool | p.1.card = 4}.ncard = k.choose 4 * 2 := by
  have h : {p : Finset (Fin k) × Bool | p.1.card = 4} =
      ↑((Finset.univ.powersetCard 4 : Finset (Finset (Fin k))) ×ˢ (Finset.univ : Finset Bool)) := by
    ext p
    simp [Finset.mem_powersetCard]
  rw [h, Set.ncard_coe_finset, Finset.card_product, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, Finset.card_univ, Fintype.card_bool]

end Label

section Triv

variable {Y : Type} [Group Y] [Finite Y]

theorem le_centralizer_of_mem_trivialOnQuot {J : Subgroup Y} {c : Y} (hJ2 : IsPGroup 2 J)
    (hc : c ∈ Balance.Bootstrap.trivialOnQuot J) : J ≤ Subgroup.centralizer ({c} : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := ((Balance.Bootstrap.mem_trivialOnQuot_iff).mp hc).2 x hx
  have hJ' := Balance.oddCoreIn_le J h1
  obtain ⟨a, ha⟩ := hJ2 ⟨_, hJ'⟩
  have hodd := orderOf_dvd_natCard (⟨_, h1⟩ : Balance.oddCoreIn J)
  rw [Subgroup.orderOf_mk] at hodd
  have ha' := congrArg Subtype.val ha
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at ha'
  have h2 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Balance.odd_card_oddCoreIn J)))
    (orderOf_dvd_of_pow_eq_one ha') hodd)
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

end Triv

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g b : Y} {V : Subgroup Y}

theorem K_le_Ce_of (hc : P23Cfg n Y R S t K' W u e g) (htwo : ∀ J ∈ Om R, IsPGroup 2 J) :
    tightCore R ≤ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨R₁, -, -, -, hR₁, -, hRD, -⟩ := e_decomp hc
  have heq : tightCore R = R₁ :=
    hR₁.2.2 (tightCore R) le_rfl (htwo _ (CoreAssembly.mem_conjClass_self _)) hR₁.1
  rw [heq]
  exact hRD.2.trans (normalizer_le_centralizer_e hc.data)

theorem exists_conj_of_le_Ce_of (hc : P23Cfg n Y R S t K' W u e g)
    (htwo : ∀ J ∈ Om R, IsPGroup 2 J) (hA6 : SecAE R e 6) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∃ x ∈ rLayer (Om R) e, conjSub x (tightCore R) = J := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hS := p23_q8Section hc.std.perp hc.data.he2
  obtain ⟨I₆⟩ := hA6
  have htr := TwinDisc.AE5.trans_of_aeIdent (by norm_num : 5 ≤ 6) hS I₆
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    mem_tqMembers3_of_le_centralizer (CoreAssembly.mem_conjClass_self _) (K_le_Ce_of hc htwo)
  have hJtq : J ∈ tqMembers3 (Om R) e := mem_tqMembers3_of_le_centralizer hJ hJc
  obtain ⟨gb, hgb⟩ :=
    htr _ (TwinDisc.secImg_mem_secFam hKtq) _ (TwinDisc.secImg_mem_secFam hJtq)
  obtain ⟨x, hx⟩ := TwinPerpV3.A6d.exists_conj_hull_of_secImg hΩ hc2 hKtq hJtq ⟨gb, hgb⟩
  exact ⟨((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y),
    TwinDisc.coreHull_map_le_rLayer hΩ hc2 ⟨_, x.2, rfl⟩, hx.symm⟩

theorem eb_of_meet (hc : P23Cfg n Y R S t K' W u e g) (htwo : ∀ J ∈ Om R, IsPGroup 2 J)
    (hA6 : SecAE R e 6)
    (hmeet : ∃ J ∈ Om R, J ≤ rLayer (Om R) e ∧ J ≤ conjSub b (rLayer (Om R) e)) :
    ∀ J ∈ Om R, J ≤ conjSub b (rLayer (Om R) e) →
      ∃ x ∈ p23XE R e b, conjSub x (tightCore R) = J := by
  intro J hJ hJE
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  obtain ⟨J₀, hJ₀, hJ₀E, hJ₀Eb⟩ := hmeet
  have hCe := rLayer_le_centralizer' (Om R) e
  obtain ⟨g₀, hg₀, hg₀J⟩ := exists_conj_of_le_Ce_of hc htwo hA6 hJ₀ (hJ₀E.trans hCe)
  have hb : ∀ {M : Subgroup Y}, M ≤ conjSub b (rLayer (Om R) e) →
      conjSub b⁻¹ M ≤ rLayer (Om R) e := by
    intro M hM
    have := conjSub_mono (n := b⁻¹) hM
    rwa [conjSub_inv_conjSub] at this
  obtain ⟨g₁, hg₁, hg₁J⟩ := exists_conj_of_le_Ce_of hc htwo hA6 (hΩ.conjInvariant b⁻¹ J₀ hJ₀)
    ((hb hJ₀Eb).trans hCe)
  obtain ⟨g₂, hg₂, hg₂J⟩ := exists_conj_of_le_Ce_of hc htwo hA6 (hΩ.conjInvariant b⁻¹ J hJ)
    ((hb hJE).trans hCe)
  refine ⟨(b * (g₂ * g₁⁻¹) * b⁻¹) * g₀, ?_, ?_⟩
  · refine (p23XE R e b).mul_mem (Eb_le_X R e b (conj_mem_conjSub ?_)) (E_le_X R e b hg₀)
    exact (rLayer (Om R) e).mul_mem hg₂ ((rLayer (Om R) e).inv_mem hg₁)
  · calc conjSub (b * (g₂ * g₁⁻¹) * b⁻¹ * g₀) (tightCore R)
        = conjSub (b * g₂) (conjSub g₁⁻¹ (conjSub b⁻¹ (conjSub g₀ (tightCore R)))) := by
          simp only [← conjSub_mul]
          congr 1
          group
      _ = J := by
          rw [hg₀J, ← hg₁J, conjSub_inv_conjSub, conjSub_mul, hg₂J, conjSub_conjSub_inv]

structure Hyp (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g b : Y) (V : Subgroup Y) : Prop where
  cfg : P23Cfg n Y R S t K' W u e g
  two : ∀ J ∈ Om R, IsPGroup 2 J
  ae6 : SecAE R e 6
  norm : ∀ x ∈ p23XE R e b, ∀ v ∈ V, x * v * x⁻¹ ∈ V
  v2 : IsPGroup 2 V
  tV : t ∈ V
  ne : conjSub b (rLayer (Om R) e) ≠ rLayer (Om R) e
  eb : ∀ J ∈ Om R, J ≤ conjSub b (rLayer (Om R) e) →
    ∃ x ∈ p23XE R e b, conjSub x (tightCore R) = J

namespace Hyp

variable (H : Hyp n Y R S t K' W u e g b V)
include H

theorem hypOmega : HypOmegaGen (Om R) := (CoreData.of_S H.cfg.std.perp.core).hyp

omit H in
theorem mem_K : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _

theorem isUniqueInvolution_t : IsUniqueInvolution (tightCore R) t :=
  Inner.isUniqueInvolution_core (CoreData.of_S H.cfg.std.perp.core).datum

theorem isPGroup_zpowers_e : IsPGroup 2 (Subgroup.zpowers e) :=
  ExactLayer.isPGroup_zpowers_of_sq_eq_one H.cfg.data.he2

theorem le_normalizer : p23XE R e b ≤ Subgroup.normalizer (V : Set Y) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => H.norm x hx v hv, fun hv => ?_⟩
  have := H.norm x⁻¹ ((p23XE R e b).inv_mem hx) _ hv
  simpa [mul_assoc] using this

theorem v_ne_bot : V ≠ ⊥ := by
  intro h
  have := H.tV
  rw [h, Subgroup.mem_bot] at this
  exact H.isUniqueInvolution_t.ne_one this

theorem card_lt : Nat.card (p23XE R e b) < n := by
  have hC := H.cfg.std.perp.core
  haveI := hC.simple
  have hne := ne_top_of_le_normalizer hC.nonab H.v_ne_bot H.v2 H.le_normalizer
  rw [← hC.card]
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
    hne ((Subgroup.card_eq_iff_eq_top _).mp heq)

theorem q8_of_mem {J : Subgroup Y} (hJ : J ∈ Om R) : Nonempty (↥J ≃* QuaternionGroup 2) :=
  members_sylow_q8 H.cfg.std.perp J hJ J
    ⟨le_rfl, H.two J hJ, fun _ hV' _ hle => le_antisymm hV' hle⟩

theorem card_of_mem {J : Subgroup Y} (hJ : J ∈ Om R) : Nat.card J = 8 := by
  obtain ⟨e8⟩ := H.q8_of_mem hJ
  rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem K_le_Ce : tightCore R ≤ Subgroup.centralizer ({e} : Set Y) :=
  K_le_Ce_of H.cfg H.two

theorem K'_le_Ce : K' ≤ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨-, R₁', -, -, -, hR₁', -, hR'D, -⟩ := e_decomp H.cfg
  have heq : K' = R₁' := hR₁'.2.2 K' le_rfl (H.two _ H.cfg.std.hK'.1) hR₁'.1
  rw [heq]
  exact hR'D.2.trans (normalizer_le_centralizer_e H.cfg.data)

theorem le_E_of_le_Ce {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({e} : Set Y)) : J ≤ rLayer (Om R) e :=
  C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hJ (H.two J hJ)) hJc

theorem K_le_X : tightCore R ≤ p23XE R e b :=
  (H.le_E_of_le_Ce mem_K H.K_le_Ce).trans (E_le_X R e b)

theorem exists_conj_of_le_Ce {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∃ x ∈ rLayer (Om R) e, conjSub x (tightCore R) = J :=
  exists_conj_of_le_Ce_of H.cfg H.two H.ae6 hJ hJc

theorem exists_conj_of_le_Eb {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJE : J ≤ conjSub b (rLayer (Om R) e)) :
    ∃ x ∈ p23XE R e b, conjSub x (tightCore R) = J :=
  H.eb J hJ hJE

theorem conj_K_le_X (x : p23XE R e b) : conjSub (x : Y) (tightCore R) ≤ p23XE R e b := by
  have := conjSub_mono (n := (x : Y)) H.K_le_X
  rwa [conjSub_eq_self_of_mem x.2] at this

theorem gen : (⨆ x : p23XE R e b, conjSub (x : Y) (tightCore R)) = p23XE R e b := by
  refine le_antisymm (iSup_le fun x => H.conj_K_le_X x) (sup_le ?_ ?_)
  · unfold rLayer
    refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
    rw [rSet_eq_of_isPGroup H.two] at hQ
    obtain ⟨x, hx, rfl⟩ := H.exists_conj_of_le_Ce hQ hQC
    exact le_iSup_of_le ⟨x, E_le_X R e b hx⟩ le_rfl
  · rw [← rLayer_conj (R := R) b e]
    unfold rLayer
    refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
    rw [rSet_eq_of_isPGroup H.two] at hQ
    have hQE : Q ≤ conjSub b (rLayer (Om R) e) := by
      rw [← rLayer_conj (R := R) b e]
      exact C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hQ (H.two Q hQ)) hQC
    obtain ⟨x, hx, rfl⟩ := H.exists_conj_of_le_Eb hQ hQE
    exact le_iSup_of_le ⟨x, hx⟩ le_rfl

theorem pSpan_eq : pSpan {J | J ∈ Om R ∧ J ≤ p23XE R e b} = p23XE R e b := by
  refine le_antisymm (pSpan_le fun J hJ => hJ.2) (H.gen.symm.le.trans (iSup_le fun x => ?_))
  exact le_pSpan ⟨H.hypOmega.conjInvariant _ _ mem_K, H.conj_K_le_X x⟩

theorem oddCore_le_center :
    classicalInvolutionOddCore ↥(p23XE R e b) ≤ Subgroup.center ↥(p23XE R e b) := by
  set X := p23XE R e b with hX
  set P : Set (Subgroup Y) := {L | ∃ x ∈ X, conjSub x (tightCore R) = L} with hP
  have hPΩ : P ⊆ Om R := by
    rintro _ ⟨x, -, rfl⟩
    exact H.hypOmega.conjInvariant x _ mem_K
  have hPX : ∀ L ∈ P, L ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.conj_K_le_X ⟨x, hx⟩
  have hinv : ∀ L ∈ P, ∀ x ∈ X, conjSub x L ∈ P := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    exact ⟨x * y, X.mul_mem hx hy, by rw [conjSub_mul]⟩
  have hzV : ∀ L ∈ P, ∀ z : Y, IsUniqueInvolution L z → z ∈ V := by
    rintro _ ⟨x, hx, rfl⟩ z hz
    rw [hz.eq (H.isUniqueInvolution_t.conj x)]
    exact H.norm x hx t H.tV
  have hgen : X ≤ pSpan P := H.gen.symm.le.trans (iSup_le fun x => le_pSpan ⟨x, x.2, rfl⟩)
  have hc := comm_of_mem_oddCoreOf H.hypOmega H.two H.norm H.v2 hPΩ hPX hinv hzV hgen
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hc r ⟨r, hr, rfl⟩ y y.2).symm

theorem mem_oddCore_of_theta_eq_one {h : ↥(coreHull (Om R) e)}
    (h1 : theta H.hypOmega H.isPGroup_zpowers_e b h = 1) :
    h ∈ classicalInvolutionOddCore ↥(coreHull (Om R) e) := by
  set X := p23XE R e b with hX
  set x : ↥X := ⟨hullInc R e h, hullInc_mem H.hypOmega H.isPGroup_zpowers_e b h⟩ with hx
  have hxO : x ∈ classicalInvolutionOddCore ↥X := by
    have : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x = 1 := h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hxc := H.oddCore_le_center hxO
  have hcomm : ∀ g : ↥(coreHull (Om R) e), g * h * g⁻¹ = h := by
    intro g
    apply hullInc_injective R e
    have h2 := Subgroup.mem_center_iff.mp hxc
      ⟨hullInc R e g, hullInc_mem H.hypOmega H.isPGroup_zpowers_e b g⟩
    have h3 : hullInc R e g * hullInc R e h = hullInc R e h * hullInc R e g :=
      congrArg Subtype.val h2
    rw [map_mul, map_mul, map_inv, h3]
    group
  have hn : (Subgroup.zpowers h).Normal := ⟨fun a ha g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, hcomm g]
    exact Subgroup.zpow_mem_zpowers h k⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers h)) := by
    rw [Nat.card_zpowers, ← orderOf_injective (hullInc R e) (hullInc_injective R e) h]
    have h4 : orderOf (hullInc R e h) = orderOf x := by rw [hx, Subgroup.orderOf_mk]
    rw [h4]
    have h5 : orderOf x ∣ Nat.card (classicalInvolutionOddCore ↥X) := by
      have := orderOf_dvd_natCard (⟨x, hxO⟩ : classicalInvolutionOddCore ↥X)
      rwa [Subgroup.orderOf_mk] at this
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥X).of_dvd_nat h5
  have hle : Subgroup.zpowers h ≤ classicalInvolutionOddCore ↥(coreHull (Om R) e) :=
    le_sSup ⟨hn, hodd⟩
  exact hle (Subgroup.mem_zpowers h)

theorem thin {Q : Subgroup (SecQuot (p23XE R e b))} (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    {k : Y} (hk : k ∈ tightCore R)
    (hkQ : QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b)) ⟨k, H.K_le_X hk⟩ ∈ Q) :
    k = 1 ∨ k = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) e) with hN
  have hS := p23_q8Section H.cfg.std.perp H.cfg.data.he2
  have hgen : pSpan (TwinDisc.secFam (Om R) e) = ⊤ := TwinDisc.AE5.hgen_of hS
  obtain ⟨I₆⟩ := H.ae6
  set T₁ := (Q.comap (theta H.hypOmega H.isPGroup_zpowers_e b)).map (QuotientGroup.mk' N)
    with hT₁
  have hT₁n : T₁.Normal := (hQn.comap _).map _ (QuotientGroup.mk'_surjective N)
  have hT₁2 : IsPGroup 2 T₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨h, hh, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hQ2 ⟨theta H.hypOmega H.isPGroup_zpowers_e b h, hh⟩
    have ha' : theta H.hypOmega H.isPGroup_zpowers_e b (h ^ 2 ^ a) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val ha
      simpa using this
    refine ⟨a, Subtype.ext ?_⟩
    show (QuotientGroup.mk' N h) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact H.mem_oddCore_of_theta_eq_one ha'
  set T₂ := T₁.comap (pSpan (TwinDisc.secFam (Om R) e)).subtype with hT₂
  have hT₂n : T₂.Normal := hT₁n.comap _
  have hT₂2 : IsPGroup 2 T₂ := hT₁2.comap_subtype
  have hker := TL4.AECov.le_ker_permHom_of_normal I₆ (by norm_num) hT₂n hT₂2
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    mem_tqMembers3_of_le_centralizer mem_K H.K_le_Ce
  have hcore : TwinADescent.coreAt e (tightCore R) = tightCore R :=
    coreAt_eq_self' H.K_le_Ce (H.two _ mem_K)
  have hkC : k ∈ Subgroup.centralizer ({e} : Set Y) := H.K_le_Ce hk
  have hkcore : (⟨k, hkC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) ∈
      (TwinADescent.coreAt e (tightCore R)).subgroupOf (Subgroup.centralizer ({e} : Set Y)) := by
    rw [Subgroup.mem_subgroupOf, hcore]
    exact hk
  set hk' : ↥(coreHull (Om R) e) := ⟨⟨k, hkC⟩, TwinDisc.le_coreHull hKtq hkcore⟩ with hhk'
  have hθk : theta H.hypOmega H.isPGroup_zpowers_e b hk' ∈ Q := hkQ
  set y : ↥(pSpan (TwinDisc.secFam (Om R) e)) :=
    ⟨QuotientGroup.mk' N hk', by rw [hgen]; exact Subgroup.mem_top _⟩ with hy
  have hyT : y ∈ T₂ := ⟨hk', hθk, rfl⟩
  obtain ⟨v, -, hv⟩ := TL4.AECov.exists_vec_of_mem_ker_permHom I₆ (hker hyT)
  set M := TwinDisc.secImg (Om R) e (tightCore R) with hM
  have hMm : M ∈ TwinDisc.secFam (Om R) e := TwinDisc.secImg_mem_secFam hKtq
  obtain ⟨α, hα, b₀, hlab⟩ := I₆.label M hMm
  have h8 := TwinDisc.AE5.members_card8 (by norm_num) hS I₆ M hMm
  have hyM : QuotientGroup.mk' N hk' ∈ M := ⟨hk', Subgroup.mem_subgroupOf.mpr hkcore, rfl⟩
  have hsq : QuotientGroup.mk' N hk' * QuotientGroup.mk' N hk' = 1 := by
    refine I₆.injOn (by norm_num) hMm h8 hlab (M.mul_mem hyM hyM) M.one_mem ?_
    have e1 : (⟨QuotientGroup.mk' N hk' * QuotientGroup.mk' N hk',
        le_pSpan hMm (M.mul_mem hyM hyM)⟩ : ↥(pSpan (TwinDisc.secFam (Om R) e))) = y * y := rfl
    have e2 : (⟨1, le_pSpan hMm M.one_mem⟩ : ↥(pSpan (TwinDisc.secFam (Om R) e))) = 1 := rfl
    have hvv : AE.Wr.ofVec v * AE.Wr.ofVec v = 1 :=
      AE.vecSub_mul_self (show (AE.Wr.ofVec v).perm = 1 from rfl)
    rw [e1, e2, map_mul, hv, map_one, ← map_mul, hvv, map_one]
  have hkk : hk' * hk' ∈ N := by
    have : QuotientGroup.mk' N (hk' * hk') = 1 := by rw [map_mul]; exact hsq
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hk2 : k * k = 1 := by
    have hodd : Odd (orderOf (hk' * hk')) := by
      have := orderOf_dvd_natCard (⟨hk' * hk', hkk⟩ : N)
      rw [Subgroup.orderOf_mk] at this
      exact (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat this
    have he : orderOf (k * k) = orderOf (hk' * hk') :=
      orderOf_injective (hullInc R e) (hullInc_injective R e) (hk' * hk')
    obtain ⟨j, hj⟩ := (H.two _ mem_K) ⟨k * k, (tightCore R).mul_mem hk hk⟩
    have hj' : (k * k) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hodd' : Odd (orderOf (k * k)) := by rw [he]; exact hodd
    have h1 : orderOf (k * k) = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd')) (orderOf_dvd_of_pow_eq_one hj')
      dvd_rfl
    exact orderOf_eq_one_iff.mp h1
  exact H.isUniqueInvolution_t.unique k hk hk2

theorem exists_orderOf_five : ∃ y : SecQuot (p23XE R e b), orderOf y = 5 := by
  obtain ⟨I₆⟩ := H.ae6
  obtain ⟨x₀, hx₀, h5, hne⟩ := TwinPerpV3.A6d.exists_order_five_aeSub
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (AE.mkQ 6 x₀) = 5 := orderOf_eq_prime h5 hne
  have hmem : AE.mkQ 6 x₀ ∈ I₆.φ.range := by
    rw [I₆.range_eq]
    exact ⟨x₀, hx₀, rfl⟩
  obtain ⟨yb, hyb⟩ := hmem
  have h1 : 5 ∣ orderOf yb := by
    rw [← hord, ← hyb]
    exact orderOf_map_dvd I₆.φ yb
  have h2 : 5 ∣ orderOf (yb : SecQ R e) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk_surjective (yb : SecQ R e)
  set m := orderOf (theta H.hypOmega H.isPGroup_zpowers_e b h₁) with hm
  have h3 : 5 ∣ m := by
    have hθm : theta H.hypOmega H.isPGroup_zpowers_e b (h₁ ^ m) = 1 := by
      rw [map_pow, hm, pow_orderOf_eq_one]
    have h4 := H.mem_oddCore_of_theta_eq_one hθm
    have h5' : (yb : SecQ R e) ^ m = 1 := by
      rw [← hh₁, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact h4
    exact h2.trans (orderOf_dvd_of_pow_eq_one h5')
  exact ⟨_, orderOf_pow_orderOf_div (orderOf_pos _).ne' h3⟩

theorem thmDHyp : ThmDHyp 3 (SectionThmD.secClass (p23XE R e b) (tightCore R)) :=
  SectionThmD.thmDHyp_secClass H.hypOmega H.two mem_K (H.card_of_mem mem_K)
    (CoreData.of_S H.cfg.std.perp.core).aEmpty H.K_le_X H.gen H.isUniqueInvolution_t H.norm
    H.v2 H.tV

theorem thmDConcl (hP : TL4.TightBelowRPlus 3 n) :
    ThmDConcl (SectionThmD.secClass (p23XE R e b) (tightCore R)) :=
  SectionThmD.thmDConcl_at_section H.hypOmega H.two mem_K (H.card_of_mem mem_K)
    (CoreData.of_S H.cfg.std.perp.core).aEmpty H.K_le_X H.gen H.isUniqueInvolution_t H.norm
    H.v2 H.tV hP.thmD.d2 H.card_lt

theorem oddCore_span_eq_bot :
    classicalInvolutionOddCore
      ↥(pSpan (SectionThmD.secClass (p23XE R e b) (tightCore R))) = ⊥ :=
  classicalInvolutionOddCore_eq_bot_of_mulEquiv
    ((MulEquiv.subgroupCongr H.thmDHyp.gen).trans Subgroup.topEquiv).symm
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(p23XE R e b))

theorem eq_of_secImage_eq {J J' : Subgroup Y} (hJ : J ∈ Om R) (hJ' : J' ∈ Om R)
    (hJX : J ≤ p23XE R e b) (hJ'X : J' ≤ p23XE R e b)
    (h : secImage (p23XE R e b) J = secImage (p23XE R e b) J') : J = J' := by
  have h1 := eq_of_map_eq_central H.oddCore_le_center
    (CFSG.ComponentClassification.OddCore.odd_card _) (H.two J hJ).comap_subtype
    (H.two J' hJ').comap_subtype h
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hJX, inf_eq_left.mpr hJ'X] at h2

theorem comm_of_secImage_comm {J J' : Subgroup Y} (hJ' : J' ∈ Om R)
    (hJX : J ≤ p23XE R e b) (hJ'X : J' ≤ p23XE R e b)
    (hc : ∀ x ∈ secImage (p23XE R e b) J, ∀ y ∈ secImage (p23XE R e b) J', x * y = y * x) :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  intro x hx y hy
  have hmx : QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b)) ⟨x, hJX hx⟩ ∈
      secImage (p23XE R e b) J := ⟨⟨x, hJX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hmy : QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b)) ⟨y, hJ'X hy⟩ ∈
      secImage (p23XE R e b) J' := ⟨⟨y, hJ'X hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  obtain ⟨a, ha⟩ := OddQuot.two_elt (H.two J' hJ') hy
  have hya : (⟨y, hJ'X hy⟩ : ↥(p23XE R e b)) ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha)
  exact congrArg Subtype.val (comm_of_mk_comm H.oddCore_le_center
    (CFSG.ComponentClassification.OddCore.odd_card _) hya (hc _ hmx _ hmy))

theorem eq_K'_of_comm {J : Subgroup Y} (hJ : J ∈ Om R) (hne : J ≠ tightCore R)
    (hc : ∀ x ∈ tightCore R, ∀ y ∈ J, x * y = y * x) : J = K' := by
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    H.cfg.std.perp.perp.trans (twinSet_eq_pair H.cfg.std.two H.cfg.std.hK' H.cfg.std.hne)
  have hJN : J ≤ Subgroup.normalizer (tightCore R : Set Y) :=
    le_normalizer_of_comm fun x hx y hy => (hc y hy x hx).symm
  have hJn : J ∈ omegaNbr (Om R) (tightCore R) :=
    (TC.mem_omegaNbr_iff H.hypOmega H.two).mpr ⟨hJ, hne, hJN⟩
  have hJp : J ∈ KPerp (Om R) (tightCore R) := Set.mem_insert_of_mem _ hJn
  rw [hperp] at hJp
  rcases hJp with h | h
  · exact absurd h hne
  · exact h

theorem secImage_mem_secClass (x : p23XE R e b) :
    secImage (p23XE R e b) (conjSub (x : Y) (tightCore R)) ∈
      SectionThmD.secClass (p23XE R e b) (tightCore R) :=
  SectionThmD.mem_secClass_iff.mpr ⟨x, rfl⟩

theorem K'_mem_secClass :
    secImage (p23XE R e b) K' ∈ SectionThmD.secClass (p23XE R e b) (tightCore R) := by
  obtain ⟨x, hx, hxK⟩ := H.exists_conj_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce
  have := H.secImage_mem_secClass ⟨x, E_le_X R e b hx⟩
  rwa [show conjSub x (tightCore R) = K' from hxK] at this

theorem K'_le_X : K' ≤ p23XE R e b :=
  (H.le_E_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce).trans (E_le_X R e b)

theorem secImage_K_ne_K' : secImage (p23XE R e b) (tightCore R) ≠ secImage (p23XE R e b) K' :=
  fun h => H.cfg.std.hne (H.eq_of_secImage_eq mem_K H.cfg.std.hK'.1 H.K_le_X H.K'_le_X h).symm

theorem false_of_single (hsing : ∀ L ∈ SectionThmD.secClass (p23XE R e b) (tightCore R),
    ∀ L' ∈ SectionThmD.secClass (p23XE R e b) (tightCore R), L = L') : False :=
  H.secImage_K_ne_K' (hsing _ (CoreAssembly.mem_conjClass_self _) _ H.K'_mem_secClass)

theorem false_of_wSet {W' : Subgroup (SecQuot (p23XE R e b))}
    (hW : WSet (SectionThmD.secClass (p23XE R e b) (tightCore R)) = {W'}) : False := by
  have hD := H.thmDHyp
  have hK : secImage (p23XE R e b) (tightCore R) ∈
      SectionThmD.secClass (p23XE R e b) (tightCore R) := CoreAssembly.mem_conjClass_self _
  have h4 := TL4.card_inf_of_wSet_eq hD hW _ hK
  have hWmem : W' ∈ WSet (SectionThmD.secClass (p23XE R e b) (tightCore R)) := by
    rw [hW]
    rfl
  have hWn : W'.Normal := ⟨fun w hw g => by
    have h1 := WSet.conj hD.hyp.conjInvariant hWmem g
    rw [hW] at h1
    have h2 : g * w * g⁻¹ ∈ conjSub g W' := conj_mem_conjSub hw
    rwa [show conjSub g W' = W' from h1] at h2⟩
  have hW2 : IsPGroup 2 W' := by
    obtain ⟨η, ⟨S, hη, -⟩, hWeq⟩ := hWmem
    have hWS : W' ≤ (S : Subgroup _) := by
      rw [hWeq]
      exact iSup₂_le fun U hU => (hη.1 hU).2
    exact S.isPGroup'.to_le hWS
  have hle : Nat.card ↥(secImage (p23XE R e b) (tightCore R) ⊓ W') ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1)
      (b := QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b))
        ⟨t, H.K_le_X H.isUniqueInvolution_t.mem⟩) fun x hx => ?_
    obtain ⟨⟨k', hk'X⟩, hk', rfl⟩ := hx.1
    have hk'K : k' ∈ tightCore R := Subgroup.mem_subgroupOf.mp hk'
    rcases H.thin hWn hW2 hk'K hx.2 with h1 | h1
    · left
      rw [← map_one (QuotientGroup.mk' (classicalInvolutionOddCore ↥(p23XE R e b)))]
      exact congrArg _ (Subtype.ext h1)
    · right
      exact congrArg _ (Subtype.ext h1)
  omega

theorem false_of_e8 {E' : Subgroup (SecQuot (p23XE R e b))} (hE : E8Struct ⊤ E') : False := by
  have hz' : IsUniqueInvolution K' t :=
    isUniqueInvolution_of_mem_twinSet H.isUniqueInvolution_t H.cfg.std.hK'
  have h1 := SectionThmD.isUniqueInvolution_secImage H.K_le_X (H.two _ mem_K) H.isUniqueInvolution_t
  have h2 := SectionThmD.isUniqueInvolution_secImage H.K'_le_X (H.two _ H.cfg.std.hK'.1) hz'
  exact H.secImage_K_ne_K' (eq_of_inv_e8 H.thmDHyp hE (CoreAssembly.mem_conjClass_self _)
    H.K'_mem_secClass h1 h2)

theorem false_of_order_five_model {m : ℕ} {𝒜 : Set (Finset (Fin m))} {Hm : Subgroup (AE.AEQ m)}
    (I : AEIdentOn (SectionThmD.secClass (p23XE R e b) (tightCore R)) m 𝒜 Hm)
    (hno : TwinPerpV3.A6d.NoOrderFive Hm) : False := by
  obtain ⟨y, hy⟩ := H.exists_orderOf_five
  have hk := I.toLabel.isPGroup_ker H.oddCore_span_eq_bot
  refine TwinPerpV3.A6d.false_of_order_five I.φ hk I.range_eq hno
    ⟨y, by rw [H.thmDHyp.gen]; exact Subgroup.mem_top y⟩ ?_
  rw [Subgroup.orderOf_mk]
  exact hy

theorem false_of_ae_ge8 {m : ℕ} (hm : 8 ≤ m)
    (I : AEIdent (SectionThmD.secClass (p23XE R e b) (tightCore R)) m) : False := by
  have hD := H.thmDHyp
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker H.oddCore_span_eq_bot
  have hn5 : 5 ≤ m := by omega
  have hK : secImage (p23XE R e b) (tightCore R) ∈
      SectionThmD.secClass (p23XE R e b) (tightCore R) := CoreAssembly.mem_conjClass_self _
  obtain ⟨α, hα, b₀, hlab₀⟩ := I.label _ hK
  obtain ⟨β, hβsub, hβ⟩ : ∃ β ⊆ Finset.univ \ α, β.card = 4 := Finset.exists_subset_card_eq (by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hα]
    omega)
  have hd : Disjoint α β := Finset.disjoint_of_subset_right hβsub Finset.disjoint_sdiff
  have hneK : ∀ {L : Subgroup (SecQuot (p23XE R e b))} {c : Bool},
      (L.subgroupOf (pSpan (SectionThmD.secClass (p23XE R e b) (tightCore R)))).map I.φ =
        AE.memBar β hβ c → L ≠ secImage (p23XE R e b) (tightCore R) := by
    intro L c hlab h
    rw [h, hlab₀] at hlab
    have hαβ : α = β := AE.eq_of_memBar_eq' hn5 hlab
    subst hαβ
    have h0 : α = ∅ := disjoint_self.mp hd
    rw [h0, Finset.card_empty] at hα
    omega
  have hcomm : ∀ {L : Subgroup (SecQuot (p23XE R e b))} {c : Bool},
      L ∈ SectionThmD.secClass (p23XE R e b) (tightCore R) →
      (L.subgroupOf (pSpan (SectionThmD.secClass (p23XE R e b) (tightCore R)))).map I.φ =
        AE.memBar β hβ c → L = secImage (p23XE R e b) K' := by
    intro L c hL hlab
    have hc := aeIdent_comm_of_map_comm hD.hyp hD.two subset_rfl I hk hK hL (hneK hlab).symm
      (by rw [hlab₀, hlab]; exact AE.comm_memBar_of_disjoint hd b₀ c)
    obtain ⟨x, hx⟩ := SectionThmD.mem_secClass_iff.mp hL
    have hJ : conjSub (x : Y) (tightCore R) ∈ Om R := H.hypOmega.conjInvariant _ _ mem_K
    have hcY := H.comm_of_secImage_comm hJ H.K_le_X (H.conj_K_le_X x) (by rw [hx]; exact hc)
    have hJne : conjSub (x : Y) (tightCore R) ≠ tightCore R := fun h =>
      hneK hlab (by rw [← hx, h])
    rw [← hx, H.eq_K'_of_comm hJ hJne hcY]
  obtain ⟨L₁, hL₁, hlab₁⟩ := I.label_surj β hβ true
  obtain ⟨L₂, hL₂, hlab₂⟩ := I.label_surj β hβ false
  have h12 : L₁ = L₂ := (hcomm hL₁ hlab₁).trans (hcomm hL₂ hlab₂).symm
  rw [h12] at hlab₁
  exact AE.memBar_true_ne_false hn5 β hβ (hlab₁.symm.trans hlab₂)

theorem false_of_ae_le6 {m : ℕ} (hm5 : 5 ≤ m) (hm6 : m ≤ 6)
    (I : AEIdent (SectionThmD.secClass (p23XE R e b) (tightCore R)) m) : False := by
  classical
  have hD := H.thmDHyp
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker H.oddCore_span_eq_bot
  obtain ⟨I₆⟩ := H.ae6
  set 𝔐 : Set (Subgroup Y) := {J | J ∈ Om R ∧ J ≤ Subgroup.centralizer ({e} : Set Y)} with h𝔐
  set F : Subgroup Y → Finset (Fin m) × Bool := fun J => labelOf I (secImage (p23XE R e b) J)
    with hF
  set G' : Subgroup Y → Finset (Fin 6) × Bool := fun J => labelOf I₆ (TwinDisc.secImg (Om R) e J)
    with hG'
  have hX𝔐 : ∀ J ∈ 𝔐, J ≤ p23XE R e b := fun J hJ =>
    (H.le_E_of_le_Ce hJ.1 hJ.2).trans (E_le_X R e b)
  have hΦ𝔐 : ∀ J ∈ 𝔐, secImage (p23XE R e b) J ∈
      SectionThmD.secClass (p23XE R e b) (tightCore R) := by
    intro J hJ
    obtain ⟨x, hx, rfl⟩ := H.exists_conj_of_le_Ce hJ.1 hJ.2
    exact H.secImage_mem_secClass ⟨x, E_le_X R e b hx⟩
  have hmaps : ∀ J ∈ 𝔐, F J ∈ {p : Finset (Fin m) × Bool | p.1.card = 4} := fun J hJ =>
    (labelOf_spec I (hΦ𝔐 J hJ)).1
  have hinj : Set.InjOn F 𝔐 := by
    intro J hJ J' hJ' h
    have h1 := map_eq_of_labelOf_eq I (hΦ𝔐 J hJ) (hΦ𝔐 J' hJ') h
    have h2 := aeIdent_eq_of_map_eq hD.hyp hD.two subset_rfl hm5 I hk (hΦ𝔐 J hJ) (hΦ𝔐 J' hJ') h1
    exact H.eq_of_secImage_eq hJ.1 hJ'.1 (hX𝔐 J hJ) (hX𝔐 J' hJ') h2
  have hsurj : {p : Finset (Fin 6) × Bool | p.1.card = 4} ⊆ G' '' 𝔐 := by
    rintro ⟨α, c⟩ hp
    obtain ⟨M, hM, hlab⟩ := I₆.label_surj α hp c
    obtain ⟨J, hJtq, rfl⟩ := TwinDisc.exists_of_mem_secFam hM
    have hJc : J ≤ Subgroup.centralizer ({e} : Set Y) :=
      le_centralizer_of_mem_trivialOnQuot (H.two J hJtq.1) hJtq.2
    exact ⟨J, ⟨hJtq.1, hJc⟩, labelOf_eq I₆ (by norm_num) hM hlab⟩
  have hfin : 𝔐.Finite := Set.toFinite _
  have h1 : {p : Finset (Fin 6) × Bool | p.1.card = 4}.ncard ≤ 𝔐.ncard :=
    (Set.ncard_le_ncard hsurj (hfin.image _)).trans (Set.ncard_image_le hfin)
  have h2 : 𝔐.ncard ≤ {p : Finset (Fin m) × Bool | p.1.card = 4}.ncard :=
    Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.toFinite _)
  rw [ncard_labels] at h1 h2
  interval_cases m
  · norm_num [Nat.choose] at h1 h2
    omega
  ·
    have hall : F '' 𝔐 = {p : Finset (Fin 6) × Bool | p.1.card = 4} := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro _ ⟨J, hJ, rfl⟩
        exact hmaps J hJ
      · rw [hinj.ncard_image, ncard_labels]
        exact h1
    have hEb : conjSub b (rLayer (Om R) e) ≤ rLayer (Om R) e := by
      rw [← rLayer_conj (R := R) b e]
      refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
      rw [rSet_eq_of_isPGroup H.two] at hQ
      have hQEb : Q ≤ conjSub b (rLayer (Om R) e) := by
        rw [← rLayer_conj (R := R) b e]
        exact C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hQ (H.two Q hQ)) hQC
      obtain ⟨x, hx, hxQ⟩ := H.exists_conj_of_le_Eb hQ hQEb
      have hQΦ : secImage (p23XE R e b) Q ∈ SectionThmD.secClass (p23XE R e b) (tightCore R) := by
        rw [← hxQ]
        exact H.secImage_mem_secClass ⟨x, hx⟩
      have hQX : Q ≤ p23XE R e b := hQEb.trans (Eb_le_X R e b)
      have hFQ : F Q ∈ F '' 𝔐 := by
        rw [hall]
        exact (labelOf_spec I hQΦ).1
      obtain ⟨J, hJ, hJQ⟩ := hFQ
      have h3 := map_eq_of_labelOf_eq I (hΦ𝔐 J hJ) hQΦ hJQ
      have h4 := aeIdent_eq_of_map_eq hD.hyp hD.two subset_rfl (by norm_num) I hk (hΦ𝔐 J hJ)
        hQΦ h3
      have h5 := H.eq_of_secImage_eq hJ.1 hQ (hX𝔐 J hJ) hQX h4
      rw [← h5]
      exact H.le_E_of_le_Ce hJ.1 hJ.2
    have hcard : Nat.card (rLayer (Om R) e) ≤ Nat.card (conjSub b (rLayer (Om R) e)) :=
      (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge
    exact H.ne (Subgroup.eq_of_le_of_card_ge hEb hcard)

theorem trans (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJX : J ≤ p23XE R e b) : ∃ x : p23XE R e b, conjSub (x : Y) (tightCore R) = J := by
  by_contra hcon
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥(p23XE R e b)
  have hΩX : HypOmegaGen (restrictFamily (Om R) (p23XE R e b)) :=
    hypOmegaGen_restrict H.hypOmega (p23XE R e b)
  have h2X : ∀ L ∈ restrictFamily (Om R) (p23XE R e b), IsPGroup 2 L := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact (H.two L hL).comap_subtype
  have hAX : ∀ L ∈ restrictFamily (Om R) (p23XE R e b),
      AEmpty (restrictFamily (Om R) (p23XE R e b)) L := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    exact aEmpty_restrictFamily H.hypOmega H.two subset_rfl hLX
      ((CoreData.of_S H.cfg.std.perp.core).aEmpty_all L hL)
  have hΔ1 := OddQuot.hypOmegaGen_quotFamily hΩX h2X hNodd
  have hΔA := OddQuot.aEmpty_quotFamily hΩX h2X hNodd hAX
  have hmemΔ : ∀ {L : Subgroup Y}, L ∈ Om R → L ≤ p23XE R e b → secImage (p23XE R e b) L ∈
      quotFamily (restrictFamily (Om R) (p23XE R e b))
        (classicalInvolutionOddCore ↥(p23XE R e b)) :=
    fun hL hLX => ⟨_, ⟨_, hL, hLX, rfl⟩, rfl⟩
  have hΔ2' : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e b))
      (classicalInvolutionOddCore ↥(p23XE R e b)), IsPGroup 2 M := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact (H.two L hL).comap_subtype.map _
  have hΔ2 : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e b))
      (classicalInvolutionOddCore ↥(p23XE R e b)),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := fun M hM =>
    (hΔ2' M hM).to_quotient (classicalInvolutionOddCore ↥M)
  have hΔq : ∀ M ∈ quotFamily (restrictFamily (Om R) (p23XE R e b))
      (classicalInvolutionOddCore ↥(p23XE R e b)), ∀ P : Subgroup (SecQuot (p23XE R e b)),
      IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rintro _ ⟨_, ⟨L, hL, hLX, rfl⟩, rfl⟩ P hP
    have hM2 : IsPGroup 2 (secImage (p23XE R e b) L) :=
      SectionThmD.isPGroup_secImage (H.two L hL)
    have hPM : P = secImage (p23XE R e b) L := (hP.2.2 _ le_rfl hM2 hP.1).symm
    obtain ⟨e8⟩ := H.q8_of_mem hL
    exact ⟨(MulEquiv.subgroupCongr hPM).trans
      ((SectionThmD.secImageEquiv hLX (H.two L hL)).trans e8)⟩
  have hodd : classicalInvolutionOddCore (SecQuot (p23XE R e b)) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥(p23XE R e b)
  have hcard : Nat.card (SecQuot (p23XE R e b)) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)) H.card_lt
  have hnc : ¬ ∃ g : SecQuot (p23XE R e b),
      conjSub g (secImage (p23XE R e b) (tightCore R)) = secImage (p23XE R e b) J := by
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(p23XE R e b)) g
    have hg' : secImage (p23XE R e b) (conjSub (x : Y) (tightCore R)) =
        secImage (p23XE R e b) J := by
      rw [SectionThmD.secImage_conjSub]
      exact hg
    exact hcon ⟨x, H.eq_of_secImage_eq (H.hypOmega.conjInvariant _ _ mem_K) hJ
      (H.conj_K_le_X x) hJX hg'⟩
  have hcomm := hT (SecQuot (p23XE R e b)) hcard _ hΔ1 hΔ2 hΔq hΔA hodd _
    (hmemΔ mem_K H.K_le_X) _ (hmemΔ hJ hJX) hnc
  have hcY := H.comm_of_secImage_comm hJ H.K_le_X hJX hcomm
  have hJne : J ≠ tightCore R := fun h => hcon ⟨1, by rw [h]; simp⟩
  have hJK' := H.eq_K'_of_comm hJ hJne hcY
  obtain ⟨x, hx, hxK⟩ := H.exists_conj_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce
  exact hcon ⟨⟨x, E_le_X R e b hx⟩, by rw [hJK']; exact hxK⟩

theorem aeIdent7 (hT : Thm4RTwinBelow 3 n)
    (I : AEIdent (SectionThmD.secClass (p23XE R e b) (tightCore R)) 7) :
    Nonempty (AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) := by
  have hfam : SectionThmD.secClass (p23XE R e b) (tightCore R) =
      quotFamZ (classicalInvolutionOddCore ↥(p23XE R e b))
        (restrictFamily (Om R) (p23XE R e b)) := by
    ext L
    constructor
    · intro hL
      obtain ⟨x, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
      exact ⟨_, ⟨_, H.hypOmega.conjInvariant _ _ mem_K, H.conj_K_le_X x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨J, hJ, hJX, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := H.trans hT hJ hJX
      exact SectionThmD.mem_secClass_iff.mpr ⟨x, by rw [hx]; rfl⟩
  have hmap : (pSpan (restrictFamily (Om R) (p23XE R e b))).map (p23XE R e b).subtype =
      p23XE R e b := by
    refine le_antisymm (Subgroup.map_subtype_le _)
      (H.pSpan_eq.symm.le.trans (pSpan_le fun L hL => ?_))
    calc L = (L.subgroupOf (p23XE R e b)).map (p23XE R e b).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hL.2).symm
      _ ≤ _ := Subgroup.map_mono
          (le_pSpan (P := restrictFamily (Om R) (p23XE R e b)) ⟨L, hL.1, hL.2, rfl⟩)
  have hgen : pSpan (restrictFamily (Om R) (p23XE R e b)) = ⊤ := by
    apply Subgroup.map_injective (p23XE R e b).subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hO : ThmDHypO 3 (restrictFamily (Om R) (p23XE R e b)) := by
    refine ⟨hypOmegaGen_restrict H.hypOmega (p23XE R e b), ?_, ?_, ?_, hgen, ?_⟩
    · rintro _ ⟨L, hL, -, rfl⟩
      exact (H.two L hL).comap_subtype
    · rintro _ ⟨L, hL, hLX, rfl⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv, H.card_of_mem hL]
      norm_num
    · rintro _ ⟨L, hL, hLX, rfl⟩
      exact aEmpty_restrictFamily H.hypOmega H.two subset_rfl hLX
        ((CoreData.of_S H.cfg.std.perp.core).aEmpty_all L hL)
    · rintro _ ⟨L, hL, hLX, rfl⟩ u hu
      obtain ⟨x, hx⟩ := H.trans hT hL hLX
      have hu' : IsUniqueInvolution L (u : Y) := isUniqueInvolution_of_subgroupOf hu hLX
      have hxu : (u : Y) = x * t * x⁻¹ :=
        hu'.eq (by rw [← hx]; exact H.isUniqueInvolution_t.conj x)
      refine ⟨V.subgroupOf (p23XE R e b), ⟨fun v hv g => ?_⟩, H.v2.comap_subtype, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (H.norm g g.2 v (Subgroup.mem_subgroupOf.mp hv))
      · rw [Subgroup.mem_subgroupOf, hxu]
        exact H.norm x x.2 t H.tV
  have hZK : ∀ K ∈ restrictFamily (Om R) (p23XE R e b),
      classicalInvolutionOddCore ↥(p23XE R e b) ⊓ K = ⊥ := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact oddCore_inf_eq_bot (H.two L hL).comap_subtype
  exact nonempty_aeIdent_of_restrict H.pSpan_eq
    (AEIdent.ofQuotZ hO H.oddCore_le_center hZK (AEIdent.ofEq hfam I))

theorem nonempty_aeIdent (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n) :
    Nonempty (AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) := by
  rcases H.thmDConcl hP with hsing | ⟨W', hW'⟩ | ⟨E', hE'⟩ | hI64 | ⟨m, hm5, hIm⟩ | hI29
  · exact (H.false_of_single hsing).elim
  · exact (H.false_of_wSet hW').elim
  · exact (H.false_of_e8 hE').elim
  · obtain ⟨I⟩ := hI64
    exact (H.false_of_order_five_model I TwinPerpV3.A6d.noOrderFive_e64Sub).elim
  · obtain ⟨I⟩ := hIm
    rcases lt_trichotomy m 7 with hm | rfl | hm
    · exact (H.false_of_ae_le6 hm5 (by omega) I).elim
    · exact H.aeIdent7 hT I
    · exact (H.false_of_ae_ge8 (by omega) I).elim
  · obtain ⟨I⟩ := hI29
    exact (H.false_of_order_five_model I TwinPerpV3.A6d.noOrderFive_e29Sub).elim

end Hyp

end Cert

end AAE7

section Main


variable {n : ℕ}

theorem p23E8AAE7_of_xv (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hXV : P23E8AXV n) :
    P23E8AAE7 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 hα
  obtain ⟨b, V, -, hVn, hV2, htV, -, -, hne, hmeet⟩ :=
    hXV hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα
  have htwo := p23E8A_members_isPGroup hE hcit hP hc hA5 hα
  have H : AAE7.Hyp n Y R S t K' W u e g b V :=
    ⟨hc, htwo, hA6, hVn, hV2, htV, hne, AAE7.eb_of_meet hc htwo hA6 hmeet⟩
  exact ⟨b, V, H.v_ne_bot, hV2, H.le_normalizer, H.nonempty_aeIdent hP hT, H.K_le_X⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

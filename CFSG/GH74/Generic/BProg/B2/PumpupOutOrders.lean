module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableAssembly
public import CFSG.GH74.Generic.BProg.B2.PumpupOutOrdersAux
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub mem_fixSub)
open CFSG.Open (ordG2 ordTrialityD4)
open scoped commutatorElement

theorem comp_eq_of_simple_normal {G : Type} [Group G] {L F : Subgroup G} (hL : IsComponent L)
    (hcomm : ∀ a b : G, ⁅a, b⁆ ∈ F) (hF : IsSimpleGroup ↥F) : L = F := by
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hLF : L ≤ F := by
    rw [← hperf]
    exact Subgroup.commutator_le.2 (fun a _ b _ => hcomm a b)
  have hsub : (L.subgroupOf F).IsSubnormal := hL.2.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hF hsub with h | h
  · exfalso
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have hL0 : L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have : (⟨x, hLF hx⟩ : ↥F) ∈ L.subgroupOf F := hx
      rw [h] at this
      simpa using congrArg Subtype.val (Subgroup.mem_bot.1 this)
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥L)
    exact ha (Subtype.ext (Subgroup.mem_bot.1 (hL0 ▸ a.2)))
  · refine le_antisymm hLF ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥F) ∈ L.subgroupOf F := by rw [h]; trivial
    exact this

theorem no_shape_of_simple_fixed {G : Type} [Group G] {X L L0 : Subgroup G} (hL : IsCompIn X L)
    (hL0 : L0 ≤ X) (hcomm : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ L0) (hsimple : IsSimpleGroup ↥L0)
    {Z : Subgroup ↥L} (hZc : Z ≤ center ↥L) [Z.Normal] (hQ : QShapeNS (↥L ⧸ Z)) :
    L = L0 ∧ Z = ⊥ ∧ QShapeNS ↥L0 := by
  have hLc : IsComponent (L.subgroupOf X) := hL.2
  have hF0comm : ∀ a b : ↥X, ⁅a, b⁆ ∈ L0.subgroupOf X := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hcomm a a.2 b b.2
  have hF0 : IsSimpleGroup ↥(L0.subgroupOf X) :=
    ((Subgroup.subgroupOfEquivOfLe hL0).isSimpleGroup_congr).2 hsimple
  have hEq : L = L0 := by
    have h := comp_eq_of_simple_normal hLc hF0comm hF0
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hL.1, inf_eq_left.2 hL0] at h
    exact h
  subst hEq
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hLc.1
  have hZ : Z = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hLq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hb : b ∈ center ↥L := hZc (h ▸ Subgroup.mem_top b)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hb a).symm]
  have hinj : Function.Injective (QuotientGroup.mk' Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let eQ : ↥L ≃* (↥L ⧸ Z) :=
    MulEquiv.ofBijective (QuotientGroup.mk' Z) ⟨hinj, QuotientGroup.mk'_surjective Z⟩
  exact ⟨rfl, hZ, QShapeNS.of_mulEquiv eQ.symm hQ⟩

theorem no_shape_of_simple {G : Type} [Group G] {X L : Subgroup G} (hL : IsCompIn X L)
    (hsimple : IsSimpleGroup ↥X) {Z : Subgroup ↥L} (hZc : Z ≤ center ↥L) [Z.Normal]
    (hQ : QShapeNS (↥L ⧸ Z)) : L = X ∧ Z = ⊥ ∧ QShapeNS ↥X :=
  no_shape_of_simple_fixed hL le_rfl (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hsimple hZc hQ

section Aut

variable {N : Type} [Group N] {H : Subgroup N} [H.Normal] {t : N}

theorem conjNormal_sq (ht : orderOf t = 2) :
    (MulAut.conjNormal t : MulAut ↥H) * MulAut.conjNormal t = 1 := by
  rw [← map_mul]
  have : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, sq] at h
  rw [this, map_one]

theorem conjNormal_not_inner (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (htH : t ∉ H) :
    (MulAut.conjNormal t : MulAut ↥H) ∉ (MulAut.conj : ↥H →* MulAut ↥H).range := by
  rintro ⟨y, hy⟩
  apply htH
  have hy' : ∀ h : ↥H, (y : N) * h * (y : N)⁻¹ = t * h * t⁻¹ := by
    intro h
    have := congrArg (fun σ : MulAut ↥H => ((σ h : ↥H) : N)) hy
    simpa [MulAut.conjNormal_apply] using this
  have h1 : (y : N)⁻¹ * t = 1 := by
    apply hfaith
    intro h hh
    have := hy' ⟨h, hh⟩
    simp only at this
    calc (y : N)⁻¹ * t * h = (y : N)⁻¹ * (t * h * t⁻¹) * t := by group
      _ = (y : N)⁻¹ * ((y : N) * h * (y : N)⁻¹) * t := by rw [this]
      _ = h * ((y : N)⁻¹ * t) := by group
  have : t = (y : N) := by
    simpa using congrArg (fun z => (y : N) * z) h1
  rw [this]
  exact y.2

theorem mem_fixSub_conjNormal {y : ↥H} :
    y ∈ fixSub (MulAut.conjNormal t : MulAut ↥H) ↔ (y : N) ∈ Subgroup.centralizer ({t} : Set N) := by
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [MulAut.conjNormal_apply] at this
    calc (y : N) * t = (t * y * t⁻¹) * t := by rw [this]
      _ = t * y := by group
  · intro h
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← h]
    group

theorem exists_outer_aut (ht : orderOf t = 2)
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (htH : t ∉ H) {Y : Type} [Group Y]
    (e : ↥H ≃* Y) : ∃ α : MulAut Y, α * α = 1 ∧ α ∉ (MulAut.conj : Y →* MulAut Y).range ∧
      ∀ y : Y, α y = y ↔ ((e.symm y : ↥H) : N) ∈ Subgroup.centralizer ({t} : Set N) := by
  refine ⟨MulAut.congr e (MulAut.conjNormal t), ?_, ?_, ?_⟩
  · rw [← map_mul, conjNormal_sq ht, map_one]
  · rintro ⟨y0, hy0⟩
    refine conjNormal_not_inner hfaith htH ⟨e.symm y0, MulEquiv.ext fun h => ?_⟩
    have := congrArg (fun σ : MulAut Y => e.symm (σ (e h))) hy0
    simpa [MulAut.congr_apply] using this
  · intro y
    rw [← mem_fixSub_conjNormal (H := H) (t := t) (y := e.symm y), mem_fixSub]
    simp only [MulAut.congr_apply]
    constructor
    · intro h
      have := congrArg e.symm h
      simpa using this
    · intro h
      have := congrArg e h
      simpa using this

theorem exists_fixEquiv :
    Nonempty (↥(H ⊓ Subgroup.centralizer ({t} : Set N)) ≃*
      ↥(fixSub (MulAut.conjNormal t : MulAut ↥H))) := by
  have hF : fixSub (MulAut.conjNormal t : MulAut ↥H) =
      (H ⊓ Subgroup.centralizer ({t} : Set N)).subgroupOf H := by
    ext y
    rw [mem_fixSub_conjNormal, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  exact ⟨(Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H)).symm.trans
    (MulEquiv.subgroupCongr hF.symm)⟩

end Aut

section Descent

variable {N : Type} [Group N] [Finite N] {H : Subgroup N} [H.Normal] {t : N} {L : Subgroup N}

theorem exists_shape_comp_fixSub (hs : ShapeInCent H t L) :
    ∃ L3 : Subgroup ↥H, IsCompIn (fixSub (MulAut.conjNormal t : MulAut ↥H)) L3 ∧
      ∃ Z : Subgroup ↥L3, Z ≤ center ↥L3 ∧ Odd (Nat.card ↥Z) ∧
        ∃ _ : Z.Normal, QShapeNS (↥L3 ⧸ Z) := by
  obtain ⟨Φ⟩ := exists_fixEquiv (H := H) (t := t)
  set F : Subgroup ↥H := fixSub (MulAut.conjNormal t : MulAut ↥H) with hFdef
  set X : Subgroup N := H ⊓ Subgroup.centralizer ({t} : Set N) with hXdef
  have hL1 : IsComponent (L.subgroupOf X) := hs.comp.2
  let eM : ↥(L.subgroupOf X) ≃* ↥((L.subgroupOf X).map Φ.toMonoidHom) :=
    (L.subgroupOf X).equivMapOfInjective Φ.toMonoidHom Φ.injective
  have hL2 : IsComponent ((L.subgroupOf X).map Φ.toMonoidHom) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eM hL1.1, hL1.2.map Φ.surjective⟩
  set L2 : Subgroup ↥F := (L.subgroupOf X).map Φ.toMonoidHom with hL2def
  set L3 : Subgroup ↥H := L2.map F.subtype with hL3def
  have hL3F : L3 ≤ F := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : L3.subgroupOf F = L2 := Subgroup.comap_map_eq_self_of_injective F.subtype_injective L2
  let eL : ↥L ≃* ↥L3 :=
    (Subgroup.subgroupOfEquivOfLe hs.comp.1).symm.trans
      (eM.trans ((MulEquiv.subgroupCongr hsub).symm.trans (Subgroup.subgroupOfEquivOfLe hL3F)))
  refine ⟨L3, ⟨hL3F, by rw [hsub]; exact hL2⟩, ?_⟩
  obtain ⟨Z, hZc, hZo, hZn, hsh⟩ := hs.shape
  have := hZn
  have hn' : (Z.map eL.toMonoidHom).Normal := Subgroup.Normal.map hZn eL.toMonoidHom eL.surjective
  refine ⟨Z.map eL.toMonoidHom, ?_, ?_, hn', ?_⟩
  · rw [← Subgroup.map_center_eq eL]
    exact Subgroup.map_mono hZc
  · rwa [Subgroup.card_map_of_injective eL.injective]
  · exact QShapeNS.of_mulEquiv (QuotientGroup.congr Z (Z.map eL.toMonoidHom) eL rfl) hsh

theorem qShapeNS_of_descent (hs : ShapeInCent H t L) (L0 : Subgroup ↥H)
    (hL0 : L0 ≤ fixSub (MulAut.conjNormal t : MulAut ↥H))
    (hcomm : ∀ a ∈ fixSub (MulAut.conjNormal t : MulAut ↥H),
      ∀ b ∈ fixSub (MulAut.conjNormal t : MulAut ↥H), ⁅a, b⁆ ∈ L0)
    (hsimple : IsSimpleGroup ↥L0) : QShapeNS ↥L0 := by
  obtain ⟨L3, hL3, Z, hZc, -, hZn, hsh⟩ := exists_shape_comp_fixSub hs
  have := hZn
  exact (no_shape_of_simple_fixed hL3 hL0 hcomm hsimple hZc hsh).2.2

end Descent

@[expose] def G2OuterFixedSimple : Prop :=
  ∀ {p f : ℕ}, p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → ∀ {Y : Type} [Group Y] [Finite Y],
    LieModel Y .G2 0 p f → ∀ α : MulAut Y, α * α = 1 →
      α ∉ (MulAut.conj : Y →* MulAut Y).range →
      ∃ L0 : Subgroup Y, L0 ≤ fixSub α ∧ (L0.subgroupOf (fixSub α)).Normal ∧
        (∀ a ∈ fixSub α, ∀ b ∈ fixSub α, ⁅a, b⁆ ∈ L0) ∧ IsSimpleGroup ↥L0 ∧
        ∃ e : ℕ, 1 ≤ e ∧ LieModel ↥L0 .G2 0 p e

@[expose] def Psp4OuterNoShape : Prop :=
  ∀ {p f : ℕ}, p.Prime → p ≠ 2 → 1 ≤ f → ∀ {Y : Type} [Group Y] [Finite Y],
    LieModel Y .PSp 2 p f → ∀ α : MulAut Y, α * α = 1 →
      α ∉ (MulAut.conj : Y →* MulAut Y).range →
      ∀ L : Subgroup Y, IsCompIn (fixSub α) L →
        ∀ Z : Subgroup ↥L, Z ≤ center ↥L → Odd (Nat.card ↥Z) → ∀ _ : Z.Normal,
          ¬ QShapeNS (↥L ⧸ Z)

theorem sp4out_of_noShape (h : Psp4OuterNoShape) (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) : PumpupEmptyOut (fun X _ => LieModel X .PSp 2 p f) := by
  intro N _ _ H t L hs htH hH
  have := hs.normal
  obtain ⟨L3, hL3, Z, hZc, hZo, hZn, hsh⟩ := exists_shape_comp_fixSub hs
  exact h hp hp2 hf hH (MulAut.conjNormal t) (conjNormal_sq hs.inv)
    (conjNormal_not_inner hs.faithful htH) L3 hL3 Z hZc hZo hZn hsh

theorem not_qShape1_of_simple {K : Type} [Group K] [IsSimpleGroup K] (h1 : QShape1 K)
    (hdvd : 16 ∣ Nat.card K) : False := by
  have hc := CFSG.GH74.L5U5.IsSL4Model.natCard_center h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · rw [h, Subgroup.card_bot] at hc
    omega
  · rw [h, Subgroup.card_top] at hc
    omega

section Certified

theorem not_qShapeNS_of_G2 {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (he : 1 ≤ e) (hX : LieModel X .G2 0 p e) (hs : IsSimpleGroup X) :
    ¬ QShapeNS X := by
  have hcard : Nat.card X = ordG2 (p ^ e) := CFSG.GH74.card_of_lieModel_G2 hp2 hX
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h16 : 16 ∣ Nat.card X := hcard ▸ sixteen_dvd_ordG2 hodd
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    omega
  have hq5 : 5 ≤ p ^ e := hp5.trans (Nat.le_self_pow (by omega) p)
  rintro (h1 | ⟨s, g, hsp, hs2, hr, hL | hL⟩ | ⟨f, hf⟩ | h5)
  · exact not_qShape1_of_simple h1 h16
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
    exact g2_not_shape3 hp hp2 hq5 (r := s ^ g) (by omega) (Or.inl (hcard.symm.trans hc))
  · have hc := CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hs2 hL
    exact g2_not_shape3 hp hp2 hq5 (r := s ^ g) (by omega) (Or.inr (hcard.symm.trans hc))
  · obtain ⟨k, -, hk⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hf
    rw [hk] at h16
    exact not_sixteen_dvd_ordRee k h16
  · rw [ShapeOrders.qShape5_facts h5] at h16
    exact not_sixteen_dvd_J1 h16

theorem not_qShapeNS_of_D4 {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hX : LieModel X .trialityD4 0 p e) (hs : IsSimpleGroup X) : ¬ QShapeNS X := by
  have hcard : Nat.card X = ordTrialityD4 (p ^ e) := CFSG.GH74.card_of_lieModel_trialityD4 hp2 hX
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h16 : 16 ∣ Nat.card X := hcard ▸ sixteen_dvd_ordTrialityD4 hodd
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hq3 : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow (by omega) p)
  rintro (h1 | ⟨s, g, hsp, hs2, hr, hL | hL⟩ | ⟨f, hf⟩ | h5)
  · exact not_qShape1_of_simple h1 h16
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
    exact d4_not_shape3 hp hp2 hq3 (r := s ^ g) (by omega) (Or.inl (hcard.symm.trans hc))
  · have hc := CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hs2 hL
    exact d4_not_shape3 hp hp2 hq3 (r := s ^ g) (by omega) (Or.inr (hcard.symm.trans hc))
  · obtain ⟨k, -, hk⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hf
    rw [hk] at h16
    exact not_sixteen_dvd_ordRee k h16
  · rw [ShapeOrders.qShape5_facts h5] at h16
    exact not_sixteen_dvd_J1 h16

theorem d4out_of_descent (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    PumpupEmptyOut (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro N _ _ H t L hs htH hH
  have := hs.normal
  obtain ⟨e', he', hsimple, -, hmodel⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.td4_outer_involution_fixed hp hp2 hf hH
      (MulAut.conjNormal t : MulAut ↥H) (by rw [sq]; exact conjNormal_sq hs.inv)
      (conjNormal_not_inner hs.faithful htH)
  have hs' : IsSimpleGroup ↥(fixSub (MulAut.conjNormal t : MulAut ↥H)) := hsimple
  have hmodel' : LieModel ↥(fixSub (MulAut.conjNormal t : MulAut ↥H)) .trialityD4 0 p e' := hmodel
  have hQ := qShapeNS_of_descent hs _ le_rfl (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hs'
  exact not_qShapeNS_of_D4 hp hp2 he' hmodel' hs' hQ

theorem g2out_of_descent_simple (h : G2OuterFixedSimple) (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) : PumpupEmptyOut (fun X _ => LieModel X .G2 0 p f) := by
  intro N _ _ H t L hs htH hH
  have := hs.normal
  obtain ⟨L0, hL0, -, hcomm, hsimple, e', he', hmodel⟩ :=
    h hp hp2 hp3 hf hH (MulAut.conjNormal t : MulAut ↥H) (conjNormal_sq hs.inv)
      (conjNormal_not_inner hs.faithful htH)
  exact not_qShapeNS_of_G2 hp hp2 hp3 he' hmodel hsimple
    (qShapeNS_of_descent hs L0 hL0 hcomm hsimple)

theorem pumpupOpen_of_simple (hg2 : G2OuterFixedSimple) (hsp4 : Psp4OuterNoShape) : PumpupOpen where
  sp4out := fun p f hp hp2 hf => sp4out_of_noShape hsp4 p f hp hp2 hf
  g2out := fun p f hp hp2 hp3 hf => g2out_of_descent_simple hg2 p f hp hp2 hp3 hf
  d4out := fun p f hp hp2 hf => d4out_of_descent p f hp hp2 hf

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

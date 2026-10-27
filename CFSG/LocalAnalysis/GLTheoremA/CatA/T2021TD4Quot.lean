module

public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open scoped commutatorElement

section Central

variable {Q : Type} [Group Q]

theorem t2021TD4_commutatorElement_mul_central {x y z w : Q} (hz : z ∈ Subgroup.center Q)
    (hw : w ∈ Subgroup.center Q) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have hz' : ∀ g : Q, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 hz g).symm
  have hw' : ∀ g : Q, w * g = g * w := fun g => (Subgroup.mem_center_iff.1 hw g).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w * z⁻¹)) * x⁻¹ * w⁻¹ * y⁻¹ := by group
    _ = x * (y * w) * x⁻¹ * w⁻¹ * y⁻¹ := by rw [hz' (y * w * z⁻¹), inv_mul_cancel_right]
    _ = x * y * (w * (x⁻¹ * w⁻¹)) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hw' (x⁻¹ * w⁻¹), inv_mul_cancel_right]

theorem t2021TD4_commutator_le_fixSub {α : MulAut Q} {P : Subgroup Q}
    (h : ∀ x ∈ P, x⁻¹ * α x ∈ Subgroup.center Q) : ⁅P, P⁆ ≤ fixSub α := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  show α ⁅x, y⁆ = ⁅x, y⁆
  have key := t2021TD4_commutatorElement_mul_central (x := x) (y := y) (h x hx) (h y hy)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
  rw [map_commutatorElement]
  exact key

theorem t2021TD4_mem_center_of_fix {α : MulAut Q} {x : Q}
    (h : MulAut.mapQuotient (Subgroup.center Q) α (QuotientGroup.mk x) = QuotientGroup.mk x) :
    x⁻¹ * α x ∈ Subgroup.center Q := by
  rw [MulAut.mapQuotient_mk] at h
  exact QuotientGroup.eq.1 h.symm

theorem t2021TD4_commutator_le_self (H : Subgroup Q) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem t2021TD4_map_commutator_subtype (H : Subgroup Q) :
    (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem t2021TD4_subsingleton_sylow {V : Type*} [Group V] [Finite V] {N : Subgroup V}
    (hN : N ≤ Subgroup.center V) (h : ∀ P : Sylow 2 V, ∀ g : V, ∃ p ∈ (P : Subgroup V), p⁻¹ * g ∈ N) :
    Subsingleton (Sylow 2 V) := by
  refine ⟨fun P P' => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq V P P'
  rw [← hg]
  obtain ⟨p, hp, hpg⟩ := h P g
  have hcen : p⁻¹ * g ∈ Subgroup.center V := hN hpg
  have hgN : g ∈ Subgroup.normalizer ((P : Subgroup V) : Set V) := by
    have hg' : g = p * (p⁻¹ * g) := (mul_inv_cancel_left p g).symm
    rw [hg']
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hp) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [show p⁻¹ * g * y * (p⁻¹ * g)⁻¹ = y by
      rw [← Subgroup.mem_center_iff.1 hcen y]; group]
  exact (Sylow.smul_eq_iff_mem_normalizer.2 hgN).symm

end Central

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem t2021TD4_quot {𝔅 : Type} {p : ℕ} (hp : p.Prime) (ψQ : 𝔅 → MulAut Q) (b : 𝔅)
    (hZ : Odd (Nat.card (Subgroup.center Q))) {Kb Ub : Subgroup (Q ⧸ Subgroup.center Q)}
    (hKfix : Kb ≤ fixSub (MulAut.mapQuotient (Subgroup.center Q) (ψQ b)))
    (hKn : ∀ c ∈ fixSub (MulAut.mapQuotient (Subgroup.center Q) (ψQ b)), ∀ x ∈ Kb, c * x * c⁻¹ ∈ Kb)
    (hKinv : ∀ g : 𝔅, ∀ x ∈ Kb, MulAut.mapQuotient (Subgroup.center Q) (ψQ g) x ∈ Kb)
    (hKs : IsSimpleGroup ↥Kb) (hKnab : ¬ IsMulCommutative ↥Kb) (hK3 : p ∣ Nat.card ↥Kb)
    (hUK : Ub ≤ Kb) (hU2 : IsPGroup 2 Ub) (hU1 : Ub ≠ ⊥)
    (hUinv : ∀ g : 𝔅, ∀ u ∈ Ub, MulAut.mapQuotient (Subgroup.center Q) (ψQ g) u ∈ Ub) :
    ∃ K U : Subgroup Q, GLAPComponent p (fixSub (ψQ b)) K ∧ CFSG.Open.IsQuasisimple ↥K ∧
      Odd (Nat.card ↥(Subgroup.center ↥K)) ∧ p ∣ Nat.card ↥K ∧ U ≤ K ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∀ g : 𝔅, ∀ u ∈ U, ψQ g u ∈ U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center Q with hZdef
  set ρ : Q →* Q ⧸ Z := QuotientGroup.mk' Z with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective Z
  have hρker : ∀ x : Q, ρ x = 1 ↔ x ∈ Z := fun x => QuotientGroup.eq_one_iff x
  have hρψ : ∀ (g : 𝔅) (x : Q), ρ (ψQ g x) = MulAut.mapQuotient Z (ψQ g) (ρ x) := fun g x => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, MulAut.mapQuotient_mk]
  set P := Kb.comap ρ with hP
  set KQ := ⁅P, P⁆ with hKQ
  haveI := hKs
  have hPmap : P.map ρ = Kb := Subgroup.map_comap_eq_self_of_surjective hρs Kb
  have hKperf : ⁅Kb, Kb⁆ = Kb := by
    have htop := (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnab).commutator_eq_top
    rw [← t2021TD4_map_commutator_subtype, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKQmap : KQ.map ρ = Kb := by
    rw [hKQ, Subgroup.map_commutator, hPmap, hKperf]
  have hdecomp : ∀ p ∈ P, ∃ k ∈ KQ, k⁻¹ * p ∈ Z := by
    intro p hp
    have hp' : ρ p ∈ KQ.map ρ := by rw [hKQmap]; exact hp
    obtain ⟨k, hk, hkp⟩ := hp'
    exact ⟨k, hk, QuotientGroup.eq.1 hkp⟩
  have hKQP : KQ ≤ P := t2021TD4_commutator_le_self P
  have hKQperf : ⁅KQ, KQ⁆ = KQ := by
    refine le_antisymm (t2021TD4_commutator_le_self KQ) ?_
    conv_lhs => rw [hKQ]
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, hk, hkx⟩ := hdecomp x hx
    obtain ⟨k', hk', hky⟩ := hdecomp y hy
    have key := t2021TD4_commutatorElement_mul_central (x := k) (y := k') hkx hky
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
    rw [key]
    exact Subgroup.commutator_mem_commutator hk hk'
  have hφmem : ∀ k : ↥KQ, ρ (k : Q) ∈ Kb := fun k => by
    rw [← hKQmap]
    exact ⟨k, k.2, rfl⟩
  set φ : ↥KQ →* ↥Kb := (ρ.comp KQ.subtype).codRestrict Kb hφmem with hφ
  have hφs : Function.Surjective φ := by
    intro y
    have hy : (y : Q ⧸ Z) ∈ KQ.map ρ := by rw [hKQmap]; exact y.2
    obtain ⟨k, hk, hky⟩ := hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hφker : ∀ k : ↥KQ, φ k = 1 ↔ (k : Q) ∈ Z := by
    intro k
    rw [← hρker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcenKb : Subgroup.center ↥Kb = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnab
  have hkerc : φ.ker = Subgroup.center ↥KQ := by
    ext k
    rw [MonoidHom.mem_ker, hφker]
    constructor
    · intro hk
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hk) (g : Q))
    · intro hk
      have hc : φ k ∈ Subgroup.center ↥Kb := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ := hφs y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hk) g]
      rw [hcenKb, Subgroup.mem_bot] at hc
      exact (hφker k).1 hc
  have hcomm : commutator ↥KQ = ⊤ := by
    apply Subgroup.map_injective KQ.subtype_injective
    rw [t2021TD4_map_commutator_subtype, hKQperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eK : ↥KQ ⧸ Subgroup.center ↥KQ ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hQs : CFSG.Open.IsQuasisimple ↥KQ := ⟨hcomm, MulEquiv.isSimpleGroup eK⟩
  have hcenle : (Subgroup.center ↥KQ).map KQ.subtype ≤ Z := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ∈ φ.ker := by rw [hkerc]; exact hk
    exact (hφker k).1 (MonoidHom.mem_ker.1 hk')
  have hoddK : Odd (Nat.card ↥(Subgroup.center ↥KQ)) := by
    have h1 : Nat.card ↥((Subgroup.center ↥KQ).map KQ.subtype) = Nat.card ↥(Subgroup.center ↥KQ) :=
      Subgroup.card_map_of_injective KQ.subtype_injective
    rw [← h1]
    exact Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hcenle)
  have h3K : p ∣ Nat.card ↥KQ := hK3.trans (Subgroup.card_dvd_of_surjective hφs)
  have hPfix : ∀ x ∈ P, x⁻¹ * ψQ b x ∈ Z := by
    intro x hx
    apply t2021TD4_mem_center_of_fix
    exact hKfix hx
  have hKQC : KQ ≤ fixSub (ψQ b) := t2021TD4_commutator_le_fixSub hPfix
  have hconjP : ∀ c ∈ fixSub (ψQ b), P.map (MulAut.conj c).toMonoidHom ≤ P := by
    intro c hc
    rintro _ ⟨x, hx, rfl⟩
    have hcb : ρ c ∈ fixSub (MulAut.mapQuotient Z (ψQ b)) := by
      show MulAut.mapQuotient Z (ψQ b) (ρ c) = ρ c
      rw [← hρψ, show ψQ b c = c from hc]
    show ρ (c * x * c⁻¹) ∈ Kb
    rw [map_mul, map_mul, map_inv]
    exact hKn _ hcb _ hx
  have hKn' : (KQ.subgroupOf (fixSub (ψQ b))).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmap : KQ.map (MulAut.conj (c : Q)).toMonoidHom ≤ KQ := by
      rw [hKQ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono (hconjP c c.2) (hconjP c c.2)
    have : ((c : Q) * n * (c : Q)⁻¹) ∈ KQ.map (MulAut.conj (c : Q)).toMonoidHom := ⟨n, hn, rfl⟩
    simpa using hmap this
  have hcompK : GLAPComponent p (fixSub (ψQ b)) KQ :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hQs h3K hKQC hKn'
  have hPinv : ∀ g : 𝔅, ∀ x ∈ P, ψQ g x ∈ P := by
    intro g x hx
    show ρ (ψQ g x) ∈ Kb
    rw [hρψ]
    exact hKinv g _ hx
  have hKQinv : ∀ g : 𝔅, ∀ x ∈ KQ, ψQ g x ∈ KQ := by
    intro g x hx
    have hmap : KQ.map (ψQ g).toMonoidHom ≤ KQ := by
      rw [hKQ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono (fun _ ⟨y, hy, hyx⟩ => hyx ▸ hPinv g y hy)
        (fun _ ⟨y, hy, hyx⟩ => hyx ▸ hPinv g y hy)
    exact hmap ⟨x, hx, rfl⟩
  set V := KQ ⊓ Ub.comap ρ with hV
  have hVinv : ∀ g : 𝔅, ∀ x ∈ V, ψQ g x ∈ V := by
    intro g x hx
    refine ⟨hKQinv g x hx.1, ?_⟩
    show ρ (ψQ g x) ∈ Ub
    rw [hρψ]
    exact hUinv g _ hx.2
  have hVmap : V.map ρ = Ub := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro u hu
      have hu' : u ∈ KQ.map ρ := by rw [hKQmap]; exact hUK hu
      obtain ⟨k, hk, rfl⟩ := hu'
      exact ⟨k, ⟨hk, hu⟩, rfl⟩
  set N : Subgroup ↥V := Z.subgroupOf V with hN
  have hNc : N ≤ Subgroup.center ↥V := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hn) (g : Q))
  set φV : ↥V →* ↥Ub := (ρ.comp V.subtype).codRestrict Ub (fun v => v.2.2) with hφV
  have hφVs : Function.Surjective φV := by
    intro u
    have hu : (u : Q ⧸ Z) ∈ V.map ρ := by rw [hVmap]; exact u.2
    obtain ⟨v, hv, hvu⟩ := hu
    exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩
  have hsub : Subsingleton (Sylow 2 ↥V) := by
    refine t2021TD4_subsingleton_sylow hNc fun P₀ g => ?_
    have htop : ((P₀.mapSurjective hφVs : Sylow 2 ↥Ub) : Subgroup ↥Ub) = ⊤ :=
      ((P₀.mapSurjective hφVs).3 (IsPGroup.of_equiv hU2 Subgroup.topEquiv.symm) le_top).symm
    have hg : φV g ∈ ((P₀.mapSurjective hφVs : Sylow 2 ↥Ub) : Subgroup ↥Ub) := by
      rw [htop]; trivial
    rw [Sylow.coe_mapSurjective] at hg
    obtain ⟨p, hp, hpg⟩ := hg
    refine ⟨p, hp, ?_⟩
    rw [hN, Subgroup.mem_subgroupOf]
    have h1 : ρ ((p : Q)) = ρ (g : Q) := congrArg Subtype.val hpg
    have h2 := QuotientGroup.eq.1 h1
    simpa using h2
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 ↥V) := inferInstance
  haveI := hsub
  have hchar : (P₂ : Subgroup ↥V).Characteristic := Sylow.characteristic_of_subsingleton P₂
  set U := (P₂ : Subgroup ↥V).map V.subtype with hU
  refine ⟨KQ, U, hcompK, hQs, hoddK, h3K, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact v.2.1
  · exact P₂.2.map V.subtype
  ·
    intro hbot
    apply hU1
    have hmap : ((P₂.mapSurjective hφVs : Sylow 2 ↥Ub) : Subgroup ↥Ub) = ⊤ :=
      ((P₂.mapSurjective hφVs).3 (IsPGroup.of_equiv hU2 Subgroup.topEquiv.symm) le_top).symm
    rw [eq_bot_iff]
    intro u hu
    have hu' : (⟨u, hu⟩ : ↥Ub) ∈ ((P₂.mapSurjective hφVs : Sylow 2 ↥Ub) : Subgroup ↥Ub) := by
      rw [hmap]; trivial
    rw [Sylow.coe_mapSurjective] at hu'
    obtain ⟨p, hp, hpu⟩ := hu'
    have hpU : (p : Q) ∈ U := ⟨p, hp, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hpU
    have h1 : (u : Q ⧸ Z) = ρ (p : Q) := (congrArg Subtype.val hpu).symm
    rw [h1, hpU, map_one]
    exact Subgroup.one_mem _
  ·
    intro g u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hVeq : V.map (ψQ g).toMonoidHom = V := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨x, hx, rfl⟩
        exact hVinv g x hx
      · rw [Subgroup.card_map_of_injective (ψQ g).injective]
    let eV : ↥V ≃* ↥V := ((ψQ g).subgroupMap V).trans (MulEquiv.subgroupCongr hVeq)
    have heV : ∀ w : ↥V, ((eV w : ↥V) : Q) = ψQ g (w : Q) := fun w => rfl
    have hfix := (Subgroup.characteristic_iff_map_eq.1 hchar) eV
    have hmem : eV v ∈ (P₂ : Subgroup ↥V) := by
      rw [← hfix]
      exact ⟨v, hv, rfl⟩
    exact ⟨eV v, hmem, heV v⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T2021

end

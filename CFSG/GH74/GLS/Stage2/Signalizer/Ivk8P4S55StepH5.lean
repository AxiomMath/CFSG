module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH5Pair
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH5Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem OrdPInnerTypes.cases (h : OrdPInnerTypes) {r p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hrp : r ≠ p)
    (hY : FL3d r Y ∨ FU3d r Y ∨ FSp4d r Y ∨ FG2d r Y ∨ FD4d r Y ∨ FL4d r Y ∨ FU4d r Y ∨
      FReed r Y)
    (b : MulAut Y) (hb : orderOf b = p) :
    (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
      b ∈ (MulAut.conj : Y →* MulAut Y).range := by
  rcases hY with hT | hT | hT | hT | hT | hT | hT | hT
  · exact h.l3 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.u3 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.sp4 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.g2 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.d4 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.l4 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.u4 r p Y hr hr2 hp hp5 hrp hT b hb
  · exact h.ree r p Y hr hr2 hp hp5 hrp hT b hb

theorem Comp5Types.cases (h : Comp5Types) {r p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hrp : r ≠ p)
    (hY : FL3d r Y ∨ FU3d r Y ∨ FSp4d r Y ∨ FG2d r Y ∨ FD4d r Y ∨ FL4d r Y ∨ FU4d r Y ∨
      FReed r Y)
    (y g : Y) (hy : orderOf y = p)
    (hinv : ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥)
    (hpair : PairSL2 p y g) :
    ∃ L : Subgroup Y, L ≠ ⊤ ∧ IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧
      y ∈ normalizer (L : Set Y) ∧ ⁅L, zpowers y⁆ ≠ ⊥ := by
  rcases hY with hT | hT | hT | hT | hT | hT | hT | hT
  · exact h.l3 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.u3 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.sp4 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.g2 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.d4 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.l4 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.u4 r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair
  · exact h.ree r p Y hr hr2 hp hp5 hrp hT y g hy hinv hpair

section Main

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}

theorem Hyp89.exists_inner_of_ordPInner (hf : Hyp89 p ρ K a) (hE1 : CrossE1)
    (hO : OrdPInnerTypes) (hp5 : 5 ≤ p) {r : ℕ} (hr : OddChevHigh r (↥K ⧸ center ↥K))
    (hrp : r ≠ p) : ∃ y : ↥K ⧸ center ↥K, bAutN K a hf.norm = MulAut.conj y := by
  obtain ⟨hrpr, hr2, hT⟩ := hr
  have hY : OddChev r (↥K ⧸ center ↥K) := ⟨hrpr, hr2, Or.inr hT⟩
  rcases hO.cases hrpr hr2 hf.prime hp5 hrp hT _ hf.orderOf_bAutN with
    ⟨E, hE0, hEp, hEi⟩ | ⟨y, hy⟩
  · exact (hE0 (hf.eq_bot_of_crossE1 hE1 hY hrp E hEp hEi)).elim
  · exact ⟨y, hy.symm⟩

omit [Module.Finite (ZMod p) V] in
theorem Hyp89.cover (hf : Hyp89 p ρ K a) {y : ↥K ⧸ center ↥K}
    (hy : bAutN K a hf.norm = MulAut.conj y) {L : Subgroup (↥K ⧸ center ↥K)}
    (hLq : IsQuasisimple ↥L) (hLtop : L ≠ ⊤) (hyN : y ∈ normalizer (L : Set (↥K ⧸ center ↥K)))
    (hLc : ⁅L, zpowers y⁆ ≠ ⊥) :
    ∃ M : Subgroup Γ, Hyp89 p ρ M a ∧ Nat.card ↥M < Nat.card ↥K ∧
      Nonempty ((↥M ⧸ center ↥M) ≃* (↥L ⧸ center ↥L)) := by
  obtain ⟨M0, hM0n, hM0map, hM0q, ⟨eM⟩⟩ := exists_cover_quasisimple ↥K L hLq
  obtain ⟨yh, c, hyh, hcC, hac⟩ := hf.exists_inner_decomp hy
  obtain ⟨hMq, ⟨eM'⟩⟩ := quasisimple_map_subtype K M0 hM0q
  set M : Subgroup Γ := M0.map K.subtype with hM
  have hyhM : yh ∈ normalizer (M0 : Set ↥K) := hM0n yh (by rw [hyh]; exact hyN)
  have hyhM' : (yh : Γ) ∈ normalizer (M : Set Γ) := mem_normalizer_map_br K.subtype hyhM
  have hcM : c ∈ normalizer (M : Set Γ) := by
    refine Subgroup.centralizer_le_normalizer (M : Set Γ) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ M0.map K.subtype := hx
    obtain ⟨m, -, rfl⟩ := hx'
    exact Subgroup.mem_centralizer_iff.mp hcC m m.2
  have haM : a ∈ normalizer (M : Set Γ) := by
    rw [hac]
    exact (normalizer (M : Set Γ)).mul_mem hyhM' hcM
  have hacts : ⁅M, zpowers a⁆ ≠ ⊥ := by
    intro hbot
    apply hLc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot ⊢
    intro l hl
    rw [← hM0map] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hmM : (m : Γ) ∈ M := ⟨m, hm, rfl⟩
    have h1 : a * (m : Γ) = (m : Γ) * a :=
      Subgroup.mem_centralizer_iff.mp (hbot hmM) a (Subgroup.mem_zpowers a)
    rw [hac] at h1
    have hcm : c * (m : Γ) = (m : Γ) * c := (Subgroup.mem_centralizer_iff.mp hcC m m.2).symm
    have h2 : (yh : Γ) * (m : Γ) = (m : Γ) * (yh : Γ) := by
      have h3 : ((yh : Γ) * (m : Γ)) * c = ((m : Γ) * (yh : Γ)) * c :=
        calc ((yh : Γ) * (m : Γ)) * c = (yh : Γ) * ((m : Γ) * c) := by group
          _ = (yh : Γ) * (c * (m : Γ)) := by rw [hcm]
          _ = ((yh : Γ) * c) * (m : Γ) := by group
          _ = (m : Γ) * ((yh : Γ) * c) := h1
          _ = ((m : Γ) * (yh : Γ)) * c := by group
      exact mul_right_cancel h3
    have hcomm : Commute m (yh ^ n) := by
      have hc1 : Commute m yh := Subtype.ext h2.symm
      exact hc1.zpow_right n
    rw [← hyh]
    have h4 : (QuotientGroup.mk (yh ^ n * m) : ↥K ⧸ center ↥K) =
        QuotientGroup.mk (m * yh ^ n) := by rw [hcomm.eq]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h4
    exact h4
  have hcard : Nat.card ↥M < Nat.card ↥K := by
    have hlt : M0 < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hLtop ?_
      rw [← hM0map, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have h1 : Nat.card ↥M0 < Nat.card ↥(⊤ : Subgroup ↥K) := Subgroup.card_lt_of_lt hlt
    rw [Subgroup.card_top] at h1
    have h2 : Nat.card ↥M = Nat.card ↥M0 :=
      (Nat.card_congr (M0.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm
    rwa [h2]
  exact ⟨M, ⟨hf.prime, hf.odd, hf.faithful, haM, hMq, hf.quad, hacts⟩, hcard, ⟨eM'.trans eM⟩⟩

end Main

theorem stepH5_of (hE1 : CrossE1) (hE2 : CrossE2) (hO : OrdPInnerTypes) (hC : Comp5Types) :
    StepH5 := by
  intro p Γ _ _ V _ _ _ ρ K a hf hIH hp5 r hr hrp
  obtain ⟨y, hy⟩ := hf.exists_inner_of_ordPInner hE1 hO hp5 hr hrp
  obtain ⟨g, hg⟩ := hf.exists_pairSL2 hE2 hy
  obtain ⟨hrpr, hr2, hT⟩ := hr
  have hY : OddChev r (↥K ⧸ center ↥K) := ⟨hrpr, hr2, Or.inr hT⟩
  have hZ : center (↥K ⧸ center ↥K) = ⊥ := center_quot_eq_bot hf.quasi
  have hcen : ∀ z : ↥K ⧸ center ↥K, (∀ x, z * x = x * z) → z = 1 := by
    intro z hz
    have hz' : z ∈ center (↥K ⧸ center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [hZ] at hz'
    exact hz'
  have hyord : orderOf y = p := by
    have h1 := hf.orderOf_bAutN
    rw [hy] at h1
    rwa [orderOf_injective (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K))
      (conj_inj_of_centerless hcen) y] at h1
  have hinv : ∀ E : Subgroup (↥K ⧸ center ↥K), IsPGroup r ↥E →
      (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥ := by
    intro E hE hE'
    refine hf.eq_bot_of_crossE1 hE1 hY hrp E hE fun x hx => ?_
    rw [hy, MulAut.conj_apply]
    exact hE' x hx
  obtain ⟨L, hLtop, hLq, hLodd, hLn, hLc⟩ :=
    hC.cases hrpr hr2 hf.prime hp5 hrp hT y g hyord hinv hg
  obtain ⟨M, hfM, hcard, ⟨eM⟩⟩ := hf.cover hy hLq hLtop hLn hLc
  have hodd' : OddChev r (↥M ⧸ center ↥M) := OddChev.of_mulEquiv eM.symm hLodd
  rcases hIH p Γ V ρ M a hfM hcard r hodd' with h | ⟨h3, -⟩
  · exact hrp h
  · omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

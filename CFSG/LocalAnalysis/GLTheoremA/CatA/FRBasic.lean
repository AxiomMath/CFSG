module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

theorem normal_subgroupOf_of_commutator_le {G : Type*} [Group G] (T D : Subgroup G)
    (h : ⁅T, T⁆ ≤ D) : (D.subgroupOf T).Normal := by
  refine ⟨fun n hn t => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : ⁅(t : G), (n : G)⁆ ∈ D := h (Subgroup.commutator_mem_commutator t.2 n.2)
  have h2 : ((t * n * t⁻¹ : T) : G) = ⁅(t : G), (n : G)⁆ * (n : G) := by
    simp [commutatorElement_def]
  rw [h2]
  exact D.mul_mem h1 hn

section Core

variable {H : Type*} [Group H] [Finite H]

theorem subfield_core (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZ : Odd (Nat.card Z)) (ρ : MulAut H) (f : MulAut (H ⧸ Z))
    (hmk : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ x)) :
    (FP.fixSub ρ).map (QuotientGroup.mk' Z) ≤ FP.fixSub f ∧
      ⁅FP.fixSub f, FP.fixSub f⁆ ≤ (FP.fixSub ρ).map (QuotientGroup.mk' Z) ∧
      Odd (((FP.fixSub ρ).map (QuotientGroup.mk' Z)).relIndex (FP.fixSub f)) := by
  set π : H →* H ⧸ Z := QuotientGroup.mk' Z with hπ
  set C : Subgroup H := FP.fixSub ρ with hC
  set D : Subgroup (H ⧸ Z) := C.map π with hD
  set T : Subgroup (H ⧸ Z) := FP.fixSub f with hT
  have hDT : D ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ρ x = x := FP.mem_fixSub.1 hx
    show f (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [hmk, hx']
  set Tt : Subgroup H := T.comap π with hTt
  have hmem : ∀ x : H, x ∈ Tt ↔ (ρ x)⁻¹ * x ∈ Z := by
    intro x
    change f (QuotientGroup.mk x) = QuotientGroup.mk x ↔ _
    rw [hmk, QuotientGroup.eq]
  let δ : Tt →* Z := MonoidHom.mk' (fun x => ⟨(ρ x.1)⁻¹ * x.1, (hmem x.1).1 x.2⟩) (by
    intro x y
    apply Subtype.ext
    have hz : (ρ x.1)⁻¹ * x.1 ∈ Subgroup.center H := hZc ((hmem x.1).1 x.2)
    have hc' := Subgroup.mem_center_iff.1 hz
    show (ρ (x.1 * y.1))⁻¹ * (x.1 * y.1) = (ρ x.1)⁻¹ * x.1 * ((ρ y.1)⁻¹ * y.1)
    rw [map_mul, mul_inv_rev]
    calc (ρ y.1)⁻¹ * (ρ x.1)⁻¹ * (x.1 * y.1)
        = (ρ y.1)⁻¹ * ((ρ x.1)⁻¹ * x.1) * y.1 := by group
      _ = ((ρ x.1)⁻¹ * x.1) * (ρ y.1)⁻¹ * y.1 := by rw [hc' ((ρ y.1)⁻¹)]
      _ = _ := by group)
  have hδker : ∀ x : Tt, δ x = 1 → ρ x.1 = x.1 := by
    intro x hx
    have h1 : (ρ x.1)⁻¹ * x.1 = 1 := congrArg Subtype.val hx
    exact inv_mul_eq_one.1 h1
  have hker_δ : ∀ x : Tt, ρ x.1 = x.1 → δ x = 1 := by
    intro x hx
    apply Subtype.ext
    show (ρ x.1)⁻¹ * x.1 = 1
    rw [hx]; group
  have hcomm : ⁅T, T⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Tt := ha
    have hy : y ∈ Tt := hb
    refine ⟨⁅x, y⁆, ?_, ?_⟩
    · have h1 : δ ⁅(⟨x, hx⟩ : Tt), ⟨y, hy⟩⁆ = 1 := by
        rw [map_commutatorElement]
        apply commutatorElement_eq_one_iff_mul_comm.2
        exact Subtype.ext ((Subgroup.mem_center_iff.1 (hZc (δ ⟨x, hx⟩).2) _).symm)
      exact hδker _ h1
    · simp [hπ, commutatorElement_def]
  have hN : (D.subgroupOf T).Normal := normal_subgroupOf_of_commutator_le T D hcomm
  refine ⟨hDT, hcomm, ?_⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  let q : Tt →* T := π.subgroupComap T
  have hq : Function.Surjective q := MonoidHom.subgroupComap_surjective π T
    (QuotientGroup.mk'_surjective Z)
  let r : Tt →* T ⧸ D.subgroupOf T := (QuotientGroup.mk' (D.subgroupOf T)).comp q
  have hr : Function.Surjective r := (QuotientGroup.mk'_surjective _).comp hq
  have hrk : δ.ker ≤ r.ker := by
    intro x hx
    have hx' : ρ x.1 = x.1 := hδker x (MonoidHom.mem_ker.1 hx)
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (D.subgroupOf T) (q x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨x.1, hx', rfl⟩
  let r' : Tt ⧸ δ.ker →* T ⧸ D.subgroupOf T := QuotientGroup.lift δ.ker r hrk
  have hr' : Function.Surjective r' := by
    intro y
    obtain ⟨x, rfl⟩ := hr y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have h1 : Nat.card (T ⧸ D.subgroupOf T) ∣ Nat.card (Tt ⧸ δ.ker) :=
    Subgroup.card_dvd_of_surjective hr'
  have h2 : Nat.card (Tt ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have h3 : Nat.card δ.range ∣ Nat.card Z := Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat hZ (h1.trans (h2 ▸ h3))


theorem equiv_of_map_mk {H' : Type*} [Group H'] (Z : Subgroup H) [Z.Normal] (C : Subgroup H)
    (Zk : Subgroup H') [Zk.Normal] (e : H' ≃* C) (he : ∀ x : H', x ∈ Zk ↔ ((e x : C) : H) ∈ Z) :
    Nonempty (C.map (QuotientGroup.mk' Z) ≃* H' ⧸ Zk) := by
  let g : C →* H ⧸ Z := (QuotientGroup.mk' Z).comp C.subtype
  have hker : g.ker = Z.subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hrange : g.range = C.map (QuotientGroup.mk' Z) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hZk : Zk.map e.toMonoidHom = Z.subgroupOf C := by
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (he x).1 hx
    · intro hy
      refine ⟨e.symm y, (he _).2 (by simpa using hy), by simp⟩
  have e1 : H' ⧸ Zk ≃* C ⧸ Z.subgroupOf C := QuotientGroup.congr Zk _ e hZk
  have e2 : C ⧸ Z.subgroupOf C ≃* g.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange g)
  exact ⟨((e1.trans e2).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end Core

section Fix

theorem fixSub_pow_eq {R : Type*} [Group R] {f : MulAut R} {p n : ℕ} (hp : p.Prime)
    (hord : orderOf f = p) (hn : ¬ p ∣ n) : FP.fixSub (f ^ n) = FP.fixSub f := by
  have hcop : (orderOf f).Coprime n := by
    rw [hord]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn
  have hord' : orderOf (f ^ n) = p := by rw [Nat.Coprime.orderOf_pow hcop, hord]
  have h1 : f ^ n ∈ Subgroup.zpowers f := Subgroup.pow_mem _ (Subgroup.mem_zpowers f) n
  have h2 : f ∈ Subgroup.zpowers (f ^ n) :=
    FP.mem_zpowers_of_orderOf_eq hp.pos (f₀ := f) h1 (Subgroup.mem_zpowers f) hord' hord
  ext x
  rw [FP.mem_fixSub, FP.mem_fixSub]
  exact ⟨fun h => FP.fix_of_mem_zpowers h2 h, fun h => FP.fix_of_mem_zpowers h1 h⟩

end Fix

section FixEquiv

noncomputable def fixSubEquiv {R S : Type*} [Group R] [Group S] (φ : R ≃* S) (f : MulAut R)
    (g : MulAut S) (h : ∀ x, φ (f x) = g (φ x)) : ↥(FP.fixSub f) ≃* ↥(FP.fixSub g) where
  toFun x := ⟨φ x, FP.mem_fixSub.2 (by rw [← h, FP.mem_fixSub.1 x.2])⟩
  invFun y := ⟨φ.symm y, FP.mem_fixSub.2 (φ.injective (by
    rw [h, MulEquiv.apply_symm_apply, FP.mem_fixSub.1 y.2]))⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv y := Subtype.ext (φ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul φ _ _)

noncomputable def fixSubEquivCongr {R S : Type*} [Group R] [Group S] (e : R ≃* S) (f : MulAut R) :
    ↥(FP.fixSub f) ≃* ↥(FP.fixSub (MulAut.congr e f)) :=
  fixSubEquiv e f _ fun x => by simp [MulAut.congr_apply]

noncomputable def fixSubEquivConj {R : Type*} [Group R] (u f : MulAut R) :
    ↥(FP.fixSub f) ≃* ↥(FP.fixSub (u * f * u⁻¹)) :=
  fixSubEquiv (u : R ≃* R) f _ fun x => by simp

end FixEquiv

section Sigma

variable {K : Type} [Field K] {H : Type} [Group H] [Finite H]

theorem sigma_order {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z))
    (ρ : (K ≃+* K) →* MulAut H) (good : (K ≃+* K) → Prop)
    (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n)) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hC : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (FP.fixNum (ρ σ)) ^ v = 2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (f : MulAut (H ⧸ Z)) (σ : K ≃+* K)
    (hσf : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ σ x)) (hord : orderOf f = p) :
    ∃ n : ℕ, ¬ p ∣ n ∧ orderOf (σ ^ n) = p ∧ good (σ ^ n) ∧
      ∀ x : H, (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk (ρ (σ ^ n) x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ n : ℕ, ∀ x : H, (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((ρ (σ ^ n)) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hσf, ih, pow_succ, map_mul, MulAut.mul_apply]
  obtain ⟨n, hn, hgn⟩ := hred σ
  have hcop : (orderOf f).Coprime n := by
    rw [hord]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn
  have hord' : orderOf (f ^ n) = p := by rw [Nat.Coprime.orderOf_pow hcop, hord]
  have hσf' := hpow n
  refine ⟨n, hn, ?_, hgn, hσf'⟩
  set σ' : K ≃+* K := σ ^ n with hσ'
  set f' : MulAut (H ⧸ Z) := f ^ n with hf'
  have hHZ : (twoPart (Nat.card (H ⧸ Z))) ^ v = 2 ^ (m * u) := by
    rw [twoPart_card_quotient Z hZ]; exact hH
  have hfp : f' ^ p = 1 := hord' ▸ pow_orderOf_eq_one f'
  have hσp : σ' ^ p = 1 := by
    have h1 := FQ.twoPart_fixNum_quotient Z hZc hZ (ρ (σ' ^ p)) (f' ^ p) (by
      intro x
      have := hpow (n * p) x
      rw [pow_mul f n p, pow_mul σ n p] at this
      exact this)
    rw [hfp, FQ.fixNum_one] at h1
    obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK (σ' ^ p)
    have h2 := hC (σ' ^ p) (hgood σ' hgn p) _ hcard
    rw [← h1, hHZ] at h2
    have h3 : m * u = (m / orderOf (σ' ^ p)) * u := by
      have := Nat.pow_right_injective (le_refl 2) h2
      exact this
    have h4 : m = m / orderOf (σ' ^ p) := Nat.eq_of_mul_eq_mul_right hu h3
    have hpos : 0 < orderOf (σ' ^ p) := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have h5 : orderOf (σ' ^ p) = 1 := by
      by_contra hne
      have h6 : 2 ≤ orderOf (σ' ^ p) := by omega
      have h7 : m / orderOf (σ' ^ p) < m := Nat.div_lt_self (by omega) h6
      omega
    exact orderOf_eq_one_iff.1 h5
  have hσ1 : σ' ≠ 1 := by
    intro h
    have : f' = 1 := by
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hσf', h]
      simp
    rw [this, orderOf_one] at hord'
    exact hp.one_lt.ne hord'
  exact orderOf_eq_prime hσp hσ1

end Sigma

end FR

end CFSG.LocalAnalysis.GLTheoremA

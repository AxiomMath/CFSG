module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Gen
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GH74.GLS.Stage1.Thm4.Pure
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG

section K0

variable {X : Type} [Group X] [Finite X] (x : X) [CentralInv x]

@[expose] noncomputable def K0 (Lc : Subgroup (Qh x)) : Subgroup X :=
  (perfectResidual ↥(Lc.comap (piH x))).map (Lc.comap (piH x)).subtype

variable {x} {Lc : Subgroup (Qh x)}

omit [Finite X] in
theorem K0_le_comap : K0 x Lc ≤ Lc.comap (piH x) :=
  Subgroup.map_subtype_le _

instance K0_normal [Lc.Normal] : (K0 x Lc).Normal := by
  have : (Lc.comap (piH x)).Normal := inferInstance
  unfold K0
  exact ConjAct.normal_of_characteristic_of_normal

theorem K0_perfect : Group.IsPerfect ↥(K0 x Lc) := by
  have : Group.IsPerfect (perfectResidual ↥(Lc.comap (piH x))) :=
    (perfect_residual_characterization (G := ↥(Lc.comap (piH x)))).2.2.1
  unfold K0
  exact Group.IsPerfect.map _

theorem K0_le_commutator : K0 x Lc ≤ commutator X := by
  have h : ⁅K0 x Lc, K0 x Lc⁆ = K0 x Lc := Subgroup.isPerfect_iff.1 (K0_perfect (x := x) (Lc := Lc))
  calc K0 x Lc = ⁅K0 x Lc, K0 x Lc⁆ := h.symm
    _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := Subgroup.commutator_mono le_top le_top

theorem derivedSeries_top_of_perfect {A : Type*} [Group A] [Group.IsPerfect A] (n : ℕ) :
    derivedSeries A n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero A
  | succ n ih => rw [derivedSeries_succ, ih]; exact Group.IsPerfect.commutator_eq_top

theorem K0_map [Group.IsPerfect ↥Lc] : (K0 x Lc).map (piH x) = Lc := by
  let N : Subgroup X := Lc.comap (piH x)
  let f : ↥N →* ↥Lc := ((piH x).comp N.subtype).codRestrict Lc (fun n => n.2)
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨g, hg⟩ := piH_surjective x l.1
    exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact l.2⟩, Subtype.ext hg⟩
  obtain ⟨n₁, hn₁, -⟩ := exists_perfectResidual_eq_derivedSeries (G := ↥N)
  have h1 : (perfectResidual ↥N).map f = ⊤ := by
    rw [hn₁, map_derivedSeries_eq hf, derivedSeries_top_of_perfect]
  have hcomp : (piH x).comp N.subtype = Lc.subtype.comp f := by ext g; rfl
  show ((perfectResidual ↥N).map N.subtype).map (piH x) = Lc
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h1, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite X] in
theorem odd_orderOf_of_mem_O {o : X} (ho : o ∈ pPrimeCore 2 X) [Finite X] : Odd (orderOf o) := by
  have hd : orderOf o ∣ Nat.card (pPrimeCore 2 X) := by
    have := orderOf_dvd_natCard (⟨o, ho⟩ : pPrimeCore 2 X)
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat (odd_card_pPrimeCore X) hd

theorem ker_inf_le {K₀ : Subgroup X} (hxK : x ∉ K₀) : K₀ ⊓ (piH x).ker ≤ pPrimeCore 2 X := by
  rintro k ⟨hk, hker⟩
  rw [ker_piH] at hker
  obtain ⟨o, ho, s, hs, hos⟩ := Subgroup.mem_sup_of_normal_left.1 hker
  rcases CentralInv.mem_zpowers hs with hs1 | hs1
  · rw [hs1, mul_one] at hos
    rw [← hos]; exact ho
  · exfalso
    rw [hs1] at hos
    obtain ⟨j, hj⟩ := odd_orderOf_of_mem_O ho
    have hcx : Commute o x := (CentralInv.comm (x := x) o)
    have hkm : k ^ orderOf o = x := by
      rw [← hos, hcx.mul_pow, pow_orderOf_eq_one, one_mul, hj, pow_succ, pow_mul,
        pow_two, CentralInv.sq (x := x), one_pow, one_mul]
    exact hxK (hkm ▸ K₀.pow_mem hk _)

theorem pPrimeCore_map_normal (K₀ : Subgroup X) [K₀.Normal] :
    (pPrimeCore 2 ↥K₀).map K₀.subtype = pPrimeCore 2 X ⊓ K₀ := by
  apply le_antisymm
  · have hn : ((pPrimeCore 2 ↥K₀).map K₀.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    refine le_inf ?_ (Subgroup.map_subtype_le _)
    refine le_sSup ⟨hn, ?_⟩
    rw [Subgroup.card_map_of_injective K₀.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥K₀)
  · rintro g ⟨hgO, hgK⟩
    have hn : ((pPrimeCore 2 X ⊓ K₀).subgroupOf K₀).Normal :=
      Subgroup.Normal.subgroupOf inferInstance K₀
    have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 X ⊓ K₀).subgroupOf K₀)) := by
      refine Nat.Coprime.coprime_dvd_right ?_ (pPrimeCore_coprime_card (p := 2) (G := X))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : pPrimeCore 2 X ⊓ K₀ ≤ K₀)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hle : (pPrimeCore 2 X ⊓ K₀).subgroupOf K₀ ≤ pPrimeCore 2 ↥K₀ := le_sSup ⟨hn, hcop⟩
    have hmem : (⟨g, hgK⟩ : ↥K₀) ∈ (pPrimeCore 2 X ⊓ K₀).subgroupOf K₀ := ⟨hgO, hgK⟩
    exact ⟨⟨g, hgK⟩, hle hmem, rfl⟩

theorem two_elt_K0 [Lc.Normal] [Group.IsPerfect ↥Lc] {g : X} (hg : g ∈ Lc.comap (piH x)) {m : ℕ}
    (hgm : g ^ (2 ^ m) = 1) : g ∈ K0 x Lc ∨ g * x ∈ K0 x Lc := by
  have hπ : piH x g ∈ (K0 x Lc).map (piH x) := by rw [K0_map]; exact hg
  obtain ⟨k, hk, hkg⟩ := hπ
  have hker : k⁻¹ * g ∈ (piH x).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  rw [ker_piH] at hker
  obtain ⟨o, ho, s, hs, hos⟩ := Subgroup.mem_sup_of_normal_left.1 hker
  have hg' : g = k * (o * s) := by rw [hos]; group
  rcases CentralInv.mem_zpowers hs with hs1 | hs1
  · left
    rw [hs1, mul_one] at hg'
    exact Stage1.Thm4.mem_of_mem_sup_odd (odd_card_pPrimeCore X) hgm
      (hg' ▸ Subgroup.mul_mem_sup hk ho)
  · right
    rw [hs1] at hg'
    have hgx : g * x = k * o := by
      rw [hg']
      calc k * (o * x) * x = k * o * (x * x) := by group
        _ = k * o := by rw [CentralInv.sq (x := x), mul_one]
    have hcx : Commute g x := (CentralInv.comm (x := x) g)
    have hxx : x ^ (2 ^ (m + 1)) = 1 := by
      rw [pow_succ', pow_mul, pow_two, CentralInv.sq (x := x), one_pow]
    have hg2 : (g * x) ^ (2 ^ (m + 1)) = 1 := by
      rw [hcx.mul_pow, hxx, mul_one, pow_succ, pow_mul, hgm, one_pow]
    exact Stage1.Thm4.mem_of_mem_sup_odd (odd_card_pPrimeCore X) hg2
      (hgx ▸ Subgroup.mul_mem_sup hk ho)

omit [Finite X] in
theorem isSolvable_of_odd_card {A : Type*} [Group A] [Finite A] (h : Odd (Nat.card A)) :
    Group.IsSolvable A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ h

theorem le_of_subnormal {K : Subgroup X} (hKp : Group.IsPerfect ↥K) {J : Subgroup X}
    (hJ : J.IsSubnormal) (hK : K ≤ J ⊔ pPrimeCore 2 X) : K ≤ J := by
  induction hJ with
  | top => exact le_top
  | step H K' hHK' hK'sub hHn ih =>
    have hKK' : K ≤ K' := ih (hK.trans (sup_le_sup_right hHK' _))
    set H' : Subgroup ↥K' := H.subgroupOf K' with hH'
    have : H'.Normal := hHn
    let ρ' : ↥K' →* ↥K' ⧸ H' := QuotientGroup.mk' H'
    let φ : ↥K →* ↥K' ⧸ H' := ρ'.comp (Subgroup.inclusion hKK')
    let A : Subgroup ↥K' := (pPrimeCore 2 X).subgroupOf K'
    let ψ : ↥A →* ↥K' ⧸ H' := ρ'.comp A.subtype
    have hle : φ.range ≤ ψ.range := by
      rintro _ ⟨k, rfl⟩
      obtain ⟨h, hh, o, ho, hk⟩ := Subgroup.mem_sup_of_normal_right.1 (hK k.2)
      have hoK' : o ∈ K' := by
        have : o = h⁻¹ * k := by rw [← hk]; group
        rw [this]; exact K'.mul_mem (K'.inv_mem (hHK' hh)) (hKK' k.2)
      refine ⟨⟨⟨o, hoK'⟩, ho⟩, ?_⟩
      show ρ' ⟨o, hoK'⟩ = ρ' ⟨k, hKK' k.2⟩
      have : (⟨k, hKK' k.2⟩ : ↥K') = ⟨h, hHK' hh⟩ * ⟨o, hoK'⟩ := Subtype.ext hk.symm
      rw [this, map_mul]
      have h1 : ρ' ⟨h, hHK' hh⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hh
      rw [h1, one_mul]
    have hoddA : Odd (Nat.card ψ.range) := by
      have h1 : Nat.card ψ.range ∣ Nat.card A := Subgroup.card_range_dvd ψ
      have h2 : Nat.card A ∣ Nat.card (pPrimeCore 2 X) := by
        let ι : ↥A →* ↥(pPrimeCore 2 X) :=
          ((K'.subtype).comp A.subtype).codRestrict (pPrimeCore 2 X) (fun a => a.2)
        refine Subgroup.card_dvd_of_injective ι fun a b hab => ?_
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this)
      exact Odd.of_dvd_nat (odd_card_pPrimeCore X) (h1.trans h2)
    have hsolv : Group.IsSolvable ↥ψ.range := isSolvable_of_odd_card hoddA
    have hsolv2 : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have hperf : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    have hsub : Subsingleton ↥φ.range := by
      by_contra hns
      have : Nontrivial ↥φ.range := not_subsingleton_iff_nontrivial.1 hns
      have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥φ.range
      rw [Group.IsPerfect.commutator_eq_top] at h1
      exact lt_irrefl _ h1
    intro k hk
    have h1 : φ ⟨k, hk⟩ = 1 := by
      have : (⟨φ ⟨k, hk⟩, ⟨_, rfl⟩⟩ : ↥φ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val this
    have h2 : (⟨k, hKK' hk⟩ : ↥K') ∈ H' := (QuotientGroup.eq_one_iff _).1 h1
    exact h2

omit [Finite X] in
theorem K0_surj [Finite X] [Lc.Normal] [Group.IsPerfect ↥Lc] :
    Function.Surjective (((piH x).comp (K0 x Lc).subtype).codRestrict Lc
      (fun k => K0_le_comap k.2)) := by
  intro l
  have : l.1 ∈ (K0 x Lc).map (piH x) := by rw [K0_map]; exact l.2
  obtain ⟨k, hk, hkl⟩ := this
  exact ⟨⟨k, hk⟩, Subtype.ext hkl⟩

theorem K0_ker [Lc.Normal] [Group.IsPerfect ↥Lc] (hxK : x ∉ K0 x Lc) :
    (((piH x).comp (K0 x Lc).subtype).codRestrict Lc (fun k => K0_le_comap k.2)).ker =
      pPrimeCore 2 ↥(K0 x Lc) := by
  have hmap := pPrimeCore_map_normal (K0 x Lc)
  ext k
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hk
    have h1 : piH x (k : X) = 1 := congrArg Subtype.val hk
    have h2 : (k : X) ∈ pPrimeCore 2 X ⊓ K0 x Lc :=
      ⟨ker_inf_le hxK ⟨k.2, h1⟩, k.2⟩
    rw [← hmap] at h2
    obtain ⟨k', hk', hkk⟩ := h2
    have : k' = k := Subtype.ext hkk
    rw [← this]; exact hk'
  · intro hk
    have h2 : (k : X) ∈ pPrimeCore 2 X ⊓ K0 x Lc := by
      rw [← hmap]; exact ⟨k, hk, rfl⟩
    have h3 : (k : X) ∈ (piH x).ker := by
      rw [ker_piH]; exact Subgroup.mem_sup_left h2.1
    exact Subtype.ext h3

theorem K0_quot [Lc.Normal] [Group.IsPerfect ↥Lc] (hxK : x ∉ K0 x Lc) :
    Nonempty (↥(K0 x Lc) ⧸ pPrimeCore 2 ↥(K0 x Lc) ≃* ↥Lc) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (K0_ker hxK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ K0_surj)⟩

omit [Finite X] in
theorem isQuasisimple_of_equiv {A S : Type} [Group A] [Group S] (e : A ≃* S) [IsSimpleGroup S]
    (hS : Group.IsPerfect S) : CFSG.IsQuasisimple A := by
  have hA : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hAs : IsSimpleGroup A := (MulEquiv.isSimpleGroup_congr e).2 inferInstance
  have hcen : center A = ⊥ := by
    rcases hAs.eq_bot_or_eq_top_of_normal (center A) with h | h
    · exact h
    · exfalso
      exact Group.IsPerfect.not_isMulCommutative A (Subgroup.center_eq_top_iff.mp h)
  let eq1 : A ⧸ center A ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hq : IsSimpleGroup (A ⧸ center A) := (MulEquiv.isSimpleGroup_congr eq1).2 hAs
  refine ⟨hA, hq, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative (A ⧸ center A) := ⟨⟨fun a b => hcon a b⟩⟩
  have : Group.IsPerfect (A ⧸ center A) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative (A ⧸ center A) hcomm

theorem K0_isPComponent [Lc.Normal] [Group.IsPerfect ↥Lc] [IsSimpleGroup ↥Lc] (hxK : x ∉ K0 x Lc) :
    IsPComponent 2 (K0 x Lc) := by
  set O := pPrimeCore 2 X with hO
  set Kt := (K0 x Lc).map (QuotientGroup.mk' O) with hKt
  have hmap := pPrimeCore_map_normal (K0 x Lc)
  let θ : ↥(K0 x Lc) →* ↥Kt := (QuotientGroup.mk' O).subgroupMap (K0 x Lc)
  have hθ : Function.Surjective θ := (QuotientGroup.mk' O).subgroupMap_surjective _
  have hθker : θ.ker = pPrimeCore 2 ↥(K0 x Lc) := by
    ext k
    simp only [MonoidHom.mem_ker]
    have : θ k = 1 ↔ (QuotientGroup.mk' O) (k : X) = 1 := by
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hk
      have h2 : (k : X) ∈ pPrimeCore 2 X ⊓ K0 x Lc := ⟨hk, k.2⟩
      rw [← hmap] at h2
      obtain ⟨k', hk', hkk⟩ := h2
      have : k' = k := Subtype.ext hkk
      rw [← this]; exact hk'
    · intro hk
      have h2 : (k : X) ∈ pPrimeCore 2 X ⊓ K0 x Lc := by
        rw [← hmap]; exact ⟨k, hk, rfl⟩
      exact h2.1
  obtain ⟨eQ⟩ := K0_quot (x := x) (Lc := Lc) hxK
  let eK : ↥Kt ≃* ↥Lc :=
    ((QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hθker)).trans eQ
  have hqs : CFSG.IsQuasisimple ↥Kt := isQuasisimple_of_equiv eK inferInstance
  refine ⟨Kt, ⟨hqs, ?_⟩, (K0_normal (x := x) (Lc := Lc)).isSubnormal, rfl, ?_⟩
  · exact ((K0_normal (x := x) (Lc := Lc)).map _ (QuotientGroup.mk'_surjective O)).isSubnormal
  · intro J hJlt hJsub hJmap
    have hKJ : K0 x Lc ≤ J ⊔ O := by
      have h1 : K0 x Lc ≤ (Kt).comap (QuotientGroup.mk' O) := Subgroup.le_comap_map _ _
      rw [← hJmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
      exact h1
    exact (not_le_of_gt hJlt) (le_of_subnormal K0_perfect hJsub hKJ)

end K0

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

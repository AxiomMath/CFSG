module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Main
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG CFSG.GorensteinWalter DihedralGroup
open scoped commutatorElement

section Cases

variable {X : Type} [Group X] [Finite X] {x : X} [CentralInv x] {ψ : DihedralGroup 4 →* X}
  {T : Sylow 2 X} {P : X → Prop}

theorem hasDihedralSylowTwo_Qx (hD : DihData x ψ T) : HasDihedralSylowTwo (Qx x) := by
  let mk := QuotientGroup.mk' (zpowers x)
  let Tq : Sylow 2 (Qx x) := T.mapSurjective (QuotientGroup.mk'_surjective (zpowers x))
  have hTq : (Tq : Subgroup (Qx x)) = (T : Subgroup X).map mk :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (zpowers x)) T
  let ψq : DihedralGroup 4 →* Qx x := mk.comp ψ
  have hψq : Function.Injective ψq := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ψ g ∈ zpowers x := (QuotientGroup.eq_one_iff _).1 hg
    have h2 : ψ g ∈ zpowers x ⊓ ψ.range := ⟨h1, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
    rw [hD.disj] at h2
    exact hD.inj (by rw [(Subgroup.mem_bot).1 h2, map_one])
  have hrange : ψq.range = (T : Subgroup X).map mk := by
    rw [hD.sup, Subgroup.map_sup, MonoidHom.range_comp]
    have : (zpowers x).map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  let e0 : DihedralGroup 4 ≃* ↥(Tq : Subgroup (Qx x)) :=
    (MonoidHom.ofInjective hψq).trans (MulEquiv.subgroupCongr (hrange.trans hTq.symm))
  intro S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Qx x) Tq S
  refine ⟨2, by norm_num, ⟨?_⟩⟩
  have e1 : ↥(Tq : Subgroup (Qx x)) ≃* ↥((g • Tq : Sylow 2 (Qx x)) : Subgroup (Qx x)) := Tq.equivSMul g
  rw [hg] at e1
  exact e1.symm.trans e0.symm

theorem exists_sylow_Qh (hD : DihData x ψ T) : ∃ m, Odd m ∧ Nat.card (Qh x) = 8 * m := by
  let Tq : Sylow 2 (Qh x) := T.mapSurjective (piH_surjective x)
  have hTq : (Tq : Subgroup (Qh x)) = (T : Subgroup X).map (piH x) :=
    Sylow.coe_mapSurjective (piH_surjective x) T
  let ψh : DihedralGroup 4 →* Qh x := (piH x).comp ψ
  have hrange : ψh.range = (T : Subgroup X).map (piH x) := by
    rw [hD.sup, Subgroup.map_sup, MonoidHom.range_comp]
    have : (zpowers x).map (piH x) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, ker_piH]
      exact le_sup_right
    rw [this, bot_sup_eq]
  have hcard : Nat.card (Tq : Subgroup (Qh x)) = 8 := by
    rw [hTq, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hD.piPsi_injective).toEquiv,
      DihedralGroup.nat_card]
  refine ⟨(Tq : Subgroup (Qh x)).index, ?_, ?_⟩
  · exact Nat.odd_iff.2 (by have := Tq.not_dvd_index; omega)
  · rw [← Subgroup.index_mul_card (Tq : Subgroup (Qh x)), hcard, mul_comm]

theorem orderOf_piPsi (hD : DihData x ψ T) {g : DihedralGroup 4} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    orderOf (piH x (ψ g)) = 2 := by
  refine orderOf_eq_prime (by rw [pow_two, ← map_mul, ← map_mul, hg2, map_one, map_one]) fun h => hg1 ?_
  exact hD.piPsi_injective (by rw [map_one]; exact h)

theorem not_oneClass (hc : Cfg x ψ T P)
    (h1 : ∀ s t : Qh x, orderOf s = 2 → orderOf t = 2 → IsConj s t) : False := by
  have hy2 : orderOf (ψ (sr 0)) = 2 := orderOf_psi_sr hc.dih 0
  have hz2 : orderOf (ψ (r 2)) = 2 := orderOf_psi_r2 hc.dih
  have hy' : orderOf (piH x (ψ (sr 0))) = 2 :=
    orderOf_piPsi hc.dih (by rw [DihedralGroup.one_def]; exact fun h => by cases h) (by decide)
  have hz' : orderOf (piH x (ψ (r 2))) = 2 :=
    orderOf_piPsi hc.dih (by rw [DihedralGroup.one_def]; decide) (by decide)
  obtain ⟨l, hl⟩ := isConj_iff.1 (h1 _ _ hy' hz')
  obtain ⟨c, hc'⟩ := piH_surjective x l
  have hconj : piH x (c * ψ (sr 0) * c⁻¹) = piH x (ψ (r 2)) := by
    rw [map_mul, map_mul, map_inv, hc']; exact hl
  rcases conj_lift x hy2 hz2 hconj with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    exact hc.nPz (hg ▸ hc.Pconj g _ hc.Py)
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    exact hc.nPz (hg ▸ hc.Pconj g _ hc.Pyx)

omit [Finite X] in
theorem isSolvable_of_quot_pPrimeCore {Y : Type} [Group Y] [Finite Y]
    (h : Group.IsSolvable (Y ⧸ pPrimeCore 2 Y)) : Group.IsSolvable Y := by
  have : Group.IsSolvable ↥(pPrimeCore 2 Y) := isSolvable_of_odd_card (odd_card_pPrimeCore Y)
  refine Group.isSolvable_of_ker_le_range (pPrimeCore 2 Y).subtype (QuotientGroup.mk' (pPrimeCore 2 Y)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem isSolvable_of_Qh (h : Group.IsSolvable (Qh x)) : Group.IsSolvable X := by
  have hQ : Group.IsSolvable (Qx x) := isSolvable_of_quot_pPrimeCore h
  have : Group.IsSolvable ↥(zpowers x) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
      simp only [Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq)
  refine Group.isSolvable_of_ker_le_range (zpowers x).subtype (QuotientGroup.mk' (zpowers x)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

omit [Finite X] [CentralInv x] in
theorem three_le_of_isOddPrimePower {q : ℕ} (hK : IsOddPrimePower q) : 3 ≤ q := by
  obtain ⟨p, n, hp, hpodd, hn, rfl⟩ := hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hpodd) even_two
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn

end Cases

section Fusion

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem oneClass_of_equiv {B : Type} [Group B] (φ : H ≃* B)
    (hB : ∀ a b : B, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution a →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution b → ∃ g : B, g * a * g⁻¹ = b) :
    ∀ s t : H, orderOf s = 2 → orderOf t = 2 → IsConj s t := by
  intro s t hs ht
  have hI : ∀ g : H, orderOf g = 2 → CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (φ g) := by
    intro g hg
    refine (isInvolution_iff _).2 ?_
    have := orderOf_injective φ.toMonoidHom φ.injective g
    rw [← hg]; exact this
  obtain ⟨g, hg⟩ := hB _ _ (hI s hs) (hI t ht)
  exact isConj_iff.2 ⟨φ.symm g, φ.injective (by simpa using hg)⟩

theorem oneClass_of_psl2 {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup H) [L.Normal] (hLodd : Odd L.index) (e : ↥L ≃* PSL2 K) :
    ∀ s t : H, orderOf s = 2 → orderOf t = 2 → IsConj s t := by
  intro s t hs ht
  have hsq : ∀ g : H, orderOf g = 2 → g ^ (2 ^ 1) = 1 := fun g hg => by
    rw [pow_one]; exact hg ▸ pow_orderOf_eq_one g
  have hsL : s ∈ L := two_elt_mem_L hLodd (hsq s hs)
  have htL : t ∈ L := two_elt_mem_L hLodd (hsq t ht)
  have hI : ∀ (g : H) (hg : g ∈ L), orderOf g = 2 →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (e ⟨g, hg⟩) := by
    intro g hg h2
    refine (isInvolution_iff _).2 ?_
    have := orderOf_injective e.toMonoidHom e.injective ⟨g, hg⟩
    rw [Subgroup.orderOf_mk, h2] at this
    exact this
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K hK _ _ (hI s hsL hs) (hI t htL ht)
  refine isConj_iff.2 ⟨((e.symm g : ↥L) : H), ?_⟩
  have : (e.symm g) * ⟨s, hsL⟩ * (e.symm g)⁻¹ = ⟨t, htL⟩ := by
    apply e.injective; simpa using hg
  exact congrArg Subtype.val this

end Fusion

section Main

variable {X : Type} [Group X] [Finite X] {x : X} [CentralInv x] {ψ : DihedralGroup 4 →* X}
  {T : Sylow 2 X} {P : X → Prop}

theorem main_abstract (hGW : gorensteinWalterStatement.{0})
    (hc : Cfg x ψ T P) : NC X x P := by
  have hD : IsDGroup (Qx x) := hGW (Qx x) (hasDihedralSylowTwo_Qx hc.dih)
  have h8 := exists_sylow_Qh hc.dih
  cases hD with
  | quotientIsTwoGroup hSylow h =>
    exfalso
    have : Group.IsNilpotent (Qh x) := h.isNilpotent
    exact hc.nonsolv (isSolvable_of_Qh (x := x) inferInstance)
  | quotientIsASeven hSylow e =>
    exfalso
    obtain ⟨e⟩ := e
    exact not_oneClass hc (oneClass_of_equiv e fun a b ha hb => aSeven_involutions_conjugate a b ha hb)
  | quotientHasLinearNormalSubgroup hSylow K hKpp L hLnormal hLindex hLmodel =>
    have : L.Normal := hLnormal
    rcases hLmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exfalso
      exact not_oneClass hc (oneClass_of_psl2 hKpp L hLindex e)
    · by_cases hK3 : Nat.card K = 3
      · exfalso
        let _ : Fintype K := Fintype.ofFinite K
        have hF : Fintype.card K = 3 := by
          rw [← Nat.card_eq_fintype_card]; exact hK3
        let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hF
        let e4 : ↥L ≃* Equiv.Perm (Fin 4) := (e.trans (pgl2RingEquiv eK).symm).trans pgl2_three_equiv_perm
        have hS4 : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
        have hLs : Group.IsSolvable ↥L :=
          Group.isSolvable_of_isSolvable_injective (f := e4.toMonoidHom) e4.injective
        have : Group.IsSolvable (Qh x ⧸ L) := isSolvable_of_odd_card hLindex
        have hQh : Group.IsSolvable (Qh x) := by
          refine Group.isSolvable_of_ker_le_range L.subtype (QuotientGroup.mk' L) ?_
          rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
        exact hc.nonsolv (isSolvable_of_Qh (x := x) hQh)
      · exact main_pgl2 hc hKpp (lt_of_le_of_ne (three_le_of_isOddPrimePower hKpp) (Ne.symm hK3))
          hLindex e h8

end Main

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

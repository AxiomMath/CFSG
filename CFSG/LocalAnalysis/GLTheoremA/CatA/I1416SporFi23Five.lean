module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi22Cent5
public import CFSG.RankThree.PartOne.LIT.FiveRecords

public section

set_option linter.unusedSectionVars false

namespace CFSG.Sporadic.Fi23

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint.Fischer
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem mul_pow_five_ne_one {G : Type*} [Group G] {d w : G} (hd2 : d ^ 2 = 1) (hd1 : d ≠ 1)
    (hdw : d * w = w * d) (hw5 : w ^ 5 = 1) : (d * w) ^ 5 ≠ 1 := by
  have hc : Commute d w := hdw
  rw [hc.mul_pow 5, hw5, mul_one, show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, hd2,
    one_pow, one_mul]
  exact hd1

theorem card_centralizer_inf_conj {G : Type*} [Group G] (h w d : G) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({h * d * h⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({h⁻¹ * w * h} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)) := by
  have hmap : (Subgroup.centralizer ({h⁻¹ * w * h} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({h * d * h⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      constructor
      · calc h * y * h⁻¹ * w = h * (y * (h⁻¹ * w * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * w * h) * y) * h⁻¹ := by rw [hy1]
          _ = w * (h * y * h⁻¹) := by group
      · calc h * y * h⁻¹ * (h * d * h⁻¹) = h * (y * d) * h⁻¹ := by group
          _ = h * (d * y) * h⁻¹ := by rw [hy2]
          _ = h * d * h⁻¹ * (h * y * h⁻¹) := by group
    · rintro ⟨hx1, hx2⟩
      refine ⟨h⁻¹ * x * h, ⟨?_, ?_⟩, by group⟩
      · calc h⁻¹ * x * h * (h⁻¹ * w * h) = h⁻¹ * (x * w) * h := by group
          _ = h⁻¹ * (w * x) * h := by rw [hx1]
          _ = h⁻¹ * w * h * (h⁻¹ * x * h) := by group
      · calc h⁻¹ * x * h * d = h⁻¹ * (x * (h * d * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * d * h⁻¹) * x) * h := by rw [hx2]
          _ = d * (h⁻¹ * x * h) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem orderOf_conj_inv_mul {G : Type*} [Group G] (h w : G) : orderOf (h⁻¹ * w * h) = orderOf w := by
  have := (MulAut.conj h⁻¹).orderOf_eq w
  simpa [MulAut.conj_apply] using this

theorem commute_conj_inv_mul {G : Type*} [Group G] {h w d : G} (hwe : w * (h * d * h⁻¹) =
    (h * d * h⁻¹) * w) : h⁻¹ * w * h * d = d * (h⁻¹ * w * h) := by
  calc h⁻¹ * w * h * d = h⁻¹ * (w * (h * d * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * d * h⁻¹) * w) * h := by rw [hwe]
    _ = d * (h⁻¹ * w * h) := by group

noncomputable def rhoRangeEquiv : ↥rho.range ≃* ↥CFSG.Monster.B.Fischer.fi22P :=
  (MulEquiv.subgroupCongr range_rho).trans
    (((MonoidHom.ofInjective pi22_injective).symm.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm).trans
      CFSG.Monster.B.Fischer.fi22PermEquiv)

set_option maxRecDepth 100000 in
theorem card_centralizer_Cd_five (w : Cd) (hw : orderOf w = 5) :
    Nat.card (Subgroup.centralizer ({w} : Set Cd)) = 1200 := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup Cd, C = Subgroup.centralizer ({w} : Set Cd) := ⟨_, rfl⟩
  rw [← hCdef]
  have hdZ : dCd ∈ Subgroup.center Cd := by
    rw [center_C]; exact Subgroup.mem_zpowers _
  have hwd : w * dCd = dCd * w := Subgroup.mem_center_iff.mp hdZ w
  have hdw : dCd * w = w * dCd := hwd.symm
  have hdC : dCd ∈ C := hCdef ▸ Subgroup.mem_centralizer_singleton_iff.mpr hdw
  have hker : rho.ker ≤ C := by
    rw [ker_rho, Subgroup.zpowers_le]
    exact hdC
  have hrw1 : rho w ≠ 1 := by
    intro h
    have hk : w ∈ rho.ker := h
    rw [ker_rho] at hk
    have hd := orderOf_dvd_of_mem_zpowers hk
    rw [hw, orderOf_dCd] at hd
    norm_num at hd
  have hro : orderOf (⟨rho w, MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩ : ↥rho.range) = 5 := by
    have h5 : rho w ^ 5 = 1 := by rw [← map_pow, ← hw, pow_orderOf_eq_one, map_one]
    refine orderOf_eq_prime ?_ (fun h => hrw1 (congrArg Subtype.val h))
    apply Subtype.ext
    simpa using h5
  have himg : C.map rho = Subgroup.centralizer ({rho w} : Set (Equiv.Perm (Fin 3510))) ⊓ rho.range := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      rw [hCdef] at hg
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ⟨g, rfl⟩⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
    · intro σ hσ'
      obtain ⟨hσ, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.1 hσ'
      refine ⟨g, hCdef ▸ Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hσ
      have hcomm : g * w * g⁻¹ * w⁻¹ ∈ rho.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hσ]
        group
      rw [ker_rho] at hcomm
      have hd2 : dCd ^ 2 = 1 := by rw [← orderOf_dCd, pow_orderOf_eq_one]
      classical
      obtain ⟨n, hn, hxn⟩ := Finset.mem_image.1 ((mem_zpowers_iff_mem_range_orderOf).1 hcomm)
      rw [Finset.mem_range, orderOf_dCd] at hn
      have hw5 : w ^ 5 = 1 := by rw [← hw, pow_orderOf_eq_one]
      interval_cases n
      ·
        rw [pow_zero] at hxn
        have h : g * w * g⁻¹ = w := by
          calc g * w * g⁻¹ = g * w * g⁻¹ * w⁻¹ * w := by group
            _ = w := by rw [← hxn, one_mul]
        calc g * w = g * w * g⁻¹ * g := by group
          _ = w * g := by rw [h]
      ·
        exfalso
        rw [pow_one] at hxn
        have hconj : g * w * g⁻¹ = dCd * w := by
          calc g * w * g⁻¹ = g * w * g⁻¹ * w⁻¹ * w := by group
            _ = dCd * w := by rw [← hxn]
        have h5 : (g * w * g⁻¹) ^ 5 = 1 := by
          rw [conj_pow, hw5, mul_one, mul_inv_cancel]
        have hd1 : dCd ≠ 1 := fun h => by
          have := orderOf_dCd
          rw [h, orderOf_one] at this
          norm_num at this
        exact mul_pow_five_ne_one hd2 hd1 hdw hw5 (hconj ▸ h5)
  have hrange : Nat.card ↥(Subgroup.centralizer ({rho w} : Set (Equiv.Perm (Fin 3510))) ⊓ rho.range) =
      600 := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype rho.range
      ⟨rho w, MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩, Subgroup.card_map_of_injective rho.range.subtype_injective]
    exact card_centralizer_five_of_equiv rhoRangeEquiv _ hro
  have h1 : Nat.card C = Nat.card (rho.comp C.subtype).range * Nat.card (rho.comp C.subtype).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (rho.comp C.subtype).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (rho.comp C.subtype)).toEquiv]
  have hr : Nat.card (rho.comp C.subtype).range = 600 := by
    rw [← hrange, ← himg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card (rho.comp C.subtype).ker = 2 := by
    rw [← MonoidHom.comap_ker, ← card_ker_rho]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [hr, hk] at h1
  rw [h1]

set_option maxRecDepth 100000 in
theorem card_centralizer_inf_d (w : J) (hw : orderOf w = 5) (hwd : w * d = d * w) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set J) ⊓ Cd) = 1200 := by
  have hwC : w ∈ Cd := mem_Cd.2 hwd
  have hmap := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype Cd ⟨w, hwC⟩
  rw [← hmap, Subgroup.card_map_of_injective Cd.subtype_injective]
  refine card_centralizer_Cd_five ⟨w, hwC⟩ ?_
  rw [← Subgroup.orderOf_coe]
  exact hw

set_option maxRecDepth 100000 in
theorem card_centralizer_inf_D23 (w : J) (hw : orderOf w = 5) {e : J} (he : e ∈ D23)
    (hwe : w * e = e * w) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set J) ⊓ Subgroup.centralizer ({e} : Set J)) = 1200 := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 he
  rw [card_centralizer_inf_conj h w d]
  exact card_centralizer_inf_d (h⁻¹ * w * h) (by rw [orderOf_conj_inv_mul, hw])
    (commute_conj_inv_mul hwe)

end CFSG.Sporadic.Fi23

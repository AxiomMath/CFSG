module

public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Local.FixedMaximalElementaryAbelianTrivialAction
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
public import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
public import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
public import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
public import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem maximal_isElementaryAbelianSubgroup_subgroupOf {E H : Subgroup X}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hEH : E ≤ H) :
    Maximal (IsElementaryAbelianSubgroup p) (E.subgroupOf H) := by
  refine ⟨hE.prop.comap H.subtype_injective, fun A hA hle => ?_⟩
  have hmap : A.map H.subtype ≤ E := by
    refine hE.le_of_ge (hA.map _) fun x hx => ?_
    exact ⟨⟨x, hEH hx⟩, hle (mem_subgroupOf.2 hx), rfl⟩
  exact fun a ha => mem_subgroupOf.2 (hmap (mem_map_of_mem _ ha))

omit [Finite X] in
theorem maximal_isElementaryAbelianSubgroup_map_mk' (N : Subgroup X) [N.Normal] {E S : Subgroup X}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hES : E ≤ S) (hdisj : Disjoint S N)
    (habs : ∀ A : Subgroup (X ⧸ N), IsElementaryAbelianSubgroup p A →
      A ≤ S.map (QuotientGroup.mk' N)) :
    Maximal (IsElementaryAbelianSubgroup p) (E.map (QuotientGroup.mk' N)) := by
  have hinj : ∀ x ∈ S, ∀ y ∈ S, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have := disjoint_def.1 hdisj (mul_mem hx (inv_mem hy)) h1
    rwa [mul_inv_eq_one] at this
  refine ⟨hE.prop.map _, fun A hA hle => ?_⟩
  have hAS : A ≤ S.map (QuotientGroup.mk' N) := habs A hA
  have hT : IsElementaryAbelianSubgroup p (A.comap (QuotientGroup.mk' N) ⊓ S) := by
    constructor
    · intro x hx y hy
      refine hinj _ (mul_mem hx.2 hy.2) _ (mul_mem hy.2 hx.2) ?_
      rw [map_mul, map_mul]
      exact hA.mul_comm _ hx.1 _ hy.1
    · intro x hx
      refine hinj _ (pow_mem hx.2 p) _ (one_mem S) ?_
      rw [map_pow, map_one]
      exact hA.pow_eq_one _ hx.1
  have hTE := hE.le_of_ge hT (le_inf (fun e he => hle (mem_map_of_mem _ he)) hES)
  intro a ha
  obtain ⟨x, hxS, rfl⟩ := hAS ha
  exact mem_map_of_mem _ (hTE ⟨ha, hxS⟩)

omit [Finite X] in
theorem le_centralizer_of_disjoint_of_le_normalizer {E S Y : Subgroup X} (hS : S.Normal)
    (hES : E ≤ S) (hdisj : Disjoint Y S) (hEY : E ≤ normalizer (Y : Set X)) :
    Y ≤ centralizer (E : Set X) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro e he
  have h1 : e * y * e⁻¹ * y⁻¹ ∈ Y :=
    mul_mem ((mem_normalizer_iff.1 (hEY he) y).1 hy) (inv_mem hy)
  have h2 : e * y * e⁻¹ * y⁻¹ ∈ S := by
    have h3 : e * (y * e⁻¹ * y⁻¹) ∈ S :=
      mul_mem (hES he) (hS.conj_mem _ (inv_mem (hES he)) y)
    simpa [mul_assoc] using h3
  have h4 := disjoint_def.1 hdisj h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem le_centralizer_of_maximal_of_le_centralizer (hp : p.Prime) (hodd : Odd p) {S Y : Subgroup X}
    (hS : S.Normal) (hSP : IsPGroup p S) {E : Subgroup X}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hES : E ≤ S)
    (hcop : (Nat.card Y).Coprime (Nat.card S))
    (hYE : Y ≤ centralizer (E : Set X)) : Y ≤ centralizer (S : Set X) := by
  have hSi : S.Normal := hS
  let ρ : Y →* MulAut S := (MulAut.conjNormal (H := S)).comp Y.subtype
  have hfix : ∀ a : Y, ∀ e ∈ E.subgroupOf S, ρ a e = e := by
    intro a e he
    refine Subtype.ext ?_
    have hc : (a : X) * (e : X) = (e : X) * (a : X) :=
      (mem_centralizer_iff.1 (hYE a.2) _ (mem_subgroupOf.1 he)).symm
    change (a : X) * (e : X) * (a : X)⁻¹ = (e : X)
    rw [hc, mul_inv_cancel_right]
  have htriv := apply_eq_self_of_maximal_isElementaryAbelianSubgroup_fixed (P := S) hp hodd hSP ρ
    hcop (maximal_isElementaryAbelianSubgroup_subgroupOf hE hES) hfix
  intro y hy
  rw [mem_centralizer_iff]
  intro s hs
  have h2 : y * s * y⁻¹ = s := congrArg Subtype.val (htriv ⟨y, hy⟩ ⟨s, hs⟩)
  conv_lhs => rw [← h2]
  group

theorem le_pComplCore_of_maximal_isElementaryAbelianSubgroup (hp : p.Prime) (hodd : Odd p)
    [Group.IsSolvable X] (hX : HasPLengthLeOne p X) {E Y : Subgroup X}
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hY : p.Coprime (Nat.card Y))
    (hEY : E ≤ normalizer (Y : Set X)) : Y ≤ pComplCore p X := by
  have hpf := Fact.mk hp
  have hYdvd : ¬ p ∣ Nat.card Y := hp.coprime_iff_not_dvd.1 hY
  set N := pComplCore p X with hN
  have hNnormal : N.Normal := pComplCore_normal p X
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  set Sbar := pCore p (X ⧸ N) with hSbar
  have hSbarNormal : Sbar.Normal := pCore_normal p _
  have hSbarP : IsPGroup p Sbar := isPGroup_pCore hp _
  obtain ⟨n, hn⟩ := hSbarP.exists_card_eq
  have habsP : ∀ A : Subgroup (X ⧸ N), IsPGroup p A → A ≤ Sbar := fun A hA => by
    obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
    exact hQ.trans (le_of_eq (hX.coe_eq_pCore Q))
  obtain ⟨S, hSE⟩ := hE.prop.isPGroup.exists_le_sylow
  have hSmap : (S : Subgroup X).map π = Sbar := by
    rw [hSbar, ← Sylow.coe_mapSurjective hsurj S]
    exact hX.coe_eq_pCore _
  have hSdisj : Disjoint (S : Subgroup X) N := by
    obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard
      (hm ▸ (hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCore hp X)).pow_left m)
  have hEbar : Maximal (IsElementaryAbelianSubgroup p) (E.map π) :=
    maximal_isElementaryAbelianSubgroup_map_mk' N hE hSE hSdisj
      (fun A hA => hSmap ▸ habsP A hA.isPGroup)
  set Ybar := Y.map π with hYbar
  have hYbarp : ¬ p ∣ Nat.card Ybar := fun h => hYdvd (h.trans (natCard_map_mk'_dvd Y N))
  have hcop : (Nat.card Ybar).Coprime (Nat.card Sbar) :=
    hn ▸ ((hp.coprime_iff_not_dvd.2 hYbarp).symm).pow_right n
  have hYS : Disjoint Ybar Sbar := disjoint_of_coprime_natCard hcop
  have hEbarS : E.map π ≤ Sbar := hSmap ▸ map_mono hSE
  have hEYbar : E.map π ≤ normalizer (Ybar : Set (X ⧸ N)) :=
    (map_mono hEY).trans (le_normalizer_map π)
  have hYcentE : Ybar ≤ centralizer ((E.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    le_centralizer_of_disjoint_of_le_normalizer hSbarNormal hEbarS hYS hEYbar
  have hYcentS : Ybar ≤ centralizer ((Sbar : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    le_centralizer_of_maximal_of_le_centralizer hp hodd hSbarNormal hSbarP hEbar hEbarS hcop
      hYcentE
  have hYSbar : Ybar ≤ Sbar :=
    hYcentS.trans (centralizer_pCore_le_pCore hp (pComplCore_quotient_pComplCore p X))
  have hYbot : Ybar = ⊥ := by
    rw [eq_bot_iff]
    exact fun y hy => disjoint_def.1 hYS hy (hYSbar hy) ▸ one_mem _
  have := (Subgroup.map_eq_bot_iff Y).1 hYbot
  rwa [hπ, QuotientGroup.ker_mk'] at this

theorem le_pComplCore_of_maximal_isElementaryAbelian (hp : p.Prime) (hodd : Odd p)
    [Group.IsSolvable X] (hX : HasPLengthLeOne p X) {E Y : Subgroup X}
    (hE : Maximal (IsElementaryAbelian p) E) (hY : p.Coprime (Nat.card Y))
    (hEY : E ≤ normalizer (Y : Set X)) : Y ≤ pComplCore p X :=
  le_pComplCore_of_maximal_isElementaryAbelianSubgroup hp hodd hX
    (maximal_isElementaryAbelianSubgroup_iff.2 (maximal_isElementaryAbelian_iff.1 hE)) hY hEY

end

end CFSG.FeitThompson

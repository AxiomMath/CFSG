module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.Sporadic.SuzOddCore.SmallAut
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.OuterAutomorphisms

section Generic

theorem mulAut_conj_conj {X : Type*} [Group X] (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_inner_of_card_outer {X : Type*} [Group X] (hout : Nat.card (Outer X) = 2)
    {U : Subgroup (MulAut X)} (hU4 : 4 ≤ Nat.card U) : ∃ u ∈ U, u ≠ 1 ∧ u ∈ inner X := by
  by_contra h
  push Not at h
  have : Finite (Outer X) := Nat.finite_of_card_ne_zero (by rw [hout]; norm_num)
  let f : ↥U →* Outer X := (QuotientGroup.mk' (inner X)).comp U.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : (a : MulAut X)⁻¹ * b ∈ inner X := by
      have := QuotientGroup.eq.mp hab
      simpa using this
    by_contra hne
    have hne' : (a : MulAut X)⁻¹ * b ≠ 1 := fun h1 => hne (Subtype.ext (by
      rw [inv_mul_eq_one] at h1
      exact h1))
    exact h _ (U.mul_mem (U.inv_mem a.2) b.2) hne' hab'
  have := Nat.card_le_card_of_injective f hf
  omega

theorem card_quot_center_dvd_card_map_conj {X : Type*} [Group X] [Finite X] (L : Subgroup X) :
    Nat.card (↥L ⧸ center ↥L) ∣ Nat.card (L.map (MulAut.conj : X →* MulAut X)) := by
  set f : ↥L →* MulAut X := (MulAut.conj : X →* MulAut X).comp L.subtype
  have hrange : f.range = L.map (MulAut.conj : X →* MulAut X) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : f.ker ≤ center ↥L := by
    intro l hl
    rw [mem_center_iff]
    intro m
    have h := congrArg (fun α : MulAut X => α (m : X)) (MonoidHom.mem_ker.mp hl)
    simp only [f, MonoidHom.comp_apply, MulAut.conj_apply, coe_subtype, MulAut.one_apply] at h
    apply Subtype.ext
    simp only [coe_mul]
    calc (m : X) * l = l * m * (l : X)⁻¹ * l := by rw [h]
      _ = l * m := by group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  refine ⟨c, ?_⟩
  have : Nat.card (L.map (MulAut.conj : X →* MulAut X)) * Nat.card f.ker =
      Nat.card (↥L ⧸ center ↥L) * c * Nat.card f.ker := by
    rw [← h1, h2, hc]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem mem_of_not_dvd {G : Type*} [Group G] [Finite G] {C N : Subgroup G} (hNC : N ≤ C)
    (h9 : 9 ∣ Nat.card N) (h27 : ¬ 27 ∣ Nat.card C) {σ : G} (hσC : σ ∈ C)
    (hσN : σ ∈ normalizer (N : Set G)) {k : ℕ} (hσk : σ ^ 3 ^ k = 1) : σ ∈ N := by
  set H := C ⊓ normalizer (N : Set G)
  have hNH : N ≤ H := le_inf hNC le_normalizer
  have : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  set s : ↥H := ⟨σ, hσC, hσN⟩
  set q : ↥H ⧸ N.subgroupOf H := (s : ↥H ⧸ N.subgroupOf H)
  by_contra hσ
  have hq1 : q ≠ 1 := by
    intro h
    exact hσ ((QuotientGroup.eq_one_iff s).mp h)
  have hqk : q ^ 3 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : s ^ 3 ^ k = 1 := Subtype.ext (by simpa using hσk)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hqk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hq1 hj
  have h3 : 3 ∣ Nat.card (↥H ⧸ N.subgroupOf H) :=
    (dvd_pow_self 3 hj0).trans (hj ▸ orderOf_dvd_natCard q)
  have hH := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  rw [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv] at hH
  have h27H : 27 ∣ Nat.card H := by
    rw [hH, show (27 : ℕ) = 3 * 9 by norm_num]
    exact Nat.mul_dvd_mul h3 h9
  exact h27 (h27H.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem l34DiagFact_of_outer {X : Type} [Group X] [Finite X] (hout : Nat.card (Outer X) = 2)
    (hcent : ∀ u : MulAut X, u ∈ inner X → u ^ 2 = 1 → u ≠ 1 →
      7 ∣ Nat.card (centralizer ({u} : Set (MulAut X))) →
        ¬ 27 ∣ Nat.card (centralizer ({u} : Set (MulAut X)))) :
    L34DiagFact X := by
  intro L U σ hL hmodel hfix hU hU4 hσL hσU hσ3
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) fun f g h => MulEquiv.ext (congrFun h)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hmodel
  have hLZ : Nat.card (↥L ⧸ center ↥L) = 20160 := by
    rw [Nat.card_congr eK.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hKcard]
    decide
  have hN : 20160 ∣ Nat.card (L.map (MulAut.conj : X →* MulAut X)) :=
    hLZ ▸ card_quot_center_dvd_card_map_conj L
  obtain ⟨u, huU, hu1, hinn⟩ := exists_inner_of_card_outer hout hU4
  have hu2 : u ^ 2 = 1 := hU.2 u huU
  have hNu : L.map (MulAut.conj : X →* MulAut X) ≤ centralizer ({u} : Set (MulAut X)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mulAut_conj_conj u l
    rw [hfix u huU l hl] at h
    calc MulAut.conj l * u = u * MulAut.conj l * u⁻¹ * u := by rw [h]
      _ = u * MulAut.conj l := by group
  have h7 : 7 ∣ Nat.card (centralizer ({u} : Set (MulAut X))) :=
    ((by norm_num : 7 ∣ 20160).trans hN).trans (Subgroup.card_dvd_of_le hNu)
  have h27 := hcent u hinn hu2 hu1 h7
  have hσu : σ ∈ centralizer ({u} : Set (MulAut X)) :=
    mem_centralizer_singleton_iff.mpr (hσU u huU)
  have hσN : σ ∈ normalizer ((L.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) :
      Set (MulAut X)) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨σ l, (hσL l).mp hl, (mulAut_conj_conj σ l).symm⟩
    · rintro ⟨l, hl, hl'⟩
      refine ⟨σ⁻¹ l, ?_, ?_⟩
      · show σ⁻¹ l ∈ L
        rw [hσL, MulAut.apply_inv_self]
        exact hl
      · rw [← mulAut_conj_conj σ⁻¹ l, hl']
        group
  obtain ⟨k, hk⟩ := hσ3
  obtain ⟨l, hl, hσl⟩ := mem_of_not_dvd hNu ((by norm_num : 9 ∣ 20160).trans hN) h27 hσu hσN hk
  refine ⟨l, hl, fun x _ => ?_⟩
  rw [← hσl, MulAut.conj_apply, mul_inv_cancel]
  exact one_mem _

end Generic

section Suz

@[expose] noncomputable def suzAutEquiv
    : suzT ≃* MulAut NativeSporadic.Suz :=
  MulEquiv.ofBijective suzConjTSuz suzConjTSuz_bijective

theorem card_centralizer_suzT (t : suzT) :
    Nat.card (centralizer ({t} : Set suzT)) = Nat.card (centT (t : Equiv.Perm (Fin 1782))) := by
  have hmap : (centralizer ({t} : Set suzT)).map suzT.subtype =
      centT (t : Equiv.Perm (Fin 1782)) := by
    ext g
    simp only [mem_map, mem_centralizer_singleton_iff, coe_subtype, centT, mem_inf]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨congrArg Subtype.val hh, h.2⟩
    · rintro ⟨hg, hgT⟩
      exact ⟨⟨g, hgT⟩, Subtype.ext hg, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective suzT.subtype_injective]

theorem card_centT_conj {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (x : Equiv.Perm (Fin 1782)) :
    Nat.card (centT (c * x * c⁻¹)) = Nat.card (centT x) := by
  have hmap : (centT x).map (MulAut.conj c).toMonoidHom = centT (c * x * c⁻¹) := by
    ext g
    simp only [mem_map, centT, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨h, ⟨hh, hhT⟩, rfl⟩
      refine ⟨?_, suzT.mul_mem (suzT.mul_mem hc hhT) (suzT.inv_mem hc)⟩
      calc c * h * c⁻¹ * (c * x * c⁻¹) = c * (h * x) * c⁻¹ := by group
        _ = c * (x * h) * c⁻¹ := by rw [hh]
        _ = c * x * c⁻¹ * (c * h * c⁻¹) := by group
    · rintro ⟨hg, hgT⟩
      refine ⟨c⁻¹ * g * c, ⟨?_, suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hc) hgT) hc⟩, by group⟩
      calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hg]
        _ = x * (c⁻¹ * g * c) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem suzAut_not_dvd_card_centralizer
    {u : MulAut NativeSporadic.Suz} (hu : u ∈ inner NativeSporadic.Suz) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (h7 : 7 ∣ Nat.card (centralizer ({u} : Set (MulAut NativeSporadic.Suz)))) :
    ¬ 27 ∣ Nat.card (centralizer ({u} : Set (MulAut NativeSporadic.Suz))) := by
  set e := suzAutEquiv
  set t := e.symm u with ht_def
  have hu' : e t = u := e.apply_symm_apply u
  have htM : (t : Equiv.Perm (Fin 1782)) ∈ suzM := by
    obtain ⟨s, hs⟩ := hu
    set m := suzEquivM s
    set t' : suzT := ⟨(m : Equiv.Perm (Fin 1782)), suzM_le_suzT m.2⟩
    have hconj : ∀ x : NativeSporadic.Suz, suzEquivM (e t' x) = suzEquivM (u x) := by
      intro x
      have h1 : suzEquivM (e t' x) = suzConjT t' (suzEquivM x) := by
        change suzEquivM' (suzEquivM'.symm (suzConjT t' (suzEquivM' x))) = _
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [h1, ← hs, MulAut.conj_apply, map_mul, map_mul, map_inv]
      apply Subtype.ext
      rw [suzConjT_apply]
      rfl
    have he : e t' = u := MulEquiv.ext fun x => suzEquivM.injective (hconj x)
    have ht : t = t' := by
      rw [ht_def, ← he, MulEquiv.symm_apply_apply]
    rw [ht]
    exact m.2
  have ht2 : orderOf (t : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, ht_def, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hu2 hu1
  have hcard : Nat.card (centralizer ({u} : Set (MulAut NativeSporadic.Suz))) =
      Nat.card (centT (t : Equiv.Perm (Fin 1782))) := by
    rw [← card_centralizer_suzT t]
    have hmap : (centralizer ({t} : Set suzT)).map e.toMonoidHom =
        centralizer ({u} : Set (MulAut NativeSporadic.Suz)) := by
      ext g
      simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨h, hh, rfl⟩
        have := congrArg e hh
        rwa [map_mul, map_mul, hu'] at this
      · intro hg
        refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hu']
        exact hg
    rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  obtain ⟨c, hc, hct⟩ := suzM_involution_class htM ht2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hD, hD0, hD1, -⟩ :=
    CTUC_Suz_four_exact_involution_centralizers
  rw [hcard] at h7 ⊢
  rcases hct with h | h
  · rw [← h, card_centT_conj hc, ← (hD 0 (by norm_num)).1, hD0]
    norm_num
  · rw [← h, card_centT_conj hc, ← (hD 1 (by norm_num)).1, hD1] at h7
    norm_num at h7

end Suz

theorem suzL34DiagInput
    : SuzL34DiagInput :=
  @l34DiagFact_of_outer NativeSporadic.Suz inferInstance inferInstance out_suz.1
    (fun _ hu hu2 hu1 h7 => suzAut_not_dvd_card_centralizer hu hu2 hu1 h7)

end CFSG.ComponentClassification.RankTwoExceptional

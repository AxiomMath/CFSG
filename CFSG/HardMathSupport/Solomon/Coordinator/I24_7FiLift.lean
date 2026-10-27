module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiRank
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

variable {Y : Type*} [Group Y] [Finite Y]

theorem fi_central_mem_sylow (PS : Sylow 3 Y) {n : Y} (hn : n ∈ Subgroup.center Y) {j : ℕ}
    (hnj : n ^ 3 ^ j = 1) : n ∈ (PS : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 (Subgroup.zpowers n) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hnj)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y PS Q
  have hnQ : n ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers n)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hnQ
  obtain ⟨s, hs, hsn⟩ := hnQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hsn
  have : s = n := by
    have h1 : g * s * g⁻¹ = n := hsn
    have h2 : g * n = n * g := Subgroup.mem_center_iff.1 hn g
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = g⁻¹ * n * g := by rw [h1]
      _ = n := by rw [mul_assoc, ← h2]; group
  exact this ▸ hs

variable (N : Subgroup Y) [N.Normal]

theorem fi_three_elt_mem (hNc : N ≤ Subgroup.center Y) (PS : Sylow 3 Y)
    {Ē : Subgroup (Y ⧸ N)} (hĒ : Ē ≤ (PS : Subgroup Y).map (QuotientGroup.mk' N)) {t : Y}
    (ht : QuotientGroup.mk' N t ∈ Ē) {k : ℕ} (htk : t ^ 3 ^ k = 1) : t ∈ (PS : Subgroup Y) := by
  obtain ⟨p, hp, hpt⟩ := Subgroup.mem_map.1 (hĒ ht)
  have hn : p⁻¹ * t ∈ N := by
    apply (QuotientGroup.eq_one_iff _).1
    change QuotientGroup.mk' N (p⁻¹ * t) = 1
    rw [map_mul, map_inv, hpt, inv_mul_cancel]
  obtain ⟨j, hj⟩ := PS.isPGroup' ⟨p, hp⟩
  have hpj : p ^ 3 ^ j = 1 := congrArg Subtype.val hj
  have hcomm : Commute p (p⁻¹ * t) := by
    have := Subgroup.mem_center_iff.1 (hNc hn) p
    exact this
  have htp : t = p * (p⁻¹ * t) := by group
  set n := p⁻¹ * t with hndef
  have hK : ∀ m, 3 ^ k ∣ 3 ^ m → t ^ 3 ^ m = 1 := fun m hm =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one htk).trans hm)
  have hKp : ∀ m, 3 ^ j ∣ 3 ^ m → p ^ 3 ^ m = 1 := fun m hm =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hpj).trans hm)
  set m := max k j with hm
  have h1 : t ^ 3 ^ m = 1 := hK m (pow_dvd_pow 3 (le_max_left _ _))
  have h2 : p ^ 3 ^ m = 1 := hKp m (pow_dvd_pow 3 (le_max_right _ _))
  have h3 : n ^ 3 ^ m = 1 := by
    have : (p * n) ^ 3 ^ m = p ^ 3 ^ m * n ^ 3 ^ m := hcomm.mul_pow _
    rw [← htp, h1, h2, one_mul] at this
    exact this.symm
  have hnP : n ∈ (PS : Subgroup Y) := fi_central_mem_sylow PS (hNc hn) h3
  rw [htp]
  exact (PS : Subgroup Y).mul_mem hp hnP

theorem fi_normalizer_R (hNc : N ≤ Subgroup.center Y) (PS : Sylow 3 Y)
    {Ē : Subgroup (Y ⧸ N)} (hĒ : Ē ≤ (PS : Subgroup Y).map (QuotientGroup.mk' N)) {y : Y}
    (hy : QuotientGroup.mk' N y ∈ Subgroup.normalizer (Ē : Set (Y ⧸ N))) :
    y ∈ Subgroup.normalizer (((PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) : Subgroup Y) :
      Set Y) := by
  have aux : ∀ y : Y, QuotientGroup.mk' N y ∈ Subgroup.normalizer (Ē : Set (Y ⧸ N)) →
      ∀ h ∈ ((PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) : Subgroup Y),
        y * h * y⁻¹ ∈ ((PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) : Subgroup Y) := by
    intro y hy h hh
    obtain ⟨hhP, hhE⟩ := hh
    have hhE' : QuotientGroup.mk' N h ∈ Ē := hhE
    have hE2 : QuotientGroup.mk' N (y * h * y⁻¹) ∈ Ē := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hy _).1 hhE'
    obtain ⟨k, hk⟩ := PS.isPGroup' ⟨h, hhP⟩
    have hhk : h ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hconj : (y * h * y⁻¹) ^ 3 ^ k = 1 := by
      rw [conj_pow, hhk]
      group
    exact ⟨fi_three_elt_mem N hNc PS hĒ hE2 hconj, hE2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => aux y hy h hh, fun hh => ?_⟩
  have hy' : QuotientGroup.mk' N y⁻¹ ∈ Subgroup.normalizer (Ē : Set (Y ⧸ N)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hy
  have := aux y⁻¹ hy' _ hh
  rw [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at this
  exact this

theorem fi_elemAbelian_map {G G' : Type*} [Group G] [Group G'] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (f : G →* G') : IsElemAbelian 3 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem fi_le_pRank {Q E : Subgroup Y} (hE : E ≤ Q) (he : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) : 3 ≤ CFSG.Open.pRank 3 Q :=
  CFSG.SectionRank.le_pRank (by norm_num) hE he hc

theorem fi_exists_rank_three (hNc : N ≤ Subgroup.center Y) (PS : Sylow 3 Y)
    {Ē : Subgroup (Y ⧸ N)} (hĒ : Ē ≤ (PS : Subgroup Y).map (QuotientGroup.mk' N))
    (hĒe : IsElemAbelian 3 Ē) {r : ℕ} (hr : 4 ≤ r) (hĒc : Nat.card Ē = 3 ^ r)
    (hNP : Nat.card ↥(N ⊓ (PS : Subgroup Y)) ≤ 3) :
    ∃ E : Subgroup Y, E ≤ (PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  set R : Subgroup Y := (PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) with hR
  have hNR : N ⊓ (PS : Subgroup Y) ≤ R := fun x hx => ⟨hx.2, by
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).2 hx.1
    show QuotientGroup.mk' N x ∈ Ē
    rw [h1]
    exact Ē.one_mem⟩
  set Z : Subgroup ↥R := (N ⊓ (PS : Subgroup Y)).subgroupOf R with hZ
  have hG : IsPGroup 3 ↥R := PS.isPGroup'.to_le inf_le_left
  have hZc : Z ≤ Subgroup.center ↥R := fun x hx =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext
      (Subgroup.mem_center_iff.1 (hNc (Subgroup.mem_subgroupOf.1 hx).1) g.1)
  have hZcard : Nat.card Z ≤ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv]
    exact hNP
  have hπ1 : ∀ x : ↥R, QuotientGroup.mk' N (x : Y) ∈ Ē := fun x => x.2.2
  have hcube : ∀ x : ↥R, x ^ 3 ∈ Z := by
    intro x
    refine Subgroup.mem_subgroupOf.2 ⟨?_, (PS : Subgroup Y).pow_mem x.2.1 3⟩
    apply (QuotientGroup.eq_one_iff _).1
    change QuotientGroup.mk' N ((x : Y) ^ 3) = 1
    rw [map_pow]
    exact hĒe.2 _ (hπ1 x)
  have hcomm : ∀ x y : ↥R, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x y
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · apply (QuotientGroup.eq_one_iff _).1
      change QuotientGroup.mk' N ((x : Y) * y * (x : Y)⁻¹ * (y : Y)⁻¹) = 1
      simp only [map_mul, map_inv]
      have := fi_comm_of_elemAbelian hĒe (hπ1 x) (hπ1 y)
      rw [this]
      group
    · exact (PS : Subgroup Y).mul_mem ((PS : Subgroup Y).mul_mem ((PS : Subgroup Y).mul_mem x.2.1
        y.2.1) ((PS : Subgroup Y).inv_mem x.2.1)) ((PS : Subgroup Y).inv_mem y.2.1)
  set f : ↥R →* Y ⧸ N := (QuotientGroup.mk' N).comp R.subtype with hf
  have hker : f.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker, hZ, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨(QuotientGroup.eq_one_iff _).1 h, x.2.1⟩
    · intro h
      exact (QuotientGroup.eq_one_iff _).2 h.1
  have hrange : f.range = Ē := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact hπ1 x
    · intro he
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.1 (hĒ he)
      refine ⟨⟨p, hp, ?_⟩, hpe⟩
      show QuotientGroup.mk' N p ∈ Ē
      rw [hpe]
      exact he
  have hcardR : Nat.card ↥R = Nat.card Z * 3 ^ r := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker, hrange, hĒc] at h1
    exact h1.symm
  have hcardR' : 3 ^ 4 * Nat.card Z ≤ Nat.card ↥R := by
    rw [hcardR, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr)
  obtain ⟨E, hE, hE27⟩ := i247fi_exists_elemAbelian_card_27 hG hZc hZcard hcube hcomm hcardR'
  refine ⟨E.map R.subtype, Subgroup.map_subtype_le E, fi_elemAbelian_map hE _, ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective, hE27]

theorem fi_lift_mem_weakCore (hNc : N ≤ Subgroup.center Y) (PS : Sylow 3 Y)
    {Ē : Subgroup (Y ⧸ N)} (hĒ : Ē ≤ (PS : Subgroup Y).map (QuotientGroup.mk' N))
    (hĒe : IsElemAbelian 3 Ē) {r : ℕ} (hr : 4 ≤ r) (hĒc : Nat.card Ē = 3 ^ r)
    (hNP : Nat.card ↥(N ⊓ (PS : Subgroup Y)) ≤ 3) {y : Y}
    (hy : QuotientGroup.mk' N y ∈ Subgroup.normalizer (Ē : Set (Y ⧸ N))) :
    y ∈ weakCoreIn 3 (PS : Subgroup Y) ⊤ := by
  obtain ⟨E, hER, hEe, hE27⟩ := fi_exists_rank_three N hNc PS hĒ hĒe hr hĒc hNP
  set R : Subgroup Y := (PS : Subgroup Y) ⊓ Ē.comap (QuotientGroup.mk' N) with hR
  have h3 : 3 ≤ CFSG.Open.pRank 3 R := fi_le_pRank hER hEe hE27
  have h3' : 3 ≤ CFSG.Open.pRank 3 (R ⊔ ((PS : Subgroup Y) ⊓ Subgroup.centralizer (R : Set Y))) :=
    fi_le_pRank (hER.trans le_sup_left) hEe hE27
  unfold weakCoreIn
  refine Subgroup.mem_iSup_of_mem R (Subgroup.mem_iSup_of_mem
    ⟨inf_le_left, by omega, h3'⟩ ?_)
  exact ⟨Subgroup.mem_top y, fi_normalizer_R N hNc PS hĒ hy⟩

end CFSG.HardMathSupport.Solomon.Coordinator

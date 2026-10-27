module

public import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

open Pointwise Subgroup QuotientGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ}

theorem map_conj_smul {H : Type*} [Group H] (f : G →* H) (g : G) (S : Subgroup G) :
    (MulAut.conj g • S).map f = MulAut.conj (f g) • S.map f := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, by simp⟩
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, by simp⟩

theorem conj_smul_eq_iff_mem_normalizer {g : G} {S : Subgroup G} :
    MulAut.conj g • S = S ↔ g ∈ normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.pointwise_smul_def]; rfl

theorem map_subtype_subgroupOf {S M : Subgroup G} (h : S ≤ M) :
    (S.subgroupOf M).map M.subtype = S := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h]

theorem mem_normalizer_comap {H : Type*} [Group H] {f : G →* H} {K : Subgroup H} {g : G}
    (hg : f g ∈ normalizer (K : Set H)) : g ∈ normalizer ((K.comap f : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  simpa using hg (f h)

variable [Finite G] [Fact p.Prime] {N R : Subgroup G} [N.Normal]

section
omit [N.Normal]

theorem inf_eq_bot_of_coprime_natCard (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    R ⊓ N = ⊥ := by
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  exact (Subgroup.disjoint_of_coprime_natCard (by rw [ha]; exact (hN.pow_right a).symm)).eq_bot

end

theorem natCard_sup_eq (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    Nat.card (N ⊔ R : Subgroup G) = Nat.card N * Nat.card R := by
  have h := natCard_mul_mul_natCard_inf N R
  rw [← Subgroup.normal_mul N R, inf_comm, inf_eq_bot_of_coprime_natCard hN hR] at h
  simpa using h

theorem natCard_eq_pow_factorization_natCard_sup
    (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    Nat.card R = p ^ (Nat.card (N ⊔ R : Subgroup G)).factorization p := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  have hNz : ¬ p ∣ Nat.card N := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hN h dvd_rfl)
  rw [natCard_sup_eq hN hR, ha, Nat.factorization_mul Nat.card_pos.ne'
      (pow_ne_zero _ hp.pos.ne'), Finsupp.coe_add, Pi.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hNz, hp.factorization_pow]
  simp

theorem exists_mem_conj_smul_eq_of_conj_smul_sup_eq (hN : (Nat.card N).Coprime p)
    (hR : IsPGroup p R)
    {g : G} (hg : MulAut.conj g • (N ⊔ R : Subgroup G) = N ⊔ R) :
    ∃ n ∈ N, MulAut.conj g • R = MulAut.conj n • R := by
  set M : Subgroup G := N ⊔ R with hM
  have hRM : R ≤ M := le_sup_right
  have hconjRM : MulAut.conj g • R ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hRM
  have h1 : Nat.card (R.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv]
    exact natCard_eq_pow_factorization_natCard_sup hN hR
  have h2 : Nat.card ((MulAut.conj g • R).subgroupOf M)
      = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconjRM).toEquiv, natCard_conj_smul]
    exact natCard_eq_pow_factorization_natCard_sup hN hR
  obtain ⟨m, hm⟩ := exists_conj_smul_eq (p := p) h1 h2
  have hmG : MulAut.conj (m : G) • R = MulAut.conj g • R := by
    have := congrArg (Subgroup.map M.subtype) hm
    rwa [map_conj_smul, map_subtype_subgroupOf hRM, map_subtype_subgroupOf hconjRM] at this
  have hmM : (m : G) ∈ (N : Set G) * (R : Set G) := by
    rw [← Subgroup.normal_mul N R]; exact m.2
  obtain ⟨n, hn, r, hr, hnr⟩ := hmM
  refine ⟨n, hn, ?_⟩
  rw [← hmG, ← hnr, map_mul, mul_smul,
    conj_smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hr)]

theorem normalizer_map_mk'_eq (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    normalizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (normalizer (R : Set G)).map (mk' N) := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map _)
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ g =>
    have hgmk : (mk' N) g ∈ normalizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := hx
    have hgN : g ∈ normalizer ((N ⊔ R : Subgroup G) : Set G) := by
      have := mem_normalizer_comap hgmk
      rwa [QuotientGroup.comap_map_mk'] at this
    obtain ⟨n, hn, hcon⟩ :=
      exists_mem_conj_smul_eq_of_conj_smul_sup_eq hN hR
        (conj_smul_eq_iff_mem_normalizer.2 hgN)
    have hng : n⁻¹ * g ∈ normalizer (R : Set G) := by
      rw [← conj_smul_eq_iff_mem_normalizer, map_mul, mul_smul, hcon, map_inv, ← mul_smul]
      simp
    refine ⟨n⁻¹ * g, hng, ?_⟩
    simp only [mk'_apply, map_mul, map_inv]
    rw [(QuotientGroup.eq_one_iff n).2 hn]
    simp

theorem centralizer_map_mk'_eq (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    centralizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (centralizer (R : Set G)).map (mk' N) := by
  refine le_antisymm ?_ ?_
  swap
  · rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image _ _
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ g =>
    have hxc : (mk' N) g ∈ centralizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := hx
    have hxn : (mk' N) g ∈ normalizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      Subgroup.centralizer_le_normalizer _ hxc
    rw [normalizer_map_mk'_eq hN hR] at hxn
    obtain ⟨h, hh, hhg⟩ := hxn
    simp only [SetLike.mem_coe] at hh
    have hhc : (mk' N) h ∈ centralizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [hhg]; exact hxc
    refine ⟨h, ?_, hhg⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro r hr
    have hrh : h⁻¹ * r * h ∈ R := (Subgroup.mem_normalizer_iff''.1 hh r).1 hr
    rw [Subgroup.mem_centralizer_iff] at hhc
    have hcomm := hhc ((mk' N) r) (Subgroup.mem_map_of_mem _ hr)
    have hquot : ((r : G) : G ⧸ N) = ((h⁻¹ * r * h : G) : G ⧸ N) := by
      have : (mk' N) (h⁻¹ * r * h) = (mk' N) r := by
        simp only [map_mul, map_inv, mul_assoc]
        rw [hcomm, ← mul_assoc]
        simp
      simpa only [mk'_apply] using this.symm
    have hmem : r⁻¹ * (h⁻¹ * r * h) ∈ R ⊓ N :=
      ⟨R.mul_mem (R.inv_mem hr) hrh, QuotientGroup.eq.1 hquot⟩
    rw [inf_eq_bot_of_coprime_natCard hN hR, Subgroup.mem_bot] at hmem
    have hfix : h⁻¹ * r * h = r :=
      mul_left_cancel (a := r⁻¹) (by rw [hmem]; simp)
    calc r * h = h * (h⁻¹ * r * h) := by group
      _ = h * r := by rw [hfix]

theorem comap_normalizer_map_mk'_eq (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    (normalizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap (mk' N)
      = N ⊔ normalizer (R : Set G) := by
  rw [normalizer_map_mk'_eq hN hR, QuotientGroup.comap_map_mk']

theorem comap_centralizer_map_mk'_eq (hN : (Nat.card N).Coprime p) (hR : IsPGroup p R) :
    (centralizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap (mk' N)
      = N ⊔ centralizer (R : Set G) := by
  rw [centralizer_map_mk'_eq hN hR, QuotientGroup.comap_map_mk']

end

end CFSG.FeitThompson

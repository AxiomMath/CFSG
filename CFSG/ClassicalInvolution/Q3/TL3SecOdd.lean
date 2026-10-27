module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot

public section

namespace CFSG.ClassicalInvolution.Q3.OddQ

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]

omit [Finite Y] in
theorem exists_conj_eq_mul {t n : Y} (ht : t * t = 1) (htn : (t * n) * (t * n) = 1)
    (hn : Odd (orderOf n)) : ∃ k : ℕ, n ^ k * t * (n ^ k)⁻¹ = t * n := by
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, ?_⟩
  have hinv : t * n * t = n⁻¹ := by
    calc t * n * t = (t * n) * t := rfl
      _ = (t * n)⁻¹ * ((t * n) * (t * n)) * t := by group
      _ = (t * n)⁻¹ * t := by rw [htn, mul_one]
      _ = n⁻¹ * (t⁻¹ * t) := by group
      _ = n⁻¹ := by rw [inv_mul_cancel, mul_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hpow : ∀ j : ℕ, t * (n ^ j)⁻¹ = n ^ j * t := by
    intro j
    have e : t * n ^ j * t = (n ^ j)⁻¹ := by
      induction j with
      | zero => rw [pow_zero, mul_one, ht, inv_one]
      | succ j ih =>
        calc t * n ^ (j + 1) * t = (t * n ^ j * t) * (t * n * t) := by
              rw [pow_succ]
              calc t * (n ^ j * n) * t = t * n ^ j * (t * t) * n * t := by rw [ht]; group
                _ = (t * n ^ j * t) * (t * n * t) := by group
          _ = (n ^ j)⁻¹ * n⁻¹ := by rw [ih, hinv]
          _ = (n ^ (j + 1))⁻¹ := by group
    calc t * (n ^ j)⁻¹ = t * (t * n ^ j * t) := by rw [e]
      _ = (t * t) * n ^ j * t := by group
      _ = n ^ j * t := by rw [ht, one_mul]
  have hn1 : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
  calc n ^ k * t * (n ^ k)⁻¹ = n ^ k * (t * (n ^ k)⁻¹) := by group
    _ = n ^ k * (n ^ k * t) := by rw [hpow k]
    _ = n ^ (2 * k + 1) * n⁻¹ * t := by
        rw [show 2 * k + 1 = k + k + 1 by ring, pow_succ, pow_add]; group
    _ = n⁻¹ * t := by rw [hn1, one_mul]
    _ = t * n := by
        calc n⁻¹ * t = (t * n * t) * t := by rw [hinv]
          _ = t * n * (t * t) := by group
          _ = t * n := by rw [ht, mul_one]

omit [Finite Y] in
theorem centralizer_mk_eq (hNodd : Odd (Nat.card ↥N)) {t : Y} (ht : t * t = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) =
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have h1 : QuotientGroup.mk' N (g * t * g⁻¹) = QuotientGroup.mk' N t := by
      rw [map_mul, map_mul, map_inv, hx]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    set n : Y := t⁻¹ * (g * t * g⁻¹) with hndef
    have hnN : n ∈ N := by
      have := N.inv_mem h1
      rwa [show ((g * t * g⁻¹)⁻¹ * t)⁻¹ = t⁻¹ * (g * t * g⁻¹) by group] at this
    have hgt : g * t * g⁻¹ = t * n := by rw [hndef]; group
    have htn : (t * n) * (t * n) = 1 := by
      rw [← hgt]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht]; group
    have hnodd : Odd (orderOf n) := by
      have hdvd : orderOf n ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hnN
      exact hNodd.of_dvd_nat hdvd
    obtain ⟨k, hk⟩ := exists_conj_eq_mul ht htn hnodd
    have hmN : n ^ k ∈ N := N.pow_mem hnN k
    refine ⟨(n ^ k)⁻¹ * g, ?_, ?_⟩
    · show (n ^ k)⁻¹ * g ∈ Subgroup.centralizer ({t} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (n ^ k)⁻¹ * g * t * ((n ^ k)⁻¹ * g)⁻¹ = t := by
        calc (n ^ k)⁻¹ * g * t * ((n ^ k)⁻¹ * g)⁻¹ = (n ^ k)⁻¹ * (g * t * g⁻¹) * n ^ k := by
              group
          _ = (n ^ k)⁻¹ * (n ^ k * t * (n ^ k)⁻¹) * n ^ k := by rw [hgt, ← hk]
          _ = t := by group
      calc (n ^ k)⁻¹ * g * t = (n ^ k)⁻¹ * g * t * ((n ^ k)⁻¹ * g)⁻¹ * ((n ^ k)⁻¹ * g) := by
            group
        _ = t * ((n ^ k)⁻¹ * g) := by rw [e]
    · have h2 : QuotientGroup.mk' N (n ^ k) = 1 := (QuotientGroup.eq_one_iff (n ^ k)).mpr hmN
      rw [map_mul, map_inv, h2, inv_one, one_mul]
  · rintro ⟨g', hg', hgg⟩
    have hg'' : g' * t = t * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
    rw [← hgg, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg'']

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [N.Normal] in
theorem inf_eq_bot_of_two {P : Subgroup Y} (hP : IsPGroup 2 ↥P) (hNodd : Odd (Nat.card ↥N)) :
    P ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_isPGroup_of_mem_odd hNodd hx.2
    (hP.to_le (Subgroup.zpowers_le.mpr hx.1))

noncomputable def sylowEquiv (hd : TightDatum R S t) (hNodd : Odd (Nat.card ↥N)) :
    ↥(S : Subgroup R) ≃* ↥((TwistQ.sylowMap N S : Sylow 2 _) :
      Subgroup ↥(R.map (QuotientGroup.mk' N))) :=
  MulEquiv.ofBijective (((QuotientGroup.mk' N).subgroupMap R).subgroupMap (S : Subgroup R))
    ⟨by
      intro a b hab
      have h : QuotientGroup.mk' N ((a : R) : Y) = QuotientGroup.mk' N ((b : R) : Y) := by
        have := congrArg (fun x => ((x : ↥(R.map (QuotientGroup.mk' N))) : Y ⧸ N))
          (congrArg Subtype.val hab)
        exact this
      have hS2 : IsPGroup 2 ↥((S : Subgroup R).map R.subtype) := hd.sylow_core.2.1
      have hSN := inf_eq_bot_of_two hS2 hNodd
      have ha : ((a : R) : Y) ∈ (S : Subgroup R).map R.subtype := ⟨a, a.2, rfl⟩
      have hb : ((b : R) : Y) ∈ (S : Subgroup R).map R.subtype := ⟨b, b.2, rfl⟩
      have := TwistQ.mk_inj hSN ha hb h
      exact Subtype.ext (Subtype.ext this),
     ((QuotientGroup.mk' N).subgroupMap R).subgroupMap_surjective _⟩

theorem datum (hd : TightDatum R S t) (hNodd : Odd (Nat.card ↥N)) :
    TightDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t) := by
  have ht2 : t * t = 1 := t_mul_t hd
  have hcent : R.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)]
  have htN : t ∉ N := by
    intro h
    have hZ : IsPGroup 2 ↥(Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order, pow_one])
    have := Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers t, h⟩
    rw [inf_eq_bot_of_two hZ hNodd, Subgroup.mem_bot] at this
    exact hd.isUniqueInvolution_core.ne_one this
  refine ⟨?_, ?_, ?_, hcent, ?_, ?_⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(sylowEquiv hd hNodd).symm.trans e⟩⟩
  · rw [TwistQ.sylowMap_map_subtype]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hd.order, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htN
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr ?_
    rw [centralizer_mk_eq hNodd ht2]
    exact (Subgroup.map_mono hd.le_normalizer).trans (Subgroup.le_normalizer_map _)
  ·
    set f : ↥R →* ↥(R.map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap R
    have hf : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective R
    have hle : classicalInvolutionOddCore ↥R ≤
        (classicalInvolutionOddCore ↥(R.map (QuotientGroup.mk' N))).comap f := by
      intro x hx
      have hmap : (classicalInvolutionOddCore ↥R).map f ≤
          classicalInvolutionOddCore ↥(R.map (QuotientGroup.mk' N)) :=
        le_sSup ⟨(classicalInvolutionOddCore_normal ↥R).map f hf,
          (CFSG.ComponentClassification.OddCore.odd_card ↥R).of_dvd_nat
            (Subgroup.card_map_dvd _ _)⟩
      exact hmap ⟨x, hx, rfl⟩
    exact hd.twoGroup.of_surjective (QuotientGroup.map _ _ f hle)
      (QuotientGroup.map_surjective_of_surjective _ _ f (QuotientGroup.mk_surjective.comp hf)
        hle)

theorem cls (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    TightCls (Y ⧸ classicalInvolutionOddCore Y)
      (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (TwistQ.sylowMap (classicalInvolutionOddCore Y) S)
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) t) := by
  have hNodd : Odd (Nat.card ↥(classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  obtain ⟨e⟩ := hq8
  refine ⟨⟨(sylowEquiv hd hNodd).symm.trans e⟩, ?_,
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot⟩
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ classicalInvolutionOddCore Y,
      conjSub g (tightCore (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (classicalInvolutionOddCore Y)), ← hgen', Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map]
  refine le_trans ?_ (le_iSup (fun g : Y ⧸ classicalInvolutionOddCore Y =>
    conjSub g (tightCore (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))))
    (QuotientGroup.mk' (classicalInvolutionOddCore Y) g))
  refine conjSub_mono ?_
  unfold tightCore
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
  refine ⟨⟨x, hxR, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

end CFSG.ClassicalInvolution.Q3.OddQ

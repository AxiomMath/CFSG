module

public import CFSG.Goldschmidt.Steps.G312Core
public import CFSG.Walter.Bender1970.S1.PCoreRankTwo
import CFSG.Goldschmidt.Steps.Balance
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.FeitThompson.OddOrderTheorem
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Walter

namespace G312

variable {G : Type} [Group G] [Finite G]

theorem qCoreOf_le_oddCoreOf (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    qCoreOf H p ≤ oddCoreOf H := by
  have : Fact p.Prime := ⟨hp⟩
  refine Subgroup.map_mono (le_sSup ⟨inferInstance, ?_⟩)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := H)).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem qCoreOf_le_centralizer_pResidualOf (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreOf H p ≤
      Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf H) p : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hP
  set F := generalizedFittingSubgroupOf H with hF
  have hFH : F ≤ H := generalizedFittingSubgroupOf_le H
  have hPn : IsNormalIn P H := qCoreOf_normal_in H p
  have hPfit : P ≤ CFSG.fittingSubgroupOf H := qCoreOf_le_fittingSubgroupOf H p hp
  have hPF : P ≤ F := hPfit.trans le_sup_left
  set N : Subgroup F := (Subgroup.centralizer (P : Set G)).subgroupOf F with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro z hz
    have hg : ((g : F) : G) ∈ H := hFH g.2
    have hz' : (g : G)⁻¹ * z * (g : G) ∈ P := by
      simpa using hPn.2 _ (H.inv_mem hg) z hz
    have hc := hn _ hz'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc z * ((g : G) * n * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * z * (g : G)) * n) * (g : G)⁻¹ := by group
      _ = (g : G) * (n * ((g : G)⁻¹ * z * (g : G))) * (g : G)⁻¹ := by rw [hc]
      _ = (g : G) * n * (g : G)⁻¹ * z := by group
  have hFle : F ≤ P ⊔ (Subgroup.centralizer (P : Set G) ⊓ F) := by
    refine sup_le ?_ ?_
    · rw [fittingSubgroupOf_eq_iSup_qCoreOf H]
      refine iSup_le fun q => ?_
      by_cases hqp : q.1.1 = p
      · rw [hqp]
        exact le_sup_left
      · have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
        refine le_sup_of_le_right (le_inf ?_ ?_)
        · exact qCoreOf_centralizer_of_ne H hp hq (Ne.symm hqp)
        · exact (qCoreOf_le_fittingSubgroupOf H q.1.1 hq).trans le_sup_left
    · refine le_sup_of_le_right (le_inf ?_ le_sup_right)
      exact ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp
        (layer_centralizes_fitting H)).trans (Subgroup.centralizer_le hPfit)
  have hquot : IsPGroup p (F ⧸ N) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ P.subgroupOf F ⊔ N := by
        have h1 : x ∈ (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ F)).subgroupOf F := hFle x.2
        rwa [Subgroup.subgroupOf_sup hPF inf_le_right, Subgroup.inf_subgroupOf_right] at h1
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H p) ⟨(y : G), hy⟩
      refine ⟨k, ?_⟩
      have hyk : y ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one,
        ← QuotientGroup.mk_pow, hyk, QuotientGroup.mk_one]
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  have hR := pResidualOf_le_of_normal_index F p N hNn ⟨n, hn⟩
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hR hx
  exact hy

end G312

open G312 in
theorem G312 : S_G312 := by
  intro G _ _ H A hS p hp hp2 hrank
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K := normalClosureIn H A with hKdef
  set O := oddCoreOf H with hOdef
  set H₀ := K ⊔ O with hH₀def
  set P := qCoreOf H p with hPdef
  set F := generalizedFittingSubgroupOf H with hFdef
  set R := pResidualOf F p with hRdef
  have hKH : K ≤ H := Sec8.normalClosureIn_le_self H A
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hH₀H : H₀ ≤ H := sup_le hKH hOH
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hPO : P ≤ O := qCoreOf_le_oddCoreOf H hp hp2
  have hPR : P ≤ Subgroup.centralizer (R : Set G) := qCoreOf_le_centralizer_pResidualOf H hp
  have hPZ : P ≤ H₀ ⊓ Subgroup.centralizer (R : Set G) :=
    le_inf (hPO.trans le_sup_right) hPR
  have hcentbot : P = ⊥ → Subgroup.centralizer (P : Set G) = ⊤ := by
    intro hP₀
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hP₀, SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  by_cases hP₀ : P = ⊥
  · refine ⟨⟨0, by rw [hcentbot hP₀]; exact le_top⟩, hPZ, hPp, fun Q hQZ hQp hPQ => ?_⟩
    refine le_antisymm ?_ hPQ
    exact le_qCoreOf_of_centralizes H hp (hQZ.trans (inf_le_left.trans hH₀H)) hQp
      (by rw [hcentbot hP₀]; exact le_top) (hQZ.trans inf_le_right)
  have hPn : IsNormalIn P H := qCoreOf_normal_in H p
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := le_normalizer_of_isNormalIn hPn
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP₀
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hp2 hPp
  have hDp : IsPGroup p D := hPp.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hrankD : CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 2 := by
    let ι : D →* G := P.subtype.comp D.subtype
    have hι : Function.Injective ι := P.subtype_injective.comp D.subtype_injective
    have hle : (⊤ : Subgroup D).map ι ≤ P := by
      rintro _ ⟨x, -, rfl⟩
      exact (x : P).2
    calc CFSG.Open.pRank p (⊤ : Subgroup D) ≤ CFSG.Open.pRank p ((⊤ : Subgroup D).map ι) :=
          pRank_le_map hp.one_lt ι hι ⊤
      _ ≤ CFSG.Open.pRank p P := pRank_mono hp.one_lt hle
      _ ≤ 2 := hrank
  have hWcard : Nat.card (D ⧸ frattini D) ≤ p ^ 2 :=
    (rank_two_exponent_prime_order_bound hDp hexpD hrankD).2
  let _ : MulDistribMulAction H P := Subgroup.conjMulDistribMulActionOfLeNormalizer H P hHP
  let ρ₀ : H →* MulAut P := MulDistribMulAction.toMulAut H P
  have hρ₀ : ∀ (h : H) (x : P), ((ρ₀ h x : P) : G) = (h : G) * x * (h : G)⁻¹ :=
    fun _ _ => rfl
  let ρ : H →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp ρ₀
  obtain ⟨ζ₀, hζ₀, hUI⟩ := exists_central_involution_mulAut hp2 hWcomm hWpow hWcard
  have hkey : ∀ h : H, (h : G) ∈ H₀ → ∃ m : ℕ, ρ h ^ 2 ^ m ∈ (O.subgroupOf H).map ρ :=
    fun h hh => exists_two_pow_mem hS ρ hζ₀ hUI h hh
  set X₁ := (O.subgroupOf H).map ρ with hX₁def
  have hOodd : Odd (Nat.card (O.subgroupOf H)) := by
    have hOsub : O.subgroupOf H = goldschmidtOddCore H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hOsub]
    have := Balance.odd_card_oddCoreOf H
    rwa [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective] at this
  have hX₁odd : Odd (Nat.card X₁) := Odd.of_dvd_nat hOodd (Subgroup.card_map_dvd _ _)
  have hX₁syl : BenderSuzuki.HasAbelianSylow 2 X₁ := by
    intro S
    have hS1 : Nat.card (S : Subgroup X₁) = 1 := by
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      have hdvd : Nat.card (S : Subgroup X₁) ∣ Nat.card X₁ := Subgroup.card_subgroup_dvd_card _
      rw [hk] at hdvd ⊢
      rcases k with _ | k
      · rfl
      · exfalso
        have h2 : 2 ∣ Nat.card X₁ := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
        exact (Nat.not_even_iff_odd.mpr hX₁odd) (even_iff_two_dvd.mpr h2)
    have : Subsingleton (S : Subgroup X₁) := (Nat.card_eq_one_iff_unique.mp hS1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hpX₁ : ∀ h : H, (h : G) ∈ H₀ → IsPElement p (ρ h) → ρ h ∈ X₁ := by
    intro h hh hhp
    obtain ⟨m, hm⟩ := hkey h hh
    obtain ⟨j, hj⟩ := hhp
    have hcop : Nat.Coprime (2 ^ m) (orderOf (ρ h)) := by
      rw [hj]
      exact Nat.Coprime.pow m j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hu]
    exact X₁.pow_mem hm u
  set ι₀ : H₀ →* H := Subgroup.inclusion hH₀H with hι₀
  set σ₀ : H₀ →* MulAut P := ρ₀.comp ι₀ with hσ₀
  set σ : H₀ →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp σ₀ with hσ
  have hX₁σ : X₁ ≤ σ.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o, (le_sup_right : O ≤ H₀) (Subgroup.mem_subgroupOf.mp ho)⟩, rfl⟩
  have hσsolv : Group.IsSolvable σ.range := by
    set Y := σ.range with hY
    set Y₁ : Subgroup Y := X₁.subgroupOf Y with hY₁
    have hY₁n : Y₁.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hY₁, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := hn
      obtain ⟨h, hh⟩ := g.2
      refine ⟨ι₀ h * o * (ι₀ h)⁻¹, ?_, ?_⟩
      · show _ ∈ O.subgroupOf H
        rw [Subgroup.mem_subgroupOf]
        simpa using Balance.conj_mem_oddCoreOf (ι₀ h).2 (Subgroup.mem_subgroupOf.mp ho)
      · rw [map_mul, map_mul, map_inv, hon]
        change σ h * (n : MulAut (D ⧸ frattini D)) * (σ h)⁻¹ = _
        rw [hh]
        rfl
    have hY₁odd : Odd (Nat.card Y₁) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁σ).toEquiv]
      exact hX₁odd
    have : Group.IsSolvable Y₁ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY₁odd
    have hq : IsPGroup 2 (Y ⧸ Y₁) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨h, hh⟩ := y.2
        obtain ⟨m, hm⟩ := hkey (ι₀ h) h.2
        refine ⟨m, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hY₁, Subgroup.mem_subgroupOf,
          Subgroup.coe_pow, ← hh]
        exact hm
    have : Group.IsNilpotent (Y ⧸ Y₁) := hq.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient Y₁
  have hσ₀solv : Group.IsSolvable σ₀.range := by
    set τ : σ₀.range →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp σ₀.range.subtype
      with hτ
    have hτrange : τ.range = σ.range := by
      rw [hτ, hσ, MonoidHom.range_comp (frattiniAction D) σ₀.range.subtype,
        MonoidHom.range_comp (frattiniAction D) σ₀, Subgroup.range_subtype]
    have : Group.IsSolvable τ.range := by rw [hτrange]; exact hσsolv
    have hkerp : IsPGroup p τ.ker := by
      intro x
      obtain ⟨i, hi⟩ := hker ⟨((x : σ₀.range) : MulAut P), x.2⟩
      refine ⟨i, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hi
    have : Group.IsNilpotent τ.ker := hkerp.isNilpotent
    exact Group.isSolvable_of_ker_le_range τ.ker.subtype τ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  obtain ⟨n, hn⟩ := hσ₀solv.solvable
  refine ⟨⟨n, ?_⟩, hPZ, hPp, fun Q hQZ hQp hPQ => ?_⟩
  · have hmap := map_derivedSeries_eq σ₀.rangeRestrict_surjective n
    rw [hn] at hmap
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : σ₀ x = 1 := by
      have : σ₀.rangeRestrict x ∈ (derivedSeries H₀ n).map σ₀.rangeRestrict := ⟨x, hx, rfl⟩
      rw [hmap, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut P => ((α ⟨y, hy⟩ : P) : G)) hx1
    simp only [MulAut.one_apply] at h
    change (x : G) * y * (x : G)⁻¹ = y at h
    calc y * (x : G) = (x : G) * y * (x : G)⁻¹ * (x : G) := by rw [h]
      _ = (x : G) * y := by group
  refine le_antisymm ?_ hPQ
  set Z := H₀ ⊓ Subgroup.centralizer (R : Set G) with hZdef
  set Zsub : Subgroup H := Z.subgroupOf H with hZsub
  let Mx : Subgroup H :=
    { carrier := {h | h ∈ Zsub ∧ IsPElement p (ρ h)}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Zsub.mul_mem ha hb, ?_⟩
        rw [map_mul]
        exact isPElement_mul_of_le_mulAut hp2 hWcomm hWpow hWcard hX₁syl
          (hpX₁ a (Subgroup.mem_subgroupOf.mp ha).1 hap)
          (hpX₁ b (Subgroup.mem_subgroupOf.mp hb).1 hbp) hap hbp
      one_mem' := ⟨Zsub.one_mem, 0, by rw [map_one, orderOf_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨Zsub.inv_mem ha, n, by rw [map_inv, orderOf_inv, hn]⟩ }
  set M := Mx.map H.subtype with hMdef
  have hMZ : ∀ m ∈ M, m ∈ Z := by
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hm.1
  have hRn : IsNormalIn R H := pResidualOf_generalizedFitting_isNormalIn H p
  have hKn' : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (Sec8.le_normalizer_normalClosureIn H A)
  have hOn' : (O.subgroupOf H).Normal := by
    have hOsub : O.subgroupOf H = goldschmidtOddCore H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hOsub]
    infer_instance
  have hH₀n : (H₀.subgroupOf H).Normal := by
    rw [hH₀def, Subgroup.subgroupOf_sup hKH hOH]
    exact Subgroup.sup_normal _ _
  have hZconj : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z := by
    intro h hh z hz
    refine ⟨?_, ?_⟩
    · have := hH₀n.conj_mem ⟨z, hH₀H hz.1⟩ (Subgroup.mem_subgroupOf.mpr hz.1) ⟨h, hh⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · show h * z * h⁻¹ ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : h⁻¹ * k * h ∈ R := by
        simpa using hRn.2 h⁻¹ (H.inv_mem hh) k hk
      have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
      calc k * (h * z * h⁻¹) = h * ((h⁻¹ * k * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * k * h)) * h⁻¹ := by rw [hc]
        _ = h * z * h⁻¹ * k := by group
  have hMH : IsNormalIn M H := by
    refine ⟨Subgroup.map_subtype_le Mx, ?_⟩
    rintro h hh _ ⟨m, ⟨hmZ, hmp⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.mpr (hZconj h hh m (Subgroup.mem_subgroupOf.mp hmZ))
    · obtain ⟨n, hn⟩ := hmp
      refine ⟨n, ?_⟩
      have hconj : ρ (⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹) = MulAut.conj (ρ ⟨h, hh⟩) (ρ m) := by
        rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
      rw [hconj, MulEquiv.orderOf_eq, hn]
  have hQM : Q ≤ M := by
    intro x hx
    have hxH : x ∈ H := hH₀H (hQZ hx).1
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.mpr (hQZ hx)
    · obtain ⟨n, hn⟩ := hQp ⟨x, hx⟩
      have hdvd : orderOf (ρ ⟨x, hxH⟩) ∣ p ^ n := by
        refine (orderOf_map_dvd ρ _).trans ?_
        rw [Subgroup.orderOf_mk]
        have := orderOf_dvd_of_pow_eq_one hn
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      exact ⟨m, hm⟩
  have hcent : ∀ y ∈ M, Nat.Coprime p (orderOf y) → ∀ m ∈ M, m * y = y * m := by
    rintro _ ⟨y, ⟨hyZ, hyp⟩, rfl⟩ hcop m hm
    have hcop' : Nat.Coprime p (orderOf y) := by
      rwa [orderOf_injective H.subtype H.subtype_injective y] at hcop
    have hρy : ρ y = 1 := by
      obtain ⟨j, hj⟩ := hyp
      have hdvd : orderOf (ρ y) ∣ orderOf y := orderOf_map_dvd ρ y
      rw [hj] at hdvd
      have hj0 : j = 0 := by
        by_contra hj0
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop' ((dvd_pow_self p hj0).trans hdvd))
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    have hρ₀y : ρ₀ y = 1 := by
      have hmem : ρ₀ y ∈ (frattiniAction D).ker := hρy
      obtain ⟨i, hi⟩ := hker ⟨ρ₀ y, hmem⟩
      have hdvd1 : orderOf (ρ₀ y) ∣ p ^ i := by
        have := orderOf_dvd_of_pow_eq_one hi
        rwa [Subgroup.orderOf_mk] at this
      have hdvd2 : orderOf (ρ₀ y) ∣ orderOf y := orderOf_map_dvd ρ₀ y
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd1
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at hdvd2
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop' ((dvd_pow_self p hk0).trans hdvd2))
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    have hyP : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun α : MulAut P => ((α ⟨x, hx⟩ : P) : G)) hρ₀y
      simp only [hρ₀, MulAut.one_apply] at h
      calc x * (y : G) = (y : G) * x * (y : G)⁻¹ * y := by rw [h]
        _ = (y : G) * x := by group
    have hyR : (y : G) ∈ Subgroup.centralizer (R : Set G) := (Subgroup.mem_subgroupOf.mp hyZ).2
    have hyF : (y : G) ∈ Subgroup.centralizer (F : Set G) := by
      have hle : Subgroup.zpowers (y : G) ≤ Subgroup.centralizer (F : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        refine (generalizedFitting_le_qCoreOf_sup_pResidualOf H hp).trans (sup_le ?_ ?_)
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hyP
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hyR
      exact hle (Subgroup.mem_zpowers _)
    have hyFF : (y : G) ∈ F := centralizer_intersection_fstar_le_fstar H ⟨hyF, y.2⟩
    have hyRR : (y : G) ∈ R := by
      apply mem_pResidualOf_of_order_coprime F p hp hyFF
      rw [Subgroup.orderOf_coe]
      exact hcop'
    exact (Subgroup.mem_centralizer_iff.mp (hMZ m hm).2 _ hyRR).symm
  exact le_qCoreOf_of_pPrime_central H hp hMH hcent hQM hQp

end CFSG.Goldschmidt

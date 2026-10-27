module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank
public import CFSG.LocalAnalysis.ComponentClassification.AS81L34Transport
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Fixed
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.EvenSporadicStandard.L34Q8
open CFSG.EvenSporadicStandard.Induction.CoverFix

variable {G : Type} [Group G] [Finite G]

private theorem l34Odd_sylowSetup {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) {e : G}
    (heQ : e ∈ Q) (he : orderOf e = 2) :
    ∃ (T : Sylow 2 ↥Q) (H₁ : Subgroup ↥Q),
      (⟨e, heQ⟩ : ↥Q) ∈ H₁ ∧ H₁ ≤ (T : Subgroup ↥Q) ∧
      (T : Subgroup ↥Q) ≤ centralizer ({⟨e, heQ⟩} : Set ↥Q) ∧
      Open.IsElemAbelian 2 H₁ ∧ Nat.card H₁ = 16 ∧
      (⟨e, heQ⟩ : ↥Q) ∈ ⁅(T : Subgroup ↥Q), (T : Subgroup ↥Q)⁆ ∧
      (T : Subgroup ↥Q).map Q.subtype ≤ Q ⊓ centralizer ({e} : Set G) := by
  have hopen : CFSG.Open.IsQuasisimple ↥Q := ⟨hQ.1.commutator_eq_top, hQ.2.1⟩
  have hL34 : AS81.TypeL34 (RankTwoStandard.rankTwoQuot Q) :=
    Blueprint.LieModel.statedClassicalModel hQL (by decide)
  obtain ⟨c⟩ := AS81.nonempty_l34Cover_of_odd hopen hL34 hQodd
  have hord' : orderOf (⟨e, heQ⟩ : ↥Q) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨e, heQ⟩ : ↥Q)]
    exact he
  have he'2 : (⟨e, heQ⟩ : ↥Q) ^ 2 = 1 := by
    rw [← hord']
    exact pow_orderOf_eq_one _
  have he'1 : (⟨e, heQ⟩ : ↥Q) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨e, heQ⟩ : ↥Q) = 1 := by rw [h, orderOf_one]
    omega
  obtain ⟨T, heT, hTC⟩ := AS81.exists_sylow_le_centralizer c he'2 he'1
  have hkerOdd : Odd (Nat.card c.π.ker) := by
    rw [c.ker_eq]
    exact hQodd.of_dvd_nat (Subgroup.card_map_dvd (center ↥Q) (QuotientGroup.mk' _))
  have hker2 : IsPGroup 2 c.π.ker := c.elem.isPGroup 2 c.π.ker
  obtain ⟨n, hn⟩ := hker2.exists_card_eq
  have hn0 : n = 0 := by
    rcases n with _ | n
    · rfl
    · exfalso
      have hdvd : 2 ∣ Nat.card c.π.ker := by
        rw [hn, pow_succ]
        exact dvd_mul_left 2 _
      exact absurd (hkerOdd.of_dvd_nat hdvd) (by decide)
  have hker1 : Nat.card c.π.ker = 1 := by rw [hn, hn0, pow_zero]
  obtain ⟨H₁, H₂, hH1T, hH2T, hH1elem, hH2elem, hH1card, hH2card, hsup, hinf,
    hcenter, hcommT⟩ := AS81.sylow_structure c T
  have hH1card16 : Nat.card H₁ = 16 := by rw [hH1card, hker1, mul_one]
  have heZ : (⟨e, heQ⟩ : ↥Q) ∈ AS81.centerIn (T : Subgroup ↥Q) := by
    refine ⟨heT, mem_centralizer_iff.mpr ?_⟩
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hTC ht)
  have heTT : (⟨e, heQ⟩ : ↥Q) ∈ ⁅(T : Subgroup ↥Q), (T : Subgroup ↥Q)⁆ := by
    rw [hcommT hopen.1]
    exact heZ
  have heH1 : (⟨e, heQ⟩ : ↥Q) ∈ H₁ := by
    have hmem : (⟨e, heQ⟩ : ↥Q) ∈ H₁ ⊓ H₂ := by rw [hinf]; exact heZ
    exact (mem_inf.mp hmem).1
  have hmapT : (T : Subgroup ↥Q).map Q.subtype ≤ Q ⊓ centralizer ({e} : Set G) := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨t.2, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hTC ht))).symm
  exact ⟨T, H₁, heH1, hH1T, hTC, hH1elem, hH1card16, heTT, hmapT⟩

private theorem l34Odd_memCommutator {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) {e : G}
    (heQ : e ∈ Q) (he : orderOf e = 2) :
    e ∈ ⁅Q ⊓ centralizer ({e} : Set G), Q ⊓ centralizer ({e} : Set G)⁆ := by
  obtain ⟨T, H₁, heH1, hH1T, hTC, hH1elem, hH1card, heTT, hmapT⟩ :=
    l34Odd_sylowSetup hQ hQodd hQL heQ he
  have heTTmap : e ∈ (⁅(T : Subgroup ↥Q), (T : Subgroup ↥Q)⁆).map Q.subtype :=
    Subgroup.mem_map_of_mem Q.subtype heTT
  rw [Subgroup.map_commutator] at heTTmap
  exact Subgroup.commutator_mono hmapT hmapT heTTmap

theorem exists_involution_mem_of_l34Odd {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) :
    ∃ e ∈ Q, orderOf e = 2 := by
  have _ : IsQuasisimple ↥Q := hQ
  have _ : Odd (Nat.card (center ↥Q)) := hQodd
  have hL34 : AS81.TypeL34 (RankTwoStandard.rankTwoQuot Q) :=
    Blueprint.LieModel.statedClassicalModel hQL (by decide)
  have hcard : Nat.card (↥Q ⧸ center ↥Q) = 20160 :=
    AS81.card_rankTwoQuot_of_typeL34 hL34
  have heven : Even (Nat.card ↥Q) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥Q), hcard]
    exact (by decide : Even 20160).mul_right _
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  exact ⟨(e : G), e.2, by rw [Subgroup.orderOf_coe, he]⟩

theorem mem_commutator_inf_centralizer_of_l34Odd {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) {e : G}
    (heQ : e ∈ Q) (he : orderOf e = 2) :
    e ∈ ⁅Q ⊓ centralizer ({e} : Set G), Q ⊓ centralizer ({e} : Set G)⁆ :=
  l34Odd_memCommutator hQ hQodd hQL heQ he

theorem exists_elemAbelian_sixteen_of_l34Odd {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) {e : G}
    (heQ : e ∈ Q) (he : orderOf e = 2) :
    ∃ E : Subgroup G, E ≤ Q ⊓ centralizer ({e} : Set G) ∧ e ∈ E ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 16 := by
  obtain ⟨T, H₁, heH1, hH1T, hTC, hH1elem, hH1card, heTT, hmapT⟩ :=
    l34Odd_sylowSetup hQ hQodd hQL heQ he
  refine ⟨H₁.map Q.subtype, (Subgroup.map_mono hH1T).trans hmapT,
    Subgroup.mem_map_of_mem Q.subtype heH1, ?_, ?_⟩
  · exact hH1elem.map Q.subtype
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hH1card]

theorem three_le_pRank_of_l34Odd {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) :
    3 ≤ pRank 2 ↥Q := by
  obtain ⟨e, heQ, he⟩ := exists_involution_mem_of_l34Odd hQ hQodd hQL
  obtain ⟨E, hEQ, -, hEelem, hEcard⟩ := exists_elemAbelian_sixteen_of_l34Odd hQ hQodd hQL heQ he
  have hE2 : IsElemTwo E := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      exact hEelem.comm hx hy
    · intro x hx
      exact hEelem.mul_self_eq_one hx
  have hE16 : 8 ≤ Nat.card E := by rw [hEcard]; norm_num
  exact (hE2.three_le_pRank hE16).trans (GrS5.pRank_le_of_le (hEQ.trans inf_le_left))

omit [Finite G] in
private theorem l34Odd_existsConjAut {Q : Subgroup G} {b : G} (hb : orderOf b = 2)
    (hbQ : Q.map (MulAut.conj b).toMonoidHom = Q) :
    ∃ α : MulAut ↥Q, (∀ x : ↥Q, ((α x : ↥Q) : G) = b * (x : G) * b⁻¹) ∧ α * α = 1 := by
  have hbQ' : Q.map (↑(MulAut.conj b)) = Q := hbQ
  let α : MulAut ↥Q := ((MulAut.conj b).subgroupMap Q).trans (MulEquiv.subgroupCongr hbQ')
  have hαcoe : ∀ x : ↥Q, ((α x : ↥Q) : G) = b * (x : G) * b⁻¹ := by
    intro x
    simp only [α, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hb2 : b * b = 1 := by
    simpa [pow_two, hb] using pow_orderOf_eq_one b
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    change ((α (α x) : ↥Q) : G) = (x : G)
    rw [hαcoe (α x), hαcoe x]
    calc b * (b * (x : G) * b⁻¹) * b⁻¹ = (b * b) * (x : G) * (b⁻¹ * b⁻¹) := by group
      _ = (x : G) := by
        rw [hb2, one_mul, inv_eq_of_mul_eq_one_right hb2, hb2, mul_one]
  exact ⟨α, hαcoe, hα2⟩

omit [Finite G] in
private theorem l34Odd_fixedMapEq {Q : Subgroup G} {b : G}
    {α : MulAut ↥Q} (hαcoe : ∀ x : ↥Q, ((α x : ↥Q) : G) = b * (x : G) * b⁻¹) :
    (fixed α).map Q.subtype = Q ⊓ centralizer ({b} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have hconj : b * (x : G) * b⁻¹ = (x : G) := by
      rw [← hαcoe x, mem_fixed.mp hx]
    calc (x : G) * b = (b * (x : G) * b⁻¹) * b := by rw [hconj]
      _ = b * (x : G) * (b⁻¹ * b) := by group
      _ = b * (x : G) := by rw [inv_mul_cancel, mul_one]
  · rintro y ⟨hyQ, hyC⟩
    have hyF : (⟨y, hyQ⟩ : ↥Q) ∈ fixed α := by
      rw [mem_fixed]
      refine Subtype.ext ?_
      show ((α ⟨y, hyQ⟩ : ↥Q) : G) = y
      rw [hαcoe]
      have hcomm : y * b = b * y := mem_centralizer_singleton_iff.mp hyC
      calc b * y * b⁻¹ = (y * b) * b⁻¹ := by rw [hcomm]
        _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyQ⟩, hyF, rfl⟩

private theorem l34Odd_involutionCommutatorOfFixed {K : Type} [Group K] [Finite K]
    {α : MulAut K} (h : ¬ Group.IsSolvable ↥(fixed α) ∨ NonabelianTwoIn α) :
    ∃ x ∈ ⁅fixed α, fixed α⁆, orderOf x = 2 := by
  rcases h with hns | hnab
  · set D := CFSG.perfectResidual ↥(fixed α)
    have hchar := CFSG.perfect_residual_characterization (G := ↥(fixed α))
    have hDne : D ≠ ⊥ := fun hbot => hns (hchar.2.2.2.2.2.mp hbot)
    have hDperf : Group.IsPerfect ↥D := hchar.2.2.1
    have hDcomm : D ≤ ⁅(⊤ : Subgroup ↥(fixed α)), ⊤⁆ := by
      have h := iInf_le (fun n => derivedSeries ↥(fixed α) n) 1
      rwa [derivedSeries_one] at h
    have hnotOdd : ¬ Odd (Nat.card ↥D) := by
      intro hodd
      have hnt : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
      exact (@Group.IsPerfect.not_isSolvable ↥D inferInstance hnt hDperf)
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    have heven : Even (Nat.card ↥D) := Nat.not_odd_iff_even.mp hnotOdd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hxcommK : (x : K) ∈ ⁅fixed α, fixed α⁆ := by
      have h := Subgroup.mem_map_of_mem (fixed α).subtype (hDcomm x.2)
      rw [Subgroup.map_commutator] at h
      simpa [Subgroup.map_top, Subgroup.range_subtype] using h
    refine ⟨(x : K), hxcommK, ?_⟩
    rw [Subgroup.orderOf_coe (x : ↥(fixed α)), Subgroup.orderOf_coe x]
    exact hx
  · obtain ⟨P, hPF, hP2, p, hpP, q, hqP, hpq⟩ := hnab
    have hPcomm_ne : ⁅P, P⁆ ≠ ⊥ := by
      intro hbot
      have hab : P ≤ centralizer (P : Set K) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hqp : q * p = p * q := mem_centralizer_iff.mp (hab hpP) q hqP
      exact (Ne.symm hpq) hqp
    set P' : Subgroup K := ⁅P, P⁆ with hP'def
    have hPcomm2 : IsPGroup 2 P' := hP2.to_le (Subgroup.commutator_le_self P)
    have hnt : Nontrivial ↥P' := (Subgroup.nontrivial_iff_ne_bot _).mpr hPcomm_ne
    obtain ⟨n, hnpos, hncard⟩ := (IsPGroup.nontrivial_iff_card hPcomm2).mp hnt
    have hdvd : 2 ∣ Nat.card ↥P' := by
      rw [hncard]
      exact dvd_pow_self 2 hnpos.ne'
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hxcommK : (x : K) ∈ ⁅fixed α, fixed α⁆ :=
      (Subgroup.commutator_mono hPF hPF) x.2
    refine ⟨(x : K), hxcommK, ?_⟩
    rw [Subgroup.orderOf_coe x]
    exact hx

theorem exists_involution_mem_commutator_inf_centralizer_of_l34Odd
    {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hQodd : Odd (Nat.card (center ↥Q))) (hQL : IsL34Type (↥Q ⧸ center ↥Q)) {b : G}
    (hb : orderOf b = 2) (hbQ : Q.map (MulAut.conj b).toMonoidHom = Q) :
    ∃ x ∈ ⁅Q ⊓ centralizer ({b} : Set G), Q ⊓ centralizer ({b} : Set G)⁆, orderOf x = 2 := by
  obtain ⟨α, hαcoe, hα2⟩ := l34Odd_existsConjAut hb hbQ
  have hS : (fixed α).map Q.subtype = Q ⊓ centralizer ({b} : Set G) :=
    l34Odd_fixedMapEq hαcoe
  by_cases hα1 : α = 1
  · obtain ⟨e, heQ, he⟩ := exists_involution_mem_of_l34Odd hQ hQodd hQL
    have hS' : Q ⊓ centralizer ({b} : Set G) = Q := by
      rw [← hS, hα1]
      rw [show fixed (1 : MulAut ↥Q) = ⊤ by ext x; simp [fixed],
        Subgroup.map_top, Subgroup.range_subtype]
    refine ⟨e, ?_, he⟩
    rw [hS', Subgroup.isPerfect_iff.mp hQ.1]
    exact heQ
  · obtain ⟨ψ⟩ := nonempty_equiv_S_of_lieModel hQL
    obtain ⟨π, hπ, hπker⟩ := exists_cover_map (MulEquiv.refl _) ψ
    have hoddker : Odd (Nat.card ↥π.ker) := by rw [hπker]; exact hQodd
    have hcase : ¬ Group.IsSolvable ↥(fixed α) ∨ NonabelianTwoIn α := by
      rcases cover_profile hQ.1 π hπ hπker hα1 hα2 with hns | ⟨-, hnab, -, -⟩ | hnab
      · exact Or.inl hns
      · exact Or.inr (hnab (no_involution_of_odd hoddker))
      · exact Or.inr hnab
    obtain ⟨x, hxcomm, hx⟩ := l34Odd_involutionCommutatorOfFixed hcase
    have hxmap : Q.subtype x ∈ (⁅fixed α, fixed α⁆).map Q.subtype :=
      Subgroup.mem_map_of_mem Q.subtype hxcomm
    rw [Subgroup.map_commutator, hS] at hxmap
    refine ⟨Q.subtype x, hxmap, ?_⟩
    change orderOf (↑x : G) = 2
    rw [Subgroup.orderOf_coe x]
    exact hx

end CFSG.ComponentClassification.GrSLit.L34Sec5S

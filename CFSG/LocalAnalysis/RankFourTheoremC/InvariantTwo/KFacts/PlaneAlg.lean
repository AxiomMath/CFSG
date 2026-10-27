module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

section General

variable {H : Type*} [Group H] [Finite H]

theorem pRank_le_of_isSylowOf {p : ℕ} (hp : p.Prime) {S K : Subgroup H}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) {k : ℕ} (hk : Nat.card S = p ^ k) :
    Open.pRank p K ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEK hE => ?_
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨Q, hQ⟩ := (hEp.comap_subtype (K := K)).exists_le_sylow
  calc Nat.card E = Nat.card (E.subgroupOf K) :=
        Nat.card_congr (subgroupOfEquivOfLe hEK).symm.toEquiv
    _ ≤ Nat.card (Q : Subgroup K) := card_le_of_le hQ
    _ = Nat.card S := by rw [Sylow.card_eq_multiplicity, hS.card_eq]
    _ = p ^ k := hk

theorem pRank_le_two_of_card {p : ℕ} (hp : p.Prime) {D : Subgroup H}
    (hD : Nat.card D = p ^ 2) : Open.pRank p D ≤ 2 :=
  CFSG.SectionRank.pRank_le hp.one_lt fun _ hE _ => hD ▸ card_le_of_le hE

theorem zpowers_eq_of_mem_zpowers {p : ℕ} [Fact p.Prime] {y c : H} (hy : y ^ p = 1) (hc : c ^ p = 1)
    (hy1 : y ≠ 1) (hc1 : c ≠ 1) (h : y ∈ zpowers c) : zpowers y = zpowers c :=
  eq_of_le_of_card_ge (zpowers_le.2 h) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy hy1, orderOf_eq_prime hc hc1])

omit [Finite H] in
theorem map_conj_zpowers_eq_zpowers (g z : H) :
    (zpowers z).map (MulAut.conj g).toMonoidHom = zpowers (g * z * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

namespace Lemma212ConfigGe

variable {n p : ℕ} {P : Sylow p H} {z : H} {D : Subgroup H}

theorem ne_one (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) : z ≠ 1 := fun hz =>
  hp.one_lt.ne (by rw [← h.ord, hz, orderOf_one])

theorem isPGroup (h : Lemma212ConfigGe n p P z D) : IsPGroup p D :=
  IsPGroup.of_card h.card

theorem pRank_eq_two (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) : Open.pRank p D = 2 :=
  le_antisymm (pRank_le_two_of_card hp h.card)
    (CFSG.SectionRank.le_pRank hp.one_lt le_rfl h.elem h.card)

theorem exists_mem_notMem_zpowers (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) :
    ∃ d ∈ D, d ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have := card_le_of_le (show D ≤ zpowers z from fun x hx => hcon x hx)
  rw [h.card, Nat.card_zpowers, h.ord] at this
  nlinarith [hp.two_le]

theorem inf_centralizer_eq_of_isPGroup (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    {R : Subgroup H} (hR : IsPGroup p R) (hDR : D ≤ R) : R ⊓ centralizer (D : Set H) = D := by
  have : Fact p.Prime := ⟨hp⟩
  have hDC : D ≤ centralizer (D : Set H) := le_centralizer_iff_isMulCommutative.mpr h.elem.1
  exact h.sylow.eq_of_le (le_inf hDR hDC) inf_le_right hR.to_inf_left

theorem inf_centralizer_eq (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) :
    (P : Subgroup H) ⊓ centralizer (D : Set H) = D :=
  h.inf_centralizer_eq_of_isPGroup hp P.isPGroup' h.le

theorem exists_mem_normalizer_inf_notMem (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) :
    ∃ t ∈ normalizer (D : Set H) ⊓ (P : Subgroup H), t ∉ D ∧ t ∈ centralizer ({z} : Set H) := by
  have hDP : D < (P : Subgroup H) := lt_of_le_of_ne h.le fun heq =>
    h.notNormal (by rw [← heq]; exact le_normalizer)
  obtain ⟨t, ⟨htP, htN⟩, htD⟩ := SetLike.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hp (P : Subgroup H) D P.isPGroup' hDP)
  exact ⟨t, ⟨htN, htP⟩, htD, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.central
    t htP)⟩

theorem exists_transvection (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) :
    ∃ t : H, (∃ k : ℕ, t ^ (p ^ k) = 1) ∧ t ∈ normalizer (D : Set H) ∧ t * z = z * t ∧
      t ∉ centralizer (D : Set H) := by
  obtain ⟨t, ⟨htN, htP⟩, htD, htz⟩ := h.exists_mem_normalizer_inf_notMem hp
  refine ⟨t, ?_, htN, mem_centralizer_singleton_iff.mp htz, fun htC => htD ?_⟩
  · obtain ⟨k, hk⟩ := P.isPGroup' ⟨t, htP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rw [← h.inf_centralizer_eq hp]
    exact ⟨htP, htC⟩

theorem exists_transvection_of_three_le_pRank (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    {d : H} (hd : d ∈ D) (hrank : 3 ≤ Open.pRank p (centralizer ({d} : Set H))) :
    ∃ t : H, (∃ k : ℕ, t ^ (p ^ k) = 1) ∧ t ∈ normalizer (D : Set H) ∧ t * d = d * t ∧
      t ∉ centralizer (D : Set H) := by
  have hDC : D ≤ centralizer ({d} : Set H) := fun x hx => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨d, hd⟩))
  obtain ⟨S, hS⟩ := (h.isPGroup.comap_subtype (K := centralizer ({d} : Set H))).exists_le_sylow
  set R : Subgroup H := (S : Subgroup (centralizer ({d} : Set H))).map
    (centralizer ({d} : Set H)).subtype
  have hRp : IsPGroup p R := S.isPGroup'.map _
  have hRC : R ≤ centralizer ({d} : Set H) := map_subtype_le _
  have hDR : D ≤ R := fun x hx => ⟨⟨x, hDC hx⟩, hS hx, rfl⟩
  have hRD : D < R := by
    refine lt_of_le_of_ne hDR fun heq => ?_
    have := pRank_le_of_isSylowOf hp (K := centralizer ({d} : Set H)) ⟨S, heq.symm⟩ h.card
    omega
  obtain ⟨t, ⟨htR, htN⟩, htD⟩ := SetLike.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hp R D hRp hRD)
  refine ⟨t, ?_, htN, mem_centralizer_singleton_iff.mp (hRC htR), fun htC => htD ?_⟩
  · obtain ⟨k, hk⟩ := hRp ⟨t, htR⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rw [← h.inf_centralizer_eq_of_isPGroup hp hRp hDR]
    exact ⟨htR, htC⟩

end Lemma212ConfigGe

end General

section Concrete

variable {H : Type} [Group H] [Finite H]

theorem exists_mem_normalizer_zpowers_eq_of_transvections {p : ℕ} [Fact p.Prime] {D : Subgroup H}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {z d : H} (hzD : z ∈ D) (hdD : d ∈ D)
    (hz1 : z ≠ 1) (hd1 : d ≠ 1) (hdz : d ∉ zpowers z) {t₁ t₂ : H}
    (ht₁p : ∃ k : ℕ, t₁ ^ (p ^ k) = 1) (ht₁N : t₁ ∈ normalizer (D : Set H))
    (ht₁z : t₁ * z = z * t₁) (ht₁C : t₁ ∉ centralizer (D : Set H))
    (ht₂p : ∃ k : ℕ, t₂ ^ (p ^ k) = 1) (ht₂N : t₂ ∈ normalizer (D : Set H))
    (ht₂d : t₂ * d = d * t₂) (ht₂C : t₂ ∉ centralizer (D : Set H)) :
    ∀ y ∈ D, y ≠ 1 → ∃ g ∈ normalizer (D : Set H),
      zpowers y = (zpowers z).map (MulAut.conj g).toMonoidHom := by
  have hzp : z ^ p = 1 := hD.2 z hzD
  have hdp : d ^ p = 1 := hD.2 d hdD
  have hzd : z ∉ zpowers d := fun hmem => hdz
    ((zpowers_eq_of_mem_zpowers hzp hdp hz1 hd1 hmem).symm ▸ mem_zpowers d)
  intro y hyD hy1
  by_cases hyd : y ∈ zpowers d
  ·
    have hwD : d * z ∈ D := mul_mem hdD hzD
    have hwz : d * z ∉ zpowers z := fun hmem => hdz (by
      simpa using mul_mem hmem (inv_mem (mem_zpowers z)))
    have hwd : d * z ∉ zpowers d := fun hmem => hzd (by
      simpa using mul_mem (inv_mem (mem_zpowers d)) hmem)
    obtain ⟨k, hk⟩ := exists_pow_conj_zpowers_eq hD hDc hzD hz1 ht₁p ht₁N ht₁z ht₁C hdD hdz hwD hwz
    obtain ⟨j, hj⟩ := exists_pow_conj_zpowers_eq hD hDc hdD hd1 ht₂p ht₂N ht₂d ht₂C hzD hzd hwD hwd
    refine ⟨(t₁ ^ k)⁻¹ * t₂ ^ j, mul_mem (inv_mem (pow_mem ht₁N k)) (pow_mem ht₂N j), ?_⟩
    rw [zpowers_eq_of_mem_zpowers (hD.2 y hyD) hdp hy1 hd1 hyd, map_conj_zpowers_eq_zpowers]
    have h2 := congrArg (Subgroup.map (MulAut.conj (t₁ ^ k)⁻¹).toMonoidHom) (hk.trans hj.symm)
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    convert h2 using 2 <;> simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] <;> group
  ·
    obtain ⟨j, hj⟩ := exists_pow_conj_zpowers_eq hD hDc hdD hd1 ht₂p ht₂N ht₂d ht₂C hzD hzd hyD hyd
    exact ⟨t₂ ^ j, pow_mem ht₂N j, by rw [map_conj_zpowers_eq_zpowers, hj]⟩

namespace Lemma212ConfigGe

variable {n p : ℕ} {P : Sylow p H} {z : H} {D : Subgroup H}

theorem inf_centralizer_singleton_eq (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) {d : H}
    (hd : d ∈ D) (hdz : d ∉ zpowers z) :
    (P : Subgroup H) ⊓ centralizer ({d} : Set H) = D := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (le_inf h.le fun x hx => ?_)
  · rintro x ⟨hxP, hxd⟩
    rw [← h.inf_centralizer_eq hp]
    refine ⟨hxP, mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hy
    have hxz : Commute x z := mem_centralizer_iff.mp h.central x hxP
    have hxd' : Commute x d := mem_centralizer_singleton_iff.mp hxd
    exact ((hxd'.pow_right s).mul_right (hxz.pow_right t)).eq.symm
  · exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨d, hd⟩))

theorem pRank_inf_centralizer_singleton (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) {d : H}
    (hd : d ∈ D) (hdz : d ∉ zpowers z) :
    Open.pRank p ((P : Subgroup H) ⊓ centralizer ({d} : Set H)) = 2 := by
  rw [h.inf_centralizer_singleton_eq hp hd hdz, h.pRank_eq_two hp]

theorem le_three_of_prime_three {P : Sylow 3 H} (h : Lemma212ConfigGe n 3 P z D) : n ≤ 3 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hdz⟩ := h.exists_mem_notMem_zpowers Nat.prime_three
  have h3 := three_le_pRank_inf_centralizer
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds
    P.isPGroup' ((Nat.succ_le_of_lt hn).trans h.rank) (h.le hd) (h.elem.2 d hd)
  have := h.pRank_inf_centralizer_singleton Nat.prime_three hd hdz
  omega

theorem five_le (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D) (hn : 4 ≤ n) :
    5 ≤ p := by
  refine hp.five_le_of_ne_two_of_ne_three hp2 fun hp3 => ?_
  subst hp3
  have := h.le_three_of_prime_three
  omega

theorem exists_mem_normalizer_zpowers_eq_of_three_le_pRank (hp : p.Prime)
    (h : Lemma212ConfigGe n p P z D) {d : H} (hd : d ∈ D) (hdz : d ∉ zpowers z)
    (hrank : 3 ≤ Open.pRank p (centralizer ({d} : Set H))) :
    ∀ y ∈ D, y ≠ 1 → ∃ g ∈ normalizer (D : Set H),
      zpowers y = (zpowers z).map (MulAut.conj g).toMonoidHom := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₁, ht₁p, ht₁N, ht₁z, ht₁C⟩ := h.exists_transvection hp
  obtain ⟨t₂, ht₂p, ht₂N, ht₂d, ht₂C⟩ := h.exists_transvection_of_three_le_pRank hp hd hrank
  exact exists_mem_normalizer_zpowers_eq_of_transvections h.elem h.card h.mem hd (h.ne_one hp)
    (fun hd1 => hdz (hd1 ▸ one_mem _)) hdz ht₁p ht₁N ht₁z ht₁C ht₂p ht₂N ht₂d ht₂C

end Lemma212ConfigGe

end Concrete

theorem sq_ne_one_of_orderOf_eq_pred {p : ℕ} (h5 : 5 ≤ p) {a : ZMod p} (ha : orderOf a = p - 1) :
    a ^ 2 ≠ 1 := by
  intro h
  have := Nat.le_of_dvd two_pos (ha ▸ orderOf_dvd_of_pow_eq_one h)
  omega

end CFSG.LocalAnalysis.RankFourTheoremC

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem IsPlaneDiagonal.exists_sq_ne_one {H : Type*} [Group H] {p : ℕ} (h5 : 5 ≤ p)
    {D : Subgroup H} {z g : H} (h : IsPlaneDiagonal p D z g) :
    ∃ a b : ℕ, a * b % p = 1 ∧ orderOf (a : ZMod p) = p - 1 ∧ (a : ZMod p) ^ 2 ≠ 1 ∧
      (a : ZMod p) ≠ b ∧ g * z * g⁻¹ = z ^ a ∧
      ∀ d ∈ D, d ∉ Subgroup.zpowers z → ∃ c : ℕ, g * d * g⁻¹ = d ^ b * z ^ c := by
  obtain ⟨-, -, a, b, hab, hord, hga, hgd⟩ := h
  have hsq := CFSG.LocalAnalysis.RankFourTheoremC.sq_ne_one_of_orderOf_eq_pred h5 hord
  have hone : (a : ZMod p) * b = 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hab
    rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  exact ⟨a, b, hab, hord, hsq, fun hba => hsq (by rw [sq]; nth_rw 2 [hba]; exact hone), hga, hgd⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

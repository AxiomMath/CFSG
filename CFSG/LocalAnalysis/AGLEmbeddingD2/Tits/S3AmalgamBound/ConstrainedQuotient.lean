module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.MulAutElemAbelianSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ConstraintQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.GroupTheory.PrimeCorefreeQuasisimple
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.GorensteinWalter CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open

section StabQE

variable {Y : Type*} [Group Y]

def stabQE (Q E : Subgroup Y) [Q.Normal] [E.Normal] : Subgroup Y where
  carrier := {x | ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ E}
  one_mem' := fun q _ => by simp
  mul_mem' := fun {x y} hx hy q hq => by
    have h1 : y * q * y⁻¹ * q⁻¹ ∈ E := hy q hq
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ E := hx q hq
    have h3 : x * (y * q * y⁻¹ * q⁻¹) * x⁻¹ ∈ E := ‹E.Normal›.conj_mem _ h1 x
    have := E.mul_mem h3 h2
    convert this using 1
    group
  inv_mem' := fun {x} hx q hq => by
    have hq' : x⁻¹ * q * x ∈ Q := by
      have := ‹Q.Normal›.conj_mem q hq x⁻¹
      simpa using this
    have h := E.inv_mem (hx _ hq')
    convert h using 1
    group

theorem mem_stabQE {Q E : Subgroup Y} [Q.Normal] [E.Normal] {x : Y} :
    x ∈ stabQE Q E ↔ ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ E := Iff.rfl

instance stabQE_normal (Q E : Subgroup Y) [Q.Normal] [E.Normal] : (stabQE Q E).Normal where
  conj_mem x hx y q hq := by
    have hq' : y⁻¹ * q * y ∈ Q := by
      have := ‹Q.Normal›.conj_mem q hq y⁻¹
      simpa using this
    have h1 := ‹E.Normal›.conj_mem _ (hx _ hq') y
    convert h1 using 1
    group

end StabQE

section Kernel

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem false_of_prime_order_mem_stabQE_centralizing (Q E : Subgroup Y) [Q.Normal] [E.Normal]
    (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set Y) ≤ Q) {u : Y}
    (hu : u ∈ stabQE Q E) (hcent : ∀ z ∈ E, u * z * u⁻¹ = z) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hord : orderOf u = q) : False := by
  set R := Subgroup.zpowers u with hR
  have hRs : R ≤ stabQE Q E := (Subgroup.zpowers_le).2 hu
  have hRcard : Nat.card R = q := by rw [hR, Nat.card_zpowers, hord]
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    rw [hRcard, hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq (Fact.out)).2 hqp)
  have hnorm : R ≤ Subgroup.normalizer (Q : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact le_top
  have hQR : ⁅Q, R⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have h := hRs hr x hx
    have := E.inv_mem h
    convert this using 1
    group
  have hER : ⁅E, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hc : Commute u z := by
      have := hcent z hz
      exact (commute_iff_eq _ _).2 (by rw [mul_inv_eq_iff_eq_mul] at this; exact this)
    exact (hc.zpow_left k).eq
  have hdouble : ⁅⁅Q, R⁆, R⁆ = ⊥ := by
    apply le_bot_iff.1
    calc ⁅⁅Q, R⁆, R⁆ ≤ ⁅E, R⁆ := Subgroup.commutator_mono hQR le_rfl
      _ = ⊥ := hER
  have h0 := commutator_eq_bot_of_coprime_double_commutator_eq_bot Q R hnorm hcop hdouble
  have hu' : u ∈ Subgroup.centralizer (Q : Set Y) := by
    have : ⁅R, Q⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h0
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at this
    exact this (Subgroup.mem_zpowers u)
  have huQ : u ∈ Q := hQc hu'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨u, huQ⟩
  have h2 : orderOf u = p ^ k := by
    have : orderOf (⟨u, huQ⟩ : Q) = orderOf u := Subgroup.orderOf_mk _ _
    rw [← this]; exact hk
  rw [hord] at h2
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).1
    (hq.dvd_of_dvd_pow (show q ∣ p ^ k from h2 ▸ dvd_refl q)))

theorem isPGroup_stabQE_inf_centralizer (Q E : Subgroup Y) [Q.Normal] [E.Normal]
    (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set Y) ≤ Q) :
    IsPGroup p ↥(stabQE Q E ⊓ Subgroup.centralizer (E : Set Y)) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hxs, hxc⟩
  have hx : orderOf x = orderOf (⟨x, hxs, hxc⟩ : ↥(stabQE Q E ⊓ Subgroup.centralizer (E : Set Y))) :=
    (Subgroup.orderOf_mk _ _).symm
  rw [← hx]
  have hpos : 0 < orderOf x := orderOf_pos x
  obtain ⟨k, hk⟩ : ∃ k, orderOf x = p ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := p) hpos.ne' ?_⟩
    intro q hq hqd
    by_contra hqp
    have hqf : q.Prime := hq
    set u := x ^ (orderOf x / q) with hu
    have hord : orderOf u = q := by
      rw [hu]; exact orderOf_pow_orderOf_div hpos.ne' hqd
    refine false_of_prime_order_mem_stabQE_centralizing Q E hQ hQc (u := u) ?_ ?_ hqf hqp hord
    · exact (stabQE Q E).pow_mem hxs _
    · intro z hz
      have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.pow_mem _ hxc (orderOf x / q)) z hz
      rw [← hu] at hc
      rw [← hc]; group
  exact ⟨k, hk⟩

theorem isSolvable_stabQE (Q E : Subgroup Y) [Q.Normal] [E.Normal]
    (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set Y) ≤ Q)
    (hE : Group.IsSolvable (MulAut ↥E)) : Group.IsSolvable ↥(stabQE Q E) := by
  have hP := isPGroup_stabQE_inf_centralizer (p := p) Q E hQ hQc
  have : Group.IsNilpotent ↥(stabQE Q E ⊓ Subgroup.centralizer (E : Set Y)) :=
    hP.isNilpotent
  have : Group.IsSolvable ↥(stabQE Q E ⊓ Subgroup.centralizer (E : Set Y)) := inferInstance
  let f : ↥(stabQE Q E ⊓ Subgroup.centralizer (E : Set Y)) →* ↥(stabQE Q E) :=
    Subgroup.inclusion inf_le_left
  let g : ↥(stabQE Q E) →* MulAut ↥E := (MulAut.conjNormal : Y →* MulAut ↥E).comp (stabQE Q E).subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  refine ⟨⟨a.1, a.2, ?_⟩, rfl⟩
  show a.1 ∈ Subgroup.centralizer (E : Set Y)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have := congrArg (fun φ : MulAut ↥E => ((φ ⟨z, hz⟩ : ↥E) : Y)) ha
  simp only [g, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply, MulAut.one_apply] at this
  change a.1 * z * a.1⁻¹ = z at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

end Kernel

section Crit

variable {W : Type*} [Group W] [Finite W]

theorem fittingSubgroup_le_pCore_three (hW : primeComplementCore (G := W) 3 = ⊥) :
    CFSG.fittingSubgroup W ≤ CFSG.pCore 3 W := by
  have hX : CFSG.pPrimeCore 3 W = ⊥ := hW
  rw [CFSG.fitting_eq_sup_pCore W]
  refine iSup_le fun p => ?_
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases hp3 : p.1.1 = 3
  · rw [hp3]
  · have : Fact p.1.1.Prime := ⟨hp⟩
    have hle : CFSG.pCore p.1.1 W ≤ CFSG.pPrimeCore 3 W := by
      refine CFSG.GroupTheory.le_pPrimeCore_of_normal CFSG.pCore_normal
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => hp3 ?_)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p.1.1) (G := W))
      rw [hk] at h3
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    rw [hX, le_bot_iff] at hle
    rw [hle]
    exact bot_le

theorem centralizer_pCore_le_pCore_of_solvable (hW : primeComplementCore (G := W) 3 = ⊥)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer (CFSG.pCore 3 W : Set W))) :
    Subgroup.centralizer (CFSG.pCore 3 W : Set W) ≤ CFSG.pCore 3 W := by
  set P := CFSG.pCore 3 W with hP
  have hDn : (Subgroup.centralizer (P : Set W)).Normal := Subgroup.normal_centralizer
  have hF : CFSG.fittingSubgroupOf (Subgroup.centralizer (P : Set W)) ≤ P :=
    (CFSG.fittingSubgroupOf_le_fittingSubgroup _ hDn).trans (fittingSubgroup_le_pCore_three hW)
  have h12 := CFSG.GorensteinWalter.fact_1_2_centralizer_fitting_le_fitting
    (Subgroup.centralizer (P : Set W)) hsolv
  intro x hx
  refine hF (h12 ⟨hx, ?_⟩)
  exact Subgroup.centralizer_le hF hx

end Crit

section Main

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_of_isPGroup_of_map_mem_coprime {N Q : Subgroup X} [N.Normal] (hQ : IsPGroup 3 Q)
    {K : Subgroup (X ⧸ N)} (hK : Nat.Coprime 3 (Nat.card K)) {c : X} (hcQ : c ∈ Q)
    (hc : QuotientGroup.mk' N c ∈ K) : c ∈ N := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨c, hcQ⟩
  have h1 : orderOf c = 3 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_mk _ _).symm
  have hd1 : orderOf (QuotientGroup.mk' N c) ∣ 3 ^ k := h1 ▸ orderOf_map_dvd _ _
  have hd2 : orderOf (QuotientGroup.mk' N c) ∣ Nat.card K := by
    exact Subgroup.orderOf_dvd_natCard K hc
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' N c)) (Nat.card K) :=
    (Nat.Coprime.pow_left k hK).coprime_dvd_left hd1
  have := Nat.Coprime.eq_one_of_dvd hcop hd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

theorem hasPrimeConstraint_three_quotient (Q N : Subgroup X) [Q.Normal] [N.Normal]
    (hQ : IsPGroup 3 Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hN : ∀ E : Subgroup X, E ≤ N → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9) :
    HasPrimeConstraint (G := X ⧸ N) 3 := by
  set K : Subgroup (X ⧸ N) := primeComplementCore (G := X ⧸ N) 3 with hKdef
  set φ : X →* (X ⧸ N) ⧸ K := (QuotientGroup.mk' K).comp (QuotientGroup.mk' N) with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective K).comp (QuotientGroup.mk'_surjective N)
  have hφapp : ∀ x, φ x = QuotientGroup.mk' K (QuotientGroup.mk' N x) := fun x => rfl
  refine ⟨CFSG.pCore 3 ((X ⧸ N) ⧸ K), CFSG.pCore_normal, CFSG.pCore_isPGroup, ?_⟩
  set E : Subgroup X := Q ⊓ N with hE
  have hEQ : E ≤ Q := inf_le_left
  have hEN : E ≤ N := inf_le_right
  have hEab := hN E hEN (hQ.to_le hEQ)
  have : Finite ↥E := inferInstance
  have hAut : Group.IsSolvable (MulAut ↥E) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.mulAut_elemAbelian_three_solvable hEab.1 hEab.2
  have hRsolv : Group.IsSolvable ↥(stabQE Q E) := isSolvable_stabQE (p := 3) Q E hQ hQc hAut
  have hQP : ∀ q ∈ Q, φ q ∈ CFSG.pCore 3 ((X ⧸ N) ⧸ K) := by
    intro q hq
    have hn : (Q.map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
    have hp : IsPGroup 3 (Q.map φ) := hQ.map φ
    exact (le_sSup (show Q.map φ ∈ {S : Subgroup _ | S.Normal ∧ IsPGroup 3 S} from ⟨hn, hp⟩))
      ⟨q, hq, rfl⟩
  have hlift : ∀ g : X, φ g ∈ Subgroup.centralizer (CFSG.pCore 3 ((X ⧸ N) ⧸ K) : Set _) →
      g ∈ stabQE Q E := by
    intro g hg q hq
    have hcom := Subgroup.mem_centralizer_iff.1 hg (φ q) (hQP q hq)
    have hcQ : g * q * g⁻¹ * q⁻¹ ∈ Q :=
      Q.mul_mem (‹Q.Normal›.conj_mem q hq g) (Q.inv_mem hq)
    have hker : φ (g * q * g⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, ← hcom]
      group
    have hmem : QuotientGroup.mk' N (g * q * g⁻¹ * q⁻¹) ∈ K := by
      rw [hφapp, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hker
      exact hker
    exact ⟨hcQ, mem_of_isPGroup_of_map_mem_coprime hQ (primeComplementCore_coprime 3) hcQ hmem⟩
  have hsolv : Group.IsSolvable
      ↥(Subgroup.centralizer (CFSG.pCore 3 ((X ⧸ N) ⧸ K) : Set ((X ⧸ N) ⧸ K))) := by
    have hrange : Group.IsSolvable ↥((φ.domRestrict (stabQE Q E)).range) :=
      Group.isSolvable_of_surjective (φ.domRestrict (stabQE Q E)).rangeRestrict_surjective
    refine Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion (show Subgroup.centralizer
        (CFSG.pCore 3 ((X ⧸ N) ⧸ K) : Set ((X ⧸ N) ⧸ K)) ≤ (φ.domRestrict (stabQE Q E)).range from ?_)))
      (Subgroup.inclusion_injective _)
    intro d hd
    obtain ⟨g, rfl⟩ := hφs d
    exact ⟨⟨g, hlift g hd⟩, rfl⟩
  exact centralizer_pCore_le_pCore_of_solvable (primeComplementCore_quotient_eq_bot 3) hsolv

end Main

section Lift

variable {X Y : Type*} [Group X] [Group Y]

theorem isElemAbelian_map {p : ℕ} (f : X →* Y) {E : Subgroup X} (h : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map h _

theorem exists_isPGroup_map_eq [Finite X] (f : X →* Y) (A : Subgroup X) (E : Subgroup Y)
    (hE : IsPGroup 3 E) (hle : E ≤ A.map f) :
    ∃ P : Subgroup X, P ≤ A ∧ IsPGroup 3 P ∧ P.map f = E := by
  set S : Subgroup X := A ⊓ E.comap f with hS
  have hmem : ∀ s : S, f s.1 ∈ E := fun s => s.2.2
  let g : ↥S →* ↥E := (f.domRestrict S).codRestrict E hmem
  have hg : Function.Surjective g := by
    intro e
    obtain ⟨a, haA, ha⟩ := hle e.2
    refine ⟨⟨a, haA, by show f a ∈ E; rw [ha]; exact e.2⟩, ?_⟩
    exact Subtype.ext ha
  have hTop : IsPGroup 3 (⊤ : Subgroup ↥E) :=
    hE.of_injective (Subgroup.topEquiv (G := ↥E)).toMonoidHom
      (Subgroup.topEquiv (G := ↥E)).injective
  have hP0 : (⊤ : Subgroup ↥E).index ≠ 0 := by simp
  let P0 : Sylow 3 ↥E := hTop.toSylow (by simp)
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hg 3 P0
  have hQtop : (Q : Subgroup ↥S).map g = ⊤ := by
    have := congrArg (fun R : Sylow 3 ↥E => (R : Subgroup ↥E)) hQ
    simpa [P0] using this
  refine ⟨(Q : Subgroup ↥S).map S.subtype, ?_, Q.2.map _, ?_⟩
  · rintro _ ⟨s, _, rfl⟩
    exact s.2.1
  · ext y
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact hmem s
    · intro hy
      have : (⟨y, hy⟩ : ↥E) ∈ (Q : Subgroup ↥S).map g := by rw [hQtop]; trivial
      obtain ⟨s, hs, hsg⟩ := this
      exact ⟨s.1, ⟨s, hs, rfl⟩, congrArg Subtype.val hsg⟩

end Lift

theorem small_threeSubgroups_map {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] (f : X →* Y)
    (N : Subgroup X)
    (hN : ∀ E : Subgroup X, E ≤ N → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9) :
    ∀ E : Subgroup Y, E ≤ N.map f → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9 := by
  intro E hE hEp
  obtain ⟨P, hPN, hPp, hPE⟩ := exists_isPGroup_map_eq f N E hEp hE
  obtain ⟨hab, hcard⟩ := hN P hPN hPp
  subst hPE
  have hdvd : Nat.card ↥(P.map f) ∣ Nat.card P := P.card_map_dvd f
  have hpos : 0 < Nat.card ↥P := Nat.card_pos
  have h2 : IsElemAbelian 3 (P.map f) := isElemAbelian_map f hab
  exact ⟨h2, (Nat.le_of_dvd hpos hdvd).trans hcard⟩

section Transfer

variable {X Y : Type*} [Group X] [Group Y]

theorem hasPrimeConstraint_of_surjective_of_coprime_ker_rev [Finite X] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    (h : HasPrimeConstraint (G := Y) p) : HasPrimeConstraint (G := X) p := by
  obtain ⟨N, hNn, hNp, hNc⟩ := h
  set e := quotientEquivOfCoprimeKer f hf hker
  refine ⟨N.map e.symm.toMonoidHom, hNn.map e.symm.toMonoidHom e.symm.surjective,
    hNp.map e.symm.toMonoidHom, ?_⟩
  intro c hc
  have hc' : e c ∈ Subgroup.centralizer (N : Set (Y ⧸ primeComplementCore (G := Y) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := Subgroup.mem_centralizer_iff.1 hc (e.symm n) ⟨n, hn, rfl⟩
    apply e.symm.injective
    simpa using this
  have := hNc hc'
  exact ⟨e c, this, by simp⟩

end Transfer

section Final

variable {X : Type*} [Group X] [Finite X]

theorem isPConstrained_three_quotient_of_small_normal (N : Subgroup X) [N.Normal]
    (hX : CFSG.ABGLocalTools.IsPConstrained 3 X)
    (hN : ∀ E : Subgroup X, E ≤ N → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9) :
    CFSG.ABGLocalTools.IsPConstrained 3 (X ⧸ N) := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_iff_hasPrimeConstraint] at hX ⊢
  obtain ⟨Qb, hQn, hQp, hQc⟩ := hX
  set L : Subgroup X := primeComplementCore (G := X) 3 with hL
  set π : X →* X ⧸ L := QuotientGroup.mk' L with hπ
  set Nb : Subgroup (X ⧸ L) := N.map π with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective L)
  have hNbsmall := small_threeSubgroups_map π N hN
  have h1 := hasPrimeConstraint_three_quotient Qb Nb hQp hQc hNbsmall
  have hle : N ≤ Nb.comap π := Subgroup.le_comap_map π N
  set f : X ⧸ N →* (X ⧸ L) ⧸ Nb := QuotientGroup.map N Nb π hle with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y'
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker : f.ker ≤ L.map (QuotientGroup.mk' N) := by
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [MonoidHom.mem_ker] at hw
    have : π x ∈ Nb := by
      have h2 : ((π x : X ⧸ L) : (X ⧸ L) ⧸ Nb) = 1 := hw
      exact (QuotientGroup.eq_one_iff _).1 h2
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 this
    have hxn : x * n⁻¹ ∈ L := by
      have : π (x * n⁻¹) = 1 := by rw [map_mul, map_inv, ← hnx, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    refine ⟨x * n⁻¹, hxn, ?_⟩
    have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).2 hn
    have : QuotientGroup.mk' N (x * n⁻¹) = QuotientGroup.mk' N x := by
      rw [map_mul, map_inv, hn', inv_one, mul_one]
    exact this
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    refine (primeComplementCore_coprime (G := X) 3).of_dvd_right ?_
    have h1 : Nat.card f.ker ∣ Nat.card ↥(L.map (QuotientGroup.mk' N)) := Subgroup.card_dvd_of_le hker
    exact h1.trans (L.card_map_dvd _)
  exact hasPrimeConstraint_of_surjective_of_coprime_ker_rev f hfs hcop h1

end Final

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

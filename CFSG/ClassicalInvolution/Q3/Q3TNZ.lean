module

public import CFSG.ClassicalInvolution.Q3.Q3TNGen
public import CFSG.ClassicalInvolution.Q3.Q3SBasic
public import CFSG.ClassicalInvolution.Q3.Q3UTight
public import CFSG.ClassicalInvolution.Q3.Q3UFix
public import CFSG.ClassicalInvolution.Q3.Subnormal
public import CFSG.ClassicalInvolution.LBalance.Glauberman
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Normalizes
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.ClassicalInvolution.Generic.StepDefs
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem commute_of_mem_inf_centralizer {E : Subgroup Y} {a b : Y}
    (ha : a ∈ E ⊓ Subgroup.centralizer (E : Set Y))
    (hb : b ∈ E ⊓ Subgroup.centralizer (E : Set Y)) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp hb.2 a ha.1

theorem isPGroup_two_of_comm_normal (hO : classicalInvolutionOddCore Y = ⊥) {Z : Subgroup Y}
    [Z.Normal] (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : IsPGroup 2 Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative Z := ⟨⟨fun x y => Subtype.ext (hZ x x.2 y y.2)⟩⟩
  have hcore : CFSG.pPrimeCore 2 Y = ⊥ := by
    rw [pPrimeCore_two_eq_oddCore]
    exact hO
  exact CFSG.isPGroup_of_nilpotent_normal Z inferInstance CommGroup.isNilpotent hcore

theorem mem_of_isPGroup_of_ne_bot {L : Subgroup Y} {z : Y} (hz : IsClassicalMember3 L z)
    {A : Subgroup Y} (hA : IsPGroup 2 A) (hne : L ⊓ A ≠ ⊥) : z ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (L ⊓ A : Subgroup Y) := by
    have hp : IsPGroup 2 (L ⊓ A : Subgroup Y) := hA.to_le inf_le_right
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hne (Subgroup.eq_bot_of_card_eq _ hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw' : orderOf (w : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwz : (w : Y) = z := hz.eq_of_orderOf_eq_two w.2.1 hw'
  rw [← hwz]
  exact w.2.2

theorem eq_bot_of_inf_centralizer_eq_bot {A : Subgroup Y} (hA : IsPGroup 2 A) {t : Y}
    (ht : t * t = 1) (htA : ∀ x ∈ A, t * x * t⁻¹ ∈ A)
    (hfix : A ⊓ Subgroup.centralizer ({t} : Set Y) = ⊥) : A = ⊥ := by
  by_contra hne
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hne (Subgroup.eq_bot_of_card_eq _ hn)
  have hev : Even (Nat.card A) := by
    rw [hn]
    exact (Nat.even_pow' hn0).mpr even_two
  have h := Balance.LocalBalance.even_card_inf_centralizer_of_even ht htA hev
  rw [hfix, Subgroup.card_bot] at h
  exact Nat.not_even_one h

omit [Finite Y] in
theorem isPGroup_zpowers_of_pow_eq_one {p k : ℕ} (hp : p.Prime) {g : Y} (hg : g ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem le_centralizer_center_layerOrbit (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} (hTL : T ⊔ L = ⊤)
    (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) :
    L ≤ Subgroup.centralizer
      ((layerOrbit L T ⊓ Subgroup.centralizer (layerOrbit L T : Set Y) : Subgroup Y) : Set Y) := by
  set E := layerOrbit L T with hE
  set Z₁ : Subgroup Y := E ⊓ Subgroup.centralizer (E : Set Y) with hZ₁
  have hEn : E.Normal := layerOrbit_normal hTL
  have hZn : Z₁.Normal := Subgroup.normal_inf_normal _ _
  have hZc : ∀ a ∈ Z₁, ∀ b ∈ Z₁, a * b = b * a := fun a ha b hb =>
    commute_of_mem_inf_centralizer ha hb
  have hZ2 : IsPGroup 2 Z₁ := isPGroup_two_of_comm_normal hO hZc
  have hzZ : z ∉ Z₁ := by
    intro h
    apply hTz
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h.2 t (le_layerOrbit ht)
  have hLZ : L ⊓ Z₁ = ⊥ := by
    by_contra hne
    exact hzZ (mem_of_isPGroup_of_ne_bot hz hZ2 hne)
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  set N : Subgroup Y := Z₁ ⊓ C with hN
  have hNn : (N.subgroupOf C).Normal := by
    rw [hN, Subgroup.inf_subgroupOf_right]
    infer_instance
  refine le_of_forall_oddPrimePow_mem hz fun g hgL p k hp hp2 hg => ?_
  have : Fact p.Prime := ⟨hp⟩
  set P := Subgroup.zpowers g with hP
  have hPp : IsPGroup p P := isPGroup_zpowers_of_pow_eq_one hp hg
  have hPL : P ≤ L := (Subgroup.zpowers_le).mpr hgL
  have hp2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hcop : ¬ p ∣ Nat.card N := by
    obtain ⟨j, hj⟩ := (hZ2.to_le inf_le_left : IsPGroup 2 N).exists_card_eq
    rw [hj]
    intro h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j hp2') h)
  have h1 : ⁅N, P⁆ ≤ L :=
    commutator_le_of_isSubnormal hp hz.subnormal inf_le_right hNn hcop hPL hPp
  have h2 : ⁅N, P⁆ ≤ Z₁ :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans (Subgroup.commutator_le_left Z₁ P)
  have hNg : ∀ a ∈ N, a * g = g * a := by
    intro a ha
    have hmem : ⁅a, g⁆ ∈ L ⊓ Z₁ :=
      ⟨h1 (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers g)),
        h2 (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers g))⟩
    rw [hLZ, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  set A : Subgroup Y := ⁅P, Z₁⁆ with hA
  have hAZ : A ≤ Z₁ := Subgroup.commutator_le_right P Z₁
  have hPZ : P ≤ Subgroup.normalizer (Z₁ : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]
    exact le_top
  have hcopPZ : Nat.Coprime (Nat.card P) (Nat.card Z₁) := by
    obtain ⟨i, hi⟩ := hPp.exists_card_eq
    obtain ⟨j, hj⟩ := hZ2.exists_card_eq
    rw [hi, hj]
    exact Nat.Coprime.pow i j hp2'
  have hAC : A ⊓ Subgroup.centralizer (P : Set Y) = ⊥ :=
    CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hZc hPZ hcopPZ
  have hfix : A ⊓ C = ⊥ := by
    refine le_bot_iff.mp fun a ha => ?_
    rw [← hAC]
    refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hNg a ⟨hAZ ha.1, ha.2⟩).symm n).eq
  have hgz : g * z = z * g := hz.commute_involution hgL
  have hzA : ∀ x ∈ A, z * x * z⁻¹ ∈ A := by
    have hPmap : P.map (MulAut.conj z).toMonoidHom = P := by
      rw [hP, MonoidHom.map_zpowers]
      simp [MulAut.conj_apply, ← hgz]
    have hZmap : Z₁.map (MulAut.conj z).toMonoidHom = Z₁ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hZn.conj_mem y hy z
      · intro hx
        refine ⟨z⁻¹ * x * z, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := hZn.conj_mem x hx z⁻¹
        simpa using this
    have hAmap : A.map (MulAut.conj z).toMonoidHom = A := by
      rw [hA, Subgroup.map_commutator, hPmap, hZmap]
    intro x hx
    have : (MulAut.conj z).toMonoidHom x ∈ A.map (MulAut.conj z).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rwa [hAmap] at this
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz.sq_eq_one
  have hAbot : A = ⊥ := eq_bot_of_inf_centralizer_eq_bot (hZ2.to_le hAZ) hzz hzA hfix
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hmem : ⁅g, a⁆ ∈ A := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers g) ha
  rw [hAbot, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm

theorem inf_centralizer_le_center (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} (hT : IsComponentOf T ⊤)
    (hTL : T ⊔ L = ⊤) (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) :
    T ⊓ Subgroup.centralizer (T : Set Y) ≤ Subgroup.center Y := by
  intro a ha
  have hTc : IsComponent T := (isComponent_iff_open T).mpr hT
  have hEa : layerOrbit L T ≤ Subgroup.centralizer ({a} : Set Y) := by
    refine iSup₂_le fun l _ => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases heq : conjSub l T = T
    · rw [heq] at hy
      exact Subgroup.mem_centralizer_iff.mp ha.2 y hy
    · exact commute_of_ne_isComponent (isComponent_map_mulEquiv (MulAut.conj l) hTc) hTc heq hy
        ha.1
  have haZ : a ∈ layerOrbit L T ⊓ Subgroup.centralizer (layerOrbit L T : Set Y) :=
    ⟨le_layerOrbit ha.1, Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hEa hh)⟩
  have hLa := le_centralizer_center_layerOrbit hO hz hTL hTz
  have hle : T ⊔ L ≤ Subgroup.centralizer ({a} : Set Y) := by
    refine sup_le (fun t ht => ?_) (fun l hl => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp ha.2 t ht
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hLa hl) a haZ).symm
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hTL ▸ Subgroup.mem_top y))

end CFSG.ClassicalInvolution.Q3.Q3T

module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.EvenBN.Common.StandardNormalClosure
import CFSG.Adapters.LieModelSimple
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Setting
public import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement

section Quotient

variable {G : Type} [Group G]

@[expose] def zpowersC (a : G) : Subgroup (centralizer ({a} : Set G)) :=
  (zpowers a).subgroupOf (centralizer ({a} : Set G))

theorem zpowersC_comm {a : G} {n : centralizer ({a} : Set G)} (hn : n ∈ zpowersC a)
    (x : centralizer ({a} : Set G)) : n * x = x * n := by
  have hn' : (n : G) ∈ zpowers a := hn
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn'
  have hxa : Commute (x : G) a := mem_centralizer_singleton_iff.1 x.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
  exact (hxa.zpow_right k).eq.symm

instance (a : G) : (zpowersC a).Normal :=
  ⟨fun n hn g => by rw [← zpowersC_comm hn g, mul_inv_cancel_right]; exact hn⟩

abbrev CBar (a : G) : Type := centralizer ({a} : Set G) ⧸ zpowersC a

@[expose] def GomiOnePConclusion (a : G) : Prop :=
  LieModel (genFittingLayer (CBar a)) .PSp 2 2 2 ∧
    centralizer (genFittingLayer (CBar a) : Set (CBar a)) = standardComponentOddCore (CBar a)

end Quotient

section Lift

variable {X Y : Type} [Group X] [Group Y]

theorem commutator_self_le (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem perfect_commutator_of_central (π : X →* Y) (hcent : ∀ n ∈ π.ker, ∀ x : X, n * x = x * n)
    {P : Subgroup X} (hPerf : ⁅P.map π, P.map π⁆ = P.map π) :
    ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⁅P, P⁆ ∧ (⁅P, P⁆).map π = P.map π := by
  have hmap : (⁅P, P⁆).map π = P.map π := by rw [map_commutator, hPerf]
  refine ⟨le_antisymm (commutator_self_le _) ?_, hmap⟩
  have hdec : ∀ p ∈ P, ∃ m ∈ ⁅P, P⁆, ∃ n ∈ π.ker, p = m * n := by
    intro p hp
    obtain ⟨m, hm, hmp⟩ : π p ∈ (⁅P, P⁆).map π := hmap ▸ mem_map_of_mem π hp
    refine ⟨m, hm, m⁻¹ * p, ?_, by rw [mul_inv_cancel_left]⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmp, inv_mul_cancel]
  rw [Subgroup.commutator_le]
  intro p hp q hq
  obtain ⟨m, hm, n, hn, rfl⟩ := hdec p hp
  obtain ⟨m', hm', n', hn', rfl⟩ := hdec q hq
  rw [Data.Hyp.commutatorElement_mul_mul_eq (hcent n hn m') (hcent n hn n') (hcent n' hn' m)]
  exact commutator_mem_commutator hm hm'

end Lift

section Symplectic

theorem isSimpleGroup_of_lieModel_PSp {J : Type} [Group J] {f : ℕ}
    (h : LieModel J .PSp 2 2 f) : IsSimpleGroup J :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour in
theorem exists_four_of_lieModel_PSp {J : Type} [Group J] (h : LieModel J .PSp 2 2 2) :
    ∃ E : Subgroup J, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_lieModel h
  have : CharP K 2 := finite_field_prime_power_characteristic (K := K) Nat.prime_two
    (by norm_num) hK
  let τ₁ : Multiplicative K →* CFSG.Assembly.LowTwoRank.StatedSp 2 K :=
    { toFun := fun b => tauS (Multiplicative.toAdd b) 0 0
      map_one' := tauS_zero
      map_mul' := fun b b' => by
        rw [tauS_mul_tauS, add_zero]
        rfl }
  have hinj : Function.Injective τ₁ := by
    intro b b' hbb
    have h1 := congrArg (fun x : CFSG.Assembly.LowTwoRank.StatedSp 2 K =>
      ((x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inr 0)) hbb
    simp only [τ₁, MonoidHom.coe_mk, OneHom.coe_mk, coe_tauS] at h1
    have h2 : Multiplicative.toAdd b = Multiplicative.toAdd b' := by
      simpa [SymplecticFour.sym2] using h1
    exact Multiplicative.toAdd.injective h2
  let f : Multiplicative K →* J := e.symm.toMonoidHom.comp τ₁
  have hfinj : Function.Injective f := e.symm.injective.comp hinj
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, b, rfl⟩ := x
    obtain ⟨_, b', rfl⟩ := y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have hb : b ^ 2 = 1 := by
      rw [sq]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]
    rw [hb, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, hK]
    norm_num

end Symplectic

section Standard

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_pow_two_pow {A B : Type*} [Group A] [Group B] [Finite B] (π : A →* B)
    {x : A} {k : ℕ} (hx : x ^ 2 ^ k = 1) {O : Subgroup B} (hO : Odd (Nat.card O))
    (hxO : π x ∈ O) : π x = 1 := by
  have h1 : orderOf (π x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (π x) ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk (π x) hxO]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  have h3 : orderOf (π x) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour in
theorem exists_standard_of_gomiOneP {a : G} (ha : orderOf a = 2) (h1P : GomiOnePConclusion a) :
    ∃ L' : Subgroup G, standardComponentIsStandard L' ∧ center L' = ⊥ ∧
      LieModel L' .PSp 2 2 2 ∧ L' ≤ centralizer ({a} : Set G) ∧
      ∃ S : Sylow 2 (centralizer (L' : Set G)),
        (S : Subgroup (centralizer (L' : Set G))).map (centralizer (L' : Set G)).subtype =
          zpowers a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({a} : Set G) with hX
  set N := zpowersC a with hN
  set π := QuotientGroup.mk' N with hπ
  set E := genFittingLayer (CBar a) with hE
  set P : Subgroup X := E.comap π with hP
  obtain ⟨hEm, hEC⟩ := h1P
  have hEperf : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.mp (CFSG.ComponentClassification.Layer.perfect (CBar a))
  have hEn : E.Normal := CFSG.ComponentClassification.Layer.normal (CBar a)
  have hPmap : P.map π = E := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
  have hkerN : ∀ x : X, x ∈ π.ker ↔ x ∈ N := fun x => by rw [hπ, QuotientGroup.ker_mk']
  have hcent : ∀ n ∈ π.ker, ∀ x : X, n * x = x * n := fun n hn x =>
    zpowersC_comm ((hkerN n).1 hn) x
  obtain ⟨hMperf, hMmap⟩ := perfect_commutator_of_central π hcent (P := P)
    (by rw [hPmap]; exact hEperf)
  rw [hPmap] at hMmap
  set M : Subgroup X := ⁅P, P⁆ with hM
  have hMn : M.Normal := by
    have : P.Normal := Subgroup.Normal.comap hEn π
    exact Subgroup.commutator_normal P P
  have hMle : ∀ m ∈ M, π m ∈ E := fun m hm => hMmap ▸ mem_map_of_mem π hm
  let η : M →* E := (π.comp M.subtype).codRestrict E (fun m => hMle m m.2)
  have hηs : Function.Surjective η := by
    rintro ⟨e, he⟩
    rw [← hMmap] at he
    obtain ⟨m, hm, rfl⟩ := he
    exact ⟨⟨m, hm⟩, rfl⟩
  have hηker : ∀ m : M, m ∈ η.ker ↔ (m : X) ∈ N := by
    intro m
    rw [MonoidHom.mem_ker, ← hkerN, MonoidHom.mem_ker]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  have hηC : η.ker ≤ center M := by
    intro m hm
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcent _ ((hkerN _).2 ((hηker m).1 hm)) y).symm
  have hη2 : IsPGroup 2 η.ker := by
    let ψ : η.ker →* zpowers a :=
      (X.subtype.comp (M.subtype.comp η.ker.subtype)).codRestrict (zpowers a)
        (fun m => (hηker m).1 m.2)
    have hψ : Function.Injective ψ := by
      intro x y hxy
      ext
      exact congrArg (fun z : zpowers a => (z : G)) hxy
    exact (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])).of_injective ψ hψ
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hMperf
  obtain ⟨-, hηbij⟩ :=
    even_symplectic_four_catalog_perfect_central_two_cover_trivial η hηs hηC hη2 le_rfl hEm
  set L' : Subgroup G := M.map X.subtype with hL'
  let eL : L' ≃* E :=
    (M.equivMapOfInjective X.subtype X.subtype_injective).symm.trans
      (MulEquiv.ofBijective η hηbij)
  have hLm : LieModel L' .PSp 2 2 2 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eL.symm hEm
  have hLs : IsSimpleGroup L' := isSimpleGroup_of_lieModel_PSp hLm
  have : Group.IsPerfect E := CFSG.ComponentClassification.Layer.perfect (CBar a)
  have hLperf : Group.IsPerfect L' :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hLZ : center L' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L') with hb | ht
    · exact hb
    · exfalso
      have hcomm : commutator L' = ⊥ := by
        rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_center_iff.1 (ht ▸ mem_top y) x)
      have htop : (⊤ : Subgroup L') = ⊥ := by rw [← hcomm, hLperf.commutator_eq_top]
      obtain ⟨x, y, hxy⟩ := exists_pair_ne L'
      have hx : x = 1 := Subgroup.mem_bot.1 (htop ▸ mem_top x)
      have hy : y = 1 := Subgroup.mem_bot.1 (htop ▸ mem_top y)
      exact hxy (hx.trans hy.symm)
  have hLq : CFSG.Assembly.IsQuasisimple L' := by
    refine ⟨hLperf.commutator_eq_top, ?_⟩
    have e : L' ⧸ center L' ≃* L' :=
      (QuotientGroup.quotientMulEquivOfEq hLZ).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup
  have hE4 : ∃ E₄ : Subgroup G, E₄ ≤ L' ∧ CFSG.Assembly.IsElemAbelian 2 E₄ ∧ Nat.card E₄ = 4 := by
    obtain ⟨E₀, ⟨hE₀c, hE₀2⟩, hE₀4⟩ := exists_four_of_lieModel_PSp hLm
    refine ⟨E₀.map L'.subtype, map_subtype_le _, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
      obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
      apply Subtype.ext
      have := congrArg Subtype.val (hE₀c.1.1 ⟨x', hx'⟩ ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at this ⊢
      rw [← map_mul, ← map_mul, this]
    · rintro _ ⟨x', hx', rfl⟩
      rw [← map_pow, hE₀2 x' hx', map_one]
    · rw [Subgroup.card_map_of_injective L'.subtype_injective, hE₀4]
  have hLX : L' ≤ X := map_subtype_le _
  have haJ : a ∈ centralizer (L' : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (hLX hl)
  have hcomp : CFSG.Assembly.IsComponentOf L' X := by
    have hsub : L'.subgroupOf X = M := comap_map_eq_self_of_injective X.subtype_injective M
    refine ⟨hLX, CFSG.Assembly.IsSubnormal.step hLX (hsub ▸ hMn)
      (CFSG.Assembly.IsSubnormal.refl _), hLq⟩
  have hsyl : ∃ S : Sylow 2 ↥(centralizer (L' : Set G) ⊓ X),
      (S : Subgroup _).map (centralizer (L' : Set G) ⊓ X).subtype = zpowers a := by
    set Q := centralizer (L' : Set G) ⊓ X with hQ
    have haQ : zpowers a ≤ Q := zpowers_le.2 ⟨haJ, mem_centralizer_singleton_iff.2 rfl⟩
    have hz2 : IsPGroup 2 ((zpowers a).subgroupOf Q) :=
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])).comap_of_injective
        Q.subtype Q.subtype_injective
    obtain ⟨S, hS⟩ := hz2.exists_le_sylow
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      have hsX : (s : G) ∈ X := s.2.2
      have hπO : π ⟨s, hsX⟩ ∈ standardComponentOddCore (CBar a) := by
        rw [← hEC, mem_centralizer_iff]
        intro e he
        have he' : e ∈ E := he
        rw [← hMmap] at he'
        obtain ⟨m, hm, rfl⟩ := he'
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact mem_centralizer_iff.1 s.2.1 (m : G) ⟨m, hm, rfl⟩
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
      have hk' : (⟨s, hsX⟩ : X) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        have := congrArg (fun z : S => ((z : Q) : G)) hk
        simpa using this
      have h1 := eq_one_of_pow_two_pow π hk'
        (CFSG.LocalAnalysis.EvenBN.Common.odd_card_standardComponentOddCore (CBar a)) hπO
      rw [← MonoidHom.mem_ker, hkerN] at h1
      exact h1
    · intro z hz
      exact ⟨⟨z, haQ hz⟩, hS (by rw [mem_subgroupOf]; exact hz), rfl⟩
  obtain ⟨hS, -, hstd⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.quasisimple_involution_centralizer_order_two_standard hLq hE4
      haJ ha hcomp hsyl
  exact ⟨L', hstd, hLZ, hLm, hLX, hS⟩

end Standard

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

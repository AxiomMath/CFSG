module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Dickson.I271 (fixSubgroup_congr coprime_ker_mulEquiv pSimpleEquiv)

theorem congr_mem_range_conj_iff {S T : Type} [Group S] [Group T] (e : S ≃* T) (β : MulAut S) :
    MulAut.congr e β ∈ (MulAut.conj : T →* MulAut T).range ↔
      β ∈ (MulAut.conj : S →* MulAut S).range := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨e.symm t, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  · rintro ⟨s, rfl⟩
    exact ⟨e s, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e s).symm⟩

theorem orderOf_three_of_not_inner {S : Type} [Group S] {β : MulAut S} (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) : orderOf β = 3 := by
  refine orderOf_eq_prime hβ fun h => hout ⟨1, ?_⟩
  rw [map_one, h]

theorem component_transport {S T : Type} [Group S] [Finite S] [Group T] (ψ : S ≃* T) {β : MulAut S}
    {a : MulAut T} (h : MulAut.congr ψ β = a) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    GLAPComponent 3 (fixSubgroup a) (I.map ψ.toMonoidHom) ∧
      Nonempty (PSimple 3 I ≃* PSimple 3 (I.map ψ.toMonoidHom)) := by
  have hfix := fixSubgroup_congr ψ β
  rw [h] at hfix
  refine ⟨?_, ⟨pSimpleEquiv 3 (ψ.subgroupMap I)⟩⟩
  rw [hfix]
  exact glaPComponent_map Nat.prime_three ψ.toMonoidHom (coprime_ker_mulEquiv ψ _) hI

theorem eq_of_component {T : Type} [Group T] [Finite T] {C J I : Subgroup T} (hJC : J ≤ C)
    [(J.subgroupOf C).Normal] (hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C)) (hJs : IsSimpleGroup ↥J)
    (hI : GLAPComponent 3 C I) : I = J := by
  have hIC : I ≤ C := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hIJ : I ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC hsolv hIC hperf
  have hsn : IsSubnormal I J := isSubnormal_of_le_of_le hI.2.1 hIJ hJC
  rcases IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hJs with h0 | h0
  · exact absurd h0 (glaPComponent_ne_bot' hI)
  · exact h0

theorem primeCore_eq_bot {T : Type} [Group T] [Finite T] {J : Subgroup T} (hJs : IsSimpleGroup ↥J)
    (hdvd : 3 ∣ Nat.card ↥J) : GLAPPrimeCore 3 ↥J = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥J) with h0 | h0
  · exact h0
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card
    rw [h0, Subgroup.card_top] at hcop
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) hdvd)

noncomputable def pSimple_equiv_self {T : Type} [Group T] [Finite T] {J : Subgroup T}
    (hJs : IsSimpleGroup ↥J) (hnc : ∃ x y : ↥J, x * y ≠ y * x) (hdvd : 3 ∣ Nat.card ↥J) :
    PSimple 3 J ≃* ↥J := by
  have h1 : GLAPPrimeCore 3 ↥J = ⊥ := primeCore_eq_bot hJs hdvd
  let e : PQuot 3 J ≃* ↥J := (QuotientGroup.quotientMulEquivOfEq h1).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (PQuot 3 J) := e.isSimpleGroup
  have hZ : Subgroup.center (PQuot 3 J) = ⊥ := by
    refine CFSG.LocalAnalysis.GLTheoremA.chev_center_eq_bot_of_simple_nonabelian ?_
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e.symm x, e.symm y, fun h' => hxy (by simpa using congrArg e h')⟩
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)

theorem exists_equiv_of_conj {S T : Type} [Group S] [Finite S] [Group T] (ψ : S ≃* T) {β : MulAut S}
    {a : MulAut T} (h : MulAut.congr ψ β = a) {J : Subgroup T} (hJC : J ≤ fixSubgroup a)
    [(J.subgroupOf (fixSubgroup a)).Normal]
    (hsolv : Group.IsSolvable (↥(fixSubgroup a) ⧸ J.subgroupOf (fixSubgroup a)))
    (hJs : IsSimpleGroup ↥J) (hnc : ∃ x y : ↥J, x * y ≠ y * x) (hdvd : 3 ∣ Nat.card ↥J) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) : Nonempty (PSimple 3 I ≃* ↥J) := by
  haveI : Finite T := Finite.of_equiv S ψ.toEquiv
  obtain ⟨hI', ⟨e⟩⟩ := component_transport ψ h hI
  have hIJ := eq_of_component hJC hsolv hJs hI'
  rw [hIJ] at e
  exact ⟨e.trans (pSimple_equiv_self hJs hnc hdvd)⟩

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank

theorem mem_primes_25920 : ∀ p : ℕ, p.Prime → p ∣ 25920 → p ∈ [2, 3, 5] := by
  intro p hp hd
  have h : p ∣ 2 ^ 6 * 3 ^ 4 * 5 := by norm_num; exact hd
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      simp [this]
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h1
    simp [this]

theorem lieSearch_u42 :
    lieSearch [2, 3, 5] 25920 (fun t n q o => decide (o = 25920 →
      (t = .PSp ∧ n = 2 ∧ q = 3) ∨ (t = .PSU ∧ n = 4 ∧ q = 2))) = true := by
  decide +kernel

theorem arith_u42 {t : StatedLieTag} {n a : ℕ} (ht : t ∈ searchTags) (ha : 1 ≤ a) (hn : lieMin t ≤ n)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t 3 a = true) (h : lieOrd t n (3 ^ a) = 25920) :
    t = .PSp ∧ n = 2 ∧ a = 1 := by
  have hC := lieSearch_sound (N := 25920) (by norm_num) mem_primes_25920 lieSearch_u42 ht
    Nat.prime_three ha hn hnB hadm (by rw [h])
  rw [h] at hC
  rcases (of_decide_eq_true hC) rfl with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨h1, h2, ?_⟩
    have : 3 ^ a = 3 ^ 1 := by simpa using h3
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  · exfalso
    have h4 : 3 ∣ 2 := by
      rw [← h3]
      exact dvd_pow_self 3 (by omega)
    omega

theorem finish_classical_card {T : Type} [Group T] {t : StatedLieTag} {n a : ℕ}
    (hm : StatedClassicalModel T t n 3 a) (hc : Nat.card T = 25920) :
    t = .PSp ∧ n = 2 ∧ a = 1 := by
  have hc' := card_eq_lieOrd_of_classical hm
  rw [hc] at hc'
  obtain ⟨⟨-, ha, hcl⟩, hm2⟩ := hm
  cases t
  case PSL =>
    exact arith_u42 (by decide) ha hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc'.symm
  case PSU =>
    exact arith_u42 (by decide) ha hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc'.symm
  case PSp =>
    exact arith_u42 (by decide) ha hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc'.symm
  case POmegaOdd =>
    exact arith_u42 (by decide) ha hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc'.symm
  case POmegaPlus =>
    exact arith_u42 (by decide) ha hcl (le_lieExp_add_one hcl (by simp)) rfl hc'.symm
  case POmegaMinus =>
    exact arith_u42 (by decide) ha hcl (le_lieExp_add_one hcl (by simp)) rfl hc'.symm
  all_goals exact hm2.elim

theorem finish_classical {T : Type} [Group T] {t : StatedLieTag} {n a : ℕ}
    (hm : StatedClassicalModel T t n 3 a) (hU : catalogIs T S9.isU4two) :
    t = .PSp ∧ n = 2 ∧ a = 1 :=
  finish_classical_card hm (I1431Z.card_eq_of_u4two hU)

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

end

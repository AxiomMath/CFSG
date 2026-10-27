module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Polynomial Module CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitaryLines
  CFSG.RankThree.PartOne.KCUnitaryThree CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.RankThree.PartOne.KCUnitaryScalar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem noTorsion_of_not_dvd_gcd {p : ℕ} (hp : p.Prime) (h : UnitaryFieldData ℓ f K)
    (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
  intro c hc hcn hcp
  have h1 : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
  have h2 : orderOf c ∣ Nat.gcd p (Nat.gcd n (ℓ ^ f + 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp)
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcn) (orderOf_dvd_of_pow_eq_one h1))
  rw [(Nat.Prime.coprime_iff_not_dvd hp).2 hpg, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact h2

theorem exists_perfect_fixSubgroup_of_goodBlock
    (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)} (hx : x ∈ Ahat)
    (i : GoodBlockIdx h x) (hpd : p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X]))) :
    ∃ P : Subgroup (primeFormP h (idGram K n)),
      P ≤ fixSubgroup (primeFormConjHom h (idGram K n) (liftUnitary x)) ∧
      ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  classical
  have := h.finite
  let a : K[X] := (i.1 : K[X])
  have hpd_a : p ∣ Nat.card (idSpecialBlock h x a) := hpd
  have GS := (S.planeData hx).goodSetting
    (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range le_rfl
  let SB : Subgroup (primeFormUnitary h (idGram K n)) := idSpecialBlock h x a
  have hSB : SB ≤ (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)) :=
    GS.F_le_Hs i
  let j : SB →* gramSU h (idGram K n) :=
    { toFun := fun g => ⟨(g : GL (Fin n) K), hSB g.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun g g' => Subtype.ext rfl }
  let π : gramSU h (idGram K n) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  let f : SB →* primeFormP h (idGram K n) := π.comp j
  let P : Subgroup (primeFormP h (idGram K n)) := f.range
  refine ⟨P, ?_, ?_, ?_⟩
  · rintro y ⟨g, rfl⟩
    rw [mem_fixSubgroup, primeFormConjHom_liftUnitary, MulAut.conj_apply]
    have hcommU : (g : primeFormUnitary h (idGram K n)) * liftUnitary x =
        liftUnitary x * (g : primeFormUnitary h (idGram K n)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (idSpecialBlock_le x a g.2)
    have hcommGL : ((j g : gramSU h (idGram K n)) : GL (Fin n) K) * (x : GL (Fin n) K) =
        (x : GL (Fin n) K) * ((j g : gramSU h (idGram K n)) : GL (Fin n) K) := by
      change (g : GL (Fin n) K) * (x : GL (Fin n) K) =
        (x : GL (Fin n) K) * (g : GL (Fin n) K)
      exact congrArg (fun w : primeFormUnitary h (idGram K n) => (w : GL (Fin n) K)) hcommU
    have hcommG : j g * x = x * j g := Subtype.ext (by simpa using hcommGL)
    have hcommT : f g * ((x : gramSU h (idGram K n)) : primeFormP h (idGram K n)) =
        ((x : gramSU h (idGram K n)) : primeFormP h (idGram K n)) * f g := by
      have := congrArg π hcommG
      simpa [f, π, MonoidHom.comp_apply] using this
    rw [hcommT.symm, mul_assoc, mul_inv_cancel, mul_one]
  · have hSBperf : Group.IsPerfect SB := isPerfect_idSpecialBlock S hx i
    haveI : Group.IsPerfect SB := hSBperf
    haveI : Group.IsPerfect P := Group.IsPerfect.range f
    exact Subgroup.commutator_eq_self
  · have hj_inj : Function.Injective j := by
      intro u v huv
      have h' : ((j u : gramSU h (idGram K n)) : GL (Fin n) K) =
          ((j v : gramSU h (idGram K n)) : GL (Fin n) K) :=
        congrArg (fun w : gramSU h (idGram K n) => (w : GL (Fin n) K)) huv
      exact Subtype.ext (Subtype.ext h')
    have hker_map : f.ker.map j ≤ (innerLift h n).ker := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [MonoidHom.mem_ker, innerLift_apply]
      have hzf : f z = 1 := MonoidHom.mem_ker.mp hz
      rw [show ((j z : gramSU h (idGram K n)) : primeFormP h (idGram K n)) = f z from rfl,
        hzf, map_one]
    have hker_dvd : Nat.card f.ker ∣ Nat.card (innerLift h n).ker := by
      rw [← Subgroup.card_map_of_injective (f := j) hj_inj]
      exact Subgroup.card_dvd_of_le hker_map
    have hker : ¬ p ∣ Nat.card f.ker := fun hdvd =>
      not_dvd_card_ker_innerLift S.three_le S.ne S.prime S.noTorsion (hdvd.trans hker_dvd)
    have hcard : Nat.card f.ker * Nat.card P = Nat.card SB := by
      simpa [P] using Subgroup.card_ker_mul_card_range f
    have hd : p ∣ Nat.card P * Nat.card f.ker := by
      rw [mul_comm, hcard]
      exact hpd_a
    exact (S.prime.dvd_mul.mp hd).resolve_right hker

private theorem exists_goodBlock_of_active_line
    (S : PlaneSetup h n p Ahat) (F : NonsplitFacts h n p Ahat)
    {L : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hV : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    {t : ↥Ahat} (htL : t ∈ L) (ht1 : t ≠ 1) :
    ∃ i : GoodBlockIdx h t.1, p ∣ Nat.card (idSpecialBlock h t.1 (i.1 : K[X])) := by
  classical
  have := h.finite
  obtain ⟨hmem_t, hgood_t⟩ := isGoodBlock_X_sub_one F hL hV htL ht1
  have hWt := primaryComponent_X_sub_one_eq F hL htL ht1
  have hjm : ordNegQ ℓ f p ≤
      Module.finrank K (primaryComponent (xlin h n t.1) (X - C 1)) := by
    rw [hWt]
    exact (F.e_le_finrank hL hV).trans (Submodule.finrank_mono le_sup_right)
  exact ⟨⟨⟨X - C 1, hmem_t⟩, hgood_t⟩,
    dvd_card_idSpecialBlock_X_sub_one (S.planeData t.2) hmem_t F.e_gt hjm
      (dvd_pow_ordNegQ_sub S.prime)⟩

theorem exists_goodBlock_of_dvd (S : PlaneSetup h n p Ahat) (hpq : p ∣ ℓ ^ f + 1)
    (hq : 3 < ℓ ^ f) :
    ∃ (x : gramSU h (idGram K n)) (_ : x ∈ Ahat) (_ : x ≠ 1) (i : GoodBlockIdx h x),
      p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X])) := by
  classical
  have := h.finite
  obtain ⟨b, hbON, hbeig⟩ := exists_orthonormal_eigenbasis_of_dvd S hpq
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hn3 := S.three_le
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h' => by simpa [i0, i1] using congrArg Fin.val h'
  obtain ⟨x, hx, hx1, μ, hμ, hei, hej⟩ := exists_pair_eigenvalue S hb0 hbeig i0 i1
  have hev : Module.End.HasEigenvalue (xlin h n x) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hei, hb0 i0⟩
  have hmem : (X - C μ : K[X]) ∈ primaryFactors (xlin h n x) := X_sub_C_mem_primaryFactors hev
  have hm : 2 ≤ Module.finrank K (primaryComponent (xlin h n x) (X - C μ)) :=
    two_le_finrank_of_pair (mem_primaryComponent_X_sub_C.mpr hei)
      (mem_primaryComponent_X_sub_C.mpr hej) (hbON.pair h01).linearIndependent
  have hgood : IsGoodBlock h (toLinU h n (liftUnitary x)) ⟨X - C μ, hmem⟩ :=
    isGoodBlock_X_sub_C (hK := h) hmem hm (not_exceptional_of_three_lt hq)
  refine ⟨x, hx, hx1, ⟨⟨X - C μ, hmem⟩, hgood⟩, ?_⟩
  by_cases hμ1 : μ = 1
  · subst μ
    refine dvd_card_idSpecialBlock_X_sub_one (S.planeData hx) hmem (j := 2) le_rfl hm ?_
    have e : ((ℓ ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 =
        (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by ring
    rw [e]
    exact Dvd.dvd.mul_left (by exact_mod_cast hpq) _
  · have hne : (X - C μ : K[X]) ≠ X - C 1 := by
      intro h'
      apply hμ1
      have h2 : (1 : K) - μ = 0 := by
        simpa using congrArg (fun p : K[X] => p.eval (1 : K)) h'
      exact (sub_eq_zero.mp h2).symm
    exact dvd_card_idSpecialBlock_of_ne (S.planeData hx) ⟨⟨X - C μ, hmem⟩, hgood⟩ hne

private theorem exists_good_mem_of_goodBlock
    (S : PlaneSetup h n p Ahat) {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hEmap : Ahat.map (innerLift h n) = D) (hinj : Set.InjOn (innerLift h n) Ahat)
    {x : gramSU h (idGram K n)} (hx : x ∈ Ahat) (hx1 : x ≠ 1)
    (i : GoodBlockIdx h x) (hpd : p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X]))) :
    ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (primeFormP h (idGram K n)),
      P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  obtain ⟨P, hPfix, hPperf, hPdvd⟩ := exists_perfect_fixSubgroup_of_goodBlock S hx i hpd
  refine ⟨primeFormConjHom h (idGram K n) (liftUnitary x), ?_, ?_, P, hPfix, hPperf, hPdvd⟩
  · rw [primeFormConjHom_liftUnitary]
    have h1 : MulAut.conj ((x : gramSU h (idGram K n)) : primeFormP h (idGram K n)) ∈ D := by
      rw [← innerLift_apply, ← hEmap]
      exact Subgroup.mem_map_of_mem _ hx
    exact h1
  · intro h1
    have h2 : innerLift h n x = innerLift h n 1 := by
      rw [innerLift_apply, map_one, ← primeFormConjHom_liftUnitary, h1]
    exact hx1 (hinj hx (one_mem Ahat) h2)

theorem innGoodAt_primeFormP_of_not_dvd_gcd {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) (d : TauCeti.LieTypeIndex) :
    InnGoodAt p d (primeFormP h (idGram K n)) := by
  classical
  have := h.finite
  intro D hDel hDcard hDle
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 :=
    noTorsion_of_not_dvd_gcd hp h hpg
  have hDsub : D ≤ primeFormD h (idGram K n) :=
    hDle.trans (innAutDerived_le_primeFormD h isPrimeFormGram_idGram hn hne)
  have hDinner : D ≤ inner (primeFormP h (idGram K n)) := fun x hx =>
    mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin n) K) hp hpg (hDsub hx) (hDel.2 x hx)
  have hDel' : CFSG.IsElementaryAbelian p D :=
    { toIsMulCommutative := hDel.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hDel.2 x x.2) }
  obtain ⟨Ahat, hlift, -⟩ :=
    exists_unique_planeLift hn hne hp hZp D hDinner hDel' hDcard
  have S : PlaneSetup h n p Ahat := ⟨hn, hne, hp, hpℓ, hZp, hlift.1, hlift.2.1⟩
  have hEmap := hlift.2.2.1
  have hinj := hlift.2.2.2
  have hgood_mem : ∀ (x : gramSU h (idGram K n)) (hx : x ∈ Ahat), x ≠ 1 →
      ∀ i : GoodBlockIdx h x, p ∣ Nat.card (idSpecialBlock h x (i.1 : K[X])) →
      ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (primeFormP h (idGram K n)),
        P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := fun x hx hx1 i hpd =>
    exists_good_mem_of_goodBlock S hEmap hinj hx hx1 i hpd
  by_cases hpq : p ∣ ℓ ^ f + 1
  · obtain ⟨x, hx, hx1, i, hpd⟩ :=
      exists_goodBlock_of_dvd S hpq (three_lt_of_dvd_add_one h hp hp2 h32 hpq)
    exact Or.inl (hgood_mem x hx hx1 i hpd)
  · have F := nonsplitFacts_of S hp2 hpq
    obtain ⟨L₀, -, hL₀, -, -, hV₀, -⟩ := F.decomp.exists_two_active
    obtain ⟨t, htL₀, ht1⟩ := exists_ne_one_mem_line S hL₀
    have hx1 : t.1 ≠ 1 := fun h' => ht1 (Subtype.ext h')
    obtain ⟨i, hpd⟩ := exists_goodBlock_of_active_line S F hL₀ hV₀ htL₀ ht1
    exact Or.inl (hgood_mem t.1 t.2 hx1 i hpd)

@[expose] def UnitaryInnGoodDvd : Prop :=
  ∀ (q : TauCeti.PrimePower) (n p : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData q.p q.exponent K), 3 ≤ n → ¬ (n = 3 ∧ q.card = 2) → p.Prime →
      p ≠ 2 → p ≠ q.p → p ∣ Nat.gcd n (q.card + 1) → ¬ (p = 3 ∧ q.card = 2) →
        InnGoodAt p (.twistedA (n - 1) q) (primeFormP h (idGram K n))

theorem lieInnGood_unitary_of_dvd (hdvd : UnitaryInnGoodDvd) : LieInnGood isUnitaryIdx := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨r, q, K, _, hU, hr, hdA, hne, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx hP
  have hpℓ : p ≠ q.p := by
    rw [hdA, TauCeti.LieTypeIndex.characteristic_twistedA] at hpc
    exact hpc
  have h32 : ¬ (p = 3 ∧ q.card = 2) := by
    rintro ⟨hp3, hq2⟩
    exact h3 ⟨hp3, by rw [hdA]; exact hq2⟩
  by_cases hgcd : p ∣ Nat.gcd (r + 1) (q.card + 1)
  · have hmodel := hdvd q (r + 1) p K hU (by omega) hne hp hp2 hpℓ hgcd h32
    have hidx : (.twistedA (r + 1 - 1) q : TauCeti.LieTypeIndex) = d.1 := by
      rw [hdA]
      simp
    rw [hidx] at hmodel
    exact innGoodAt_of_mulEquiv eP hmodel
  · have hne' : ¬ (r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h1, h2⟩
      exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
    have hgcd' : ¬ p ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := by
      rwa [TauCeti.PrimePower.card_def] at hgcd
    have h32' : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨hp3, h2⟩
      exact h32 ⟨hp3, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
    have hmodel :=
      innGoodAt_primeFormP_of_not_dvd_gcd hU (by omega) hne' hp hp2 hpℓ hgcd' h32' d.1
    exact innGoodAt_of_mulEquiv eP hmodel

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

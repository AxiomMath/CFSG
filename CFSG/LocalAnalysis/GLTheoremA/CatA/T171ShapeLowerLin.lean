module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerBase
public import CFSG.RankThree.PartOne.K159.CoverPSL
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.CentralCover
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift
open CFSG.RankThree.PartOne.K159 (invElem invElem_conj)
open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {k : Type} [Field k] [Fintype k]

section Cover

variable {Y : Type*} [Group Y] [Finite Y]

theorem lowerLin_of_cover {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Fintype.card k - 1) (hm : 1 ≤ m) (hk2 : ringChar k = 2)
    {φ : Y →* PSL(m + 1, k)} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ E U : Subgroup Y, IsElemAbelian p E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set Y) ∧
      p ^ (m - if p ∣ m + 1 then 1 else 0) * Nat.card ↥(E ⊓ φ.ker) ≤ Nat.card E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨hDp, hF, hDcard⟩ := torusPSL_package (Y := Y) hp hp2 hζo hζ hm hφ hker
  set θ := torusPSL ζ hζ m with hθdef
  set D := θ.range with hDdef
  set π : SL(m + 1, k) →* PSL(m + 1, k) :=
    QuotientGroup.mk' (Subgroup.center SL(m + 1, k)) with hπdef
  set g : Fin m → PSL(m + 1, k) := fun j => θ (.ofAdd (Pi.single j (1 : ZMod p))) with hgdef
  have hgp : ∀ j, g j ^ p = 1 := fun j => hDp _ (by rw [hDdef]; exact ⟨_, rfl⟩)
  have hgj : ∀ j, g j = π (torusElem ζ hζ (Pi.single j 1)) := by
    intro j
    rw [hgdef, hθdef, hπdef]
    rfl
  have hinv : ∀ j, ∃ w : PSL(m + 1, k), w * g j * w⁻¹ = (g j)⁻¹ := by
    intro j
    refine ⟨π (invElem (k := k) j), ?_⟩
    rw [hgj]
    have h := congrArg π (invElem_conj (k := k) ζ hζ j)
    rw [map_mul, map_mul, map_inv] at h
    rw [h, map_inv]
  have hgen : Subgroup.closure (Set.range g) = D := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin m =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
          Multiplicative (Fin m → ZMod p)))).map (torusPSL ζ hζ m) = D := by
      rw [hDdef, hθdef, CFSG.RankThree.PartOne.K159.closure_range_ofAdd_single,
        ← MonoidHom.range_eq_map]
    rw [MonoidHom.map_closure] at h1
    rw [← h1]
    congr 1
    rw [hgdef, hθdef]
    exact Set.range_comp _ _
  have hlift : ∀ e ∈ D, ∃ y : Y, φ y = e ∧ y ^ p = 1 := by
    intro e he
    have hSE : Set.range g ⊆ D := by rw [← hgen]; exact Subgroup.subset_closure
    have hS : ∀ s ∈ Set.range g, ∃ y : Y, φ y = s ∧ y ^ p = 1 := by
      rintro _ ⟨j, rfl⟩
      exact exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (hp.odd_of_ne_two hp2) (hgp j)
        (hinv j).choose_spec
    exact exists_lift_pow_eq_one_of_mem_closure hF hSE hS (hgen ▸ he)
  obtain ⟨E, hEab, hEmap, hEcard⟩ := exists_elemAbelian_index_of_lift hF hlift
  set i₀ : Fin (m + 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have htwo : (2 : k) = 0 := by
    have h := ringChar.Nat.cast_ringChar (R := k)
    rwa [hk2, Nat.cast_ofNat] at h
  let rootHom : Multiplicative k →* SL(m + 1, k) :=
    { toFun := fun t => rootElem h01 (Multiplicative.toAdd t)
      map_one' := rootElem_zero h01
      map_mul' := fun _ _ => rootElem_add h01 _ _ }
  set π : SL(m + 1, k) →* PSL(m + 1, k) := QuotientGroup.mk' _ with hπ
  set U : Subgroup (PSL(m + 1, k)) := rootHom.range.map π with hU
  have hmemU : ∀ x ∈ U, ∃ t : k, x = π (rootElem h01 t) := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  have hUmem : ∀ t : k, π (rootElem h01 t) ∈ U := fun t =>
    ⟨_, ⟨Multiplicative.ofAdd t, rfl⟩, rfl⟩
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 := hUmem 1
    rw [h, Subgroup.mem_bot] at h1
    exact rootElem_not_mem_center h01 one_ne_zero ((QuotientGroup.eq_one_iff _).1 h1)
  have hU2 : IsPGroup 2 U := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨t, rfl⟩ := hmemU x hx
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, pow_two, ← rootElem_add,
      ← two_mul, htwo, zero_mul, rootElem_zero, map_one]
  have hDU : ∀ d ∈ D, ∀ u ∈ U, d * u * d⁻¹ ∈ U := by
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨t, rfl⟩ := hmemU u hu
    change π (torusSL ζ hζ m a) * π (rootElem h01 t) * (π (torusSL ζ hζ m a))⁻¹ ∈ U
    rw [← map_inv, ← map_mul, ← map_mul, diag_conj_rootElem h01 _ t _ rfl]
    exact hUmem _
  have hEU : ∀ x ∈ E, ∀ u ∈ U, φ x * u * (φ x)⁻¹ ∈ U := by
    intro x hx
    have hxD : φ x ∈ D := hEmap ▸ Subgroup.mem_map_of_mem φ hx
    exact hDU (φ x) hxD
  obtain ⟨R, hR1, hR2, hER⟩ := exists_two_subgroup_normalized_of_cover hφ hker hU1 hU2 hEU
  refine ⟨E, R, hEab, hR2, hR1, hER, ?_⟩
  have hle : p ^ (m - if p ∣ m + 1 then 1 else 0) ≤ Nat.card D := hDcard
  calc p ^ (m - if p ∣ m + 1 then 1 else 0) * Nat.card ↥(E ⊓ φ.ker)
      ≤ Nat.card D * Nat.card ↥(E ⊓ φ.ker) := Nat.mul_le_mul_right _ hle
    _ = Nat.card E := hEcard

end Cover

section Order

variable {p m : ℕ} [NeZero p] {ζ : kˣ}

theorem torusElem_single_proj_ne_one (hp : p.Prime) (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (hm : 2 ≤ m) :
    (QuotientGroup.mk' (Subgroup.center SL(m + 1, k))
        (torusElem ζ hζ (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod p)))) ≠ 1 := by
  intro h
  set a : Fin m → ZMod p := Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod p) with ha
  have hmem : Multiplicative.ofAdd a ∈ (torusPSL ζ hζ m).ker := by
    show (torusPSL ζ hζ m) (Multiplicative.ofAdd a) = 1
    show (QuotientGroup.mk' (Subgroup.center SL(m + 1, k)))
      (torusSL ζ hζ m (Multiplicative.ofAdd a)) = 1
    rw [torusSL_apply]
    exact h
  have heq := torusExp_eq_of_mem_ker hζo hζ hmem
    (⟨0, by omega⟩ : Fin (m + 1)) (⟨1, by omega⟩ : Fin (m + 1))
  have h0 : torusExp (Multiplicative.toAdd (Multiplicative.ofAdd a))
      (⟨0, by omega⟩ : Fin (m + 1)) = 1 := by
    have := torusExp_castSucc (Multiplicative.toAdd (Multiplicative.ofAdd a))
      (⟨0, by omega⟩ : Fin m)
    rw [show (⟨0, by omega⟩ : Fin (m + 1)) = Fin.castSucc (⟨0, by omega⟩ : Fin m) from rfl,
      this]
    change a ⟨0, by omega⟩ = 1
    rw [ha]
    exact Pi.single_eq_same (M := fun _ : Fin m => ZMod p) (⟨0, by omega⟩ : Fin m) (1 : ZMod p)
  have h1 : torusExp (Multiplicative.toAdd (Multiplicative.ofAdd a))
      (⟨1, by omega⟩ : Fin (m + 1)) = 0 := by
    have := torusExp_castSucc (Multiplicative.toAdd (Multiplicative.ofAdd a))
      (⟨1, by omega⟩ : Fin m)
    rw [show (⟨1, by omega⟩ : Fin (m + 1)) = Fin.castSucc (⟨1, by omega⟩ : Fin m) from rfl,
      this]
    change a ⟨1, by omega⟩ = 0
    rw [ha]
    exact Pi.single_eq_of_ne (M := fun _ : Fin m => ZMod p)
      (show (⟨1, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ by simp [Fin.ext_iff]) (1 : ZMod p)
  rw [h0, h1] at heq
  have hd : p ∣ 1 := by
    have h2 : ((1 : ℕ) : ZMod p) = 0 := by simpa using heq
    rwa [ZMod.natCast_eq_zero_iff] at h2
  exact hp.not_dvd_one hd

theorem p_dvd_card_psl (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (hpq : p ∣ Fintype.card k - 1) : p ∣ Nat.card (PSL(m + 1, k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  set y : PSL(m + 1, k) := QuotientGroup.mk' (Subgroup.center SL(m + 1, k))
    (torusElem ζ hζ (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod p))) with hydef
  have hyp : y ^ p = 1 := by
    rw [hydef, ← map_pow]
    have h1 : (torusElem ζ hζ (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod p))) ^ p = 1 := by
      rw [show torusElem ζ hζ (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod p)) =
          torusSL ζ hζ m (Multiplicative.ofAdd (Pi.single (⟨0, by omega⟩ : Fin m)
            (1 : ZMod p))) from rfl,
        ← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
    rw [h1, map_one]
  have hy1 : y ≠ 1 := torusElem_single_proj_ne_one hp hζo hζ hm
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  rw [← hyo]
  exact orderOf_dvd_natCard y

end Order

theorem lowerLin_holds : LowerLin := by
  intro G _ _ L p N hp hp2 hN hq hcat
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨i, hQi, ⟨eCat⟩⟩ := hcat
  rcases i with ⟨pr, hpr⟩ | ⟨deg, hdeg⟩ | d | s
  · exact hQi.elim
  · exact hQi.elim
  · obtain ⟨idx, hv⟩ := d
    obtain ⟨q, hidx, hq2, hpq⟩ := hQi
    subst hidx
    have hlm : CFSG.Blueprint.LieModel (PSimple p L) .PSL (m + 1) q.p q.exponent := by
      have h := CFSG.Models.lieModel_A m q hv eCat
      exact CFSG.Models.LieModel.toBlueprint (by decide) h
    rw [hq2] at hlm
    have hmem : StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags := by decide
    obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨eStated⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hlm hmem
    letI := hKfield
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    have hKcard' : Nat.card K = 2 ^ q.exponent := hKcard
    have hKcardF : Fintype.card K = 2 ^ q.exponent := by
      rw [← Nat.card_eq_fintype_card]; exact hKcard'
    have hpqK : p ∣ Fintype.card K - 1 := by
      have h1 : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
      rw [hKcardF, ← h1]
      exact hpq
    have hK2 : ringChar K = 2 := by
      haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := q.exponent) hKcardF
      exact ringChar.eq K 2
    have hpL : p ∣ Nat.card ↥L := by
      have hpsl : p ∣ Nat.card (PSL(m + 1, K)) :=
        p_dvd_card_psl (k := K) (p := p) (m := m) hp hp2 (by omega) hpqK
      have hpsimple : p ∣ Nat.card (PSimple p L) := by
        rw [Nat.card_congr eStated.toEquiv,
          ← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj (m + 1) K).toEquiv]
        exact hpsl
      refine hpsimple.trans ?_
      have h1 : Nat.card (PSimple p L) ∣ Nat.card (PQuot p L) :=
        Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot p L))
      have h2 : Nat.card (PQuot p L) ∣ Nat.card ↥L :=
        Subgroup.card_quotient_dvd_card (GLAPPrimeCore p ↥L)
      exact h1.trans h2
    have hO : GLAPPrimeCore p ↥L ≠ ⊤ := by
      intro htop
      have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) :=
        CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L)
      rw [htop, Subgroup.card_top] at hc
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpL)
    have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
      CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hO
    haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
    let eP : (↥L ⧸ Subgroup.center ↥L) ≃* PSimple p L :=
      CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hOZ
    let eAll : (↥L ⧸ Subgroup.center ↥L) ≃* PSL(m + 1, K) :=
      eP.trans (eStated.trans (projectiveSpecialLinearGroupEquivStatedProj (m + 1) K).symm)
    let φ : ↥L →* PSL(m + 1, K) :=
      eAll.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hφ : Function.Surjective φ :=
      eAll.surjective.comp (QuotientGroup.mk'_surjective _)
    have hφker : φ.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 := by
          apply eAll.injective
          rw [map_one]
          exact hx
        exact (QuotientGroup.eq_one_iff _).1 h1
      · intro hx
        change eAll ((QuotientGroup.mk' (Subgroup.center ↥L)) x) = 1
        rw [show (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 from
          (QuotientGroup.eq_one_iff _).2 hx, map_one]
    obtain ⟨E, U, hEab, hU2, hU1, hEU, hEcard⟩ :=
      lowerLin_of_cover (k := K) (Y := ↥L) (m := m) (φ := φ) hp hp2 hpqK (by omega) hK2 hφ
        (by rw [hφker])
    refine ⟨E.map L.subtype, U.map L.subtype, Subgroup.map_subtype_le E,
      Subgroup.map_subtype_le U, hEab.map L.subtype, hU2.map L.subtype, ?_, ?_, ?_⟩
    · intro h
      exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U L.subtype_injective).1 h)
    · refine (Subgroup.map_mono hEU).trans ?_
      exact Subgroup.le_normalizer_map L.subtype
    ·
      have hkerE : E ⊓ φ.ker = E ⊓ Subgroup.center ↥L := by rw [hφker]
      have h1 : Nat.card ↥(E.map L.subtype) = Nat.card E :=
        Subgroup.card_map_of_injective L.subtype_injective
      have h2 : Nat.card ↥((E.map L.subtype) ⊓ Subgroup.centralizer (L : Set G)) =
          Nat.card ↥(E ⊓ Subgroup.center ↥L) := by
        rw [inf_centralizer_map_eq, Subgroup.card_map_of_injective L.subtype_injective]
      have hexp : p ^ (m + 1 - 2) ≤ p ^ (m - if p ∣ m + 1 then 1 else 0) := by
        have hm1 : m + 1 - 2 = m - 1 := by omega
        rw [hm1]
        by_cases hpdiv : p ∣ m + 1
        · rw [if_pos hpdiv]
        · rw [if_neg hpdiv]
          exact Nat.pow_le_pow_right (by have := hp.two_le; omega) (by omega)
      rw [h1, h2]
      rw [hkerE] at hEcard
      exact (Nat.mul_le_mul_right _ hexp).trans hEcard
  · exact hQi.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

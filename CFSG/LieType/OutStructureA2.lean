module

public import CFSG.LieType.OutStructureA1
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBULinearUnitaryOuterExtraspecial
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem exists_fieldPart_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (F : Subgroup (MulAut X)) (hFp : IsPGroup p F) (hFcyc : IsCyclic ↥F)
    (hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X = ⊥)
    (hSylow : ∀ S : Sylow p (Outer X), (S : Subgroup (Outer X)).Normal)
    (hidx : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).index) :
    ∃ F : Subgroup (MulAut X),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).index ∧
      ∀ x : MulAut X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Outer X) := finite_outer X
  let mk : MulAut X →* Outer X := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have hker : mk.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner X := QuotientGroup.ker_mk' _
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).map mk = F.map mk := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hindex : (F.map mk).index = (CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F).index := by
    rw [← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F) (QuotientGroup.mk'_surjective _)
      (by rw [hker]; exact le_sup_left)
  have hCp : IsPGroup p (F.map mk) := hFp.map mk
  have hCnormal : (F.map mk).Normal := by
    have hS := hSylow (hCp.toSylow (by rwa [hindex]))
    simpa using hS
  have hpre : (F.map mk).comap mk = CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔ F := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact le_sup_left)
  refine ⟨F, ?_, hFcyc, hFbot, hidx, ?_⟩
  · rw [← hpre]
    exact hCnormal.comap mk
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    have hxmem : mk x ∈ F.map mk := by
      have h1 : orderOf (QuotientGroup.mk' (F.map mk) (mk x)) ∣ p ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ← map_pow, hk]
        simp
      have h2 : orderOf (QuotientGroup.mk' (F.map mk) (mk x)) ∣ (F.map mk).index := by
        rw [Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime p (F.map mk).index :=
        (hp.coprime_iff_not_dvd).2 (by rwa [hindex])
      have hz1 : orderOf (QuotientGroup.mk' (F.map mk) (mk x)) = 1 :=
        Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) h1 h2
      exact (QuotientGroup.eq_one_iff (N := F.map mk) (mk x)).mp
        (orderOf_eq_one_iff.mp hz1)
    rw [← hpre]
    exact hxmem

theorem exists_fieldPart_projectiveSL_three (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL 3 K)) ≤ 1) :
    ∃ F : Subgroup (MulAut (projectiveSL 3 K)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F).index ∧
      ∀ x : MulAut (projectiveSL 3 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hp0, hKcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp0⟩
  have hKcard' : Nat.card K = ringChar K ^ (e : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  have hfcard : Nat.card (K ≃+* K) = (e : ℕ) := fieldAut_card K hp0 hKcard'
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hfcard]; exact e.pos.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut (projectiveSL 3 K)) :=
    (S : Subgroup (K ≃+* K)).map (fieldAut 3 K)
  have hfinj : Function.Injective (fieldAut 3 K) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (K := K) (n := 3) (by norm_num) 1 σ
      (by rw [map_one, one_mul]; exact hσ)).1
  have hinner_le : CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ≤ linearAutGroup 3 K :=
    (standard_outer_quotients (n := 3) (K := K)).1
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨σ, -, rfl⟩ := hxF
    have hxI' : fieldAut 3 K σ ∈ linearAutGroup 3 K := hinner_le hxI
    rw [linearAutGroup_eq_range] at hxI'
    obtain ⟨A, hA⟩ := hxI'
    have h1 : conjAut 3 K A * fieldAut 3 K σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    have h2 : σ⁻¹ = 1 :=
      (eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) A σ⁻¹ h1).1
    have h3 : σ = 1 := inv_eq_one.mp h2
    rw [h3, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K)) (fieldAut 3 K)
      hfinj).isCyclic.mp hScyc
  have hFp : IsPGroup p F := (S.isPGroup').map (fieldAut 3 K)
  have hSylow : ∀ S : Sylow p (Outer (projectiveSL 3 K)),
      (S : Subgroup (Outer (projectiveSL 3 K))).Normal := by
    obtain ⟨N, hN, -, hNcard, hab, -⟩ :=
      CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter.linear_outer_filtration
        (K := K) (n := 3) (by norm_num)
    haveI := hN
    have hNle : Nat.card N ≤ p := by
      have h3 : Nat.card N ∣ 3 := hNcard.trans (Nat.gcd_dvd_left 3 _)
      have hle3 : Nat.card N ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      omega
    exact sylow_normal_of_quotient N hNle (sylow_normal_of_comm hab)
  have hgcd : ¬ p ∣ Nat.gcd 3 (Nat.card K - 1) := by
    intro hdvd
    have h2 := GL83.I713.two_le_pRank_projectiveSL_of_dvd (K := K) (n := 3)
      (by norm_num) hp hp2 hdvd
    omega
  have hOutdvd : Nat.card (Outer (projectiveSL 3 K)) ∣
      2 * (e : ℕ) * Nat.gcd 3 (Nat.card K - 1) := by
    have h :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
        (k := K) (p := ringChar K) (f := (e : ℕ)) (n := 3) hp0 e.pos (by norm_num) hKcard'
    rw [hKcard']
    exact h
  let φ : (K ≃+* K) →* Outer (projectiveSL 3 K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K))).comp (fieldAut 3 K)
  let C : Subgroup (Outer (projectiveSL 3 K)) := (S : Subgroup (K ≃+* K)).map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K))) = C := by
    dsimp [F, C, φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F).map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K))) = F.map
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K))) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C.index = (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F)
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : fieldAut 3 K (x : K ≃+* K) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K)))
          (fieldAut 3 K (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K)) _).mp hx'
    have hxbot : fieldAut 3 K (x : K ≃+* K) ∈ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) :=
      ⟨Subgroup.mem_map_of_mem (fieldAut 3 K) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C, φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (e : ℕ) p := by
    rw [Sylow.card_eq_multiplicity, hfcard]
  have hOutEq : Nat.card (Outer (projectiveSL 3 K)) =
      C.index * p ^ Nat.factorization (e : ℕ) p := by
    have h1 := Subgroup.index_mul_card C
    rw [hCcard, hScard] at h1
    exact h1.symm
  set v := Nat.factorization (e : ℕ) p with hv
  set m := ordCompl[p] (e : ℕ) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : (e : ℕ) = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (e : ℕ) p]
  have hout' : C.index * p ^ v ∣ p ^ v * (2 * m * Nat.gcd 3 (Nat.card K - 1)) := by
    have h := hOutdvd
    rw [hOutEq] at h
    rw [show 2 * (e : ℕ) * Nat.gcd 3 (Nat.card K - 1) =
      p ^ v * (2 * m * Nat.gcd 3 (Nat.card K - 1)) by rw [heq]; ring] at h
    exact h
  have hidxC : C.index ∣ 2 * m * Nat.gcd 3 (Nat.card K - 1) := by
    have hpv0 : 0 < p ^ v := pow_pos hp.pos v
    rw [mul_comm C.index (p ^ v)] at hout'
    exact (Nat.mul_dvd_mul_iff_left hpv0).mp hout'
  have h2not : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hidxC' : ¬ p ∣ C.index := by
    intro h
    rcases hp.dvd_mul.mp (h.trans hidxC) with h1 | h1
    · rcases hp.dvd_mul.mp h1 with h2 | h2
      · exact h2not h2
      · exact hpm h2
    · exact hgcd h1
  have hidx : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) ⊔ F).index := by
    rw [← hCindex]
    exact hidxC'
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hidx

theorem exists_fieldPart_primeFormP_three {p₀ f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hq : p₀ ^ f ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) ≤ 1) :
    ∃ F : Subgroup (MulAut (primeFormP h
        ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⊔ F).index ∧
      ∀ x : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
        (∃ k : ℕ, x ^ (p ^ k) = 1) →
          x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⊔ F := by
  classical
  haveI : Fact p₀.Prime := ⟨h.prime⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  let C : GL (Fin 3) K := 1
  have hC : IsPrimeFormGram C := isPrimeFormGram_one
  let T := primeFormP h (C : Matrix (Fin 3) (Fin 3) K)
  have hq' : ¬(3 = 3 ∧ p₀ ^ f = 2) := by
    rintro ⟨-, h2⟩
    exact hq h2
  obtain ⟨-, -, -, -, -, hfac, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC (n := 3) (by norm_num) hq'
  obtain ⟨-, -, -, hOut, -, -⟩ :=
    unitary_full_diagonal_outer_order h (n := 3) (by norm_num) hq'
  have hcardAut : Nat.card (K ≃+* K) = 2 * f := fieldAut_card K h.prime h.card
  have h2f : 0 < 2 * f := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le zero_lt_one h.one_le)
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact h2f.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut T) :=
    (S : Subgroup (K ≃+* K)).map (primeFormFieldHom h hC)
  have hfacφ : ∀ φ : K ≃+* K,
      primeFormFieldFactor h hC (n := 3) (by norm_num) hq'
        (primeFormFieldHom h hC φ) = φ := by
    intro φ
    have := hfac (1 : primeFormUnitary h (C : Matrix (Fin 3) (Fin 3) K)) φ
    simpa using this
  have hfinj : Function.Injective (primeFormFieldHom h hC) := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 := hfacφ φ
    rw [hφ, map_one] at h1
    exact h1.symm
  have hinner_le_D : CFSG.ComponentClassification.OuterAutomorphisms.inner T ≤ primeFormD h (C : Matrix (Fin 3) (Fin 3) K) := by
    intro α hα
    obtain ⟨s, hs⟩ := (hinn α).1 hα
    exact ⟨⟨s, s.2.1⟩, hs.symm⟩
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨φ, -, rfl⟩ := hxF
    have hmem : primeFormFieldHom h hC φ ∈
        (primeFormFieldFactor h hC (n := 3) (by norm_num) hq').ker := by
      rw [hFker]
      exact hinner_le_D hxI
    have hφ1 : φ = 1 := by
      have h1 := (MonoidHom.mem_ker).mp hmem
      rw [hfacφ φ] at h1
      exact h1
    rw [hφ1, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K))
      (primeFormFieldHom h hC) hfinj).isCyclic.mp hScyc
  have hFp : IsPGroup p F := (S.isPGroup').map (primeFormFieldHom h hC)
  have hSylow : ∀ S : Sylow p (Outer T), (S : Subgroup (Outer T)).Normal := by
    obtain ⟨N, hN, -, hNcard, hQcyc⟩ :=
      CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter.unitary_outer_filtration
        h (n := 3) (by norm_num) hq'
    haveI := hN
    have hNle : Nat.card N ≤ p := by
      have h3 : Nat.card N ∣ 3 := hNcard.trans (Nat.gcd_dvd_left 3 _)
      have hle3 : Nat.card N ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      omega
    haveI : IsCyclic (Outer T ⧸ N) := hQcyc
    exact sylow_normal_of_quotient N hNle fun S => sylow_normal_of_isCyclic S
  have hgcd : ¬ p ∣ Nat.gcd 3 (p₀ ^ f + 1) := by
    intro hdvd
    have h3n : p ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
    have h3q : p ∣ p₀ ^ f + 1 := hdvd.trans (Nat.gcd_dvd_right 3 _)
    have hKsq : Nat.card K = (p₀ ^ f) ^ 2 := by
      rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have h2 := GL83.I713.two_le_pRank_statedPSU_of_dvd (K := K) (q := p₀ ^ f)
      (n := 3) (ℓ := p) hKsq hp hp2 (by norm_num) h3n h3q
    let ePU : primeFormP h (C : Matrix (Fin 3) (Fin 3) K) ≃* unitaryPSU h 3 :=
      Classical.choice (nonempty_primeFormP_mulEquiv h hC)
    let ePS : unitaryPSU h 3 ≃* StatedProj (StatedSU 3 (p₀ ^ f) K) :=
      unitaryPSUEquiv h (by norm_num)
    have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (ePU.trans ePS)
    have hpRank' : CFSG.Open.pRank p
        (⊤ : Subgroup (StatedProj (StatedSU 3 (p₀ ^ f) K))) ≤ 1 := by
      rwa [hEq] at hpRank
    exact Nat.not_le_of_lt (Nat.lt_of_le_of_lt hpRank' (by norm_num)) h2
  let φ : (K ≃+* K) →* Outer T :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)).comp (primeFormFieldHom h hC)
  let C' : Subgroup (Outer T) := (S : Subgroup (K ≃+* K)).map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) = C' := by
    dsimp [F, C', φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) =
      F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C'.index = (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : primeFormFieldHom h hC (x : K ≃+* K) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T))
          (primeFormFieldHom h hC (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner T) _).mp hx'
    have hxbot : primeFormFieldHom h hC (x : K ≃+* K) ∈ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
      ⟨Subgroup.mem_map_of_mem (primeFormFieldHom h hC) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C' = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C' = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C', φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (2 * f) p := by
    rw [Sylow.card_eq_multiplicity, hcardAut]
  have hOutEq : Nat.card (Outer T) = C'.index * p ^ Nat.factorization (2 * f) p := by
    have h1 := Subgroup.index_mul_card C'
    rw [hCcard, hScard] at h1
    exact h1.symm
  have hOut' : Nat.card (Outer T) = 2 * f * Nat.gcd 3 (p₀ ^ f + 1) := by
    simpa [T, C] using hOut
  set v := Nat.factorization (2 * f) p with hv
  set m := ordCompl[p] (2 * f) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : 2 * f = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (2 * f) p]
  have hout' : C'.index * p ^ v ∣ p ^ v * (m * Nat.gcd 3 (p₀ ^ f + 1)) := by
    have h := hOut'
    rw [hOutEq] at h
    rw [show 2 * f * Nat.gcd 3 (p₀ ^ f + 1) =
      p ^ v * (m * Nat.gcd 3 (p₀ ^ f + 1)) by rw [heq]; ring] at h
    rw [h]
  have hidxC : C'.index ∣ m * Nat.gcd 3 (p₀ ^ f + 1) := by
    have hpv0 : 0 < p ^ v := pow_pos hp.pos v
    rw [mul_comm C'.index (p ^ v)] at hout'
    exact (Nat.mul_dvd_mul_iff_left hpv0).mp hout'
  have hidxC' : ¬ p ∣ C'.index := by
    intro h
    rcases hp.dvd_mul.mp (h.trans hidxC) with h1 | h1
    · exact hpm h1
    · exact hgcd h1
  have hidx : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).index := by
    rw [← hCindex]
    exact hidxC'
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hidx

theorem i713ClauseFor_lie_A2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let Fq := GaloisField q.p q.exponent
  have hqcard : Nat.card Fq = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  let ePSL : (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ≃*
      projectiveSL 3 Fq :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 Fq)
  have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (eK.trans ePSL)
  have hpRank' : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL 3 Fq)) ≤ 1 := hEq ▸ hpRank
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans ePSL)
    (exists_fieldPart_projectiveSL_three Fq hp hp2 hpRank')))

theorem i713ClauseFor_lie_twistedA2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hpq, hf, -, h32⟩, L, _, _, hL, ⟨eL⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
      (G := (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) (MulEquiv.refl _)
  let hU : UnitaryFieldData q.p q.exponent L :=
    ⟨hpq, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  haveI : Finite L := hU.finite
  have hq2 : q.p ^ q.exponent ≠ 2 := by
    intro h2
    exact h32 (by rw [h2])
  have hC : IsPrimeFormGram (1 : GL (Fin 3) L) := isPrimeFormGram_one
  let ePU : primeFormP hU ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ≃*
      unitaryPSU hU 3 := Classical.choice (nonempty_primeFormP_mulEquiv hU hC)
  let ePS : unitaryPSU hU 3 ≃* StatedProj (StatedSU 3 (q.p ^ q.exponent) L) :=
    unitaryPSUEquiv hU (by norm_num)
  let eC : (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group ≃*
      primeFormP hU ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
    eL.trans (ePU.trans ePS).symm
  have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (eK.trans eC)
  have hpRank' : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP hU
      ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))) ≤ 1 := hEq ▸ hpRank
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eC)
    (exists_fieldPart_primeFormP_three hU hq2 hp hp2 hpRank')))

end CFSG.LieType.OutStructure

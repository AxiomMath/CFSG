module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

theorem twAC_card_le_mul_ker {D Q : Type*} [Group D] [Finite D] [Group Q] [IsCyclic Q] {p : ℕ}
    (hp : p.Prime) (hexp : ∀ x : D, x ^ p = 1) (f : D →* Q) :
    Nat.card D ≤ p * Nat.card f.ker := by
  have hexpα : Monoid.exponent f.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective y
    rw [← map_pow, hexp x, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card D = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [hsplit]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos hexpα)

theorem twAC_exists_ne_one {D A Q : Type*} [Group D] [Finite D] [Group A] [IsCyclic A] [Group Q]
    [IsCyclic Q] {p : ℕ} (hp : p.Prime) (hexp : ∀ x : D, x ^ p = 1) (hcard : p ^ 2 < Nat.card D)
    (α : D →* A) (β : α.ker →* Q) : ∃ x : α.ker, β x = 1 ∧ x ≠ 1 := by
  have h1 := twAC_card_le_mul_ker hp hexp α
  have hexp' : ∀ x : α.ker, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp (x : D))
  have h2 := twAC_card_le_mul_ker hp hexp' β
  have hp0 : 0 < p := hp.pos
  have hlt : 1 < Nat.card β.ker := by
    by_contra hle
    have hle' : Nat.card β.ker ≤ 1 := by omega
    have : Nat.card D ≤ p * (p * 1) :=
      h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ hle')))
    nlinarith
  have : Nontrivial β.ker := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : β.ker)
  exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩

theorem twAC_isCyclic_of_ker_le {G Q M : Type*} [Group G] [Group Q] [Group M] [IsCyclic M]
    (f : G →* Q) (hf : Function.Surjective f) (N : G →* M) (hker : N.ker ≤ f.ker) :
    IsCyclic Q := by
  let g : N.range →* Q :=
    (QuotientGroup.lift N.ker f hker).comp (QuotientGroup.quotientKerEquivRange N).symm.toMonoidHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := hf y
    refine ⟨QuotientGroup.quotientKerEquivRange N (QuotientGroup.mk a), ?_⟩
    simp [g]
  exact isCyclic_of_surjective g hg

section TwistedA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem twAC_exists_inner_primeFormP {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p ^ 2 < Nat.card D) :
    ∃ x ∈ D ⊓ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), x ≠ 1 := by
  classical
  have hfin := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set Dl := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDl
  set IT : Subgroup (MulAut T) := inner T with hIT
  have hIN : IT.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set F := primeFormFieldFactor h hC hn hq with hF
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  let α : D →* (K ≃+* K) := F.comp D.subtype
  have hcycQ : IsCyclic (Dl ⧸ IT.subgroupOf Dl) := by
    let c : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* Dl := (primeFormConjHom h _).rangeRestrict
    let f' : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* Dl ⧸ IT.subgroupOf Dl :=
      (QuotientGroup.mk' (IT.subgroupOf Dl)).comp c
    have hs : Function.Surjective f' :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective _)
    let δ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* Kˣ :=
      Matrix.GeneralLinearGroup.det.comp (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype
    have hδ : ∀ A, (δ A : K) = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det :=
      fun _ => rfl
    refine twAC_isCyclic_of_ker_le f' hs δ ?_
    intro A hA
    have hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      have h1 : δ A = 1 := hA
      have h2 := congrArg Units.val h1
      rw [hδ] at h2
      exact h2
    rw [MonoidHom.mem_ker]
    have hAS : (A : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := (mem_gramSU_iff_unitary h).2 ⟨A.2, hdet⟩
    have : (c A : MulAut T) = primeFormConjHom h _ A := rfl
    change QuotientGroup.mk (c A) = (1 : Dl ⧸ IT.subgroupOf Dl)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, this, mem_inner_primeFormP]
    exact ⟨⟨A, hAS⟩, rfl⟩
  let g : α.ker →* MulAut T := D.subtype.comp α.ker.subtype
  have hg : ∀ x : α.ker, g x ∈ Dl := by
    intro x
    rw [← hFker, MonoidHom.mem_ker]
    exact x.2
  let β : α.ker →* Dl ⧸ IT.subgroupOf Dl :=
    (QuotientGroup.mk' (IT.subgroupOf Dl)).comp (g.codRestrict Dl hg)
  obtain ⟨x, hβ, hx1⟩ := twAC_exists_ne_one hp (fun a : D => Subtype.ext (hexp a a.2)) hcard α β
  refine ⟨(x : D), ⟨(x : D).2, ?_⟩, fun h => hx1 (Subtype.ext (Subtype.ext h))⟩
  have hβ' : QuotientGroup.mk (g.codRestrict Dl hg x) =
      (1 : Dl ⧸ IT.subgroupOf Dl) := hβ
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hβ'
  exact hβ'

theorem lieOuterRankFamTwistedA : LieOuterRankFam .twistedA := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  set φ := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := twAC_exists_inner_primeFormP h (n := r + 1)
    (by omega) hq' hp (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      exact Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

end TwistedA

section TypeC

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem twAC_exists_inner_projectiveSp {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p ^ 2 < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range, x ≠ 1 := by
  classical
  have : NeZero r := ⟨by omega⟩
  set Dl := spLinearAutGroup r K with hDl
  set Es := spSemilinearAutGroup r K with hEs
  set I := (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range with hI
  have hIN : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hgen := (automorphism_generation (K := K) hr).1
  obtain ⟨-, -, hDnorm, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  have hDE : D ≤ Es := fun x hx => by rw [hEs, hgen]; exact Subgroup.mem_top x
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  let α : D →* Es ⧸ Dl.subgroupOf Es :=
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hDE)
  have hcycQ : IsCyclic (Dl ⧸ I.subgroupOf Dl) := by
    let c : gsp r K →* Dl := (conjAut r K).codRestrict Dl fun A => conjAut_mem_spLinearAutGroup A
    let f' : gsp r K →* Dl ⧸ I.subgroupOf Dl := (QuotientGroup.mk' (I.subgroupOf Dl)).comp c
    have hcs : Function.Surjective c := by
      rintro ⟨y, hy⟩
      obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hy
      exact ⟨A, rfl⟩
    have hs : Function.Surjective f' := (QuotientGroup.mk'_surjective _).comp hcs
    refine twAC_isCyclic_of_ker_le f' hs (multiplier r K) ?_
    intro A hA
    rw [ker_multiplier, Subgroup.mem_subgroupOf] at hA
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk (c A) = (1 : Dl ⧸ I.subgroupOf Dl)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h2 : A = ⟨((⟨_, hA⟩ : StatedSp r K) : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp hA⟩ := rfl
    have h3 : (c A : MulAut (StatedProj (StatedSp r K))) = conjAut r K A := rfl
    rw [h3, h2, conjAut_statedSp]
    exact ⟨_, rfl⟩
  let gg : α.ker →* MulAut (StatedProj (StatedSp r K)) := D.subtype.comp α.ker.subtype
  have hgg : ∀ x : α.ker, gg x ∈ Dl := by
    intro x
    have h : α x = 1 := x.2
    change QuotientGroup.mk (Subgroup.inclusion hDE (x : D)) =
      (1 : Es ⧸ Dl.subgroupOf Es) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  let β : α.ker →* Dl ⧸ I.subgroupOf Dl :=
    (QuotientGroup.mk' (I.subgroupOf Dl)).comp (gg.codRestrict Dl hgg)
  obtain ⟨x, hβ, hx1⟩ := twAC_exists_ne_one hp (fun a : D => Subtype.ext (hexp a a.2)) hcard α β
  refine ⟨(x : D), ⟨(x : D).2, ?_⟩, fun h => hx1 (Subtype.ext (Subtype.ext h))⟩
  have hβ' : QuotientGroup.mk (gg.codRestrict Dl hgg x) = (1 : Dl ⧸ I.subgroupOf Dl) := hβ
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hβ'
  exact hβ'

theorem lieOuterRankFamC : LieOuterRankFam .C := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨.C r q, hv⟩ :
    TauCeti.ValidLieTypeIndex)
  let K := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  let e : S ≃* StatedProj (StatedSp r K) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  set φ : MulAut S ≃* MulAut (StatedProj (StatedSp r K)) := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := twAC_exists_inner_projectiveSp
    (K := K) (r := r) hrange.1 hp (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      exact Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

end TypeC

end CFSG.HardMathSupport.Timmesfeld.DefChar

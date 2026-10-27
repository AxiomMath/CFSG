module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LieType.OutStructureHInputLinear
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed

public section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Generic

variable {X : Type*} [Group X] [Finite X] {L : Subgroup X} [L.Normal] {p : ℕ}

omit [Finite X] in
theorem not_mem_inner_mulAutCongr_conjHom (hL : CFSG.IsComponent L) {S : Type*} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {x : X}
    (hxU : x ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    MulAut.congr e (conjHom (L := L) x) ∉ inner S := by
  rintro ⟨z, hz⟩
  apply hxU
  rw [← mem_ker_conjOuterHom_iff hL, conjOuterHom_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  refine ⟨e.symm z, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hz]
  ext w
  simp [MulAut.congr]

theorem hInput_of_exists_of_fixRank (hL : CFSG.IsComponent L) {S : Type} [Group S] [Finite S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hFix : ∀ α : MulAut S, α ^ p = 1 → α ∉ inner S →
      CFSG.Open.pRank p (CFSG.autFixedSubgroup α) = CFSG.Open.pRank p (⊤ : Subgroup S))
    (hExists : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      ¬ (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) →
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧
        x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a := by
  intro hnot
  by_cases hc : ∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p
  · exact Or.inl hc
  · obtain ⟨x, hxord, hxU⟩ := hExists hnot hc
    refine Or.inr ⟨x, hxord, hxU, ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    let Z : Subgroup ↥L := Subgroup.center ↥L
    let T := ↥L ⧸ Z
    let α : MulAut ↥L := MulAut.conjNormal (H := L) x
    let a : MulAut T := conjHom (L := L) x
    have hxpow : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hαp : α ^ p = 1 := by
      change MulAut.conjNormal (H := L) x ^ p = 1
      rw [← map_pow, hxpow, map_one]
    have haq : CFSG.quotientAut α = a := quotientAut_conjNormal_eq_conjHom x
    have hRankT : CFSG.Open.pRank p (CFSG.autFixedSubgroup a) =
        CFSG.Open.pRank p (⊤ : Subgroup T) := by
      have h1 : CFSG.Open.pRank p (CFSG.autFixedSubgroup a) =
          CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) :=
        pRank_autFixedSubgroup_congr hp.one_lt e a
      have h2 : CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) =
          CFSG.Open.pRank p (⊤ : Subgroup S) :=
        hFix _ (by rw [← map_pow, ← map_pow, ← hxord, pow_orderOf_eq_one, map_one, map_one])
          (not_mem_inner_mulAutCongr_conjHom hL e hxU)
      have h3 : CFSG.Open.pRank p (⊤ : Subgroup S) = CFSG.Open.pRank p (⊤ : Subgroup T) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
      exact h1.trans (h2.trans h3)
    have hTrank : CFSG.Open.pRank p (⊤ : Subgroup T) = CFSG.Open.pRank p L := by
      calc CFSG.Open.pRank p (⊤ : Subgroup T)
          = CFSG.pRank p T := (CFSG.SectionRank.pRank_eq_open_pRank_top p T).symm
        _ = CFSG.pRank p ↥L :=
            CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp Z hZ
        _ = CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top p ↥L
        _ = CFSG.Open.pRank p L := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm
    obtain ⟨E₀, hE₀le, hE₀e, hE₀card⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (CFSG.autFixedSubgroup a)
    have hE₀card' : Nat.card E₀ = p ^ CFSG.Open.pRank p L := by
      rw [hE₀card, hRankT, hTrank]
    have hfix : CFSG.autFixedSubgroup a =
        (CFSG.autFixedSubgroup α).map (QuotientGroup.mk' Z) := by
      rw [← haq]
      exact autFixedSubgroup_quotientAut_eq_map hp α hαp hZ
    let C : Subgroup ↥L := CFSG.autFixedSubgroup α
    let ψ : ↥C →* T := (QuotientGroup.mk' Z).comp C.subtype
    have hrange : E₀ ≤ ψ.range := by
      rw [show ψ.range = C.map (QuotientGroup.mk' Z) from
        (MonoidHom.range_comp _ _).trans (by rw [Subgroup.range_subtype])]
      rw [← hfix]
      exact hE₀le
    have hker : ψ.ker = Z.subgroupOf C := by
      ext y
      exact (QuotientGroup.eq_one_iff (C.subtype y)).trans Subgroup.mem_subgroupOf.symm
    have hkerdvd : Nat.card ↥ψ.ker ∣ Nat.card ↥Z := by
      have hcard : Nat.card ↥ψ.ker = Nat.card ↥(Z ⊓ C) := by
        rw [hker, ← Subgroup.inf_subgroupOf_right Z C]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Z ⊓ C ≤ C)).toEquiv
      rw [hcard]
      exact Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ C ≤ Z)
    have hkerp : ¬ p ∣ Nat.card ↥ψ.ker := fun h => hZ (h.trans hkerdvd)
    obtain ⟨E', hE'e, hE'map, hE'card⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ hkerp hrange hE₀e
    have hinj : Function.Injective (L.subtype.comp C.subtype) := by
      intro y₁ y₂ h
      exact Subtype.ext (Subtype.ext h)
    refine ⟨E'.map (L.subtype.comp C.subtype), ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact (C.subtype y).2
    · exact hE'e.map (L.subtype.comp C.subtype)
    · rw [Subgroup.card_map_of_injective hinj, hE'card, hE₀card']
    · intro y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have hyC : α y' = y' := CFSG.mem_autFixedSubgroup.mp y'.2
      have hconj : x * (y' : X) * x⁻¹ = (y' : X) := by
        have h := congrArg Subtype.val hyC
        simpa [α, MulAut.conjNormal_apply] using h
      have hcomm : x * (y' : X) = (y' : X) * x := by
        calc x * (y' : X) = (x * (y' : X) * x⁻¹) * x := by group
          _ = (y' : X) * x := by rw [hconj]
      exact hcomm.symm

end Generic

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {n : ℕ}

theorem conjHom_mem_inner_of_pow_eq_one_unitary [Finite K] {p : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hA : primeFormConjHom h _ A ^ p = 1) :
    primeFormConjHom h _ A ∈
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  let a : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨primeFormConjHom h _ A, ⟨A, rfl⟩⟩
  let x : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := QuotientGroup.mk a
  have ha : a ^ p = 1 := Subtype.ext (by simpa [a] using hA)
  have hx : x ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
  have hdvd2 : orderOf x ∣ Nat.gcd n (ℓ ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hx) with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff a).mp h1)
  · rw [h1] at hdvd2
    exact absurd hdvd2 hdiv

theorem pRank_primeFormP_one [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hn : 1 ≤ n) (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    CFSG.Open.pRank p
        (⊤ : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      if p ∣ ℓ ^ f + 1 then n - 1 else n / orderOf (-((ℓ ^ f : ℕ) : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h hn]
    exact hdiv
  rw [CFSG.SectionRank.pRank_quotient_eq _ hZ, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU h,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    have := h.charP
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hdvd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp hdvd).symm
  have hpq : ¬ p ∣ ℓ ^ f := fun hdvd =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp h.prime).mp (hp.dvd_of_dvd_pow hdvd))
  split
  · exact CFSG.LocalAnalysis.RankThreeUC.S15.pRank_top_statedSU_eq_pred hn hpK hcard ‹_›
  · have : Fintype K := Fintype.ofFinite K
    exact CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSU_of_not_dvd hp hp2
      (by rw [← Nat.card_eq_fintype_card, hcard]) hpq ‹_› n hn

theorem pRank_autFixedSubgroup_fieldHom_eq [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hn : 3 ≤ n) (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup
        (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) =
      CFSG.Open.pRank p
        (⊤ : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpf, -⟩ := CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hmod : ((ℓ ^ f : ℕ) : ZMod p) = ((ℓ ^ (f / p) : ℕ) : ZMod p) := by
    rw [hq, Nat.cast_pow, ZMod.pow_card]
  have hdvd_iff : p ∣ ℓ ^ f + 1 ↔ p ∣ ℓ ^ (f / p) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_add,
      hmod]
  have hdiv₀ : ¬ p ∣ Nat.gcd n (ℓ ^ (f / p) + 1) := fun hd => hdiv (Nat.dvd_gcd
    (hd.trans (Nat.gcd_dvd_left _ _)) (hdvd_iff.mpr (hd.trans (Nat.gcd_dvd_right _ _))))
  have hrange := CFSG.RankThree.Classical.range_subfieldPSU_le h n h₀ hbar
  have hle : (CFSG.RankThree.Classical.subfieldPSU h h₀ hbar n).range ≤
      CFSG.autFixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    fun x hx => CFSG.mem_autFixedSubgroup.mpr (hrange hx)
  have hinj := CFSG.RankThree.Classical.subfieldPSU_injective h h₀ hbar n (by omega)
  refine le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt le_top) ?_
  calc CFSG.Open.pRank p
        (⊤ : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
      = if p ∣ ℓ ^ (f / p) + 1 then n - 1
          else n / orderOf (-((ℓ ^ (f / p) : ℕ) : ZMod p)) := by
        rw [pRank_primeFormP_one h hp hp2 hpℓ (by omega) hdiv, hmod]
        exact if_congr hdvd_iff rfl rfl
    _ = CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h₀
          ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
            Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)))) :=
        (pRank_primeFormP_one h₀ hp hp2 hpℓ (by omega) hdiv₀).symm
    _ = CFSG.Open.pRank p (CFSG.RankThree.Classical.subfieldPSU h h₀ hbar n).range :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MonoidHom.ofInjective hinj)).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ ≤ _ := CFSG.SectionRank.pRank_mono hp.one_lt hle

theorem pRank_autFixedSubgroup_eq_of_pow_eq_one_unitary [Finite K] {p : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hα : α ^ p = 1)
    (hout : α ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup α) =
      CFSG.Open.pRank p
        (⊤ : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have : NeZero n := ⟨by omega⟩
  obtain ⟨-, -, -, -, huniq, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨σ, ⟨A, rfl⟩, -⟩ := huniq α
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hα hout
    exact absurd (conjHom_mem_inner_of_pow_eq_one_unitary h hn hq hp hdiv A hα) hout
  obtain ⟨hord, H, hH⟩ :=
    CFSG.StandardType.RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn hq hp hp2 A σ hσ hα
  have hc : MulAut.congr (primeFormConjHom h _ H) (primeFormFieldHom h hC σ) =
      primeFormConjHom h _ A * primeFormFieldHom h hC σ := by
    rw [hH]
    ext z
    simp [MulAut.congr]
  rw [← hc, ← pRank_autFixedSubgroup_congr hp.one_lt (primeFormConjHom h _ H)
    (primeFormFieldHom h hC σ)]
  exact pRank_autFixedSubgroup_fieldHom_eq h hp hp2 hpℓ hn hdiv σ hord

end Unitary

theorem hInput_unitary_of_exists_of_cross {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] {p : ℕ} (hL : CFSG.IsComponent L) {ℓ f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K) {n : ℕ}
    (e : (↥L ⧸ Subgroup.center ↥L) ≃*
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hExists : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      ¬ (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) →
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧
        x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a :=
  have : Finite K := h.finite
  hInput_of_exists_of_fixRank hL e hp hZ
    (fun α hα hout => pRank_autFixedSubgroup_eq_of_pow_eq_one_unitary h hn hq hp hp2 hpℓ hdiv α
      hα hout) hExists

end CFSG.LieType.OutStructure

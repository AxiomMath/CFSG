module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUBlocks

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem psu_det_eq_one_of_commutator_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : Type} [Group Q] (hQ : commutator Q = ⊤)
    (ι : Q →* LinearMap.GeneralLinearGroup K V) (x : Q) :
    LinearMap.det ((ι x : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = 1 := by
  let δ : Q →* Kˣ := (Units.map (LinearMap.det : (V →ₗ[K] V) →* K)).comp ι
  have h1 : commutator Q ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hQ] at h1
  have hx : x ∈ δ.ker := h1 (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have := congrArg Units.val hx
  simpa [δ] using this

theorem psu_exists_involution_lift {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2) :
    ∃ T : sesqUnitaryGroup (idForm h n),
      (T : LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) ∧
      orderOf (QuotientGroup.mk T : sesqProjUnitary h (idForm h n)) = 2 := by
  have hA1 : primeFormConjHom h (idGram K n) A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, hcN, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn
    (A := A * A) (by rw [map_mul, hA2])
  have hAA : (A : GL (Fin n) K) * A = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_mul]
    exact hc
  set B := idForm h n with hBdef
  let T : sesqUnitaryGroup B :=
    ⟨Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K),
      (toLin_mem_sesqUnitaryGroup_iff _).mpr A.2⟩
  have hTcoe : ((T : LinearMap.GeneralLinearGroup K (Fin n → K))) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) := rfl
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    refine ⟨(c : K), hcN, ?_⟩
    have e1 : ((T * T : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) := by
      rw [← hAA, map_mul]
      rfl
    rw [e1, CatLeafProof.OddInner.toLin_scalar]
  have hTne : (QuotientGroup.mk T : sesqProjUnitary h B) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c', -, hc'⟩ := h1
    apply hA1
    have hcomm : ∀ g : GL (Fin n) K, (A : GL (Fin n) K) * g = g * A := by
      intro g
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ← hTcoe, hc', smul_mul_assoc, one_mul, mul_smul_comm,
        mul_one]
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [primeFormConjHom_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
      rw [hcomm, mul_inv_cancel_right]
  refine ⟨T, rfl, ?_⟩
  refine orderOf_eq_prime ?_ hTne
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact hTT

section Perfect

variable {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K)
  (A : primeFormUnitary h (idGram K n)) (T : sesqUnitaryGroup (idForm h n))
  (hT : (T : LinearMap.GeneralLinearGroup K (Fin n → K)) =
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))

include hT in
theorem psu_inner_perfect_hom {Q : Type} [Group Q] (ι : Q →* sesqUnitaryGroup (idForm h n))
    (hι : Function.Injective ι)
    (hc : ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))))
    (hQ : commutator Q = ⊤) :
    ∃ ρ : Q →* ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)),
      PSUIsTransfer h (primeFormConjHom h (idGram K n) A)
        ((sesqUnitaryGroup (idForm h n)).subtype.comp ι) ρ ∧ ρ.ker ≤ Subgroup.center Q := by
  refine psu_exists_hom_fixed_inner h A ((sesqUnitaryGroup (idForm h n)).subtype.comp ι)
    ((Subgroup.subtype_injective _).comp hι) (fun x => ?_) (fun x => ?_)
  · rw [mem_sesqSpecialUnitaryGroup]
    exact ⟨(ι x).2, psu_det_eq_one_of_commutator_eq_top hQ
      ((sesqUnitaryGroup (idForm h n)).subtype.comp ι) x⟩
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hc x)
    rw [← hT]
    exact congrArg Subtype.val h1

include hT in
theorem psu_inner_perfect_dvd {D : Subgroup ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A))}
    (hD : A6Hyp (primeFormConjHom h (idGram K n) A) D) {Q : Type} [Group Q]
    (ι : Q →* sesqUnitaryGroup (idForm h n)) (hι : Function.Injective ι)
    (hc : ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))))
    (hQ : commutator Q = ⊤) : Nat.card (Q ⧸ Subgroup.center Q) ∣ 360 := by
  haveI : Finite K := h.finite
  obtain ⟨ρ, -, hρ⟩ := psu_inner_perfect_hom h A T hT ι hι hc hQ
  exact hD.psu_central_quotient_dvd ρ hQ hρ

include hT in
theorem psu_inner_pair_false {D : Subgroup ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A))}
    (hD : A6Hyp (primeFormConjHom h (idGram K n) A) D) {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂]
    (ι₁ : Q₁ →* sesqUnitaryGroup (idForm h n)) (ι₂ : Q₂ →* sesqUnitaryGroup (idForm h n))
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hc₁ : ∀ x, ι₁ x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))))
    (hc₂ : ∀ x, ι₂ x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))))
    (hQ₁ : commutator Q₁ = ⊤) (hQ₂ : commutator Q₂ = ⊤)
    (hn₁ : Nat.card (Q₁ ⧸ Subgroup.center Q₁) = 360)
    (hn₂ : Nat.card (Q₂ ⧸ Subgroup.center Q₂) = 360)
    (hcomm : ∀ x y, ι₁ x * ι₂ y = ι₂ y * ι₁ x) : False := by
  haveI : Finite K := h.finite
  obtain ⟨ρ₁, hρ₁, hk₁⟩ := psu_inner_perfect_hom h A T hT ι₁ hι₁ hc₁ hQ₁
  obtain ⟨ρ₂, hρ₂, hk₂⟩ := psu_inner_perfect_hom h A T hT ι₂ hι₂ hc₂ hQ₂
  refine hD.psu_commuting_pair_false ρ₁ ρ₂ hQ₁ hQ₂ hk₁ hk₂ hn₁ hn₂ ?_
  exact PSUIsTransfer.commute h hρ₁ hρ₂ (fun x y => by
    have := congrArg Subtype.val (hcomm x y)
    exact this)

end Perfect

section Embed

theorem psu_emb_left {G U₁ U₂ : Type} [Group G] [Group U₁] [Group U₂] (C : Subgroup G)
    (e : C ≃* U₁ × U₂) {Q : Type} [Group Q] (j : Q →* U₁) (hj : Function.Injective j) :
    ∃ ι : Q →* G, Function.Injective ι ∧ ∀ x, ι x ∈ C :=
  ⟨C.subtype.comp (e.symm.toMonoidHom.comp ((MonoidHom.inl U₁ U₂).comp j)),
    (Subgroup.subtype_injective _).comp (e.symm.injective.comp (fun a b hab =>
      hj (congrArg Prod.fst hab))), fun x => (e.symm (j x, 1)).2⟩

theorem psu_emb_right {G U₁ U₂ : Type} [Group G] [Group U₁] [Group U₂] (C : Subgroup G)
    (e : C ≃* U₁ × U₂) {Q : Type} [Group Q] (j : Q →* U₂) (hj : Function.Injective j) :
    ∃ ι : Q →* G, Function.Injective ι ∧ ∀ x, ι x ∈ C :=
  ⟨C.subtype.comp (e.symm.toMonoidHom.comp ((MonoidHom.inr U₁ U₂).comp j)),
    (Subgroup.subtype_injective _).comp (e.symm.injective.comp (fun a b hab =>
      hj (congrArg Prod.snd hab))), fun x => (e.symm (1, j x)).2⟩

theorem psu_emb_gl {G U : Type} [Group G] [Group U] (C : Subgroup G) (e : C ≃* U) {Q : Type}
    [Group Q] (j : Q →* U) (hj : Function.Injective j) :
    ∃ ι : Q →* G, Function.Injective ι ∧ ∀ x, ι x ∈ C :=
  ⟨C.subtype.comp (e.symm.toMonoidHom.comp j),
    (Subgroup.subtype_injective _).comp (e.symm.injective.comp hj), fun x => (e.symm (j x)).2⟩

theorem psu_emb_pair {G U₁ U₂ : Type} [Group G] [Group U₁] [Group U₂] (C : Subgroup G)
    (e : C ≃* U₁ × U₂) {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] (j₁ : Q₁ →* U₁) (j₂ : Q₂ →* U₂)
    (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂) :
    ∃ (ι₁ : Q₁ →* G) (ι₂ : Q₂ →* G), Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ x, ι₁ x ∈ C) ∧ (∀ y, ι₂ y ∈ C) ∧ ∀ x y, ι₁ x * ι₂ y = ι₂ y * ι₁ x := by
  refine ⟨C.subtype.comp (e.symm.toMonoidHom.comp ((MonoidHom.inl U₁ U₂).comp j₁)),
    C.subtype.comp (e.symm.toMonoidHom.comp ((MonoidHom.inr U₁ U₂).comp j₂)),
    (Subgroup.subtype_injective _).comp (e.symm.injective.comp (fun a b hab =>
      hj₁ (congrArg Prod.fst hab))),
    (Subgroup.subtype_injective _).comp (e.symm.injective.comp (fun a b hab =>
      hj₂ (congrArg Prod.snd hab))),
    fun x => (e.symm (j₁ x, 1)).2, fun y => (e.symm (1, j₂ y)).2, fun x y => ?_⟩
  have h1 : e.symm (j₁ x, 1) * e.symm (1, j₂ y) = e.symm (1, j₂ y) * e.symm (j₁ x, 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp
  exact congrArg Subtype.val h1

end Embed

section Analysis

variable {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K)

theorem psu_inner_split_false (hO : LieOrderFormulasInput) (hn : 3 ≤ n)
    (hnot : ¬ ((n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1)))
    (T : sesqUnitaryGroup (idForm h n)) (P M : Submodule K (Fin n → K))
    (hP1 : 1 ≤ finrank K P) (hM1 : 1 ≤ finrank K M) (hrs : finrank K P + finrank K M = n)
    (hlP : ((idForm h n).domRestrict₁₂ P P).SeparatingLeft)
    (hlM : ((idForm h n).domRestrict₁₂ M M).SeparatingLeft)
    (e : Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))) ≃*
      sesqUnitaryGroup ((idForm h n).domRestrict₁₂ P P) ×
        sesqUnitaryGroup ((idForm h n).domRestrict₁₂ M M))
    (hW1 : ∀ {Q : Type} [Group Q] (ι : Q →* sesqUnitaryGroup (idForm h n)),
      Function.Injective ι →
      (∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      commutator Q = ⊤ → Nat.card (Q ⧸ Subgroup.center Q) ∣ 360)
    (hW2 : ∀ {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] (ι₁ : Q₁ →* sesqUnitaryGroup (idForm h n))
      (ι₂ : Q₂ →* sesqUnitaryGroup (idForm h n)), Function.Injective ι₁ → Function.Injective ι₂ →
      (∀ x, ι₁ x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      (∀ x, ι₂ x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      commutator Q₁ = ⊤ → commutator Q₂ = ⊤ →
      Nat.card (Q₁ ⧸ Subgroup.center Q₁) = 360 → Nat.card (Q₂ ⧸ Subgroup.center Q₂) = 360 →
      (∀ x y, ι₁ x * ι₂ y = ι₂ y * ι₁ x) → False) : False := by
  have hsymm : ∀ Pm : Submodule K (Fin n → K), ((idForm h n).domRestrict₁₂ Pm Pm).IsSymm :=
    fun Pm => ⟨fun x y => (idForm_isSymm h n).eq (x : Fin n → K) (y : Fin n → K)⟩
  have h327 : ¬ (27 ∣ 360) := by decide
  have hfpos := h.one_le
  have hbig : ∀ (Pm : Submodule K (Fin n → K)),
      ((idForm h n).domRestrict₁₂ Pm Pm).SeparatingLeft → 3 ≤ finrank K Pm →
      ∀ {U : Type} [Group U] (emb : ∀ {Q : Type} [Group Q] (j : Q →* sesqUnitaryGroup
        ((idForm h n).domRestrict₁₂ Pm Pm)), Function.Injective j →
          ∃ ι : Q →* sesqUnitaryGroup (idForm h n), Function.Injective ι ∧
            ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))),
      False := by
    intro Pm hl h3 U _ emb
    obtain ⟨Q, _, j, hj, hperf, h27⟩ := psu_exists_perfect_unitary_three h (hsymm Pm) hl h3
    obtain ⟨ι, hι, hc⟩ := emb j hj
    exact h327 (h27.trans (hW1 ι hι hc hperf))
  have hdim2 : ∀ (Pm : Submodule K (Fin n → K)),
      ((idForm h n).domRestrict₁₂ Pm Pm).SeparatingLeft → finrank K Pm = 2 → 3 ≤ f →
      (∀ {Q : Type} [Group Q] (j : Q →* sesqUnitaryGroup
        ((idForm h n).domRestrict₁₂ Pm Pm)), Function.Injective j →
          ∃ ι : Q →* sesqUnitaryGroup (idForm h n), Function.Injective ι ∧
            ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      False := by
    intro Pm hl h2 hf3 emb
    obtain ⟨Q, _, j, hj, hperf, h27, -⟩ := psu_exists_perfect_unitary_two h hO (hsymm Pm) hl h2
      (by omega)
    obtain ⟨ι, hι, hc⟩ := emb j hj
    exact h327 ((h27 hf3).trans (hW1 ι hι hc hperf))
  have embP : ∀ {Q : Type} [Group Q] (j : Q →* sesqUnitaryGroup
      ((idForm h n).domRestrict₁₂ P P)), Function.Injective j →
      ∃ ι : Q →* sesqUnitaryGroup (idForm h n), Function.Injective ι ∧
        ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))) :=
    fun j hj => psu_emb_left _ e j hj
  have embM : ∀ {Q : Type} [Group Q] (j : Q →* sesqUnitaryGroup
      ((idForm h n).domRestrict₁₂ M M)), Function.Injective j →
      ∃ ι : Q →* sesqUnitaryGroup (idForm h n), Function.Injective ι ∧
        ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))) :=
    fun j hj => psu_emb_right _ e j hj
  by_cases hP3 : 3 ≤ finrank K P
  · exact hbig P hlP hP3 (U := Unit) embP
  by_cases hM3 : 3 ≤ finrank K M
  · exact hbig M hlM hM3 (U := Unit) embM
  by_cases hf3 : 3 ≤ f
  ·
    by_cases hP2 : finrank K P = 2
    · exact hdim2 P hlP hP2 hf3 embP
    · have hM2 : finrank K M = 2 := by omega
      exact hdim2 M hlM hM2 hf3 embM
  ·
    have hn4 : n = 4 ∧ f = 2 := by omega
    obtain ⟨hn4, hf2⟩ := hn4
    have hP2 : finrank K P = 2 := by omega
    have hM2 : finrank K M = 2 := by omega
    obtain ⟨Q₁, _, j₁, hj₁, hperf₁, -, hc₁⟩ := psu_exists_perfect_unitary_two h hO (hsymm P) hlP hP2
      (by omega)
    obtain ⟨Q₂, _, j₂, hj₂, hperf₂, -, hc₂⟩ := psu_exists_perfect_unitary_two h hO (hsymm M) hlM hM2
      (by omega)
    obtain ⟨ι₁, ι₂, hι₁, hι₂, hcc₁, hcc₂, hcomm⟩ := psu_emb_pair _ e j₁ j₂ hj₁ hj₂
    exact hW2 ι₁ ι₂ hι₁ hι₂ hcc₁ hcc₂ hperf₁ hperf₂ (hc₁ hf2) (hc₂ hf2) hcomm

theorem psu_inner_paired_false (hO : LieOrderFormulasInput) (hn : 3 ≤ n)
    (hnot : ¬ ((n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1)))
    (T : sesqUnitaryGroup (idForm h n)) (P : Submodule K (Fin n → K))
    (hdim : 2 * finrank K P = n)
    (e : Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))) ≃*
      LinearMap.GeneralLinearGroup K P)
    (hW1 : ∀ {Q : Type} [Group Q] (ι : Q →* sesqUnitaryGroup (idForm h n)),
      Function.Injective ι →
      (∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      commutator Q = ⊤ → Nat.card (Q ⧸ Subgroup.center Q) ∣ 360) : False := by
  have hfpos := h.one_le
  have hm : 2 ≤ finrank K P := by omega
  have hcase : 3 ≤ finrank K P ∨ 2 ≤ f := by omega
  obtain ⟨Q, _, j, hj, hperf, h27⟩ := psu_exists_perfect_GL h hO hm hcase
  have h327 : ¬ (27 ∣ 360) := by decide
  obtain ⟨ι, hι, hc⟩ := psu_emb_gl (Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n))))
    e j hj
  exact h327 (h27.trans (hW1 ι hι hc hperf))

end Analysis

theorem psuInner_false (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n)
    (hnot : ¬ ((n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1)))
    (A : primeFormUnitary h (idGram K n))
    (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {D : Subgroup ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A))}
    (hD : A6Hyp (primeFormConjHom h (idGram K n) A) D) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  obtain ⟨T, hT, hT2⟩ := psu_exists_involution_lift h hn A hA
  have hdimV : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hnV : 2 ≤ finrank K (Fin n → K) := by omega
  obtain ⟨l, -, -, hN, hP, hM, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h (by norm_num : (3 : ℕ) ≠ 2) hnV
      (idForm_isSymm h n) (idForm_separatingLeft h n) hT2
  have hW1 : ∀ {Q : Type} [Group Q] (ι : Q →* sesqUnitaryGroup (idForm h n)),
      Function.Injective ι →
      (∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h n)))) →
      commutator Q = ⊤ → Nat.card (Q ⧸ Subgroup.center Q) ∣ 360 :=
    fun ι hι hc hQ => psu_inner_perfect_dvd h A T hT hD ι hι hc hQ
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have hr := Submodule.finrank_add_eq_of_isCompl hcompl
    refine psu_inner_split_false h hO hn hnot T _ _ (Submodule.one_le_finrank_iff.mpr hP)
      (Submodule.one_le_finrank_iff.mpr hM) (by omega) hlP hlM e hW1 ?_
    intro Q₁ Q₂ _ _ ι₁ ι₂ hι₁ hι₂ hc₁ hc₂ hQ₁ hQ₂ hn₁ hn₂ hcomm
    exact psu_inner_pair_false h A T hT hD ι₁ ι₂ hι₁ hι₂ hc₁ hc₂ hQ₁ hQ₂ hn₁ hn₂ hcomm
  · obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    exact psu_inner_paired_false h hO hn hnot T _ (by omega) e hW1

end CFSG.ComponentClassification.CatFC

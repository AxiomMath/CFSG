module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup
open scoped commutatorElement

section Counting

variable {X : Type*} [Group X]

private theorem relIndex_sup_eq_of_le_normalizer {H N : Subgroup X}
    (h : H ≤ normalizer (N : Set X)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  haveI : (N.subgroupOf (H ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv).symm

private theorem le_normalizer_sup {H P O : Subgroup X}
    (hP : ∀ k ∈ H, ∀ x ∈ P, k * x * k⁻¹ ∈ P ⊔ O)
    (hO : ∀ k ∈ H, ∀ x ∈ O, k * x * k⁻¹ ∈ P ⊔ O) :
    H ≤ normalizer ((P ⊔ O : Subgroup X) : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  have h : P ⊔ O ≤ (P ⊔ O).comap (MulAut.conj k).toMonoidHom :=
    sup_le (fun y hy => by simpa using hP k hk y hy) (fun y hy => by simpa using hO k hk y hy)
  simpa using h hx

private theorem relIndex_sup_eq_mul {E M O : Subgroup X} (hOM : O ≤ M)
    (hEM : E ≤ normalizer (M : Set X)) (hinf : E ⊓ M = O) :
    O.relIndex (E ⊔ M) = O.relIndex M * O.relIndex E := by
  have h1 : M.relIndex E = O.relIndex E := by
    rw [← hinf]
    exact (Subgroup.inf_relIndex_left E M).symm
  rw [← Subgroup.relIndex_mul_relIndex O M (E ⊔ M) hOM le_sup_right,
    relIndex_sup_eq_of_le_normalizer hEM, h1]

private theorem relIndex_iSup_sup_eq_prod {ι : Type*} [DecidableEq ι] (K : ι → Subgroup X)
    (O : Subgroup X) (hKO : ∀ i, K i ≤ normalizer (O : Set X))
    (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ O)
    (hind : ∀ i, (K i ⊔ O) ⊓ ((⨆ j ≠ i, K j) ⊔ O) ≤ O) (s : Finset ι) :
    O.relIndex ((⨆ i ∈ s, K i) ⊔ O) = ∏ i ∈ s, O.relIndex (K i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hKM : ∀ i, K i ≤ normalizer ((K a ⊔ O : Subgroup X) : Set X) := by
      intro i
      by_cases hia : i = a
      · rw [hia]
        exact le_sup_left.trans Subgroup.le_normalizer
      · refine le_normalizer_sup ?_ ?_
        · intro k hk x hx
          have h1 : ⁅k, x⁆ ∈ O := hcomm i a hia (Subgroup.commutator_mem_commutator hk hx)
          have h2 : k * x * k⁻¹ = ⁅k, x⁆ * x := by simp [commutatorElement_def]
          rw [h2]
          exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hx)
        · intro k hk x hx
          exact Subgroup.mem_sup_right (Subgroup.le_normalizer_iff.mp (hKO i) k hk x hx)
    have hEM : (⨆ i ∈ s, K i) ⊔ O ≤ normalizer ((K a ⊔ O : Subgroup X) : Set X) :=
      sup_le (iSup₂_le fun i _ => hKM i) (le_sup_right.trans Subgroup.le_normalizer)
    have hE' : (⨆ i ∈ s, K i) ⊔ O ≤ (⨆ j ≠ a, K j) ⊔ O := by
      refine sup_le_sup_right (iSup₂_le fun i hi => ?_) O
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      exact le_iSup₂_of_le i hia le_rfl
    have hEinfM : ((⨆ i ∈ s, K i) ⊔ O) ⊓ (K a ⊔ O) = O := by
      refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
      calc ((⨆ i ∈ s, K i) ⊔ O) ⊓ (K a ⊔ O) = (K a ⊔ O) ⊓ ((⨆ i ∈ s, K i) ⊔ O) := inf_comm _ _
        _ ≤ (K a ⊔ O) ⊓ ((⨆ j ≠ a, K j) ⊔ O) := inf_le_inf_left _ hE'
        _ ≤ O := hind a
    have hsup : (⨆ i ∈ insert a s, K i) ⊔ O =
        ((⨆ i ∈ s, K i) ⊔ O) ⊔ (K a ⊔ O) := by
      rw [Finset.iSup_insert]
      apply le_antisymm
      · exact sup_le (sup_le (le_sup_of_le_right le_sup_left) (le_sup_of_le_left le_sup_left))
          (le_sup_of_le_left le_sup_right)
      · exact sup_le (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
    rw [hsup, Finset.prod_insert ha,
      relIndex_sup_eq_mul le_sup_right hEM hEinfM,
      relIndex_sup_eq_of_le_normalizer (hKO a), ih]

private theorem relIndex_iSup_sup_eq_prod_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Subgroup X) (O : Subgroup X) (hKO : ∀ i, K i ≤ normalizer (O : Set X))
    (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ O) (hind : ∀ i, (K i ⊔ O) ⊓ ((⨆ j ≠ i, K j) ⊔ O) ≤ O) :
    O.relIndex ((⨆ i, K i) ⊔ O) = ∏ i, O.relIndex (K i) := by
  simpa using relIndex_iSup_sup_eq_prod K O hKO hcomm hind Finset.univ

end Counting

section PCore

variable {X : Type*} [Group X]

private theorem map_pCore_subgroupOf (D : Subgroup X) :
    ((CFSG.pCore 2 ↥D).map D.subtype).subgroupOf D = CFSG.pCore 2 ↥D :=
  Subgroup.comap_map_eq_self_of_injective D.subtype_injective _

private theorem le_normalizer_map_pCore (D : Subgroup X) :
    D ≤ normalizer (((CFSG.pCore 2 ↥D).map D.subtype : Subgroup X) : Set X) := by
  have h : (CFSG.pCore 2 ↥D).map D.subtype ≤ D := Subgroup.map_subtype_le _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer h).mp ?_
  rw [map_pCore_subgroupOf]
  infer_instance

private theorem isPGroup_map_pCore (D : Subgroup X) :
    IsPGroup 2 ((CFSG.pCore 2 ↥D).map D.subtype) :=
  CFSG.pCore_isPGroup.map D.subtype

private theorem le_map_pCore_of_normalizes {D R : Subgroup X} (hRD : R ≤ D)
    (hDR : D ≤ normalizer (R : Set X)) (hR : IsPGroup 2 R) :
    R ≤ (CFSG.pCore 2 ↥D).map D.subtype := by
  haveI : (R.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRD).mpr hDR
  have hS : IsPGroup 2 (R.subgroupOf D) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRD).symm
  have hmem : R.subgroupOf D ∈ {K : Subgroup ↥D | K.Normal ∧ IsPGroup 2 K} :=
    ⟨inferInstance, hS⟩
  have hle : R.subgroupOf D ≤ CFSG.pCore 2 ↥D := le_sSup hmem
  intro x hx
  exact ⟨⟨x, hRD hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem subgroupOf_eq_pCore {A O : Subgroup X} (hAO : A ≤ normalizer (O : Set X))
    (hO : IsPGroup 2 O) (hle : (CFSG.pCore 2 ↥A).map A.subtype ≤ O) :
    O.subgroupOf A = CFSG.pCore 2 ↥A := by
  apply le_antisymm
  · haveI : (O.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAO
    have hmem : O.subgroupOf A ∈ {K : Subgroup ↥A | K.Normal ∧ IsPGroup 2 K} :=
      ⟨inferInstance, hO.comap_subtype⟩
    exact le_sSup hmem
  · exact Subgroup.map_le_iff_le_comap.mp hle

private theorem map_pCore_le_of_comm {ι : Type*} (K : ι → Subgroup X) (i₀ : ι) {D O : Subgroup X}
    (hD : D = ⨆ j, K j) (hO : O = (CFSG.pCore 2 ↥D).map D.subtype)
    (hcomm : ∀ j, j ≠ i₀ → ⁅K j, K i₀⁆ ≤ O) :
    (CFSG.pCore 2 ↥(K i₀)).map (K i₀).subtype ≤ O := by
  obtain ⟨P, hP⟩ : ∃ P : Subgroup X, P = (CFSG.pCore 2 ↥(K i₀)).map (K i₀).subtype :=
    ⟨_, rfl⟩
  rw [← hP]
  have hKD : ∀ j, K j ≤ D := fun j => by rw [hD]; exact le_iSup K j
  have hDO : D ≤ normalizer (O : Set X) := by rw [hO]; exact le_normalizer_map_pCore D
  have hOD : O ≤ D := by rw [hO]; exact Subgroup.map_subtype_le _
  have hO2 : IsPGroup 2 O := by rw [hO]; exact isPGroup_map_pCore D
  have hPA : P ≤ K i₀ := by rw [hP]; exact Subgroup.map_subtype_le _
  have hAP : K i₀ ≤ normalizer (P : Set X) := by rw [hP]; exact le_normalizer_map_pCore (K i₀)
  have hP2 : IsPGroup 2 P := by rw [hP]; exact isPGroup_map_pCore (K i₀)
  have hDPO : D ≤ normalizer ((P ⊔ O : Subgroup X) : Set X) := by
    rw [hD]
    refine iSup_le fun j => ?_
    by_cases hj : j = i₀
    · rw [hj]
      refine le_normalizer_sup ?_ ?_
      · intro k hk x hx
        exact Subgroup.mem_sup_left (Subgroup.le_normalizer_iff.mp hAP k hk x hx)
      · intro k hk x hx
        exact Subgroup.mem_sup_right
          (Subgroup.le_normalizer_iff.mp ((hKD i₀).trans hDO) k hk x hx)
    · refine le_normalizer_sup ?_ ?_
      · intro k hk x hx
        have h1 : ⁅k, x⁆ ∈ O := hcomm j hj (Subgroup.commutator_mem_commutator hk (hPA hx))
        have h2 : k * x * k⁻¹ = ⁅k, x⁆ * x := by simp [commutatorElement_def]
        rw [h2]
        exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hx)
      · intro k hk x hx
        exact Subgroup.mem_sup_right
          (Subgroup.le_normalizer_iff.mp ((hKD j).trans hDO) k hk x hx)
  have hPOp : IsPGroup 2 ↥(P ⊔ O) :=
    IsPGroup.to_sup_of_normal_right' hP2 hO2 (hPA.trans ((hKD i₀).trans hDO))
  have hle := le_map_pCore_of_normalizes (D := D) (R := P ⊔ O)
    (sup_le (hPA.trans (hKD i₀)) hOD) hDPO hPOp
  rw [← hO] at hle
  exact le_sup_left.trans hle

theorem card_quotient_pCore_eq_prod_of_indep {ι : Type*} [Fintype ι] (K : ι → Subgroup X)
    (D O : Subgroup X) (hD : D = ⨆ i, K i) (hO : O = (CFSG.pCore 2 ↥D).map D.subtype)
    (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ O)
    (hind : ∀ i, (K i ⊔ O) ⊓ ((⨆ j ≠ i, K j) ⊔ O) ≤ O) :
    Nat.card (↥D ⧸ CFSG.pCore 2 ↥D) = ∏ i, Nat.card (↥(K i) ⧸ CFSG.pCore 2 ↥(K i)) := by
  classical
  have hKD : ∀ i, K i ≤ D := fun i => by rw [hD]; exact le_iSup K i
  have hDO : D ≤ normalizer (O : Set X) := by rw [hO]; exact le_normalizer_map_pCore D
  have hOD : O ≤ D := by rw [hO]; exact Subgroup.map_subtype_le _
  have hO2 : IsPGroup 2 O := by rw [hO]; exact isPGroup_map_pCore D
  have h1 := relIndex_iSup_sup_eq_prod_univ K O (fun i => (hKD i).trans hDO) hcomm hind
  have hDsup : (⨆ i, K i) ⊔ O = D := by rw [← hD]; exact sup_eq_left.mpr hOD
  rw [hDsup] at h1
  have hsubD : O.subgroupOf D = CFSG.pCore 2 ↥D := by rw [hO]; exact map_pCore_subgroupOf D
  have hL : O.relIndex D = Nat.card (↥D ⧸ CFSG.pCore 2 ↥D) := by
    rw [Subgroup.relIndex, hsubD, Subgroup.index_eq_card]
  have hR : ∀ i, O.relIndex (K i) = Nat.card (↥(K i) ⧸ CFSG.pCore 2 ↥(K i)) := by
    intro i
    have hsub := subgroupOf_eq_pCore ((hKD i).trans hDO) hO2
      (map_pCore_le_of_comm K i hD hO (fun j hj => hcomm j i hj))
    rw [Subgroup.relIndex, hsub, Subgroup.index_eq_card]
  rw [← hL, h1]
  exact Finset.prod_congr rfl fun i _ => hR i

end PCore

section Conjugates

variable {X : Type} [Group X] [Finite X]

private theorem mem_map_conj_iff (J : Subgroup X) (y z : X) :
    z ∈ J.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ J := by
  rw [Subgroup.mem_map_equiv]
  rfl

private theorem map_conj_eq_iff (J : Subgroup X) (y y' : X) :
    J.map (MulAut.conj y).toMonoidHom = J.map (MulAut.conj y').toMonoidHom ↔
      y⁻¹ * y' ∈ normalizer (J : Set X) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := SetLike.ext_iff.mp h (y' * x * y'⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at h1
    have e1 : y'⁻¹ * (y' * x * y'⁻¹) * y' = x := by group
    have e2 : y⁻¹ * y' * x * (y⁻¹ * y')⁻¹ = y⁻¹ * (y' * x * y'⁻¹) * y := by group
    rw [e1] at h1
    rw [e2]
    exact h1.symm
  · intro h
    ext z
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have h1 := Subgroup.mem_normalizer_iff.mp h (y'⁻¹ * z * y')
    have e : y⁻¹ * y' * (y'⁻¹ * z * y') * (y⁻¹ * y')⁻¹ = y⁻¹ * z * y := by group
    rw [e] at h1
    exact h1.symm

theorem SolvThreeDirectCond.of_indep (X₀ J D O : Subgroup X)
    (hD : D = ⨆ y ∈ X₀, J.map (MulAut.conj y).toMonoidHom)
    (hO : O = (CFSG.pCore 2 ↥D).map D.subtype)
    (hcomm : ∀ y₁ ∈ X₀, ∀ y₂ ∈ X₀,
      J.map (MulAut.conj y₁).toMonoidHom ≠ J.map (MulAut.conj y₂).toMonoidHom →
        ⁅J.map (MulAut.conj y₁).toMonoidHom, J.map (MulAut.conj y₂).toMonoidHom⁆ ≤ O)
    (hind : ∀ y ∈ X₀, (J.map (MulAut.conj y).toMonoidHom ⊔ O) ⊓
      ((⨆ y' ∈ X₀, ⨆ (_ : J.map (MulAut.conj y').toMonoidHom ≠ J.map (MulAut.conj y).toMonoidHom),
        J.map (MulAut.conj y').toMonoidHom) ⊔ O) ≤ O) :
    SolvThreeDirectCond X₀ J := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup X₀, N = (normalizer (J : Set X) ⊓ X₀).subgroupOf X₀ :=
    ⟨_, rfl⟩
  obtain ⟨cj, hcj⟩ : ∃ cj : X → Subgroup X, ∀ y, cj y = J.map (MulAut.conj y).toMonoidHom :=
    ⟨_, fun _ => rfl⟩
  have hN : ∀ a b : X₀, a⁻¹ * b ∈ N ↔ cj a = cj b := by
    intro a b
    rw [hcj, hcj, map_conj_eq_iff, hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (a⁻¹ * b).2⟩⟩
  have hwd : ∀ a b : X₀, QuotientGroup.leftRel N a b → cj a = cj b := fun a b hab =>
    (hN a b).mp (QuotientGroup.leftRel_apply.mp hab)
  obtain ⟨f, hf⟩ : ∃ f : X₀ ⧸ N → Subgroup X, ∀ a : X₀, f (QuotientGroup.mk a) = cj a :=
    ⟨Quotient.lift (fun a : X₀ => cj a) hwd, fun a => rfl⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective i
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective j
    rw [hf, hf] at hij
    exact QuotientGroup.eq.mpr ((hN a b).mpr hij)
  have hfmem : ∀ i, ∃ y ∈ X₀, f i = cj y := by
    intro i
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective i
    exact ⟨a, a.2, hf a⟩
  have hfsurj : ∀ y ∈ X₀, ∃ i, f i = cj y := fun y hy => ⟨QuotientGroup.mk ⟨y, hy⟩, hf ⟨y, hy⟩⟩
  have hDf : D = ⨆ i, f i := by
    rw [hD]
    apply le_antisymm
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨i, hi⟩ := hfsurj y hy
      rw [← hcj, ← hi]
      exact le_iSup f i
    · refine iSup_le fun i => ?_
      obtain ⟨y, hy, hi⟩ := hfmem i
      rw [hi, hcj]
      exact le_iSup₂_of_le y hy le_rfl
  have hcomm' : ∀ i j, i ≠ j → ⁅f i, f j⁆ ≤ O := by
    intro i j hij
    obtain ⟨y₁, hy₁, h₁⟩ := hfmem i
    obtain ⟨y₂, hy₂, h₂⟩ := hfmem j
    have hne : cj y₁ ≠ cj y₂ := fun h => hij (hfinj (h₁.trans (h.trans h₂.symm)))
    rw [h₁, h₂, hcj, hcj]
    rw [hcj, hcj] at hne
    exact hcomm y₁ hy₁ y₂ hy₂ hne
  have hind' : ∀ i, (f i ⊔ O) ⊓ ((⨆ j ≠ i, f j) ⊔ O) ≤ O := by
    intro i
    obtain ⟨y, hy, hi⟩ := hfmem i
    have hle : (⨆ j ≠ i, f j) ≤ ⨆ y' ∈ X₀,
        ⨆ (_ : J.map (MulAut.conj y').toMonoidHom ≠ J.map (MulAut.conj y).toMonoidHom),
          J.map (MulAut.conj y').toMonoidHom := by
      refine iSup₂_le fun j hj => ?_
      obtain ⟨y', hy', hj'⟩ := hfmem j
      have hne : J.map (MulAut.conj y').toMonoidHom ≠ J.map (MulAut.conj y).toMonoidHom := by
        rw [← hcj, ← hcj]
        exact fun h => hj (hfinj (hj'.trans (h.trans hi.symm)))
      refine le_iSup₂_of_le y' hy' (le_iSup_of_le hne ?_)
      rw [hj', hcj]
    rw [hi, hcj]
    exact (inf_le_inf (le_refl _) (sup_le_sup_right hle O)).trans (hind y hy)
  haveI : Fintype (X₀ ⧸ N) := Fintype.ofFinite _
  have key := card_quotient_pCore_eq_prod_of_indep f D O hDf hO hcomm' hind'
  have hfac : ∀ i, Nat.card (↥(f i) ⧸ CFSG.pCore 2 ↥(f i)) =
      Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) := by
    intro i
    obtain ⟨y, hy, hi⟩ := hfmem i
    rw [hi, hcj]
    exact (Nat.card_congr (QuotientGroup.congr (CFSG.pCore 2 ↥J)
      (CFSG.pCore 2 ↥(J.map (MulAut.conj y).toMonoidHom)) (MulEquiv.subgroupMap (MulAut.conj y) J)
      (CFSG.pCore_map_iso 2 (MulEquiv.subgroupMap (MulAut.conj y) J))).toEquiv).symm
  unfold SolvThreeDirectCond
  rw [← hD, key, Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
    ← hNdef, Subgroup.index_eq_card, Nat.card_eq_fintype_card (α := X₀ ⧸ N)]

end Conjugates

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

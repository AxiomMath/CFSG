module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uC
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2205
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Layer
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uB

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement


section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_fourth3 (hΩ : Q3T7M.HM Ω) {z : G} {J₁ J₂ J₃ : Subgroup G} {v₁ v₂ v₃ : G}
    {R₁ R₂ R₃ B : Subgroup G} (hT : T7J.Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B)
    {M' : Subgroup G} (hM'Ω : M' ∈ Ω) (hM'u : IsUniqueInvolution M' z) (hM'₁ : M' ≠ J₁)
    (hM'₂ : M' ≠ J₂) (hM'₃ : M' ≠ J₃) :
    ∃ S : Subgroup G, IsSylow2In S M' ∧ Commutes R₁ S ∧ Commutes R₂ S ∧ Commutes R₃ S := by
  have p₁ : IsPGroup 2 ↥R₁ := hT.syl₁.2.1
  have p₂ : IsPGroup 2 ↥R₂ := hT.syl₂.2.1
  have p₃ : IsPGroup 2 ↥R₃ := hT.syl₃.2.1
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes hT.c₁₂.symm)
  have hP : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' p₃ (sup_le (T7A.le_normalizer_of_commutes hT.c₁₃.symm)
      (T7A.le_normalizer_of_commutes hT.c₂₃.symm))
  have n₁ : J₁ ≤ Subgroup.normalizer (M' : Set G) :=
    hΩ.le_normalizer_of_twin hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u
  have n₂ : J₂ ≤ Subgroup.normalizer (M' : Set G) :=
    hΩ.le_normalizer_of_twin hT.mem₂ hM'Ω (fun h => hM'₂ h.symm) hT.uniq₂ hM'u
  have n₃ : J₃ ≤ Subgroup.normalizer (M' : Set G) :=
    hΩ.le_normalizer_of_twin hT.mem₃ hM'Ω (fun h => hM'₃ h.symm) hT.uniq₃ hM'u
  have hPM' : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (M' : Set G) :=
    sup_le (sup_le (hT.syl₁.1.trans n₁) (hT.syl₂.1.trans n₂)) (hT.syl₃.1.trans n₃)
  obtain ⟨S, hS, hSfix⟩ := exists_sylow_normalized hP hPM'
  have hPS : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hSfix x hx)
  have hQ : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ S) := hP.to_sup_of_normal_right' hS.2.1 hPS
  have hR₁Q : R₁ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ S := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hR₂Q : R₂ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ S := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ S := le_sup_right.trans le_sup_left
  have hSQ : S ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ S := le_sup_right
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u
      hT.syl₁.1 hS.1 (hQ.to_le (sup_le hR₁Q hSQ))
  · exact hΩ.commutes_of_twin_of_isPGroup hT.mem₂ hM'Ω (fun h => hM'₂ h.symm) hT.uniq₂ hM'u
      hT.syl₂.1 hS.1 (hQ.to_le (sup_le hR₂Q hSQ))
  · exact hΩ.commutes_of_twin_of_isPGroup hT.mem₃ hM'Ω (fun h => hM'₃ h.symm) hT.uniq₃ hM'u
      hT.syl₃.1 hS.1 (hQ.to_le (sup_le hR₃Q hSQ))

theorem exists_triple3 {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, T7J.Triple Ω z K K' K₃ u₁ u₂ u₃ R R' R₃
      (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, c12, c13, c23⟩ :=
    Q3T8.Asc77.T7J.exists_sylow_triple h
  exact ⟨R, R', R₃,
    { mem₁ := h.stand.mem
      mem₂ := h.hK'.1
      mem₃ := h.hK₃.1
      uniq₁ := h.hz
      uniq₂ := h.hzK'
      uniq₃ := h.hzK₃
      ne₁₂ := h.hne.symm
      ne₁₃ := h.hK₃K.symm
      ne₂₃ := h.hK₃K'.symm
      syl₁ := hR
      syl₂ := hR'
      syl₃ := hR₃
      v₁R := hu₁R
      v₂R := hu₂R'
      v₃R := hu₃R₃
      cm := ⟨h.sq₁, h.sq₂, h.sq₃, h.hz.sq, h.comm₁₂, Q3T8.Asc77.T7J.comm₁₃ h, h.comm₂₃⟩
      c₁₂ := c12
      c₁₃ := c13
      c₂₃ := c23
      hB := h.isElemAbelian_B
      hzB := T7B.mem_closure_snd
      hz1 := h.hz.ne_one
      h₁₂ := T7B.mem_closure_fst
      h₂₃ := T7B.mem_closure_thd
      hgen := le_rfl }⟩

end Frame

section Hyp51

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

omit [IsSimpleGroup G] in
theorem padicValNat_inf_eq_one3 {A B : Subgroup G} {z : G} (hzA : z ∈ A) (hzB : z ∈ B)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (h : padicValNat 2 (Nat.card ↥(A ⊓ B)) ≤ 1) :
    padicValNat 2 (Nat.card ↥(A ⊓ B)) = 1 := by
  have hmem : z ∈ A ⊓ B := ⟨hzA, hzB⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : 2 ∣ Nat.card ↥(A ⊓ B) := by
    have := Subgroup.orderOf_dvd_natCard (A ⊓ B) hmem
    rwa [hzo] at this
  have hpos : Nat.card ↥(A ⊓ B) ≠ 0 := Nat.card_pos.ne'
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(A ⊓ B)) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
  exact le_antisymm h h1

theorem hyp51At_of_triple3 (hrows : TwinSqAlphaAll3) {K₀ : Subgroup G}
    (hst : Q3T8.Asc77.AscStand Ω K₀) {z : G} {J₁ J₂ J₃ : Subgroup G} {v₁ v₂ v₃ : G}
    {R₁ R₂ R₃ B : Subgroup G} (hT : T7J.Triple Ω z J₁ J₂ J₃ v₁ v₂ v₃ R₁ R₂ R₃ B) {c : G}
    (hc : c = v₁ * v₂ ∨ c = v₁ * v₂ * z) (hc1 : c ≠ 1) (hcz : c ≠ z) {M' : Subgroup G}
    (hM'Ω : M' ∈ Ω) (hM'u : IsUniqueInvolution M' z) (hM'₁ : M' ≠ J₁) (hM'₂ : M' ≠ J₂)
    (hM'₃ : M' ≠ J₃) : Hyp51At B c := by
  classical
  have cm := hT.cm
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hΩ3 : InClass3 Ω := inClass3_of_stand3 hst.toStand3
  have hBelow : CIT3Below (Nat.card G) := cit3Below_of_stand3 hst.toStand3
  have hcB : c ∈ B := by
    rcases hc with rfl | rfl
    · exact hT.h₁₂
    · exact B.mul_mem hT.h₁₂ hT.hzB
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hT.hB hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hcomm_c : ∀ x : G, v₁ * x = x * v₁ → v₂ * x = x * v₂ → z * x = x * z → c * x = x * c := by
    intro x h1 h2 hz
    rcases hc with rfl | rfl
    · exact T7J.commute_pair h1 h2
    · exact T7J.commute_pair (T7J.commute_pair h1 h2) hz
  have hzcomm : ∀ x : G, v₁ * x = x * v₁ → z * x = x * z := by
    intro x h1
    calc z * x = v₁ * (v₁ * x) := by rw [← cm.s₁, mul_assoc]
      _ = v₁ * (x * v₁) := by rw [h1]
      _ = (v₁ * x) * v₁ := by rw [mul_assoc]
      _ = (x * v₁) * v₁ := by rw [h1]
      _ = x * z := by rw [mul_assoc, cm.s₁]
  have hR₃c : R₃ ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : v₁ * x = x * v₁ := hT.c₁₃ v₁ hT.v₁R x hx
    have h2 : v₂ * x = x * v₂ := hT.c₂₃ v₂ hT.v₂R x hx
    exact (hcomm_c x h1 h2 (hzcomm x h1)).symm
  have hJ₃t : J₃ ∈ tqMembers3 Ω c :=
    ⟨hT.mem₃, (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hT.mem₃).mpr
      ⟨R₃, hT.syl₃, hR₃c⟩⟩
  have hMz : IsClassicalMember3 J₃ z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hT.mem₃ hT.uniq₃).toQ3 (by norm_num)
  have hnab : ∃ x y : G, x * y ≠ y * x := Q3T8.Asc77.T7C.exists_not_commute_of_stand hst
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := Balance.not_subset_center_of_ne_one hnab hc1
  have hv₁M' : v₁ ∈ trivialOnQuot M' :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u
      (hT.syl₁.1 hT.v₁R)
  have hv₂M' : v₂ ∈ trivialOnQuot M' :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hT.mem₂ hM'Ω (fun h => hM'₂ h.symm) hT.uniq₂ hM'u
      (hT.syl₂.1 hT.v₂R)
  have hzM' : z ∈ trivialOnQuot M' :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hT.mem₁ hM'Ω (fun h => hM'₁ h.symm) hT.uniq₁ hM'u
      hT.uniq₁.mem
  have hcM' : c ∈ trivialOnQuot M' := by
    rcases hc with rfl | rfl
    · exact Subgroup.mul_mem _ hv₁M' hv₂M'
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hv₁M' hv₂M') hzM'
  have hM't : M' ∈ tqMembers3 Ω c := ⟨hM'Ω, hcM'⟩
  have hM'z : IsClassicalMember3 M' z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hM'Ω hM'u).toQ3 (by norm_num)
  have h12 : ∀ S : Subgroup G, c ∈ S → z ∈ S → v₁ * v₂ ∈ S := by
    intro S hcS hzS'
    rcases hc with rfl | rfl
    · exact hcS
    · have : v₁ * v₂ = (v₁ * v₂ * z) * z := by rw [mul_assoc, cm.z2, mul_one]
      rw [this]
      exact S.mul_mem hcS hzS'
  have hgen' : ∀ S : Subgroup G, v₁ * v₂ ∈ S → z ∈ S → v₂ * v₃ ∈ S → B ≤ S := by
    intro S h1 h2 h3
    refine hT.hgen.trans ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hc_v₁ : c * v₁ = v₁ * c := hcomm_c v₁ rfl cm.c₁₂.symm cm.zc₁
  have hBle₁ : B ≤ Subgroup.closure ({c, z, v₁ * v₃} : Set G) := by
    set S := Subgroup.closure ({c, z, v₁ * v₃} : Set G) with hS
    have hzS' : z ∈ S := Subgroup.subset_closure (by simp)
    have hcS : c ∈ S := Subgroup.subset_closure (by simp)
    have havS : v₁ * v₃ ∈ S := Subgroup.subset_closure (by simp)
    have h12S := h12 S hcS hzS'
    refine hgen' S h12S hzS' ?_
    have h : v₂ * v₃ = (v₁ * v₂) * (z * (v₁ * v₃)) := by
      calc v₂ * v₃ = ((v₁ * v₂) * (v₁ * v₂)) * (v₂ * v₃) := by rw [cm.sq_pair, one_mul]
        _ = (v₁ * v₂) * ((v₁ * v₂) * (v₂ * v₃)) := by rw [mul_assoc]
        _ = (v₁ * v₂) * (z * (v₁ * v₃)) := by rw [cm.rel]
    rw [h]
    exact S.mul_mem h12S (S.mul_mem hzS' havS)
  have hv₁J₃ : v₁ ∈ trivialOnQuot J₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hT.mem₁ hT.mem₃ hT.ne₁₃ hT.uniq₁ hT.uniq₃
      (hT.syl₁.1 hT.v₁R)
  have haC : v₁ ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc_v₁.symm
  have hΦ : SecData3 c (exactFamily3 Ω c) := secData3_exactFamily hΩ3 hc2 ⟨J₃, hJ₃t⟩
  have hMΦ : exactCore3 c J₃ ∈ exactFamily3 Ω c := exactCore3_mem_exactFamily3 hJ₃t
  have hM'Φ : exactCore3 c M' ∈ exactFamily3 Ω c := exactCore3_mem_exactFamily3 hM't
  have hzU : IsUniqueInvolution (exactCore3 c J₃) z :=
    Q3T6D.isUniqueInvolution_of_le' hT.uniq₃ (mem_exactCore3 hMz hc2 hJ₃t.2)
      (exactCore3_le_left c J₃)
  have hzU' : IsUniqueInvolution (exactCore3 c M') z :=
    Q3T6D.isUniqueInvolution_of_le' hM'u (mem_exactCore3 hM'z hc2 hM't.2)
      (exactCore3_le_left c M')
  have hvm : v₃ ∈ exactCore3 c J₃ :=
    Subgroup.mem_inf.mpr ⟨hT.syl₃.1 hT.v₃R, hR₃c hT.v₃R⟩
  obtain ⟨S, hS, hRS₁, hRS₂, hRS₃⟩ := exists_sylow_fourth3 hΩ hT hM'Ω hM'u hM'₁ hM'₂ hM'₃
  have hSC : S ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : v₁ * x = x * v₁ := hRS₁ v₁ hT.v₁R x hx
    have h2 : v₂ * x = x * v₂ := hRS₂ v₂ hT.v₂R x hx
    exact (hcomm_c x h1 h2 (hzcomm x h1)).symm
  have hSM' : S ≤ exactCore3 c M' := le_inf hS.1 hSC
  have hR₃M : R₃ ≤ exactCore3 c J₃ := le_inf hT.syl₃.1 hR₃c
  have h8 : 8 ≤ Nat.card R₃ := (Q3T7P25.natCard_isSylow2In_member hΩ hT.mem₃ hT.syl₃).ge
  have hS8 : Nat.card S = 8 := Q3T7P25.natCard_isSylow2In_member hΩ hM'Ω hS
  have hω4 := omega4_exactCore3 hst.toStand3 hc2 hJ₃t hM't hM'₃.symm
  have hv1 : padicValNat 2 (Nat.card ↥(exactCore3 c J₃ ⊓ exactCore3 c M')) = 1 :=
    padicValNat_inf_eq_one3 (mem_exactCore3 hMz hc2 hJ₃t.2) (mem_exactCore3 hM'z hc2 hM't.2)
      hT.uniq₃.sq hT.hz1 hω4.1
  have hv₁J₃' : v₁ ∈ trivialOnQuot (exactCore3 c J₃) :=
    mem_trivialOnQuot_exactCore3 hMz hc2 hJ₃t.2 hv₁J₃ haC
  have hv₁M'' : v₁ ∈ trivialOnQuot (exactCore3 c M') :=
    mem_trivialOnQuot_exactCore3 hM'z hc2 hM't.2 hv₁M' haC
  have hα : ∀ (ι : Type) (D : LieSystemData3 ι (↥(centralizingLayer (exactFamily3 Ω c) {c}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (exactFamily3 Ω c) {c}))
        (oddQuotientFamily (restrictFamily (centralizingMembers (exactFamily3 Ω c) {c})
          (centralizingLayer (exactFamily3 Ω c) {c})))) (j : ι),
      modOdd c (exactCore3 c J₃) ≤ secComp hΦ D j → MovedByAll B c (secComp hΦ D j) →
        CFSG.IsComponent (secComp hΦ D j) →
          alphaOf (inducedImage (secComp hΦ D j) (modOdd c B)) = ⊥ := by
    intro ι D j hMj hmov hLc
    have hne : modOdd c (exactCore3 c J₃) ≠ modOdd c (exactCore3 c M') := by
      intro heq
      have hSR : S ≤ R₃ := le_of_modOdd_eq_of_commutes3 hΦ D hMΦ hM'Φ heq hR₃M hSM'
        hT.syl₃.2.1 hS.2.1 hRS₃ h8
      have hSle : S ≤ exactCore3 c J₃ ⊓ exactCore3 c M' := le_inf (hSR.trans hR₃M) hSM'
      have hdvd : 2 ^ 3 ∣ Nat.card ↥(exactCore3 c J₃ ⊓ exactCore3 c M') := by
        have := Subgroup.card_dvd_of_le hSle
        rw [hS8] at this
        simpa using this
      have hpos : Nat.card ↥(exactCore3 c J₃ ⊓ exactCore3 c M') ≠ 0 := Nat.card_pos.ne'
      have h3 := (padicValNat_dvd_iff_le (p := 2) hpos).mp hdvd
      omega
    have hcomm : ∀ x ∈ modOdd c (exactCore3 c J₃), ∀ y ∈ modOdd c (exactCore3 c M'),
        x * y = y * x := by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      have hk' : (k : G) ∈ exactCore3 c J₃ := Subgroup.mem_subgroupOf.mp hk
      have hl' : (l : G) ∈ exactCore3 c M' := Subgroup.mem_subgroupOf.mp hl
      have h4 := hω4.2 hv1 (Subgroup.commutator_mem_commutator hk' hl')
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hMΦ k.2 l.2 h4.1
    have hcommM : ∀ x ∈ modOdd c (exactCore3 c J₃),
        oddQuotMk c ⟨v₁, haC⟩ * x = x * oddQuotMk c ⟨v₁, haC⟩ := by
      rintro _ ⟨k, hk, rfl⟩
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hMΦ haC k.2
        (hv₁J₃'.2 k (Subgroup.mem_subgroupOf.mp hk))
    have hcommM' : ∀ x ∈ modOdd c (exactCore3 c M'),
        oddQuotMk c ⟨v₁, haC⟩ * x = x * oddQuotMk c ⟨v₁, haC⟩ := by
      rintro _ ⟨k, hk, rfl⟩
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hM'Φ haC k.2
        (hv₁M''.2 k (Subgroup.mem_subgroupOf.mp hk))
    exact alpha_of_twinSq3 hrows hΦ D hT.hB hcB hc1 hT.hzB hT.hz1 hcz.symm hMΦ hM'Φ hzU hzU'
      hne hcomm haC cm.s₁ hcommM hcommM' hvm cm.s₃ hT.h₁₃ hBle₁ hMj hmov hLc
  exact hyp51At_of_witness_alpha3 hBelow hΦ hnc hMΦ
    (isSectionMember3_exactCore3 hMz hc2 hJ₃t.2) hT.hB hcB hc1 hT.hzB hcz.symm hα

theorem hyp22Hyp51u_of_fourthTwin3 (hrows : TwinSqAlphaAll3)
    (h4 : Q3T8.Asc77.Hyp22FourthTwin) : Q3T8.Asc77.Hyp22Hyp51u := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h c hc hc1 hcz
  obtain ⟨K₄, hK₄, hK₄K, hK₄K', hK₄K₃⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨R, R', R₃, hT⟩ := exists_triple3 h
  have hK₄u : IsUniqueInvolution K₄ z :=
    CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_of_mem_twinSet h.hz hK₄
  have cm := hT.cm
  have hcm := T7J.mem_closure_three cm.commute_xz cm.commute_xw cm.commute_wz.symm cm.sq_pair
    cm.z2 cm.rot.sq_pair hc
  rcases hcm with h1 | h2 | h3 | h4' | h5 | h6 | h7 | h8
  · exact absurd h1 hc1
  · exact hyp51At_of_triple3 hrows h.stand hT (Or.inl h2) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K' hK₄K₃
  · exact absurd h3 hcz
  · exact hyp51At_of_triple3 hrows h.stand hT.rot (Or.inl h4') hc1 hcz hK₄.1 hK₄u hK₄K' hK₄K₃
      hK₄K
  · exact hyp51At_of_triple3 hrows h.stand hT (Or.inr h5) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K' hK₄K₃
  · exact hyp51At_of_triple3 hrows h.stand hT.rot.rot (Or.inr (h6.trans cm.eq_xw)) hc1 hcz hK₄.1
      hK₄u hK₄K₃ hK₄K hK₄K'
  · exact hyp51At_of_triple3 hrows h.stand hT.rot (Or.inr (h7.trans cm.zc₂₃)) hc1 hcz hK₄.1 hK₄u
      hK₄K' hK₄K₃ hK₄K
  · exact hyp51At_of_triple3 hrows h.stand hT.rot.rot (Or.inl (h8.trans cm.eq_xyw)) hc1 hcz
      hK₄.1 hK₄u hK₄K₃ hK₄K hK₄K'

end Hyp51

end CFSG.ClassicalInvolution.Q3.Q3T7

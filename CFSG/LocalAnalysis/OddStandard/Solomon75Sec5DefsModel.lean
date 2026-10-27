module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Induces

variable {n : ℕ} {K : Type} [Group K]

theorem exists_induces_perm (hn : 5 ≤ n) (hn6 : n ≠ 6) (C : AhatData.CoverSetup n K)
    (α : MulAut K) : ∃ σ : Perm (Fin n), C.Induces α σ := by
  let e : K ⧸ center K ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq C.ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective C.π C.surj)
  have he : ∀ x : K, e (QuotientGroup.mk x) = C.π x := fun x => by
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let α' : K ⧸ center K ≃* K ⧸ center K :=
    QuotientGroup.congr (center K) (center K) α (Subgroup.map_center_eq α)
  let β : MulAut (alternatingGroup (Fin n)) := (e.symm.trans α').trans e
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 β
  refine ⟨σ, ⟨fun x => ?_⟩⟩
  have h1 : C.π (α x) = β (C.π x) := by
    have : β (C.π x) = e (α' (QuotientGroup.mk x)) := by
      rw [← he x]
      simp [β]
    rw [this, QuotientGroup.congr_mk, he]
  have h2 : C.ρ (α x) = ((β (C.π x) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    rw [C.ρ_apply, h1]
  rw [h2, ← hσ, MulAut.conjNormal_apply, C.ρ_apply]

theorem induces_unique (hn : 4 ≤ n) {C : AhatData.CoverSetup n K} {α : MulAut K}
    {σ σ' : Perm (Fin n)} (h : C.Induces α σ) (h' : C.Induces α σ') : σ = σ' := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  have hc : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin n))) = MulAut.conjNormal σ' := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := C.surj y
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← C.ρ_apply]
    exact (h.map_ρ x).symm.trans (h'.map_ρ x)
  exact hinj hc

theorem AhatData.CoverSetup.Induces.mul' {C : AhatData.CoverSetup n K} {α β : MulAut K}
    {σ τ : Perm (Fin n)} (h : C.Induces α σ) (h' : C.Induces β τ) :
    C.Induces (α * β) (σ * τ) :=
  ⟨fun x => by
    simp only [MulAut.mul_apply, h.map_ρ, h'.map_ρ]
    group⟩

theorem AhatData.CoverSetup.induces_one' (C : AhatData.CoverSetup n K) : C.Induces 1 1 :=
  ⟨fun x => by simp⟩

end Induces

section ModelAPI

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

theorem mem_oddCoreOf_iff {x : X} :
    x ∈ oddCoreOf A ↔ ∃ h : x ∈ A, (⟨x, h⟩ : ↥A) ∈ pPrimeCore 2 ↥A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨x, h⟩, hh, rfl⟩

theorem AhatModel.autOf_mk (M : AhatModel X n A) {c : X} (hc : c ∈ normalizer (A : Set X))
    (a : ↥A) :
    M.autOf c hc (M.e (QuotientGroup.mk a)) = M.e (QuotientGroup.mk (conjAut hc a)) := by
  simp only [AhatModel.autOf, quotConj, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact congrArg M.e (QuotientGroup.congr_mk _ _ _ _ a)

theorem AhatModel.surj_mk (M : AhatModel X n A) (k : M.K) :
    ∃ a : ↥A, M.e (QuotientGroup.mk a) = k := by
  obtain ⟨q, rfl⟩ := M.e.surjective k
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, rfl⟩

theorem AhatModel.autOf_mul (M : AhatModel X n A) {c d : X} (hc : c ∈ normalizer (A : Set X))
    (hd : d ∈ normalizer (A : Set X)) :
    M.autOf (c * d) (Subgroup.mul_mem _ hc hd) = M.autOf c hc * M.autOf d hd := by
  refine MulEquiv.ext fun k => ?_
  obtain ⟨a, rfl⟩ := M.surj_mk k
  have h : conjAut (Subgroup.mul_mem _ hc hd) a = conjAut hc (conjAut hd a) :=
    Subtype.ext (by simp only [coe_conjAut, mul_inv_rev]; group)
  rw [MulAut.mul_apply, M.autOf_mk, M.autOf_mk, M.autOf_mk, h]

theorem AhatModel.autOf_one (M : AhatModel X n A) :
    M.autOf 1 (Subgroup.one_mem _) = 1 := by
  refine MulEquiv.ext fun k => ?_
  obtain ⟨a, rfl⟩ := M.surj_mk k
  have h : conjAut (Subgroup.one_mem (normalizer (A : Set X))) a = a :=
    Subtype.ext (by simp [coe_conjAut])
  rw [M.autOf_mk, h]
  rfl

theorem AhatModel.induces_perm (hn : 8 ≤ n) (M : AhatModel X n A) (c : X)
    (hc : c ∈ normalizer (A : Set X)) : M.C.Induces (M.autOf c hc) (M.perm c hc) := by
  have h := exists_induces_perm (by omega) (by omega) M.C (M.autOf c hc)
  simp only [AhatModel.perm, h, ↓reduceDIte]
  exact h.choose_spec

theorem AhatModel.perm_eq_of_induces (hn : 8 ≤ n) (M : AhatModel X n A) {c : X}
    (hc : c ∈ normalizer (A : Set X)) {σ : Perm (Fin n)} (h : M.C.Induces (M.autOf c hc) σ) :
    M.perm c hc = σ :=
  induces_unique (by omega) (M.induces_perm hn c hc) h

theorem AhatModel.perm_mul (hn : 8 ≤ n) (M : AhatModel X n A) {c d : X}
    (hc : c ∈ normalizer (A : Set X)) (hd : d ∈ normalizer (A : Set X)) :
    M.perm (c * d) (Subgroup.mul_mem _ hc hd) = M.perm c hc * M.perm d hd := by
  apply M.perm_eq_of_induces hn
  rw [M.autOf_mul hc hd]
  exact (M.induces_perm hn c hc).mul' (M.induces_perm hn d hd)

theorem AhatModel.perm_one (hn : 8 ≤ n) (M : AhatModel X n A) :
    M.perm 1 (Subgroup.one_mem _) = 1 := by
  apply M.perm_eq_of_induces hn
  rw [M.autOf_one]
  exact M.C.induces_one'

@[expose] noncomputable def AhatModel.permHom (hn : 8 ≤ n) (M : AhatModel X n A) :
    ↥(normalizer (A : Set X)) →* Perm (Fin n) where
  toFun c := M.perm c c.2
  map_one' := M.perm_one hn
  map_mul' c d := M.perm_mul hn c.2 d.2

theorem AhatModel.autOf_of_mem (M : AhatModel X n A) {a : X} (ha : a ∈ A) :
    M.autOf a (Subgroup.le_normalizer ha) =
      MulAut.conj (M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A))) := by
  refine MulEquiv.ext fun k => ?_
  obtain ⟨b, rfl⟩ := M.surj_mk k
  rw [M.autOf_mk, MulAut.conj_apply]
  have h : conjAut (Subgroup.le_normalizer ha) b = (⟨a, ha⟩ : ↥A) * b * (⟨a, ha⟩ : ↥A)⁻¹ :=
    Subtype.ext (by simp [coe_conjAut])
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv]

theorem AhatModel.perm_of_mem (hn : 8 ≤ n) (M : AhatModel X n A) {a : X} (ha : a ∈ A) :
    M.perm a (Subgroup.le_normalizer ha) = M.C.ρ (M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A))) := by
  apply M.perm_eq_of_induces hn
  rw [M.autOf_of_mem ha]
  exact M.C.induces_conj _

theorem centModOdd_iff {c : X} (hc : c ∈ normalizer (A : Set X)) :
    CentModOdd A c ↔ ∀ b : ↥A,
      (QuotientGroup.mk (conjAut hc b) : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk b := by
  have key : ∀ b : ↥A, ⁅((b⁻¹ : ↥A) : X), c⁆ ∈ oddCoreOf A ↔
      (QuotientGroup.mk (conjAut hc b) : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk b := by
    intro b
    have h1 : ⁅((b⁻¹ : ↥A) : X), c⁆ = ((b⁻¹ * conjAut hc b : ↥A) : X) := by
      simp only [commutatorElement_def, coe_conjAut, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1, eq_comm, QuotientGroup.eq]
    constructor
    · intro h
      obtain ⟨hmem, hP⟩ := mem_oddCoreOf_iff.1 h
      exact hP
    · intro h
      exact mem_oddCoreOf_iff.2 ⟨(b⁻¹ * conjAut hc b).2, h⟩
  constructor
  · intro h b
    exact (key b).1 (h _ (b⁻¹).2)
  · intro h a ha
    have := (key (⟨a, ha⟩ : ↥A)⁻¹).2 (h _)
    simpa using this

theorem AhatModel.perm_eq_one_iff (hn : 8 ≤ n) (M : AhatModel X n A) {c : X}
    (hc : c ∈ normalizer (A : Set X)) : M.perm c hc = 1 ↔ CentModOdd A c := by
  rw [centModOdd_iff hc]
  constructor
  · intro h b
    have hind : M.C.Induces (M.autOf c hc) 1 := by
      rw [← h]
      exact M.induces_perm hn c hc
    have hcomm := hind.commutator_le_fixSub ⊤ (fun x _ => by simp)
    have htop : (⁅(⊤ : Subgroup M.K), ⊤⁆ : Subgroup M.K) = ⊤ := by
      have hp := M.C.hX.1.1
      exact hp.commutator_eq_top
    have hfix : ∀ k : M.K, M.autOf c hc k = k := fun k => by
      have hk : k ∈ (⁅(⊤ : Subgroup M.K), ⊤⁆ : Subgroup M.K) := by
        rw [htop]; exact Subgroup.mem_top k
      exact hcomm hk
    have := hfix (M.e (QuotientGroup.mk b))
    rw [M.autOf_mk] at this
    exact M.e.injective this
  · intro h
    apply M.perm_eq_of_induces hn
    have : M.autOf c hc = 1 := by
      refine MulEquiv.ext fun k => ?_
      obtain ⟨b, rfl⟩ := M.surj_mk k
      rw [M.autOf_mk, h b]
      rfl
    rw [this]
    exact M.C.induces_one'

end ModelAPI

section Canonical

variable {X : Type} [Group X]

@[expose] noncomputable def AhatModel.ofCover {n : ℕ} {A : Subgroup X}
    (hA : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n) : AhatModel X n A :=
  ⟨↥A ⧸ pPrimeCore 2 ↥A, MulEquiv.refl _, AhatData.CoverSetup.ofCover hA⟩

end Canonical

section Counts

variable {n : ℕ}

theorem fixCount_add_support (σ : Perm (Fin n)) : fixCount σ + σ.support.card = n := by
  classical
  unfold fixCount
  have h : (Finset.univ.filter fun i => σ i = i) = Finset.univ \ σ.support := by
    ext i
    simp [Equiv.Perm.mem_support]
  rw [h, Finset.card_univ_sdiff, Fintype.card_fin]
  have : σ.support.card ≤ n := by
    simpa using Finset.card_le_univ σ.support
  omega

theorem transCount_conj (g σ : Perm (Fin n)) : transCount (g * σ * g⁻¹) = transCount σ := by
  unfold transCount
  rw [Equiv.Perm.card_support_conj]

theorem fixCount_conj (g σ : Perm (Fin n)) : fixCount (g * σ * g⁻¹) = fixCount σ := by
  have h1 := fixCount_add_support (g * σ * g⁻¹)
  have h2 := fixCount_add_support σ
  rw [Equiv.Perm.card_support_conj] at h1
  omega

end Counts

end CFSG.OddStandard.Solomon75

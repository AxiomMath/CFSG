module

public import CFSG.Holt.H78.Sec4Prop43R2
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4Prop43W

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

theorem exists_mem_fixSet_of_kerC (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) {V : Subgroup G} (hVQ : V ≤ C.calP ⊓ C.kerC C.i₁) (hV1 : V ≠ ⊥)
    {c₁ c₂ : C.D.Ψc C.i₁} (hc₁ : c₁ ≠ C.D.coord C.γ C.i₁) (hc₂ : c₂ ≠ C.D.coord C.γ C.i₁)
    (hc₁₂ : c₁ ≠ c₂)
    (hfix : ∀ v : C.kerC C.i₁, (v : G) ∈ V →
      C.kerCHom C.i₁ v c₁ = c₁ ∧ C.kerCHom C.i₁ v c₂ = c₂)
    {P₀ : Subgroup G} (hP₀ : P₀ ≤ C.calP) (hP₀V : P₀ ≤ Subgroup.normalizer (V : Set G)) :
    ∃ ω ∈ fixSet Ω P₀, ω ∉ ({α, β, (C.γ : Ω)} : Set Ω) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := C.sylow.2.1.to_le (hVQ.trans (inf_le_left.trans inf_le_left))
  have hVα : ∀ v ∈ V, v • α = α := fun v hv =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.kerC_le_inf _ (hVQ hv).2)).1
  have hVβ : ∀ v ∈ V, v • β = β := fun v hv =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.kerC_le_inf _ (hVQ hv).2)).2
  set a : fixSet Ω V := ⟨α, fun v hv => hVα v hv⟩
  set b : fixSet Ω V := ⟨β, fun v hv => hVβ v hv⟩
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3V := hS.three_le_card_fixSet_of_ne hV2 hab
  set Λ₁ : Set (C.D.Ψc C.i₁) :=
    {x | ∀ v : C.kerC C.i₁, (v : G) ∈ V → C.kerCHom C.i₁ v x = x} with hΛ₁
  set Λc : ∀ i, Set (C.D.Ψc i) := Function.update (fun _ => Set.univ) C.i₁ Λ₁ with hΛc
  have hΛc₁ : Λc C.i₁ = Λ₁ := Function.update_self _ _ _
  have hΛcj : ∀ j, j ≠ C.i₁ → Λc j = Set.univ := fun j hj => Function.update_of_ne hj _ _
  have hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, C.D.coord δ i ∈ Λc i := by
    intro δ
    constructor
    · intro h i
      by_cases hi : i = C.i₁
      · subst hi
        rw [hΛc₁]
        intro v hv
        exact (C.coord_smul_eq_kerCHom v (h v hv).symm).symm
      · rw [hΛcj i hi]
        exact Set.mem_univ _
    · intro h v hv
      refine C.smul_eq_of_kerCHom_fix ⟨v, (hVQ hv).2⟩
        (Λc := Function.update (fun _ => Set.univ) C.i₁ {C.D.coord δ C.i₁}) (fun x hx => ?_) δ
        fun j => ?_
      · rw [Function.update_self, Set.mem_singleton_iff] at hx
        rw [hx]
        have h1 := h C.i₁
        rw [hΛc₁] at h1
        exact h1 ⟨v, (hVQ hv).2⟩ hv
      · by_cases hj : j = C.i₁
        · subst hj
          rw [Function.update_self]
          exact rfl
        · rw [Function.update_of_ne hj]
          exact Set.mem_univ _
  have hγΛ : C.D.coord C.γ C.i₁ ∈ Λ₁ := fun v _ => C.kerCHom_apply_γ v
  have hc₁Λ : c₁ ∈ Λ₁ := fun v hv => (hfix v hv).1
  have hc₂Λ : c₂ ∈ Λ₁ := fun v hv => (hfix v hv).2
  have hnt : ∀ i, (Λc i).Nontrivial := by
    intro i
    by_cases hi : i = C.i₁
    · subst hi
      rw [hΛc₁]
      exact ⟨_, hγΛ, _, hc₁Λ, hc₁.symm⟩
    · rw [hΛcj i hi]
      have := C.nontrivial_Ψc i
      exact Set.nontrivial_univ
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ C.D C.oddCore_eq_bot C.alt hV2
    (a := a) (b := b) rfl rfl Λc hbox (p := fun _ => True) (fun i _ => hnt i)
    (fun _ h => absurd trivial h)
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hV2 hV1 h3V
  have hK := hS.star_centralizerImage hV2 h3V
  have hcardΛc : ∀ j, Fintype.card ↥(Λc j) = (Λc j).ncard := fun j => by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h3 : ∀ j : {i // True}, 3 ≤ Fintype.card ↥(Λc j.1) := by
    rintro ⟨j, -⟩
    rw [hcardΛc]
    by_cases hj : j = C.i₁
    · subst hj
      rw [hΛc₁]
      have h1 : ({C.D.coord C.γ C.i₁, c₁, c₂} : Set (C.D.Ψc C.i₁)).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨_, _, _, hc₁.symm, hc₂.symm, hc₁₂, rfl⟩
      rw [← h1]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      rintro x (rfl | rfl | rfl)
      exacts [hγΛ, hc₁Λ, hc₂Λ]
    · rw [hΛcj j hj, C.ncard_univ_Ψc]
      have := C.D.five_le_card j
      omega
  have hbox3 := CCLBox3.of_equiv (G := centralizerImage Ω V) h3 hcoord hreal
  set ε : (∀ j : {i // True}, ↥(Λc j.1)) → fixSet Ω V := fun x => (e.symm x : fixSet Ω V)
  set δ₁ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c₁) with hδ₁
  have hcδ₁ : C.D.coord δ₁ = Function.update (C.D.coord C.γ) C.i₁ c₁ := C.coord_coordEquiv_symm _
  have hVγ : ∀ v ∈ V, v • (C.γ : Ω) = C.γ := fun v hv => C.smul_eq_of_mem_kerC (hVQ hv).2 rfl
  have hVδ₁ : ∀ v ∈ V, v • (δ₁ : Ω) = δ₁ := fun v hv =>
    C.smul_linePoint_eq ⟨v, (hVQ hv).2⟩ (hfix _ hv).1
  set γV : fixSet Ω V := ⟨C.γ, fun v hv => hVγ v hv⟩
  set γ'V : fixSet Ω V := ⟨δ₁, fun v hv => hVδ₁ v hv⟩
  have hmemK : ∀ ω : fixSet Ω V, (ω : Ω) ∈ holtDelta G Ω α β →
      ω ∈ holtDelta (centralizerImage Ω V) (fixSet Ω V) a b := fun ω hω =>
    (hS.mem_holtDelta_centralizerImage_iff hV2 h3V hab).mpr hω
  have hεe : ∀ (ω : fixSet Ω V) (hω : ω ∈ holtDelta (centralizerImage Ω V) (fixSet Ω V) a b),
      ε (e ⟨ω, hω⟩) = ω := fun ω hω => by
    change ((e.symm (e ⟨ω, hω⟩) : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) :
      fixSet Ω V) = ω
    rw [e.symm_apply_apply]
  set i₁' : {i // True} := ⟨C.i₁, trivial⟩
  set xγ := e ⟨γV, hmemK γV C.γ.2⟩
  have hline : ∀ (ω : fixSet Ω V) (hω : (ω : Ω) ∈ C.line),
      e ⟨ω, hmemK ω (C.line_subset_holtDelta hω)⟩ =
        Function.update xγ i₁' (e ⟨ω, hmemK ω (C.line_subset_holtDelta hω)⟩ i₁') := by
    intro ω hω
    funext j
    by_cases hj : j = i₁'
    · subst hj
      rw [Function.update_self]
    · rw [Function.update_of_ne hj]
      apply Subtype.ext
      rw [he _ ⟨ω, C.line_subset_holtDelta hω⟩ rfl j, he _ C.γ rfl j]
      exact (C.mem_line_iff ⟨ω, C.line_subset_holtDelta hω⟩).mp hω j
        fun h => hj (Subtype.ext h)
  have hsep := C.notMem_orbit_jOddCore_linePoint hS hαβ hT hP hr hVQ hc₁ hc₂ hc₁₂ hfix γV γ'V
    rfl rfl
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, DK.coord γ'V k₁ ≠ DK.coord γV k₁ := by
    by_contra h
    push Not at h
    exact hsep ((DK.coord_eq_iff γV γ'V).mp (funext fun k => (h k).symm))
  have hγ'L : (γ'V : Ω) ∈ C.line := C.linePoint_mem c₁
  have hγL : (γV : Ω) ∈ C.line := C.γ_mem_line
  have hT₁ : ∀ k, ∀ ω : fixSet Ω V, (ω : Ω) ∈ C.line → DK.coord ω k ≠ DK.coord γV k →
      i₁' ∈ DK.boxSupport ε k := by
    intro k ω hω hne
    refine ⟨xγ, e ⟨ω, hmemK ω (C.line_subset_holtDelta hω)⟩ i₁', ?_⟩
    rw [← hline ω hω]
    beta_reduce
    rw [hεe, hεe]
    exact hne
  have hi₁T := hT₁ k₁ γ'V hγ'L hk₁
  obtain ⟨j₀, hj₀⟩ := hr
  set j₀' : {i // True} := ⟨j₀, trivial⟩
  have h5 : 5 ≤ Fintype.card ↥(Λc j₀'.1) := by
    rw [hcardΛc, hΛcj j₀ hj₀, C.ncard_univ_Ψc]
    exact C.D.five_le_card j₀
  obtain ⟨k₂, hk₂⟩ := DK.exists_mem_boxSupport_of_five_le hK hbox3 h5
  have hk₂' : i₁' ∉ DK.boxSupport ε k₂ := fun h =>
    hj₀ (congrArg Subtype.val (DK.eq_of_mem_boxSupport_of_five_le hbox3 h5 hk₂ h)).symm
  set S₁ : Set DK.ι := {k | ∃ ω : fixSet Ω V, (ω : Ω) ∈ C.line ∧ DK.coord ω k ≠ DK.coord γV k}
    with hS₁
  have hk₁S : k₁ ∈ S₁ := ⟨γ'V, hγ'L, hk₁⟩
  have hk₂S : k₂ ∉ S₁ := by
    rintro ⟨ω, hω, hne⟩
    apply hne
    have h1 := CCL.apply_update_eq_of_notMem_coordSupport hk₂' xγ
      (e ⟨ω, hmemK ω (C.line_subset_holtDelta hω)⟩ i₁')
    rw [← hline ω hω, hεe, hεe] at h1
    exact h1
  have hS₁ab : ∀ k ∈ S₁, DK.coord a k ≠ DK.coord b k := fun k ⟨ω, hω, hne⟩ =>
    DK.coord_ne_of_mem_boxSupport hbox3 (hT₁ k ω hω hne)
  have hab₂ := DK.coord_ne_of_mem_boxSupport hbox3 hk₂
  have hγb₁ : DK.coord γV k₁ ≠ DK.coord b k₁ := by
    have h1 := DK.coord_box_ne_right hbox3 (hS₁ab k₁ hk₁S) xγ
    rwa [hεe] at h1
  obtain ⟨x', hx'⟩ := DK.coord_surjective fun k => if k ∈ S₁ then DK.coord b k else DK.coord a k
  have hx'S : ∀ k ∈ S₁, DK.coord x' k = DK.coord b k := fun k hk => by
    rw [hx']
    simp [hk]
  have hx'n : ∀ k ∉ S₁, DK.coord x' k = DK.coord a k := fun k hk => by
    rw [hx']
    simp [hk]
  have hP₀x' : ∀ g (hg : g ∈ P₀), DK.coord ((⟨g, hP₀V hg⟩ : Subgroup.normalizer (V : Set G)) • x') =
      DK.coord x' ∧ ∀ y z : fixSet Ω V, DK.coord y = DK.coord z ↔
        DK.coord ((⟨g, hP₀V hg⟩ : Subgroup.normalizer (V : Set G)) • y) =
          DK.coord ((⟨g, hP₀V hg⟩ : Subgroup.normalizer (V : Set G)) • z) := by
    intro g hg
    set n : Subgroup.normalizer (V : Set G) := ⟨g, hP₀V hg⟩
    obtain ⟨σ, hσ⟩ := DK.exists_equiv_coord_eq_iff_of_mem_normalizer
      (toPermHom_mem_normalizer_centralizerImage (Ω := Ω) n)
    have hσ' : ∀ i y z, DK.coord y i = DK.coord z i ↔ DK.coord (n • y) (σ i) =
        DK.coord (n • z) (σ i) := hσ
    have hgG : g ∈ C.calG := C.calP_le_calG (hP₀ hg)
    have hna : n • a = a := Subtype.ext (mem_stabilizer_iff.mp (C.calG_le_inf hgG).1)
    have hnb : n • b = b := Subtype.ext (mem_stabilizer_iff.mp (C.calG_le_inf hgG).2)
    have hnγ : n • γV = γV := Subtype.ext (C.calG_le_stabilizer_γ hgG)
    have hσS : ∀ k ∈ S₁, σ k ∈ S₁ := by
      rintro k ⟨ω, hω, hne⟩
      refine ⟨n • ω, C.smul_mem_line hgG hω, fun h => hne ?_⟩
      rw [← hnγ] at h
      exact (hσ' k ω γV).mpr h
    have hσS' : ∀ k, σ k ∈ S₁ → k ∈ S₁ := by
      intro k hk
      by_contra hkS
      have himg : σ '' S₁ = S₁ := Set.eq_of_subset_of_ncard_le
        (by rintro _ ⟨k', hk', rfl⟩; exact hσS k' hk')
        (by rw [Set.ncard_image_of_injective _ σ.injective]) (Set.toFinite _)
      rw [← himg] at hk
      obtain ⟨k', hk', hkk'⟩ := hk
      exact hkS (σ.injective hkk' ▸ hk')
    refine ⟨funext fun k' => ?_, fun y z => ?_⟩
    · obtain ⟨k, rfl⟩ := σ.surjective k'
      by_cases hk : k ∈ S₁
      · rw [hx'S _ (hσS k hk), ← hnb]
        exact (hσ' k x' b).mp (hx'S k hk)
      · rw [hx'n _ (fun h => hk (hσS' k h)), ← hna]
        exact (hσ' k x' a).mp (hx'n k hk)
    · rw [funext_iff, funext_iff]
      constructor
      · intro h i'
        obtain ⟨i, rfl⟩ := σ.surjective i'
        exact (hσ' i y z).mp (h i)
      · intro h i
        exact (hσ' i y z).mpr (h (σ i))
  set B : Set Ω := {ω | ∃ h : ω ∈ fixSet Ω V, DK.coord ⟨ω, h⟩ = DK.coord x'} with hB
  have hPB : P₀ ≤ stabilizer G B := by
    intro g hg
    rw [mem_stabilizer_set]
    intro ω
    obtain ⟨hx'fix, hcoordeq⟩ := hP₀x' g hg
    constructor
    · rintro ⟨h, hω⟩
      have hω' : ω ∈ fixSet Ω V := by
        have h' := smul_mem_fixSet_of_mem_normalizer (inv_mem (hP₀V hg)) h
        rwa [inv_smul_smul] at h'
      refine ⟨hω', (hcoordeq _ _).mpr ?_⟩
      rw [hx'fix]
      exact hω
    · rintro ⟨h, hω⟩
      refine ⟨smul_mem_fixSet_of_mem_normalizer (hP₀V hg) h, ?_⟩
      have h' := (hcoordeq _ _).mp hω
      rw [hx'fix] at h'
      exact h'
  have hBorb : B = Subtype.val '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) x' := by
    ext ω
    constructor
    · rintro ⟨h, hω⟩
      exact ⟨⟨ω, h⟩, (DK.coord_eq_iff x' ⟨ω, h⟩).mp hω.symm, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, ((DK.coord_eq_iff x' y).mpr hy).symm⟩
  have hBodd : Odd (Nat.card B) := by
    rw [hBorb, Nat.card_image_of_injective Subtype.val_injective]
    exact odd_card_orbit_jOddCore x'
  have hP₀2 : IsPGroup 2 P₀ := C.sylow.2.1.to_le (hP₀.trans inf_le_left)
  have hFB : Odd (Nat.card ↥(fixSet Ω P₀ ∩ B)) := by
    rw [Nat.odd_iff] at hBodd ⊢
    rw [← card_modEq_card_fixSet_inter_of_le_stabilizer hP₀2 hPB, hBodd]
  obtain ⟨ω₀, hω₀P, hω₀V, hω₀⟩ : (fixSet Ω P₀ ∩ B).Nonempty := by
    have h := hFB.pos
    rw [Nat.card_pos_iff] at h
    exact Set.nonempty_coe_sort.mp h.1
  refine ⟨ω₀, hω₀P, ?_⟩
  rintro (h | h | h)
  · have h' : (⟨ω₀, hω₀V⟩ : fixSet Ω V) = a := Subtype.ext h
    rw [h'] at hω₀
    exact hS₁ab k₁ hk₁S ((congrFun hω₀ k₁).trans (hx'S k₁ hk₁S))
  · have h' : (⟨ω₀, hω₀V⟩ : fixSet Ω V) = b := Subtype.ext h
    rw [h'] at hω₀
    exact hab₂ ((congrFun hω₀ k₂).trans (hx'n k₂ hk₂S)).symm
  · have h' : (⟨ω₀, hω₀V⟩ : fixSet Ω V) = γV := Subtype.ext h
    rw [h'] at hω₀
    exact hγb₁ ((congrFun hω₀ k₁).trans (hx'S k₁ hk₁S))

abbrev boxA (A : Set (C.D.Ψc C.i₁)) : Set Ω :=
  C.boxSet (Function.update (fun _ => Set.univ) C.i₁ A)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_boxA_iff {A : Set (C.D.Ψc C.i₁)} (δ : holtDelta G Ω α β) :
    (δ : Ω) ∈ C.boxA A ↔ C.D.coord δ C.i₁ ∈ A := by
  rw [mem_boxSet_iff]
  refine ⟨fun h => by simpa using h C.i₁, fun h j => ?_⟩
  by_cases hj : j = C.i₁
  · subst hj
    rw [Function.update_self]
    exact h
  · rw [Function.update_of_ne hj]
    exact Set.mem_univ _

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_stabilizer_boxA {p : G} (hp : p ∈ C.calP) {A : Set (C.D.Ψc C.i₁)}
    (hA : ∀ c, C.calGHom ⟨p, C.calP_le_calG hp⟩ c ∈ A ↔ c ∈ A) :
    p ∈ stabilizer G (C.boxA A) := by
  refine C.mem_stabilizer_boxSet (C.mem_stabilizer_pair_of_mem_calP hp) fun δ δ' e => ?_
  rw [← C.mem_boxSet_iff, ← C.mem_boxSet_iff]
  change (δ' : Ω) ∈ C.boxA A ↔ (δ : Ω) ∈ C.boxA A
  rw [C.mem_boxA_iff, C.mem_boxA_iff, C.coord_smul_eq_calGHom ⟨p, C.calP_le_calG hp⟩ e]
  exact hA _

theorem exists_mem_fixSet_of_boxA (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) {A : Set (C.D.Ψc C.i₁)} {c₁ c₂ : C.D.Ψc C.i₁} (hc₁A : c₁ ∈ A)
    (hc₂A : c₂ ∈ A) (hc₁ : c₁ ≠ C.D.coord C.γ C.i₁) (hc₂ : c₂ ≠ C.D.coord C.γ C.i₁)
    (hc₁₂ : c₁ ≠ c₂) (hV1 : C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) ≠ ⊥)
    {P₀ : Subgroup G} (hP₀ : P₀ ≤ C.calP ⊓ stabilizer G (C.boxA A)) :
    ∃ ω ∈ fixSet Ω P₀, ω ∉ ({α, β, (C.γ : Ω)} : Set Ω) := by
  set V := C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) with hV
  have hfixc : ∀ v : C.kerC C.i₁, (v : G) ∈ V → ∀ c ∈ A, C.kerCHom C.i₁ v c = c := by
    intro v hv c hc
    set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
    have hδ : (δ : Ω) ∈ C.boxA A := (C.mem_boxA_iff δ).mpr (by
      rw [C.coord_coordEquiv_symm, Function.update_self]
      exact hc)
    have h := C.coord_smul_eq_kerCHom v (δ := δ) (δ' := δ)
      ((mem_fixingSubgroup_iff G).mp hv.2 _ hδ).symm
    rw [C.coord_coordEquiv_symm, Function.update_self] at h
    exact h.symm
  have hconj : ∀ p ∈ C.calP ⊓ stabilizer G (C.boxA A), ∀ x ∈ V, p * x * p⁻¹ ∈ V := by
    intro p hp x hx
    obtain ⟨⟨hxP, hxK⟩, hxT⟩ := hx
    refine ⟨⟨C.calP.mul_mem (C.calP.mul_mem hp.1 hxP) (C.calP.inv_mem hp.1),
      C.conj_mem_kerC_i₁ (C.calP_le_calG hp.1) hxK⟩, (mem_fixingSubgroup_iff G).mpr ?_⟩
    intro ω hω
    have h1 : p⁻¹ • ω ∈ C.boxA A := by
      have := (mem_stabilizer_set.mp ((stabilizer G (C.boxA A)).inv_mem hp.2) ω).mpr hω
      exact this
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hxT _ h1, smul_inv_smul]
  refine C.exists_mem_fixSet_of_kerC hS hαβ hT hP hr inf_le_left hV1 hc₁ hc₂ hc₁₂
    (fun v hv => ⟨hfixc v hv c₁ hc₁A, hfixc v hv c₂ hc₂A⟩) (hP₀.trans inf_le_left)
    fun p hp => mem_normalizer_of_forall_conj_mem (hconj p (hP₀ hp)) fun x hx => by
      have h := hconj p⁻¹ ((C.calP ⊓ stabilizer G (C.boxA A)).inv_mem (hP₀ hp)) x hx
      rwa [inv_inv] at h

theorem false_of_rStar_two_pow_add_three (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) {a : ℕ} (ha : 2 ≤ a)
    (hcard : Fintype.card (C.D.Ψc C.i₁) = 2 ^ a + 3) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP C.i₁
  set U := C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) with hUdef
  have h2a : 4 ≤ 2 ^ a := (Nat.pow_le_pow_right (by norm_num) ha : 2 ^ 2 ≤ 2 ^ a)
  have h4 : 4 ≤ Fintype.card (C.D.Ψc C.i₁) := by omega
  have hbit : (Fintype.card (C.D.Ψc C.i₁)).testBit 1 := by
    rw [hcard, Nat.testBit_two_pow_add_gt (by omega)]
    decide
  obtain ⟨x₀, hx₀⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hU 1).mp hbit
  rw [pow_one] at hx₀
  obtain ⟨u, v, huv, hO⟩ := Set.ncard_eq_two.mp (by rw [← Nat.card_coe_set_eq]; exact hx₀)
  set γ₁ := C.D.coord C.γ C.i₁ with hγ₁
  have hγO : γ₁ ∉ orbit U x₀ := by
    intro h
    have hOQ : ∀ y, orbit (C.Qimg C.i₁) y = orbit U y := C.orbit_Qimg_eq hS hP C.i₁
    have h1 : orbit U x₀ = {γ₁} := by
      rw [← orbit_eq_iff.mpr h, ← hOQ, C.orbit_Qimg_γ]
    rw [h1, Nat.card_unique] at hx₀
    omega
  have hγu : u ≠ γ₁ := fun h => hγO (h ▸ (hO ▸ Set.mem_insert u {v}))
  have hγv : v ≠ γ₁ := fun h => hγO (h ▸ (hO ▸ Set.mem_insert_of_mem u rfl))
  set A : Set (C.D.Ψc C.i₁) := {u, v} with hA
  have hPA : ∀ p (hp : p ∈ C.calP), ∀ c, c ∈ A → C.calGHom ⟨p, C.calP_le_calG hp⟩ c ∈ A := by
    intro p hp c hc
    rw [← hO] at hc ⊢
    exact C.calGHom_mem_orbit hS hP hp hc
  have hPstab : C.calP ≤ C.calP ⊓ stabilizer G (C.boxA A) := by
    intro p hp
    refine ⟨hp, mem_stabilizer_set.mpr fun ω => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨δ', hδ', hδ'A⟩ := h
      have hω : ω ∈ holtDelta G Ω α β := by
        have h1 := (twoPointElt (C.mem_stabilizer_pair_of_mem_calP (C.calP.inv_mem hp)) • δ').2
        change p⁻¹ • (δ' : Ω) ∈ holtDelta G Ω α β at h1
        rwa [hδ', inv_smul_smul] at h1
      refine (C.mem_boxA_iff ⟨ω, hω⟩).mpr ?_
      have h2 := C.coord_smul_eq_calGHom ⟨p⁻¹, C.calP_le_calG (C.calP.inv_mem hp)⟩
        (δ := δ') (δ' := ⟨ω, hω⟩) (by change ω = p⁻¹ • (δ' : Ω); rw [hδ', inv_smul_smul])
      rw [h2]
      exact hPA _ (C.calP.inv_mem hp) _ ((C.mem_boxA_iff δ').mp ⟨δ', rfl, hδ'A⟩)
    · obtain ⟨δ, rfl, hδA⟩ := h
      have hmem := (twoPointElt (C.mem_stabilizer_pair_of_mem_calP hp) • δ).2
      refine (C.mem_boxA_iff ⟨_, hmem⟩).mpr ?_
      rw [C.coord_smul_eq_calGHom ⟨p, C.calP_le_calG hp⟩ (δ := δ) (δ' := ⟨_, hmem⟩) rfl]
      exact hPA p hp _ ((C.mem_boxA_iff δ).mp ⟨δ, rfl, hδA⟩)
  set Λ : Set (C.D.Ψc C.i₁) := insert γ₁ A with hΛ
  have hUγ : ∀ w ∈ U, w γ₁ = γ₁ := fun w hw => C.Qimg_le_stabilizer C.i₁ hw.1
  have hinv : ∀ w ∈ U, ∀ x ∈ Λ, w x ∈ Λ := by
    intro w hw x hx
    rcases hx with rfl | hx
    · rw [hUγ w hw]; exact Set.mem_insert _ _
    · refine Or.inr ?_
      rw [← hO] at hx ⊢
      have h := orbit_eq_iff.mpr hx
      rw [← h]
      exact ⟨⟨w, hw⟩, rfl⟩
  have hΛcard : Λ.ncard = 3 := by
    rw [hΛ, Set.ncard_insert_of_notMem (by rintro (h | h); exacts [hγu h.symm, hγv h.symm])
      (Set.toFinite _), Set.ncard_pair huv]
  have hcompl : Nat.card ↥Λᶜ = 2 ^ a := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl, hΛcard, Nat.card_eq_fintype_card, hcard]
    omega
  have hfixU := fixSet_inf_fixingSubgroup_eq hU hinv
    (by rw [hcompl]; exact (Nat.even_pow' (by omega)).mpr even_two)
    (by rw [hcompl]; omega)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ Λ := by
    by_contra h
    push Not at h
    have h1 : (Set.univ : Set (C.D.Ψc C.i₁)).ncard ≤ Λ.ncard :=
      Set.ncard_le_ncard (fun x _ => h x) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hΛcard] at h1
    omega
  have hcfix : c ∉ fixSet (C.D.Ψc C.i₁) (U ⊓ fixingSubgroup (Equiv.Perm _) Λ) := by
    rw [hfixU]
    exact hc
  simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hcfix
  obtain ⟨w, hw, hwc⟩ := hcfix
  obtain ⟨q, hqP, hqw⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).1
  have hwΛ : ∀ x ∈ Λ, w x = x := fun x hx =>
    (mem_fixingSubgroup_iff _).mp (Subgroup.mem_inf.mp hw).2 x hx
  have hV1 : C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) ≠ ⊥ := by
    intro h
    have hqV : (q : G) ∈ C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) := by
      refine ⟨⟨hqP, q.2⟩, (mem_fixingSubgroup_iff G).mpr ?_⟩
      rintro _ ⟨δ, rfl, hδ⟩
      refine C.smul_eq_of_kerCHom_fix q (Λc := Function.update (fun _ => Set.univ) C.i₁ A)
        (fun x hx => ?_) δ hδ
      rw [Function.update_self] at hx
      rw [hqw]
      exact hwΛ x (Or.inr hx)
    rw [h, Subgroup.mem_bot] at hqV
    apply hwc
    rw [← hqw, show q = 1 from Subtype.ext hqV, map_one, one_smul]
  obtain ⟨ω, hω, hωt⟩ := C.exists_mem_fixSet_of_boxA hS hαβ hT hP hr (A := A) (c₁ := u)
    (c₂ := v) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) hγu hγv huv hV1 hPstab
  exact C.false_of_mem_fixSet_calP hαβ hω hωt

theorem false_of_rStar_five_of_not_le (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) (hcard : Fintype.card (C.D.Ψc C.i₁) = 5)
    (hodd : ¬ C.Qimg C.i₁ ≤ alternatingGroup (C.D.Ψc C.i₁)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set γ₁ := C.D.coord C.γ C.i₁ with hγ₁
  have hcardΛ : Nat.card ↥(({γ₁} : Set (C.D.Ψc C.i₁))ᶜ) = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp [hcard]
  have hV := C.fusionIsSylowIn_Qimg_inf hS hP C.i₁
  rw [← fixingSubgroup_singleton_perm] at hV
  set QP : Subgroup (Equiv.Perm (C.D.Ψc C.i₁)) := (C.calP.subgroupOf C.calG).map C.calGHom
    with hQPdef
  have hQP : IsPGroup 2 QP :=
    (((C.sylow.2.1.to_le inf_le_left).comap_of_injective C.calG.subtype
      C.calG.subtype_injective).to_le le_rfl).map _
  have hfQP : ∀ (q : C.kerC C.i₁), (q : G) ∈ C.calP → C.kerCHom C.i₁ q ∈ QP := fun q hq =>
    ⟨⟨q, C.kerC_le_calG _ q.2⟩, hq, (C.kerCHom_eq_calGHom q).symm⟩
  have hQimgQP : C.Qimg C.i₁ ≤ QP := by
    intro u hu
    obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg hu
    exact hfQP q hqP
  have hγfix : ∀ p : C.calG, C.calGHom p γ₁ = γ₁ := fun p =>
    (C.coord_smul_eq_calGHom p (δ := C.γ) (δ' := C.γ) (C.calG_le_stabilizer_γ p.2).symm).symm
  have hQPΛ : QP ≤ fixingSubgroup (Equiv.Perm (C.D.Ψc C.i₁)) {γ₁} := by
    rintro _ ⟨p, -, rfl⟩
    rw [fixingSubgroup_singleton_perm]
    exact hγfix p
  obtain ⟨H₁, hH₁Λ, hH₁card, hinv, ⟨s, hsV, hs2, hssw, r, hrV, hr2, hrH, hrfree, hsr⟩, -⟩ :=
    exists_half_system_strong le_rfl hcardΛ hV hQP (inf_le_left.trans hQimgQP) hQPΛ
  have hmemΛ : ∀ x : C.D.Ψc C.i₁, x ∈ ({γ₁} : Set (C.D.Ψc C.i₁))ᶜ ↔ x ≠ γ₁ := fun x => by simp
  have hγH : γ₁ ∉ H₁ := fun h => (hmemΛ _).mp (hH₁Λ h) rfl
  have hsγ : s γ₁ = γ₁ := by
    have := hV.1 hsV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  have hrγ : r γ₁ = γ₁ := by
    have := hV.1 hrV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  have hss : s * s = 1 := by rw [← sq, hs2]
  have hrr : r * r = 1 := by rw [← sq, hr2]
  have hsQ : s ∈ C.Qimg C.i₁ := (Subgroup.mem_inf.mp hsV).1
  have hrQ : r ∈ C.Qimg C.i₁ := (Subgroup.mem_inf.mp hrV).1
  have hrA : r ∈ alternatingGroup (C.D.Ψc C.i₁) := (Subgroup.mem_inf.mp hrV).2
  have hsA : s ∈ alternatingGroup (C.D.Ψc C.i₁) := (Subgroup.mem_inf.mp hsV).2
  have hcompl : ∀ (π : Equiv.Perm (C.D.Ψc C.i₁)), π γ₁ = γ₁ → ∀ x, x ≠ γ₁ → π x ≠ γ₁ :=
    fun π hπ x hx h => hx (π.injective (h.trans hπ.symm))
  have hswapH : ∀ (π : Equiv.Perm (C.D.Ψc C.i₁)), π γ₁ = γ₁ →
      (∀ x ∈ ({γ₁} : Set (C.D.Ψc C.i₁))ᶜ, π x ∈ H₁ ↔ x ∉ H₁) → ∀ x, s (π x) ∈ H₁ ↔ x ∈ H₁ := by
    intro π hπγ hπ x
    by_cases hx : x = γ₁
    · rw [hx, hπγ, hsγ]
    · rw [hssw (π x) ((hmemΛ _).mpr (hcompl π hπγ x hx)), hπ x ((hmemΛ x).mpr hx), not_not]
  have hH₁ne : H₁.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [← Nat.card_coe_set_eq]
    omega
  have hQ : ∀ q : C.kerC C.i₁, (q : G) ∈ C.calP → (∀ x, C.kerCHom C.i₁ q x ∈ H₁ ↔ x ∈ H₁) ∨
      (∀ x, x ≠ γ₁ → (C.kerCHom C.i₁ q x ∈ H₁ ↔ x ∉ H₁)) := by
    intro q hq
    rcases hinv _ (hfQP q hq) with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx => h x ((hmemΛ x).mpr hx)
  obtain ⟨s', hs'P, hs', hfixQ⟩ := C.fix_of_half hS hαβ hT hP (by rw [hcard]) hγH hH₁ne hQ hsQ
    hrQ hsγ (fun x hx => hssw x ((hmemΛ x).mpr hx)) hrγ hrH
    (fun x hx => hrfree x ((hmemΛ x).mpr hx)) hss hrr hsr.eq
  have hH₁2 : H₁.ncard = 2 := by rw [← Nat.card_coe_set_eq]; omega
  obtain ⟨x, y, hxy, hH₁xy⟩ := Set.ncard_eq_two.mp hH₁2
  have hxH : x ∈ H₁ := hH₁xy ▸ Set.mem_insert _ _
  have hyH : y ∈ H₁ := hH₁xy ▸ Set.mem_insert_of_mem _ rfl
  have hxγ : x ≠ γ₁ := fun h => hγH (h ▸ hxH)
  have hyγ : y ≠ γ₁ := fun h => hγH (h ▸ hyH)
  have hH₁mem : ∀ z, z ∈ H₁ ↔ z = x ∨ z = y := fun z => by rw [hH₁xy]; rfl
  obtain ⟨g, hgQ, hgA⟩ : ∃ g ∈ C.Qimg C.i₁, g ∉ alternatingGroup (C.D.Ψc C.i₁) := by
    by_contra h
    push Not at h
    exact hodd h
  have hgγ : g γ₁ = γ₁ := C.Qimg_le_stabilizer C.i₁ hgQ
  obtain ⟨g₁, hg₁Q, hg₁A, hg₁γ, hg₁H⟩ : ∃ g₁ ∈ C.Qimg C.i₁, g₁ ∉ alternatingGroup (C.D.Ψc C.i₁) ∧
      g₁ γ₁ = γ₁ ∧ ∀ z, g₁ z ∈ H₁ ↔ z ∈ H₁ := by
    rcases hinv g (hQimgQP hgQ) with h | h
    · exact ⟨g, hgQ, hgA, hgγ, h⟩
    · refine ⟨s * g, mul_mem hsQ hgQ, fun h' => hgA ?_, by rw [Equiv.Perm.mul_apply, hgγ, hsγ],
        hswapH g hgγ h⟩
      have := mul_mem (inv_mem hsA) h'
      rwa [inv_mul_cancel_left] at this
  obtain ⟨g₂, hg₂Q, hg₂A, hg₂γ, hg₂x, hg₂y⟩ : ∃ g₂ ∈ C.Qimg C.i₁,
      g₂ ∉ alternatingGroup (C.D.Ψc C.i₁) ∧ g₂ γ₁ = γ₁ ∧ g₂ x = x ∧ g₂ y = y := by
    have hg₁x := (hH₁mem _).mp ((hg₁H x).mpr hxH)
    have hg₁y := (hH₁mem _).mp ((hg₁H y).mpr hyH)
    have hrx := (hH₁mem _).mp ((hrH x).mpr hxH)
    have hry := (hH₁mem _).mp ((hrH y).mpr hyH)
    have hrx' : r x = y := hrx.resolve_left (hrfree x ((hmemΛ x).mpr hxγ))
    have hry' : r y = x := hry.resolve_right (hrfree y ((hmemΛ y).mpr hyγ))
    rcases hg₁x with h1 | h1
    · have h2 : g₁ y = y := hg₁y.resolve_left fun h => hxy (g₁.injective (h1.trans h.symm))
      exact ⟨g₁, hg₁Q, hg₁A, hg₁γ, h1, h2⟩
    · have h2 : g₁ y = x := hg₁y.resolve_right fun h => hxy (g₁.injective (h1.trans h.symm))
      refine ⟨g₁ * r, mul_mem hg₁Q hrQ, fun h' => hg₁A ?_, by rw [Equiv.Perm.mul_apply, hrγ,
        hg₁γ], by rw [Equiv.Perm.mul_apply, hrx', h2], by rw [Equiv.Perm.mul_apply, hry', h1]⟩
      have := mul_mem h' (inv_mem hrA)
      rwa [mul_inv_cancel_right] at this
  set A : Set (C.D.Ψc C.i₁) := insert γ₁ H₁ with hA
  obtain ⟨q, hqP, hqg⟩ := C.exists_of_mem_Qimg hg₂Q
  have hV1 : C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) ≠ ⊥ := by
    intro h
    have hqV : (q : G) ∈ C.calP ⊓ C.kerC C.i₁ ⊓ fixingSubgroup G (C.boxA A) := by
      refine ⟨⟨hqP, q.2⟩, (mem_fixingSubgroup_iff G).mpr ?_⟩
      rintro _ ⟨δ, rfl, hδ⟩
      refine C.smul_eq_of_kerCHom_fix q (Λc := Function.update (fun _ => Set.univ) C.i₁ A)
        (fun z hz => ?_) δ hδ
      rw [Function.update_self] at hz
      rw [hqg]
      rcases hz with rfl | hz
      · exact hg₂γ
      · rcases (hH₁mem z).mp hz with rfl | rfl
        exacts [hg₂x, hg₂y]
    rw [h, Subgroup.mem_bot] at hqV
    apply hg₂A
    rw [← hqg, show q = 1 from Subtype.ext hqV, map_one]
    exact one_mem _
  have hstabP : ∀ p (hp : p ∈ C.calP), (∀ z, C.calGHom ⟨p, C.calP_le_calG hp⟩ z ∈ H₁ ↔ z ∈ H₁) →
      p ∈ C.calP ⊓ stabilizer G (C.boxA A) := by
    intro p hp hpH
    refine ⟨hp, C.mem_stabilizer_boxA hp fun c => ?_⟩
    by_cases hc : c = γ₁
    · rw [hc, hγfix]
    · have hpc := hcompl _ (hγfix ⟨p, C.calP_le_calG hp⟩) c hc
      simp only [hA, Set.mem_insert_iff, hc, hpc, false_or, hpH]
  obtain ⟨ω, hω, hωt⟩ := C.exists_mem_fixSet_of_boxA hS hαβ hT hP hr (A := A) (c₁ := x)
    (c₂ := y) (Set.mem_insert_of_mem _ hxH) (Set.mem_insert_of_mem _ hyH) hxγ hyγ hxy hV1 le_rfl
  have hRP0 : C.halfStab C.i₁ H₁ ≤ C.calP ⊓ stabilizer G (C.boxA A) := by
    rintro g ⟨hgP, hgK, hgH⟩
    refine hstabP g hgP fun z => ?_
    rw [show C.calGHom ⟨g, C.calP_le_calG hgP⟩ = C.kerCHom C.i₁ ⟨g, hgK⟩ from
      (C.kerCHom_eq_calGHom ⟨g, hgK⟩).symm]
    exact hgH z
  have hωR : ω ∈ fixSet Ω (C.halfStab C.i₁ H₁) := fun g hg => hω g (hRP0 hg)
  have hs'ω : (s' : G) • ω = ω := hfixQ ω hωR s' ⟨hs'P, s'.2⟩
  have hωP : ω ∈ fixSet Ω C.calP := by
    intro p hp
    rcases hinv _ ⟨⟨p, C.calP_le_calG hp⟩, hp, rfl⟩ with h | h
    · exact hω p (hstabP p hp h)
    · have hsp : (s' : G) * p ∈ C.calP := C.calP.mul_mem hs'P hp
      have h1 : (s' : G) * p ∈ C.calP ⊓ stabilizer G (C.boxA A) := by
        refine hstabP _ hsp fun z => ?_
        have h2 : C.calGHom ⟨(s' : G) * p, C.calP_le_calG hsp⟩ =
            C.calGHom ⟨s', C.kerC_le_calG _ s'.2⟩ * C.calGHom ⟨p, C.calP_le_calG hp⟩ :=
          map_mul C.calGHom ⟨s', C.kerC_le_calG _ s'.2⟩ ⟨p, C.calP_le_calG hp⟩
        rw [h2, ← C.kerCHom_eq_calGHom, hs', Equiv.Perm.mul_apply]
        exact hswapH _ (hγfix _) h z
      have h3 := hω _ h1
      rw [mul_smul] at h3
      exact smul_left_cancel _ (h3.trans hs'ω.symm)
  exact C.false_of_mem_fixSet_calP hαβ hωP hωt

end AltConfig

end CFSG.Holt.H78

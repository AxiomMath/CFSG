module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank

section Target

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem one_lt_card_statedProj_statedSp {r : ℕ} (hr : 1 ≤ r) :
    1 < Nat.card (StatedProj (StatedSp r K)) := by
  have hmono : StrictMono fun r : ℕ => Nat.card (StatedProj (StatedSp r K)) :=
    strictMono_nat_of_lt_succ card_statedProj_statedSp_lt_succ
  have h0 : 0 < Nat.card (StatedProj (StatedSp 0 K)) := Nat.card_pos
  have h1 := hmono (show 0 < r by omega)
  simp only at h1
  omega

theorem exists_mul_ne_statedProj_statedSp (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : 1 ≤ r) :
    ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
  obtain ⟨hsimple, hperf⟩ := simple_perfect_statedProj_of_one_le hq hr
  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  have hbot : commutator (StatedProj (StatedSp r K)) = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hall a b, mul_inv_cancel_right, mul_inv_cancel]
  have htop : commutator (StatedProj (StatedSp r K)) = ⊤ := hperf.commutator_eq_top
  have hnt : Nontrivial (StatedProj (StatedSp r K)) := IsSimpleGroup.toNontrivial
  rw [hbot] at htop
  exact (bot_ne_top : (⊥ : Subgroup (StatedProj (StatedSp r K))) ≠ ⊤) htop

@[expose] noncomputable def spMatTrace {r : ℕ} (g : StatedSp r K) : K :=
  Matrix.trace ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

omit [Finite K] in
theorem spTrace_spProjEquivCharTwo_symm {r : ℕ} (g : StatedSp r K) :
    spTrace ((spProjEquivCharTwo K r).symm g) = spMatTrace g := by
  rw [spTrace, MulEquiv.apply_symm_apply]
  rfl

end Target

section Sections

variable {K : Type} [Field K] [Finite K] [CharP K 2] {C : Type*} [Group C] [Finite C]

theorem spLeviSection_top (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) :
    SpLeviSection fp X ⊤ := by
  refine Or.inl fun r hr => ⟨fun ε => ?_⟩
  have h1 : Nat.card (↥X ⧸ (⊤ : Subgroup ↥X)) = 1 :=
    @Nat.card_of_subsingleton _ 1 QuotientGroup.subsingleton_quotient_top
  have h2 := Nat.card_congr ε.toEquiv
  have h3 := one_lt_card_statedProj_statedSp (K := K) hr
  omega

omit [Finite K] in
theorem spLeviSection_of_card_ne (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C)
    (N : Subgroup ↥X) [N.Normal]
    (h : ∀ r : ℕ, 1 ≤ r → Nat.card (↥X ⧸ N) ≠ Nat.card (StatedProj (StatedSp r K))) :
    SpLeviSection fp X N :=
  Or.inl fun r hr => ⟨fun ε => h r hr (Nat.card_congr ε.toEquiv)⟩

omit [Finite K] in
theorem spLeviSection_of_hom (fp : MulAut C →* (K ≃+* K)) {X : Subgroup C} {r : ℕ} (hr : 1 ≤ r)
    (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X),
      (∀ m ∈ ρ.ker, restrictAutOfMapsTo β X hβ m ∈ ρ.ker) → ∀ x : ↥X,
        spMatTrace (ρ (restrictAutOfMapsTo β X hβ x)) = fp β (spMatTrace (ρ x))) :
    SpLeviSection fp X ρ.ker := by
  set ε₀ : ↥X ⧸ ρ.ker ≃* StatedProj (StatedSp r K) :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).trans (spProjEquivCharTwo K r).symm
    with hε₀
  have hmk : ∀ x : ↥X, ε₀ (x : ↥X ⧸ ρ.ker) = (spProjEquivCharTwo K r).symm (ρ x) := fun x => rfl
  refine Or.inr ⟨r, hr, ε₀, fun β hβ hN y => ?_⟩
  obtain ⟨z, rfl⟩ := ε₀.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [quotAutOfMapsTo_mk, hmk, hmk, spTrace_spProjEquivCharTwo_symm,
    spTrace_spProjEquivCharTwo_symm]
  exact htr β hβ hN x

end Sections

section Characteristic

theorem mem_of_isEmpty_mulEquiv {X : Type*} [Group X] [Finite X] (N₁ N₂ N₃ : Subgroup X)
    [N₁.Normal] [N₂.Normal] [N₃.Normal] (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)),
      ∀ M : Subgroup X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    [IsSimpleGroup (X ⧸ N₁)] (hnc : ∃ a b : X ⧸ N₁, a * b ≠ b * a)
    (h₂ : IsEmpty (X ⧸ N₂ ≃* X ⧸ N₁)) (h₃ : IsEmpty (X ⧸ N₃ ≃* X ⧸ N₁)) (θ : MulAut X) :
    ∀ m ∈ N₁, θ m ∈ N₁ := by
  set M : Subgroup X := N₁.map θ.toMonoidHom with hMdef
  have hMn : M.Normal := ‹N₁.Normal›.map _ θ.surjective
  set e : X ⧸ N₁ ≃* X ⧸ M := QuotientGroup.congr N₁ M θ rfl with he
  have : IsSimpleGroup (X ⧸ M) := MulEquiv.isSimpleGroup e.symm
  have hnc' : ∃ a b : X ⧸ M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' := congrArg e.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : N₁ ⊓ N₂ ⊓ N₃ ≤ M := le_of_isPGroup_of_simple hnc' h123
  have hMtop : M ≠ ⊤ := by
    rintro hM
    have hnt : Nontrivial (X ⧸ M) := IsSimpleGroup.toNontrivial
    have hsub : Subsingleton (X ⧸ M) := by
      rw [hM]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
  have key : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)), N ≤ M → M = N := fun N hN hle =>
    (hq N hN M hMn hle).resolve_right hMtop
  have hM1 : M = N₁ := by
    rcases le_or_le_of_inf_le hnc' hinf with h | h
    · rcases le_or_le_of_inf_le hnc' h with h' | h'
      · exact key N₁ (by simp) h'
      · exfalso
        have hM2 : M = N₂ := key N₂ (by simp) h'
        exact h₂.false ((QuotientGroup.quotientMulEquivOfEq hM2.symm).trans e.symm)
    · exfalso
      have hM3 : M = N₃ := key N₃ (by simp) h
      exact h₃.false ((QuotientGroup.quotientMulEquivOfEq hM3.symm).trans e.symm)
  intro m hm
  have hθm : θ m ∈ M := ⟨m, hm, rfl⟩
  rwa [hM1] at hθm

theorem eq_ker_or_eq_top_of_range {G H : Type*} [Group G] [Group H] (ρ : G →* H)
    (hρ : IsSimpleGroup ρ.range ∨ ρ.range = ⊥) (M : Subgroup G) (hM : M.Normal)
    (hle : ρ.ker ≤ M) : M = ρ.ker ∨ M = ⊤ := by
  rcases hρ with hs | hb
  · have : IsSimpleGroup (G ⧸ ρ.ker) :=
      MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivRange ρ)
    exact eq_or_eq_top_of_simple_quotient M hM hle
  · right
    rw [eq_top_iff]
    intro x _
    apply hle
    have hx : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rw [hb, Subgroup.mem_bot] at hx
    exact hx

end Characteristic

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] {C : Type*} [Group C] [Finite C]

omit [Finite C] in
theorem isEmpty_quotient_top_mulEquiv (X : Subgroup C) {r : ℕ} (hr : 1 ≤ r) :
    IsEmpty (↥X ⧸ (⊤ : Subgroup ↥X) ≃* StatedProj (StatedSp r K)) := by
  refine ⟨fun ε => ?_⟩
  have h1 : Nat.card (↥X ⧸ (⊤ : Subgroup ↥X)) = 1 :=
    @Nat.card_of_subsingleton _ 1 QuotientGroup.subsingleton_quotient_top
  have h2 := Nat.card_congr ε.toEquiv
  have h3 := one_lt_card_statedProj_statedSp (K := K) hr
  omega

theorem spLeviData_of_isEmpty_mulEquiv (fp : MulAut C →* (K ≃+* K)) (hq4 : 4 ≤ Nat.card K)
    {X : Subgroup C} (N₁ N₂ N₃ : Subgroup ↥X) [N₁.Normal] [N₂.Normal] [N₃.Normal]
    (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hs : ∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      SpLeviSection fp X N)
    {r : ℕ} (hr : 1 ≤ r) (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K))
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K)))
    (h₃ : IsEmpty (↥X ⧸ N₃ ≃* StatedProj (StatedSp r K))) : SpLeviData fp X := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  have : IsSimpleGroup (↥X ⧸ N₁) := MulEquiv.isSimpleGroup e
  have hnc : ∃ a b : ↥X ⧸ N₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_statedProj_statedSp hq4 hr
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact ⟨N₁, N₂, N₃, inferInstance, inferInstance, inferInstance, h123, hq, hs, r, hr, ⟨e⟩,
    fun β hβ => mem_of_isEmpty_mulEquiv N₁ N₂ N₃ h123 hq hnc
      ⟨fun e₂ => h₂.false (e₂.trans e)⟩ ⟨fun e₃ => h₃.false (e₃.trans e)⟩ _⟩

theorem spLeviData_two_of_isEmpty_mulEquiv (fp : MulAut C →* (K ≃+* K)) (hq4 : 4 ≤ Nat.card K)
    {X : Subgroup C} (N₁ N₂ : Subgroup ↥X) [N₁.Normal] [N₂.Normal]
    (h12 : IsPGroup 2 ↥(N₁ ⊓ N₂))
    (hq₁ : ∀ M : Subgroup ↥X, M.Normal → N₁ ≤ M → M = N₁ ∨ M = ⊤)
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₁ : SpLeviSection fp X N₁) (hs₂ : SpLeviSection fp X N₂)
    {r : ℕ} (hr : 1 ≤ r) (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K))
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K))) : SpLeviData fp X := by
  refine spLeviData_of_isEmpty_mulEquiv fp hq4 N₁ N₂ ⊤ (by rwa [inf_top_eq]) ?_ ?_ hr e h₂
    (isEmpty_quotient_top_mulEquiv X hr)
  · intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₂ M hM hle
    · exact Or.inr (top_le_iff.mp hle)
  · intro N _ hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hs₁
    · exact hs₂
    · exact spLeviSection_top fp X

theorem spLeviData_one (fp : MulAut C →* (K ≃+* K)) (hq4 : 4 ≤ Nat.card K) {X : Subgroup C}
    (N₁ : Subgroup ↥X) [N₁.Normal] (h1 : IsPGroup 2 ↥N₁)
    (hs₁ : SpLeviSection fp X N₁) {r : ℕ} (hr : 1 ≤ r)
    (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K)) : SpLeviData fp X := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  have : IsSimpleGroup (↥X ⧸ N₁) := MulEquiv.isSimpleGroup e
  exact spLeviData_two_of_isEmpty_mulEquiv fp hq4 N₁ ⊤ (by rwa [inf_top_eq])
    (eq_or_eq_top_of_simple_quotient (N := N₁))
    (fun M _ hle => Or.inr (top_le_iff.mp hle)) hs₁ (spLeviSection_top fp X) hr e
    (isEmpty_quotient_top_mulEquiv X hr)

end Data

end CFSG.SeitzReduction.OmegaPilot

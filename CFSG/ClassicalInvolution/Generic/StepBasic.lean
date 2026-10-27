module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType CFSG.LieType.Universal

variable (p f : ℕ) [Fact p.Prime]

section Corefree

variable {Y : Type} [Group Y]

@[expose] noncomputable def oddQuotientEquivOfCorefree
    (hO : classicalInvolutionOddCore Y = ⊥) : Y ≃* Y ⧸ classicalInvolutionOddCore Y :=
  MulEquiv.ofBijective (QuotientGroup.mk' (classicalInvolutionOddCore Y))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hO]),
      QuotientGroup.mk'_surjective _⟩

theorem oddQuotientEquivOfCorefree_toMonoidHom (hO : classicalInvolutionOddCore Y = ⊥) :
    (oddQuotientEquivOfCorefree hO).toMonoidHom =
      QuotientGroup.mk' (classicalInvolutionOddCore Y) := rfl

variable {p f}

theorem lieSystemMod_of_lieSystem_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : LieSystem p f Y Λ) : LieSystemMod p f Λ :=
  LieSystem.congr (oddQuotientEquivOfCorefree hO) h

theorem lieSystem_of_lieSystemMod_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : LieSystemMod p f Λ) : LieSystem p f Y Λ := by
  have key : Subgroup.map (oddQuotientEquivOfCorefree hO).symm.toMonoidHom ''
      oddQuotientFamily Λ = Λ := by
    ext L
    constructor
    · rintro ⟨_, ⟨L', hL', rfl⟩, rfl⟩
      rw [Subgroup.map_map]
      have : (oddQuotientEquivOfCorefree hO).symm.toMonoidHom.comp
          (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = MonoidHom.id Y := by
        ext x
        exact (oddQuotientEquivOfCorefree hO).symm_apply_apply x
      rw [this, Subgroup.map_id]
      exact hL'
    · intro hL
      refine ⟨L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)), ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map]
      have : (oddQuotientEquivOfCorefree hO).symm.toMonoidHom.comp
          (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = MonoidHom.id Y := by
        ext x
        exact (oddQuotientEquivOfCorefree hO).symm_apply_apply x
      rw [this, Subgroup.map_id]
  have := LieSystem.congr (oddQuotientEquivOfCorefree hO).symm h
  rwa [key] at this

end Corefree

section Single

variable {p f} {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] noncomputable def LieSystemData.single {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n e : ℕ} (hp : p.Prime) (ht : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e)
    (hexp : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) (ψ : (modelUniv t n p e hp).K →* X)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _)
    (hfund : ∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, L = R.map ψ)
    (hmeets : ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, R.map ψ ∈ Φ) :
    LieSystemData p f X Φ where
  card := 1
  tag := fun _ => t
  rank := fun _ => n
  exp := fun _ => e
  hom := fun _ => ψ
  isFundTag := fun _ => ht
  admissible := fun _ => hadm
  exp_eq := fun _ => hexp
  ker_le_center := fun _ => hker
  commute := fun i j h => absurd (Subsingleton.elim i j) h
  generate := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨y, rfl⟩
  fundamental := fun L hL => ⟨0, hfund L hL⟩
  meets := fun _ => hmeets

theorem lieSystem_range_conj_of_model {G : Type} [Group G] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n e : ℕ} (hp : p.Prime) (ht : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e)
    (hexp : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) (ψ : (modelUniv t n p e hp).K →* G)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D) :
    LieSystem p f G (Set.range fun g : G => conjSub g (R.map ψ)) := by
  refine ⟨LieSystemData.single hp ht hadm hexp ψ hsurj hker ?_ ?_⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ := hsurj g
    refine ⟨conjSub k R, ?_, conjSub_map ψ k R⟩
    obtain ⟨h, γ, hγ, rfl⟩ := hR
    exact ⟨k * h, γ, hγ, (conjSub_mul k h _).symm⟩
  · exact ⟨R, hR, 1, conjSub_one _⟩

end Single

section Simple

variable {p f} {G : Type} [Group G] [IsSimpleGroup G] {Φ : Set (Subgroup G)}

theorem LieSystemData.range_normal {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) : ((D.hom i).range).Normal := by
  have key : ∀ g ∈ (⨆ k, (D.hom k).range : Subgroup X), ∀ n ∈ (D.hom i).range,
      g * n * g⁻¹ ∈ (D.hom i).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact ((D.hom k).range).mul_mem (((D.hom k).range).mul_mem hy hn)
          (((D.hom k).range).inv_mem hy)
      · obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hn
        rw [D.commute k i hki a b, mul_assoc, mul_inv_cancel, mul_one]
        exact ⟨b, rfl⟩
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

theorem LieSystemData.exists_surjective_of_simple (D : LieSystemData p f G Φ) :
    ∃ i, Function.Surjective (D.hom i) := by
  by_contra hne
  push Not at hne
  have hbot : ∀ i, (D.hom i).range = ⊥ := fun i => by
    have := D.range_normal i
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.hom i).range).resolve_right
      fun h => hne i (MonoidHom.range_eq_top.mp h)
  have h : (⨆ i, (D.hom i).range : Subgroup G) = ⊥ := by simp [hbot]
  rw [D.generate] at h
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have h1 : a ∈ (⊤ : Subgroup G) := trivial
  have h2 : b ∈ (⊤ : Subgroup G) := trivial
  rw [h, Subgroup.mem_bot] at h1 h2
  exact hab (h1.trans h2.symm)

theorem LieSystemData.ker_eq_center_of_surjective (hnab : ∃ a b : G, a * b ≠ b * a)
    (D : LieSystemData p f G Φ) {i : Fin D.card} (hi : Function.Surjective (D.hom i)) :
    (D.hom i).ker = Subgroup.center _ := by
  refine le_antisymm (D.ker_le_center i) fun x hx => ?_
  have hc : D.hom i x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hi g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx k]
  rw [CFSG.ComponentClassification.Helpers.center_eq_bot G hnab, Subgroup.mem_bot] at hc
  exact hc

theorem LieSystemData.exists_model_of_simple (hnab : ∃ a b : G, a * b ≠ b * a)
    (D : LieSystemData p f G Φ) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) (hp : p.Prime)
      (ψ : (modelUniv t n p e hp).K →* G),
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center _ ∧ IsFundTag t ∧
        CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e ∧
        (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) := by
  obtain ⟨i, hsurj⟩ := D.exists_surjective_of_simple
  exact ⟨D.tag i, D.rank i, D.exp i, Fact.out, D.hom i, hsurj,
    D.ker_eq_center_of_surjective hnab hsurj, D.isFundTag i, D.admissible i, D.exp_eq i⟩

end Simple

theorem oddCore_eq_bot_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) : classicalInvolutionOddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore G) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (classicalInvolutionOddCore G)) :=
      CFSG.ComponentClassification.OddCore.odd_card G
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    have hcard : Nat.card (classicalInvolutionOddCore G) = Nat.card G := by
      rw [h, Subgroup.card_top]
    rw [hcard] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.ClassicalInvolution.Generic

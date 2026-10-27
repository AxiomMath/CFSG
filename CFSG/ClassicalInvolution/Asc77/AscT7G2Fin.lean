module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRLit
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Bsub
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Act
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Idx4
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Swap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected


variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_20_ex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
          ∃ s ∈ (S : Subgroup G), conjSub s R = R ∧ s ∉ R ⊔ R' ∧ s * t' = t' * s ∧ s * s = 1

@[expose] def C25_20_inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∀ t' : G, t' ∈ (S : Subgroup G) → t' * t' = 1 → (∃ g : G, g * z * g⁻¹ = t') →
          conjSub t' R = R' → (¬ ∃ y : G, y * z * y⁻¹ = t' * z) →
            ∃ s ∈ (S : Subgroup G), conjSub s R = R ∧ s ∉ R ⊔ R' ∧ s * t' = t' * s ∧ s * s = 1

variable {p f}

namespace T7G2

open T7F2 T7DR
open scoped commutatorElement

theorem c25_20_of_ex (h11 : C25_11 p f) (h16 : C25_16 p f) (hex : C25_20_ex p f) :
    C25_20 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, s, hsS, hsR, hsn, hst', hs2⟩ :=
    hex G Ω K K' W S R R' z t u₁ u₂ hyp h4
  have hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  obtain ⟨hC', hC, hP', hP, hidx⟩ := struct hT h11 h16 h4
  have hsN : s ∈ Nsub S R := mem_Nsub.mpr ⟨hsS, hsR⟩
  have hti := hT.ht'inv
  refine ⟨s, t', hsS, ht'S, ⟨g, hg⟩, ht'R, hs2, hst', hsR, ?_, ?_⟩
  ·
    have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
      h16 G Ω K K' W S R R' z t u₁ u₂ hyp y (mem_Nsub.mp hy).1
    have hN2 : IsPGroup 2 ↥(Nsub S R) := S.isPGroup'.to_le (show Nsub S R ≤ _ from inf_le_left)
    have hm : t' * s * t'⁻¹ ∈ Nsub S R := hT.N_conj hsN
    have hmn : t' * s * t'⁻¹ ∉ R' ⊔ (Nsub S R ⊓ Subgroup.centralizer (R' : Set G)) := by
      have heq : Nsub S R ⊓ Subgroup.centralizer (R' : Set G) = Csub S R' := by
        ext x
        constructor
        · rintro ⟨hxN, hxc⟩
          exact mem_Csub.mpr ⟨(mem_Nsub.mp hxN).1,
            fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
        · intro hx
          exact ⟨hT.C'_le_N hx, Subgroup.mem_centralizer_iff.mpr (mem_Csub.mp hx).2⟩
      rw [heq]
      have hPeq : R' ⊔ Csub S R' = R ⊔ R' := hP'
      rw [hPeq]
      intro hmem
      apply hsn
      have h1 := conj_mem_RR hT ht'S hmem
      have e : t' * (t' * s * t'⁻¹) * t'⁻¹ = s := by
        calc t' * (t' * s * t'⁻¹) * t'⁻¹ = (t' * t') * s * (t'⁻¹ * t'⁻¹) := by group
          _ = s := by rw [ht'2, hti, ht'2]; group
      rw [e] at h1
      exact h1
    obtain ⟨r', hr', hnot⟩ := exists_comm_not_mem hT.hqR' hT.hzR' hT.R'_le_N hN2
      (fun y hy => hT.conj_R'_of_mem_N hy) hF hm hmn
    have hr : t'⁻¹ * r' * t' ∈ R := by
      have : r' ∈ conjSub t' R := by rw [ht'R]; exact hr'
      exact mem_conjSub_iff.mp this
    refine ⟨t'⁻¹ * r' * t', hr, fun hmem => hnot ?_⟩
    have hconjR : ∀ r ∈ R, t' * r * t'⁻¹ ∈ R' := fun r hr => by
      have := conj_mem_conjSub (n := t') hr
      rwa [ht'R] at this
    have h1 := squaresSub_conj_mem hconjR hmem
    have e : t' * ⁅s, t'⁻¹ * r' * t'⁆ * t'⁻¹ = ⁅t' * s * t'⁻¹, r'⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e] at h1
    exact h1
  ·
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact (sup_le hT.hRS hT.hR'S) hx
      · rcases hx with rfl | hx
        · exact hsS
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ht'S
    · intro x hx
      have hclN : ∀ y ∈ Nsub S R,
          y ∈ Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) := by
        intro y hy
        by_cases hyR : y ∈ R ⊔ R'
        · exact Subgroup.subset_closure (Or.inl hyR)
        · have hs1 : s⁻¹ ∉ R ⊔ R' := fun h1 => hsn (by simpa using (R ⊔ R').inv_mem h1)
          have hmem : s⁻¹ * y ∈ R ⊔ R' :=
            (mul_mem_iff_of_relIndex_two hidx ((Nsub S R).inv_mem hsN) hy).mpr
              (iff_of_false hs1 hyR)
          have e : y = s * (s⁻¹ * y) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
            (Subgroup.subset_closure (Or.inl hmem))
      have ht'c : t' ∈ Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) :=
        Subgroup.subset_closure (Or.inr (Or.inr rfl))
      rcases hT.S_cover hx with hxN | htxN
      · exact hclN x hxN
      · have e : x = t'⁻¹ * (t' * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.closure _).inv_mem ht'c) (hclN _ htxN)

theorem c25_20_ex_of_inv (hinv : C25_20_inv p f) : C25_20_ex p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨t', ht'S, ht'2, hg, ht'R, hnf⟩ := exists_swap_nonfused hyp
  obtain ⟨s, hsS, hsR, hsn, hst', hs2⟩ :=
    hinv G Ω K K' W S R R' z t u₁ u₂ hyp h4 t' ht'S ht'2 hg ht'R hnf
  exact ⟨t', ht'S, ht'2, hg, ht'R, s, hsS, hsR, hsn, hst', hs2⟩

theorem c25_20_of_inv (h11 : C25_11 p f) (h16 : C25_16 p f) (hinv : C25_20_inv p f) :
    C25_20 p f :=
  c25_20_of_ex h11 h16 (c25_20_ex_of_inv hinv)

theorem c25_20_ex_of_c25_20 (h : C25_20 p f) : C25_20_ex p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨s, t', hsS, ht'S, ⟨g, hg⟩, ht'R, hs2, hst', hsR, ⟨r, hr, hnot⟩, -⟩ :=
    h G Ω K K' W S R R' z t u₁ u₂ hyp h4
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hcomm : Commutes R R' := by
    have hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
    exact hT.hcomm
  refine ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, s, hsS, hsR, ?_, hst', hs2⟩
  intro hs
  apply hnot
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := Out.exists_mul_of_mem_sup_of_commute hcomm hs
  have h1 : ρ' * r = r * ρ' := (hcomm r hr ρ' hρ').symm
  have e : ⁅ρ * ρ', r⁆ = ⁅ρ, r⁆ := by
    simp only [commutatorElement_def]
    calc ρ * ρ' * r * (ρ * ρ')⁻¹ * r⁻¹ = ρ * (ρ' * r) * ρ'⁻¹ * ρ⁻¹ * r⁻¹ := by group
      _ = ρ * (r * ρ') * ρ'⁻¹ * ρ⁻¹ * r⁻¹ := by rw [h1]
      _ = ρ * r * ρ⁻¹ * r⁻¹ := by group
  rw [e]
  exact commutator_mem_squaresSub hρ hr

end T7G2

end CFSG.ClassicalInvolution.Asc77

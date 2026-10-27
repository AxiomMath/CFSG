module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.NoFusion
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {X : Type*} [Group X]

section Transfer

theorem inf_commutator_eq (hIG : IG_15_15) {Y : Type} [Group Y]
    [Finite Y] {T A : Subgroup Y} (hT : IsSylow2In T ⊤) (hAT : A ≤ T) (hidx : A.relIndex T = 2)
    (hNF : ∀ w ∈ T, w ∉ A → ∀ c : Y, c * w * c⁻¹ ∉ A) (hAc : A ≤ commutator Y) :
    T ⊓ commutator Y = A := by
  classical
  have hne : ∃ w, w ∈ T ∧ w ∉ A := by
    by_contra h
    have h1 : A.relIndex T = 1 := Subgroup.relIndex_eq_one.2 (fun t ht => by
      by_contra hn; exact h ⟨t, ht, hn⟩)
    omega
  obtain ⟨w, hw⟩ := hne
  obtain ⟨u, ⟨huT, huA⟩, hmin⟩ := Set.exists_min_image {w : Y | w ∈ T ∧ w ∉ A} orderOf
    (Set.toFinite _) ⟨w, hw⟩
  have hAneT : A ≠ T := fun h => huA (h ▸ huT)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ A := by
    refine ⟨u, huT, fun t ht => ?_⟩
    rcases pigeon_of_relIndex_two hidx huT ht with h | h | h
    · exact absurd h huA
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hext : ∀ y ∈ T, (∃ g : Y, g⁻¹ * u * g = y) →
      IsExtremal T y → y ∈ A ∨ u⁻¹ * y ∈ A := by
    intro y hy _ _
    rcases pigeon_of_relIndex_two hidx huT hy with h | h | h
    · exact absurd h huA
    · exact Or.inl h
    · exact Or.inr h
  have hmin' : ∀ v ∈ T, v ∉ A → orderOf u ≤ orderOf v := fun v hv hvA => hmin v ⟨hv, hvA⟩
  rcases hIG Y T A u hT hAT (fun t ht q hq => conj_mem_of_relIndex_two hAT hidx ht hq) hAneT hcyc
      huT huA hmin' hext with ⟨N, hN, hcycN, _, huN⟩ | ⟨g, hg, _, _⟩
  · have hcomm : ∀ a b : Y ⧸ N, a * b = b * a := by
      obtain ⟨g, hg⟩ := hcycN
      intro a b
      obtain ⟨m, rfl⟩ := hg a
      obtain ⟨n, rfl⟩ := hg b
      exact (Commute.zpow_zpow_self g m n).eq
    have hcN : commutator Y ≤ N := by
      show ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ N
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm (a : Y ⧸ N) (b : Y ⧸ N)]
      group
    refine le_antisymm (fun x hx => ?_) (le_inf hAT hAc)
    by_contra hxA
    have hxT : x ∈ T := (Subgroup.mem_inf.1 hx).1
    have hxc : x ∈ commutator Y := (Subgroup.mem_inf.1 hx).2
    rcases pigeon_of_relIndex_two hidx huT hxT with h | h | h
    · exact huA h
    · exact hxA h
    · have h1 : u⁻¹ * x ∈ N := hcN (hAc h)
      have h2 : x ∈ N := hcN hxc
      apply huN
      have := N.mul_mem h2 (N.inv_mem h1)
      simpa using this
  · exact absurd hg (by simpa using hNF u huT huA g⁻¹)


theorem isSylow2In_top_subgroupOf {H A : Subgroup X} (hA : IsSylow2In A H) :
    IsSylow2In (A.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, hA.2.1.comap_subtype (K := H), ?_⟩
  have := hA.2.2
  rwa [Subgroup.relIndex_top_right]

theorem fusion_control (hIG : IG_16_2) {Y : Type} [Group Y]
    [Finite Y] {H A : Subgroup Y} [H.Normal] (hA : IsSylow2In A H)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ g : Y, g⁻¹ * a * g = b →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * a * n = b := by
  intro a ha b hb g hg
  have hHg : Hconj g H = H := by
    ext t
    simp only [mem_Hconj]
    constructor
    · intro ht
      have := (inferInstance : H.Normal).conj_mem _ ht g⁻¹
      simpa [mul_assoc] using this
    · intro ht
      exact (inferInstance : H.Normal).conj_mem _ ht g
  have hAg : IsSylow2In (Hconj g A) H := by
    have := sylow2_conj hA g
    rwa [hHg] at this
  obtain ⟨m, hmH, hm⟩ := sylow2_exists_conj hA hAg
  have hn₁ : g * m⁻¹ ∈ Subgroup.normalizer (A : Set Y) := by
    have h1 : Hconj (g * m⁻¹) A = A := by
      have e1 : Hconj (g * m⁻¹) A = Hconj m⁻¹ (Hconj g A) := by rw [Hconj_mul]
      rw [e1, hm, Hconj_inv_Hconj]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := congrArg (fun K : Subgroup Y => h ∈ K) h1
    simp only [mem_Hconj, eq_iff_iff] at this
    exact this.symm
  set n₁ := g * m⁻¹ with hn₁def
  have hgm : g = n₁ * m := by rw [hn₁def]; group
  have ha' : n₁⁻¹ * a * n₁ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn₁) a).1 ha
    simpa using this
  set P := A.subgroupOf H with hP
  have hPS := isSylow2In_top_subgroupOf hA
  have hAH : A ≤ H := hA.1
  have hbm : m⁻¹ * (n₁⁻¹ * a * n₁) * m = b := by
    rw [← hg, hgm]; group
  obtain ⟨n', hn', hnb⟩ := hIG ↥H P hPS (⟨n₁⁻¹ * a * n₁, hAH ha'⟩ : ↥H) (⟨b, hAH hb⟩ : ↥H) ha'
    hb (fun t ht => Subtype.ext (hAab _ ha' _ ht)) (fun t ht => Subtype.ext (hAab _ hb _ ht))
    ⟨⟨m, hmH⟩, Subtype.ext (by simpa using hbm)⟩
  refine ⟨n₁ * (n' : Y), ?_, ?_⟩
  · refine Subgroup.mul_mem _ hn₁ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhH : h ∈ H
    · exact Subgroup.mem_normalizer_iff.1 hn' (⟨h, hhH⟩ : ↥H)
    · refine iff_of_false (fun hh => hhH (hAH hh)) (fun hh => hhH ?_)
      have h1 : (n' : Y) * h * (n' : Y)⁻¹ ∈ H := hAH hh
      have h2 : (n' : Y)⁻¹ * ((n' : Y) * h * (n' : Y)⁻¹) * (n' : Y) ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem n'.2) h1) n'.2
      simpa [mul_assoc] using h2
  · have := congrArg Subtype.val hnb
    have e : (n₁ * (n' : Y))⁻¹ * a * (n₁ * (n' : Y)) =
        (n' : Y)⁻¹ * (n₁⁻¹ * a * n₁) * (n' : Y) := by group
    rw [e]
    simpa using this

end Transfer

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERIdx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7F2

section Basic

variable {G : Type} [Group G]

@[expose] def Nsub (S : Sylow 2 G) (R : Subgroup G) : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)

@[expose] def Csub (S : Sylow 2 G) (R : Subgroup G) : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G)

theorem mem_Nsub {S : Sylow 2 G} {R : Subgroup G} {n : G} :
    n ∈ Nsub S R ↔ n ∈ (S : Subgroup G) ∧ conjSub n R = R := by
  unfold Nsub
  rw [Subgroup.mem_inf, mem_normalizer_iff_conjSub_eq]

theorem mem_Csub {S : Sylow 2 G} {R : Subgroup G} {x : G} :
    x ∈ Csub S R ↔ x ∈ (S : Subgroup G) ∧ ∀ r ∈ R, r * x = x * r := by
  unfold Csub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem conjSub_eq_of_centralizes {R : Subgroup G} {x : G} (hx : ∀ r ∈ R, r * x = x * r) :
    conjSub x R = R := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have h1 : x * (x⁻¹ * y * x) = (x⁻¹ * y * x) * x := (hx _ hy).symm
    have : y = x⁻¹ * y * x := by
      calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
        _ = (x⁻¹ * y * x) * x * x⁻¹ := by rw [h1]
        _ = x⁻¹ * y * x := by group
    rw [this]; exact hy
  · intro hy
    have h1 := hx y hy
    have : x⁻¹ * y * x = y := by
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [← h1]
        _ = y := by group
    rw [this]; exact hy

theorem conjSub_inf_centralizer (g : G) (A X : Subgroup G) :
    conjSub g (A ⊓ Subgroup.centralizer (X : Set G)) =
      conjSub g A ⊓ Subgroup.centralizer ((conjSub g X : Subgroup G) : Set G) := by
  ext y
  simp only [mem_conjSub_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h x hx => ?_⟩
  · have hx := h (g⁻¹ * z * g) (mem_conjSub_iff.mp hz)
    calc z * y = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hx]
      _ = y * z := by group
  · have hgx : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have := h (g * x * g⁻¹) (mem_conjSub_iff.mpr (by rw [hgx]; exact hx))
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * y * g) * x := by group

theorem conjSub_sup' (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
  Subgroup.map_sup _ _ _

end Basic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}


structure Hyp25T (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G) : Prop where
  hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂
  ht'S : t' ∈ (S : Subgroup G)
  ht'2 : t' * t' = 1
  ht'R : conjSub t' R = R'

namespace Hyp25T

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem hs : Hyp23Setting p f Ω K K' z := h.hyp.std.setting

theorem hp : p ≠ 2 := h.hs.stand.odd

theorem hΩ : HypOmegaMod p f Ω := h.hs.stand.hyp

theorem hK : K ∈ Ω := h.hs.stand.mem

theorem hK' : K' ∈ Ω := h.hs.hK'.1

theorem hz : IsUniqueInvolution K z := h.hs.hz

theorem hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hs.hK'

theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hp h.hΩ h.hK h.hyp.hR.1 h.hyp.hR.2.1

theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hp h.hΩ h.hK' h.hyp.hR'.1 h.hyp.hR'.2.1

theorem hRS : R ≤ (S : Subgroup G) := h.hyp.hR.2.2

theorem hR'S : R' ≤ (S : Subgroup G) := h.hyp.hR'.2.2

theorem hcomm : Commutes R R' :=
  h.hΩ.commutes_of_twin_of_isPGroup h.hK h.hK' h.hs.hne.symm h.hz h.hz' h.hRsyl.1 h.hR'syl.1
    (S.isPGroup'.to_le (sup_le h.hRS h.hR'S))

theorem hne : R ≠ R' := T7ER.ne_of_hyp25 h.hyp

theorem hqR : IsQuatSub R := h.hΩ.isQuatSub_of_mem_RSet h.hp h.hyp.hR.1

theorem hqR' : IsQuatSub R' := h.hΩ.isQuatSub_of_mem_RSet h.hp h.hyp.hR'.1

theorem hzR : IsUniqueInvolution R z :=
  AscL62.isUniqueInvolution_of_le h.hz h.hRsyl.1
    (mem_of_isUniqueInvolution_of_isPGroup h.hz h.hRsyl.1 h.hRsyl.2.1
      (by have := h.hqR.eight_le; omega))

theorem hzR' : IsUniqueInvolution R' z :=
  AscL62.isUniqueInvolution_of_le h.hz' h.hR'syl.1
    (mem_of_isUniqueInvolution_of_isPGroup h.hz' h.hR'syl.1 h.hR'syl.2.1
      (by have := h.hqR'.eight_le; omega))

theorem perm_R {s : G} (hs : s ∈ (S : Subgroup G)) : conjSub s R = R ∨ conjSub s R = R' := by
  have hmem : conjSub s R ∈ RSet Ω := RSet.conj h.hΩ.conjInvariant h.hyp.hR.1 s
  have hle : conjSub s R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (h.hRS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact h.hyp.hRS _ hmem hle

theorem perm_R' {s : G} (hs : s ∈ (S : Subgroup G)) : conjSub s R' = R ∨ conjSub s R' = R' := by
  have hmem : conjSub s R' ∈ RSet Ω := RSet.conj h.hΩ.conjInvariant h.hyp.hR'.1 s
  have hle : conjSub s R' ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (h.hR'S hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact h.hyp.hRS _ hmem hle

theorem ht'R' : conjSub t' R' = R := by
  have : conjSub (t' * t') R = R := by rw [h.ht'2, conjSub_one]
  rw [conjSub_mul, h.ht'R] at this
  exact this

theorem ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right h.ht'2

theorem card_R_eq : Nat.card R = Nat.card R' := by
  rw [← h.ht'R, AscL62.natCard_conjSub]

theorem conj_R'_of_mem_N {n : G} (hn : n ∈ Nsub S R) : conjSub n R' = R' := by
  obtain ⟨hnS, hnR⟩ := mem_Nsub.mp hn
  rcases h.perm_R' hnS with h1 | h1
  · exfalso
    exact h.hne (conjSub_injective n (hnR.trans h1.symm))
  · exact h1

theorem mem_N_of_conj_R' {n : G} (hnS : n ∈ (S : Subgroup G)) (hn : conjSub n R' = R') :
    n ∈ Nsub S R := by
  refine mem_Nsub.mpr ⟨hnS, ?_⟩
  rcases h.perm_R hnS with h1 | h1
  · exact h1
  · exfalso
    exact h.hne (conjSub_injective n (h1.trans hn.symm))

theorem t'_not_mem_N : t' ∉ Nsub S R := by
  intro hmem
  have := (mem_Nsub.mp hmem).2
  rw [h.ht'R] at this
  exact h.hne this.symm

theorem S_cover {s : G} (hs : s ∈ (S : Subgroup G)) : s ∈ Nsub S R ∨ t' * s ∈ Nsub S R := by
  rcases h.perm_R hs with h1 | h1
  · exact Or.inl (mem_Nsub.mpr ⟨hs, h1⟩)
  · right
    refine mem_Nsub.mpr ⟨(S : Subgroup G).mul_mem h.ht'S hs, ?_⟩
    rw [conjSub_mul, h1, h.ht'R']

theorem N_conj {n : G} (hn : n ∈ Nsub S R) : t' * n * t'⁻¹ ∈ Nsub S R := by
  obtain ⟨hnS, hnR⟩ := mem_Nsub.mp hn
  refine mem_Nsub.mpr ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem h.ht'S hnS)
    ((S : Subgroup G).inv_mem h.ht'S), ?_⟩
  rw [conjSub_mul, conjSub_mul, h.ht'inv, h.ht'R, h.conj_R'_of_mem_N hn, h.ht'R']

theorem C_le_N : Csub S R ≤ Nsub S R := fun _ hx =>
  mem_Nsub.mpr ⟨(mem_Csub.mp hx).1, conjSub_eq_of_centralizes (mem_Csub.mp hx).2⟩

theorem C'_le_N : Csub S R' ≤ Nsub S R := fun _ hx =>
  h.mem_N_of_conj_R' (mem_Csub.mp hx).1 (conjSub_eq_of_centralizes (mem_Csub.mp hx).2)

theorem R_le_N : R ≤ Nsub S R := fun _ hr =>
  mem_Nsub.mpr ⟨h.hRS hr, conjSub_eq_self_of_mem hr⟩

theorem R'_le_N : R' ≤ Nsub S R := fun _ hr =>
  h.mem_N_of_conj_R' (h.hR'S hr) (conjSub_eq_self_of_mem hr)

theorem R'_le_C : R' ≤ Csub S R := fun r hr =>
  mem_Csub.mpr ⟨h.hR'S hr, fun x hx => (h.hcomm x hx r hr)⟩

theorem R_le_C' : R ≤ Csub S R' := fun r hr =>
  mem_Csub.mpr ⟨h.hRS hr, fun x hx => (h.hcomm r hr x hx).symm⟩

theorem conj_C' : conjSub t' (Csub S R') = Csub S R := by
  unfold Csub
  rw [conjSub_inf_centralizer, h.ht'R', conjSub_eq_self_of_mem h.ht'S]

@[expose] def Psub (S : Sylow 2 G) (R : Subgroup G) : Subgroup G := R ⊔ Csub S R

theorem conj_P' : conjSub t' (Psub S R') = Psub S R := by
  unfold Psub
  rw [conjSub_sup', h.ht'R', h.conj_C']

theorem P_le_N : Psub S R ≤ Nsub S R := sup_le h.R_le_N h.C_le_N

theorem P'_le_N : Psub S R' ≤ Nsub S R := sup_le h.R'_le_N h.C'_le_N

theorem swap_P {n : G} : t' * n * t'⁻¹ ∈ Psub S R ↔ n ∈ Psub S R' := by
  rw [← h.conj_P', mem_conjSub_iff]
  have : t'⁻¹ * (t' * n * t'⁻¹) * t' = n := by group
  rw [this]

end Hyp25T

end T7F2

end CFSG.ClassicalInvolution.Asc77

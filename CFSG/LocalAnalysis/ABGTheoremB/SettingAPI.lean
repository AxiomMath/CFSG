module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] (σ : Setting G)

theorem x_mem_S [Finite G] (hσ : σ.IsValid) : σ.x ∈ (σ.S : Subgroup G) :=
  hσ.x_mem_center.1

theorem mem_N_iff (g : G) : g ∈ σ.N ↔ g * σ.x = σ.x * g := by
  rw [N, Subgroup.mem_centralizer_singleton_iff]

theorem x_mem_N : σ.x ∈ σ.N :=
  (σ.mem_N_iff σ.x).mpr rfl

theorem S_le_N [Finite G] (hσ : σ.IsValid) : (σ.S : Subgroup G) ≤ σ.N := by
  intro g hg
  rw [mem_N_iff]
  exact (Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) g hg

theorem x₂_mem_N [Finite G] (hσ : σ.IsValid) : σ.x₂ ∈ σ.N := by
  rw [mem_N_iff]
  exact hσ.commute.symm

theorem x_mem_T : σ.x ∈ σ.T :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem x₂_mem_T : σ.x₂ ∈ σ.T :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem T_le_S [Finite G] (hσ : σ.IsValid) : σ.T ≤ (σ.S : Subgroup G) := by
  rw [T, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact σ.x_mem_S hσ
  · exact hσ.x₂_mem

theorem T_le_N [Finite G] (hσ : σ.IsValid) : σ.T ≤ σ.N :=
  (σ.T_le_S hσ).trans (σ.S_le_N hσ)

theorem T_le_D [Finite G] (hσ : σ.IsValid) : σ.T ≤ σ.D :=
  le_inf (σ.T_le_S hσ) Subgroup.le_normalizer

theorem D_le_S : σ.D ≤ (σ.S : Subgroup G) :=
  inf_le_left

theorem D_le_N [Finite G] (hσ : σ.IsValid) : σ.D ≤ σ.N :=
  σ.D_le_S.trans (σ.S_le_N hσ)

theorem C_le_N : σ.C ≤ σ.N := by
  intro g hg
  rw [mem_N_iff]
  exact (Subgroup.mem_centralizer_iff.mp hg σ.x σ.x_mem_T).symm

theorem T_le_C [Finite G] (hσ : σ.IsValid) : σ.T ≤ σ.C := by
  have hcomm : ∀ a ∈ ({σ.x, σ.x₂} : Set G), ∀ b ∈ ({σ.x, σ.x₂} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hσ.commute
    · exact hσ.commute.symm
    · rfl
  intro g hg
  rw [C, T, Subgroup.mem_centralizer_iff]
  intro h hh
  have hcl := Subgroup.closure_le_centralizer_centralizer ({σ.x, σ.x₂} : Set G)
  have hab : Subgroup.closure ({σ.x, σ.x₂} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({σ.x, σ.x₂} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ Subgroup.centralizer (Subgroup.centralizer ({σ.x, σ.x₂} : Set G) : Set G) :=
      hcl hb
    rw [Subgroup.mem_centralizer_iff] at hb'
    have ha' : a ∈ Subgroup.centralizer ({σ.x, σ.x₂} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (hcomm a ha c hc).symm
    exact (hb' a ha').symm
  exact (Subgroup.mem_centralizer_iff.mp (hab hh) g hg).symm

theorem ON_le_N : σ.ON ≤ σ.N :=
  oddCoreIn_le σ.N

theorem N_le_normalizer_ON : σ.N ≤ Subgroup.normalizer (σ.ON : Set G) :=
  le_normalizer_oddCoreIn σ.N

theorem odd_card_ON [Finite G] : Odd (Nat.card σ.ON) :=
  odd_card_oddCoreIn σ.N

end Setting

end CFSG.ABGTheoremB

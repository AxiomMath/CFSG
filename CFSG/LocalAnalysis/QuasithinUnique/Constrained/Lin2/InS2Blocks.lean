module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep8

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem S_le_normalizer_conjJoin' (S L : Subgroup G) :
    S ≤ Subgroup.normalizer (conjJoin S L : Set G) := fun _ hs => C56.S_le_normalizer_conjJoin L hs

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem pCore_L : pCoreOf 2 L = blockU L :=
  le_antisymm B.su.blockQ_le_blockU (blockU_le_pCoreOf L)

theorem pCore_L₂ : pCoreOf 2 (conjR L t) = blockU (conjR L t) := by
  rw [conjR_pCoreOf, B.pCore_L, DoubleA3.blockU_conjR]

theorem centerOf_L : centerOf L = blockZ L := (blockZ_eq_centerOf B.hL.2.1 B.pCore_L).symm

theorem centerOf_L₂ : centerOf (conjR L t) = blockZ (conjR L t) :=
  (blockZ_eq_centerOf B.hL₂.2.1 B.pCore_L₂).symm

theorem L_inf_L₂ : L ⊓ conjR L t = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h1 : g ∈ centerOf L :=
    ⟨hg.1, Subgroup.mem_centralizer_iff.2 fun a ha => B.comm_elem a ha g hg.2⟩
  have h2 : g ∈ centerOf (conjR L t) :=
    ⟨hg.2, Subgroup.mem_centralizer_iff.2 fun b hb => (B.comm_elem g hg.1 b hb).symm⟩
  rw [B.centerOf_L] at h1
  rw [B.centerOf_L₂] at h2
  have h3 : g ∈ blockU L ⊓ conjR (blockU L) t :=
    ⟨blockZ_le_blockU L h1, by rw [← DoubleA3.blockU_conjR]; exact blockZ_le_blockU _ h2⟩
  have := B.su.U₁_inf_U₂
  have h4 : g ∈ blockU L ⊓ conjSubgroup (blockU L) t := h3
  rw [this] at h4
  exact h4

theorem L_le_normalizer_L₂ : L ≤ Subgroup.normalizer ((conjR L t : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb a ha).symm

theorem L₂_le_normalizer_L : conjR L t ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_commute fun a ha b hb => B.comm_elem a ha b hb

theorem R_le_normalizer_L : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := by
  have h := B.dbl.baum_le_normalizer
  rwa [← B.su.thompsonJ_eq] at h

theorem conjR_R : conjR (thompsonJ S) t = thompsonJ S := thompsonJ_normalized (Subgroup.le_normalizer B.ht)

theorem R_le_normalizer_L₂ : thompsonJ S ≤ Subgroup.normalizer ((conjR L t : Subgroup G) : Set G) := by
  intro r hr
  have h1 : conjR (thompsonJ S) t ≤ conjR (Subgroup.normalizer (L : Set G)) t :=
    conjR_mono B.R_le_normalizer_L t
  rw [B.conjR_R, ← conjR_normalizer] at h1
  exact h1 hr

theorem isSylowTwoOf_R : IsSylowTwoOf (thompsonJ S) (L ⊔ thompsonJ S) := by
  have h := B.dbl.isSylowTwoOf_baum
  rwa [← B.su.thompsonJ_eq] at h

theorem isSylowTwoOf_R₁ : IsSylowTwoOf (thompsonJ S ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal B.isSylowTwoOf_R le_sup_left
    (sup_le Subgroup.le_normalizer B.R_le_normalizer_L)

theorem isSylowTwoOf_R₂ : IsSylowTwoOf (thompsonJ S ⊓ conjR L t) (conjR L t) := by
  have h := isSylowTwoOf_conjR B.isSylowTwoOf_R₁ t
  rwa [conjR_inf, B.conjR_R] at h

end S2Base

end CFSG.QuasithinUnique.Lin2

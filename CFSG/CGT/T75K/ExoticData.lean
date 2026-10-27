module

public import CFSG.CGT.T75K.ExoticLin
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75K

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G]

structure LinData (T H : Subgroup G) (n m : ℕ) where
  hTH : T ≤ H
  hHN : H ≤ Subgroup.normalizer (T : Set G)
  ρ : ↥H →* SL(n, GaloisField 2 m)
  surj : Function.Surjective ρ
  ker_iff : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ T
  φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m)
  compat : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
    φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
      Multiplicative.ofAdd (sv (ρ h) (Multiplicative.toAdd (φ t)))

theorem NaturalSL.toLinData {T H : Subgroup G} {n m : ℕ} (hTH : T ≤ H)
    (hHN : H ≤ Subgroup.normalizer (T : Set G)) (hnat : NaturalSL T H n m) :
    Nonempty (LinData T H n m) := by
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  refine ⟨⟨hTH, hHN, e.toMonoidHom.comp (QuotientGroup.mk' (T.subgroupOf H)), ?_, ?_, φ, ?_⟩⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro h
    show e (QuotientGroup.mk h) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro h t hmem
    exact hcompat h t hmem

namespace LinData

variable {T H : Subgroup G} {n m : ℕ} (D : LinData T H n m)

@[expose] noncomputable def mat (g : G) : SL(n, GaloisField 2 m) :=
  open Classical in if hg : g ∈ H then D.ρ ⟨g, hg⟩ else 1

@[expose] noncomputable def vec (t : G) : Fin n → GaloisField 2 m :=
  open Classical in if ht : t ∈ T then Multiplicative.toAdd (D.φ ⟨t, ht⟩) else 0

variable {D}

theorem mat_of_mem {g : G} (hg : g ∈ H) : D.mat g = D.ρ ⟨g, hg⟩ := by
  simp [mat, hg]

theorem vec_of_mem {t : G} (ht : t ∈ T) : D.vec t = Multiplicative.toAdd (D.φ ⟨t, ht⟩) := by
  simp [vec, ht]

theorem mat_mul {g g' : G} (hg : g ∈ H) (hg' : g' ∈ H) : D.mat (g * g') = D.mat g * D.mat g' := by
  rw [mat_of_mem (H.mul_mem hg hg'), mat_of_mem hg, mat_of_mem hg']
  exact D.ρ.map_mul ⟨g, hg⟩ ⟨g', hg'⟩

theorem mat_one : D.mat 1 = 1 := by
  rw [mat_of_mem H.one_mem]
  exact D.ρ.map_one

theorem mat_inv {g : G} (hg : g ∈ H) : D.mat g⁻¹ = (D.mat g)⁻¹ := by
  rw [mat_of_mem (H.inv_mem hg), mat_of_mem hg]
  exact D.ρ.map_inv ⟨g, hg⟩

theorem mat_eq_one_iff {g : G} (hg : g ∈ H) : D.mat g = 1 ↔ g ∈ T := by
  rw [mat_of_mem hg]
  exact D.ker_iff ⟨g, hg⟩

theorem mat_of_mem_T {t : G} (ht : t ∈ T) : D.mat t = 1 :=
  (mat_eq_one_iff (D.hTH ht)).2 ht

theorem exists_mat (s : SL(n, GaloisField 2 m)) : ∃ g ∈ H, D.mat g = s := by
  obtain ⟨h, rfl⟩ := D.surj s
  exact ⟨h, h.2, mat_of_mem h.2⟩

theorem vec_mul {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) : D.vec (t * t') = D.vec t + D.vec t' := by
  rw [vec_of_mem (T.mul_mem ht ht'), vec_of_mem ht, vec_of_mem ht']
  exact congrArg Multiplicative.toAdd (D.φ.map_mul ⟨t, ht⟩ ⟨t', ht'⟩)

theorem vec_one : D.vec 1 = 0 := by
  rw [vec_of_mem T.one_mem]
  exact congrArg Multiplicative.toAdd (D.φ.map_one)

theorem vec_inv {t : G} (ht : t ∈ T) : D.vec t⁻¹ = - D.vec t := by
  rw [vec_of_mem (T.inv_mem ht), vec_of_mem ht]
  exact congrArg Multiplicative.toAdd (D.φ.map_inv ⟨t, ht⟩)

theorem vec_inj {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (h : D.vec t = D.vec t') : t = t' := by
  rw [vec_of_mem ht, vec_of_mem ht'] at h
  have := D.φ.injective (Multiplicative.toAdd.injective h)
  exact congrArg Subtype.val this

theorem exists_vec (w : Fin n → GaloisField 2 m) : ∃ t ∈ T, D.vec t = w := by
  obtain ⟨t, ht⟩ := D.φ.surjective (Multiplicative.ofAdd w)
  refine ⟨t, t.2, ?_⟩
  rw [vec_of_mem t.2]
  exact congrArg Multiplicative.toAdd ht

theorem vec_conj {g t : G} (hg : g ∈ H) (ht : t ∈ T) :
    g * t * g⁻¹ ∈ T ∧ D.vec (g * t * g⁻¹) = sv (D.mat g) (D.vec t) := by
  have hmem : g * t * g⁻¹ ∈ T := conj_mem_of_mem_normalizer (D.hHN hg) ht
  refine ⟨hmem, ?_⟩
  have h := D.compat ⟨g, hg⟩ ⟨t, ht⟩ hmem
  rw [vec_of_mem hmem, vec_of_mem ht, mat_of_mem hg]
  exact congrArg Multiplicative.toAdd h

end LinData

end CFSG.CGT.T75K

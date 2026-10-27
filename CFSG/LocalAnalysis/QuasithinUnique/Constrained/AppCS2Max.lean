module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cent2

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem x_sq_mem : x * x ∈ S := by
  have h := inv_mul_mem_of_relIndex_two X.h2 (x := x⁻¹) (y := x) ((X.M₀).inv_mem X.hxM)
    (fun h => X.hxS (by simpa using S.inv_mem h)) X.hxM X.hxS
  simpa using h

theorem M₀_le_normalizer {Y : Subgroup G} (hS : ∀ s ∈ S, s ∈ normalizer (Y : Set G))
    (hx : x ∈ normalizer (Y : Set G)) : X.M₀ ≤ normalizer (Y : Set G) := by
  intro m hm
  by_cases hmS : m ∈ S
  · exact hS m hmS
  · have hs : x⁻¹ * m ∈ S := inv_mul_mem_of_relIndex_two X.h2 X.hxM X.hxS hm hmS
    have e : m = x * (x⁻¹ * m) := by group
    rw [e]
    exact (normalizer (Y : Set G)).mul_mem hx (hS _ hs)

theorem baumD_inf_conj : baumD S L ⊓ conjR (baumD S L) x = ⊥ := by
  have hD := X.C.D
  rw [X.baumD_eq_blockD]
  have hCs : ∀ s ∈ S, conjR (blockD S L) s = blockD S L := fun s hs =>
    C5.conjSubgroup_eq_self (S_le_normalizer_blockD hs)
  have hCxs : ∀ s ∈ S, conjR (conjR (blockD S L) x) s = conjR (blockD S L) x := by
    intro s hs
    have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx s).1 hs
    rw [Dbl.conjR_conjR]
    have e : x * s = (x * s * x⁻¹) * x := by group
    rw [e, ← Dbl.conjR_conjR, hCs _ hxs]
  have hYs : ∀ s ∈ S, conjR (blockD S L ⊓ conjR (blockD S L) x) s =
      blockD S L ⊓ conjR (blockD S L) x := by
    intro s hs
    show conjSubgroup (blockD S L ⊓ conjR (blockD S L) x) s = _
    rw [C5.conjSubgroup_inf]
    exact congrArg₂ (· ⊓ ·) (hCs s hs) (hCxs s hs)
  have hYx : conjR (blockD S L ⊓ conjR (blockD S L) x) x =
      blockD S L ⊓ conjR (blockD S L) x := by
    show conjSubgroup (blockD S L ⊓ conjR (blockD S L) x) x = _
    rw [C5.conjSubgroup_inf]
    have h1 : conjSubgroup (conjR (blockD S L) x) x = blockD S L := by
      show conjR (conjR (blockD S L) x) x = blockD S L
      rw [Dbl.conjR_conjR]
      exact hCs _ X.x_sq_mem
    rw [h1]
    exact inf_comm _ _
  by_contra hne
  have hSM' : S ≠ X.M₀ := fun h => X.hxS (h ▸ X.hxM)
  have hYS : blockD S L ⊓ conjR (blockD S L) x ≤ S := inf_le_left.trans inf_le_left
  refine C56.noCommonNormal hD.hcs X.hSM X.hMT hSM' _ hYS hne ?_ ?_
  · intro h hh
    rw [hD.hcs.eq_join] at hh
    refine (sup_le (fun k hk => ?_) (fun s hs => ?_) : conjJoin S L ⊔ S ≤
      normalizer ((blockD S L ⊓ conjR (blockD S L) x : Subgroup G) : Set G)) hh
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 hy.1.2 k hk).symm)
    · exact Lin2.conjR_eq_self_iff.1 (hYs s hs)
  · exact X.M₀_le_normalizer (fun s hs => Lin2.conjR_eq_self_iff.1 (hYs s hs))
      (Lin2.conjR_eq_self_iff.1 hYx)

theorem pCoreOf_isMax : IsMaxElemAbelian S (pCoreOf 2 H) := by
  have hD := X.C.D
  refine ⟨hD.Q_le_S, X.pCoreOf_isElemAbelian, fun B' hB'S hB'e => ?_⟩
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian S
  have h1 : Nat.card B' ≤ Nat.card A₀ := hA₀.2.2 B' hB'S hB'e
  have hA₀J : A₀ ≤ thompsonJ S := GammaExtra.le_thompsonJ hA₀
  obtain ⟨-, h2, h3, -⟩ := hD.aU_spec X.C.P.toPiData hA₀.2.1 (hA₀J.trans hD.thompsonJ_le_s2SI)
  exact h1.trans (h2.trans (Subgroup.card_le_of_le h3))

theorem thompsonJ_eq_baum : thompsonJ S = baum S := by
  have hD := X.C.D
  refine le_antisymm (C5.thompsonJ_le_baum' S) ?_
  rw [X.baum_eq, ← X.pCoreOf_eq]
  refine sup_le (GammaExtra.le_thompsonJ X.pCoreOf_isMax) ?_
  have hPx : conjR (pCoreOf 2 H) x ≤ thompsonJ S :=
    GammaExtra.le_thompsonJ (C56.isMaxElemAbelian_conjSubgroup X.pCoreOf_isMax X.hx)
  have hU0P : blockU0 S L ≤ pCoreOf 2 H := by rw [hD.blockU0_eq]; exact hD.U0_le_Q
  exact (C5.conjSubgroup_mono hU0P x).trans hPx

end Two

end CFSG.QuasithinUnique.AppCS2

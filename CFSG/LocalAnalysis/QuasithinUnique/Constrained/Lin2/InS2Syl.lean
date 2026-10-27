module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Blocks

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem baum_eq : baum S = thompsonJ S := B.su.thompsonJ_eq.symm

theorem baum_le_sup_inf :
    baum S ≤ (baum S ⊓ L) ⊔ (baum S ⊓ Subgroup.centralizer (blockU L : Set G)) := by
  have hB2 : IsPGroup 2 (baum S) := B.cs.sylow.isPGroup.to_le inf_le_left
  have hQX : baum S ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
    C56.baum_inf_centralizer_eq B.hL hB2 B.dbl.baum_le_normalizer B.dbl.isSylowTwoOf_baum
  have := B.dbl.baumann_Lin2_R1.2
  rwa [B.dbl.baum_R1_eq, ← hQX] at this

theorem R_eq_sup₁ : thompsonJ S = (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ Subgroup.centralizer (L : Set G)) := by
  rw [← B.baum_eq]
  have hkf := B.su.kf₁
  have hU1 : blockU L ≤ baum S ⊓ L := le_inf hkf.U_le_B (blockU_le L)
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  refine B.baum_le_sup_inf.trans (sup_le le_sup_left ?_)
  rw [hkf.Q_eq]
  refine sup_le (hU1.trans le_sup_left) ?_
  exact le_sup_of_le_right (inf_le_inf_right _ inf_le_left)

theorem R_eq_sup₂ : thompsonJ S =
    (thompsonJ S ⊓ conjR L t) ⊔ (thompsonJ S ⊓ Subgroup.centralizer ((conjR L t : Subgroup G) : Set G)) := by
  have h := congrArg (fun X => conjR X t) B.R_eq_sup₁
  simp only [conjR_sup, conjR_inf, B.conjR_R, ← conjR_centralizer] at h
  exact h

theorem R_eq_sup : thompsonJ S = ((thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t)) ⊔
    (thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G)) := by
  have hE₁ : thompsonJ S ⊓ Subgroup.centralizer (L : Set G) ≤
      ((thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t)) ⊔
        (thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G)) := by
    intro e he
    have heR : e ∈ (thompsonJ S ⊓ conjR L t) ⊔
        (thompsonJ S ⊓ Subgroup.centralizer ((conjR L t : Subgroup G) : Set G)) :=
      B.R_eq_sup₂ ▸ he.1
    have hN : (thompsonJ S ⊓ Subgroup.centralizer ((conjR L t : Subgroup G) : Set G)) ≤
        Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
      le_normalizer_of_commute fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a ha.2
    obtain ⟨k, hk, e₂, he₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 heR
    have hkc : ∀ a ∈ L, a * k = k * a := fun a ha => B.comm_elem a ha k hk.2
    have he₂L : ∀ a ∈ L, a * e₂ = e₂ * a := by
      intro a ha
      have h1 := Subgroup.mem_centralizer_iff.1 he.2 a ha
      have h2 := hkc a ha
      apply mul_left_cancel (a := k)
      calc k * (a * e₂) = (k * a) * e₂ := by rw [mul_assoc]
        _ = (a * k) * e₂ := by rw [h2]
        _ = a * (k * e₂) := by rw [mul_assoc]
        _ = (k * e₂) * a := h1
        _ = k * (e₂ * a) := by rw [mul_assoc]
    have he₂C : e₂ ∈ Subgroup.centralizer (conjJoin S L : Set G) := by
      rw [B.hjoin]
      exact C56.mem_centralizer_sup (fun a ha => he₂L a ha)
        (fun b hb => (Subgroup.mem_centralizer_iff.1 he₂.2 b hb))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hk))
      (Subgroup.mem_sup_right ⟨he₂.1, he₂C⟩)
  refine le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  calc thompsonJ S = (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ Subgroup.centralizer (L : Set G)) :=
        B.R_eq_sup₁
    _ ≤ _ := sup_le (le_sup_of_le_left le_sup_left) hE₁

theorem isSylowTwoOf_R₁R₂ :
    IsSylowTwoOf ((thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t)) (conjJoin S L) := by
  rw [B.hjoin]
  exact isSylowTwoOf_sup B.L_le_normalizer_L₂ B.L_inf_L₂
    (le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb.2 a ha.2).symm)
    B.isSylowTwoOf_R₁ B.isSylowTwoOf_R₂

theorem isSylowTwoOf_S_inf_L₀ : IsSylowTwoOf (S ⊓ conjJoin S L) (conjJoin S L) :=
  A4.isSylowTwoOf_inf_normal B.sylow B.L₀_le_H (by
    rw [B.H_eq]
    exact sup_le Subgroup.le_normalizer (S_le_normalizer_conjJoin' S L))

theorem S_inf_L₀_eq : S ⊓ conjJoin S L = (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t) := by
  have hle : (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t) ≤ S ⊓ conjJoin S L := by
    refine sup_le (le_inf ((inf_le_left.trans (thompsonJ_le_self S)))
      (inf_le_right.trans (B.hjoin ▸ le_sup_left))) (le_inf (inf_le_left.trans (thompsonJ_le_self S))
      (inf_le_right.trans (B.hjoin ▸ le_sup_right)))
  exact B.isSylowTwoOf_R₁R₂.eq_of_le hle inf_le_right (B.cs.sylow.isPGroup.to_le inf_le_left)

theorem R_eq_P_sup_C : thompsonJ S = (S ⊓ conjJoin S L) ⊔
    (thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G)) := by
  rw [B.S_inf_L₀_eq]
  exact B.R_eq_sup

theorem D_le_L₀ : D ≤ conjJoin S L := B.cfg.hall.1.trans inf_le_left

theorem D_le_normalizer_P : D ≤ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) := by
  have := B.cfg.norm
  rwa [inf_comm] at this

theorem D_comm_C {d c : G} (hd : d ∈ D) (hc : c ∈ Subgroup.centralizer (conjJoin S L : Set G)) :
    d * c = c * d := Subgroup.mem_centralizer_iff.1 hc d (B.D_le_L₀ hd)

theorem D_le_normalizer_R : D ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  intro d hd
  have hP := conjR_eq_of_mem_normalizer (B.D_le_normalizer_P hd)
  have hDC : D ≤ Subgroup.normalizer
      ((thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha b hb => (B.D_comm_C hb ha.2).symm
  have hC := conjR_eq_of_mem_normalizer (hDC hd)
  rw [← conjR_eq_self_iff]
  have h1 : conjR (thompsonJ S) d = conjR ((S ⊓ conjJoin S L) ⊔
      (thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G))) d := by
    rw [← B.R_eq_P_sup_C]
  rw [h1, conjR_sup, hP, hC, ← B.R_eq_P_sup_C]

end S2Base

end CFSG.QuasithinUnique.Lin2

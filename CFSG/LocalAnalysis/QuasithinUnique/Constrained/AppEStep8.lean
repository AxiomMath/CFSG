module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep7

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

namespace Dbl

variable (D : Dbl T M H S L n t)
include D

theorem blockU0_eq : blockU0 S L = blockU L ⊔ conjSubgroup (blockU L) t := by
  refine le_antisymm (iSup_le fun s => ?_)
    (sup_le (C56.le_conjJoin _ (one_mem _)) (conjR_le_conjJoin' D.ht))
  have e : (blockU L).map (MulAut.conj (s : G)).toMonoidHom = conjSubgroup (blockU L) (s : G)⁻¹ := by
    simp [conjSubgroup, inv_inv]
  rw [e]
  rcases D.U_cases₂ (S.inv_mem s.2) with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact le_sup_left
  · rw [h1]; exact le_sup_right

theorem pCoreOf_K_le : pCoreOf 2 (conjJoin S L) ≤ blockQ L ⊔ blockQ (conjR L t) := by
  have hNn : conjJoin S L ≤ normalizer ((pCoreOf 2 (conjJoin S L) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hN2 : IsPGroup 2 (pCoreOf 2 (conjJoin S L)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hNK : pCoreOf 2 (conjJoin S L) ≤ conjJoin S L :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
  have hLK : L ≤ conjJoin S L := L_le_K (S := S) (L := L)
  have hL₂K : conjR L t ≤ conjJoin S L := D.L₂_le_K
  have hNL : pCoreOf 2 (conjJoin S L) ⊓ L ≤ blockQ L :=
    C1.le_pCoreOf_of_normalized inf_le_right
      (fun g hg => C5.mem_normalizer_inf (hNn (hLK hg)) (Subgroup.le_normalizer hg))
      (hN2.to_le inf_le_left)
  have hNL₂ : pCoreOf 2 (conjJoin S L) ⊓ conjR L t ≤ blockQ (conjR L t) :=
    C1.le_pCoreOf_of_normalized inf_le_right
      (fun g hg => C5.mem_normalizer_inf (hNn (hL₂K hg)) (Subgroup.le_normalizer hg))
      (hN2.to_le inf_le_left)
  intro y hy
  have hyK : y ∈ conjJoin S L := hNK hy
  have hLN : L ≤ normalizer ((conjR L t : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun u hu a ha => D.comm_elem u hu a ha
  have hyK' : y ∈ ((L ⊔ conjR L t : Subgroup G) : Set G) := by
    rw [← D.hjoin]; exact hyK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L (conjR L t) hLN] at hyK'
  obtain ⟨a, ha, b, hb, hab⟩ := hyK'
  have hab' : a * b = y := hab
  have haQ : a ∈ blockQ L := by
    refine mem_blockQ_of_comm_lin2 D.hn D.hlin ha fun z hz => ?_
    have hbz : b * z = z * b := (D.comm_elem z hz b hb).symm
    have e : y * z * y⁻¹ * z⁻¹ = a * z * a⁻¹ * z⁻¹ := by
      rw [← hab']
      calc a * b * z * (a * b)⁻¹ * z⁻¹ = a * (b * z) * b⁻¹ * a⁻¹ * z⁻¹ := by group
        _ = a * (z * b) * b⁻¹ * a⁻¹ * z⁻¹ := by rw [hbz]
        _ = a * z * a⁻¹ * z⁻¹ := by group
    have hmem : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (conjJoin S L) := by
      have h3 : z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (conjJoin S L) :=
        (Subgroup.mem_normalizer_iff.1 (hNn (hLK hz)) y⁻¹).1 ((pCoreOf 2 (conjJoin S L)).inv_mem hy)
      have : y * z * y⁻¹ * z⁻¹ = y * (z * y⁻¹ * z⁻¹) := by group
      rw [this]
      exact mul_mem hy h3
    have hmemL : a * z * a⁻¹ * z⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ha hz) (L.inv_mem ha)) (L.inv_mem hz)
    rw [e] at hmem
    exact hNL ⟨hmem, hmemL⟩
  have hbQ : b ∈ blockQ (conjR L t) := by
    refine mem_blockQ_of_comm_lin2 D.hn D.hlin₂ hb fun z hz => ?_
    have hay : a * (b * z * b⁻¹) = (b * z * b⁻¹) * a :=
      D.comm_elem a ha _ (mul_mem (mul_mem hb hz) (inv_mem hb))
    have e : y * z * y⁻¹ * z⁻¹ = b * z * b⁻¹ * z⁻¹ := by
      rw [← hab']
      calc a * b * z * (a * b)⁻¹ * z⁻¹ = a * (b * z * b⁻¹) * a⁻¹ * z⁻¹ := by group
        _ = (b * z * b⁻¹) * a * a⁻¹ * z⁻¹ := by rw [hay]
        _ = b * z * b⁻¹ * z⁻¹ := by group
    have hmem : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (conjJoin S L) := by
      have h3 : z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (conjJoin S L) :=
        (Subgroup.mem_normalizer_iff.1 (hNn (hL₂K hz)) y⁻¹).1
          ((pCoreOf 2 (conjJoin S L)).inv_mem hy)
      have : y * z * y⁻¹ * z⁻¹ = y * (z * y⁻¹ * z⁻¹) := by group
      rw [this]
      exact mul_mem hy h3
    have hmemL : b * z * b⁻¹ * z⁻¹ ∈ conjR L t :=
      (conjR L t).mul_mem ((conjR L t).mul_mem ((conjR L t).mul_mem hb hz)
        ((conjR L t).inv_mem hb)) ((conjR L t).inv_mem hz)
    rw [e] at hmem
    exact hNL₂ ⟨hmem, hmemL⟩
  rw [← hab']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haQ) (Subgroup.mem_sup_right hbQ)

end Dbl

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem blockQ_le_blockU : blockQ L ≤ blockU L := by
  have hOe := P.O_elemAb
  have hOB : pCoreOf 2 H ≤ baum S := P.O_le_baum
  have hOH : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hLH : L ≤ H := L_le_H1.trans P.D.H1_le_H
  have hLO : L ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := fun g hg => hOH (hLH hg)
  have hBS : baum S ≤ S := inf_le_left
  have hBO : baum S ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := fun g hg =>
    hOH (P.D.hcs.sylow.le (hBS hg))
  have hO2 : IsPGroup 2 (pCoreOf 2 H) :=
    P.D.hcs.sylow.isPGroup.to_le (C56.pCoreOf_le_S P.D.hcs)
  have hXuB : conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ≤ baum S := by
    rw [C5.conjSubgroup_sup]
    exact sup_le P.X_le_B P.Y_le_B
  have hLXB : L ⊔ pCoreOf 2 H ≤ L ⊔ baum S := sup_le le_sup_left (hOB.trans le_sup_right)
  have hBN : L ⊔ baum S ≤ normalizer ((L ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    refine sup_le (fun g hg => C1.mem_normalizer_sup (Subgroup.le_normalizer hg) (hLO hg))
      (fun g hg => C1.mem_normalizer_sup (P.D.baum_le_normalizer hg) (hBO hg))
  have hP : IsSylowTwoOf (baum S ⊓ (L ⊔ pCoreOf 2 H)) (L ⊔ pCoreOf 2 H) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal P.D.isSylowTwoOf_baum hLXB
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLXB).mpr hBN).isSubnormal
  obtain ⟨C, hCE, hCF, hCsupF⟩ := C5.exists_complement_elemAb2
    (E := conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ⊓ (L ⊔ pCoreOf 2 H))
    (F := conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ⊓ (L ⊔ pCoreOf 2 H) ⊓
      pCoreOf 2 H)
    ((P.elemAb_U.conjSubgroup x).mono inf_le_left) inf_le_left
  have hCP : C ≤ baum S ⊓ (L ⊔ pCoreOf 2 H) := fun c hc => ⟨hXuB (hCE hc).1, (hCE hc).2⟩
  have hCQ : C ⊓ pCoreOf 2 H = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcC, hcO⟩
    have : c ∈ C ⊓ (conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ⊓ (L ⊔ pCoreOf 2 H) ⊓
        pCoreOf 2 H) := ⟨hcC, hCE hcC, hcO⟩
    rw [hCF] at this
    exact this
  have hBeq : baum S = conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ⊔ pCoreOf 2 H := by
    rw [P.B_eq_sup, ← P.O_eq_DU, sup_comm]
  have hCsup : C ⊔ pCoreOf 2 H = baum S ⊓ (L ⊔ pCoreOf 2 H) := by
    refine le_antisymm (sup_le hCP (le_inf hOB le_sup_right)) fun g hg => ?_
    obtain ⟨hgB, hgX⟩ := hg
    rw [hBeq] at hgB
    obtain ⟨a, ha, q', hq', rfl⟩ := C5.mem_sup_of_le_normalizer (fun g hg => hBO (hXuB hg)) hgB
    have haX : a ∈ L ⊔ pCoreOf 2 H := by
      have := Subgroup.mul_mem _ hgX (Subgroup.inv_mem _ (Subgroup.mem_sup_right hq'))
      simpa using this
    have : a ∈ C ⊔ pCoreOf 2 H := by
      have h1 : a ∈ C ⊔ (conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ⊓
          (L ⊔ pCoreOf 2 H) ⊓ pCoreOf 2 H) := by
        rw [hCsupF]; exact ⟨ha, haX⟩
      exact sup_le_sup_left inf_le_right C h1
    exact Subgroup.mul_mem _ this (Subgroup.mem_sup_right hq')
  obtain ⟨X₀, -, hX₀inf, hX₀sup⟩ := C5.exists_complement_of_sylow_split
    (le_sup_right : pCoreOf 2 H ≤ L ⊔ pCoreOf 2 H) (sup_le hLO Subgroup.le_normalizer) hOe.1 hO2 hP
    hCP hCQ hCsup
  exact C5.blockQ_le_blockU_of_split P.D.hL hOe.1 hOe.2 hLO
    (fun q hq u hu => P.O_comm_U q hq u (Subgroup.mem_sup_left hu))
    (fun q hq l hl => C56.bb1 P.D.hcs q hq l hl)
    ((C56.blockQ_le_pCoreOf_conjJoin P.D.hcs).trans (C56.pCoreOf_conjJoin_le P.D.hcs))
    hX₀inf hX₀sup

theorem pCoreOf_conjJoin_eq : blockU0 S L = pCoreOf 2 (conjJoin S L) := by
  rw [P.D.blockU0_eq]
  have hU₁ : blockU L = blockQ L := le_antisymm (C1.blockU_le_blockQ P.D.hL) P.blockQ_le_blockU
  have hU₂ : conjSubgroup (blockU L) t = blockQ (conjR L t) := by
    rw [hU₁]; exact C5.conjSubgroup_pCoreOf 2 L t
  have hU₁K : blockU L ≤ pCoreOf 2 (conjJoin S L) :=
    (C1.blockU_le_blockQ P.D.hL).trans (C56.blockQ_le_pCoreOf_conjJoin P.D.hcs)
  refine le_antisymm (sup_le hU₁K ?_) ?_
  · have h := C5.conjSubgroup_mono hU₁K t
    rwa [C5.conjSubgroup_pCoreOf, C5.conjSubgroup_eq_self
      (C56.S_le_normalizer_conjJoin L P.D.ht)] at h
  · refine P.D.pCoreOf_K_le.trans ?_
    rw [hU₂, hU₁]

end Setup

end CFSG.QuasithinUnique.AppE

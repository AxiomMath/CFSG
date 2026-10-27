module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Defs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Spec
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Tab
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Emb

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
  Certificates.Seitz77CaseB45

theorem isSimpleGroup_of_lieModel_psl_three_four {K : Type} [Group K]
    (h : LieModel K .PSL 3 2 2) : IsSimpleGroup K :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ (h.statedClassicalModel (by decide))).2

theorem card_of_lieModel_psl_three_four {K : Type} [Group K] (h : LieModel K .PSL 3 2 2) :
    Nat.card K = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

section Comp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
  {G₁ G₂ S₀ W₁ W₂ : Subgroup G}

omit [Finite G] in
theorem datum_t_sq (d : Datum A) : d.t * d.t = 1 := by
  have h : d.t ^ 2 = 1 := by rw [← d.sector.t_order]; exact pow_orderOf_eq_one d.t
  rwa [sq] at h

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.compData (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) :
    CompData G₁ G₂ d.t :=
  ⟨datum_t_sq d, c.swap, c.comm, c.perfect, isSimpleGroup_of_lieModel_psl_three_four c.model⟩

end Comp

section Inner

variable {G : Type} [Group G]

theorem actQ_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    actQ H ⟨g, Subgroup.le_normalizer hg⟩ =
      MulAut.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥H) : ↥H ⧸ center ↥H) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [actQ_mk, MulAut.conj_apply]
    show QuotientGroup.mk (H.normalizerMonoidHom _ x) = _
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem actQ_of_centralizes (H : Subgroup G) {n : G} (hn : n ∈ normalizer (H : Set G))
    (h : ∀ x ∈ H, n * x = x * n) : actQ H ⟨n, hn⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [actQ_mk]
    show QuotientGroup.mk (H.normalizerMonoidHom _ x) = _
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := h x.1 x.2
    show n * x.1 * n⁻¹ = x.1
    rw [this]
    group

variable {Q : Type} [Group Q] (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q)

theorem psiT_mem_of_mem {L : Subgroup Q} (hL : ∀ k, Φ (MulAut.conj k) ∈ L) {g : G} (hg : g ∈ G₁) :
    psiT G₁ Φ g ∈ L := by
  rw [psiT_of_mem G₁ Φ (Subgroup.le_normalizer hg), actQ_of_mem G₁ hg]
  exact hL _

theorem psiT_eq_one_of_centralizes {g : G} (hn : g ∈ normalizer (G₁ : Set G))
    (h : ∀ x ∈ G₁, g * x = x * g) : psiT G₁ Φ g = 1 := by
  rw [psiT_of_mem G₁ Φ hn, actQ_of_centralizes G₁ hn h, map_one]

variable {G₁} {G₂ : Subgroup G} {t : G} [Finite G]

theorem theta_mem_ss_G₁ (cd : CompData G₁ G₂ t) {L : Subgroup Q}
    (hL : ∀ k, Φ (MulAut.conj k) ∈ L) {g : G} (hg : g ∈ G₁)
    (hgN : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    theta Φ cd ⟨g, hgN⟩ ∈ Wr.ss L := by
  have hg1 : g ∈ normalizer (G₁ : Set G) := Subgroup.le_normalizer hg
  rw [theta_apply, thetaFun_of_mem G₁ Φ t hg1, Wr.mem_ss]
  refine ⟨psiT_mem_of_mem G₁ Φ hL hg, ?_, rfl⟩
  have h2 : t⁻¹ * g * t ∈ G₂ := by
    refine (cd.swap _).2 ?_
    have e : t⁻¹ * (t⁻¹ * g * t) * t = g := by
      rw [cd.t_inv]
      calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
        _ = g := by rw [cd.t_sq]; group
    rw [e]
    exact hg
  have hn2 : t⁻¹ * g * t ∈ normalizer (G₁ : Set G) :=
    mem_normalizer_iff.2 fun x => cd.normalizes_G₁ h2
  rw [psiT_eq_one_of_centralizes G₁ Φ hn2 fun x hx => (cd.mul_comm_of_mem hx h2).symm]
  exact L.one_mem

theorem theta_mem_ss_G₂ (cd : CompData G₁ G₂ t) {L : Subgroup Q}
    (hL : ∀ k, Φ (MulAut.conj k) ∈ L) {g : G} (hg : g ∈ G₂)
    (hgN : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    theta Φ cd ⟨g, hgN⟩ ∈ Wr.ss L := by
  have hg1 : g ∈ normalizer (G₁ : Set G) := mem_normalizer_iff.2 fun x => cd.normalizes_G₁ hg
  rw [theta_apply, thetaFun_of_mem G₁ Φ t hg1, Wr.mem_ss]
  have h0 : psiT G₁ Φ g = 1 :=
    psiT_eq_one_of_centralizes G₁ Φ hg1 fun x hx => (cd.mul_comm_of_mem hx hg).symm
  refine ⟨?_, psiT_mem_of_mem G₁ Φ hL ((cd.swap g).1 hg), rfl⟩
  rw [h0]
  exact L.one_mem

theorem theta_mem_ss (cd : CompData G₁ G₂ t) {L : Subgroup Q} (hL : ∀ k, Φ (MulAut.conj k) ∈ L)
    (n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))) (hn : (n : G) ∈ G₁ ⊔ G₂) :
    theta Φ cd n ∈ Wr.ss L := by
  have hsub : G₁ ⊔ G₂ ≤ ((Wr.ss L).comap (theta Φ cd)).map
      (normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)).subtype := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · have hgN : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) :=
        Subgroup.le_normalizer (Subgroup.mem_sup_left hg)
      exact ⟨⟨g, hgN⟩, theta_mem_ss_G₁ Φ cd hL hg hgN, rfl⟩
    · have hgN : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) :=
        Subgroup.le_normalizer (Subgroup.mem_sup_right hg)
      exact ⟨⟨g, hgN⟩, theta_mem_ss_G₂ Φ cd hL hg hgN, rfl⟩
  obtain ⟨m, hm, hmn⟩ := hsub hn
  have : m = n := Subtype.ext hmn
  subst this
  exact hm

end Inner

section Emb

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
  {G₁ G₂ S₀ W₁ W₂ : Subgroup G}

theorem _root_.CFSG.OddStandard.Seitz77.CaseBG0.exists_emb
    (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) (hchk : fbSixCheck = true) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (MD : ModelData Q),
      Nonempty (EmbSpec c.compData MD) := by
  obtain ⟨e⟩ := L34.equiv_of_lieModel c.model
  obtain ⟨M, hP, hA⟩ := L34.autModel e
  have hK : Nat.card (↥G₁ ⧸ center ↥G₁) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  simp only [fbSixCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨hT, h7⟩, h6⟩ := hchk
  obtain ⟨MD, hMD⟩ := exists_modelData M (tablesFacts_of_ok hT) hA hP hK h7 h6
  refine ⟨↥M.A, inferInstance, inferInstance, MD, ⟨?_⟩⟩
  let Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* ↥M.A := M.Φ.toMonoidHom
  have hL : ∀ k, Φ (MulAut.conj k) ∈ MD.Lm := by
    intro k
    rw [hMD]
    exact ⟨MulAut.conj k, ⟨k, rfl⟩, rfl⟩
  exact { θ := theta Φ c.compData
          ker := theta_eq_one Φ c.compData M.Φ.injective
          e_iff := theta_e Φ c.compData
          swap := theta_t Φ c.compData
          inner := theta_mem_ss Φ c.compData hL }

end Emb

end CFSG.OddStandard.Seitz77.CaseB45

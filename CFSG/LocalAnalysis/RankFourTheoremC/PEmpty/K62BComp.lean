module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkSylow
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.CenterCyclic
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Layer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

@[expose] def Fixed (P : Subgroup Y) (C : ComponentIndex Y) : Prop :=
  ∀ g ∈ P, g ∈ normalizer (C.1 : Set Y)

theorem comp_isSubnormal (C : ComponentIndex Y) : C.1.IsSubnormal := C.2.2

theorem comp_isQuasisimple (C : ComponentIndex Y) : CFSG.Open.IsQuasisimple ↥C.1 :=
  ((CFSG.isComponent_iff_open C.1).1 C.2).2.2

theorem Cfg.isSylowOf_inf_comp (h : Cfg p P x z) (C : ComponentIndex Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ C.1) C.1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact isSylowOf_inf_of_isSubnormal' h.sylow (comp_isSubnormal C)

theorem Cfg.dvd_card_comp (h : Cfg p P x z) (C : ComponentIndex Y) : p ∣ Nat.card C.1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.dvd_card_comp h.core C

theorem Cfg.inf_comp_ne_bot (h : Cfg p P x z) (C : ComponentIndex Y) : P ⊓ C.1 ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro hbot
  have hcard := (h.isSylowOf_inf_comp C).card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hfac : 1 ≤ (Nat.card C.1).factorization p :=
    (h.prime.dvd_iff_one_le_factorization Nat.card_pos.ne').1 (h.dvd_card_comp C)
  have h1 : 1 < p ^ (Nat.card C.1).factorization p := Nat.one_lt_pow (by omega) h.prime.one_lt
  omega

theorem Cfg.z_mem_comp_of_fixed (h : Cfg p P x z) {C : ComponentIndex Y} (hC : Fixed P C) :
    z ∈ C.1 := by
  have hN : ∀ g ∈ P, ∀ n ∈ P ⊓ C.1, g * n * g⁻¹ ∈ P ⊓ C.1 := fun g hg n hn =>
    ⟨P.mul_mem (P.mul_mem hg hn.1) (P.inv_mem hg),
      (mem_normalizer_iff.mp (hC g hg) n).mp hn.2⟩
  exact (h.z_mem_of_normal inf_le_left hN (h.inf_comp_ne_bot C)).2

theorem comp_commute {C C' : ComponentIndex Y} (hne : C ≠ C') :
    ∀ a ∈ C.1, ∀ b ∈ C'.1, a * b = b * a := fun a ha b hb =>
  componentIndex_commute hne a b ha hb

theorem isCyclic_subgroupOf_iff {A C : Subgroup Y} (hAC : A ≤ C) :
    IsCyclic ↥(A.subgroupOf C) ↔ IsCyclic ↥A :=
  ⟨fun h => isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAC).surjective,
   fun h => isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAC).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAC).symm.surjective⟩

theorem Cfg.not_isCyclic_inf_comp (h : Cfg p P x z) (h610 : GL83.I_6_10_1)
    (C : ComponentIndex Y) (hdvd : p ∣ Nat.card (center C.1)) : ¬ IsCyclic ↥(P ⊓ C.1) := by
  intro hcyc
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf_comp C
  have hodd : p ≠ 2 := by have := h.five_le; omega
  have hnc := (h610 C.1 (comp_isQuasisimple C) p h.prime hodd hdvd Q).1
  apply hnc
  have hQc : IsCyclic ↥(Q : Subgroup C.1) := by
    have e : ↥(Q : Subgroup C.1) ≃* ↥((Q : Subgroup C.1).map C.1.subtype) :=
      (Q : Subgroup C.1).equivMapOfInjective C.1.subtype C.1.subtype_injective
    rw [hQ] at e
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩


theorem Cfg.zpowers_central (h : Cfg p P x z) {w g : Y} (hw : w ∈ zpowers z) (hg : g ∈ P) :
    g * w = w * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute g z from h.z_central g hg) n).eq

theorem Cfg.comm_mul_mem (h : Cfg p P x z) {e e' : Y} (he : e ∈ P)
    (he1 : x * e * x⁻¹ * e⁻¹ ∈ zpowers z) (he2 : x * e' * x⁻¹ * e'⁻¹ ∈ zpowers z) :
    x * (e * e') * x⁻¹ * (e * e')⁻¹ ∈ zpowers z := by
  have hc : e * (x * e' * x⁻¹ * e'⁻¹) = (x * e' * x⁻¹ * e'⁻¹) * e := h.zpowers_central he2 he
  have : x * (e * e') * x⁻¹ * (e * e')⁻¹ =
      (x * e * x⁻¹ * e⁻¹) * (x * e' * x⁻¹ * e'⁻¹) := by
    calc x * (e * e') * x⁻¹ * (e * e')⁻¹
        = (x * e * x⁻¹ * e⁻¹) * (e * (x * e' * x⁻¹ * e'⁻¹) * e⁻¹) := by group
      _ = (x * e * x⁻¹ * e⁻¹) * ((x * e' * x⁻¹ * e'⁻¹) * e * e⁻¹) := by rw [hc]
      _ = (x * e * x⁻¹ * e⁻¹) * (x * e' * x⁻¹ * e'⁻¹) := by group
  rw [this]
  exact (zpowers z).mul_mem he1 he2

theorem Cfg.comm_mem_sup (h : Cfg p P x z) {V V' : Subgroup Y} (hV : V ≤ P) (hV' : V' ≤ P)
    (h1 : ∀ e ∈ V, x * e * x⁻¹ * e⁻¹ ∈ zpowers z)
    (h2 : ∀ e ∈ V', x * e * x⁻¹ * e⁻¹ ∈ zpowers z) :
    ∀ e ∈ V ⊔ V', x * e * x⁻¹ * e⁻¹ ∈ zpowers z := by
  intro e he
  have hE : V ⊔ V' = ⨆ i : Bool, cond i V V' := sup_eq_iSup V V'
  have heP : ∀ e ∈ V ⊔ V', e ∈ P := fun e he => sup_le hV hV' he
  have he' := he
  rw [hE] at he'
  refine Subgroup.iSup_induction' (fun i : Bool => cond i V V')
    (C := fun e _ => x * e * x⁻¹ * e⁻¹ ∈ zpowers z) ?_ ?_ ?_ he'
  · intro i e he
    cases i
    · exact h2 e he
    · exact h1 e he
  · simpa using (zpowers z).one_mem
  · intro a b ha hb iha ihb
    exact h.comm_mul_mem (heP a (hE ▸ ha)) iha ihb

theorem Cfg.false_of_two_fixed (h : Cfg p P x z) (h64 : KFactCenterCyclicGeFive)
    (h610 : GL83.I_6_10_1) {C C' : ComponentIndex Y} (hne : C ≠ C') (hC : Fixed P C)
    (hC' : Fixed P C') : False := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hzC := h.z_mem_comp_of_fixed hC
  have hzC' := h.z_mem_comp_of_fixed hC'
  have hzZ : ∀ {D D' : ComponentIndex Y}, D ≠ D' → z ∈ D.1 → z ∈ D'.1 →
      p ∣ Nat.card (center D.1) := by
    intro D D' hDD' hzD hzD'
    have hcent : (⟨z, hzD⟩ : ↥D.1) ∈ center ↥D.1 := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact comp_commute hDD' c c.2 z hzD'
    have h1 : orderOf (⟨(⟨z, hzD⟩ : ↥D.1), hcent⟩ : ↥(center ↥D.1)) = p :=
      (Subgroup.orderOf_mk _ hcent).trans ((Subgroup.orderOf_mk z hzD).trans h.orderOf_z)
    exact h1 ▸ orderOf_dvd_natCard _
  have hplane : ∀ D : ComponentIndex Y, Fixed P D → p ∣ Nat.card (center D.1) →
      ∃ V : Subgroup Y, V ≤ P ⊓ D.1 ∧ (∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
        Nat.card V = p ^ 2 ∧ (∀ v ∈ V, v ^ p = 1) ∧ ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro D hD hdv
    have hnc := h.not_isCyclic_inf_comp h610 D hdv
    obtain ⟨V, hVR, hPV, hVc, hVp, hVab⟩ :=
      CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2 h.isPGroup inf_le_left
        (fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, hD g hg⟩) hnc
    exact ⟨V, hVR, fun g hg v hv => (mem_normalizer_iff.mp (hPV hg) v).mp hv, hVc, hVp, hVab⟩
  obtain ⟨V, hVR, hVn, hVc, hVp, hVab⟩ := hplane C hC (hzZ hne hzC hzC')
  obtain ⟨V', hVR', hVn', hVc', hVp', hVab'⟩ := hplane C' hC' (hzZ hne.symm hzC' hzC)
  have hVP : V ≤ P := hVR.trans inf_le_left
  have hVP' : V' ≤ P := hVR'.trans inf_le_left
  have hVe : IsElemAbelian p V := ⟨⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩, hVp⟩
  have hVe' : IsElemAbelian p V' := ⟨⟨⟨fun a b => Subtype.ext (hVab' a a.2 b b.2)⟩⟩, hVp'⟩
  have hVV' : ∀ a ∈ V, ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
    comp_commute hne a (hVR ha).2 b (hVR' hb).2
  have hEe := isElemAbelian_sup hVe hVe' hVV'
  have hcomm := h.comm_mem_sup hVP hVP'
    (fun e he => h.comm_mem_zpowers hVP hVn hVc x h.x_mem e he)
    (fun e he => h.comm_mem_zpowers hVP' hVn' hVc' x h.x_mem e he)
  have hcard := h.card_le_sq_of_comm (sup_le hVP hVP') hEe hcomm
  have hVeq : V = V ⊔ V' :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hVc]; exact hcard)
  have hVeq' : V' = V ⊔ V' :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hVc']; exact hcard)
  have hVV : V = V' := hVeq.trans hVeq'.symm
  have hVz : V.subgroupOf C.1 ≤ center ↥C.1 := by
    intro a ha
    have haV : (a : Y) ∈ V := ha
    have haC' : (a : Y) ∈ C'.1 := (hVR' (hVV ▸ haV)).2
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact comp_commute hne c c.2 a haC'
  obtain ⟨-, hsimple, a, b, hab⟩ := C.2.1
  have hcat : IsCatalogGroup (↥C.1 ⧸ center ↥C.1) :=
    h.catalog C.1 (center ↥C.1) inferInstance hsimple ⟨a, b, hab⟩
  have hVpg : IsPGroup p (V.subgroupOf C.1) := (h.isPGroup.to_le hVP).comap_subtype
  have hcyc := h64 C.1 (comp_isQuasisimple C) hcat p hp h.five_le (V.subgroupOf C.1) hVz hVpg
  exact CFSG.Goldschmidt.Sec82.not_isCyclic_of_card_sq hp hVc hVp
    ((isCyclic_subgroupOf_iff (hVR.trans inf_le_right)).1 hcyc)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

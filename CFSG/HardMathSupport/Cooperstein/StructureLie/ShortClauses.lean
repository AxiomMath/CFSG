module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeQuotient
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalCentre
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace TransvIrr

open Subgroup CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L V : Subgroup G} {s : G}

private theorem exists_rep_of_setting_act (h : Setting M L V s) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsn : s ∉ L ⊔ M ⊓ centralizer (V : Set G))
    (hN : ∀ T : Subgroup G, T ≤ M → M ≤ normalizer (T : Set G) →
      M ⊓ centralizer (V : Set G) ≤ T → ∀ x ∈ T,
        x ∉ L ⊔ M ⊓ centralizer (V : Set G) → L ≤ T) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (_ : Nontrivial W) (ρ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ P : Submodule (ZMod 2) W,
        (∀ m : ↥M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤) ∧
      IsF2Transvection (ρ ⟨s, h.mem⟩) ∧
      (∀ T : Subgroup ↥M, T.Normal → ρ.ker ≤ T → (⟨s, h.mem⟩ : ↥M) ∈ T → T = ⊤) ∧
      ⊤ ≤ L.subgroupOf M ⊔ Subgroup.zpowers (⟨s, h.mem⟩ : ↥M) ⊔ ρ.ker ∧
      L.subgroupOf M ≤ ⁅L.subgroupOf M, L.subgroupOf M⁆ ⊔ ρ.ker ∧
      ¬ L.subgroupOf M ≤ ρ.ker ∧
      ρ ⟨s, h.mem⟩ ∉ (L.subgroupOf M).map ρ ∧
      (∀ c : ↥M, (c : G) ∈ centralizer (V : Set G) → ρ c = 1) ∧
      (∀ m : ↥M, ρ m = 1 → ∀ u ∈ ⁅V, L⁆, ⁅u, (m : G)⁆ ∈ ⁅V, L⁆ ⊓ centralizer (L : Set G)) := by
  set U : Subgroup G := ⁅V, L⁆ with hUdef
  set Cl : Subgroup G := U ⊓ centralizer (L : Set G) with hCl
  have hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv =>
    h.comm u (h.U_le_V hu) v (h.U_le_V hv)
  have hU2 : ∀ u ∈ U, u * u = 1 := fun u hu => hV2 u (h.U_le_V hu)
  obtain ⟨W, _, _, _, cls, ρ, hadd, hsurj, hker, hact⟩ :=
    exists_quotientModule M U Cl h.normU h.normCl hUc hU2
  have hcls1 : cls 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact add_left_cancel (a := cls 1) (by rw [add_zero]; exact this.symm)
  have hclsinv : ∀ a, cls a⁻¹ = - cls a := fun a => by
    have := hadd a a⁻¹
    rw [mul_inv_cancel, hcls1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  let cu : ↥M → ↥U → ↥U := fun m u =>
    ⟨(m : G) * u * (m : G)⁻¹, conj_mem_of_le_normalizer h.normU m.2 u.2⟩
  have hρcu : ∀ m u, (ρ m : W →ₗ[ZMod 2] W) (cls u) = cls (cu m u) := fun m u =>
    hact m u (cu m u) rfl
  have hC : ∀ c : ↥M, (c : G) ∈ centralizer (V : Set G) → ρ c = 1 := by
    intro c hc
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨u, rfl⟩ := hsurj w
    have hcu : cu c u = u := Subtype.ext (by
      have := mem_centralizer_iff.mp hc u (h.U_le_V u.2)
      show (c : G) * u * (c : G)⁻¹ = u
      rw [← this]; group)
    rw [hρcu, hcu]
    rfl
  have hL1 : ¬ L.subgroupOf M ≤ ρ.ker := by
    intro hLk
    have hcomm : (⁅U, L⁆ : Subgroup G) ≤ Cl := by
      refine commutator_le.mpr fun u hu l hl => ?_
      have hρl : ρ ⟨l, h.le hl⟩ = 1 := hLk (mem_subgroupOf.mpr hl)
      have hv : (⁅u, l⁆ : G) = ((⟨u, hu⟩ * (cu ⟨l, h.le hl⟩ ⟨u, hu⟩)⁻¹ : ↥U) : G) := by
        show _ = u * ((l : G) * u * (l : G)⁻¹)⁻¹
        simp only [commutatorElement_def]; group
      have hmemU : (⁅u, l⁆ : G) ∈ U := by rw [hv]; exact (⟨u, hu⟩ * (cu ⟨l, h.le hl⟩ ⟨u, hu⟩)⁻¹ : ↥U).2
      have hz : cls ⟨⁅u, l⁆, hmemU⟩ = 0 := by
        have e : (⟨⁅u, l⁆, hmemU⟩ : ↥U) = ⟨u, hu⟩ * (cu ⟨l, h.le hl⟩ ⟨u, hu⟩)⁻¹ := Subtype.ext hv
        rw [e, hadd, hclsinv, ← hρcu, hρl]
        simp
      exact (hker _).mp hz
    exact absurd (h.comm_comm_ge.trans hcomm) (not_le_of_gt h.Cl_lt)
  set s' : ↥M := ⟨s, h.mem⟩ with hs'
  have hlift : ∀ (T : Subgroup ↥M) [T.Normal],
      (∀ c : ↥M, (c : G) ∈ centralizer (V : Set G) → c ∈ T) → ∀ x : ↥M, x ∈ T →
        (x : G) ∉ L ⊔ M ⊓ centralizer (V : Set G) → L.subgroupOf M ≤ T := by
    intro T _ hCT x hxT hxn
    have hTM : T.map M.subtype ≤ M := Subgroup.map_subtype_le T
    have hMT : M ≤ normalizer ((T.map M.subtype : Subgroup G) : Set G) := by
      apply le_normalizer_of_conj_mem
      rintro g hg _ ⟨k, hk, rfl⟩
      exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem ‹T.Normal› k hk _, rfl⟩
    have hCT' : M ⊓ centralizer (V : Set G) ≤ T.map M.subtype := by
      rintro c ⟨hcM, hcV⟩
      exact ⟨⟨c, hcM⟩, hCT ⟨c, hcM⟩ hcV, rfl⟩
    have hL := hN _ hTM hMT hCT' x ⟨x, hxT, rfl⟩ hxn
    intro l hl
    obtain ⟨k, hk, hkl⟩ := hL (show (l : G) ∈ L from hl)
    have : k = l := Subtype.ext hkl
    rwa [← this]
  have hM : ⊤ ≤ L.subgroupOf M ⊔ Subgroup.zpowers s' ⊔ ρ.ker := by
    intro m _
    have hm : (m : G) ∈ L ⊔ zpowers s ⊔ M ⊓ centralizer (V : Set G) := h.gen m.2
    have hLz : L ⊔ zpowers s ≤ M := sup_le h.le (zpowers_le.mpr h.mem)
    have hm' : m ∈ (L ⊔ zpowers s ⊔ M ⊓ centralizer (V : Set G)).subgroupOf M := hm
    rw [Subgroup.subgroupOf_sup hLz inf_le_left,
      Subgroup.subgroupOf_sup h.le (zpowers_le.mpr h.mem)] at hm'
    have hle : (L.subgroupOf M ⊔ (zpowers s).subgroupOf M) ⊔
        (M ⊓ centralizer (V : Set G)).subgroupOf M ≤ L.subgroupOf M ⊔ zpowers s' ⊔ ρ.ker := by
      refine sup_le_sup (sup_le_sup le_rfl ?_) ?_
      · intro x hx
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_zpow]
        exact hn
      · intro x hx
        exact hC x hx.2
    exact hle hm'
  have hgen : ∀ T : Subgroup ↥M, T.Normal → ρ.ker ≤ T → s' ∈ T → T = ⊤ := by
    intro T hT hkT hsT
    have hLT := hlift T (fun c hc => hkT (hC c hc)) s' hsT hsn
    exact eq_top_iff.mpr (hM.trans (sup_le (sup_le hLT (zpowers_le.mpr hsT)) hkT))
  have hperf : L.subgroupOf M ≤ ⁅L.subgroupOf M, L.subgroupOf M⁆ ⊔ ρ.ker := by
    have hLL : ⁅L, L⁆ ≤ M := Subgroup.commutator_le_of_le h.le h.le
    have hcomm : ⁅L, L⁆.subgroupOf M = ⁅L.subgroupOf M, L.subgroupOf M⁆ := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hLL, Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le h.le]
    intro l hl
    have : l ∈ (⁅L, L⁆ ⊔ M ⊓ centralizer (V : Set G)).subgroupOf M := h.perf hl
    rw [Subgroup.subgroupOf_sup hLL inf_le_left, hcomm] at this
    have hle : ⁅L.subgroupOf M, L.subgroupOf M⁆ ⊔ (M ⊓ centralizer (V : Set G)).subgroupOf M ≤
        ⁅L.subgroupOf M, L.subgroupOf M⁆ ⊔ ρ.ker :=
      sup_le_sup le_rfl (fun x hx => hC x hx.2)
    exact hle this
  have hs : ρ s' ∉ (L.subgroupOf M).map ρ := by
    rintro ⟨l', hl', he⟩
    apply hL1
    have hk : l'⁻¹ * s' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    refine hlift ρ.ker (fun c hc => hC c hc) _ hk ?_
    intro hmem
    apply hsn
    have hl'L : (l' : G) ∈ L := hl'
    have e : s = (l' : G) * ((l'⁻¹ * s' : ↥M) : G) := by simp [hs']
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl'L) hmem
  have hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ m : ↥M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤ := by
    intro P hP
    let Wp : Subgroup G :=
      { carrier := {g | ∃ hg : g ∈ U, cls ⟨g, hg⟩ ∈ P}
        one_mem' := ⟨U.one_mem, by
          have : (⟨1, U.one_mem⟩ : ↥U) = 1 := rfl
          rw [this, hcls1]; exact P.zero_mem⟩
        mul_mem' := by
          rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
          refine ⟨U.mul_mem ha hb, ?_⟩
          have : (⟨a * b, U.mul_mem ha hb⟩ : ↥U) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
          rw [this, hadd]; exact P.add_mem hpa hpb
        inv_mem' := by
          rintro a ⟨ha, hpa⟩
          refine ⟨U.inv_mem ha, ?_⟩
          have : (⟨a⁻¹, U.inv_mem ha⟩ : ↥U) = (⟨a, ha⟩ : ↥U)⁻¹ := rfl
          rw [this, hclsinv]; exact P.neg_mem hpa }
    have hCW : Cl ≤ Wp := fun c hc =>
      ⟨hc.1, by rw [(hker ⟨c, hc.1⟩).mpr hc]; exact P.zero_mem⟩
    have hWU : Wp ≤ U := fun g hg => hg.1
    have hLW : L ≤ normalizer (Wp : Set G) := by
      apply le_normalizer_of_conj_mem
      rintro l hl g ⟨hg, hpg⟩
      have hmem : l * g * l⁻¹ ∈ U := conj_mem_of_le_normalizer h.normU (h.le hl) hg
      refine ⟨hmem, ?_⟩
      have := hP ⟨l, h.le hl⟩ _ hpg
      rw [hρcu] at this
      exact this
    rcases h.irred hCW hWU hLW with h1 | h1
    · left
      refine eq_bot_iff.mpr fun p hp => ?_
      obtain ⟨u, rfl⟩ := hsurj p
      have : (u : G) ∈ Wp := ⟨u.2, hp⟩
      rw [h1] at this
      rw [Submodule.mem_bot]
      exact (hker u).mpr this
    · right
      refine eq_top_iff.mpr fun p _ => ?_
      obtain ⟨u, rfl⟩ := hsurj p
      have : (u : G) ∈ Wp := by rw [h1]; exact u.2
      obtain ⟨_, hp⟩ := this
      exact hp
  have hρs_ne : ρ s' ≠ 1 := by
    intro h1
    apply hL1
    exact hlift ρ.ker (fun c hc => hC c hc) s' h1 hsn
  have hkey : ∀ (u v : ↥U), (v : G) = ⁅(u : G), s⁆ →
      cls v = cls u + (ρ s' : W →ₗ[ZMod 2] W) (cls u) := by
    intro u v hv
    have e : v = u * (cu s' u)⁻¹ := Subtype.ext (by
      rw [hv]
      show _ = (u : G) * ((s : G) * u * (s : G)⁻¹)⁻¹
      simp only [commutatorElement_def]; group)
    rw [e, hadd, hclsinv, ← hρcu, zmod2_neg]
  have hexists : ∃ u1 : ↥U, (ρ s' : W →ₗ[ZMod 2] W) (cls u1) ≠ cls u1 := by
    by_contra hcon
    push Not at hcon
    apply hρs_ne
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨u, rfl⟩ := hsurj w
    exact hcon u
  obtain ⟨u1, hu1⟩ := hexists
  let v1 : ↥U := ⟨⁅(u1 : G), s⁆, h.comm_s_mem (h.normU h.mem) u1.2⟩
  set w0 : W := cls u1 + (ρ s' : W →ₗ[ZMod 2] W) (cls u1) with hw0
  have hw0v : cls v1 = w0 := hkey u1 v1 rfl
  have hw0ne : w0 ≠ 0 := by
    intro h0
    apply hu1
    have := eq_neg_of_add_eq_zero_right h0
    rw [this, zmod2_neg]
  have hrange : ∀ w : W, w + (ρ s' : W →ₗ[ZMod 2] W) w = 0 ∨
      w + (ρ s' : W →ₗ[ZMod 2] W) w = w0 := by
    intro w
    obtain ⟨u, rfl⟩ := hsurj w
    have hmu : ⁅(u : G), s⁆ ∈ U := h.comm_s_mem (h.normU h.mem) u.2
    let v : ↥U := ⟨⁅(u : G), s⁆, hmu⟩
    rw [← hkey u v rfl]
    by_cases hv1 : (⁅(u : G), s⁆ : G) = 1
    · left
      have : v = 1 := Subtype.ext hv1
      rw [this, hcls1]
    · right
      have hv1' : (⁅(u1 : G), s⁆ : G) ≠ 1 := by
        intro e
        apply hw0ne
        rw [← hw0v]
        have : v1 = 1 := Subtype.ext e
        rw [this, hcls1]
      have heq := h.Z_eq_of_ne_one (h.mem_Z (h.U_le_V u.2)) (h.mem_Z (h.U_le_V u1.2)) hv1 hv1'
      have : v = v1 := Subtype.ext heq
      rw [this, hw0v]
  have hcomspace : commutatorSpace (ρ s') = Submodule.span (ZMod 2) {w0} := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      have e : ((LinearMap.id + (ρ s' : W →ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w) = w + (ρ s' : W →ₗ[ZMod 2] W) w :=
        rfl
      rw [e]
      rcases hrange w with h0 | h0
      · rw [h0]; exact Submodule.zero_mem _
      · rw [h0]; exact Submodule.mem_span_singleton_self w0
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨cls u1, rfl⟩
  have htr : IsF2Transvection (ρ s') :=
    ⟨hρs_ne, by rw [hcomspace, finrank_span_singleton hw0ne]⟩
  have hnt : Nontrivial W := ⟨⟨w0, 0, hw0ne⟩⟩
  have hactρ : ∀ m : ↥M, ρ m = 1 → ∀ u ∈ U, ⁅u, (m : G)⁆ ∈ Cl := by
    intro m hm u hu
    have hid : ∀ w : W, (ρ m : W →ₗ[ZMod 2] W) w = w := fun w => by rw [hm]; rfl
    have h1 : cls ⟨u, hu⟩ = cls (cu m ⟨u, hu⟩) := (hid _).symm.trans (hρcu m ⟨u, hu⟩)
    have h2 : cls (⟨u, hu⟩ * (cu m ⟨u, hu⟩)⁻¹) = 0 := by
      rw [hadd, hclsinv, ← h1, add_neg_cancel]
    have h3 := (hker _).mp h2
    have e : ⁅u, (m : G)⁆ = (((⟨u, hu⟩ * (cu m ⟨u, hu⟩)⁻¹ : ↥U)) : G) := by
      show _ = u * ((m : G) * u * (m : G)⁻¹)⁻¹
      simp only [commutatorElement_def]; group
    rw [e]
    exact h3
  exact ⟨W, inferInstance, inferInstance, Module.Finite.of_finite, hnt, ρ, hirr, htr,
    hgen, hM, hperf, hL1, hs, hC, hactρ⟩
end TransvIrr

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM blockV)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (sup_le_normalizer_blockV le_normalizer_of_isWeakSBlock pCoreOf_le_centralizer_blockV)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub)
open CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
open Subgroup
open scoped commutatorElement

section Centre

private theorem center_eq_bot_of_shapeOut {Y : Type} [Group Y] (h : ShapeOut Y)
    (hsimp : IsSimpleGroup (Y ⧸ Subgroup.center Y))
    (hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases h with ⟨W, i1, i2, i3, Q, hQ, ⟨e⟩⟩ | ⟨W, i1, i2, i3, f, h4, hnd, halt, ⟨e⟩⟩ |
    ⟨m, hm, ⟨e⟩⟩
  · exact (isOrthogonalTwo_of_orth Q hQ e hsimp hnonab).1
  · obtain ⟨e6⟩ := nonempty_commutator_bilinIsometryGroup_alt_six hnd halt h4
    exact center_eq_bot_of_mulEquiv (e.trans e6)
      (alternatingGroup.center_eq_bot (by simp))
  · exact center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ m)))

variable {G : Type} [Group G] [Finite G]

private def commKer' (M W₁ W₂ : Subgroup G) (hW₂ : M ≤ normalizer (W₂ : Set G)) : Subgroup G where
  carrier := {g | g ∈ M ∧ ∀ w ∈ W₁, ⁅w, g⁆ ∈ W₂}
  one_mem' := ⟨M.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun w hw => ?_⟩
    have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W₂.mul_mem (ha' w hw) (TransvIrr.conj_mem_of_le_normalizer hW₂ ha (hb' w hw))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun w hw => ?_⟩
    have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact TransvIrr.conj_mem_of_le_normalizer hW₂ (M.inv_mem ha) (W₂.inv_mem (ha' w hw))

private theorem commutator_mem_of_center {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (ht : TransvectionData S L) {z : G} (hzL : z ∈ L)
    (hz : barMHomSub hL.le ⟨z, hzL⟩ ∈ Subgroup.center ↥(barM X L)) :
    ⁅⁅blockV S L, L⁆, zpowers z⁆ ≤ ⁅blockV S L, L⁆ ⊓ centralizer (L : Set G) := by
  obtain ⟨s, hsS, hgen, hsn, hZ⟩ := ht
  have hset := TransvIrr.setting_of hX hA hL hsS hgen hsn hZ
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (CFSG.Open.pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨W, _, _, _, _, ρ, hirr, htr, hgenρ, hM, hperf, hL1, hs, hC, hact⟩ :=
    TransvIrr.exists_rep_of_setting_act hset hV2 hsn
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hX hA hL hTM hMT hCT hx hxn)
  have hnorm : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr hset.normL
  have hshape := shapeOut_map_of_transvection_rep ρ (L.subgroupOf (L ⊔ S)) ⟨s, hset.mem⟩ hirr htr
    hgenρ hM hperf hL1 hs
  let φ : ↥L →* ↥((L.subgroupOf (L ⊔ S)).map ρ) :=
    (ρ.comp (Subgroup.inclusion hset.le)).codRestrict _ fun l =>
      ⟨⟨l, hset.le l.2⟩, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, l', hl', rfl⟩
    exact ⟨⟨(l' : G), hl'⟩, Subtype.ext rfl⟩
  have hφ1 : ∀ l : ↥L, φ l = 1 ↔ ρ ⟨l, hset.le l.2⟩ = 1 := fun l =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let π := barMHomSub hL.le
  have hπ := barMHomSub_surjective hL.le
  have hk : π.ker ≤ φ.ker := by
    intro l hl
    rw [ker_barMHomSub] at hl
    have hl' : (l : G) ∈ CFSG.Open.pCoreOf 2 L :=
      hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨l.2, hl⟩
    exact (hφ1 l).mpr (hC _ (pCoreOf_le_centralizer_blockV hA hL hl'))
  have hq := hL.component.2.2
  have hcomm := hq.1
  have hcen : ∀ a ∈ φ.ker, π a ∈ Subgroup.center ↥(barM X L) := by
    intro a ha
    have hNn : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases normal_le_center_or_eq_top hcomm hq.2 _ hNn with hc | htop
    · exact hc ⟨a, ha, rfl⟩
    · exfalso
      apply hL1
      intro l' hl'
      let l : ↥L := ⟨l', hl'⟩
      have hl : π l ∈ φ.ker.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨a', ha', hπa⟩ := hl
      have h1 : a'⁻¹ * l ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
      have h2 : φ l = 1 := by
        have : φ (a' * (a'⁻¹ * l)) = 1 := by
          rw [map_mul, ha', hk h1, one_mul]
        rwa [mul_inv_cancel_left] at this
      exact (hφ1 l).mp h2
  obtain ⟨h, hhs, hhk, hhπ⟩ := exists_central_factor π hπ φ hφ hk hcen
  have hperfL : ⁅(⊤ : Subgroup ↥(barM X L)), (⊤ : Subgroup ↥(barM X L))⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact hcomm
  obtain ⟨e⟩ := nonempty_quotientCenterEquiv_of_central_ker h hhs hhk hperfL
  have hsimp : IsSimpleGroup (_ ⧸ Subgroup.center ↥((L.subgroupOf (L ⊔ S)).map ρ)) := by
    have := hq.2
    exact e.symm.isSimpleGroup
  have hnonab : ∃ a b : _ ⧸ Subgroup.center ↥((L.subgroupOf (L ⊔ S)).map ρ), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (CFSG.HardMathSupport.Cooperstein.Coordinator.isQuasisimple_of_open' hq).2.2
    refine ⟨e a, e b, fun h' => hab ?_⟩
    simpa using congrArg e.symm h'
  have hY := center_eq_bot_of_shapeOut hshape hsimp hnonab
  have hzY : h (π ⟨z, hzL⟩) ∈ Subgroup.center ↥((L.subgroupOf (L ⊔ S)).map ρ) := by
    rw [← map_center_eq_center h hhs hhk hperfL]
    exact ⟨_, hz, rfl⟩
  rw [hY, Subgroup.mem_bot, hhπ] at hzY
  have hρz : ρ ⟨z, hset.le hzL⟩ = 1 := (hφ1 ⟨z, hzL⟩).mp hzY
  have hzK : z ∈ commKer' (L ⊔ S) ⁅blockV S L, L⁆
      (⁅blockV S L, L⁆ ⊓ centralizer (L : Set G)) hset.normCl :=
    show z ∈ L ⊔ S ∧ ∀ w ∈ ⁅blockV S L, L⁆, ⁅w, z⁆ ∈ ⁅blockV S L, L⁆ ⊓ centralizer (L : Set G) from
      ⟨hset.le hzL, fun w hw => hact ⟨z, hset.le hzL⟩ hρz w hw⟩
  rw [Subgroup.commutator_le]
  intro u hu g hg
  have hg' := Subgroup.zpowers_le.mpr hzK hg
  exact (show g ∈ L ⊔ S ∧ ∀ w ∈ ⁅blockV S L, L⁆, ⁅w, g⁆ ∈ ⁅blockV S L, L⁆ ⊓
    centralizer (L : Set G) from hg').2 u hu

end Centre

section Coprime

variable {G : Type} [Group G] [Finite G]

open CFSG.AGLEmbedding (le_normalizer_commutator_of_le_normalizer commutator_le_left_of_le_normalizer)

private theorem coprime_card_zpowers {z : G} (hz : Odd (orderOf z)) {W : Subgroup G}
    (hW : IsPGroup 2 ↥W) : Nat.Coprime (Nat.card ↥(Subgroup.zpowers z)) (Nat.card ↥W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
  rw [Nat.card_zpowers, hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hz) |>.symm.symm

private theorem commutator_zpowers_eq_bot {V U Cl : Subgroup G} {z : G} (hz : Odd (orderOf z))
    (hV : IsPGroup 2 ↥V) (hzV : z ∈ Subgroup.normalizer (V : Set G))
    (hVU : ⁅V, Subgroup.zpowers z⁆ ≤ U) (hUCl : ⁅U, Subgroup.zpowers z⁆ ≤ Cl)
    (hCl : ⁅Cl, Subgroup.zpowers z⁆ = ⊥) : ⁅V, Subgroup.zpowers z⁆ = ⊥ := by
  set R := Subgroup.zpowers z with hR
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hzV
  have hRA : R ≤ Subgroup.normalizer ((⁅V, R⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizer hRV
  have hAV : ⁅V, R⁆ ≤ V := commutator_le_left_of_le_normalizer hRV
  have h2 : ⁅⁅⁅V, R⁆, R⁆, R⁆ = ⊥ := le_bot_iff.mp (by
    calc ⁅⁅⁅V, R⁆, R⁆, R⁆ ≤ ⁅⁅U, R⁆, R⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hVU le_rfl) le_rfl
      _ ≤ ⁅Cl, R⁆ := Subgroup.commutator_mono hUCl le_rfl
      _ = ⊥ := hCl)
  have h1 : ⁅⁅V, R⁆, R⁆ = ⊥ :=
    CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot _ R hRA
      (coprime_card_zpowers hz (hV.to_le hAV)) h2
  exact CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot _ R hRV
    (coprime_card_zpowers hz hV) h1

end Coprime

section Main

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (IsTwoPrimeComponent)
open CFSG.HardMathSupport.Cooperstein.Coordinator (asc81bHyp_sup)

omit [Finite G] in
private theorem inf_pCoreOf_sup_le {S L : Subgroup G} :
    L ⊓ CFSG.Open.pCoreOf 2 (L ⊔ S) ≤ CFSG.Open.pCoreOf 2 L := by
  refine normal_pGroup_le_pCoreOf 2 _ L inf_le_left ?_
    ((pCoreOf_isPGroup 2 (L ⊔ S)).to_le inf_le_right)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  exact common_normalizer_le_normalizer_inf L L _ Subgroup.le_normalizer
    (le_sup_left.trans (localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)))

variable {X S L : Subgroup G}

private theorem mem_pCoreOf_of_center (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L)
    (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) {z : G} (hzL : z ∈ L)
    (hz : barMHomSub hL.le ⟨z, hzL⟩ ∈ Subgroup.center ↥(barM X L)) (hodd : Odd (orderOf z)) :
    z ∈ CFSG.Open.pCoreOf 2 L := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have hQM : L ⊔ S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (L ⊔ S) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hzR : Subgroup.zpowers z ≤ L := Subgroup.zpowers_le.mpr hzL
  have hVQ : blockV S L ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hV2 : IsPGroup 2 ↥(blockV S L) := (pCoreOf_isPGroup 2 (L ⊔ S)).to_le hVQ
  have hUCl := commutator_mem_of_center hX hA hL ht hzL hz
  have hVU : ⁅blockV S L, Subgroup.zpowers z⁆ ≤ ⁅blockV S L, L⁆ :=
    Subgroup.commutator_mono le_rfl hzR
  have hCl : ⁅⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G), Subgroup.zpowers z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_right.trans (Subgroup.centralizer_le hzR))
  have hVz := commutator_zpowers_eq_bot hodd hV2
    (hMV (Subgroup.mem_sup_left hzL)) hVU hUCl hCl
  have hQz : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), Subgroup.zpowers z⁆ = ⊥ := by
    have hQ2 := pCoreOf_isPGroup 2 (L ⊔ S)
    have hQR : Subgroup.zpowers z ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (L ⊔ S) : Set G) :=
      hzR.trans (le_sup_left.trans hQM)
    refine CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot _ _ hQR
      (coprime_card_zpowers hodd hQ2) (le_bot_iff.mp ?_)
    calc ⁅⁅CFSG.Open.pCoreOf 2 (L ⊔ S), Subgroup.zpowers z⁆, Subgroup.zpowers z⁆
        ≤ ⁅blockV S L, Subgroup.zpowers z⁆ :=
          Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hzR).trans hQV) le_rfl
      _ = ⊥ := hVz
  have hzC : z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (L ⊔ S) : Set G) := by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (this hq) z (Subgroup.mem_zpowers z)).symm
  have hA' := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  exact inf_pCoreOf_sup_le ⟨hzL, hA'.charTwo ⟨Subgroup.mem_sup_left hzL, hzC⟩⟩

theorem centre_barM_trivial (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L)
    (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) :
    Subgroup.center ↥(barM X L) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨⟨z, hzL⟩, rfl⟩ := barMHomSub_surjective hL.le c
  have hodd := odd_card_center_barM hL.toIsTwoPrimeComponent
  have hordc : Odd (orderOf (barMHomSub hL.le ⟨z, hzL⟩)) := by
    have h1 : orderOf (⟨barMHomSub hL.le ⟨z, hzL⟩, hc⟩ : Subgroup.center ↥(barM X L)) ∣
        Nat.card (Subgroup.center ↥(barM X L)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  obtain ⟨k, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  have hz' : orderOf (z ^ 2 ^ k) = r := by
    rw [orderOf_pow_of_dvd (by positivity) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hz'L : z ^ 2 ^ k ∈ L := L.pow_mem hzL _
  have hmap : barMHomSub hL.le ⟨z ^ 2 ^ k, hz'L⟩ = (barMHomSub hL.le ⟨z, hzL⟩) ^ 2 ^ k := by
    rw [← map_pow]; rfl
  have hcen' : barMHomSub hL.le ⟨z ^ 2 ^ k, hz'L⟩ ∈ Subgroup.center ↥(barM X L) := by
    rw [hmap]; exact Subgroup.pow_mem _ hc _
  have hmem := mem_pCoreOf_of_center hX hA hL ht hQV hz'L hcen' (hz' ▸ hr)
  have h1 : barMHomSub hL.le ⟨z ^ 2 ^ k, hz'L⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_barMHomSub]
    exact (hL.toIsTwoPrimeComponent.inf_twoCore.symm.le.trans inf_le_right) hmem
  rw [hmap] at h1
  have hdvd : orderOf (barMHomSub hL.le ⟨z, hzL⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hordc))
    hdvd
  rw [orderOf_eq_one_iff.mp this]
  exact Subgroup.one_mem _

end Main

section Short

variable {G : Type} [Group G] [Finite G]

open CFSG.AGLEmbedding (HasIrreducibleCommutatorQuotient)
open CFSG.QuasithinUnique (IsShort2 blockQ blockU blockZ)
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (asc81bHyp_sup isQuasisimple_of_open' twoCore_sup_le)
open CFSG.AGLEmbedding (le_normalizer_commutator_of_le_normalizer commutator_le_left_of_le_normalizer)

private theorem noTwoQuotient {M L : Subgroup G} (hL : CFSG.AGLEmbedding.IsTwoPrimeComponent M L) :
    ∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤ := by
  intro N _ hp
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
  have : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (↥L ⧸ N) := hp.isNilpotent
  have : Group.IsSolvable (↥L ⧸ N) := inferInstance
  have hsub := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := ↥L ⧸ N)
  refine eq_top_iff.mpr fun x _ => ?_
  have h1 : (QuotientGroup.mk x : ↥L ⧸ N) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff x).mp h1

omit [Finite G] in
private theorem commutator_le_commutator_commutator_of_perfect {N L : Subgroup G}
    (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hL : ⁅L, L⁆ = L) :
    ⁅N, L⁆ ≤ ⁅⁅N, L⁆, L⁆ := by
  have h1 : L ≤ Subgroup.normalizer ((⁅N, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizer hLN
  have h2 : L ≤ Subgroup.normalizer ((⁅⁅N, L⁆, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizer h1
  have := TransvIrr.commutator_commutator_le_of_rotate (A := L) (B := N) (C := L)
    (N := ⁅⁅N, L⁆, L⁆) h2 (hNL.trans h2) h2
    (by rw [Subgroup.commutator_comm L N]) (by exact le_rfl)
  rw [hL, Subgroup.commutator_comm L N] at this
  exact this

section PCoreQuotient

variable {L : Subgroup G}
open CFSG.AGLEmbedding (IsTwoPrimeComponent)

omit [Finite G] in
private theorem ker_barMHomSub_eq {X : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    (barMHomSub hL.le).ker = CFSG.pCore 2 ↥L := by
  ext x
  rw [ker_barMHomSub, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hN := hL.inf_twoCore.le ⟨x.2, h⟩
    rw [CFSG.Open.pCoreOf] at hN
    obtain ⟨y, hy, hyx⟩ := hN
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  · intro h
    have hx : (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
      rw [CFSG.Open.pCoreOf]
      exact ⟨x, by exact h,
        rfl⟩
    exact (hL.inf_twoCore.symm.le hx).2

private noncomputable def quotPCoreEquiv {X : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(barM X L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barMHomSub_eq hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (barMHomSub_surjective hL.le))

omit [Finite G] in
private theorem isQuasisimple_quotient_pCore {X : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
  isQuasisimple_of_open'
    (CFSG.HardMathSupport.Cooperstein.Proving.isQuasisimple_of_mulEquiv'
      (quotPCoreEquiv hL).symm hL.component.2.2)

end PCoreQuotient

variable {X S L : Subgroup G}

private theorem pCoreOf_le_pCoreOf_sup (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) :
    CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) := by
  have hXLS : L ⊔ S ≤ X := sup_le hL.le hA.twoRadical.1
  have hQS : CFSG.Open.pCoreOf 2 X ≤ L ⊔ S := hA.twoCore_le.trans le_sup_right
  have h1 : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    normal_pGroup_le_pCoreOf 2 _ _ hQS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr
        (hXLS.trans (localGroup_le_normalizer_pCoreOf 2 X)))
      (pCoreOf_isPGroup 2 X)
  exact (hL.toIsTwoPrimeComponent.inf_twoCore.symm.le.trans inf_le_right).trans h1

section Aux

variable (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)

include hX hA hL

private theorem commutator_pCoreOf_sup_le :
    ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hQL : CFSG.Open.pCoreOf 2 (L ⊔ S) ≤ Subgroup.normalizer (L : Set G) :=
    (twoCore_sup_le hA hL hSL).trans hSL
  have h1 : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ L := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hQL
  have h2 : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    commutator_le_left_of_le_normalizer (le_sup_left.trans (localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)))
  exact (le_inf h1 h2).trans inf_pCoreOf_sup_le

variable (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L)

include hQV

private theorem blockU_eq : blockU L = ⁅blockV S L, L⁆ := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) := le_sup_left.trans hMV
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 L
  have hVQ : blockV S L ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hV2 : IsPGroup 2 ↥(blockV S L) := (pCoreOf_isPGroup 2 (L ⊔ S)).to_le hVQ
  have hQLN := commutator_pCoreOf_sup_le hX hA hL
  show ⁅CFSG.Open.pCoreOf 2 L, L⁆ = _
  apply le_antisymm
  · calc ⁅CFSG.Open.pCoreOf 2 L, L⁆
        ≤ ⁅⁅CFSG.Open.pCoreOf 2 L, L⁆, L⁆ :=
          commutator_le_commutator_commutator_of_perfect (pCoreOf_le 2 L) hLN hL.perfect
      _ ≤ ⁅blockV S L, L⁆ := Subgroup.commutator_mono
          ((Subgroup.commutator_mono (pCoreOf_le_pCoreOf_sup hA hL) le_rfl).trans hQV) le_rfl
  · have hVL : ⁅blockV S L, L⁆ ≤ blockV S L := commutator_le_left_of_le_normalizer hLV
    have hVN : ⁅blockV S L, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
      (Subgroup.commutator_mono hVQ le_rfl).trans hQLN
    calc ⁅blockV S L, L⁆
        ≤ ⁅⁅blockV S L, L⁆, L⁆ :=
          CFSG.AGLEmbedding.commutator_le_commutator_commutator_of_twoGroup
            (noTwoQuotient hL.toIsTwoPrimeComponent) hLV
            (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).1 (hV2.to_le hVL)
      _ ≤ ⁅CFSG.Open.pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hVN le_rfl

private theorem blockU_clause :
    blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) ∧
      ∀ x ∈ blockU L, x ^ 2 = 1 := by
  have hMV := sup_le_normalizer_blockV S L
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 L
  have hUN : blockU L ≤ CFSG.Open.pCoreOf 2 L := commutator_le_left_of_le_normalizer hLN
  have hUV : blockU L ≤ blockV S L := by
    rw [blockU_eq hX hA hL hQV]
    exact commutator_le_left_of_le_normalizer (le_sup_left.trans hMV)
  refine ⟨le_inf hUN fun u hu => ?_, fun x hx =>
    (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).2 x (hUV hx)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnV : n ∈ Subgroup.centralizer (blockV S L : Set G) :=
    CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self _
      (pCoreOf_le_pCoreOf_sup hA hL hn)
  exact (Subgroup.mem_centralizer_iff.mp hnV u (hUV hu)).symm

private theorem blockZ_clause (hirr : HasIrreducibleCommutatorQuotient L (blockV S L)) :
    blockZ L < blockU L ∧
      ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L → L ≤ Subgroup.normalizer (W : Set G) →
        W = blockZ L ∨ W = blockU L := by
  have hU := blockU_eq hX hA hL hQV
  have hZ : blockZ L = ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← hU]; rfl
  rw [hZ, hU]
  exact hirr

private theorem charTwo_clause (hirr : HasIrreducibleCommutatorQuotient L (blockV S L))
    (hcen : Subgroup.center ↥(barM X L) = ⊥) : CFSG.QuasithinUnique.CharTwo L := by
  intro x hx
  obtain ⟨hxL, hxC⟩ := hx
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 L
  let D : Subgroup ↥L := (L ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 L : Set G)).subgroupOf L
  have hDn : D.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg => ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, CFSG.Quasithin.InternalSec.le_normalizer_centralizer hLN hg⟩
  let π := barMHomSub hL.le
  have hπ := barMHomSub_surjective hL.le
  have hq := hL.component.2.2
  have hNn : (D.map π).Normal := hDn.map π hπ
  rcases normal_le_center_or_eq_top hq.1 hq.2 _ hNn with hc | htop
  · have h1 : π ⟨x, hxL⟩ ∈ Subgroup.center ↥(barM X L) :=
      hc ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr ⟨hxL, hxC⟩, rfl⟩
    rw [hcen, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ π.ker := h1
    rw [ker_barMHomSub] at h2
    exact hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨hxL, h2⟩
  · exfalso
    have hq2 : IsPGroup 2 (↥L ⧸ D) := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl : π l ∈ D.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdl⟩ := hl
      have hker : d⁻¹ * l ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, inv_mul_cancel]
      rw [ker_barMHomSub] at hker
      have hnN : ((d⁻¹ * l : ↥L) : G) ∈ CFSG.Open.pCoreOf 2 L :=
        hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨(d⁻¹ * l).2, hker⟩
      obtain ⟨e, he⟩ := pCoreOf_isPGroup 2 L ⟨_, hnN⟩
      refine ⟨e, ?_⟩
      have hmk : (QuotientGroup.mk l : ↥L ⧸ D) = QuotientGroup.mk (d⁻¹ * l) := by
        have h1 : (QuotientGroup.mk d : ↥L ⧸ D) = 1 := (QuotientGroup.eq_one_iff d).mpr hd
        calc (QuotientGroup.mk l : ↥L ⧸ D) = QuotientGroup.mk (d * (d⁻¹ * l)) := by
              rw [mul_inv_cancel_left]
          _ = QuotientGroup.mk d * QuotientGroup.mk (d⁻¹ * l) := QuotientGroup.mk_mul _ _ _
          _ = _ := by rw [h1, one_mul]
      have hpow1 : (d⁻¹ * l) ^ 2 ^ e = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val he)
      rw [hmk, ← QuotientGroup.mk_pow, hpow1, QuotientGroup.mk_one]
    have hDtop := @noTwoQuotient _ _ _ _ _ hL.toIsTwoPrimeComponent D hDn hq2
    have hLC : L ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 L : Set G) := fun l hl =>
      (Subgroup.mem_subgroupOf.mp
        (show (⟨l, hl⟩ : ↥L) ∈ D by rw [hDtop]; exact Subgroup.mem_top _)).2
    have h0 : ⁅CFSG.Open.pCoreOf 2 L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
    have h1 : ⁅blockV S L, L⁆ = ⊥ := by
      rw [← blockU_eq hX hA hL hQV]
      exact h0
    have h2 := hirr.1
    rw [h1, bot_inf_eq] at h2
    exact lt_irrefl _ h2

end Aux

open CFSG.AGLEmbedding (NineThreeFour)
open CFSG.RankThree.PartTwo (IsA6Z3Type)

theorem isShort2_of_hQV_of_center_eq_bot (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hirr : HasIrreducibleCommutatorQuotient L (blockV S L))
    (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L)
    (hcen : Subgroup.center ↥(barM X L) = ⊥) : IsShort2 L :=
  ⟨noTwoQuotient hL.toIsTwoPrimeComponent, charTwo_clause hX hA hL hQV hirr hcen,
    blockU_clause hX hA hL hQV, Or.inl (isQuasisimple_quotient_pCore hL.toIsTwoPrimeComponent),
    blockZ_clause hX hA hL hQV hirr⟩

theorem isShort2_of_hQV (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L)
    (hirr : HasIrreducibleCommutatorQuotient L (blockV S L))
    (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) : IsShort2 L :=
  isShort2_of_hQV_of_center_eq_bot hX hA hL hirr hQV (centre_barM_trivial hX hA hL ht hQV)

theorem card_center_barM_ne_three (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L)
    (hQV : ⁅CFSG.Open.pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) :
    Nat.card (Subgroup.center ↥(barM X L)) ≠ 3 := by
  rw [centre_barM_trivial hX hA hL ht hQV, Subgroup.card_bot]
  norm_num

end Short

end CFSG.HardMathSupport.Cooperstein.StructureLie

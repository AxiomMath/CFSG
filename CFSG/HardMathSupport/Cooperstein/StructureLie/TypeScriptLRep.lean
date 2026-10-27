module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace TransvIrr

open Subgroup CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L V : Subgroup G} {s : G}

theorem exists_rep_data_of_setting (h : Setting M L V s) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsn : s ∉ L ⊔ M ⊓ centralizer (V : Set G))
    (hN : ∀ T : Subgroup G, T ≤ M → M ≤ normalizer (T : Set G) →
      M ⊓ centralizer (V : Set G) ≤ T → ∀ x ∈ T,
        x ∉ L ⊔ M ⊓ centralizer (V : Set G) → L ≤ T) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (_ : Nontrivial W) (cls : ↥⁅V, L⁆ → W) (ρ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ a b, cls (a * b) = cls a + cls b) ∧ Function.Surjective cls ∧
      (∀ u, cls u = 0 ↔ (u : G) ∈ ⁅V, L⁆ ⊓ centralizer (L : Set G)) ∧
      (∀ (m : ↥M) (u v : ↥⁅V, L⁆), (v : G) = m * u * (m : G)⁻¹ →
        (ρ m : W →ₗ[ZMod 2] W) (cls u) = cls v) ∧
      (∀ P : Submodule (ZMod 2) W,
        (∀ m : ↥M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤) ∧
      IsF2Transvection (ρ ⟨s, h.mem⟩) ∧
      (∀ T : Subgroup ↥M, T.Normal → ρ.ker ≤ T → (⟨s, h.mem⟩ : ↥M) ∈ T → T = ⊤) ∧
      ⊤ ≤ L.subgroupOf M ⊔ Subgroup.zpowers (⟨s, h.mem⟩ : ↥M) ⊔ ρ.ker ∧
      L.subgroupOf M ≤ ⁅L.subgroupOf M, L.subgroupOf M⁆ ⊔ ρ.ker ∧
      ¬ L.subgroupOf M ≤ ρ.ker ∧
      ρ ⟨s, h.mem⟩ ∉ (L.subgroupOf M).map ρ ∧
      (∀ c : ↥M, (c : G) ∈ centralizer (V : Set G) → ρ c = 1) := by
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
  exact ⟨W, inferInstance, inferInstance, Module.Finite.of_finite, hnt, cls, ρ, hadd, hsurj, hker,
    hact, hirr, htr, hgen, hM, hperf, hL1, hs, hC⟩

end TransvIrr

end CFSG.HardMathSupport.Cooperstein.StructureLie

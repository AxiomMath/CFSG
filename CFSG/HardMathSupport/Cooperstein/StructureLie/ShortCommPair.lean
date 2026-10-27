module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

section Abstract

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {M : Type*} [Group M]

theorem exists_symm_pair [Nontrivial W]
    (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (L : Subgroup M) [L.Normal] (s : M)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ m : M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤)
    (htr : IsF2Transvection (ρ s))
    (hgen : ∀ T : Subgroup M, T.Normal → ρ.ker ≤ T → s ∈ T → T = ⊤)
    (hM : ⊤ ≤ L ⊔ Subgroup.zpowers s ⊔ ρ.ker)
    (hperf : L ≤ ⁅L, L⁆ ⊔ ρ.ker) (hL1 : ¬ L ≤ ρ.ker) (hs : ρ s ∉ L.map ρ)
    {φ : Dual (ZMod 2) W} {a : W} (h0 : φ a = 0) (hts : ρ s = tv φ a h0) :
    ∃ l ∈ L, φ (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) = 1 ∧
      φ (((ρ l : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) = 1 := by
  classical
  have hn : 1 ≤ finrank (ZMod 2) W := Module.finrank_pos
  have hidx : (L.map ρ).relIndex ρ.range = 2 := relIndex_map_eq_two ρ L s htr hM hs
  have hperfL : ⁅L.map ρ, L.map ρ⁆ = L.map ρ := by
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun x hx y hy => by
        have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · calc L.map ρ ≤ (⁅L, L⁆ ⊔ ρ.ker).map ρ := Subgroup.map_mono hperf
        _ = ⁅L.map ρ, L.map ρ⁆ := by
          rw [Subgroup.map_sup, Subgroup.map_commutator,
            (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hL1' : L.map ρ ≠ ⊥ := fun h => hL1 ((Subgroup.map_eq_bot_iff _).mp h)
  have h3 : 3 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    exact hL1' (eq_bot_of_isPerfect_of_finrank_le_two (by omega) _ hperfL)
  have hHtop : ρ.range ≠ ⊤ := by
    intro hH
    refine false_of_perfect_of_relIndex_two hidx ?_
    rw [hH]
    exact commutator_top_eq_top_of_three_le h3
  have hgenH : GenByTransvections ρ.range :=
    ⟨_, by
      rintro _ ⟨g, -, rfl⟩
      exact isF2Transvection_conj htr g, range_eq_closure_conj ρ s hgen⟩
  have hirrH : IsIrreducibleOn ρ.range := fun P hP =>
    hirr P fun m w hw => hP (ρ m) ⟨m, rfl⟩ w hw
  have hno : NoDihedralPair ρ.range := fun φ ψ a b ha hψ hφa hψb hφb hψa =>
    hHtop (eq_top_of_dihedral hgenH hirrH ha hψ hφa hψb hφb hψa)
  have hφne : φ ≠ 0 := by
    rintro rfl
    exact htr.1 (by rw [hts]; exact tv_zero_left a h0)
  have hane : a ≠ 0 := by
    rintro rfl
    exact htr.1 (by rw [hts]; exact tv_zero_right φ h0)
  have hsa : (ρ s : W →ₗ[ZMod 2] W) a = a := by
    rw [hts, tv_apply, h0, zero_smul, add_zero]
  have hsinv : ρ s⁻¹ = ρ s := by
    rw [map_inv]; exact inv_eq_of_mul_eq_one_right (isF2Transvection_mul_self htr)
  have hex : ∃ l ∈ L, φ (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) = 1 := by
    by_contra hall
    push Not at hall
    set P : Submodule (ZMod 2) W :=
      Submodule.span (ZMod 2) {w | ∃ l ∈ L, w = ((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a}
      with hP
    have hgenP : ∀ l ∈ L, ((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a ∈ P :=
      fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩
    have hLinv : ∀ m ∈ L, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P := by
      intro m hm w hw
      have : P ≤ P.comap (ρ m : W →ₗ[ZMod 2] W) := by
        rw [hP, Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        show (ρ m : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) ∈ P
        have e : (ρ m : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) =
            ((ρ (l * m⁻¹)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a := by
          rw [show (l * m⁻¹)⁻¹ = m * l⁻¹ by group, map_mul]
          rfl
        rw [e]
        exact hgenP _ (L.mul_mem hl (L.inv_mem hm))
      exact this hw
    set Tm : Subgroup M :=
      { carrier := {m | (∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) ∧
          ∀ w ∈ P, (ρ m⁻¹ : W →ₗ[ZMod 2] W) w ∈ P}
        one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
        mul_mem' := by
          rintro m n ⟨hm1, hm2⟩ ⟨hn1, hn2⟩
          refine ⟨fun w hw => ?_, fun w hw => ?_⟩
          · have := hm1 _ (hn1 w hw)
            simpa [map_mul] using this
          · have := hn2 _ (hm2 w hw)
            have e : (m * n)⁻¹ = n⁻¹ * m⁻¹ := mul_inv_rev m n
            rw [e, map_mul]
            exact this
        inv_mem' := by
          rintro m ⟨hm1, hm2⟩
          exact ⟨hm2, fun w hw => by simpa using hm1 w hw⟩ } with hTm
    have hLT : L ≤ Tm := fun m hm => ⟨hLinv m hm, hLinv m⁻¹ (L.inv_mem hm)⟩
    have hsT : s ∈ Tm := by
      have key : ∀ w ∈ P, (ρ s : W →ₗ[ZMod 2] W) w ∈ P := by
        intro w hw
        have : P ≤ P.comap (ρ s : W →ₗ[ZMod 2] W) := by
          rw [hP, Submodule.span_le]
          rintro _ ⟨l, hl, rfl⟩
          show (ρ s : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) ∈ P
          have e : (ρ s : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) =
              ((ρ (s * l * s⁻¹)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a := by
            have e1 : (s * l * s⁻¹)⁻¹ = s * l⁻¹ * s⁻¹ := by group
            rw [e1, map_mul, map_mul, hsinv]
            show (ρ s : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) =
              (ρ s : W →ₗ[ZMod 2] W) (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
                W →ₗ[ZMod 2] W) ((ρ s : W →ₗ[ZMod 2] W) a))
            rw [hsa]
          rw [e]
          exact hgenP _ (Subgroup.Normal.conj_mem ‹L.Normal› l hl s)
        exact this hw
      exact ⟨key, by rw [hsinv]; exact key⟩
    have hkT : ρ.ker ≤ Tm := fun k hk => by
      have hk1 : ρ k = 1 := hk
      have hk2 : ρ k⁻¹ = 1 := by rw [map_inv, hk1, inv_one]
      exact ⟨fun w hw => by rw [hk1]; simpa using hw, fun w hw => by rw [hk2]; simpa using hw⟩
    have hTtop : Tm = ⊤ := by
      rw [eq_top_iff]
      exact hM.trans (sup_le (sup_le hLT (Subgroup.zpowers_le.mpr hsT)) hkT)
    have hinv : ∀ m : M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P := fun m w hw => by
      have : m ∈ Tm := by rw [hTtop]; trivial
      exact this.1 w hw
    have haP : a ∈ P := by
      have := hgenP 1 L.one_mem
      simpa using this
    rcases hirr P hinv with hb | ht
    · exact hane (by simpa using (hb ▸ haP : a ∈ (⊥ : Submodule (ZMod 2) W)))
    · have hker : P ≤ LinearMap.ker φ := by
        rw [hP, Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        rcases zmod2_eq_zero_or_one (φ (((ρ l⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a)) with h | h
        · exact h
        · exact absurd h (hall l hl)
      rw [ht] at hker
      apply hφne
      ext w
      exact LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := w)))
  obtain ⟨l, hl, hφl⟩ := hex
  refine ⟨l, hl, hφl, ?_⟩
  set g : LinearMap.GeneralLinearGroup (ZMod 2) W := ρ l⁻¹ with hg
  have hgH : g ∈ ρ.range := ⟨l⁻¹, rfl⟩
  have hginv : g⁻¹ = ρ l := by rw [hg, map_inv, inv_inv]
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W))
      ((g : W →ₗ[ZMod 2] W) a) = 0 := by
    rw [LinearMap.comp_apply]
    have : ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W)
        ((g : W →ₗ[ZMod 2] W) a) = a := by
      change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a = a
      rw [inv_mul_cancel]; rfl
    rw [this]; exact h0
  have hgg : ∀ w : W, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W)
      ((g : W →ₗ[ZMod 2] W) w) = w := fun w => by
    change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w = w
    rw [inv_mul_cancel]; rfl
  have hconj := conj_tv g φ a h0 h'
  set ψ : Dual (ZMod 2) W := φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    W →ₗ[ZMod 2] W) with hψdef
  set b : W := (g : W →ₗ[ZMod 2] W) a with hbdef
  have hmem : tv ψ b h' ∈ ρ.range := by
    rw [← hconj]
    exact ρ.range.mul_mem (ρ.range.mul_mem hgH (by rw [← hts]; exact ⟨s, rfl⟩))
      (ρ.range.inv_mem hgH)
  have hb0 : b ≠ 0 := fun hb => hane (by rw [← hgg a]; rw [← hbdef, hb]; simp)
  have hψne : ψ ≠ 0 := by
    intro hψ0
    apply hφne
    ext w
    have := LinearMap.congr_fun hψ0 ((g : W →ₗ[ZMod 2] W) w)
    rw [hψdef, LinearMap.comp_apply, hgg] at this
    simpa using this
  have hsymm := apply_eq_apply hno hane hb0 hφne hψne ⟨h0, by rw [← hts]; exact ⟨s, rfl⟩⟩
    ⟨h', hmem⟩
  rw [hbdef, hφl] at hsymm
  rw [← hginv]
  exact hsymm.symm

end Abstract

namespace TransvIrr

open Subgroup

variable {G : Type} [Group G] [Finite G] {M L V : Subgroup G} {s : G}

theorem exists_pair_of_setting (h : Setting M L V s) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsn : s ∉ L ⊔ M ⊓ centralizer (V : Set G))
    (hN : ∀ T : Subgroup G, T ≤ M → M ≤ normalizer (T : Set G) →
      M ⊓ centralizer (V : Set G) ≤ T → ∀ x ∈ T,
        x ∉ L ⊔ M ⊓ centralizer (V : Set G) → L ≤ T) :
    ∃ z ∈ (⁅V, zpowers s⁆ : Subgroup G), z ≠ 1 ∧ ∃ l ∈ L,
      ⁅l⁻¹ * z * l, s⁆ ≠ 1 ∧ ⁅l * z * l⁻¹, s⁆ ≠ 1 := by
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
  have : Nontrivial W := hnt
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hnormL : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normL
  obtain ⟨φ, a, h0, hφ, ha, hts⟩ := (isF2Transvection_iff _).mp htr
  have haw : a = w0 := by
    obtain ⟨w, hw⟩ := exists_apply_eq_one hφ
    have h1 : w + (ρ s' : W →ₗ[ZMod 2] W) w = a := by
      rw [hts, tv_apply, hw, one_smul, ← add_assoc, zmod2_add_self, zero_add]
    rcases hrange w with h2 | h2
    · exact absurd (h1.symm.trans h2) ha
    · exact h1.symm.trans h2
  obtain ⟨l, hl, hl1, hl2⟩ :=
    exists_symm_pair ρ (L.subgroupOf M) s' hirr htr hgen hM hperf hL1 hs h0 hts
  have hzZ : ((v1 : ↥U) : G) ∈ (⁅V, zpowers s⁆ : Subgroup G) :=
    h.mem_Z (h.U_le_V u1.2)
  have hz1 : ((v1 : ↥U) : G) ≠ 1 := by
    intro hz
    have : v1 = 1 := Subtype.ext hz
    apply hw0ne
    rw [← hw0v, this, hcls1]
  have key : ∀ m : ↥M, φ (((ρ m : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a) = 1 →
      ⁅(m : G) * ((v1 : ↥U) : G) * (m : G)⁻¹, s⁆ ≠ 1 := by
    intro m hm hcomm
    have hmU : (m : G) * ((v1 : ↥U) : G) * (m : G)⁻¹ ∈ U :=
      conj_mem_of_le_normalizer h.normU m.2 v1.2
    set mv : ↥U := ⟨(m : G) * ((v1 : ↥U) : G) * (m : G)⁻¹, hmU⟩ with hmvdef
    have h1 : ((ρ m : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) (cls v1) = cls mv :=
      hact m v1 mv rfl
    have h1' : ((ρ m : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) a = cls mv := by
      rw [haw, ← hw0v]; exact h1
    rw [h1'] at hm
    have hfix : (mv : G) = (s' : G) * (mv : G) * (s' : G)⁻¹ := by
      have := commutatorElement_eq_one_iff_mul_comm.mp hcomm
      show (m : G) * ((v1 : ↥U) : G) * (m : G)⁻¹ = s * ((m : G) * ((v1 : ↥U) : G) * (m : G)⁻¹) * s⁻¹
      rw [← this]
      group
    have h3 := hact s' mv mv hfix
    have e1 : ((ρ s' : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) (cls mv) =
        cls mv + φ (cls mv) • a := by rw [hts, tv_apply]
    rw [e1, hm, one_smul] at h3
    apply ha
    simpa using h3
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  refine ⟨((v1 : ↥U) : G), hzZ, hz1, (l : G), hlL, ?_, ?_⟩
  · have := key l⁻¹ hl1
    have e : ((l⁻¹ : ↥M) : G) * ((v1 : ↥U) : G) * ((l⁻¹ : ↥M) : G)⁻¹ =
        (l : G)⁻¹ * ((v1 : ↥U) : G) * (l : G) := by
      simp
    rwa [e] at this
  · exact key l hl2

end TransvIrr

end CFSG.HardMathSupport.Cooperstein.StructureLie

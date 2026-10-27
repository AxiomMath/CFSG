module

public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def LocalCStarConcl (G T : Subgroup Γ) : Prop :=
  ∃ 𝒢 : Set (Subgroup Γ), (∀ E ∈ 𝒢, IsBTBlock G T E) ∧
    (∀ E ∈ 𝒢, ∀ g ∈ G, conjSub g E ∈ 𝒢) ∧
    (∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) ∧
    cStarIn G T ⊔ (⨆ E ∈ 𝒢, E) = G ∧
    (∀ F : Subgroup Γ, IsBTBlock G T F → ¬ F ≤ cStarIn G T → ∃ E ∈ 𝒢, F ≤ E) ∧
    cStarIn G T ⊓ (⨆ E ∈ 𝒢, E) = ⨆ E ∈ 𝒢, cStarIn G T ⊓ E ∧
    ∀ E ∈ 𝒢,
      ((∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∧
        cStarIn G T ⊓ E = Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ) ⊓ E) ∨
      (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
        Nonempty ((((cStarIn G T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
          alternatingGroup (Fin (2 * m))))

theorem bhsLocalCStar_of_concl
    (h : ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T : Subgroup Γ), CharTwo G → IsSylowOf 2 T G →
      cStarIn G T ≠ G → LocalCStarConcl G T) : BHSLocalCStar :=
  fun Γ _ _ G T h1 h2 h3 => h Γ G T h1 h2 h3

structure MinCex [Finite Γ] (G T : Subgroup Γ) : Prop where
  charTwo : CharTwo G
  sylow : IsSylowOf 2 T G
  ne : cStarIn G T ≠ G
  not_concl : ¬ LocalCStarConcl G T
  ih : ∀ G' T' : Subgroup Γ, Nat.card G' < Nat.card G → CharTwo G' → IsSylowOf 2 T' G' →
    cStarIn G' T' ≠ G' → LocalCStarConcl G' T'

theorem concl_of_forall_not_minCex [Finite Γ] (h : ∀ G T : Subgroup Γ, ¬ MinCex G T)
    (G T : Subgroup Γ) (hc : CharTwo G) (hT : IsSylowOf 2 T G) (hne : cStarIn G T ≠ G) :
    LocalCStarConcl G T := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G T with
  | h n ih =>
    by_contra hcon
    refine h G T ⟨hc, hT, hne, hcon, fun G' T' hlt hc' hT' hne' => ?_⟩
    exact ih _ (hn ▸ hlt) G' T' hc' hT' hne' rfl

@[expose] def vSub (G T : Subgroup Γ) : Subgroup Γ :=
  ⨆ g : G, conjSub (g : Γ) (omegaOneCenterOf T)

@[expose] def zSub (T : Subgroup Γ) : Subgroup Γ := omegaOneCenterOf (baum T)

@[expose] def lSet (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {L | L < G ∧ baum T ≤ L ∧ ¬ L ≤ cStarIn G T}

@[expose] def bStarT (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | E ∈ btBlocksMaxT G T ∧ ¬ E ≤ cStarIn G T}

@[expose] def bStarG (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | ∃ g ∈ G, E ∈ bStarT G (conjSub g T)}

theorem cgsIn_map_le (c : Γ ≃* Γ) (G S : Subgroup Γ) :
    cgsIn (G.map c.toMonoidHom) (S.map c.toMonoidHom) ≤ (cgsIn G S).map c.toMonoidHom := by
  unfold cgsIn
  refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hCc x hx => ?_
  set C' : Subgroup Γ := C.comap c.toMonoidHom with hC'
  have hCC' : C'.map c.toMonoidHom = C :=
    Subgroup.map_comap_eq_self_of_surjective c.surjective C
  have hS' : (S.map c.toMonoidHom).comap c.toMonoidHom = S :=
    Subgroup.comap_map_eq_self_of_injective c.injective S
  have hC'S : C' ≤ S := by
    have := Subgroup.comap_mono (f := c.toMonoidHom) hCS
    rwa [hS'] at this
  have hC'0 : C' ≠ ⊥ := by
    intro h
    apply hC0
    rw [← hCC', h, Subgroup.map_bot]
  have hC'char : (C'.subgroupOf S).Characteristic := by
    have h1 := Nine.characteristic_subgroupOf_map_equiv c.symm hCc
    have e1 : (S.map c.toMonoidHom).map c.symm.toMonoidHom = S := by
      rw [Subgroup.map_map]
      have : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Γ := by
        ext y; simp
      rw [this, Subgroup.map_id]
    have e2 : C.map c.symm.toMonoidHom = C' := by
      rw [hC']
      exact (Subgroup.comap_equiv_eq_map_symm c C).symm
    rwa [e1, e2] at h1
  obtain ⟨hxG, hxN⟩ := hx
  obtain ⟨y, hyG, rfl⟩ := hxG
  refine ⟨y, ?_, by simp⟩
  have hle : G ⊓ Subgroup.normalizer (C' : Set Γ) ≤
      ⨆ (C : Subgroup Γ) (_ : C ≤ S) (_ : C ≠ ⊥) (_ : (C.subgroupOf S).Characteristic),
        G ⊓ Subgroup.normalizer (C : Set Γ) :=
    le_iSup_of_le C' (le_iSup_of_le hC'S (le_iSup_of_le hC'0 (le_iSup_of_le hC'char le_rfl)))
  refine hle ⟨hyG, ?_⟩
  have hxN' : c y ∈ Subgroup.normalizer (C : Set Γ) := hxN
  show y ∈ Subgroup.normalizer (C' : Set Γ)
  rw [Subgroup.mem_normalizer_iff] at hxN' ⊢
  intro h
  have := hxN' (c h)
  simpa [hC', Subgroup.mem_comap] using this

theorem cgsIn_map_equiv (c : Γ ≃* Γ) (G S : Subgroup Γ) :
    cgsIn (G.map c.toMonoidHom) (S.map c.toMonoidHom) = (cgsIn G S).map c.toMonoidHom := by
  refine le_antisymm (cgsIn_map_le c G S) ?_
  have h := cgsIn_map_le c.symm (G.map c.toMonoidHom) (S.map c.toMonoidHom)
  have e : ∀ H : Subgroup Γ, (H.map c.toMonoidHom).map c.symm.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    have : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Γ := by
      ext y; simp
    rw [this, Subgroup.map_id]
  have e' : ∀ H : Subgroup Γ, (H.map c.symm.toMonoidHom).map c.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    have : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id Γ := by
      ext y; simp
    rw [this, Subgroup.map_id]
  rw [e, e] at h
  have h2 := Subgroup.map_mono (f := c.toMonoidHom) h
  rwa [e'] at h2

theorem cStarIn_map_equiv (c : Γ ≃* Γ) (G T : Subgroup Γ) :
    cStarIn (G.map c.toMonoidHom) (T.map c.toMonoidHom) = (cStarIn G T).map c.toMonoidHom := by
  unfold cStarIn
  rw [Subgroup.map_sup, ← baum_map_mulEquiv, cgsIn_map_equiv, ← omegaOneCenterOf_map_mulEquiv,
    Nine.centralizer_map_equiv, Subgroup.map_inf _ _ c.toMonoidHom c.injective]

theorem cStarIn_conjSub (g : Γ) (G T : Subgroup Γ) :
    cStarIn (conjSub g G) (conjSub g T) = conjSub g (cStarIn G T) :=
  cStarIn_map_equiv (MulAut.conj g) G T

end CFSG.CGT.PushingUpLit.BHS7

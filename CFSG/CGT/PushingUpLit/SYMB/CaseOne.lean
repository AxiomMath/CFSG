module

public import CFSG.CGT.PushingUpLit.SYMB.IHBlock
public import CFSG.CGT.PushingUpLit.SYMB.Setting

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

theorem eq_alt_of_normalized {n : ℕ} (hn5 : 5 ≤ n) {X : Subgroup (Equiv.Perm (Fin n))}
    (hXA : X ≤ alternatingGroup (Fin n))
    (hXn : ∀ a ∈ alternatingGroup (Fin n), ∀ x ∈ X, a * x * a⁻¹ ∈ X) (hne : X ≠ ⊥) :
    X = alternatingGroup (Fin n) := by
  classical
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn5)
  have : (X.subgroupOf (alternatingGroup (Fin n))).Normal := ⟨fun x hx a => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hXn a a.2 x hx⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal (X.subgroupOf (alternatingGroup (Fin n))) with
    hbot | htop
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXA hx⟩ : ↥(alternatingGroup (Fin n))) ∈
        X.subgroupOf (alternatingGroup (Fin n)) := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · refine le_antisymm hXA fun a ha => ?_
    have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈ X.subgroupOf (alternatingGroup (Fin n)) := by
      rw [htop]
      trivial
    exact this

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}

theorem exists_block_alt_of_imgG_eq_top {m : ℕ} (hm : 2 ≤ m)
    {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))} {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))}
    {T' : Set (Equiv.Perm (Fin (2 * m + 1)))} (S : SymSetting G T V (2 * m + 1) φ ψ T')
    (hih : IHFor G) {L : Subgroup Γ} (hL : L ∈ lSet G T) (hLtop : imgG G φ L = ⊤) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧ F ≤ L ∧
      imgG G φ F = alternatingGroup (Fin (2 * m + 1)) := by
  classical
  have h5 : 5 ≤ 2 * m + 1 := by omega
  obtain ⟨hLG, hBL, hLC⟩ := hL
  obtain ⟨S₁, 𝒢, d⟩ := exists_ihData S.charTwo hih S.sylow ⟨hLG, hBL, hLC⟩
  obtain ⟨F, hF, hFn⟩ := d.exists_block_not_le hLC
  set N : Subgroup Γ := ⨆ E ∈ 𝒢, E with hNdef
  have hNL : N ≤ L := d.join_le
  have hNG : N ≤ G := hNL.trans hLG.le
  have hnormN : ∀ σ : Equiv.Perm (Fin (2 * m + 1)), ∀ x ∈ imgG G φ N,
      σ * x * σ⁻¹ ∈ imgG G φ N := by
    intro σ x hx
    have hσ : σ ∈ imgG G φ L := by
      rw [hLtop]
      trivial
    obtain ⟨l, hlG, hlL, rfl⟩ := mem_imgG.1 hσ
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 hx
    have hc : l * g * l⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (d.normal_join hlL) g).mp hgN
    refine mem_imgG.2 ⟨l * g * l⁻¹, hNG hc, hc, ?_⟩
    have e : (⟨l * g * l⁻¹, hNG hc⟩ : ↥G) = ⟨l, hlG⟩ * ⟨g, hgG⟩ * ⟨l, hlG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hNker : ¬ N ≤ kerG G φ := fun h =>
    d.join_not_le hLC (h.trans (sym_ker_le_cStarIn S))
  have hNne : imgG G φ N ≠ ⊥ := by
    intro hbot
    apply hNker
    intro g hg
    refine mem_kerG.2 ⟨hNG hg, ?_⟩
    have : φ ⟨g, hNG hg⟩ ∈ imgG G φ N := mem_imgG.2 ⟨g, hNG hg, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have : (imgG G φ N).Normal := ⟨fun x hx σ => hnormN σ x hx⟩
  have : Nontrivial ↥(imgG G φ N) := (Subgroup.nontrivial_iff_ne_bot _).2 hNne
  have hAN : alternatingGroup (Fin (2 * m + 1)) ≤ imgG G φ N :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simpa using h5) ‹_›
  have hNA : imgG G φ N ≤ alternatingGroup (Fin (2 * m + 1)) := by
    intro σ hσ
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 hσ
    exact map_mem_alternating_of_oResidualTwo d.residual_join hNG hgN
  have hNeq : imgG G φ N = alternatingGroup (Fin (2 * m + 1)) := le_antisymm hNA hAN
  have hFL : F ≤ L := (d.blocks F hF).le
  have hFG : F ≤ G := hFL.trans hLG.le
  have hFB : IsBTBlock G T F := d.isBTBlock_of_mem hLG.le hF hFn
  have hFNN : F ≤ N := le_iSup₂ (f := fun E (_ : E ∈ 𝒢) => E) F hF
  have hFA : imgG G φ F ≤ alternatingGroup (Fin (2 * m + 1)) := by
    intro σ hσ
    obtain ⟨g, hgG, hgF, rfl⟩ := mem_imgG.1 hσ
    exact map_mem_alternating_of_oResidualTwo hFB.residual hFG hgF
  have hFne : imgG G φ F ≠ ⊥ := by
    intro hbot
    apply hFn
    intro g hg
    apply sym_ker_le_cStarIn S
    refine mem_kerG.2 ⟨hFG hg, ?_⟩
    have : φ ⟨g, hFG hg⟩ ∈ imgG G φ F := mem_imgG.2 ⟨g, hFG hg, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hFnorm : ∀ a ∈ alternatingGroup (Fin (2 * m + 1)), ∀ x ∈ imgG G φ F,
      a * x * a⁻¹ ∈ imgG G φ F := by
    intro a ha x hx
    rw [← hNeq] at ha
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 ha
    obtain ⟨f, hfG, hfF, rfl⟩ := mem_imgG.1 hx
    have hc : g * f * g⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (d.normalizes_block hF hgN) f).mp hfF
    refine mem_imgG.2 ⟨g * f * g⁻¹, hFG hc, hc, ?_⟩
    have e : (⟨g * f * g⁻¹, hFG hc⟩ : ↥G) = ⟨g, hgG⟩ * ⟨f, hfG⟩ * ⟨g, hgG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  exact ⟨F, hFB, hFn, hFL, eq_alt_of_normalized h5 hFA hFnorm hFne⟩

end CFSG.CGT.PushingUpLit.SYMB

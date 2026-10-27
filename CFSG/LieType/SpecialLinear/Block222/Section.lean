module

public import CFSG.LieType.SpecialLinear.Block222.Factor
public import CFSG.LieType.SpecialLinear.EndNode.CoverDatum
public import CFSG.Quasithin.Background.SmithParabolic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.RootSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

@[expose] def blockFix222 {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) : Submodule k V :=
  fixSub ρ (blockRadical222 c F)

theorem blockFix222_stable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) :
    ∀ g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
        SpecialLinearGroup (Fin 2) F,
      ∀ w ∈ blockFix222 c F ρ, ρ (blockEmbed222 c F g) w ∈ blockFix222 c F ρ := by
  intro g w hw
  refine act_mem_fixSub ρ (S := blockRadical222 c F) (g := blockEmbed222 c F g) ?_ hw
  intro s hs
  have h := blockRadical222_normalized c F (m := (blockEmbed222 c F g)⁻¹)
    ⟨g⁻¹, by rw [map_inv]⟩ hs
  simpa only [map_inv, inv_inv] using h

@[expose] noncomputable def blockRestrict222 {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) :
    Representation k (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F) (blockFix222 c F ρ) :=
  restrictRep (ρ.comp (blockEmbed222 c F)) (blockFix222 c F ρ) (blockFix222_stable c F ρ)

private instance finite_coxeterGroup_A (n : ℕ) :
    Finite (coxeterMatrix (isFiniteType_A n)).Group :=
  finite_group (isFiniteType_A n)

theorem blockRestrict222_isSimple [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} (hρ : IsSimpleRep ρ)
    (hsplit : SplitOver k (curtisDatum (c + 3) F p).H)
    {y : V} (hyW : y ∈ blockFix222 c F ρ) (hy0 : y ≠ 0) :
    IsSimpleRep (blockRestrict222 c F ρ) := by
  have hne : blockFix222 c F ρ ≠ ⊥ := by
    intro hbot
    have hy : y ∈ (⊥ : Submodule k V) := by rw [← hbot]; exact hyW
    exact hy0 (by simpa using hy)
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hne, ?_⟩
  intro X hX
  let Y : Submodule k V := X.map (blockFix222 c F ρ).subtype
  have hY : Y ≤ fixSub ρ (blockRadical222 c F) := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hv
    exact x.2
  have hYP : ∀ m' ∈ (blockEmbed222 c F).range, ∀ v ∈ Y, ρ m' v ∈ Y := by
    intro m' hm' v hv
    obtain ⟨a, rfl⟩ := hm'
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨_, hX a x hx, rfl⟩
  have hsmith := (curtisDatum (c + 3) F p).eq_bot_or_fixSub_le
    (hsplit := hsplit) (ρ := ρ) hρ
    (N := blockRadical222 c F) (N' := blockRadicalLower222 c F)
    (P := (blockEmbed222 c F).range)
    (fun m hm x hx => blockRadical222_normalized c F hm hx)
    (fun m hm x hx => blockRadicalLower222_normalized c F hm hx)
    (blockRadicalLower222_le_L c F p)
    (curtisDatum_U_le_block222_sup c F p)
    (curtisDatum_L_le_block222_sup c F p) hY hYP
  rcases hsmith with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxv : (x : V) ∈ Y := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxv
    exact Subtype.ext (by simpa using hxv)
  · right
    rw [Submodule.eq_top_iff']
    intro w
    have hwY : (w : V) ∈ Y := htop w.2
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hwY
    exact (Subtype.ext hxw) ▸ hx

theorem mem_blockFix222_of_isCoverType [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) :
    y ∈ blockFix222 c F ρ := by
  rw [blockFix222, mem_fixSub]
  intro g hg
  have hgU : g ∈ (curtisDatum (c + 3) F p).U := blockRadical222_le_U c F p hg
  have hyU := ht.1
  rw [CurtisDatum.mem_fixU] at hyU
  rw [coverId_datum_U (c + 3) F p] at hyU
  exact hyU g hgU

theorem blockRestrict222_isSimple_of_isCoverType [Finite F] (p : ℕ) [Fact p.Prime]
    [CharP F p] {k V : Type*} [Field k] [CharP k p] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (hρ : IsSimpleRep ρ) (hsplit : SplitOver k (curtisDatum (c + 3) F p).H)
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) :
    IsSimpleRep (blockRestrict222 c F ρ) :=
  blockRestrict222_isSimple c F p hρ hsplit
    (mem_blockFix222_of_isCoverType c F p ht) ht.2.1

end

end CFSG.LieType.SpecialLinear

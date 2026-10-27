module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48LayerY
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48SL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 Dstd Bsub exists_map_conj_Dstd
  isElemAbelian_Dstd Bsub_le_Dstd card_Bsub card_Dstd μ3 card_μ3 torusSU4)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K)

section Row28

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_adapted_model (τ : ↥L ≃* SU4) {E : Subgroup G} (hEL : E ≤ L)
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3) :
    ∃ τ' : ↥L ≃* SU4, (E.subgroupOf L).map τ'.toMonoidHom = Dstd := by
  have hEsub : IsElemAbelian 3 (E.subgroupOf L) := CatB.isElemAbelian_subgroupOf hE
  have hP : CFSG.Assembly.IsElemAbelian 3 ((E.subgroupOf L).map τ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hEsub τ.toMonoidHom
  have hPc : Nat.card ((E.subgroupOf L).map τ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective τ.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hc]
    norm_num
  obtain ⟨g, hg⟩ := exists_map_conj_Dstd hP hPc
  refine ⟨τ.trans (MulAut.conj g⁻¹), ?_⟩
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxP : τ x ∈ (E.subgroupOf L).map τ.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hg] at hxP
    obtain ⟨d, hd, hdx⟩ := hxP
    have : (τ.trans (MulAut.conj g⁻¹)) x = d := by
      change g⁻¹ * τ x * g⁻¹⁻¹ = d
      rw [← hdx]
      change g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d
      group
    exact this ▸ hd
  · intro hd
    have : g * d * g⁻¹ ∈ (E.subgroupOf L).map τ.toMonoidHom := by
      rw [hg]; exact ⟨d, hd, rfl⟩
    obtain ⟨x, hx, hxd⟩ := this
    refine ⟨x, hx, ?_⟩
    change g⁻¹ * τ x * g⁻¹⁻¹ = d
    have h2 : τ x = g * d * g⁻¹ := hxd
    rw [h2]
    group

theorem i8U48At_holds (G : Type) [Group G] [Finite G] : I8U48At G := by
  intro X L E₁ hL hcat hE₁L hE₁ hE₁c
  obtain ⟨τ, hτ⟩ := exists_adapted_model (lModel hcat) hE₁L hE₁ hE₁c
  obtain ⟨t, ht⟩ := exists_ne_one_mu3
  set f : SU4 →* G := L.subtype.comp τ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := fun a b h => τ.symm.injective (Subtype.ext h)
  have hDE : ∀ d ∈ Dstd, f d ∈ E₁ := by
    intro d hd
    rw [← hτ] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    have : f (τ.toMonoidHom x) = x := by simp [hfdef]
    rw [this]
    exact Subgroup.mem_subgroupOf.1 hx
  have hyD : yStd t ∈ Dstd := ⟨fun _ => t, rfl⟩
  set y : G := f (yStd t) with hy
  have hyL : y ∈ L := (τ.symm (yStd t)).2
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, yStd_pow_three, map_one]
  have hτy : τ.toMonoidHom ⟨y, hyL⟩ = yStd t := by simp [hy, hfdef]
  have hker : ¬ 3 ∣ Nat.card τ.toMonoidHom.ker := by
    have : τ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 τ.injective
    rw [this]
    simp
  obtain ⟨J, hJ, hJl, himg, ⟨ε⟩⟩ := layerY τ.toMonoidHom τ.surjective hker ht hyL hy3 hτy
  have hJle : J ≤ L := hJ.1.trans inf_le_left
  have hJf : J = Jblk.map f := by
    ext g
    constructor
    · intro hg
      have hgL : g ∈ L := hJle hg
      refine ⟨τ.toMonoidHom ⟨g, hgL⟩, ?_, by simp [hfdef]⟩
      rw [← himg]
      exact ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← himg] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      have : f (τ.toMonoidHom x) = x := by simp [hfdef]
      rw [this]
      exact Subgroup.mem_subgroupOf.1 hx
  have hyE₁ : y ∈ E₁ := hDE _ hyD
  have hy1 : y ≠ 1 := by
    intro h1
    apply yStd_ne_one ht
    apply hf
    rw [← hy, h1, map_one]
  refine ⟨y, hyE₁, hy1, (Bsub 0).map f, ?_, ?_, ?_, ⟨yStd t, yStd_mem_Bsub t, rfl⟩, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hDE b (Bsub_le_Dstd 0 hb)
  · exact CFSG.SectionRank.isElemAbelian_map
      (isElemAbelian_mono isElemAbelian_Dstd (Bsub_le_Dstd 0)) f
  · rw [Subgroup.card_map_of_injective hf, card_Bsub_zero]
    norm_num
  · subst hJl
    exact ⟨hJ, catalogIs_psimple_of_pquot ε, layer_third f hf _ hJf⟩

end Row28

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

section Main

theorem delBlockGenProp
    : DelBlockGenProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore hall hImage
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hfam := del_family_data hS ctx.comps ctx.deleted
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hLSnB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).1 (hImage.normal_B j)
  have hJLS : thompsonJ R ≤ LS := (thompsonJ_le_baum' R).trans le_sup_right
  refine ⟨fun i => ?_, fun i => ?_⟩
  ·
    obtain ⟨Fs, P, hP⟩ := hall i
    have hres := hP.loc.res
    set B := oddOrderSubgroup P with hB
    have hPH0 : P ≤ delH0 R V hX Fs := hP.loc.minimal.le
    have hPLS : P ≤ LS := hPH0.trans inf_le_left
    have hBP : B ≤ P := oddOrderSubgroup_le P
    have hBGi : B ≤ LS ⊓ rhoPreimage V ⊤ hX (Lc i) := by
      intro b hb
      refine ⟨hPLS (hBP hb), (mem_rhoPreimage_top_iff hX _ b).2 ?_⟩
      have h1 : MulAut.conjNormal (H := V) b ∈ autOn B V := by
        rw [autOn_eq_map_conjNormal]
        exact Subgroup.mem_map_of_mem _ hb
      rw [hres.image] at h1
      exact hP.loc.seed.le h1
    have hBBi : B ≤ blockOf (⊤ : Subgroup G) R V hX (Lc i) := by
      have h1 := oddOrderSubgroup_mono hBGi
      rwa [hB, oddOrderSubgroup_idem] at h1
    exact le_antisymm (hres.gen.symm.le.trans (sup_le_sup_right hBBi R)) le_top
  ·
    obtain ⟨Fs, P, hP⟩ := hall i
    have hres := hP.loc.res
    set Bi := blockOf (⊤ : Subgroup G) R V hX (Lc i) with hBi
    set B := oddOrderSubgroup P with hB
    have hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS := hP.ker.kernel.2
    have hPH0 : P ≤ delH0 R V hX Fs := hP.loc.minimal.le
    have hPLS : P ≤ LS := hPH0.trans inf_le_left
    have hBP : B ≤ P := oddOrderSubgroup_le P
    have hBGi : B ≤ LS ⊓ rhoPreimage V ⊤ hX (Lc i) := by
      intro b hb
      refine ⟨hPLS (hBP hb), (mem_rhoPreimage_top_iff hX _ b).2 ?_⟩
      have h1 : MulAut.conjNormal (H := V) b ∈ autOn B V := by
        rw [autOn_eq_map_conjNormal]
        exact Subgroup.mem_map_of_mem _ hb
      rw [hres.image] at h1
      exact hP.loc.seed.le h1
    have hBBi : B ≤ Bi := by
      have h1 := oddOrderSubgroup_mono hBGi
      rwa [hB, oddOrderSubgroup_idem] at h1
    have hJn : thompsonJ R ≤ Subgroup.normalizer (Bi : Set G) := hJLS.trans (hLSnB i)
    have hDB : ⁅Bi, thompsonJ R⁆ ≤ Bi := commutator_le_of_le_normalizer hJn
    have hBiJ : Bi ≤ Subgroup.normalizer ((⁅Bi, thompsonJ R⁆ : Subgroup G) : Set G) :=
      le_sup_left.trans (le_normalizer_commutator Bi (thompsonJ R))
    have hDn : (⁅Bi, thompsonJ R⁆.subgroupOf Bi).Normal := normal_commutator_subgroupOf hJn
    have hBD : B ≤ ⁅Bi, thompsonJ R⁆ :=
      calc B = ⁅B, thompsonJ R⁆ := hres.perfect.symm
        _ ≤ ⁅Bi, thompsonJ R⁆ := Subgroup.commutator_mono hBBi le_rfl
    have himgBi : Bi.map (MulAut.conjNormal (H := V)) = Lc i := by
      rw [← autOn_eq_map_conjNormal]
      exact hImage.image i
    have hDle : (⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V)) ≤ Lc i :=
      himgBi ▸ Subgroup.map_mono hDB
    obtain ⟨e, -, -⟩ := hfam.alt i
    have hsimple : IsSimpleGroup ↥(Lc i) := by
      have := isSimpleGroup_alt_five
      exact e.isSimpleGroup
    have hNn : (((⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V))).subgroupOf (Lc i)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨d, hd, hdx⟩ := hx
      have hg : (g : MulAut V) ∈ Bi.map (MulAut.conjNormal (H := V)) := by
        rw [himgBi]
        exact g.2
      obtain ⟨b, hb, hbg⟩ := hg
      refine ⟨b * d * b⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hBiJ hb) d).1 hd
      · rw [map_mul, map_mul, map_inv, hbg, hdx]
        rfl
    have hNne : (⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V)) ≠ ⊥ := by
      intro hbot
      have h1 : Fs ≤ (⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V)) := by
        rw [← hres.image, autOn_eq_map_conjNormal]
        exact Subgroup.map_mono hBD
      rw [hbot, le_bot_iff] at h1
      have h3 := hP.loc.seed.card
      rw [h1, Subgroup.card_bot] at h3
      exact absurd h3 (by norm_num)
    have hNtop : (⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V)) = Lc i := by
      have := hNn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V))).subgroupOf (Lc i)) with h | h
      · exfalso
        apply hNne
        rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hDle hx⟩ : ↥(Lc i)) ∈
            ((⁅Bi, thompsonJ R⁆).map (MulAut.conjNormal (H := V))).subgroupOf (Lc i) :=
          Subgroup.mem_subgroupOf.2 hx
        rw [h, Subgroup.mem_bot] at hx'
        exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
      · exact le_antisymm hDle (Subgroup.subgroupOf_eq_top.1 h)
    have hodd : oddOrderSubgroup Bi = Bi := by
      rw [hBi]
      exact oddOrderSubgroup_idem _
    exact eq_of_map_le_of_two_kernel (MulAut.conjNormal (H := V)) (hBLS i) hDB hDn hodd
      (fun x hx h1 => two_elt_of_conjNormal_eq_one hker hx h1) (by rw [himgBi, hNtop])

end Main

end CFSG.QuasithinUnique.Setup.Lift

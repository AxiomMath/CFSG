module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Ext
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

namespace AE5

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

theorem phi_inv (F : ExitO2.Q8Fam G P) (I : AEIdent P 5) {L : Subgroup G} (hL : L ∈ P) {u : G}
    (hu : IsUniqueInvolution L u) {α : Finset (Fin 5)} (h : α.card = 4) {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    I.φ ⟨u, le_pSpan hL hu.mem⟩ = zBar α h := by
  have h8 : ∀ L ∈ P, Nat.card ↥L = 8 := fun L hL => (F.card L hL).trans (by norm_num)
  have hm : 5 ≤ 5 := le_rfl
  have hmem : I.φ ⟨u, le_pSpan hL hu.mem⟩ ∈ memBar α h b := by
    rw [← hlab]
    exact I.mem_map hL hu.mem
  have hsq : I.φ ⟨u, le_pSpan hL hu.mem⟩ * I.φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan P)) = 1 :=
      Subtype.ext hu.sq
    rw [this, map_one]
  rcases eq_of_mem_memBar_mul_self hm hmem hsq with h1 | h1
  · exfalso
    refine hu.ne_one (phi_injOn I.φ hm hL (h8 L hL) hlab hu.mem L.one_mem ?_)
    exact h1.trans (map_one I.φ).symm
  · exact h1

theorem same_of_image (F : ExitO2.Q8Fam G P) (I : AEIdent P 5) {L M : Subgroup G} (hL : L ∈ P)
    (hM : M ∈ P) (hLM : (L.subgroupOf (pSpan P)).map I.φ = (M.subgroupOf (pSpan P)).map I.φ) :
    L = M := by
  obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
  refine ExitO2.fam_eq_of_phi_mem I.φ F (le_refl 5) I.ker_le (fun L hL => I.label L hL) hL hM haL ha2 ?_
  rw [← hLM]
  exact I.mem_map hL haL

theorem theta_fix (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) {L : Subgroup G} (hL : L ∈ P)
    (hfix : ∀ y : ↥(pSpan P), (y : G) ∈ L → ψ y = y) {α : Finset (Fin 5)} {h : α.card = 4}
    {c : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h c) :
    ∀ y (hy : y ∈ memBar α h c), inducedAutExt I ψ ⟨y, memBar_le_aeModel α h c hy⟩ =
      ⟨y, memBar_le_aeModel α h c hy⟩ := by
  intro y hy
  rw [← hlab] at hy
  obtain ⟨l, hl, hly⟩ := hy
  have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have e : (⟨y, memBar_le_aeModel α h c (by rw [← hlab]; exact ⟨l, hl, hly⟩)⟩ :
      ↥(TL4.aeModel 5)) = I.toModel l := Subtype.ext hly.symm
  rw [e, inducedAutExt_apply, hfix l hl']


theorem psi_dichotomy (F : ExitO2.Q8Fam G P) (I : AEIdent P 5)
    (ψ : MulAut ↥(pSpan P))
    (hψP : ∀ M ∈ P, ∃ M' ∈ P,
      (M.subgroupOf (pSpan P)).map ψ.toMonoidHom = M'.subgroupOf (pSpan P))
    {J J' : Subgroup G} (hJ : J ∈ P) (hJ' : J' ∈ P) (hne : J ≠ J') {t : G}
    (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t)
    (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ y = y)
    (hfixJ' : ∀ y : ↥(pSpan P), (y : G) ∈ J' → ψ y = y) :
    (∀ y, ψ y = y) ∨ (∀ y : ↥(pSpan P), ((ψ y : ↥(pSpan P)) : G) = t * y * t⁻¹) := by
  classical
  obtain ⟨α, h, b, hl⟩ := I.label J hJ
  obtain ⟨α', h', b', hl'⟩ := I.label J' hJ'
  have hz := phi_inv F I hJ ht h hl
  have hz' := phi_inv F I hJ' ht' h' hl'
  obtain rfl : α = α' := eq_of_zBar_eq (by norm_num) (hz.symm.trans hz')
  have hbb : b ≠ b' := by
    intro e
    apply hne
    refine same_of_image F I hJ hJ' ?_
    rw [hl, hl', e]
  set θ := inducedAutExt I ψ with hθ
  have hperm : ∀ (γ : Finset (Fin 5)) (hγ : γ.card = 4) (c : Bool),
      ∃ (γ' : Finset (Fin 5)) (hγ' : γ'.card = 4) (c' : Bool),
        ((memBar γ hγ c).subgroupOf (TL4.aeModel 5)).map θ.toMonoidHom =
          (memBar γ' hγ' c').subgroupOf (TL4.aeModel 5) := by
    intro γ hγ c
    obtain ⟨L, hL, hLl⟩ := I.label_surj γ hγ c
    obtain ⟨M', hM', hM'e⟩ := hψP L hL
    obtain ⟨γ', hγ', c', hM'l⟩ := I.label M' hM'
    refine ⟨γ', hγ', c', ?_⟩
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨⟨g₀, hg₀⟩, hg₀m, hθg⟩
      have hg₀m' : g₀ ∈ memBar γ hγ c := hg₀m
      rw [← hLl] at hg₀m'
      obtain ⟨l, hl, hly⟩ := hg₀m'
      have e : (⟨g₀, hg₀⟩ : ↥(TL4.aeModel 5)) = I.toModel l := Subtype.ext hly.symm
      rw [e, inducedAutExt_apply] at hθg
      have hψl : ψ l ∈ (M'.subgroupOf (pSpan P)) := by
        rw [← hM'e]
        exact ⟨l, hl, rfl⟩
      have : (g : AEQ 5) ∈ (M'.subgroupOf (pSpan P)).map I.φ := by
        refine ⟨ψ l, hψl, ?_⟩
        have := congrArg Subtype.val hθg
        exact this
      rw [hM'l] at this
      exact this
    · intro hg'
      have hg'' : g ∈ (M'.subgroupOf (pSpan P)).map I.φ := by rw [hM'l]; exact hg'
      obtain ⟨m, hm, hmy⟩ := hg''
      rw [← hM'e] at hm
      obtain ⟨l, hl, hlm⟩ := hm
      have hlmem : (I.φ l) ∈ memBar γ hγ c := by
        rw [← hLl]
        exact ⟨l, hl, rfl⟩
      refine ⟨I.toModel l, hlmem, ?_⟩
      rw [inducedAutExt_apply]
      apply Subtype.ext
      show I.φ (ψ l) = g
      rw [show ψ l = m from hlm, hmy]
  have hfixα : ∀ c, ∀ y (hy : y ∈ memBar α h c), θ ⟨y, memBar_le_aeModel α h c hy⟩ =
      ⟨y, memBar_le_aeModel α h c hy⟩ := by
    intro c y hy
    have hc : c = b ∨ c = b' := by
      revert hbb
      cases b <;> cases b' <;> cases c <;> simp
    rcases hc with rfl | rfl
    · exact theta_fix I ψ hJ hfixJ hl y hy
    · exact theta_fix I ψ hJ' hfixJ' hl' y hy
  have hmodel := aut_dichotomy θ hperm α h (hfixα true) (hfixα false)
  have hζ : I.toModel ⟨t, le_pSpan hJ ht.mem⟩ = ⟨zBar α h, zBar_mem_aeModel α h⟩ :=
    Subtype.ext (phi_inv F I hJ ht h hl)
  rcases hmodel with h1 | h1
  · left
    have hcent : ∀ g : ↥(pSpan P), g⁻¹ * ψ g ∈ Subgroup.center ↥(pSpan P) := by
      intro g
      apply I.ker_le
      rw [← I.ker_toModel, MonoidHom.mem_ker, map_mul, map_inv]
      have : θ (I.toModel g) = I.toModel (ψ g) := inducedAutExt_apply I ψ g
      rw [← this, h1, MulAut.one_apply, inv_mul_cancel]
    exact fixed_of_cent F.gen F.trans hJ ψ.toMonoidHom hcent hfixJ
  · right
    set ζ : ↥(pSpan P) := ⟨t, le_pSpan hJ ht.mem⟩ with hζdef
    set ψ' : ↥(pSpan P) →* ↥(pSpan P) :=
      (MulAut.conj ζ⁻¹).toMonoidHom.comp ψ.toMonoidHom with hψ'
    have hψ'y : ∀ y, ψ' y = ζ⁻¹ * ψ y * ζ := fun y => by
      simp [hψ']
    have hcent : ∀ g : ↥(pSpan P), g⁻¹ * ψ' g ∈ Subgroup.center ↥(pSpan P) := by
      intro g
      apply I.ker_le
      rw [← I.ker_toModel, MonoidHom.mem_ker, hψ'y, map_mul, map_mul, map_mul, map_inv, map_inv,
        hζ, ← inducedAutExt_apply I ψ g]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [h1 (I.toModel g)]
      group
    have hfix' : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ' y = y := by
      intro y hy
      rw [hψ'y, hfixJ y hy]
      have hc : (y : G) * t = t * y := TwinE4Perf.commute_of_inv ht hy
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hζdef]
      have e1 : t⁻¹ * (y : G) * t = t⁻¹ * ((y : G) * t) := by group
      rw [e1, hc]
      group
    have hall := fixed_of_cent F.gen F.trans hJ ψ' hcent hfix'
    intro y
    have h2 := hall y
    rw [hψ'y] at h2
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hζdef] at h3
    calc ((ψ y : ↥(pSpan P)) : G) = t * (t⁻¹ * (ψ y : G) * t) * t⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [h3]

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

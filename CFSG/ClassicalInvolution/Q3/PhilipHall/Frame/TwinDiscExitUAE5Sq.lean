module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Model6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Ext
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

namespace AE5

section ExtN

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

@[expose] noncomputable def inducedHomN (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) :
    ↥(TL4.aeModel n) →* ↥(TL4.aeModel n) :=
  (QuotientGroup.lift I.toModel.ker (I.toModel.comp ψ.toMonoidHom) (by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, I.ker_toModel]
    rw [I.ker_toModel] at hx
    exact I.center_le_ker hn (psi_center ψ (I.ker_le hx)))).comp
    (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm.toMonoidHom

theorem inducedHomN_apply (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) (x : ↥(pSpan P)) :
    inducedHomN hn I ψ (I.toModel x) = I.toModel (ψ x) := by
  simp only [inducedHomN, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm
      (I.toModel x) = (x : ↥(pSpan P) ⧸ I.toModel.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this, QuotientGroup.lift_mk]
  rfl

theorem inducedHomN_injective (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) :
    Function.Injective (inducedHomN hn I ψ) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  obtain ⟨x, rfl⟩ := I.toModel_surjective m
  rw [inducedHomN_apply] at hm
  have hk : ψ x ∈ I.φ.ker := by rw [← I.ker_toModel]; exact hm
  have hc := psi_center ψ.symm (I.ker_le hk)
  rw [MulEquiv.symm_apply_apply] at hc
  have hx := I.center_le_ker hn hc
  rw [← I.ker_toModel] at hx
  exact hx

@[expose] noncomputable def inducedAutN (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) :
    MulAut ↥(TL4.aeModel n) :=
  MulEquiv.ofBijective (inducedHomN hn I ψ)
    ⟨inducedHomN_injective hn I ψ, Finite.injective_iff_surjective.mp (inducedHomN_injective hn I ψ)⟩

theorem inducedAutN_apply (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) (x : ↥(pSpan P)) :
    inducedAutN hn I ψ (I.toModel x) = I.toModel (ψ x) :=
  inducedHomN_apply hn I ψ x


end ExtN

section SqMain

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

theorem phi_invN (F : ExitO2.Q8Fam G P) (hn : 5 ≤ n) (I : AEIdent P n) {L : Subgroup G} (hL : L ∈ P) {u : G}
    (hu : IsUniqueInvolution L u) {α : Finset (Fin n)} (h : α.card = 4) {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    I.φ ⟨u, le_pSpan hL hu.mem⟩ = zBar α h := by
  have h8 : ∀ L ∈ P, Nat.card ↥L = 8 := fun L hL => (F.card L hL).trans (by norm_num)
  have hm : 5 ≤ n := hn
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

theorem same_of_imageN (F : ExitO2.Q8Fam G P) (hn : 5 ≤ n) (I : AEIdent P n) {L M : Subgroup G} (hL : L ∈ P)
    (hM : M ∈ P) (hLM : (L.subgroupOf (pSpan P)).map I.φ = (M.subgroupOf (pSpan P)).map I.φ) :
    L = M := by
  obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
  refine ExitO2.fam_eq_of_phi_mem I.φ F hn I.ker_le (fun L hL => I.label L hL) hL hM haL ha2 ?_
  rw [← hLM]
  exact I.mem_map hL haL

theorem theta_fixN (hn : 5 ≤ n) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) {L : Subgroup G} (hL : L ∈ P)
    (hfix : ∀ y : ↥(pSpan P), (y : G) ∈ L → ψ y = y) {α : Finset (Fin n)} {h : α.card = 4}
    {c : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h c) :
    ∀ y (hy : y ∈ memBar α h c), inducedAutN hn I ψ ⟨y, memBar_le_aeModel α h c hy⟩ =
      ⟨y, memBar_le_aeModel α h c hy⟩ := by
  intro y hy
  rw [← hlab] at hy
  obtain ⟨l, hl, hly⟩ := hy
  have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have e : (⟨y, memBar_le_aeModel α h c (by rw [← hlab]; exact ⟨l, hl, hly⟩)⟩ :
      ↥(TL4.aeModel n)) = I.toModel l := Subtype.ext hly.symm
  rw [e, inducedAutN_apply hn, hfix l hl']



theorem tail_sq (hn : 5 ≤ n) (F : ExitO2.Q8Fam G P) (I : AEIdent P n) (Ψ : MulAut ↥(pSpan P))
    (θ : MulAut ↥(TL4.aeModel n)) (hθ : ∀ y, θ (I.toModel y) = I.toModel (Ψ y)) {J : Subgroup G}
    (hJ : J ∈ P) {t : G} (ht : IsUniqueInvolution J t) {α : Finset (Fin n)} {h : α.card = 4}
    (hζ : I.toModel ⟨t, le_pSpan hJ ht.mem⟩ = ⟨zBar α h, zBar_mem_aeModel α h⟩)
    (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → Ψ y = y)
    (hmodel : θ = 1 ∨ ∀ g : ↥(TL4.aeModel n), ((θ g : ↥(TL4.aeModel n)) : AEQ n) =
      zBar α h * g * (zBar α h)⁻¹) :
    (∀ y, Ψ y = y) ∨ (∀ y : ↥(pSpan P), ((Ψ y : ↥(pSpan P)) : G) = t * y * t⁻¹) := by
  rcases hmodel with h1 | h1
  · left
    have hcent : ∀ g : ↥(pSpan P), g⁻¹ * Ψ g ∈ Subgroup.center ↥(pSpan P) := by
      intro g
      apply I.ker_le
      rw [← I.ker_toModel, MonoidHom.mem_ker, map_mul, map_inv]
      rw [← hθ g, h1, MulAut.one_apply, inv_mul_cancel]
    exact fixed_of_cent F.gen F.trans hJ Ψ.toMonoidHom hcent hfixJ
  · right
    set ζ : ↥(pSpan P) := ⟨t, le_pSpan hJ ht.mem⟩ with hζdef
    set ψ' : ↥(pSpan P) →* ↥(pSpan P) :=
      (MulAut.conj ζ⁻¹).toMonoidHom.comp Ψ.toMonoidHom with hψ'
    have hψ'y : ∀ y, ψ' y = ζ⁻¹ * Ψ y * ζ := fun y => by
      simp [hψ']
    have hcent : ∀ g : ↥(pSpan P), g⁻¹ * ψ' g ∈ Subgroup.center ↥(pSpan P) := by
      intro g
      apply I.ker_le
      rw [← I.ker_toModel, MonoidHom.mem_ker, hψ'y, map_mul, map_mul, map_mul, map_inv, map_inv,
        hζ, ← hθ g]
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
    calc ((Ψ y : ↥(pSpan P)) : G) = t * (t⁻¹ * (Ψ y : G) * t) * t⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [h3]

theorem psi_sq_dichotomy (hn : n = 5 ∨ n = 6) (F : ExitO2.Q8Fam G P)
    (I : AEIdent P n) (ψ : MulAut ↥(pSpan P))
    (hψP : ∀ M ∈ P, ∃ M' ∈ P,
      (M.subgroupOf (pSpan P)).map ψ.toMonoidHom = M'.subgroupOf (pSpan P))
    {J J' : Subgroup G} (hJ : J ∈ P) (hJ' : J' ∈ P) (hne : J ≠ J') {t : G}
    (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t)
    (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ y = y)
    (hfixJ' : ∀ y : ↥(pSpan P), (y : G) ∈ J' → ψ y = y) :
    (∀ y, ψ (ψ y) = y) ∨ (∀ y : ↥(pSpan P), ((ψ (ψ y) : ↥(pSpan P)) : G) = t * y * t⁻¹) := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  classical
  obtain ⟨α, h, b, hl⟩ := I.label J hJ
  obtain ⟨α', h', b', hl'⟩ := I.label J' hJ'
  have hz := phi_invN F hn5 I hJ ht h hl
  have hz' := phi_invN F hn5 I hJ' ht' h' hl'
  obtain rfl : α = α' := eq_of_zBar_eq (by omega) (hz.symm.trans hz')
  have hbb : b ≠ b' := by
    intro e
    apply hne
    refine same_of_imageN F hn5 I hJ hJ' ?_
    rw [hl, hl', e]
  set θ := inducedAutN hn5 I ψ with hθ
  have hperm : ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c : Bool),
      ∃ (γ' : Finset (Fin n)) (hγ' : γ'.card = 4) (c' : Bool),
        ((memBar γ hγ c).subgroupOf (TL4.aeModel n)).map θ.toMonoidHom =
          (memBar γ' hγ' c').subgroupOf (TL4.aeModel n) := by
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
      have e : (⟨g₀, hg₀⟩ : ↥(TL4.aeModel n)) = I.toModel l := Subtype.ext hly.symm
      rw [e, inducedAutN_apply hn5] at hθg
      have hψl : ψ l ∈ (M'.subgroupOf (pSpan P)) := by
        rw [← hM'e]
        exact ⟨l, hl, rfl⟩
      have : (g : AEQ n) ∈ (M'.subgroupOf (pSpan P)).map I.φ := by
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
      rw [inducedAutN_apply hn5]
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
    · exact theta_fixN hn5 I ψ hJ hfixJ hl y hy
    · exact theta_fixN hn5 I ψ hJ' hfixJ' hl' y hy
  have hmodel := aut_sq hn θ hperm α h (hfixα true) (hfixα false)
  have hζ : I.toModel ⟨t, le_pSpan hJ ht.mem⟩ = ⟨zBar α h, zBar_mem_aeModel α h⟩ :=
    Subtype.ext (phi_invN F hn5 I hJ ht h hl)
  have hθθ : ∀ y, (θ * θ) (I.toModel y) = I.toModel ((ψ * ψ) y) := by
    intro y
    show θ (θ (I.toModel y)) = I.toModel (ψ (ψ y))
    rw [hθ, inducedAutN_apply hn5, inducedAutN_apply hn5]
  have hmodel' : θ * θ = 1 ∨ ∀ g : ↥(TL4.aeModel n), (((θ * θ) g : ↥(TL4.aeModel n)) : AEQ n) =
      zBar α h * g * (zBar α h)⁻¹ := by
    rcases hmodel with h1 | h1
    · left
      exact MulEquiv.ext h1
    · right
      exact h1
  exact tail_sq hn5 F I (ψ * ψ) (θ * θ) hθθ hJ ht hζ
    (fun y hy => by
      show ψ (ψ y) = y
      rw [hfixJ y hy, hfixJ y hy]) hmodel'

end SqMain

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

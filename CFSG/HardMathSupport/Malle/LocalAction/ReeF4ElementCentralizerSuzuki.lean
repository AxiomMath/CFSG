module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerSplit

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Matrix

section B2Equiv

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

theorem B2_fixed_mulEquiv_suzuki (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    Nonempty ((B2Q L ⊓ twistedFixed D.F n' : Subgroup (ModGL ReeTag.F4.tag L)) ≃*
      suzukiGroup a K) := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨ω, hω, hε1, hε2⟩ := b2_exists_eps hstab
  have hεW := wordProd_mem_parabolicWeylGroup_b2 (b2Words_letters ω hω)
  set ε := (coxeterSystem ReeTag.F4.tag).wordProd ω with hε
  set m := canonicalRep (coxeterSystem ReeTag.F4.tag) L ε with hm
  have hmQ : m ∈ B2Q L := canonicalRep_mem_subsystemGroup hεW
  have heq : ∀ g ∈ B2Q L, twistMap D.F n' g = twistMap D.F m g := fun g hg =>
    twist_eq_on_B2Q D hperm hε1 hε2 hg
  obtain ⟨S₀, hS₀, hLang⟩ := antiSp_lang_aut L a
  let mQ : B2Q L := ⟨m, hmQ⟩
  let M : antiSp L := B2eQ L mQ
  obtain ⟨h, hh⟩ := hLang M
  let Fm : B2Q L →* B2Q L := (MulAut.conj mQ).toMonoidHom.comp (B2Ftilde D)
  have hFm : ∀ x, B2eQ L (Fm x) = M * S₀ (B2eQ L x) * M⁻¹ := by
    intro x
    show B2eQ L (mQ * B2Ftilde D x * mQ⁻¹) = _
    rw [map_mul, map_mul, map_inv, B2eQ_Ftilde D hS₀]
  let P' : Subgroup (ModGL ReeTag.F4.tag L) := B2Q L ⊓ twistedFixed D.F n'
  let P'₀ : Subgroup (B2Q L) := P'.subgroupOf (B2Q L)
  have hP'₀ : ∀ x : B2Q L, x ∈ P'₀ ↔ Fm x = x := by
    intro x
    have hxad := B2Q_le_adjointGroup x.2
    show (x : ModGL ReeTag.F4.tag L) ∈ P' ↔ _
    constructor
    · rintro ⟨-, -, hfix⟩
      refine Subtype.ext ?_
      show m * Fext D.F x * m⁻¹ = x
      have : twistMap D.F n' x = x := hfix
      rw [heq x x.2] at this
      exact this
    · intro hFx
      refine ⟨x.2, hxad, ?_⟩
      have h1 : m * Fext D.F x * m⁻¹ = x := congrArg Subtype.val hFx
      show twistMap D.F n' x = x
      rw [heq x x.2]
      exact h1
  let Y₁ : Subgroup (antiSp L) := P'₀.map (B2eQ L).toMonoidHom
  have hY₁ : ∀ A : antiSp L, A ∈ Y₁ ↔ M * S₀ A * M⁻¹ = A := by
    intro A
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hP'₀ x).1 hx
      have h2 := hFm x
      rw [h1] at h2
      exact h2.symm
    · intro hA
      refine ⟨(B2eQ L).symm A, (hP'₀ _).2 ?_, by simp⟩
      apply (B2eQ L).injective
      rw [hFm, MulEquiv.apply_symm_apply]
      exact hA
  have hY₂ : ∀ A : antiSp L, A ∈ Y₁.map (MulAut.conj h).toMonoidHom ↔ S₀ A = A := by
    intro A
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hB' := (hY₁ B).1 hB
      rw [hh] at hB'
      show S₀ (h * B * h⁻¹) = h * B * h⁻¹
      rw [map_mul, map_mul, map_inv]
      calc S₀ h * S₀ B * (S₀ h)⁻¹ = h * (h⁻¹ * S₀ h * S₀ B * (h⁻¹ * S₀ h)⁻¹) * h⁻¹ := by group
        _ = h * B * h⁻¹ := by rw [hB']
    · intro hA
      refine ⟨h⁻¹ * A * h, (hY₁ _).2 ?_, ?_⟩
      · rw [hh, map_mul, map_mul, map_inv, hA]
        group
      · show h * (h⁻¹ * A * h) * h⁻¹ = A
        group
  have hrange : Y₁.map (MulAut.conj h).toMonoidHom = (szEmbed hK (algebraMap K L)).range := by
    ext A
    rw [hY₂, fixed_S0_iff_mem_range hK hS₀]
  have hPle : P' ≤ B2Q L := inf_le_left
  have e1 : P' ≃* P'₀ := (Subgroup.subgroupOfEquivOfLe hPle).symm
  have e2 : P'₀ ≃* Y₁ := P'₀.equivMapOfInjective (B2eQ L).toMonoidHom (B2eQ L).injective
  have e3 : Y₁ ≃* Y₁.map (MulAut.conj h).toMonoidHom :=
    Y₁.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective
  have e4 : (Y₁.map (MulAut.conj h).toMonoidHom) ≃* (szEmbed hK (algebraMap K L)).range :=
    MulEquiv.subgroupCongr hrange
  have e5 : suzukiGroup a K ≃* (szEmbed hK (algebraMap K L)).range :=
    MonoidHom.ofInjective (szEmbed_injective hK _)
  exact ⟨((((e1.trans e2).trans e3).trans e4).trans e5.symm)⟩

omit [CharP L 2] in
theorem smul_dualRoot_mem_of_image_eq {S T : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w u : WeylGroup ReeTag.F4.tag)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    (hu : (fun α => u • α) '' S = T) {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ ∈ T) :
    (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈ T := by
  rw [← hu] at hγ ⊢
  obtain ⟨β, hβ, rfl⟩ := hγ
  have hβr := hS β hβ
  refine ⟨w • ReeTag.F4.dualRoot β, (hst β hβr).2 hβ, ?_⟩
  show u • (w • ReeTag.F4.dualRoot β) = _
  rw [ReeTag.dualRoot_smul u hβr, mul_smul, mul_smul, inv_smul_smul]

theorem rootSpan_inf_twistedFixed_mulEquiv_suzuki (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hbp : ∀ i, b i ^ 5 = 1) (hb1 : b ≠ 1)
    (hlong : (rootCharKernel b ∩ ReeTag.F4.longRoots).ncard = 4)
    (hshort : (rootCharKernel b ∩ ReeTag.F4.shortRoots).ncard = 4) :
    Nonempty ((rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) :
        Subgroup (ModGL ReeTag.F4.tag L)) ≃* suzukiGroup a K) := by
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, hΦ⟩ := exists_b2_conj hbp hb1 hw hlong hshort
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot Nat.prime_five (by norm_num) hbp hw hβ
  have hFN : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hperm : PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹)
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag f4B2Support := fun γ hγ =>
    smul_dualRoot_mem_of_image_eq hS w u hst hΦ hγ
  obtain ⟨e⟩ := B2_fixed_mulEquiv_suzuki D hK hperm hstab
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ, ← B2Q_eq_rootSpan] at hmap
  have e1 := (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)).equivMapOfInjective
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective
  exact ⟨(e1.trans (MulEquiv.subgroupCongr hmap)).trans e⟩

end B2Equiv
end CFSG.HardMathSupport.Malle.LocalAction

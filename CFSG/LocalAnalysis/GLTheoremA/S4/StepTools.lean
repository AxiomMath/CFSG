module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma45

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem gLBConj_iSup₂_eq (g : G) {H : Subgroup G} (F : G → Subgroup G) :
    GLBConj g (⨆ x ∈ H, F x) = ⨆ x ∈ H, GLBConj g (F x) := by
  unfold GLBConj
  simp only [Subgroup.map_iSup]

theorem le_normalizer_closureIn (I H : Subgroup G) :
    H ≤ Subgroup.normalizer (closureIn I H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq, closureIn_eq_iSup_gLBConj I H, gLBConj_iSup₂_eq]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_biSup (fun g => GLBConj g I) (H.mul_mem hg hh)
  · refine iSup₂_le fun g hg => ?_
    have e : GLBConj g I = GLBConj h (GLBConj (g * h⁻¹) I) := by
      rw [gLBConj_gLBConj, inv_mul_cancel_right]
    rw [e]
    exact le_biSup (fun g' => GLBConj h (GLBConj g' I)) (H.mul_mem hg (H.inv_mem hh))

theorem gLBConj_closureIn_of_commute {I A : Subgroup G} {b : G} (hb : ∀ a ∈ A, a * b = b * a) :
    GLBConj b (closureIn I A) = closureIn (GLBConj b I) A := by
  rw [closureIn_eq_iSup_gLBConj I A, closureIn_eq_iSup_gLBConj (GLBConj b I) A,
    gLBConj_iSup₂_eq]
  refine iSup_congr fun a => iSup_congr fun ha => ?_
  rw [gLBConj_gLBConj, gLBConj_gLBConj, hb a ha]

theorem isSubnormal_sSup_glaPComponent {p : ℕ} (hp : p.Prime) {C : Subgroup G}
    (𝓛 : Set (Subgroup G)) (h𝓛 : ∀ L ∈ 𝓛, GLAPComponent p C L) : IsSubnormal (sSup 𝓛) C := by
  have hKE : sSup 𝓛 ≤ GLAPLayer p C :=
    sSup_le fun L hL => le_sSup (s := {L | GLAPComponent p C L}) (h𝓛 L hL)
  have hEC : GLAPLayer p C ≤ C :=
    sSup_le fun L hL => (show GLAPComponent p C L from hL).1
  have hEN : GLAPLayer p C ≤ Subgroup.normalizer ((sSup 𝓛 : Subgroup G) : Set G) := by
    refine sSup_le fun X hX => ?_
    intro x hx
    refine mem_normalizer_sSup fun L hL => ?_
    by_cases hLX : L = X
    · subst hLX
      exact Subgroup.le_normalizer hx
    · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝓛 L hL)
        (show GLAPComponent p C X from hX) hLX hx
  have hCN : C ≤ Subgroup.normalizer (GLAPLayer p C : Set G) :=
    fun c hc => CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_glaPLayer (Subgroup.le_normalizer hc)
  exact IsSubnormal.step hKE ((Subgroup.normal_subgroupOf_iff_le_normalizer hKE).2 hEN)
    (IsSubnormal.step hEC ((Subgroup.normal_subgroupOf_iff_le_normalizer hEC).2 hCN)
      (IsSubnormal.refl C))

theorem commutator_mem_of_centMod_closureIn {p : ℕ} (hp : p.Prime) {C L A : Subgroup G} {c : G}
    (hL : GLAPComponent p C L) (hcC : c ∈ C) (hAC : A ≤ C) (hcA : ∀ a ∈ A, a * c = c * a)
    (hcL : CentMod p L c) :
    c ∈ Subgroup.normalizer (closureIn L A : Set G) ∧
      ∀ h ∈ closureIn L A ⊔ GLAPPrimeCoreOf p C, ⁅h, c⁆ ∈ GLAPPrimeCoreOf p C := by
  set O : Subgroup G := GLAPPrimeCoreOf p C with hO
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p C hcC
  have hcN : c ∈ Subgroup.normalizer (A : Set G) := by
    have key : ∀ x ∈ A, c * x * c⁻¹ = x := fun x hx => by
      rw [← hcA x hx, mul_inv_cancel_right]
    have key' : ∀ x ∈ A, c⁻¹ * x * c = x := fun x hx => by
      rw [mul_assoc, hcA x hx, inv_mul_cancel_left]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rwa [key y hy]
    · intro hy
      have h1 := key' _ hy
      rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at h1
      rw [h1]
      exact hy
  have hcNcl : c ∈ Subgroup.normalizer (closureIn L A : Set G) :=
    mem_normalizer_closureIn hcL.1 hcN
  let Z : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (O : Set G) ∧ ⁅g, c⁆ ∈ O}
      one_mem' := by
        show _ ∧ _
        refine ⟨Subgroup.one_mem _, ?_⟩
        rw [commutatorElement_one_left]
        exact O.one_mem
      mul_mem' := by
        intro g₁ g₂ h₁ h₂
        obtain ⟨n₁, k₁⟩ := h₁
        obtain ⟨n₂, k₂⟩ := h₂
        show _ ∧ _
        refine ⟨Subgroup.mul_mem _ n₁ n₂, ?_⟩
        have e : ⁅g₁ * g₂, c⁆ = g₁ * ⁅g₂, c⁆ * g₁⁻¹ * ⁅g₁, c⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 n₁ _).1 k₂) k₁
      inv_mem' := by
        intro g hg
        obtain ⟨n, k⟩ := hg
        show _ ∧ _
        refine ⟨Subgroup.inv_mem _ n, ?_⟩
        have e : ⁅g⁻¹, c⁆ = g⁻¹ * ⁅g, c⁆⁻¹ * g := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n) ⁅g, c⁆⁻¹).1
          (O.inv_mem k)
        rwa [inv_inv] at h }
  have hZ : closureIn L A ⊔ O ≤ Z := by
    refine sup_le ?_ ?_
    · rw [closureIn_eq_iSup_gLBConj L A]
      refine iSup₂_le fun a ha => ?_
      intro y hy
      show y ∈ Subgroup.normalizer (O : Set G) ∧ ⁅y, c⁆ ∈ O
      have hx : a * y * a⁻¹ ∈ L := mem_gLBConj.1 hy
      have haC : a ∈ C := hAC ha
      have hyC : y ∈ C := by
        have h1 : a⁻¹ * (a * y * a⁻¹) * a ∈ C :=
          C.mul_mem (C.mul_mem (C.inv_mem haC) (hL.1 hx)) haC
        rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
      have hLO : GLAPPrimeCoreOf p L ≤ O := by
        rw [hO, ← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
        exact inf_le_right
      have hxO : ⁅a * y * a⁻¹, c⁆ ∈ O :=
        hLO (hcL.2 (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers c)))
      have hconj : a * c * a⁻¹ = c := by rw [hcA a ha, mul_inv_cancel_right]
      have e := map_commutatorElement (MulAut.conj a) y c
      simp only [MulAut.conj_apply] at e
      rw [hconj] at e
      rw [← e] at hxO
      have haO : a ∈ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p C haC
      exact ⟨le_normalizer_glaPPrimeCoreOf p C hyC, (Subgroup.mem_normalizer_iff.1 haO _).2 hxO⟩
    · intro o ho
      show o ∈ Subgroup.normalizer (O : Set G) ∧ ⁅o, c⁆ ∈ O
      refine ⟨Subgroup.le_normalizer ho, ?_⟩
      have e : ⁅o, c⁆ = o * (c * o⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 hcO o⁻¹).1 (O.inv_mem ho))
  refine ⟨hcNcl, fun h hh => ?_⟩
  have hh' : h ∈ Subgroup.normalizer (O : Set G) ∧ ⁅h, c⁆ ∈ O := hZ hh
  exact hh'.2

theorem closureIn_le_closureIn_sup {p : ℕ} (hp : p.Prime) {C L I A : Subgroup G}
    (hL : GLAPComponent p C L) (hIsup : I ⊔ GLAPPrimeCoreOf p L = L) (hAC : A ≤ C) :
    closureIn L A ≤ closureIn I A ⊔ GLAPPrimeCoreOf p C := by
  have hLO : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
    exact inf_le_right
  rw [closureIn_eq_iSup_gLBConj L A]
  refine iSup₂_le fun a ha => ?_
  have hsplit : GLBConj a L = GLBConj a I ⊔ GLBConj a (GLAPPrimeCoreOf p L) := by
    calc GLBConj a L = GLBConj a (I ⊔ GLAPPrimeCoreOf p L) := by rw [hIsup]
      _ = GLBConj a I ⊔ GLBConj a (GLAPPrimeCoreOf p L) := by
        unfold GLBConj
        exact Subgroup.map_sup _ _ _
  have hI : GLBConj a I ≤ closureIn I A := by
    rw [closureIn_eq_iSup_gLBConj I A]
    exact le_biSup (fun g => GLBConj g I) ha
  have hO : GLBConj a (GLAPPrimeCoreOf p L) ≤ GLAPPrimeCoreOf p C := by
    have haN : GLBConj a (GLAPPrimeCoreOf p C) = GLAPPrimeCoreOf p C :=
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_glaPPrimeCoreOf p C (hAC ha))
    exact (gLBConj_mono (g := a) hLO).trans haN.le
  rw [hsplit]
  exact sup_le_sup hI hO

theorem pumpRel_facts {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {t t' : Triple G}
    (hrel : PumpRel p t t') :
    GLAPComponent p (Subgroup.centralizer ({t.2.1} : Set G) ⊓
        Subgroup.centralizer ({t'.2.1} : Set G))
      (GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G))) ∧
    GLAPComponent p (closureIn t'.2.2 t'.1 ⊓ Subgroup.centralizer ({t.2.1} : Set G))
      (GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G))) ∧
    GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G)) ≤ closureIn t'.2.2 t'.1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, -, hL⟩, ⟨hB', hx', hL'c⟩, hxB', -, hx'B', hx'L, hL'⟩ := hrel
  set L := t.2.2
  set L' := t'.2.2
  set x := t.2.1
  set x' := t'.2.1
  set B' := t'.1
  set Cx := Subgroup.centralizer ({x} : Set G)
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hB'Cx' : B' ≤ Cx' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := GLAPLayer p (L ⊓ Cx')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hICx : I ≤ Cx := hIL.trans hL.1
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Cx' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf Cx') hIc
  have hKx' : CFSG.Open.IsKGroup ↥Cx' :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1)
  have hxCx' : Subgroup.zpowers x ≤ Cx' := Subgroup.zpowers_le.2 (hB'Cx' hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Cx' hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'.1 hxB') I hI2
  set J := closureIn I (GLAPLayer p Cx')
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Cx' := hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p J K := fun K hK =>
    glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hL'𝒞 : L' ∈ 𝒞 := by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL' ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'.1
  have hJcl : J ≤ closureIn L' B' := by
    rw [hJ]
    refine iSup₂_le fun K hK => ?_
    obtain ⟨e, he, rfl⟩ := h𝒞tr L' hL'𝒞 K hK
    rw [closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun b => GLBConj b L') (Subgroup.zpowers_le.2 hxB' he)
  have hclN : closureIn L' B' ≤ Subgroup.normalizer (J : Set G) := by
    rw [closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun b hb => ?_
    have hbC : GLAPComponent p Cx' (GLBConj b L') := by
      have := glaPComponent_gLBConj hL'c b
      rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hB'Cx' hb))] at this
    intro k hk
    rw [hJ, ← sSup_eq_iSup]
    refine mem_normalizer_sSup fun K hK => ?_
    by_cases hKb : K = GLBConj b L'
    · rw [hKb]
      exact Subgroup.le_normalizer hk
    · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝒞c K hK) hbC
        hKb hk
  have hIJx : GLAPComponent p (J ⊓ Cx) I := by
    refine glaPComponent_of_le hp hI2 (le_inf hIJ hICx) ?_
    rw [hCzx]
    exact inf_le_inf_right _ hJCx'
  have hJxle : J ⊓ Cx ≤ closureIn L' B' ⊓ Cx := inf_le_inf_right _ hJcl
  have hsn : IsSubnormal (J ⊓ Cx) (closureIn L' B' ⊓ Cx) := by
    refine IsSubnormal.step hJxle ((Subgroup.normal_subgroupOf_iff_le_normalizer hJxle).2 ?_)
      (IsSubnormal.refl _)
    intro g hg
    have h1 : GLBConj g J = J := mem_normalizer_iff_gLBConj_eq.1 (hclN hg.1)
    have h2 : GLBConj g Cx = Cx := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
  have hIdiag : GLAPComponent p (closureIn L' B' ⊓ Cx) I :=
    glaPComponent_of_isSubnormal' hp hsn hIJx
  have hI1 : GLAPComponent p (Cx ⊓ Cx') I := by
    rw [inf_comm, ← hCzx]
    exact hI2
  exact ⟨hI1, hIdiag, hIJ.trans hJcl⟩

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdRed
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)

namespace AE5

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] def psi (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) :
    X →* ↥((aeSub 5).map (mkQ 5)) where
  toFun y := ⟨I.φ ⟨y, mem_pSpan hgen y⟩, by rw [← I.range_eq]; exact ⟨_, rfl⟩⟩
  map_one' := Subtype.ext (map_one I.φ)
  map_mul' a b := Subtype.ext (map_mul I.φ ⟨a, mem_pSpan hgen a⟩ ⟨b, mem_pSpan hgen b⟩)

theorem coe_psi (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (y : X) :
    ((psi hgen I y : ↥((aeSub 5).map (mkQ 5))) : AEQ 5) = I.φ ⟨y, mem_pSpan hgen y⟩ := rfl

theorem psi_surjective (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) :
    Function.Surjective (psi hgen I) := by
  rintro ⟨g, hg⟩
  rw [← I.range_eq] at hg
  obtain ⟨⟨y, hy⟩, rfl⟩ := hg
  exact ⟨y, rfl⟩

theorem mem_ker_psi (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {y : X} :
    y ∈ (psi hgen I).ker ↔ y ∈ Subgroup.center X := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hy
    exact mem_center_of_mem_ker hgen I (k := ⟨y, mem_pSpan hgen y⟩) (congrArg Subtype.val hy)
  · intro hy
    exact Subtype.ext (map_eq_one_of_mem_center hgen I hy)

theorem aut_mem_center (σ : MulAut X) {c : X} (hc : c ∈ Subgroup.center X) :
    σ c ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  obtain ⟨y, rfl⟩ := σ.surjective y
  rw [← map_mul, ← map_mul, hc y]

theorem ker_psi_map (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (σ : MulAut X) :
    (psi hgen I).ker.map (σ : X →* X) = (psi hgen I).ker := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (mem_ker_psi hgen I).mpr (aut_mem_center σ ((mem_ker_psi hgen I).mp hc))
  · intro hy
    exact ⟨σ.symm y, (mem_ker_psi hgen I).mpr (aut_mem_center σ.symm ((mem_ker_psi hgen I).mp hy)),
      σ.apply_symm_apply y⟩

@[expose] noncomputable def descAut (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (σ : MulAut X) :
    MulAut ↥((aeSub 5).map (mkQ 5)) :=
  (QuotientGroup.quotientKerEquivOfSurjective (psi hgen I) (psi_surjective hgen I)).symm.trans
    ((QuotientGroup.congr (psi hgen I).ker (psi hgen I).ker σ (ker_psi_map hgen I σ)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (psi hgen I) (psi_surjective hgen I)))

theorem descAut_psi (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (σ : MulAut X) (y : X) :
    descAut hgen I σ (psi hgen I y) = psi hgen I (σ y) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (psi hgen I) (psi_surjective hgen I)).symm
      (psi hgen I y) = (y : X ⧸ (psi hgen I).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [descAut, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

theorem map_psi (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (L : Subgroup X) :
    L.map (psi hgen I) =
      ((L.subgroupOf (pSpan Φ)).map I.φ).subgroupOf ((aeSub 5).map (mkQ 5)) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, mem_pSpan hgen l⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  · rintro ⟨⟨l, hlP⟩, hl, hlg⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, Subtype.ext hlg⟩

theorem map_descAut (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (σ : MulAut X) (L : Subgroup X) :
    (L.map (psi hgen I)).map (descAut hgen I σ).toMonoidHom =
      (L.map σ.toMonoidHom).map (psi hgen I) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun y => descAut_psi hgen I σ y

theorem map_mem_of_fix (hcl : ConjInvariant Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') {A : Subgroup X} (hA : A ∈ Φ)
    {σ : MulAut X} (hσ : ∀ k ∈ A, σ k = k) : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ := by
  intro L hL
  obtain ⟨g, rfl⟩ := htr A hA L hL
  have hAσ : A.map σ.toMonoidHom = A := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩
      show σ k' ∈ A
      rw [hσ k' hk']
      exact hk'
    · intro hk
      exact ⟨k, hk, hσ k hk⟩
  rw [← conjSub_map σ.toMonoidHom g A, hAσ]
  exact hcl _ A hA

theorem comm_of_fix (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {σ : MulAut X} {y : AEQ 5}
    (hy : ∀ w : X, I.φ ⟨σ w, mem_pSpan hgen _⟩ = y * I.φ ⟨w, mem_pSpan hgen w⟩ * y⁻¹)
    {L : Subgroup X} (hL : L ∈ Φ) (hσL : ∀ k ∈ L, σ k = k) :
    ∀ a ∈ (L.subgroupOf (pSpan Φ)).map I.φ, y * a = a * y := by
  intro a ha
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL ha
  have e : y * I.φ ⟨l, mem_pSpan hgen l⟩ * y⁻¹ = I.φ ⟨l, mem_pSpan hgen l⟩ := by
    rw [← hy l]
    exact congrArg I.φ (Subtype.ext (hσL l hl))
  show y * I.φ ⟨l, mem_pSpan hgen l⟩ = I.φ ⟨l, mem_pSpan hgen l⟩ * y
  calc y * I.φ ⟨l, mem_pSpan hgen l⟩ = (y * I.φ ⟨l, mem_pSpan hgen l⟩ * y⁻¹) * y := by group
    _ = I.φ ⟨l, mem_pSpan hgen l⟩ * y := by rw [e]

variable [Finite X]

theorem exists_twin_labels (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hx : IsUniqueInvolution A x)
    (hx' : IsUniqueInvolution B x') (hxx' : x * x' ∈ Subgroup.center X) :
    ∃ (α : Finset (Fin 5)) (hα : α.card = 4) (b : Bool),
      (A.subgroupOf (pSpan Φ)).map I.φ = memBar α hα b ∧
        (B.subgroupOf (pSpan Φ)).map I.φ = memBar α hα (!b) := by
  have hB' : B ∈ Φ := hB.1
  obtain ⟨α, hα, bA, hlA⟩ := I.label A hA
  obtain ⟨β, hβ, bB, hlB⟩ := I.label B hB'
  have hzA := I.map_eq_zBar (by norm_num) hA (natCard_mem h hO hgen I hA) hlA hx
  have hzB := I.map_eq_zBar (by norm_num) hB' (natCard_mem h hO hgen I hB') hlB hx'
  have hαβ : α = β := by
    have h1 := map_eq_one_of_mem_center hgen I hxx'
    have h2 : I.φ ⟨x * x', mem_pSpan hgen _⟩ = zBar α hα * zBar β hβ := by
      rw [← hzA, ← hzB, ← map_mul]
      rfl
    rw [h2] at h1
    refine eq_of_zBar_eq (by norm_num) (h := hα) (h' := hβ) ?_
    calc zBar α hα = zBar α hα * (zBar β hβ * zBar β hβ) := by rw [zBar_mul_self, mul_one]
      _ = (zBar α hα * zBar β hβ) * zBar β hβ := by group
      _ = zBar β hβ := by rw [h1, one_mul]
  subst hαβ
  refine ⟨α, hα, bA, hlA, ?_⟩
  have hlB' : (B.subgroupOf (pSpan Φ)).map I.φ = memBar α hα bB := hlB
  have hbB : bB = !bA := by
    by_contra hb
    have hbb : bB = bA := by cases bA <;> cases bB <;> simp_all
    subst hbb
    exact hB.2.1 (eq_of_map_eq h hO hgen I hB' hA (hlB'.trans hlA.symm))
  rw [hlB', hbB]

theorem fix_of_oddCoreOf (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (I : AEIdent Φ 5) {L : Subgroup X} (hL : L ∈ Φ) {σ : MulAut X}
    (hσL : ∀ k ∈ L, σ k * k⁻¹ ∈ oddCoreOf L) : ∀ k ∈ L, σ k = k := by
  intro k hk
  have h1 := hσL k hk
  rw [oddCoreOf_eq_bot hO hgen I hL, Subgroup.mem_bot] at h1
  exact mul_inv_eq_one.mp h1

section Cert


omit [Finite X] in
theorem exists_conj_of_map_mem (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (σ : MulAut X)
    (hσ : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ) :
    ∃ y : AEQ 5, ∀ w : X, I.φ ⟨σ w, mem_pSpan hgen _⟩ = y * I.φ ⟨w, mem_pSpan hgen w⟩ * y⁻¹ := by
  obtain ⟨y, hy⟩ := model117_proved 5 (by norm_num) (by norm_num) (descAut hgen I σ) (by
    intro α hα b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα b
    obtain ⟨α', hα', b', hlab'⟩ := I.label _ (hσ L hL)
    refine ⟨α', hα', b', ?_⟩
    rw [← hlab, ← hlab', ← map_psi hgen I L, ← map_psi hgen I (L.map σ.toMonoidHom),
      map_descAut])
  refine ⟨y, fun w => ?_⟩
  have e := hy (psi hgen I w)
  rw [descAut_psi] at e
  exact e

end Cert

end AE5

theorem secIdNoRootAE5_proved : SecIdNoRootAE5 := by
  intro X _ _ Φ h hO hgen _ htr _ hI A hA B hB x x' hx hx' hxx' σ hσA hσB hσσ
  obtain ⟨I⟩ := hI
  have hB' : B ∈ Φ := hB.1
  have hfA := AE5.fix_of_oddCoreOf hO hgen I hA hσA
  obtain ⟨y, hy⟩ := AE5.exists_conj_of_map_mem hgen I σ
    (AE5.map_mem_of_fix h.hyp.conjInvariant htr hA hfA)
  obtain ⟨α, hα, b, hlA, hlB⟩ := AE5.exists_twin_labels h hO hgen I hA hB hx hx' hxx'
  have hcA := AE5.comm_of_fix hgen I hy hA hfA
  have hcB := AE5.comm_of_fix hgen I hy hB' (AE5.fix_of_oddCoreOf hO hgen I hB' hσB)
  rw [hlA] at hcA
  rw [hlB] at hcB
  have hT : ∀ a ∈ memBar α hα true, y * a = a * y := by
    cases b
    · exact hcB
    · exact hcA
  have hF : ∀ a ∈ memBar α hα false, y * a = a * y := by
    cases b
    · exact hcA
    · exact hcB
  have hyy : y * y = 1 := by
    rcases AE5.eq_one_or_eq_zBar_of_comm α hα hT hF with rfl | rfl
    · exact mul_one 1
    · exact zBar_mul_self α hα
  have hzA := I.map_eq_zBar (by norm_num) hA (AE5.natCard_mem h hO hgen I hA) hlA hx
  apply zBar_ne_one (n := 5) (by norm_num) α hα
  refine AE5.eq_one_of_comm_aeBar fun g hg => ?_
  rw [← I.range_eq] at hg
  obtain ⟨⟨w, hwP⟩, rfl⟩ := hg
  show zBar α hα * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * zBar α hα
  have e1 : σ (σ w) = MulAut.conj x w := congrArg (fun τ : MulAut X => τ w) hσσ
  have e2 : I.φ ⟨σ (σ w), AE5.mem_pSpan hgen _⟩ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ :=
    calc I.φ ⟨σ (σ w), AE5.mem_pSpan hgen _⟩ =
        y * (y * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * y⁻¹) * y⁻¹ := by rw [hy (σ w), hy w]
      _ = (y * y) * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (y * y)⁻¹ := by group
      _ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ := by rw [hyy, one_mul, inv_one, mul_one]
  have e3 : I.φ ⟨MulAut.conj x w, AE5.mem_pSpan hgen _⟩ =
      zBar α hα * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (zBar α hα)⁻¹ := by
    rw [← hzA, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg I.φ (Subtype.ext (MulAut.conj_apply x w))
  have e4 : I.φ ⟨w, AE5.mem_pSpan hgen w⟩ =
      zBar α hα * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (zBar α hα)⁻¹ :=
    e2.symm.trans ((congrArg (fun v => I.φ ⟨v, AE5.mem_pSpan hgen v⟩) e1).trans e3)
  calc zBar α hα * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ =
      (zBar α hα * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (zBar α hα)⁻¹) * zBar α hα := by group
    _ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * zBar α hα := by rw [← e4]

theorem secIdE4GenAE5_proved : SecIdE4GenAE5 := by
  intro X _ _ Φ h hO hgen _ htr _ hI A hA B hB x x' hx hx' hxx' σ hσσ _ hσA hσB hnot
  exfalso
  obtain ⟨I⟩ := hI
  have hB' : B ∈ Φ := hB.1
  have hfA := AE5.fix_of_oddCoreOf hO hgen I hA hσA
  obtain ⟨y, hy⟩ := AE5.exists_conj_of_map_mem hgen I σ
    (AE5.map_mem_of_fix h.hyp.conjInvariant htr hA hfA)
  obtain ⟨α, hα, b, hlA, hlB⟩ := AE5.exists_twin_labels h hO hgen I hA hB hx hx' hxx'
  have hcA := AE5.comm_of_fix hgen I hy hA hfA
  rw [hlA] at hcA
  have hnB : ∀ a ∈ memBar α hα (!b), y * a * y⁻¹ ∈ memBar α hα (!b) := by
    intro a ha
    rw [← hlB] at ha ⊢
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hB' ha
    show y * I.φ ⟨l, AE5.mem_pSpan hgen l⟩ * y⁻¹ ∈ _
    rw [← hy l]
    exact I.mem_map hB' (hσB l hl)
  have hyy : y * y = 1 := by
    refine AE5.eq_one_of_comm_aeBar fun g hg => ?_
    rw [← I.range_eq] at hg
    obtain ⟨⟨w, hwP⟩, rfl⟩ := hg
    show y * y * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (y * y)
    have e1 : σ (σ w) = w := congrArg (fun τ : MulAut X => τ w) hσσ
    have e2 : y * (y * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * y⁻¹) * y⁻¹ =
        I.φ ⟨w, AE5.mem_pSpan hgen w⟩ := by
      rw [← hy w, ← hy (σ w)]
      exact congrArg (fun v => I.φ ⟨v, AE5.mem_pSpan hgen v⟩) e1
    calc y * y * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ =
        (y * (y * I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * y⁻¹) * y⁻¹) * (y * y) := by group
      _ = I.φ ⟨w, AE5.mem_pSpan hgen w⟩ * (y * y) := by rw [e2]
  have hcB := AE5.comm_of_twin_of_sq α hα b hyy hcA hnB
  apply hnot
  intro k hk
  have e1 : I.φ ⟨σ k, AE5.mem_pSpan hgen _⟩ = I.φ ⟨k, AE5.mem_pSpan hgen k⟩ := by
    have hkM : I.φ ⟨k, AE5.mem_pSpan hgen k⟩ ∈ memBar α hα (!b) := by
      rw [← hlB]
      exact I.mem_map hB' hk
    rw [hy k, hcB _ hkM, mul_inv_cancel_right]
  have e2 : σ k = k :=
    I.injOn (by norm_num) hB' (AE5.natCard_mem h hO hgen I hB') hlB (hσB k hk) hk e1
  rw [e2, mul_inv_cancel]
  exact (oddCoreOf B).one_mem

end CFSG.ClassicalInvolution.Q3.TL4

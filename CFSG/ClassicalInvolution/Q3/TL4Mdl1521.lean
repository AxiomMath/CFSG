module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521MemSp
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521D
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RD
public import CFSG.ClassicalInvolution.Q3.TL4C264OmDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RC

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)

namespace E1521

theorem lieModel_psl_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : LieModel Y .PSL n p f) : LieModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e.symm h

theorem map_sigmaFixGen_equiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (H : Subgroup S)
    (σ : MulAut S) :
    (sigmaFixGen H σ).map e.toMonoidHom =
      sigmaFixGen (H.map e.toMonoidHom) ((e.symm.trans σ).trans e) := by
  have hτ : ∀ x : S, ((e.symm.trans σ).trans e) (e x) = e (σ x) := fun x => by
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hmapc : ∀ g : S, (conjSub g H).map e.toMonoidHom = conjSub (e g) (H.map e.toMonoidHom) :=
    fun g => AscQuot.map_conjSub e.toMonoidHom g H
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨⟨g, rfl⟩, hfix⟩ := hM
    rw [← Subgroup.map_le_iff_le_comap, hmapc]
    refine le_iSup₂ (f := fun (M : Subgroup T) (_ : M ∈ {M : Subgroup T | M ∈
      CoreAssembly.conjClass (H.map e.toMonoidHom) ∧ ∀ x ∈ M,
        ((e.symm.trans σ).trans e) x = x}) => M) (conjSub (e g) (H.map e.toMonoidHom))
      ⟨⟨_, rfl⟩, fun y hy => ?_⟩
    rw [← hmapc] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    show ((e.symm.trans σ).trans e) (e x) = e x
    rw [hτ, hfix x hx]
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨⟨t, rfl⟩, hfix⟩ := hM
    obtain ⟨g, rfl⟩ := e.surjective t
    have hfix' : ∀ x ∈ conjSub (e g) (H.map e.toMonoidHom),
        ((e.symm.trans σ).trans e) x = x := hfix
    show conjSub (e g) (H.map e.toMonoidHom) ≤ _
    rw [← hmapc]
    refine Subgroup.map_mono (le_iSup₂ (f := fun (M : Subgroup S) (_ : M ∈ {M : Subgroup S |
      M ∈ CoreAssembly.conjClass H ∧ ∀ x ∈ M, σ x = x}) => M) (conjSub g H)
      ⟨⟨_, rfl⟩, fun x hx => ?_⟩)
    have h1 := hfix' (e x) (by rw [← hmapc]; exact Subgroup.mem_map_of_mem _ hx)
    rw [hτ] at h1
    exact e.injective h1

end E1521


theorem model1521Twin3_proved : Model1521Twin3 := by
  intro W _ _ Φ K K' k k' σ hT N _ hN hS
  have h := hT.toTwinBase3
  set f := (QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N) with hfdef
  have hred : Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
      IsSimpleGroup ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) ∧
      Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)))) =
        ⊥ := by
    rcases hS with hS | hS
    · exact E3S3O.quotCenter_reduction h N hN (Or.inr (Or.inl rfl)) hS
    · exact E3S3O.quotCenter_reduction h N hN (Or.inl rfl) hS
  obtain ⟨hf, hf2, hs, hOS⟩ := hred
  have hσ := E3S3O.map_ker_aut h f hf hf2 hs σ
  set σb := E3S3O.descend f hf σ hσ with hσbdef
  have hσb : ∀ w, σb (f w) = f (σ w) := E3S3O.descend_apply f hf σ hσ
  have hA := E3S3O.quatTwinDatum_map_of_simple h f hf hf2 hs hOS
  obtain ⟨-, ⟨c, hcK, hcC, hK'⟩, hne⟩ := E3S3O.twin_map_of_simple h f hf hf2 hs hOS
  have hσ2 : ∀ y, σb (σb y) = y := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    rw [hσb, hσb, ← MulAut.mul_apply, hT.sq, MulAut.one_apply]
  have hK2 : IsPGroup 2 ↥K := by
    have h1 := E3S3O.isPGroup_conj_of_simple h f hf hf2 hs hOS 1
    rwa [conjSub_one] at h1
  have hfixK : ∀ x ∈ K, σ x = x := by
    obtain ⟨Q, hQ, hQσ⟩ := hT.fixK
    have hQK : K = Q := hQ.2.2 K le_rfl hK2 hQ.1
    rw [hQK]
    exact hQσ
  have hfixA : ∀ y ∈ K.map f, σb y = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hfixK x hx]
  have hmovA : ∃ y ∈ K'.map f, σb y ≠ y := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hxK', hσx⟩ := hT.movK'
    apply hσx
    refine E3S3O.fix_of_fix_map h f hf hf2 hs hOS hT.perm hσ c ?_ x (by rw [hcK]; exact hxK')
    rw [hcK]
    exact hno
  have hcomm : ∀ x ∈ K.map f, ∀ y ∈ K'.map f, x * y = y * x := by
    rcases hA.twins (f c) hcC with heq | hc
    · exact absurd (hK'.trans heq) hne
    · rw [hK']
      exact hc
  rcases hS with hSp | hSl
  ·
    exfalso
    rcases hSp with ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · rw [pow_one] at hF
      obtain ⟨e, he⟩ := E1521.exists_mulEquiv_blockQ0Sp hF e₀ hA.q8
      set τ : MulAut (StatedProj (StatedSp 2 F)) := (e.symm.trans σb).trans e with hτdef
      have hτ : ∀ y, τ (e y) = e (σb y) := fun y => by
        simp only [hτdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      refine E1521.sig_psp4_false hF τ ?_ ?_ ?_
      · ext y
        obtain ⟨x, rfl⟩ := e.surjective y
        rw [MulAut.mul_apply, hτ, hτ, hσ2, MulAut.one_apply]
      · intro x hx
        rw [← he] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        show τ (e y) = e y
        rw [hτ, hfixA y hy]
      · obtain ⟨a', ha', hmv⟩ := hmovA
        refine ⟨e a', fun z hz => ?_, fun h1 => hmv (e.injective (by rw [← hτ]; exact h1))⟩
        rw [← he] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        show e a' * e y = e y * e a'
        rw [← map_mul, ← map_mul, hcomm y hy a' ha']
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  ·
    obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ :=
      LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hSl
    rw [pow_one] at hF
    obtain ⟨e, he⟩ := E1521.exists_mulEquiv_blockQ0 hF e₀ hA.q8
    set τ : MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F) :=
      (e.symm.trans σb).trans e with hτdef
    have hτ : ∀ y, τ (e y) = e (σb y) := fun y => by
      simp only [hτdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hτ2 : τ * τ = 1 := by
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [MulAut.mul_apply, hτ, hτ, hσ2, MulAut.one_apply]
    have hτfix : ∀ x ∈ E1521.blockQ0 F, τ x = x := by
      intro x hx
      rw [← he] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      show τ (e y) = e y
      rw [hτ, hfixA y hy]
    have hτmov : ∃ x, (∀ y ∈ E1521.blockQ0 F, x * y = y * x) ∧ τ x ≠ x := by
      obtain ⟨a', ha', hmv⟩ := hmovA
      refine ⟨e a', fun z hz => ?_, fun h1 => hmv (e.injective (by rw [← hτ]; exact h1))⟩
      rw [← he] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      show e a' * e y = e y * e a'
      rw [← map_mul, ← map_mul, hcomm y hy a' ha']
    obtain ⟨B, hB, hτB⟩ := E1521.sig_psl4 hF τ hτ2 hτfix hτmov
    refine ⟨hSl, ?_, ?_⟩
    · rw [E3S3O.map_sigmaFixGen h f hf hf2 hs hOS hT.perm hσ]
      refine E1521.lieModel_psl_congr
        ((sigmaFixGen (K.map f) σb).equivMapOfInjective e.toMonoidHom e.injective) ?_
      rw [E1521.map_sigmaFixGen_equiv, he]
      exact E1521.lieModel_sigmaFixGen_psl4 hF hB hτB
    · rintro ⟨w, hw⟩
      apply E1521.ne_conj_of_eq hF hτB (e (f w))
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      obtain ⟨v, rfl⟩ := hf x
      rw [hτ, hσb, hw, MulAut.conj_apply, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

end CFSG.ClassicalInvolution.Q3.TL4

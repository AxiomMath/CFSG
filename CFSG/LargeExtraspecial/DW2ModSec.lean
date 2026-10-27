module

public import CFSG.LargeExtraspecial.DW2ModRank
public import CFSG.LargeExtraspecial.DW2ModFactor
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLCaseA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection commutatorSpace
  GenByTransvections IsIrreducibleOn IsGInvariant)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev Sec (A B : Submodule (ZMod 2) V) : Type _ :=
  ↥B ⧸ A.comap B.subtype

abbrev secMk (A B : Submodule (ZMod 2) V) : ↥B →ₗ[ZMod 2] Sec A B :=
  (A.comap B.subtype).mkQ

theorem secMk_eq_zero_iff {A B : Submodule (ZMod 2) V} {b : ↥B} :
    secMk A B b = 0 ↔ (b : V) ∈ A := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_comap, Submodule.coe_subtype]

theorem secMk_eq_iff {A B : Submodule (ZMod 2) V} {b b' : ↥B} :
    secMk A B b = secMk A B b' ↔ (b : V) - b' ∈ A := by
  rw [← sub_eq_zero, ← map_sub, secMk_eq_zero_iff, Submodule.coe_sub]

theorem secMk_surjective (A B : Submodule (ZMod 2) V) : Function.Surjective (secMk A B) :=
  Submodule.mkQ_surjective _

theorem finrank_map_secMk [FiniteDimensional (ZMod 2) V] {A B S : Submodule (ZMod 2) V}
    (hAS : A ≤ S) (hSB : S ≤ B) :
    finrank (ZMod 2) ↥((S.comap B.subtype).map (secMk A B)) + finrank (ZMod 2) A =
      finrank (ZMod 2) S := by
  set Φ : ↥S →ₗ[ZMod 2] Sec A B := secMk A B ∘ₗ Submodule.inclusion hSB with hΦ
  have hrange : LinearMap.range Φ = (S.comap B.subtype).map (secMk A B) := by
    rw [hΦ, LinearMap.range_comp, Submodule.range_inclusion]
  have hker : LinearMap.ker Φ = A.comap S.subtype := by
    rw [hΦ, LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.comap_comp,
      Submodule.subtype_comp_inclusion]
  have h := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hAS).finrank_eq] at h
  exact h

section Hom

variable (A B : Submodule (ZMod 2) V)

@[expose] noncomputable def secLin (g : V ≃ₗ[ZMod 2] V) (hB : ∀ b ∈ B, g b ∈ B)
    (hA : ∀ a ∈ A, g a ∈ A) :
    Module.End (ZMod 2) (Sec A B) :=
  (A.comap B.subtype).mapQ (A.comap B.subtype) ((g : V →ₗ[ZMod 2] V).restrict hB)
    fun _ hx => hA _ hx

theorem secLin_mk (g : V ≃ₗ[ZMod 2] V) (hB : ∀ b ∈ B, g b ∈ B) (hA : ∀ a ∈ A, g a ∈ A)
    (b : ↥B) : secLin A B g hB hA (secMk A B b) = secMk A B ⟨g b, hB b b.2⟩ :=
  rfl

variable (Y : Subgroup (V ≃ₗ[ZMod 2] V))

@[expose] noncomputable def secHom (hA : IsInv Y A) (hB : IsInv Y B) :
    Y →* LinearMap.GeneralLinearGroup (ZMod 2) (Sec A B) :=
  MonoidHom.toHomUnits
    { toFun := fun y => secLin A B y (hB y y.2) (hA y y.2)
      map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)
      map_mul' := fun _ _ => Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl) }

variable {A B Y}

theorem secHom_apply_mk (hA : IsInv Y A) (hB : IsInv Y B) (y : Y) (b : ↥B) :
    ((secHom A B Y hA hB y : LinearMap.GeneralLinearGroup (ZMod 2) (Sec A B)) :
      Module.End (ZMod 2) (Sec A B)) (secMk A B b) =
      secMk A B ⟨(y : V ≃ₗ[ZMod 2] V) b, hB y y.2 b b.2⟩ :=
  rfl

theorem secHom_eq_one_iff (hA : IsInv Y A) (hB : IsInv Y B) {y : Y} :
    secHom A B Y hA hB y = 1 ↔ ∀ b ∈ B, (y : V ≃ₗ[ZMod 2] V) b - b ∈ A := by
  constructor
  · intro h b hb
    have h1 := congrArg (fun t : LinearMap.GeneralLinearGroup (ZMod 2) (Sec A B) =>
      (t : Module.End (ZMod 2) (Sec A B)) (secMk A B ⟨b, hb⟩)) h
    simp only [secHom_apply_mk, Units.val_one, Module.End.one_apply] at h1
    exact secMk_eq_iff.mp h1
  · intro h
    refine Units.ext (Submodule.linearMap_qext _ (LinearMap.ext fun b => ?_))
    change secMk A B ⟨(y : V ≃ₗ[ZMod 2] V) b, hB y y.2 b b.2⟩ = secMk A B b
    exact secMk_eq_iff.mpr (h b b.2)

theorem commutatorSpace_secHom (hA : IsInv Y A) (hB : IsInv Y B) (y : Y) :
    commutatorSpace (secHom A B Y hA hB y) =
      ((B.map ((y : V →ₗ[ZMod 2] V) - 1) ⊔ A).comap B.subtype).map (secMk A B) := by
  have hT : ∀ b ∈ B, ((y : V →ₗ[ZMod 2] V) - 1) b ∈ B := fun b hb => by
    rw [sub_one_apply]
    exact sub_mem (hB y y.2 b hb) hb
  have happ : ∀ b : ↥B, ((LinearMap.id : Module.End (ZMod 2) (Sec A B)) +
      ((secHom A B Y hA hB y : LinearMap.GeneralLinearGroup (ZMod 2) (Sec A B)) :
        Module.End (ZMod 2) (Sec A B))) (secMk A B b) =
        secMk A B ⟨((y : V →ₗ[ZMod 2] V) - 1) b, hT b b.2⟩ := by
    intro b
    rw [LinearMap.add_apply, LinearMap.id_apply, secHom_apply_mk, ← map_add]
    congr 1
    ext
    simp only [Submodule.coe_add, sub_one_apply]
    rw [sub_eq_add_zmod2 ((y : V ≃ₗ[ZMod 2] V) b) (b : V), add_comm]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := secMk_surjective A B x
    rw [happ]
    exact mem_map_of_mem (mem_sup_left (mem_map_of_mem b.2))
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ⟨b, hb, rfl⟩, a, ha, hta⟩ := mem_sup.mp hs
    refine ⟨secMk A B ⟨b, hb⟩, ?_⟩
    rw [happ, secMk_eq_iff]
    have hta' : ((y : V →ₗ[ZMod 2] V) - 1) b + a = (s : V) := hta
    have e : (((y : V →ₗ[ZMod 2] V) - 1) b : V) - (s : V) = -a := by
      rw [← hta']; abel
    rw [e]
    exact neg_mem ha

variable [FiniteDimensional (ZMod 2) V]

theorem finrank_commutatorSpace_secHom (hA : IsInv Y A) (hB : IsInv Y B) (hAB : A ≤ B)
    (y : Y) : finrank (ZMod 2) ↥(commutatorSpace (secHom A B Y hA hB y)) =
      secRank (y : V ≃ₗ[ZMod 2] V) A B := by
  have hTB : B.map ((y : V →ₗ[ZMod 2] V) - 1) ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    rw [sub_one_apply]
    exact sub_mem (hB y y.2 b hb) hb
  rw [commutatorSpace_secHom]
  have h := finrank_map_secMk (A := A) (B := B) (le_sup_right :
    A ≤ B.map ((y : V →ₗ[ZMod 2] V) - 1) ⊔ A) (sup_le hTB hAB)
  unfold secRank
  omega

theorem isF2Transvection_secHom (hA : IsInv Y A) (hB : IsInv Y B) (hAB : A ≤ B) {y : Y}
    (h1 : secRank (y : V ≃ₗ[ZMod 2] V) A B = 1) : IsF2Transvection (secHom A B Y hA hB y) := by
  refine ⟨fun h => ?_, by rw [finrank_commutatorSpace_secHom hA hB hAB, h1]⟩
  have h0 := secRank_eq_zero_iff.mpr ((secHom_eq_one_iff hA hB).mp h)
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem isIrreducibleOn_secHom (hF : IsNontrivFactor Y A B) :
    IsIrreducibleOn (secHom A B Y hF.1 hF.2.1).range := by
  intro W' hW'
  set W : Submodule (ZMod 2) V := (W'.comap (secMk A B)).map B.subtype with hW
  have hmemW : ∀ v, v ∈ W ↔ ∃ hv : v ∈ B, secMk A B ⟨v, hv⟩ ∈ W' := by
    intro v
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨hv, h⟩
      exact ⟨⟨v, hv⟩, h, rfl⟩
  have hWinv : IsInv Y W := by
    intro y hy v hv
    obtain ⟨hvB, hvW⟩ := (hmemW v).mp hv
    refine (hmemW _).mpr ⟨hF.2.1 y hy v hvB, ?_⟩
    have h := hW' _ ⟨⟨y, hy⟩, rfl⟩ _ hvW
    rwa [secHom_apply_mk] at h
  have hAW : A ≤ W := fun a ha => (hmemW a).mpr ⟨hF.2.2.1 ha, by
    rw [secMk_eq_zero_iff.mpr ha]
    exact zero_mem _⟩
  have hWB : W ≤ B := fun v hv => ((hmemW v).mp hv).1
  rcases hF.2.2.2.2 W hWinv hAW hWB with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨b, rfl⟩ := secMk_surjective A B x
    have hbW : (b : V) ∈ W := (hmemW b).mpr ⟨b.2, hx⟩
    rw [h] at hbW
    exact (mem_bot _).mpr (secMk_eq_zero_iff.mpr hbW)
  · right
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨b, rfl⟩ := secMk_surjective A B x
    have hbW : (b : V) ∈ W := by rw [h]; exact b.2
    obtain ⟨_, hb'⟩ := (hmemW b).mp hbW
    exact hb'

omit [FiniteDimensional (ZMod 2) V] in
theorem genByTransvections_secHom {D : Set (V ≃ₗ[ZMod 2] V)} (hgen : Y = Subgroup.closure D)
    (hA : IsInv Y A) (hB : IsInv Y B)
    (htv : ∀ (d : V ≃ₗ[ZMod 2] V) (hd : d ∈ Y), d ∈ D →
      IsF2Transvection (secHom A B Y hA hB ⟨d, hd⟩)) :
    GenByTransvections (secHom A B Y hA hB).range := by
  refine ⟨secHom A B Y hA hB '' {y : Y | (y : V ≃ₗ[ZMod 2] V) ∈ D}, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact htv y y.2 hy
  · rw [MonoidHom.range_eq_map, ← MonoidHom.map_closure]
    congr 1
    subst hgen
    exact Subgroup.closure_closure_coe_preimage.symm

end Hom

section Form

variable (f : LinearMap.BilinForm (ZMod 2) V) {A B : Submodule (ZMod 2) V}

@[expose] noncomputable def secForm (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0) :
    LinearMap.BilinForm (ZMod 2) (Sec A B) :=
  ((A.comap B.subtype).liftQ ((A.comap B.subtype).liftQ (f.restrict B)
      (fun a ha => LinearMap.mem_ker.mpr (LinearMap.ext fun b => (hAB a ha b b.2).1))).flip
    (fun b hb => LinearMap.mem_ker.mpr
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (hAB b hb a a.2).2)))).flip

variable {f}

theorem secForm_mk (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0) (x y : ↥B) :
    secForm f hAB (secMk A B x) (secMk A B y) = f x y :=
  rfl

theorem secForm_self (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0) (hf : f.IsAlt)
    (x : Sec A B) : secForm f hAB x x = 0 := by
  obtain ⟨b, rfl⟩ := secMk_surjective A B x
  rw [secForm_mk]
  exact hf b

theorem secForm_comm (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0)
    (hsymm : ∀ u v, f u v = f v u) (x y : Sec A B) : secForm f hAB x y = secForm f hAB y x := by
  obtain ⟨b, rfl⟩ := secMk_surjective A B x
  obtain ⟨b', rfl⟩ := secMk_surjective A B y
  rw [secForm_mk, secForm_mk, hsymm]

theorem secForm_nondeg (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0) (hr : f.IsRefl)
    (hrad : B ⊓ f.orthogonal B ≤ A) (x : Sec A B) (hx : ∀ y, secForm f hAB x y = 0) :
    x = 0 := by
  obtain ⟨b, rfl⟩ := secMk_surjective A B x
  refine secMk_eq_zero_iff.mpr (hrad ⟨b.2, LinearMap.BilinForm.mem_orthogonal_iff.mpr
    fun c hc => hr _ _ ?_⟩)
  have h := hx (secMk A B ⟨c, hc⟩)
  rwa [secForm_mk] at h

theorem secForm_secLin (hAB : ∀ a ∈ A, ∀ b ∈ B, f a b = 0 ∧ f b a = 0)
    {g : V ≃ₗ[ZMod 2] V} (hB : ∀ b ∈ B, g b ∈ B) (hA : ∀ a ∈ A, g a ∈ A)
    (hg : ∀ u v, f (g u) (g v) = f u v) (x y : Sec A B) :
    secForm f hAB (secLin A B g hB hA x) (secLin A B g hB hA y) = secForm f hAB x y := by
  obtain ⟨b, rfl⟩ := secMk_surjective A B x
  obtain ⟨b', rfl⟩ := secMk_surjective A B y
  rw [secLin_mk, secLin_mk, secForm_mk, secForm_mk]
  exact hg b b'

end Form

end CFSG.LargeExtraspecial.DW

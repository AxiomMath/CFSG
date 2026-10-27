module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

theorem open_isQuasisimple_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : Open.IsQuasisimple X ∧ center X = ⊥ := by
  obtain ⟨a, b, hab⟩ := hX
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab
  refine ⟨⟨?_, ?_⟩, hZ⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator X := by
        rw [_root_.commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem hasDihedralSylowTwo_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : AschbacherKnownGroup.HasDihedralSylowTwo X) :
    AschbacherKnownGroup.HasDihedralSylowTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, n, hn, ⟨eP⟩⟩ := h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective hsurj, n, hn, ⟨?_⟩⟩
  exact ((P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eP

theorem isSmallDihedralSimple_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AschbacherKnownGroup.IsSmallDihedralSimple X) :
    AschbacherKnownGroup.IsSmallDihedralSimple Y := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨p, f, hpf, hadm, K, hK1, hK2, hcard, ⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr ⟨p, f, hpf, hadm, K, hK1, hK2, hcard, ⟨e.symm.trans e'⟩⟩

theorem range_inf_centralizer_eq {S : Type*} [Group S] (hS : center S = ⊥) (τ : MulAut S) :
    (MulAut.conj : S →* MulAut S).range ⊓ centralizer ({τ} : Set (MulAut S)) =
      (MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)).map MulAut.conj := by
  ext φ
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    refine ⟨s, ?_, rfl⟩
    have hs : MulAut.conj s * τ = τ * MulAut.conj s :=
      mem_centralizer_singleton_iff.mp (show MulAut.conj s ∈ centralizer ({τ} : Set (MulAut S))
        from hs)
    have h1 : MulAut.conj (τ s) = MulAut.conj s := by
      have h2 : MulAut.conj (τ s) = τ * MulAut.conj s * τ⁻¹ := by
        ext y
        simp [MulAut.conj_apply, MulAut.mul_apply]
      rw [h2, ← hs]
      group
    have h3 : s⁻¹ * τ s ∈ center S := by
      rw [mem_center_iff]
      intro y
      have h4 := DFunLike.congr_fun h1 y
      simp only [MulAut.conj_apply] at h4
      calc y * (s⁻¹ * τ s) = s⁻¹ * (s * y * s⁻¹) * τ s := by group
        _ = s⁻¹ * (τ s * y * (τ s)⁻¹) * τ s := by rw [h4]
        _ = s⁻¹ * τ s * y := by group
    rw [hS, mem_bot] at h3
    show τ s = s
    calc τ s = s * (s⁻¹ * τ s) := by group
      _ = s := by rw [h3, mul_one]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, show MulAut.conj s ∈ centralizer ({τ} : Set (MulAut S)) from ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hs' : τ s = s := hs
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, hs']

theorem injective_mulAut_conj {S : Type*} [Group S] (hS : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  rw [← hS, mem_center_iff]
  intro y
  have h1 := DFunLike.congr_fun hs y
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * s = s * y * s⁻¹ * s := by rw [h1]
    _ = s * y := by group

theorem le_normalizer_range_conj {S : Type*} [Group S] (V : Subgroup (MulAut S)) :
    V ≤ normalizer ((MulAut.conj : S →* MulAut S).range : Set (MulAut S)) := by
  intro φ _
  refine mem_normalizer_iff.mpr fun ψ => ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    refine ⟨φ s, ?_⟩
    ext y
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨s, hs⟩
    refine ⟨φ⁻¹ s, ?_⟩
    have h1 : ψ = φ⁻¹ * MulAut.conj s * φ := by rw [hs]; group
    rw [h1]
    ext y
    simp [MulAut.conj_apply, MulAut.mul_apply]

theorem footeL2_fix_generation (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hD : AschbacherKnownGroup.HasDihedralSylowTwo S)
    (hnab : ∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x)
    {T : Subgroup (MulAut S)} (hT : IsPGroup 2 T)
    (hTiso : ∃ P : Sylow 2 S, Nonempty ((P : Subgroup S) ≃* T))
    {V : Subgroup (MulAut S)} (hV : IsKleinFour V) (hVT : V ≤ T) :
    ⨆ (τ : MulAut S) (_ : τ ∈ T) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) = ⊤ := by
  by_cases hsmall : AschbacherKnownGroup.IsSmallDihedralSimple S
  · exact hcalc S hsmall hnab T hT hTiso
  obtain ⟨-, hZ⟩ := open_isQuasisimple_of_isSimpleGroup hnc
  set c : S →* MulAut S := MulAut.conj with hc
  have hcinj : Function.Injective c := injective_mulAut_conj hZ
  set Inn := c.range with hInn
  let eInn : S ≃* Inn := MonoidHom.ofInjective hcinj
  have : IsSimpleGroup Inn := eInn.symm.isSimpleGroup
  have hInnc : ∃ a b : Inn, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eInn a, eInn b, fun h => hab (eInn.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨hqI, hZI⟩ := open_isQuasisimple_of_isSimpleGroup hInnc
  let eQ : Inn ⧸ center Inn ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot).trans eInn.symm
  have hDI : AschbacherKnownGroup.HasDihedralSylowTwo (Inn ⧸ center Inn) :=
    hasDihedralSylowTwo_of_equiv eQ.symm hD
  have hfact : (Nat.card (center Inn)).factorization 2 ≤ 1 := by
    rw [hZI, card_bot]
    simp
  have hV4 : AschbacherKnownGroup.IsFourGroup V :=
    ⟨⟨@IsKleinFour.isMulCommutative V _ hV, fun x hx => sq_eq_one_of_isKleinFour hV hx⟩,
      hV.card_four⟩
  have hgen := hK.dihedral_cover_generation (MulAut S) Inn V hqI hDI hfact
    (le_normalizer_range_conj V) hV4
  have hle : Inn ≤ AschbacherKnownGroup.centralizerJoin V Inn := by
    by_contra hle
    exact hsmall (isSmallDihedralSimple_of_equiv eQ (hgen hle).1)
  have hjoin : AschbacherKnownGroup.centralizerJoin V Inn =
      (⨆ (u : MulAut S) (_ : u ∈ V) (_ : u ≠ 1),
        MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)).map c := by
    unfold AschbacherKnownGroup.centralizerJoin
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun u => iSup_congr fun _ => iSup_congr fun _ =>
      range_inf_centralizer_eq hZ u
  refine eq_top_iff.mpr fun s _ => ?_
  have h1 := hle ⟨s, rfl⟩
  rw [hjoin, mem_map_iff_mem hcinj] at h1
  have hle2 : (⨆ (u : MulAut S) (_ : u ∈ V) (_ : u ≠ 1),
      MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)) ≤
      ⨆ (τ : MulAut S) (_ : τ ∈ T) (_ : orderOf τ = 2),
        MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) := by
    refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
    have hu2 : orderOf u = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hu) hu1
    exact le_iSup₂_of_le (f := fun τ (_ : τ ∈ T) => ⨆ (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)) u (hVT hu)
      (le_iSup (fun _ : orderOf u = 2 => MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)) hu2)
  exact hle2 h1

end CFSG.ComponentClassification.FooteLit

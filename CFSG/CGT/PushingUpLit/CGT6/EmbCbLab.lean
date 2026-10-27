module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp Equiv

variable {V : Type} [CommGroup V]

private theorem cbtCardTwoCompl {m : ℕ} {a b : Fin (m + 2)} (hab : a ≠ b) :
    Fintype.card {i : Fin (m + 2) // i ≠ a ∧ i ≠ b} = m := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin (m + 2) => i ≠ a ∧ i ≠ b) = Finset.univ \ {a, b} := by
    ext i; simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_pair hab]
  omega

private def cbtRestr {m : ℕ} {a b : Fin (m + 2)} (σ : Perm (Fin (m + 2))) (ha : σ a = a)
    (hb : σ b = b) : Perm {i : Fin (m + 2) // i ≠ a ∧ i ≠ b} :=
  σ.subtypePerm (fun _ => by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h]; exact ha), fun h => h2 (by rw [h]; exact hb)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (σ.injective (h.trans ha.symm)),
        fun h => h2 (σ.injective (h.trans hb.symm))⟩)

private theorem cbtSign_restr {m : ℕ} {a b : Fin (m + 2)} (σ : Perm (Fin (m + 2))) (ha : σ a = a)
    (hb : σ b = b) : Perm.sign (cbtRestr σ ha hb) = Perm.sign σ := by
  classical
  have h1 : Perm.ofSubtype (cbtRestr σ ha hb) = σ := by
    show Perm.ofSubtype (σ.subtypePerm _) = σ
    apply Perm.ofSubtype_subtypePerm
    intro x hx
    constructor
    · intro h
      apply hx
      rw [h]
      exact ha
    · intro h
      apply hx
      rw [h]
      exact hb
  rw [← Perm.sign_ofSubtype, h1]

theorem cbtExists_label {X Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m)
    (θY : ↥Y ≃* alternatingGroup (Fin m)) (hYX : Y ≤ X)
    (θ : ↥X ≃* alternatingGroup (Fin (m + 2))) {a b : Fin (m + 2)} (hab : a ≠ b)
    (hstab : (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (m + 2) {a, b}) :
    ∃ j : Fin m → Fin (m + 2), Function.Injective j ∧ (∀ p, j p ≠ a ∧ j p ≠ b) ∧
      (∀ r, r ≠ a → r ≠ b → ∃ p, j p = r) ∧
      ∀ (y : MulAut V) (hy : y ∈ Y) (p : Fin m),
        (θ ⟨y, hYX hy⟩ : Perm (Fin (m + 2))) (j p) = j ((θY ⟨y, hy⟩ : Perm (Fin m)) p) := by
  classical
  let θ' : ↥Y →* alternatingGroup (Fin (m + 2)) :=
    θ.toMonoidHom.comp (Subgroup.inclusion hYX)
  have hθ'inj : Function.Injective θ' := θ.injective.comp (Subgroup.inclusion_injective hYX)
  have hfix : ∀ y : ↥Y, ((θ' y : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) a = a ∧
      ((θ' y : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) b = b := by
    intro y
    have h : θ' y ∈ altStabilizer (m + 2) {a, b} := by
      rw [← hstab]
      exact ⟨⟨y, hYX y.2⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    rw [CFSG.CGT.PushingUpLit.CGT6.mem_altStabilizer_iff] at h
    exact ⟨h a (by simp), h b (by simp)⟩
  let e : Fin m ≃ {i : Fin (m + 2) // i ≠ a ∧ i ≠ b} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, cbtCardTwoCompl hab])
  let rhoS : ↥Y →* Perm {i : Fin (m + 2) // i ≠ a ∧ i ≠ b} :=
    { toFun := fun y => cbtRestr ((θ' y : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2)))
        (hfix y).1 (hfix y).2
      map_one' := by
        ext x
        have h1 : ((θ' 1 : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) = 1 := by
          rw [map_one]; rfl
        simp [cbtRestr]
      map_mul' := fun y y' => by
        ext x
        simp only [cbtRestr, map_mul, Subgroup.coe_mul, Perm.subtypePerm_apply, Perm.mul_apply] }
  let rho : ↥Y →* Perm (Fin m) := (Equiv.permCongrHom e.symm).toMonoidHom.comp rhoS
  have hrho : ∀ (y : ↥Y) (p : Fin m),
      ((e (rho y p) : {i : Fin (m + 2) // i ≠ a ∧ i ≠ b}) : Fin (m + 2)) =
        ((θ' y : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) (e p) := by
    intro y p
    simp [rho, rhoS, cbtRestr]
  have hsign : ∀ y : ↥Y, Perm.sign (rho y) = 1 := by
    intro y
    have h1 : Perm.sign (rho y) = Perm.sign (cbtRestr ((θ' y : alternatingGroup (Fin (m + 2))) :
        Perm (Fin (m + 2))) (hfix y).1 (hfix y).2) := by
      show Perm.sign ((Equiv.permCongrHom e.symm) _) = _
      exact Perm.sign_permCongr e.symm _
    rw [h1, cbtSign_restr]
    exact Perm.mem_alternatingGroup.mp (θ' y).2
  have hinj : Function.Injective rho := by
    intro y y' h
    apply hθ'inj
    apply Subtype.ext
    ext x
    by_cases hxa : x = a
    · rw [hxa, (hfix y).1, (hfix y').1]
    by_cases hxb : x = b
    · rw [hxb, (hfix y).2, (hfix y').2]
    obtain ⟨p, hp⟩ : ∃ p, ((e p : {i : Fin (m + 2) // i ≠ a ∧ i ≠ b}) : Fin (m + 2)) = x :=
      ⟨e.symm ⟨x, hxa, hxb⟩, by simp⟩
    rw [← hp, ← hrho y p, ← hrho y' p, h]
  let rhoA : ↥Y →* alternatingGroup (Fin m) :=
    rho.codRestrict (alternatingGroup (Fin m)) (fun y => Perm.mem_alternatingGroup.mpr (hsign y))
  let φ : alternatingGroup (Fin m) →* alternatingGroup (Fin m) :=
    rhoA.comp θY.symm.toMonoidHom
  have hφinj : Function.Injective φ := by
    intro s s' h
    have h1 : rho (θY.symm s) = rho (θY.symm s') := congrArg Subtype.val h
    exact θY.symm.injective (hinj h1)
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφinj
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m
    (by omega) (by omega)).2 (MulEquiv.ofBijective φ hφbij)
  have key : ∀ σ : alternatingGroup (Fin m),
      ((φ σ : alternatingGroup (Fin m)) : Perm (Fin m)) = π * (σ : Perm (Fin m)) * π⁻¹ := by
    intro σ
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
      ((f σ : alternatingGroup (Fin m)) : Perm (Fin m))) hπ
    simp only [MulAut.conjNormal_apply] at h1
    exact h1.symm
  refine ⟨fun p => ((e (π p) : {i : Fin (m + 2) // i ≠ a ∧ i ≠ b}) : Fin (m + 2)), ?_, ?_, ?_, ?_⟩
  · intro p q h
    exact π.injective (e.injective (Subtype.ext h))
  · intro p
    exact (e (π p)).2
  · intro r hra hrb
    refine ⟨π.symm (e.symm ⟨r, hra, hrb⟩), ?_⟩
    simp
  · intro y hy p
    have hrhoy : (rho ⟨y, hy⟩ : Perm (Fin m)) = π * (θY ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹ := by
      have := key (θY ⟨y, hy⟩)
      simpa [φ, rhoA] using this
    have hmain := hrho ⟨y, hy⟩ (π p)
    have h3 : rho ⟨y, hy⟩ (π p) = π ((θY ⟨y, hy⟩ : Perm (Fin m)) p) := by
      rw [hrhoy]
      simp
    rw [h3] at hmain
    exact hmain.symm

end CFSG.CGT.PushingUpLit.CGT6

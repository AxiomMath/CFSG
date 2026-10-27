module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KLCE.Sector

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

theorem mem_lang_torus_of_datum
    {τ : Tag} {L : Type} [Field L] (F : ModGL τ L →* ModGL τ L) {A : Subgroup (ModGL τ L)}
    (hFix : ∀ x ∈ A, F x = x) {g0 n : ModGL τ L} (hg0 : F g0 = g0 * n)
    (hT : ∀ x ∈ A, g0⁻¹ * x * g0 ∈ torusGroup τ L) :
    ∀ x ∈ A, x ∈ (twistedTorusOf n F).map (MulAut.conj g0).toMonoidHom := by
  intro x hx
  refine ⟨g0⁻¹ * x * g0, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_twistedTorusOf]
    refine ⟨hT x hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hFix x hx, hg0]
    group
  · change g0 * (g0⁻¹ * x * g0) * g0⁻¹ = x
    group

section Lang


variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {ι : Type}

theorem lang_familyGroup_of_mapsTo {τ : Tag} (a : ι → Fin τ.rank → Lˣ) (e : ℕ) (he : 1 ≤ e)
    (Q : ModGL τ L)
    (hst : ∀ g ∈ familyGroup (K := L) a, frobTwistGL τ L ℓ e Q g ∈ familyGroup (K := L) a) :
    ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (Q * entrywiseFrobGL τ L ℓ e z * Q⁻¹) = c := by
  have hZ : IsConnectedAlgebraicSubgroup L
      ((familyGroup (K := L) a).map (modGLPoint τ L).toMonoidHom) := by
    have := isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := τ) (k := L)
      (familyChar a)
    rwa [kernelRoots_familyChar] at this
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he Q hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply] at hzc; exact hzc⟩

theorem twFrob_mem_familyGroup (t : TwistTag) {Fr : L →+* L} (hFr : Function.Surjective Fr)
    (w : WeylGroup t.tag) (a : ι → Fin t.tag.rank → Lˣ)
    (himg : (fun α => w • permLattice t.perm α) '' familyKernel a = familyKernel a)
    {g : ModGL t.tag L} (hg : g ∈ familyGroup (K := L) a) :
    twFrob t (canonicalRep (coxeterSystem t.tag) L w) Fr g ∈ familyGroup (K := L) a := by
  have hle : (familyGroup (K := L) a).map (twFrob t (canonicalRep (coxeterSystem t.tag) L w) Fr) ≤
      familyGroup (K := L) a := by
    rw [familyGroup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [twFrob_rootDiagUnit]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [map_twFrob_rootSpan t hFr w (fun α hα => hα.1), himg]
      exact le_sup_right
  exact hle ⟨g, hg, rfl⟩

theorem exists_lang_datum_of_plane_twisted (t : TwistTag) (f : ℕ) (hf : 1 ≤ f)
    (a : ι → Fin t.tag.rank → Lˣ) {g : ModGL t.tag L} (hg : g ∈ adjointGroup t.tag L)
    (hn : ∀ s, (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g) *
      twistHom t L (iterateFrobenius L ℓ f) (rootDiagUnit t.tag (a s)) *
      (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g)⁻¹ = rootDiagUnit t.tag (a s)) :
    ∃ (w' : WeylGroup t.tag) (z : ModGL t.tag L), z ∈ familyGroup (K := L) a ∧
      (g * z)⁻¹ * twistHom t L (iterateFrobenius L ℓ f) (g * z) =
        canonicalRep (coxeterSystem t.tag) L w' := by
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L ℓ f := ⟨_, rfl⟩
  rw [← hFrdef] at hn ⊢
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFrdef, iterateFrobenius_def, hx]⟩
  have hFrinj : Function.Injective (Units.map Fr.toMonoidHom) := fun x y h =>
    Units.ext (Fr.injective (congrArg Units.val h))
  obtain ⟨F, hF⟩ : ∃ F : ModGL t.tag L →* ModGL t.tag L, F = twistHom t L Fr := ⟨_, rfl⟩
  rw [← hF] at hn ⊢
  have hnG : g⁻¹ * F g ∈ adjointGroup t.tag L :=
    mul_mem (inv_mem hg) (hF ▸ twistHom_mem_adjointGroup t L Fr hg)
  obtain ⟨a'', ha''⟩ : ∃ a'' : ι → Fin t.tag.rank → Lˣ,
      a'' = fun s i => Units.map Fr.toMonoidHom (a s (t.perm.symm i)) := ⟨_, rfl⟩
  have hFd : ∀ s, F (rootDiagUnit t.tag (a s)) = rootDiagUnit t.tag (a'' s) := fun s => by
    rw [hF, twistHom_rootDiagUnit_eq, ha'']
  obtain ⟨w, hwconj⟩ := exists_weyl_of_conj_family t.tag L a a'' hnG (fun s => by
    rw [← hFd]
    exact hn s)
  have hw : ∀ s v, rootChar (a s) (w • v) =
      Units.map Fr.toMonoidHom (rootChar (a s) (permLattice t.perm.symm v)) := by
    intro s v
    rw [(rootDiagUnit_eq_conj_canonicalRep_iff (K := L) (a s) (a'' s) w).1 (hwconj s) v, ha'']
    rw [rootChar_map_tuple Fr (fun i => a s (t.perm.symm i)) v,
      rootChar_permLattice (a s) t.perm.symm v]
  obtain ⟨nw, hnw⟩ : ∃ nw, nw = canonicalRep (coxeterSystem t.tag) L w := ⟨_, rfl⟩
  have hnwG : nw ∈ adjointGroup t.tag L := hnw ▸ canonicalRep_mem_adjointGroup _ L w
  have hc : (g⁻¹ * F g) * nw⁻¹ ∈ familyCentralizer t.tag L a := by
    refine mem_familyCentralizer.2 ⟨mul_mem hnG (inv_mem hnwG), fun s => ?_⟩
    have h1 := hwconj s
    rw [← hnw] at h1
    have h2 : nw⁻¹ * rootDiagUnit t.tag (a s) * nw = F (rootDiagUnit t.tag (a s)) := by
      rw [hFd, h1]
      group
    have h3 : ((g⁻¹ * F g) * nw⁻¹) * rootDiagUnit t.tag (a s) * ((g⁻¹ * F g) * nw⁻¹)⁻¹ =
        rootDiagUnit t.tag (a s) := by
      calc ((g⁻¹ * F g) * nw⁻¹) * rootDiagUnit t.tag (a s) * ((g⁻¹ * F g) * nw⁻¹)⁻¹
          = (g⁻¹ * F g) * (nw⁻¹ * rootDiagUnit t.tag (a s) * nw) * (g⁻¹ * F g)⁻¹ := by group
        _ = rootDiagUnit t.tag (a s) := by rw [h2]; exact hn s
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  obtain ⟨w₁, hw₁, m, hm, hcm⟩ := familyCentralizer_le_mul t.tag L a hc
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w₁ w
  have hkM : k ∈ familyGroup (K := L) a := Subgroup.mem_sup_left hk
  have hn' : g⁻¹ * F g = (m * k) * canonicalRep (coxeterSystem t.tag) L (w₁ * w) := by
    have : g⁻¹ * F g = (g⁻¹ * F g) * nw⁻¹ * nw := by group
    rw [this, hcm, mul_assoc m, hnw, hkk]
    group
  have h2 : (fun α => w • permLattice t.perm α) '' familyKernel a = familyKernel a := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨IsRoot.smul (hα.permLattice t.cartan_perm) w, fun s => ?_⟩
      rw [hw, CFSG.LieType.Chevalley.permLattice_symm_permLattice, hαa s, map_one]
    · rintro ⟨hβ, hβa⟩
      refine ⟨permLattice t.perm.symm (w⁻¹ • β), ⟨?_, fun s => ?_⟩, ?_⟩
      · have hr : IsRoot t.tag (w⁻¹ • β) := IsRoot.smul hβ w⁻¹
        have := hr.permLattice (π := t.perm.symm) (fun i j => by
          have h := t.cartan_perm (t.perm.symm i) (t.perm.symm j)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm)
        exact this
      · apply hFrinj
        rw [map_one, ← hw s (w⁻¹ • β), smul_inv_smul, hβa s]
      · simp only
        rw [CFSG.LieType.Chevalley.permLattice_permLattice_symm, smul_inv_smul]
  have himg : (fun α => (w₁ * w) • permLattice t.perm α) '' familyKernel a = familyKernel a := by
    have e : (fun α => (w₁ * w) • permLattice t.perm α) =
        (fun α => w₁ • α) ∘ (fun α => w • permLattice t.perm α) :=
      funext fun α => mul_smul w₁ w _
    rw [e, Set.image_comp, h2, image_familyKernel hw₁]
  have hLang : ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (canonicalRep (coxeterSystem t.tag) L (w₁ * w) * F z *
        (canonicalRep (coxeterSystem t.tag) L (w₁ * w))⁻¹) = c := by
    have hst : ∀ x ∈ familyGroup (K := L) a, frobTwistGL t.tag L ℓ f
        (canonicalRep (coxeterSystem t.tag) L (w₁ * w) * diagramMap t L) x ∈
          familyGroup (K := L) a := by
      intro x hx
      have e : frobTwistGL t.tag L ℓ f
          (canonicalRep (coxeterSystem t.tag) L (w₁ * w) * diagramMap t L) x =
            twFrob t (canonicalRep (coxeterSystem t.tag) L (w₁ * w)) Fr x := by
        rw [frobTwistGL_apply, twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply, hFrdef]
        group
      rw [e]
      exact twFrob_mem_familyGroup t hFrs (w₁ * w) a himg hx
    intro c hc
    obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo ℓ a f hf _ hst c hc
    refine ⟨z, hz, ?_⟩
    rw [← hzc, hF, CFSG.LieType.Chevalley.twistHom_apply, hFrdef]
    group
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj F (M := familyGroup (K := L) a)
    (mul_mem hm hkM) hn' hLang
  exact ⟨w₁ * w, z, hz, hzF⟩

theorem exists_lang_torus_of_conj_torus_twisted (t : TwistTag) (f : ℕ) (hf : 1 ≤ f)
    {A : Subgroup (ModGL t.tag L)}
    (hFix : ∀ x ∈ A, twistHom t L (iterateFrobenius L ℓ f) x = x) {g : ModGL t.tag L}
    (hg : g ∈ adjointGroup t.tag L) (hgA : ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup t.tag L) :
    ∃ v : WeylGroup t.tag, ∃ g0 ∈ adjointGroup t.tag L,
      twistHom t L (iterateFrobenius L ℓ f) g0 = g0 * canonicalRep (coxeterSystem t.tag) L v ∧
      ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v)
        (twistHom t L (iterateFrobenius L ℓ f))).map (MulAut.conj g0).toMonoidHom := by
  classical
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  have hn : ∀ x : A, (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g) *
      twistHom t L (iterateFrobenius L ℓ f) (rootDiagUnit t.tag (a x)) *
      (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g)⁻¹ = rootDiagUnit t.tag (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x x.2]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane_twisted ℓ t f hf a hg hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : twistHom t L (iterateFrobenius L ℓ f) (g * z) =
      (g * z) * canonicalRep (coxeterSystem t.tag) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', g * z, mul_mem hg hzG, hu, mem_lang_torus_of_datum _ hFix hu fun x hx => ?_⟩
  have hzd : z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z = rootDiagUnit t.tag (a ⟨x, hx⟩) := by
    have := hzcomm ⟨x, hx⟩
    rw [mul_inv_eq_iff_eq_mul] at this
    calc z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z = z⁻¹ * (rootDiagUnit t.tag (a ⟨x, hx⟩) * z) := by
          group
      _ = z⁻¹ * (z * rootDiagUnit t.tag (a ⟨x, hx⟩)) := by rw [this]
      _ = rootDiagUnit t.tag (a ⟨x, hx⟩) := by group
  have ht : (g * z)⁻¹ * x * (g * z) = rootDiagUnit t.tag (a ⟨x, hx⟩) := by
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = rootDiagUnit t.tag (a ⟨x, hx⟩) := by rw [ha ⟨x, hx⟩, hzd]
  rw [ht]
  exact rootDiagUnit_mem_torusGroup _

theorem exists_lang_torus_of_conj_torus_twisted' (t : TwistTag) (f : ℕ) (hf : 1 ≤ f)
    {A : Subgroup (ModGL t.tag L)}
    (hFix : ∀ x ∈ A, twistHom t L (iterateFrobenius L ℓ f) x = x) {C : ModGL t.tag L}
    (hC : C ∈ adjointGroup t.tag L) (hCA : ∀ x ∈ A, C * x * C⁻¹ ∈ torusGroup t.tag L) :
    ∃ v : WeylGroup t.tag, ∃ g0 ∈ adjointGroup t.tag L,
      twistHom t L (iterateFrobenius L ℓ f) g0 = g0 * canonicalRep (coxeterSystem t.tag) L v ∧
      ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v)
        (twistHom t L (iterateFrobenius L ℓ f))).map (MulAut.conj g0).toMonoidHom :=
  exists_lang_torus_of_conj_torus_twisted ℓ t f hf hFix (inv_mem hC) fun x hx => by
    rw [inv_inv]
    exact hCA x hx

end Lang

theorem twistedE6PlaneToralLang_proved :
    TwistedE6PlaneToralLang := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK K₁ _ _ ι S hS A hAS hexp hcard Fr hFr hFix
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))).symm
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) ℓ f :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  subst hFr'
  obtain ⟨C, hC, hCA⟩ := exists_conj_le_torusGroup_of_isotropic_plane_E6 h3 ι hS hAS hexp hcard
  exact exists_lang_torus_of_conj_torus_twisted' ℓ TwistTag.E6 f hf hFix hC hCA

end CFSG.HardMathSupport.Timmesfeld.CrossChar

module

public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.HardMathSupport.Lang.TwE6Step3.D4LayerTools
public import CFSG.HardMathSupport.Lang.TwE6Step3.PlaneConj
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.HardMathSupport.Lang.SeitzPlane.Tw6D4LayerData

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThree.Chevalley (d4Support d4Layer)

open CFSG.RankThree.PartOne.CTP (ExtSeitzAtInnerFor)

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)

open CFSG.HardMathSupport.Malle.SeitzCube (PlaneGen)

open CFSG.HardMathSupport.Timmesfeld.CrossChar (mul_comm_of_sylowTorus)

open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def D4Split (L : Type)
    [Field L] (Fr : L →+* L) (S : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∀ m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S, tw6Theta L Fr m = m →
    ∃ t ∈ torusGroup Tag.E6 L, tw6Theta L Fr t = t ∧ ∃ a ∈ rootSpan Tag.E6 L S,
      tw6Theta L Fr a = a ∧ m = t * a

section Main



theorem le_hyperClosure_of_kernel_D4 {ℓ f : ℕ} [hℓF : Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (hphi : ℓ ≠ 2 → PhiPlaneGenAt (-1) p)
    (hext : ℓ = 2 → ExtSeitzAtInnerFor (.trialityD4 ⟨ℓ, f, hℓF.out, hf⟩) fun _ => True)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 d4Support)
    (hsplit : D4Split L (iterateFrobenius L ℓ f) (torusRootKernel (psiT g0 c y)))
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) :
    k ∈ hyperClosure p ⊤ E := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  set Sx := torusRootKernel (psiT g0 c y) with hSxdef
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L :=
    fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  obtain ⟨hpq', hord6, -, -, hp7, -⟩ := e6Six_data hpF.out hp3 hpq
  have hpℓ : p ≠ ℓ := fun h => hpq' (by rw [h]; exact dvd_pow_self ℓ (by omega))
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have : Finite (fixSubfield σ) := inferInstance
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  obtain ⟨-, hfinP, hqsP, -, -, e4, g4, he4, -, ⟨hPequiv⟩⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.tw6_D4_layer_data' (K := fixSubfield σ) (Fr := Fr)
      (ℓ := ℓ) (f := f) hf hkc hFr (hT y hy) hw
  set P : Subgroup (ModGL Tag.E6 L) :=
    rootSpan Tag.E6 L Sx ⊓ twistedFixedPoints (tw6N L) (twistE6 L Fr) with hP
  have hperfP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hqsP.1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, hfix, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0
    hperf hyo c (hT y hy)
  let ψh : twistedE6RootGroup K σ →* ModGL Tag.E6 L :=
    MonoidHom.mk' (psiT g0 c) (psiT_mul g0 c)
  have hψh : ∀ x, ψh x = psiT g0 c x := fun _ => rfl
  set Y : Subgroup (twistedE6RootGroup K σ) := (rootSpan Tag.E6 L Sx).comap ψh with hY
  have hmemY : ∀ x, x ∈ Y ↔ psiT g0 c x ∈ rootSpan Tag.E6 L Sx := fun x => Iff.rfl
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET y hy)
  have hcy : rootSpan Tag.E6 L Sx ≤ Subgroup.centralizer {psiT g0 c y} := by
    rw [hb]
    refine CFSG.LieType.Chevalley.rootSpan_le_centralizer b ?_
    rw [hSxdef, hb, torusRootKernel_rootDiagUnit]
  have hYy : ∀ g ∈ Y, g * y = y * g := by
    intro g hg
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcy hg)
    exact commute_of_psiT_commute (g0 := g0) (c := c) hc
  have hYθ : ∀ x ∈ Y, psiT g0 c x ∈ twistedFixedPoints (tw6N L) (twistE6 L Fr) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hYy x hx
    have h := hfix ⟨x, hxC⟩
    rw [hψ] at h
    exact h
  have hPsurj : ∀ u ∈ P, ∃ x : twistedE6RootGroup K σ, psiT g0 c x = u := by
    intro u hu
    have hadjP : P ≤ adjointGroup Tag.E6 L := fun v hv => rootSpan_le_adjointGroup L Sx hv.1
    have hfixP : ∀ v ∈ P, tw6N L * twistE6 L Fr v * (tw6N L)⁻¹ = v := fun v hv => hv.2
    exact exists_psiT_eq_of_mem hg0C hg0 hperf c hfinP hperfP hadjP hfixP hu
  let φ0 : ↥Y →* ↥P :=
    (ψh.comp Y.subtype).codRestrict P (fun x => ⟨x.2, hYθ x x.2⟩)
  have hφ0 : Function.Bijective φ0 := by
    refine ⟨fun a b hab => ?_, fun u => ?_⟩
    · apply Subtype.ext
      apply psiT_injective g0 c
      exact congrArg Subtype.val hab
    · obtain ⟨x, hx⟩ := hPsurj u u.2
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [hmemY, hx]
      exact u.2.1
  let eY : ↥Y ≃* ↥P := MulEquiv.ofBijective φ0 hφ0
  have hYfin : Finite Y := Finite.of_equiv _ eY.symm.toEquiv
  let φY : ↥Y ≃* ↥(d4Layer Fr e4) :=
    eY.trans (hPequiv.trans (CFSG.HardMathSupport.Malle.SeitzCube.d4ThetaFixedEquivLayer Fr e4))
  obtain ⟨hgen, ⟨F, hF, hFc⟩, hcen⟩ := d4_layer_facts (K := fixSubfield σ) hf he4 φY
    (by omega) hpℓ hpq hphi hext
  have hdisj : Disjoint (Subgroup.zpowers y) Y := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxY
    have hcomm : ∀ g : ↥Y, g * (⟨x, hxY⟩ : ↥Y) = ⟨x, hxY⟩ * g := by
      intro g
      apply Subtype.ext
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxz
      exact ((show Commute (g : twistedE6RootGroup K σ) y from hYy g g.2).zpow_right n).eq
    exact congrArg Subtype.val (hcen ⟨x, hxY⟩ hcomm)
  have hspan' : ∀ x : twistedE6RootGroup K σ, x * y = y * x →
      psiT g0 c x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hx
    have h := hspan ⟨x, hxC⟩
    rw [hψ] at h
    exact h
  have hYn : ∀ c' : twistedE6RootGroup K σ, c' * y = y * c' → ∀ x ∈ Y, c' * x * c'⁻¹ ∈ Y := by
    intro c' hc' x hx
    have hnorm : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx ≤
        Subgroup.normalizer (rootSpan Tag.E6 L Sx : Set (ModGL Tag.E6 L)) :=
      sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))
        Subgroup.le_normalizer
    have h := (Subgroup.mem_normalizer_iff.1 (hnorm (hspan' c' hc'))) (psiT g0 c x)
    rw [hmemY]
    rw [psiT_mul, psiT_mul, psiT_inv]
    exact h.1 hx
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hS := sylowTorus_twistedE6_six hℓ hf K hK σ hσ hpF.out hp7 hpq' hord6
  have hFmap : IsElemAbelian p (F.map Y.subtype) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF Y.subtype
  have hFmapc : Nat.card (F.map Y.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hFc]
  have hFY : F.map Y.subtype ≤ Y := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨E', hE'E, hE'Y, hE'ab, hE'c⟩ := exists_plane_le_cube_inf (p := p)
    (fun Q hQ a ha b hb => mul_comm_of_sylowTorus hS hQ ha hb)
    (fun F hF => hS.rank_le hpF.out hF) hE hEc hy hYy hYn hFmap hFmapc hFY
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk := hspan' k hk
  have hθk : tw6Theta L Fr (psiT g0 c k) = psiT g0 c k := by
    have h := hfix ⟨k, hkC⟩
    rw [hψ] at h
    rw [tw6Theta_apply]
    exact h
  obtain ⟨t, htH, htθ, a, haS, haθ, hdec⟩ := hsplit _ hψk hθk
  have haP : a ∈ P := by
    refine ⟨haS, ?_⟩
    show tw6N L * twistE6 L Fr a * (tw6N L)⁻¹ = a
    rw [← tw6Theta_apply]
    exact haθ
  obtain ⟨x, hx⟩ := hPsurj a haP
  have hxY : x ∈ Y := by
    rw [hmemY, hx]
    exact haS
  set k₀ := k * x⁻¹ with hk₀
  have hψk₀ : psiT g0 c k₀ = t := by
    rw [hk₀, psiT_mul, psiT_inv, hx, hdec]
    group
  have hk₀e : ∀ e ∈ E, k₀ * e = e * k₀ := fun e he =>
    commute_of_psiT_commute (by rw [hψk₀]; exact torusGroup_comm htH (hET e he))
  have hkeq : k = k₀ * x := by rw [hk₀]; group
  rw [hkeq]
  exact mem_hyperClosure_of_split hE hEc hy hy1 hYy hdisj hE'E hE'Y hE'c hgen hk₀e hxY

theorem linesOfType_D4_of_ext (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r)
    (hext : ∀ q : TauCeti.PrimePower, q.p = 2 →
      ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True) : LinesOfType IsD4Kernel := by
  intro ℓ f hℓF K _ _ _ hf hK σ hσ p hpF hp3 hpq L _ _ _ _ g0 hg0C hg0 hperf E hE hEc c hT y hy
    hy1 hP k hk
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨w, hw0⟩ := hP
  have hw : (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 d4Support := hw0
  have hFr : ∀ c, (iterateFrobenius L ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hp7 : 7 ≤ p := (e6Six_data hpF.out hp3 hpq).2.2.2.2.1
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓF.out.one_lt
  have hvS := tw6_torusRootKernel_smul_stable hFr (hT y hy)
  have hT' : ∀ β ∈ parabolicRoots Tag.E6 d4Support,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 d4Support := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  have hSx : torusRootKernel (psiT g0 c y) =
      (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 d4Support := by
    rw [← hw, Set.image_image]
    simp
  have hsplit : D4Split L (iterateFrobenius L ℓ f) (torusRootKernel (psiT g0 c y)) := by
    rw [hSx]
    intro m hm hθm
    exact fixedSplit_of_block hq2 hFr hT' hm hθm
  exact le_hyperClosure_of_kernel_D4 K hf hK σ hσ hp3 hpq (fun _ => h6 p (by omega))
    (fun hℓ2 => hext ⟨ℓ, f, hℓF.out, hf⟩ hℓ2) L hg0C hg0 hperf hE hEc c hT hy hy1 hw hsplit hk

end Main

end CFSG.HardMathSupport.Lang.TwE6Step3

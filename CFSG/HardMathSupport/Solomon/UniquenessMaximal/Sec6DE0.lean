module

public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoSubgroup
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inputFT : InputFeitThompson := fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h

theorem barX_comm_of_ne {X A C : Subgroup G} (hA : GLAPComponent 3 X A) (hC : GLAPComponent 3 X C)
    (hne : A ≠ C) : ∀ u ∈ barX 3 X A, ∀ v ∈ barX 3 X C, u * v = v * u := by
  intro u hu v hv
  have hb : barX 3 X A ≠ barX 3 X C := fun h => hne (glaPComponent_unique hA hC h)
  have hcomm : ⁅barX 3 X A, barX 3 X C⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.2.2.1 hC.2.2.1 hb
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  exact (Subgroup.mem_centralizer_iff.1 (hcen hu) v hv).symm

theorem barCenterX_eq_bot (iL3 : InputL3U3Facts) {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (ht : IsLThreeEps (barOf 3 K)) : barCenterX 3 X K = ⊥ := by
  have hsimp : IsSimpleGroup ↥(barX 3 X K) :=
    ((Lemma512Ns.barXEquiv Nat.prime_three hK.2.1).isSimpleGroup_congr).1
      ((iL3 (barOf 3 K) ht).1
        (Lemma512Ns.isQuasisimple_barX_iff Nat.prime_three hK.2.1 |>.1 hK.2.2.1.2.2).1)
  have hcen : Subgroup.center ↥(barX 3 X K) = ⊥ :=
    center_eq_bot_of_quasisimple_simple hK.2.2.1.2.2 hsimp
  unfold barCenterX
  rw [hcen, Subgroup.map_bot]

theorem exists_elem_nine {Q : Type*} [Group Q] {R : Subgroup Q} (h : IsThreeOnePlusTwo R) :
    ∃ E : Subgroup Q, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ Zc R ≤ E := by
  obtain ⟨⟨r, hr, s, hs, hrs⟩, hcard, hexp⟩ := h
  have h' : IsThreeOnePlusTwo R := ⟨⟨r, hr, s, hs, hrs⟩, hcard, hexp⟩
  have hrZ : r ∉ Zc R := fun hz => hrs ((mem_Zc.1 hz).2 s hs)
  have hr1 : r ≠ 1 := fun h1 => hrs (by rw [h1]; simp)
  have hZc : Nat.card (Zc R) = 3 := h'.card_Zc
  have hr3 : r ^ 3 = 1 := hexp r hr
  have cr : Nat.card ↥(Subgroup.zpowers r) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hr3 hr1]
  have hne : Zc R ≠ Subgroup.zpowers r := by
    intro h0; exact hrZ (h0 ▸ Subgroup.mem_zpowers r)
  have hI := inf_eq_bot_of_card_three hZc cr hne
  have hcent : Subgroup.zpowers r ≤ Subgroup.centralizer (Zc R : Set Q) := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' := mem_Zc.1 hz
    exact (Commute.zpow_right (show Commute z r from hz'.2 r hr) k).eq
  have hN : Subgroup.zpowers r ≤ Subgroup.normalizer (Zc R : Set Q) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hsup := card_sup_mul_card_inf hN
  rw [hI, Subgroup.card_bot, hZc, cr] at hsup
  have hZel : IsElemAbelian 3 (Zc R) := by
    refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext ?_, fun z hz => hexp z (Zc_le R hz)⟩
    exact (mem_Zc.1 a.2).2 b (Zc_le R b.2)
  refine ⟨Zc R ⊔ Subgroup.zpowers r, sup_le (Zc_le R) (Subgroup.zpowers_le.2 hr),
    isElemAbelian_sup_of_commute hZel (isElemAbelian_zpowers hr3) ?_, by omega, le_sup_left⟩
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := Subgroup.mem_centralizer_iff.1 (hcent hg) z hz
  exact this.symm

omit [Finite G] in
theorem not_normalizer_conj {B K : Subgroup G} (hB : IsElemAbelian 3 B) {c : G} (hc : c ∈ B)
    (h : B ≤ Subgroup.normalizer ((GLBConj c K : Subgroup G) : Set G)) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (h hg)
  rw [mem_normalizer_iff_gLBConj_eq]
  have hcg : g * c = c * g := ea_comm hB hg hc
  have e1 : GLBConj c (GLBConj g K) = GLBConj g (GLBConj c K) := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj, hcg]
  have h2 : GLBConj c (GLBConj g K) = GLBConj c K := by rw [e1, h1]
  have h3 := congrArg (GLBConj c⁻¹) h2
  rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h3

theorem barX_mono_le {X A C : Subgroup G} (h : A ≤ C) : barX 3 X A ≤ barX 3 X C :=
  Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hz))

omit [Finite G] in
theorem commutes_sup2 {Q : Type*} [Group Q] {A C : Subgroup Q} {ζ : Q}
    (hA : ∀ u ∈ A, ζ * u = u * ζ) (hC : ∀ u ∈ C, ζ * u = u * ζ) :
    ∀ u ∈ A ⊔ C, ζ * u = u * ζ := by
  have : A ⊔ C ≤ Subgroup.centralizer ({ζ} : Set Q) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hA u hu).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hC u hu).symm
  intro u hu
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hu)).symm

theorem not_mem_A_x (iL3 : InputL3U3Facts) (iK : InputKType) (h515 : Lemma515) {m : ℕ}
    {B : Subgroup G} {b : G} {L A : Subgroup G} (e : Env m B b L A) {x y : G}
    (hxA : x ∈ A) (hx1 : x ≠ 1) {K : Subgroup G}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hnotN : ¬ B ≤ Subgroup.normalizer (K : Set G)) (hy : y ∈ B)
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R) : False := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hxB : x ∈ B := e.X.AB hxA
  have hBX : B ≤ X := fun c hc => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.X.Bel hc hxB
  set Kx := kOf L A x with hKxdef
  have hKx : GLAPComponent 3 X Kx := Ka_comp iL3 e.X hxA hx1
  have hKxB : B ≤ Subgroup.normalizer (Kx : Set G) := Ka_B h515 e hxA hx1
  have hKxt : IsLThreeEps (barOf 3 Kx) := Ka_type iK e hxA hx1
  have hFKx : B ⊓ L ≤ Kx := F_le_Ka e.X x
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates e.X.Bel hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hyy : y * y ∈ B := B.mul_mem hy hy
  have hKx1' : Kx ≠ K := fun h => hnotN (by rw [← h]; exact hKxB)
  have hKx2' : Kx ≠ GLBConj y K := fun h =>
    hnotN (not_normalizer_conj e.X.Bel hy (by rw [← h]; exact hKxB))
  have hKx3' : Kx ≠ GLBConj y (GLBConj y K) := fun h => by
    rw [gLBConj_gLBConj] at h
    exact hnotN (not_normalizer_conj e.X.Bel hyy (by rw [← h]; exact hKxB))
  have ht := hR.triple
  have hcj2 : cj y⁻¹ (R ⊓ K) = R ⊓ GLBConj y K := cj_inv_inf (hR.R_inv hy)
  obtain ⟨E₁, hE₁R, hE₁el, hE₁c, hE₁Z⟩ := exists_elem_nine hR.heis
  obtain ⟨E₂, hE₂R, hE₂el, hE₂c, hE₂Z⟩ := exists_elem_nine ht.heis₂
  rw [hcj2] at hE₂R
  have hE₁K : E₁ ≤ K := hE₁R.trans (inf_le_right)
  have hE₂K : E₂ ≤ GLBConj y K := hE₂R.trans (inf_le_right)
  have hcomm12 : ∀ r ∈ E₁, ∀ s ∈ E₂, r * s = s * r := by
    intro r hr s hs
    refine ht.c12 r (hE₁R hr) s ?_
    rw [hcj2]; exact hE₂R hs
  have hinfZ : E₁ ⊓ E₂ ≤ Zc (R ⊓ K) := by
    intro r hr
    refine mem_Zc.2 ⟨hE₁R hr.1, fun s hs => ?_⟩
    have := ht.c12 s hs r (by rw [hcj2]; exact hE₂R hr.2)
    exact this.symm
  have hcinf : Nat.card ↥(E₁ ⊓ E₂) ≤ 3 :=
    (Subgroup.card_le_of_le hinfZ).trans hR.heis.card_Zc.le
  have hE₀el : IsElemAbelian 3 (E₁ ⊔ E₂) :=
    isElemAbelian_sup_of_commute hE₁el hE₂el (fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun h hh => (hcomm12 a ha h hh).symm)
  have hE₀card : 27 ≤ Nat.card ↥(E₁ ⊔ E₂) := by
    have hN : E₂ ≤ Subgroup.normalizer (E₁ : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro h hh
      exact Subgroup.mem_centralizer_iff.2 fun a ha => hcomm12 a ha h hh
    have h := card_sup_mul_card_inf hN
    rw [hE₁c, hE₂c] at h
    have h1 : Nat.card ↥(E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) ≤ Nat.card ↥(E₁ ⊔ E₂) * 3 :=
      Nat.mul_le_mul_left _ hcinf
    omega
  have hFel : IsElemAbelian 3 (B ⊓ L) :=
    ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (ea_comm e.X.Bel a.2.1 b.2.1),
      fun z hz => e.X.Bel.2 z hz.1⟩
  have hFp : IsPGroup 3 ↥(B ⊓ L) := isPGroup_of_isElemAbelian hFel
  have hFX : B ⊓ L ≤ X := hFKx.trans hKx.1
  have hE₁X : E₁ ≤ X := hE₁K.trans hK.1
  have hE₂X : E₂ ≤ X := hE₂K.trans hK2.1
  have hE₀X : E₁ ⊔ E₂ ≤ X := sup_le hE₁X hE₂X
  have hE₀p : IsPGroup 3 ↥(E₁ ⊔ E₂) := isPGroup_of_isElemAbelian hE₀el
  have key : ∀ P : Subgroup G, GLAPComponent 3 X P → P ≠ K → P ≠ GLBConj y K →
      ∀ u ∈ barX 3 X P, ∀ v ∈ barX 3 X (E₁ ⊔ E₂), u * v = v * u := by
    intro P hP hPK hPK2 u hu v hv
    rw [barX_sup hE₁X hE₂X] at hv
    refine commutes_sup2 (A := barX 3 X E₁) (C := barX 3 X E₂) (ζ := u) ?_ ?_ v hv
    · intro w hw; exact barX_comm_of_ne hP hK hPK u hu w (barX_mono_le hE₁K hw)
    · intro w hw; exact barX_comm_of_ne hP hK2 hPK2 u hu w (barX_mono_le hE₂K hw)
  set Fb := barX 3 X (B ⊓ L) with hFb
  set E0b := barX 3 X (E₁ ⊔ E₂) with hE0b
  have hFb_el : IsElemAbelian 3 Fb := isElemAbelian_barX hFel
  have hE0b_el : IsElemAbelian 3 E0b := isElemAbelian_barX hE₀el
  have hcomm_FE : ∀ u ∈ Fb, ∀ v ∈ E0b, u * v = v * u := fun u hu v hv =>
    key Kx hKx hKx1' hKx2' u (barX_mono_le hFKx hu) v hv
  have hinfbot : Fb ⊓ E0b = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have hmem : u ∈ barCenterX 3 X Kx := by
      rw [mem_barCenterX_iff]
      refine ⟨barX_mono_le hFKx hu.1, fun w hw => ?_⟩
      exact (key Kx hKx hKx1' hKx2' w hw u hu.2).symm
    rw [barCenterX_eq_bot iL3 hKx hKxt, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 hmem
  set E' := Fb ⊔ E0b with hE'
  have hE'el : IsElemAbelian 3 E' :=
    isElemAbelian_sup_of_commute hFb_el hE0b_el (fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun h hh => (hcomm_FE a ha h hh).symm)
  have hNE : E0b ≤ Subgroup.normalizer (Fb : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro h hh
    exact Subgroup.mem_centralizer_iff.2 fun a ha => hcomm_FE a ha h hh
  have hcard := card_sup_mul_card_inf hNE
  rw [hinfbot, Subgroup.card_bot, mul_one] at hcard
  have hcFb : Nat.card Fb = 9 :=
    (card_barX_of_isPGroup Nat.prime_three hFX hFp).trans e.X.Fc
  have hcE0b : Nat.card E0b = Nat.card ↥(E₁ ⊔ E₂) :=
    card_barX_of_isPGroup Nat.prime_three hE₀X hE₀p
  have hE'card : 243 ≤ Nat.card E' := by
    rw [hE', hcard, hcFb, hcE0b]; omega
  have hNcore : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥X)
  obtain ⟨S, hSel, hSmap, hScard⟩ :=
    exists_elemAbelian_lift (p := 3) (GLAPPrimeCore 3 ↥X) hNcore hE'el
  set S' := S.map X.subtype with hS'
  have hS'el : IsElemAbelian 3 S' := CFSG.SectionRank.isElemAbelian_map hSel X.subtype
  have hS'p : IsPGroup 3 ↥S' := isPGroup_of_isElemAbelian hS'el
  have hS'X : S' ≤ X := by rintro _ ⟨s, -, rfl⟩; exact s.2
  have hS'card : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective X.subtype_injective
  have hLA : ⁅GLBConj y (GLBConj y K), S'⁆ ≤ GLAPPrimeCoreOf 3 X := by
    refine Subgroup.commutator_le.2 fun k hk s hs => ?_
    obtain ⟨s0, hs0, rfl⟩ := hs
    have hkX : k ∈ X := hK3.1 hk
    have hmemE : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) s0 ∈ E' := by
      rw [← hSmap]; exact ⟨s0, hs0, rfl⟩
    have hku : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩ ∈
        barX 3 X (GLBConj y (GLBConj y K)) := mem_barX_iff.2 ⟨⟨k, hkX⟩, hk, rfl⟩
    have hcom : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) s0 =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) s0 *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩ := by
      refine commutes_sup2 (A := Fb) (C := E0b) (ζ := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩)
        ?_ ?_ _ hmemE
      · intro w hw
        exact barX_comm_of_ne hK3 hKx hKx3'.symm _ hku w (barX_mono_le hFKx hw)
      · intro w hw
        exact key _ hK3 hne2.symm hne3.symm _ hku w hw
    have hone : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨k, hkX⟩ * s0 * ⟨k, hkX⟩⁻¹ * s0⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcom
    have := (mem_coreOf_iff (p := 3) (X := X)
      (⟨k, hkX⟩ * s0 * ⟨k, hkX⟩⁻¹ * s0⁻¹)).2 ((QuotientGroup.eq_one_iff _).1 (by exact hone))
    exact this
  obtain ⟨T, hT0, hT2, hTN⟩ := exists_twoGroup_normalized_of_centralizes inputFT Nat.prime_three
    (by norm_num) hK3 hS'X hS'p hLA
  obtain ⟨k, hk⟩ := exists_card_eq_pow hS'p
  have hk5 : 5 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    (X := G) (p := 3) (by norm_num) hT0 hT2 hS'el hTN hk
  have h4 : GLATwoLocalRank 3 G = 4 := e.C.2.1
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

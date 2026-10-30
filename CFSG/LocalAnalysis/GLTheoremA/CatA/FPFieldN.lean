module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.YS09Field

section Order

variable {M R S : Type*} [Group M] [Group R] [Group S]

theorem graph_orderOf_dvd (H : Subgroup M) (π : H →* R) (hπ : Function.Surjective π)
    (act : S → M → M) (hact1 : ∀ x, act 1 x = x)
    (hactmul : ∀ a b x, act (a * b) x = act a (act b x)) (hstab : ∀ a (h : H), act a h ∈ H)
    (rel : S → H → H → Prop) (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h)
    {a : S} {f : MulAut R} (hf : LargeEvenGraphAut π (rel a) f) : orderOf f ∣ orderOf a := by
  have h1 := graph_pow H π act hact1 hactmul hstab rel hrel a f hf (orderOf a)
  rw [pow_orderOf_eq_one] at h1
  have h2 : LargeEvenGraphAut π (rel 1) (1 : MulAut R) := fun h h' hh' => by
    have : (h' : M) = h := by rw [(hrel _ _ _).1 hh', hact1]
    rw [Subtype.ext this]; rfl
  exact orderOf_dvd_of_pow_eq_one (graph_unique H π hπ act hstab rel hrel h1 h2)

end Order

section FieldDeg

open scoped Matrix

theorem natCard_ringEquiv_of_card {K : Type} [Field K] [Finite K] {j : ℕ}
    (hK : Nat.card K = 2 ^ j) : Nat.card (K ≃+* K) = j :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1

theorem matField_orderOf_dvd {ι K R : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [Group R] (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (π : H →* R) (hπ : Function.Surjective π) :
    ∀ f ∈ LargeEvenMatFieldImage π, orderOf f ∣ Nat.card (K ≃+* K) := by
  rintro f ⟨σ, hσ⟩
  exact (graph_orderOf_dvd (S := K ≃+* K) H π hπ
    (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g) glMap_one glMap_mul
    (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
    (fun τ h h' => by rw [Units.ext_iff, coe_glMap]) hσ).trans (orderOf_dvd_natCard σ)

theorem chevField_orderOf_dvd {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K] [Finite K]
    (H : Subgroup (LargeEvenChevGL A K)) (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, chevAct A K σ h ∈ H) :
    ∀ f ∈ LargeEvenChevFieldImage A K H, orderOf f ∣ Nat.card (K ≃+* K) := by
  rintro f ⟨σ, hσ⟩
  exact (graph_orderOf_dvd (S := K ≃+* K) H (LargeEvenCenterMk H)
    (QuotientGroup.mk'_surjective _) (fun τ g => chevAct A K τ g) (chevAct_one A K)
    (fun a b x => chevAct_mul A K a b x) (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
      LargeEvenEntrywise A K τ (map_zero τ)
        ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
    (fun τ h h' => by rw [Units.ext_iff, chevAct_val]) hσ).trans (orderOf_dvd_natCard σ)

theorem phiQ_orderOf_dvd {n j : ℕ} (hn4 : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2 ^ j) :
    ∀ f ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))), orderOf f ∣ 2 * j := by
  intro f hf
  obtain ⟨k, hk⟩ := CFSG.StandardType.RecipeFieldOmega.congr_minusEquiv_of_mem_phi hn4 hirr hf
  refine orderOf_dvd_of_pow_eq_one ?_
  apply (MulAut.congr (CFSG.StandardType.RecipeFieldOmega.minusEquiv hn4 b c)).injective
  rw [map_pow, hk, map_one, ← pow_mul, pow_mul',
    CFSG.StandardType.AutOm.frobAut_pow_two_mul hn4 hirr hK, one_pow]

@[expose] def fieldDeg (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .twA | .twD | .twE6 => 2 * lab.n
  | .triD4 => 3 * lab.n
  | _ => lab.n

@[expose] def FieldDegDvd (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ _ F =>
  ∀ f ∈ F, orderOf f ∣ fieldDeg lab

abbrev DegCont (j : ℕ) (Q : LargeEvenRawCont) : LargeEvenRawCont :=
  fun R _ I F => Q R I F ∧ ∀ f ∈ F, orderOf f ∣ j

theorem recLinear_deg {d j N : ℕ} (hN : N = 2 ^ j) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeLinear d N Q) : LargeEvenRecipeLinear d N (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have h1 := matField_orderOf_dvd _ (fun σ g hg => sl_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _) f hf
  rwa [natCard_ringEquiv_of_card (hK.trans hN)] at h1

theorem recUnitary_deg {d j : ℕ} (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeUnitary d (2 ^ j) Q) :
    LargeEvenRecipeUnitary d (2 ^ j) (DegCont (2 * j) Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  have h1 := matField_orderOf_dvd _ (fun σ g hg => su_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _) f hf
  rwa [natCard_ringEquiv_of_card hK'] at h1

theorem recSymplectic_deg {m j q : ℕ} (hq : q = 2 ^ j) (derived : Bool) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeSymplectic m q derived Q) :
    LargeEvenRecipeSymplectic m q derived (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hH : ∀ σ : K ≃+* K, ∀ g ∈ (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆
      else LargeEvenSpGroup K m), Matrix.GeneralLinearGroup.map σ.toRingHom g ∈
      (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m) := by
    intro σ g hg
    cases derived
    · exact sp_map_mem σ g hg
    · exact derived_stable _ _ (fun x hx => sp_map_mem σ x hx) hg
  have h1 := matField_orderOf_dvd _ hH _ (QuotientGroup.mk'_surjective _) f hf
  rwa [natCard_ringEquiv_of_card (hK.trans hq)] at h1

theorem recOmegaPlus_deg {m j : ℕ} (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeOmegaPlus m (2 ^ j) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ j) (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have h1 := matField_orderOf_dvd _ (fun σ g hg => omegaPlus_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _) f hf
  rwa [natCard_ringEquiv_of_card hK] at h1

theorem recSuzuki_deg {a j : ℕ} (Q : LargeEvenRawCont) (hj : j = 2 * a + 1)
    (h : LargeEvenRecipeSuzuki a Q) : LargeEvenRecipeSuzuki a (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hK' : Nat.card K = 2 ^ j := hK.trans (by rw [hj])
  have h1 := matField_orderOf_dvd _ (fun σ g hg => sz_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _) f hf
  rwa [natCard_ringEquiv_of_card hK'] at h1

theorem recOmegaMinus_deg {n j : ℕ} (hn4 : 4 ≤ n) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) Q) :
    LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) (DegCont (2 * j) Q) := by
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  exact ⟨K, hF, hfin, hK, b, c, hirr, hQ, phiQ_orderOf_dvd hn4 hirr hK⟩

theorem recChevalley_deg {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {j : ℕ} (derived : Bool)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeChevalley A (2 ^ j) derived Q) :
    LargeEvenRecipeChevalley A (2 ^ j) derived (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have h1 := chevField_orderOf_dvd A K _ (fun σ h hh => chevH_stable A K derived σ h hh) f hf
  rwa [natCard_ringEquiv_of_card hK] at h1

theorem recG2Derived_deg {j : ℕ} (Q : LargeEvenRawCont) (hj : 2 = 2 ^ j)
    (h : LargeEvenRecipeG2Derived Q) : LargeEvenRecipeG2Derived (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have h1 := chevField_orderOf_dvd LargeEvenCartanG2 K _
    (fun σ h hh => chevH_stable LargeEvenCartanG2 K true σ h hh) f hf
  rwa [natCard_ringEquiv_of_card (hK.trans hj)] at h1

theorem recTwisted_deg {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r))
    (m n : ℕ) (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n (DegCont (m * n) Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hK' : Nat.card K = 2 ^ (m * n) := by rw [hK, ← pow_mul, mul_comm]
  have h1 := chevField_orderOf_dvd A K _ (fun σ h hh => twisted_map_mem A K ρ n σ h hh) f hf
  rwa [natCard_ringEquiv_of_card hK'] at h1

theorem recTwF4Inherited_deg (a j : ℕ) (Q : LargeEvenRawCont) (hj : j = 2 * a + 1)
    (h : LargeEvenRecipeTwF4Inherited a Q) : LargeEvenRecipeTwF4Inherited a (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hK' : Nat.card K = 2 ^ j := hK.trans (by rw [hj])
  have h1 := chevField_orderOf_dvd LargeEvenCartanF4 K _ (fun σ h hh => twF4H_map_mem K a σ h hh) f hf
  rwa [natCard_ringEquiv_of_card hK'] at h1

theorem canonFieldDeg {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    MI.CAll lab (FieldDegDvd lab) := by
  intro Q h
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  cases tag
  case A => exact recLinear_deg rfl _ h
  case twA => exact recUnitary_deg _ h
  case B => exact recSymplectic_deg rfl false _ h
  case C => exact recSymplectic_deg rfl false _ h
  case D =>
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢
    · exact recLinear_deg rfl _ h
    · exact recOmegaPlus_deg _ h
  case twD =>
    have h2 : 2 ≤ rank := hlab.2
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h2' h3'
    · exact recLinear_deg (j := 2 * n) (by rw [← pow_mul, mul_comm]) _ h
    · exact recUnitary_deg _ h
    · exact recOmegaMinus_deg (n := rank) (by omega) _ h
  case E6 => exact recChevalley_deg (LargeEvenCartanE 6) false _ h
  case E7 => exact recChevalley_deg (LargeEvenCartanE 7) false _ h
  case E8 => exact recChevalley_deg (LargeEvenCartanE 8) false _ h
  case F4 => exact recChevalley_deg LargeEvenCartanF4 false _ h
  case twE6 => exact recTwisted_deg (LargeEvenCartanE 6) LargeEvenRhoE6 2 n _ h
  case triD4 => exact recTwisted_deg LargeEvenCartanD4 LargeEvenRhoD4 3 n _ h
  case G2 => exact recChevalley_deg LargeEvenCartanG2 false _ h
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hlab.2
    have hk' : n = 2 * k + 1 := hk
    exact recSuzuki_deg (j := n) _ (by omega) h
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hlab.2
    have hk' : n = 2 * k + 1 := hk
    exact recTwF4Inherited_deg _ n _ (by omega) h
  case B2der =>
    obtain ⟨-, hn1⟩ := hlab.2
    have hn1' : n = 1 := hn1
    subst hn1'
    exact recSymplectic_deg (j := 1) (by norm_num) true _ h
  case G2der =>
    obtain ⟨-, hn1⟩ := hlab.2
    have hn1' : n = 1 := hn1
    subst hn1'
    exact recG2Derived_deg (j := 1) _ (by norm_num) h
  case twF4der =>
    obtain ⟨-, hn1⟩ := hlab.2
    have hn1' : n = 1 := hn1
    subst hn1'
    exact recTwF4Inherited_deg _ _ _ (by show 1 = 2 * ((1 - 1) / 2) + 1; omega) h

theorem dvd_n_of_dvd_fieldDeg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) (h : p ∣ fieldDeg lab) : p ∣ lab.n := by
  obtain ⟨tag, rank, n⟩ := lab
  have h2 : ¬ p ∣ 2 := fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  cases tag
  case twA => exact ((Nat.Prime.dvd_mul hp).1 h).resolve_left h2
  case twD => exact ((Nat.Prime.dvd_mul hp).1 h).resolve_left h2
  case twE6 => exact ((Nat.Prime.dvd_mul hp).1 h).resolve_left h2
  case triD4 =>
    have h3' : ¬ p ∣ 3 := fun h' =>
      h3 ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_left h3'
  all_goals exact h

end FieldDeg

section FieldN

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.StandardType


variable {G : Type} [Group G] [Finite G]

theorem catalog_TD4_of_lieModel {R : Type} [Group R] {f : ℕ}
    (h : CFSG.Blueprint.LieModel R .trialityD4 0 2 f) :
    catalogIs R (onLie fun | .trialityD4 _ => True | _ => False) := by
  rcases h with ⟨h1, -⟩ | ⟨-, -, hCEM⟩ | ⟨-, h2, -⟩ | ⟨-, h3, -⟩
  · exact absurd h1 (by decide)
  · obtain ⟨hadm, hm⟩ := hCEM
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
      (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, trivial, ⟨e.trans b⟩⟩
  · exact absurd h2 (by decide)
  · exact absurd h3 (by decide)

theorem fieldNAt_marking {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hF : FieldOn p g L) {P : LargeEvenMarkProp (PQuot p L)}
    (hP : CFSG.Assembly.LargeEvenMarking (PQuot p L) P) :
    CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ => P lab R I F θ ∧ p ∣ lab.n := by
  have h1 := CFSG.StandardType.Canonical.largeEvenMarking_markedModel
    (fieldOn_marking_transport hp hp2 hF hP)
  have h2 := canon_marking_and_labelAll_simple' (P' := FieldDegDvd)
    (fun lab hlab => (canonFieldDeg hlab).mono fun R _ I F h _ _ => h) h1
  refine Canonical.largeEvenMarking_mono ?_ h2
  rintro lab R _ I F θ ⟨⟨⟨hPθ, hadm⟩, hMM⟩, hdeg⟩
  refine ⟨hPθ, ?_⟩
  by_cases hne : lab.tag ≠ .triD4 ∨ p ≠ 3
  · obtain ⟨-, f, hf, u, hu, hord, -⟩ := hadm hne
    have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
      rintro ⟨h, h'⟩
      rcases hne with h0 | h0
      · exact h0 h
      · exact h0 h'
    have := hdeg f hf
    rw [hord] at this
    exact dvd_n_of_dvd_fieldDeg hp hp2 h3 this
  · exfalso
    obtain ⟨ht, hp3⟩ : lab.tag = .triD4 ∧ p = 3 := by
      push Not at hne
      exact hne
    subst hp3
    obtain ⟨tg, rk, nn⟩ := lab
    dsimp only at ht
    subst ht
    have hL : CFSG.Blueprint.LieModel R .trialityD4 0 2 nn := hMM
    obtain ⟨i, hi, ⟨e⟩⟩ := catalog_TD4_of_lieModel hL
    exact td4_not_field_holds (L := L) (g := g) ⟨i, hi, ⟨θ.trans e⟩⟩ hF

theorem fieldNAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) : FieldNAt G p := by
  intro hp hp2 X L g hL hF
  refine ⟨?_, ?_, ?_⟩
  · exact Canonical.largeEvenMarking_mono (fun lab R _ I F θ h => h.2) (fieldNAt_marking hp hp2 hF hF.2)
  · intro hM
    obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, hn1, hpn⟩ :=
      Canonical.largeEvenMarking_exists (fieldNAt_marking hp hp2 hF hM)
    rw [hn1] at hpn
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
  · intro N hM
    obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, hnN, hpn⟩ :=
      Canonical.largeEvenMarking_exists (fieldNAt_marking hp hp2 hF hM)
    rwa [hnN] at hpn

end FieldN

end FP

end CFSG.LocalAnalysis.GLTheoremA

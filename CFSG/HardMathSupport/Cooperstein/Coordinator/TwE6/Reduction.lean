module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Cover
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Periodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OuterChi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.OffenderOut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.RedArith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExcFamilies
public import CFSG.Monster.B.TwoA.Census.PermClasses

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.LieType.Chevalley CFSG.Open
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg


theorem isSimpleRep_comp_surj {G H : Type*} [Group G] [Group H] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k H V) (φ : G →* H)
    (hφ : Function.Surjective φ) (h : IsSimpleRep ρ) : IsSimpleRep (ρ.comp φ) :=
  ⟨h.1, fun W hW => h.2 W fun g w hw => by
    obtain ⟨x, rfl⟩ := hφ g
    exact hW x w hw⟩

theorem sigma_ne_one {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σe : K ≃+* K) (hσ : ∀ c, σe c = c ^ (2 ^ f)) :
    σe ≠ 1 := by
  classical
  intro h1
  have : Fintype K := Fintype.ofFinite K
  have hall : ∀ c : K, c ^ (2 ^ f) = c := fun c => by rw [← hσ, h1]; rfl
  have h2 : 1 < 2 ^ f := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K h2
  have hne : (Polynomial.X ^ (2 ^ f) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K).val ⊆ (Polynomial.X ^ (2 ^ f) - Polynomial.X :
      Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hall c]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at hcard
  have : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
  omega

theorem isCentralCover_of_factor {Ĝ G L : Type*} [Group Ĝ] [Group G] [Group L] [Finite Ĝ]
    {π : Ĝ →* G} (hπ : IsCentralCover π 2) (q : L →* G) (φ : Ĝ →* L)
    (hφs : Function.Surjective φ) (hqφ : ∀ x, q (φ x) = π x) : IsCentralCover φ 2 := by
  have hle : φ.ker ≤ π.ker := fun x hx => by
    rw [MonoidHom.mem_ker, ← hqφ, MonoidHom.mem_ker.1 hx, map_one]
  exact ⟨hφs, fun x hx => hπ.ker_le (hle hx),
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hle) hπ.coprime⟩

theorem exists_lift_elem {Ĝ L : Type*} [Group Ĝ] [Group L] [Finite Ĝ] {φ : Ĝ →* L}
    (hc : IsCentralCover φ 2) (A₀ : Subgroup L) (hA : ∀ x ∈ A₀, x ^ 2 = 1) :
    ∃ Â : Subgroup Ĝ, (∀ a ∈ Â, a ^ 2 = 1) ∧ (∀ a ∈ Â, φ a ∈ A₀) ∧
      Nat.card A₀ ≤ Nat.card Â ∧ (A₀ ≠ ⊥ → Â ≠ ⊥) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 A₀ := fun x => ⟨1, Subtype.ext (by simpa using hA x x.2)⟩
  refine ⟨pLift hc A₀ hP, ?_, fun a ha => ha.1, ?_, ?_⟩
  · intro a ha
    have h2 : a ^ 2 ∈ pLift hc A₀ hP := pow_mem ha 2
    exact pLift_inj (h := hc) h2 (one_mem _) (by rw [map_pow, map_one]; exact hA _ ha.1)
  · have hsurj : Function.Surjective (fun x : pLift hc A₀ hP => (⟨φ x, x.2.1⟩ : A₀)) := by
      intro y
      obtain ⟨x, hx, hxy⟩ := exists_pLift (h := hc) (hP := hP) y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  · intro hne hbot
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    obtain ⟨x, hx, hxy⟩ := exists_pLift (h := hc) (hP := hP) y.2
    have hx1 : x = 1 := by
      have : x ∈ (⊥ : Subgroup Ĝ) := by rw [← hbot]; exact hx
      exact this
    apply hy
    apply Subtype.ext
    rw [← hxy, hx1, map_one]; rfl

theorem finrank_inv_le {Ĝ L k V : Type*} [Group Ĝ] [Group L] [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k L V) (φ : Ĝ →* L)
    (A₀ : Subgroup L) (Â : Subgroup Ĝ) (h : ∀ a ∈ Â, φ a ∈ A₀) :
    Module.finrank k (Representation.invariants (ρ.comp A₀.subtype)) ≤
      Module.finrank k (Representation.invariants ((ρ.comp φ).comp Â.subtype)) :=
  Submodule.finrank_mono fun v hv => by
    rw [Representation.mem_invariants] at hv ⊢
    intro g
    exact hv ⟨φ g, h g g.2⟩

theorem finrank_inv_le_m {G k : Type*} [Group G] [Field k] {m : ℕ}
    (ρ : Representation k G (Fin m → k)) :
    Module.finrank k (Representation.invariants ρ) ≤ m := by
  simpa using Submodule.finrank_le (Representation.invariants ρ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem noIrrFFOffender_twistedE6_of_bounds
    (hT : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      TwTypeBoundStmt hf K hK σ hσ)
    (h27 : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw27SurvivorBound hf K hK σ hσ)
    (h78 : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw78HalfOffenderBound hf K hK σ hσ)
    (hc : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw78CentreTrivial hf K hK σ hσ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  classical
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel hquad
  by_contra hcon
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨f, hfq⟩ : ∃ f, f = q.exponent := ⟨_, rfl⟩
  have hf : 1 ≤ f := hfq ▸ q.exponent_pos
  have hqc : q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hq, hfq]
  set K := GaloisField q.p (2 * q.exponent) with hKdef
  have hK2 : Nat.card K = q.card ^ 2 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  haveI : Finite K := inferInstance
  have hKf : Nat.card K = (2 ^ f) ^ 2 := by rw [hK2, hqc]
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2 * f) (by omega) (by rw [hKf, ← pow_mul]; ring_nf)
  let σ : K →+* K := iterateFrobenius K q.p q.exponent
  have hσq : ∀ x, σ x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact iterateFrobenius_def q.p q.exponent x
  have hσ : ∀ x, σ x = x ^ (2 ^ f) := fun x => by rw [hσq, hqc]
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σe : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσe : σe.toRingHom = σ := rfl
  have hK' : Nat.card K = q.card ^ TwistTag.E6.order := hK2
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq K hK' σ hσq
  let d := derivedCentralQuotientEquiv (t := TwistTag.E6) Nat.prime_two hf hKf σ hσ
  let eS : L ⧸ Subgroup.center L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    e.trans (b.symm.trans d)
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := odd_card_center_of_isIrrOn hW hirr
  have hperf : Group.IsPerfect ↥L := hql.1
  obtain ⟨φ, hφs, hφπ⟩ := exists_cover_hom hf hKf σ hσ hperf hodd eS
  haveI : Nontrivial ↥L := by
    have := hql.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, hιKinj, hWcard, hent, hext, hfix, hdisp⟩ :=
    offender_periodic_data_out hW hperf hirr hEN hE hel hquad hoff (S := ↥L) (MulEquiv.refl _)
      (n := 2 * f) (K := K) (by omega) (by rw [hKf, ← pow_mul]; ring_nf)
  letI : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  have hρ' : IsSimpleRep (ρ.comp φ) := isSimpleRep_comp_surj ρ φ hφs hρ
  have hsplit := twistedCover_split hf hKf σ hσ k
  have hntriv : ∃ x, (ρ.comp φ) x ≠ 1 := by
    refine ⟨hatX hf hKf σ hσ twN0 1, fun h1 => ?_⟩
    have h2 : φ (hatX hf hKf σ hσ twN0 1) = 1 := hρinj (by
      show ρ (φ (hatX hf hKf σ hσ twN0 1)) = ρ 1
      rw [map_one]; exact h1)
    have h3 : coverHom hf hKf σ hσ (hatX hf hKf σ hσ twN0 1) = 1 := by
      rw [← hφπ, h2]; simp
    have h4 : hatX hf hKf σ hσ twN0 1 = 1 :=
      (isCentralCover_coverHom hf hKf σ hσ).eq_one_of_isPElt (MonoidHom.mem_ker.2 h3)
        (isPElt_two_of_sq (hatX_sq hf hKf σ hσ twN0 1))
    exact (twistedE6CoverRankOne hf hKf σ hσ).x_ne_one twN0 (u := 1) h4
  obtain ⟨y, χ, J, ht⟩ := twisted_exists_isCoverType hf hKf σ hσ hρ'
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ' hsplit
  have hmemH : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (w : (orbitField TwistTag.E6 K σ a)ˣ),
      hatH hf hKf σ hσ a w ∈ (twistedE6CoverData hf hKf σ hσ).datum.H := fun a w =>
    (twistedE6CoverRankOne hf hKf σ hσ).hh_mem a w
  have hδper : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hKf σ hσ a w) ^ (2 ^ δ) = χ (hatH hf hKf σ hσ a w) := fun a w =>
    chi_pow_of_entries_datum (twistedE6CoverData hf hKf σ hσ).datum δ hρ'
      (fun s i j => hent (φ s) i j) hμ _ (hmemH a w)
  have hnper : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hKf σ hσ a w) ^ (2 ^ (2 * f)) = χ (hatH hf hKf σ hσ a w) := by
    intro a w
    have h1 := chi_hatH_pow hf hKf σ hσ hμ a w (2 ^ (2 * f))
    have hw : w ^ (2 ^ (2 * f)) = w := by
      apply Units.ext
      apply Subtype.ext
      have : Fintype K := Fintype.ofFinite K
      have hc : (2 : ℕ) ^ (2 * f) = Fintype.card K := by
        rw [← Nat.card_eq_fintype_card, hKf, ← pow_mul]; ring_nf
      have := FiniteField.pow_card ((w : orbitField TwistTag.E6 K σ a) : K)
      rw [← hc] at this
      simpa using this
    rw [hw] at h1
    exact h1.symm
  have hσ' : ∀ c, σe c = c ^ (2 ^ f) := hσ
  obtain ⟨-, -, -, -, -, -, -, hnf, ⟨Θ, hΘrel, hΘsurj, hΘker, -, -, hΘinv⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hKf σe hσ'
  have hσe1 : σe ≠ 1 := sigma_ne_one hf hKf σe hσ'
  have hΘσ : ∀ b : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ), b * b = 1 → Θ b ≠ 1 →
      Θ b = σe := by
    intro b hb h1
    rcases hΘinv b ((pow_two b).trans hb) with h | ⟨h2, -⟩
    · exfalso
      apply h1
      have : b ∈ Θ.ker := hΘker ▸ Subgroup.mem_sup_left h
      exact this
    · exact h2
  have hΘ1 : ∀ b : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ), b * b = 1 →
      Θ b = 1 → b ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →* MulAut _).range := by
    intro b hb h1
    rcases hΘinv b ((pow_two b).trans hb) with h | ⟨h2, -⟩
    · exact h
    · exact absurd (h1.symm.trans h2) (Ne.symm hσe1)
  have hOut : ∀ B : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut _).range) := by
    intro B _ hBsq
    refine (card_le_two_mul_of_theta Θ B ?_).trans (Nat.mul_le_mul_left _
      (Subgroup.card_le_of_le ?_))
    · intro b hb b' hb' h1 h1'
      rw [hΘσ b (hBsq b hb) h1, hΘσ b' (hBsq b' hb') h1']
    · intro x hx
      exact ⟨hx.1, hΘ1 x (hBsq x hx.1) hx.2⟩
  have hGlt : Nat.card ↥(TwistedE6.fixedGroup K σ) < (2 ^ f) ^ 78 :=
    card_fixedGroup_lt hf hKf σ hσ
  have : Finite ↥(TwistedE6.fixedGroup K σ) := finite_fixedGroup σ
  have hLle : Nat.card ↥L ≤ Nat.card ↥(TwistedE6.fixedGroup K σ) :=
    Nat.card_le_card_of_surjective φ hφs
  have hLc : Nat.card ↥L = Nat.card (Subgroup.center ↥L) *
      Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [this, mul_comm]
    congr 1
    exact Nat.card_congr eS.toEquiv
  have hcc : IsCentralCover φ 2 :=
    isCentralCover_of_factor (isCentralCover_coverHom hf hKf σ hσ)
      (eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) φ hφs hφπ
  have hpow : (2 : ℕ) ^ (78 * f) = (2 ^ f) ^ 78 := by rw [mul_comm, pow_mul]
  have hext' : ∀ (a : MulAut W) (ha : a ∈ E), ∃ B : Module.End k (Fin m → k), IsUnit B ∧
      ∀ l : ↥L, B * ρ l = ρ (X1.conjAut L (hEN ha) l) * B := fun a ha => by
    obtain ⟨B, hB, h⟩ := hext a ha
    exact ⟨B, hB, h⟩
  have hfix' : ∀ A : Subgroup ↥L, Nat.card ↥(fixV (A.map L.subtype)) ≤
      2 ^ (δ * Module.finrank k (Representation.invariants (ρ.comp A.subtype))) :=
    fun A => hfix A
  have hHT : ∀ (g : ℕ), 1 ≤ g → g ∣ 2 * f →
      (∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
        χ (hatH hf hKf σ hσ a w) ^ (2 ^ g) = χ (hatH hf hKf σ hσ a w)) →
      (2 * f / g = 1 → 40 ≤ m ∨ Tw27Type hf K hKf σ hσ k χ J) ∧
      (2 * f / g = 2 → 78 ≤ m ∧ (79 ≤ m ∨ Tw78Type hf K hKf σ hσ k χ J)) ∧
      (3 ≤ 2 * f / g → 39 * (2 * f / g) + 1 ≤ m) := fun g hg1 hg2 hper =>
    hT f hf K hKf σ hσ k m (ρ.comp φ) y χ J g hρ' hntriv ht hg1 hg2 hper
  by_cases hout : ∃ (a : MulAut W) (ha : a ∈ E), psiAut L eS (hEN ha) ∉
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →* MulAut _).range
  · obtain ⟨a, ha, hnin⟩ := hout
    have hb2 : psiAut L eS (hEN ha) ^ 2 = 1 := by
      have h2 : (⟨a, ha⟩ : ↥E) ^ 2 = 1 := Subtype.ext (hel.2 a ha)
      have := congrArg (psiHom L eS hEN) h2
      rwa [map_pow, map_one] at this
    rcases hΘinv _ hb2 with hin | ⟨-, g, u, hα⟩
    · exact absurd hin hnin
    obtain ⟨B, hBu, hB⟩ := hext' a ha
    have hn2per := fun (a' : Fin TwistTag.E6.foldedTag.rank)
        (w : (orbitField TwistTag.E6 K σ a')ˣ) =>
      chi_pow_of_twist hf hKf σe hσ hodd eS φ hφπ (X1.conjAut L (hEN ha))
        (psiAut L eS (hEN ha)) (fun l => psiAut_mk eS (hEN ha) l) g u hα hρ' ht B hBu hB a' w
    have hg1 : 1 ≤ Nat.gcd δ f := Nat.gcd_pos_of_pos_left _ hδ
    have hper : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
        χ (hatH hf hKf σ hσ a w) ^ (2 ^ Nat.gcd δ f) = χ (hatH hf hKf σ hσ a w) :=
      fun a w => pow_two_pow_gcd _ δ f (hδper a w) (hn2per a w)
    have hgf2 : Nat.gcd δ f ∣ 2 * f := (Nat.gcd_dvd_right δ f).trans (dvd_mul_left f 2)
    obtain ⟨-, h2, h3⟩ := hHT _ hg1 hgf2 hper
    have hgδ : Nat.gcd δ f ∣ δ := Nat.gcd_dvd_left δ f
    obtain ⟨s, hs⟩ := Nat.gcd_dvd_right δ f
    generalize hgdef : Nat.gcd δ f = g' at hg1 hgδ hs h2 h3 hgf2
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0] at hs; omega
      · exact h0
    have hdiv : 2 * f / g' = 2 * s := by
      rw [hs]
      rw [show 2 * (g' * s) = g' * (2 * s) by ring]
      exact Nat.mul_div_cancel_left _ hg1
    rw [hdiv] at h2 h3
    have hgr : g' * (2 * s) = 2 * f := by rw [hs]; ring
    have hLW : ∀ n : ℕ, 78 * f + 1 ≤ n → 2 * (Nat.card (Subgroup.center ↥L) *
        Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ)) < 2 ^ n := by
      intro n hn
      rw [← hLc]
      have h1 : 2 * Nat.card ↥L < 2 ^ (78 * f + 1) := by
        calc 2 * Nat.card ↥L < 2 * (2 ^ f) ^ 78 := by
              have := hLle.trans_lt hGlt
              omega
          _ = 2 ^ (78 * f + 1) := by rw [pow_succ 2 (78 * f), hpow, mul_comm]
      exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) hn)
    have hOut' : ∀ B : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)),
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
          MulAut _).range) := hOut
    by_cases hwin : 78 * f + 1 ≤ δ * m
    · have hlt : 2 * (Nat.card (Subgroup.center ↥L) *
          Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ)) < Nat.card W := by
        rw [hWcard]; exact hLW _ hwin
      exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 2) hOut' hlt)
        hcon
    ·
      have hs2 : s = 1 := by
        by_contra hne
        apply hwin
        exact win_outer hgδ hδ hg1 hgr (by have := h3 (by omega); omega)
      subst hs2
      have hg'f : g' = f := by omega
      have h78m := h2 rfl
      have hm79 : ¬ 79 ≤ m := fun h79 => hwin (win_outer_79 (hg'f ▸ hgδ) hδ hf h79)
      have hTw78 : Tw78Type hf K hKf σ hσ k χ J := h78m.2.resolve_left hm79
      have hm78 : m = 78 := by have := h78m.1; omega
      have hfδ : f ∣ δ := hg'f ▸ hgδ
      have hfδ' : f ≤ δ := Nat.le_of_dvd hδ hfδ
      have hδf : δ = f := by
        by_contra hne
        apply hwin
        have : δ * m = δ * 78 := by rw [hm78]
        omega
      have hδm : δ * m = f * 78 := by rw [hδf, hm78]
      have hWc : Nat.card W = (2 ^ f) ^ 78 := by rw [hWcard, hδm, pow_mul]
      rcases Nat.even_or_odd f with hev | hodd'
      ·
        have hf2 : 2 ≤ f := by obtain ⟨j, hj⟩ := hev; omega
        have hEk := card_le_mul_card_inf_of_outer hW hql.1 hirr hEN hel eS hOut'
        by_cases h0 : E ⊓ L = ⊥
        · rw [h0, Subgroup.card_bot] at hEk
          obtain ⟨⟨a0, ha0⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
          have ha1' : a0 ≠ 1 := fun h => ha1 (Subtype.ext h)
          have hd := hdisp a0 ha0 ha1'
          have hfixle : Nat.card ↥(fixV E) ≤ Nat.card {w : W // a0 w = w} :=
            Nat.card_le_card_of_injective
              (fun w : ↥(fixV E) => (⟨w.1, w.2 a0 ha0⟩ : {w : W // a0 w = w}))
              (fun x y h => Subtype.ext (congrArg (fun z : {w : W // a0 w = w} => z.1) h))
          have hWpos : 0 < Nat.card W := Nat.card_pos
          have hP4 : 4 ≤ 2 ^ δ := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ δ := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h5 : Nat.card W ≤ 2 * Nat.card {w : W // a0 w = w} :=
            calc Nat.card W ≤ Nat.card E * Nat.card ↥(fixV E) := hoff
              _ ≤ 2 * 1 * Nat.card {w : W // a0 w = w} := Nat.mul_le_mul hEk hfixle
              _ = 2 * Nat.card {w : W // a0 w = w} := by ring
          have h6 : Nat.card W * 2 ^ δ ≤ 2 * Nat.card W :=
            calc Nat.card W * 2 ^ δ ≤ (2 * Nat.card {w : W // a0 w = w}) * 2 ^ δ :=
                  Nat.mul_le_mul_right _ h5
              _ = 2 * (Nat.card {w : W // a0 w = w} * 2 ^ δ) := by ring
              _ ≤ 2 * Nat.card W := Nat.mul_le_mul_left _ hd
          have h7 : Nat.card W * 4 ≤ Nat.card W * 2 ^ δ := Nat.mul_le_mul_left _ hP4
          omega
        · set A₀ : Subgroup ↥L := (E ⊓ L).subgroupOf L with hA₀
          have hA₀2 : ∀ x ∈ A₀, x ^ 2 = 1 := fun x hx =>
            Subtype.ext (by simpa using hel.2 _ hx.1)
          have hmap : A₀.map L.subtype = E ⊓ L :=
            Subgroup.map_subgroupOf_eq_of_le inf_le_right
          have hA₀c : Nat.card A₀ = Nat.card ↥(E ⊓ L) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
          obtain ⟨Â, hÂ2, hÂφ, hÂc, hÂne⟩ := exists_lift_elem hcc A₀ hA₀2
          have hA₀ne : A₀ ≠ ⊥ := by
            intro hbot
            apply h0
            rw [← hmap, hbot, Subgroup.map_bot]
          have hsb := h78 f hf K hKf σ hσ k m (ρ.comp φ) y χ J hρ' ht hTw78 Â (hÂne hA₀ne) hÂ2
          have hc1 := finrank_inv_le ρ φ A₀ Â hÂφ
          have hfE := hfix' A₀
          rw [hmap] at hfE
          have hfEL : Nat.card ↥(fixV E) ≤ Nat.card ↥(fixV (E ⊓ L)) :=
            Subgroup.card_le_of_le fun w hw y hy => hw y hy.1
          have hm2 : (2 ^ f) ^ m = (2 ^ f) ^ 78 := by rw [hm78]
          have hpc : 2 ^ (δ * Module.finrank k
              (Representation.invariants (ρ.comp A₀.subtype))) ≤
              (2 ^ f) ^ Module.finrank k
                (Representation.invariants ((ρ.comp φ).comp Â.subtype)) := by
            rw [hδf, ← pow_mul]
            exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hc1)
          have hfinal : (2 ^ f) ^ 78 ≤ 2 * Nat.card Â * (2 ^ f) ^ Module.finrank k
              (Representation.invariants ((ρ.comp φ).comp Â.subtype)) := by
            rw [← hWc]
            calc Nat.card W ≤ Nat.card E * Nat.card ↥(fixV E) := hoff
              _ ≤ (2 * Nat.card ↥(E ⊓ L)) * (2 ^ (δ * Module.finrank k
                    (Representation.invariants (ρ.comp A₀.subtype)))) :=
                  Nat.mul_le_mul hEk (hfEL.trans hfE)
              _ ≤ (2 * Nat.card Â) * (2 ^ f) ^ Module.finrank k
                    (Representation.invariants ((ρ.comp φ).comp Â.subtype)) :=
                  Nat.mul_le_mul (Nat.mul_le_mul_left _ (hA₀c ▸ hÂc)) hpc
          rw [hm2] at hsb
          omega
      ·
        have hcen := hc f hf K hKf σ hσ k m (ρ.comp φ) y χ J hρ' ht hTw78
        have hker : (coverHom hf hKf σ hσ).ker ≤ φ.ker := fun z hz =>
          MonoidHom.mem_ker.2 (hρinj ((hcen z (MonoidHom.mem_ker.1 hz)).trans (map_one ρ).symm))
        have h3d : 3 ∣ 2 ^ f + 1 := by
          obtain ⟨j, hj⟩ := hodd'
          have h4 : 4 ^ j % 3 = 1 := by rw [Nat.pow_mod]; norm_num
          have h5 : 2 ^ f = 2 * 4 ^ j := by
            rw [hj, pow_succ, pow_mul]; norm_num; ring
          omega
        have hk3 : 3 ≤ Nat.card φ.ker := by
          have h1 := Subgroup.card_le_of_le hker
          rw [card_ker_coverHom hf hKf σ hσ, Nat.gcd_eq_left h3d] at h1
          exact h1
        have hprod := Subgroup.card_ker_mul_card_of_surjective hφs
        have hlt : 2 * (Nat.card (Subgroup.center ↥L) *
            Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ)) < Nat.card W := by
          rw [← hLc, hWc]
          have : 3 * Nat.card ↥L ≤ Nat.card ↥(TwistedE6.fixedGroup K σ) := by
            rw [← hprod]
            exact Nat.mul_le_mul_right _ hk3
          have hLpos : 0 < Nat.card ↥L := Nat.card_pos
          omega
        exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 2) hOut' hlt)
          hcon
  · push Not at hout
    have hEL : E ≤ L := by
      intro a ha
      obtain ⟨s, hs⟩ := hout a ha
      refine mem_of_psiAut_inner hW hql.1 hirr hEN hel eS ha s fun x => ?_
      rw [← hs, MulAut.conj_apply]
    have hg1 : 1 ≤ Nat.gcd δ (2 * f) := Nat.gcd_pos_of_pos_left _ hδ
    have hper : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
        χ (hatH hf hKf σ hσ a w) ^ (2 ^ Nat.gcd δ (2 * f)) = χ (hatH hf hKf σ hσ a w) :=
      fun a w => pow_two_pow_gcd _ δ (2 * f) (hδper a w) (hnper a w)
    obtain ⟨h1, h2, h3⟩ := hHT _ hg1 (Nat.gcd_dvd_right _ _) hper
    have hgr : Nat.gcd δ (2 * f) * (2 * f / Nat.gcd δ (2 * f)) = 2 * f :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    generalize hgdef : Nat.gcd δ (2 * f) = g at hgr h1 h2 h3 hg1
    generalize hrdef : 2 * f / g = r at hgr h1 h2 h3
    have hgδ : g ∣ δ := hgdef ▸ Nat.gcd_dvd_left _ _
    have hr0 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0] at hgr; omega
      · exact h0
    by_cases hsurv : r = 1 ∧ m < 40
    · obtain ⟨hr1, hm40⟩ := hsurv
      have h27t : Tw27Type hf K hKf σ hσ k χ J := (h1 hr1).resolve_left (by omega)
      have hgf : g = 2 * f := by rw [hr1] at hgr; omega
      have h2fδ : 2 * f ∣ δ := hgf ▸ hgδ
      set A₀ : Subgroup ↥L := E.subgroupOf L with hA₀
      have hA₀2 : ∀ x ∈ A₀, x ^ 2 = 1 := fun x hx =>
        Subtype.ext (by simpa using hel.2 _ hx)
      have hmap : A₀.map L.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEL
      have hA₀c : Nat.card A₀ = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
      obtain ⟨Â, hÂ2, hÂφ, hÂc, hÂne⟩ := exists_lift_elem hcc A₀ hA₀2
      have hA₀ne : A₀ ≠ ⊥ := by
        intro hbot
        apply hE
        rw [← hmap, hbot, Subgroup.map_bot]
      have hsb := h27 f hf K hKf σ hσ k m (ρ.comp φ) y χ J hρ' hntriv ht h27t Â (hÂne hA₀ne) hÂ2
      have hc1 := finrank_inv_le ρ φ A₀ Â hÂφ
      have hc2 := finrank_inv_le_m ((ρ.comp φ).comp Â.subtype)
      have hfE := hfix' A₀
      rw [hmap] at hfE
      have hK2f : Nat.card K = 2 ^ (2 * f) := by rw [hKf, ← pow_mul, mul_comm]
      rw [hK2f] at hsb
      refine survivor_numerics (n := 2 * f) hδ h2fδ hc2 ?_ hsb
      rw [← hWcard]
      calc Nat.card W ≤ Nat.card E * Nat.card ↥(fixV E) := hoff
        _ ≤ Nat.card Â * 2 ^ (δ * Module.finrank k
              (Representation.invariants ((ρ.comp φ).comp Â.subtype))) := by
          refine Nat.mul_le_mul (hA₀c ▸ hÂc) (hfE.trans ?_)
          exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hc1)
    · have hmr : 39 * r ≤ m := by
        by_cases hr1 : r = 1
        · have : ¬ m < 40 := fun hm => hsurv ⟨hr1, hm⟩
          omega
        · by_cases hr2 : r = 2
          · have := (h2 hr2).1
            omega
          · have := h3 (by omega)
            omega
      have hwin := win_inner hgδ hδ hgr hmr
      have hlt : Nat.card ↥(L ⊔ E) < Nat.card W := by
        rw [sup_eq_left.2 hEL, hWcard]
        calc Nat.card ↥L ≤ Nat.card ↥(TwistedE6.fixedGroup K σ) := hLle
          _ < (2 ^ f) ^ 78 := hGlt
          _ = 2 ^ (78 * f) := hpow.symm
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) hwin
      exact absurd (card_mul_card_fixV_lt_of_card_sup_lt hW hql hirr hEN hE hel hlt) hcon

theorem coopersteinNoIrrFFTwistedE6_of_bounds
    (hT : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      TwTypeBoundStmt hf K hK σ hσ)
    (h27 : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw27SurvivorBound hf K hK σ hσ)
    (h78 : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw78HalfOffenderBound hf K hK σ hσ)
    (hc : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      Tw78CentreTrivial hf K hK σ hσ) :
    CoopersteinNoIrrFFTwistedE6 :=
  fun q hv hq => noIrrFFOffender_twistedE6_of_bounds hT h27 h78 hc q hv hq

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

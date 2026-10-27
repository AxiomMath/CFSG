module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux1
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G] [Finite G]

theorem glaPComponent_of_subnormal {p : ℕ} (hp : p.Prime) {S X D : Subgroup G}
    (hSX : IsSubnormal S X) (hD : GLAPComponent p S D) : GLAPComponent p X D := by
  obtain ⟨hDS, hsn, hcomp, hmin⟩ := hD
  have hSX' : S ≤ X := isSubnormal_le' hSX
  have hDX : D ≤ X := hDS.trans hSX'
  have hsnX : IsSubnormal D X := isSubnormal_trans' hsn hSX
  refine ⟨hDX, hsnX, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := X) p hsnX
    rwa [barX_self] at this
  · have e : ↥(barX p S D) ≃* ↥(barX p X D) :=
      (quotEquivBarX hp hDS hsn).symm.trans (quotEquivBarX hp hDX hsnX)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJD : J ≤ D := hJ.le
    have hJS : IsSubnormal J S := isSubnormal_of_le_of_le hJsn (hJD.trans hDS) hSX'
    have hcore : D ⊓ GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p S := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnX]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn
    refine hmin J hJ hJS ?_
    show barX p S J = barX p S D
    refine le_antisymm (barX_mono p hJD) ?_
    refine barX_le_of_forall (hJD.trans hDS) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := X) (le_of_eq heq.symm) hk (hDX hk)
    exact ⟨j, hj, hcore ⟨D.mul_mem (D.inv_mem (hJD hj)) hk, hjk⟩⟩


omit [Finite G] in
theorem gLBConj_centralizer_of_mem_normalizer {A : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    GLBConj n (Subgroup.centralizer (A : Set G)) = Subgroup.centralizer (A : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ y ∈ Subgroup.centralizer (A : Set G),
      g * y * g⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    intro g hg y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : g⁻¹ * a * g ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hy _ h1
    calc a * (g * y * g⁻¹) = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * a := by group
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := key n⁻¹ (inv_mem hn) _ h
    simpa [mul_assoc] using this
  · exact key n hn y

omit [Finite G] in
theorem subnormal_bot_or_top_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q] {A B : Subgroup Q}
    (h : IsSubnormal A B) (hB : B = ⊤) : A = ⊥ ∨ A = ⊤ :=
  by subst hB; exact h.eq_bot_or_top

omit [Finite G] in
theorem le_glaPPrimeCoreOf_of_normal {p : ℕ} (hp : p.Prime) {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) (hcop : ¬ p ∣ Nat.card H) : H ≤ GLAPPrimeCoreOf p M := by
  have hcop' : Nat.Coprime p (Nat.card (H.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hcop
  have hle : H.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hn, hcop'⟩
  calc H = (H.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hHM).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem three_dvd_card_of_glaPComponent {X D : Subgroup G} (hD : GLAPComponent 3 X D) :
    3 ∣ Nat.card D := by
  by_contra h3
  have hDD : D ≤ GLAPPrimeCoreOf 3 D := by
    refine le_glaPPrimeCoreOf_of_normal Nat.prime_three le_rfl ?_ h3
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hDX : D ≤ GLAPPrimeCoreOf 3 X :=
    hDD.trans (glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hD.2.1)
  have hbot : barX 3 X D = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem X.subtype_injective).1 (hDX ((Subgroup.mem_subgroupOf).1 hc))
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 X D) := hD.2.2.1.2.2
  rw [hbot] at hq
  have := hq.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) ⧸
    Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)))
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  apply hxy
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 a.2)
  have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 b.2)
  rw [ha, hb]

theorem exists_centralizing_normalizing {X D : Subgroup G} (hD : GLAPComponent 3 X D) :
    ∃ N : Subgroup G, N ≤ X ∧ (∀ D' : Subgroup G, GLAPComponent 3 X D' → D' ≠ D → D' ≤ N) ∧
      (∀ y ∈ N, ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ GLAPPrimeCoreOf 3 X) ∧
      (∀ y ∈ N, y ∈ Subgroup.normalizer (D : Set G)) := by
  set Z : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    Subgroup.centralizer ((barX 3 X D : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) with hZ
  refine ⟨(Z.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map X.subtype,
    Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro D' hD' hne
    have hbar : barX 3 X D' ≠ barX 3 X D := fun h => hne (glaPComponent_unique hD' hD h)
    have hcomm : ⁅barX 3 X D', barX 3 X D⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hD'.2.2.1 hD.2.2.1 hbar
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    intro y hy
    have hyX : y ∈ X := hD'.1 hy
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨y, hyX⟩ ∈ Z
    exact hcen ⟨⟨y, hyX⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
  · rintro y ⟨y', hy', rfl⟩ d hd
    have hdX : d ∈ X := hD.1 hd
    have h := Subgroup.mem_centralizer_iff.1 hy' _
      (⟨⟨d, hdX⟩, (Subgroup.mem_subgroupOf).2 hd, rfl⟩ :
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩ ∈ barX 3 X D)
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (y' * ⟨d, hdX⟩ * y'⁻¹ * ⟨d, hdX⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      have h' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩ *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩ := h
      calc QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩ *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y')⁻¹ *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩)⁻¹
          = (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' *
              QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩) *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨d, hdX⟩ *
              QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y')⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨_, h2, rfl⟩
  · rintro y ⟨y', hy', rfl⟩
    refine Lemma514Ns.mem_normalizer_of_barX_normalizer' hD y'.2 ?_
    exact Subgroup.centralizer_le_normalizer _ hy'

omit [Finite G] in
theorem mem_conj_of_isSCp {B : Subgroup G} (hB : IsSCp 3 ⊤ B) {m c : G}
    (hc : ∀ y ∈ GLBConj m B, y * c = c * y) (hc3 : c ^ 3 = 1) : c ∈ GLBConj m B := by
  rw [mem_gLBConj]
  refine Sec6C.mem_of_pow_eq_one_of_isSCp hB ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hy : m⁻¹ * b * m ∈ GLBConj m B := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hb
    have := hc _ hy
    calc b * (m * c * m⁻¹) = m * ((m⁻¹ * b * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * b * m)) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * b := by group
  · calc (m * c * m⁻¹) ^ 3 = m * c ^ 3 * m⁻¹ := by
          rw [conj_pow]
      _ = 1 := by rw [hc3]; group

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

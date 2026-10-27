module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcAutRank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice Polynomial
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Four

theorem exists_cube_of_mem {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    [Finite A] (hA : IsElemAbelian p A) (hcard : p ^ 3 ≤ Nat.card A) {y : G} (hy : y ∈ A) :
    ∃ E₀ : Subgroup G, E₀ ≤ A ∧ y ∈ E₀ ∧ Nat.card E₀ = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hk3 : 3 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hdvd : p ^ 3 ∣ Nat.card A := hk ▸ pow_dvd_pow p hk3
  have hH : Nat.card (Subgroup.zpowers y) ∣ p ^ 3 := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hA.2 y hy)).trans (dvd_pow_self p (by norm_num))
  obtain ⟨E₀, hE₀, hyE, hE₀A⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp hH hdvd ((Subgroup.zpowers_le).2 hy)
  exact ⟨E₀, hE₀A, hyE (Subgroup.mem_zpowers y), hE₀⟩

theorem natCast_eq_two_or_three_of_orderOf_four {q : ℕ} (he : orderOf ((q : ℕ) : ZMod 5) = 4) :
    ((q : ℕ) : ZMod 5) = 2 ∨ ((q : ℕ) : ZMod 5) = 3 := by
  have h1 := pow_orderOf_eq_one ((q : ℕ) : ZMod 5)
  rw [he] at h1
  have h2 : ((q : ℕ) : ZMod 5) ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [he] at this
    omega
  generalize ((q : ℕ) : ZMod 5) = x at h1 h2 ⊢
  revert x
  decide

theorem five_dvd_sq_add_one_of_orderOf_four {q : ℕ} (he : orderOf ((q : ℕ) : ZMod 5) = 4) :
    5 ∣ q * q + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rcases natCast_eq_two_or_three_of_orderOf_four he with h | h <;> rw [h] <;> decide

theorem charpoly_e8P4V :
    e8P4V.charpoly = cyclotomic 4 ℤ ^ 4 * 1 := by
  rw [e8P4V_eq, charpoly_of_basis e8P4VList e8P4BRows e8P4BinvRows [4, 4, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

section Cat

theorem card_le_adjointGroup_E8_five_four (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) {E : Subgroup (adjointGroup .E8 K)}
    (hE : IsElemAbelian 5 E) : Nat.card E ≤ 5 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases lt_or_ge (Nat.card E) (5 ^ 3) with hsmall | hbig
  · exact hsmall.le.trans (by norm_num)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set L := AlgebraicClosure K with hL
  have hq5 := natCast_eq_two_or_three_of_orderOf_four he
  have h5 := five_dvd_sq_add_one_of_orderOf_four he
  have hℓ5 : ¬ ringChar K ∣ 5 := by
    intro h
    have h1 : ringChar K = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 h
    have h2 : 5 ∣ Nat.card K := by
      rw [hK, h1]
      exact dvd_pow_self 5 f.pos.ne'
    have := (Nat.dvd_add_right (Dvd.dvd.mul_right h2 _)).1 h5
    exact absurd (Nat.dvd_one.1 this) (by norm_num)
  have hFr : ∀ c, iterateFrobenius L (ringChar K) f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def (ringChar K) f c
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) (ℓ := ringChar K) Nat.prime_five hℓ5
  obtain ⟨F, hFn⟩ := exists_frame_canonical K f.pos hK L
  obtain ⟨m, hm⟩ := exists_isLift F hFn hK
  have hT0 := card_twistedTorus F hK f.pos
  haveI : Finite (sylowGrp F m) := Nat.finite_of_card_ne_zero (by
    rw [card_sylowGrp hm, hT0]
    positivity)
  have hE5 : IsPGroup 5 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨c₁, hc₁⟩ := exists_conj_into_sylowRat hm hK f.pos h5 hE5
  let ψ₀ : adjointGroup .E8 K →* ModGL .E8 L :=
    (MulAut.conj F.g0⁻¹).toMonoidHom.comp
      ((adjEmb .E8 K L).comp (MulAut.conj c₁).toMonoidHom)
  have hψ₀ : ∀ x, ψ₀ x = F.g0⁻¹ * adjEmb .E8 K L (c₁ * x * c₁⁻¹) * F.g0 := fun x => by
    simp [ψ₀, MulAut.conj_apply]
  have hψ₀inj : Function.Injective ψ₀ :=
    (MulAut.conj F.g0⁻¹).injective.comp
      ((adjEmb_injective (τ := .E8) (K := K) (L := L)).comp (MulAut.conj c₁).injective)
  have hψ₀mem : ∀ x ∈ E, ψ₀ x ∈ sylowGrp F m := fun x hx => by
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hc₁ x hx))
    have : ψ₀ x = s := by
      rw [hψ₀, ← hsx]
      show F.g0⁻¹ * (F.g0 * s * F.g0⁻¹) * F.g0 = s
      group
    rw [this]
    exact hs
  let ψ : E →* sylowGrp F m :=
    (ψ₀.comp E.subtype).codRestrict (sylowGrp F m) (fun x => hψ₀mem x x.2)
  have hψinj : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (hψ₀inj (by
      have := congrArg Subtype.val hxy
      exact this))
  set R : Subgroup (sylowGrp F m) := ψ.range with hRdef
  have hRc : Nat.card R = Nat.card E :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (hE.1.is_comm.comm a b)
  have hRexp : ∀ x ∈ R, x ^ 5 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 5 = 1 := Subtype.ext (by simpa using hE.2 a a.2)
    rw [this, map_one]
  have hRab : IsElemAbelian 5 R :=
    ⟨⟨⟨fun a b => Subtype.ext (hRcomm _ a.2 _ b.2)⟩⟩, fun x hx => hRexp x hx⟩
  have hker : R ≤ (sylowRho hm).ker := by
    intro y hy
    obtain ⟨E₀, hE₀R, hyE₀, hE₀c⟩ :=
      exists_cube_of_mem Nat.prime_five hRab (by rw [hRc]; exact hbig) hy
    exact cube_le_ker (sylowRho hm) (card_sylowRho_range hm)
      (fun y hy => ncard_sylow_fixed_le hm hζ hFr hq5 y hy) E₀
      (fun x hx y hy => hRcomm x (hE₀R hx) y (hE₀R hy)) (fun x hx => hRexp x (hE₀R hx)) hE₀c hyE₀
  set T0 := twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L (ringChar K) f)))
    with hT0def
  have hcomm : IsMulCommutative T0 := by
    rw [hT0def, F.hT]
    exact isMulCommutative_map _ inferInstance
  have htors : Nat.card (torsionSubgroup T0 hcomm 5) = 5 ^ 4 := by
    have hv2 : e8P4V ^ 2 = -1 := by rw [sq]; exact e8P4V_sq
    have hv4 : e8P4V ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hv2]
      simp
    have hq5' : ¬ 5 ∣ Nat.card K := fun h => by
      have := (Nat.dvd_add_right (Dvd.dvd.mul_right h _)).1 h5
      exact absurd (Nat.dvd_one.1 this) (by norm_num)
    rw [natCard_torsion_eq _ T0 F.hT hcomm 5,
      natCard_fixedTorsion e8P4V (iterateFrobenius L (ringChar K) f) hℓ hFr Nat.prime_five
        (fun h => hℓ5 (h ▸ dvd_refl 5)),
      natCard_solutions_modMat Nat.prime_five e8P4V (n := 4) 1 hv4 (by norm_num) charpoly_e8P4V
        hq5' he (by simp)]
  have hRT : ∀ x ∈ R, ((x : sylowGrp F m) : ModGL .E8 L) ∈ torsionSubgroup T0 hcomm 5 := by
    intro x hx
    refine ⟨(sylowRho_eq_one_iff hm x).1 (MonoidHom.mem_ker.1 (hker hx)), ?_⟩
    have := congrArg Subtype.val (hRexp x hx)
    simpa using this
  haveI : Finite (torsionSubgroup T0 hcomm 5) :=
    Nat.finite_of_card_ne_zero (by rw [htors]; positivity)
  let ι : R → torsionSubgroup T0 hcomm 5 := fun x => ⟨_, hRT x x.2⟩
  have hι : Function.Injective ι := by
    intro x y h
    have h1 : ((ι x : torsionSubgroup T0 hcomm 5) : ModGL .E8 L) = (ι y : ModGL .E8 L) := by
      rw [h]
    exact Subtype.ext (Subtype.ext h1)
  calc Nat.card E = Nat.card R := hRc.symm
    _ ≤ Nat.card (torsionSubgroup T0 hcomm 5) := Nat.card_le_card_of_injective ι hι
    _ = 5 ^ 4 := htors

theorem card_le_cat_E8_five_four {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (he : orderOf ((Q.card : ℕ) : ZMod 5) = 4) {F : Subgroup (Cat ⟨.E8 Q, hv⟩)}
    (hF : IsElemAbelian 5 F) : Nat.card F ≤ 5 ^ 4 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 Q hv
  rw [← hK] at he
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact card_le_adjointGroup_E8_five_four K he (CFSG.SectionRank.isElemAbelian_map hF _)

theorem card_le_cat_E8_all {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    {F : Subgroup (Cat ⟨.E8 Q, hv⟩)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p))) := by
  by_cases h54 : p = 5 ∧ orderOf ((Q.card : ℕ) : ZMod p) = 4
  · obtain ⟨rfl, h4⟩ := h54
    rw [h4, show max 1 (degCount Tag.E8 4) = 4 by decide]
    exact card_le_cat_E8_five_four hv h4 hF
  · exact card_le_cat_E8 hv hp hpq he h54 hF

theorem pRank_mulAut_le_E8_all (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    {X : Type} [Group X] [Finite X] (eX : X ≃* Cat ⟨.E8 Q, hv⟩) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p))) +
        if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 Q hv
  obtain ⟨Θ, hΘ⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_ringAut_E
    (Or.inr (Or.inr rfl)) K hp hp5
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact pRank_mulAut_le_of_hom (eX.trans e) Θ hp hΘ
    (conj_injective_of_mulEquiv eX (conj_injective_cat_E8 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_E8_all hv hp hpq he hF)
    fun hf => CFSG.HardMathSupport.Timmesfeld.CrossChar.coprime_card_ringAut Q K hK hp hf

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end

module

public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.LocalAnalysis.GLTheoremB.Lemma91Proof
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_of_isElemAbelian' {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup h

omit [Finite G] in
theorem barX_mono (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

omit [Finite G] in
theorem alphaOf_le (p : ℕ) (M : Subgroup G) : alphaOf p M ≤ M :=
  sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (iSup₂_le fun _ hJ => hJ.2.1)

omit [Finite G] in
theorem gLBConj_inf (g : G) (X Y : Subgroup G) :
    GLBConj g (X ⊓ Y) = GLBConj g X ⊓ GLBConj g Y :=
  Subgroup.map_inf X Y _ (MulAut.conj g⁻¹).injective

theorem pCoreOf_alphaOf_inf_le (p : ℕ) {M : Subgroup G} {b : G} :
    pCoreOf 2 (alphaOf p M ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      pCoreOf 2 (M ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set A := alphaOf p M ⊓ C with hA
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans (inf_le_inf_right C (alphaOf_le p M))
  · intro g hg
    have h1 : GLBConj g (alphaOf p M) = alphaOf p M :=
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaOf p M hg.1)
    have h2 : GLBConj g C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)
    have h3 : GLBConj g A = A := by rw [hA, gLBConj_inf, h1, h2]
    rw [mem_normalizer_iff_gLBConj_eq, ← pCoreOf_gLBConj, h3]

theorem eq_bot_of_isSubnormal_of_coprime {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    (hcore : GLAPPrimeCore p Q = ⊥) {V : Subgroup Q} (hsn : IsSubnormal V ⊤)
    (hV : Nat.Coprime p (Nat.card V)) : V = ⊥ := by
  have hVle : V ≤ GLAPPrimeCoreOf p V := by
    have hle : (⊤ : Subgroup ↥V) ≤ GLAPPrimeCore p ↥V := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rwa [Subgroup.card_top]
    intro v hv
    exact ⟨⟨v, hv⟩, hle (Subgroup.mem_top _), rfl⟩
  have htop : GLAPPrimeCoreOf p (⊤ : Subgroup Q) = ⊥ := by
    have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q)
    rw [hcore] at h
    have h2 : GLAPPrimeCore p ↥(⊤ : Subgroup Q) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _
        (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).injective).1 h
    unfold GLAPPrimeCoreOf
    rw [h2, Subgroup.map_bot]
  exact eq_bot_iff.2 (hVle.trans ((glaPPrimeCoreOf_le_of_isSubnormal hp hsn).trans htop.le))

end General

section Setting

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem GLStanding.le_pRank' (hS : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B) :
    m ≤ CFSG.Open.pRank p B :=
  CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hB.1.1 (hS.card_eq hB)

omit [Finite G] in
theorem le_centralizer_of_mem {B : Subgroup G} (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B) :
    B ≤ Subgroup.centralizer ({b} : Set G) := fun _ hb' =>
  Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hb' hb)

omit [Finite G] in
theorem piStar_le_of_clause_a {B M D : Subgroup G} (hDB : D ≤ B)
    (ha : ∀ b ∈ B, b ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ⊔ piOf p b ≤ M) :
    piStar p D ≤ M :=
  iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => by
    rw [sup_comm]
    exact ha d (hDB hd) hd1

theorem pCoreOf_le_sigmaStar (h91 : Lemma91ii) (hS : GLStanding G m p) {B M D : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) (hDB : D ≤ B)
    (hD : IsPPlane p D) : pCoreOf 2 M ≤ sigmaStar D := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBM := le_of_isPreUniquenessTwoLocal hS hB hM
  have hOp : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have : Nontrivial D := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hD.2]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  refine (le_iSup_inf_centralizer_hyperplane hD.1
    ((hDB.trans hBM).trans (le_normalizer_pCoreOf 2 M)) hOp).trans (iSup₂_le fun K hK => ?_)
  have hKcard : Nat.card K = p ^ 1 := card_eq_of_index_eq hp hK.1 hK.2 (n := 1) hD.2
  obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one K with h | h
    · rw [h, Subgroup.card_bot, pow_one] at hKcard
      have := hp.one_lt
      omega
    · exact h
  have hle : pCoreOf 2 (Subgroup.centralizer ({k} : Set G)) ≤ sigmaStar D :=
    le_iSup_of_le k (le_iSup_of_le (hK.1 hkK) (le_iSup_of_le hk1 le_rfl))
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hkK) hy.2
  exact hle (pCoreOf_inf_centralizer_le h91 hS hB hM (hDB (hK.1 hkK)) hk1 ⟨hy.1, hyC⟩)

theorem sigmaStar_le_piStar (hS : GLStanding G m p) (D : Subgroup G) :
    sigmaStar D ≤ piStar p D :=
  iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 =>
    le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1
      ((pCoreOf_two_le_glaPPrimeCoreOf hS.prime hS.ne_two _).trans le_sup_right)))

theorem pCoreOf_le_gammaStar (h91 : Lemma91ii) (h94 : Lemma94) (hS : GLStanding G m p)
    {B M D : Subgroup G} (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M)
    (hDB : D ≤ B) (hD : IsPPlane p D) (hpi : piStar p D ≤ M) :
    pCoreOf 2 M ≤ gammaStar p D := by
  have hOpi : pCoreOf 2 M ≤ piStar p D :=
    (pCoreOf_le_sigmaStar h91 hS hB hM hDB hD).trans (sigmaStar_le_piStar hS D)
  refine le_inf (h94 G m p hS B M hB hM D hDB hD).1 ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOpi
    (hpi.trans (le_normalizer_pCoreOf 2 M)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem prop95Hyp_of (h91 : Lemma91ii) (h94 : Lemma94) (hS : GLStanding G m p) {B M D : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) (hDB : D ≤ B)
    (hD : IsPPlane p D) : Prop95Hyp p M D where
  twoLocal := hM.1.1
  le := hDB.trans (le_of_isPreUniquenessTwoLocal hS hB hM)
  plane := hD
  clause_a _ hd _ :=
    (pCoreOf_two_le_glaPPrimeCoreOf hS.prime hS.ne_two _).trans (lemma91_i hS hB hM (hDB hd))
  clause_b d hd hd1 :=
    (pCoreOf_alphaOf_inf_le p).trans (h91 G m p hS B M hB hM d (hDB hd) hd1)
  clause_c := (h94 G m p hS B M hB hM D hDB hD).1

theorem barX_gammaStar_eq_bot (h99 : Lemma99) (h95 : Prop95Core) (hS : GLStanding G m p)
    {B M D : Subgroup G} (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M)
    (hDB : D ≤ B) (hD : IsPPlane p D) (hhyp : Prop95Hyp p M D) (hpi : piStar p D ≤ M) :
    barX p M (gammaStar p D) = ⊥ := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, h2, h3⟩ := h95 G m p hS M D hhyp
  set U := pCoreOf 2 (piStar p D) with hU
  have hγM : gammaStar p D ≤ M :=
    inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hpi)
  have hUM : U ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hpi
  have hcore : GLAPPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hSγ : barX p M (gammaStar p D) ≤ barX p M (gammaD D) :=
    barX_mono p (gammaStar_le_gammaD p D)
  have hS2 : IsPGroup 2 (barX p M (gammaStar p D)) :=
    IsPGroup.map ((isPGroup_gammaStar p D).of_equiv (Subgroup.subgroupOfEquivOfLe hγM).symm)
      (QuotientGroup.mk' _)
  have hU2 : IsPGroup 2 (barX p M U) :=
    IsPGroup.map ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
      (Subgroup.subgroupOfEquivOfLe hUM).symm) (QuotientGroup.mk' _)
  refine eq_bot_of_centralizes_pCore_components hp hcore (coprime_card_of_isPGroup_two hp hp2 hS2)
    (hSγ.trans h2) ?_
  intro K hK
  obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq M hK
  by_contra hnc
  have hnc' : ¬ barX p M (gammaD D) ≤
      Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := fun h => hnc (hSγ.trans h)
  obtain ⟨D₀, Kd, hD₀, hKd, hgen⟩ := h99 G m p hS B M hB hM D hDB hD L hL hnc'
  have hKdle : ∀ d ∈ D₀, Kd d ≤ piStar p D := by
    intro d hd
    obtain ⟨hdD, hd1⟩ := hD₀ d hd
    exact (hKd d hd).2.2.2.trans (le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_rfl)))
  have hYpi : (⨆ d ∈ D₀, Kd d) ≤ piStar p D := iSup₂_le fun d hd => hKdle d hd
  have hLY : barX p M L ≤ barX p M (⨆ d ∈ D₀, Kd d) := by
    rw [hgen]
    exact iSup₂_le fun d hd => barX_mono p (le_iSup₂_of_le d hd le_rfl)
  have hLbN : barX p M L ≤ Subgroup.normalizer ((barX p M U : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    hLY.trans (barX_le_normalizer (hYpi.trans (le_normalizer_pCoreOf 2 _)))
  set V : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) := barX p M L ⊓ barX p M U with hV
  have hLbV : barX p M L ≤ Subgroup.normalizer (V : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) z
    have h2 := Subgroup.mem_normalizer_iff.1 (hLbN hl) z
    simp only [hV, Subgroup.mem_inf]
    rw [h1, h2]
  have hVnorm : (V.subgroupOf (barX p M L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLbV
  have hVsn : IsSubnormal V ⊤ := IsSubnormal.step inf_le_left hVnorm hK.2.1
  have hV2 : IsPGroup 2 V := hU2.to_le inf_le_right
  have hVbot : V = ⊥ :=
    eq_bot_of_isSubnormal_of_coprime hp hcore hVsn (coprime_card_of_isPGroup_two hp hp2 hV2)
  refine hnc fun s hs => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hsN : s ∈ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := h3 L hL (hSγ hs)
  have hc1 : s * l * s⁻¹ * l⁻¹ ∈ barX p M L :=
    (barX p M L).mul_mem ((Subgroup.mem_normalizer_iff.1 hsN l).1 hl) ((barX p M L).inv_mem hl)
  have hc2 : s * l * s⁻¹ * l⁻¹ ∈ barX p M U := by
    obtain ⟨γ, hγ, rfl⟩ := hs
    obtain ⟨y, hy, rfl⟩ := hLY hl
    have hγ' : (γ : G) ∈ gammaStar p D := (Subgroup.mem_subgroupOf).1 hγ
    have hy' : (y : G) ∈ ⨆ d ∈ D₀, Kd d := (Subgroup.mem_subgroupOf).1 hy
    have hγU : (γ : G) ∈ U := hγ'.2
    have hyN : (y : G) ∈ Subgroup.normalizer (U : Set G) :=
      le_normalizer_pCoreOf 2 _ (hYpi hy')
    have h4 : (y : G) * γ⁻¹ * (y : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 hyN _).1 (U.inv_mem hγU)
    refine ⟨γ * y * γ⁻¹ * y⁻¹, (Subgroup.mem_subgroupOf).2 ?_, by simp⟩
    have := U.mul_mem hγU h4
    simpa [mul_assoc] using this
  have hmem : s * l * s⁻¹ * l⁻¹ ∈ V := ⟨hc1, hc2⟩
  rw [hVbot, Subgroup.mem_bot] at hmem
  have h5 : s * l * s⁻¹ = l := mul_inv_eq_one.1 hmem
  exact (mul_inv_eq_iff_eq_mul.1 h5).symm

theorem lemma910_of (h91 : Lemma91ii) (h94 : Lemma94) (h95 : Prop95Core) (h99 : Lemma99)
    (iPi : InputPiGen) :
    ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
      ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
        (∀ b ∈ B, b ≠ 1 →
          GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ⊔ piOf p b ≤ M) ∧
          ∀ D : Subgroup G, D ≤ B → IsPPlane p D → gammaStar p D = pCoreOf 2 M := by
  intro G _ _ m p hS B M hB hM
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1.1
  have hm4 := hS.four_le
  have hmB := hS.le_pRank' hB
  have hi : ∀ b ∈ B, b ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ⊔ piOf p b ≤ M := by
    intro b hb hb1
    refine sup_le (lemma91_i hS hB hM hb) ?_
    unfold piOf piLayer
    refine iSup_le fun L => iSup_le fun hL => ?_
    set C := Subgroup.centralizer ({b} : Set G) with hC
    have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
    have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    have hrank : GLATwoLocalRank p (↥C ⧸ GLAPPrimeCore p ↥C) ≤
        CFSG.Open.pRank p (barX p C B) := by
      refine (glaTwoLocalRank_quotient_le hp hp2 _ hN).trans
        ((glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_)
      rw [hS.rank_eq, rank_barX_of_isPGroup hp hBp hBC]
      exact hmB
    have hK : IsComponentOf (barX p C L) ⊤ := hL.1.2.2.1
    have hpi := isPiGroup_barX hp hL.1.1 hL.1.2.1 hL.2
    have hgen := iPi (↥C ⧸ GLAPPrimeCore p ↥C) p hp hp2 (barX p C L) hK hpi (barX p C B)
      (isElemAbelian_barX hB.1.1) hrank
    have hk3 : 3 ≤ CFSG.Open.pRank p (barX p C B) - 1 := by
      rw [rank_barX_of_isPGroup hp hBp hBC]
      omega
    refine le_of_barX_le_glbCore hp _ hBp hBC hL.1.1 ?_ (lemma91_i hS hB hM hb) hgen
    intro E hE hkE
    exact (le_sSup ⟨E, hE, hk3.trans hkE, rfl⟩ : Subgroup.normalizer (E : Set G) ≤
      GLBCore p 3 B).trans hM.2.2
  refine ⟨hi, fun D hDB hD => ?_⟩
  have hpi : piStar p D ≤ M := piStar_le_of_clause_a hDB hi
  have hhyp := prop95Hyp_of h91 h94 hS hB hM hDB hD
  have hbot := barX_gammaStar_eq_bot h99 h95 hS hB hM hDB hD hhyp hpi
  refine le_antisymm ?_ (pCoreOf_le_gammaStar h91 h94 hS hB hM hDB hD hpi)
  intro x hx
  have hxM : x ∈ M :=
    (inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hpi)) hx
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ barX p M (gammaStar p D) :=
    ⟨⟨x, hxM⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  have hx1 : x ∈ GLAPPrimeCoreOf p M := ⟨_, hmem, rfl⟩
  have := (h95 G m p hS M D hhyp).1
  rw [← this]
  exact ⟨gammaStar_le_gammaD p D hx, hx1⟩

theorem prop98_of_lemma99_lemma911 (h91 : Lemma91ii) (h94 : Lemma94) (h95 : Prop95Core)
    (h99 : Lemma99) (h911 : Lemma911) (i22 : Input22_5) (iPi : InputPiGen) : Prop98 := by
  intro G _ _ m p hS B M hB hM
  have h910 := lemma910_of h91 h94 h95 h99 iPi G m p hS B M hB hM
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hBM := le_of_isPreUniquenessTwoLocal hS hB hM
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1.1
  have hm4 := hS.four_le
  have hmB := hS.le_pRank' hB
  have hd : GLBCore p 2 B ≤ M := by
    refine sSup_le ?_
    rintro _ ⟨Q, hQB, hQ2, rfl⟩ g hg
    obtain ⟨E, hEQ, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Q
    obtain ⟨D, hDE, hDel, hDcard⟩ := exists_le_isElemAbelian_card hEel (n := 2)
      (by rw [hEcard]; exact pow_dvd_pow p hQ2)
    have hD : IsPPlane p D := ⟨hDel, hDcard⟩
    have hDB : D ≤ B := hDE.trans (hEQ.trans hQB)
    have hDg : GLBConj g D ≤ B :=
      (gLBConj_mono g (hDE.trans hEQ)).trans ((gLBConj_eq_of_mem_normalizer hg).le.trans hQB)
    have h1 := h910.2 _ hDg (isPPlane_gLBConj g hD)
    have h2 := h910.2 D hDB hD
    rw [gammaStar_gLBConj, h2] at h1
    have h3 : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := mem_normalizer_iff_gLBConj_eq.2 h1
    rwa [normalizer_pCoreOf_eq_of_isMaxTwoLocal hM.1] at h3
  have he : p = 3 → ∀ a ∈ B, a ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) L →
        (IsLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L) ∨ IsSLThreeFour (↥L ⧸ GLAPPrimeCore 3 ↥L)) →
          L ≤ M := by
    rintro rfl a ha ha1 L hL hty
    set C := Subgroup.centralizer ({a} : Set G) with hC
    have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 ha
    have hK : IsComponentOf (barX 3 C L) ⊤ := hL.2.2.1
    have hty' : IsLThreeFour ↥(barX 3 C L) ∨ IsSLThreeFour ↥(barX 3 C L) := by
      let e := quotEquivBarX hp hL.1 hL.2.1
      rcases hty with ⟨F, _, _, hcard, ⟨f⟩⟩ | ⟨F, _, _, hcard, ⟨f⟩⟩
      · exact Or.inl ⟨F, inferInstance, inferInstance, hcard, ⟨e.symm.trans f⟩⟩
      · exact Or.inr ⟨F, inferInstance, inferInstance, hcard, ⟨e.symm.trans f⟩⟩
    have hperf : commutator ↥(barX 3 C L) = ⊤ := hK.2.2.1
    have hm2 := pRank_mulAut_le_two_of_L34 hty' hperf
    have hrB : CFSG.Open.pRank 3 (barX 3 C B) = CFSG.Open.pRank 3 B :=
      rank_barX_of_isPGroup hp hBp hBC
    have hgen := i22 (↥C ⧸ GLAPPrimeCore 3 ↥C) 3 hp (glaPPrimeCore_quotient_eq_bot hp)
      (barX 3 C L) hK (barX 3 C B) (isElemAbelian_barX hB.1.1) (by omega) 2 (by norm_num)
      (by omega)
    refine le_of_barX_le_glbCore hp 2 hBp hBC hL.1 ?_ (lemma91_i hS hB hM ha) hgen
    intro E hE hkE
    exact (le_sSup ⟨E, hE, hkE, rfl⟩ : Subgroup.normalizer (E : Set G) ≤ GLBCore 3 2 B).trans hd
  refine ⟨⟨hM.1, hBM, hB.1.1, by omega, h910.1, ?_, ?_, hd, he, h911 G m p hS B M hB hM⟩, h910.2⟩
  · intro a ha ha1
    exact (pCoreOf_alphaOf_inf_le p).trans (h91 G m p hS B M hB hM a ha ha1)
  · intro D hDB hD
    have h2 := h910.2 D hDB hD
    refine ⟨h2.ge, fun T hT1 hT2 => ?_⟩
    rw [h2] at hT2
    rw [le_antisymm hT2 hT1]
    exact (normalizer_pCoreOf_eq_of_isMaxTwoLocal hM.1).le

theorem prop98_of_inputs (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23)
    (i19 : Input19Delta) (i19' : Input19_1_6) (h95 : Prop95Core) (h99 : Lemma99)
    (h911 : Lemma911) (i22 : Input22_5) (iPi : InputPiGen) : Prop98 :=
  prop98_of_lemma99_lemma911 (lemma91ii_of_inputs i20 i11 l23)
    (lemma94_of_lemma91ii_lemma92 (lemma91ii_of_inputs i20 i11 l23)
      (lemma92_of_inputs (lemma91ii_of_inputs i20 i11 l23) i19 i19')) h95 h99 h911 i22 iPi

end Setting

end CFSG.LocalAnalysis.GLTheoremB

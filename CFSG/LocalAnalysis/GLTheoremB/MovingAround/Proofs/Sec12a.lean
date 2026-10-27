module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec11Small

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

namespace Sec12a

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}

theorem le_alphaOf_two (M : Subgroup G) : CFSG.Open.pCoreOf 2 M ≤ alphaOf p M := by
  unfold alphaOf
  exact le_sup_left

theorem alphaOf_le_self (M : Subgroup G) : alphaOf p M ≤ M := by
  unfold alphaOf
  refine sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 M) ?_
  exact iSup₂_le fun J hJ => hJ.2.1

theorem tof_le_cg (M : Subgroup G) (a : G) : Tof p M a ≤ Cg a :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

theorem tof_le_alphaOf (M : Subgroup G) (a : G) : Tof p M a ≤ alphaOf p M :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left

theorem le_pCoreOf_two_of_le_normalizer {N K : Subgroup G} (hNK : N ≤ K)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup 2 N) : N ≤ CFSG.Open.pCoreOf 2 K :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hK hN

theorem mem_normalizer_inf {A B : Subgroup G} {k : G}
    (hA : k ∈ Subgroup.normalizer (A : Set G)) (hB : k ∈ Subgroup.normalizer (B : Set G)) :
    k ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  exact and_congr (Subgroup.mem_normalizer_iff.1 hA x) (Subgroup.mem_normalizer_iff.1 hB x)

theorem cg2_eq_inf (e a : G) : Cg2 e a = Cg a ⊓ Cg e := by
  ext g
  simp only [Cg2, Cg, Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inr hx), fun x hx => h x (Or.inl hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases hx with rfl | rfl
    · exact h2 x rfl
    · exact h1 x rfl

theorem pCoreOf_two_inf_le_alpha_inf (M : Subgroup G) (e : G) :
    CFSG.Open.pCoreOf 2 M ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (alphaOf p M ⊓ Cg e) := by
  refine le_pCoreOf_two_of_le_normalizer ?_ ?_ ?_
  · exact inf_le_inf_right _ (le_alphaOf_two M)
  · intro k hk
    have hkM : k ∈ M := alphaOf_le_self M (hk.1 : k ∈ alphaOf p M)
    exact mem_normalizer_inf
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hkM) (Subgroup.le_normalizer hk.2)
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left

end Sec12a

theorem lemma122_ii_of_cex {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
    {a : G} (h : Cex121 G m p B M E A a) : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := by
  rintro ⟨A1, hA1, haA1⟩
  have hU : IsUniquenessTwoLocal p A1 M := hA1.2
  apply h.fails
  exact hU.clause_b a haA1 h.ha.2

namespace Sec12a

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}

theorem lemma122_i_of_le (hpair : IsDDpStar p M E A) (hT : Tof p M a ≤ CFSG.Open.pCoreOf 2 M)
    {e : G} (he : e ∈ E ⊓ A) (he1 : e ≠ 1) :
    Tof p M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg2 e a) := by
  have hE : IsUniquenessTwoLocal p E M := hpair.1.1.2
  have hb : CFSG.Open.pCoreOf 2 (alphaOf p M ⊓ Cg e) ≤ CFSG.Open.pCoreOf 2 (Cg e) :=
    hE.clause_b e (Subgroup.mem_inf.1 he).1 he1
  have hN : Tof p M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊓ Cg a := by
    intro x hx
    obtain ⟨hxT, hxe⟩ := hx
    exact ⟨hb (pCoreOf_two_inf_le_alpha_inf M e ⟨hT hxT, hxe⟩), tof_le_cg M a hxT⟩
  rw [cg2_eq_inf]
  refine hN.trans ?_
  refine le_pCoreOf_two_of_le_normalizer ?_ ?_ ?_
  · exact fun x hx => ⟨hx.2, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx.1⟩
  · intro k hk
    exact mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Cg e) hk.2)
      (Subgroup.le_normalizer hk.1)
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Cg e)).to_le inf_le_left

theorem lemma122_iii_of_le (hT : Tof p M a ≤ CFSG.Open.pCoreOf 2 M) {F : Subgroup G} :
    ∃ V : G → Subgroup G,
      (∀ x ∈ F, x ≠ 1 → V x ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G)) ∧
      Tof p M a ⊓ Subgroup.centralizer (A : Set G) =
        (Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ CFSG.Open.pCoreOf 2 M) ⊔
          ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), V x ∧
      ∀ x ∈ F, x ≠ 1 →
        V x ≤ derivedInf (⨆ g ∈ (alphaOf p M ⊓ Cg x), GLBConj g (V x)) := by
  refine ⟨fun _ => ⊥, fun _ _ _ => bot_le, ?_, fun _ _ _ => bot_le⟩
  have hTA : Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ CFSG.Open.pCoreOf 2 M =
      Tof p M a ⊓ Subgroup.centralizer (A : Set G) :=
    inf_eq_left.2 (inf_le_left.trans hT)
  simp [hTA]

@[expose] def CaseB122i : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a), ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M →
      ∀ e ∈ E ⊓ A, e ≠ 1 → Tof p M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg2 e a)

@[expose] def CaseB122iii : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {F : Subgroup G} (_hF : IsEkIn p 2 A F),
    ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M →
    ∃ V : G → Subgroup G,
      (∀ x ∈ F, x ≠ 1 → V x ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G)) ∧
      Tof p M a ⊓ Subgroup.centralizer (A : Set G) =
        (Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ CFSG.Open.pCoreOf 2 M) ⊔
          ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), V x ∧
      ∀ x ∈ F, x ≠ 1 →
        V x ≤ derivedInf (⨆ g ∈ (alphaOf p M ⊓ Cg x), GLBConj g (V x))

theorem caseB_p3_hatSeven (hT : ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M) :
    p = 3 ∧ ∃ J : Subgroup G, J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧
      IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J) ∧ ¬ J ≤ CFSG.Open.pCoreOf 2 M := by
  have hα : ¬ alphaOf p M ≤ CFSG.Open.pCoreOf 2 M := fun h => hT ((tof_le_alphaOf M a).trans h)
  unfold alphaOf at hα
  refine ⟨?_, ?_⟩
  · by_contra hp3
    apply hα
    exact sup_le le_rfl (iSup₂_le fun J hJ => absurd hJ.1 hp3)
  · by_contra hcon
    apply hα
    refine sup_le le_rfl (iSup₂_le fun J hJ => ?_)
    by_contra hJn
    exact hcon ⟨J, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1, hJ.2.2.2.2, hJn⟩

@[expose] def Input18_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → CFSG.Open.IsKProper G →
    ∀ (X : Subgroup G) (d : G), X ≠ ⊤ → d ∈ X → d ^ p = 1 →
      Lstar p (X ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Lstar p X

theorem pCoreOf_two_le_lstar [Fact p.Prime] (hp2 : p ≠ 2) (X : Subgroup G) :
    CFSG.Open.pCoreOf 2 X ≤ Lstar p X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans ?_ (le_sup_left.trans le_sup_left)
  refine sec11_le_glaPPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) ?_ ?_
  · intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hh) n).1 hn
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2)

theorem tof_le_lstar_of_inputs (h : Cex121 G m p B M E A a) (hp : p.Prime) (hp2 : p ≠ 2)
    (h122i : ∀ e ∈ E ⊓ A, e ≠ 1 → Tof p M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg2 e a))
    (hI : Input18_5) : Tof p M a ≤ Lstar p (Cg a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEM, hEel, -⟩ : IsSCp p M E := h.pair.1.1.1.1
  obtain ⟨hAM, hAel, -⟩ : IsSCp p M A := h.pair.1.2.1.1.1
  have hrank : 2 ≤ CFSG.Open.pRank p (E ⊓ A : Subgroup G) := h.pair.1.2.2
  have hA₀el : CFSG.Open.IsElemAbelian p (E ⊓ A : Subgroup G) :=
    CFSG.Open.IsElemAbelian.mono hAel inf_le_right
  haveI : CFSG.IsElementaryAbelian p ↥(E ⊓ A : Subgroup G) :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA₀el
  have hcardA₀ : p ^ 2 ≤ Nat.card ↥(E ⊓ A : Subgroup G) := by
    obtain ⟨F, hFA₀, -, hFcard⟩ :=
      CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt (E ⊓ A : Subgroup G)
    have h1 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (E ⊓ A : Subgroup G) :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hrank
    exact (h1.trans (hFcard ▸ le_rfl)).trans (Subgroup.card_le_of_le hFA₀)
  have hA₀α : E ⊓ A ≤ Subgroup.normalizer ((alphaOf p M ⊓ Cg a : Subgroup G) : Set G) := by
    intro k hk
    have hkM : k ∈ M := hEM (Subgroup.mem_inf.1 hk).1
    have hkCa : k ∈ Cg a := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (CFSG.Open.IsElemAbelian.comm hAel (Subgroup.mem_inf.1 hk).2 h.ha.1).symm
    exact mem_normalizer_inf (le_normalizer_alphaOf p M hkM) (Subgroup.le_normalizer hkCa)
  have hA₀T : E ⊓ A ≤ Subgroup.normalizer ((Tof p M a : Subgroup G) : Set G) :=
    hA₀α.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (alphaOf p M ⊓ Cg a))
  let α : ↥(E ⊓ A : Subgroup G) →* MulAut ↥(Tof p M a) :=
    (Tof p M a).normalizerMonoidHom.comp (Subgroup.inclusion hA₀T)
  have hα : ∀ (k : ↥(E ⊓ A : Subgroup G)) (x : ↥(Tof p M a)),
      ((α k x : ↥(Tof p M a)) : G) = (k : G) * x * (k : G)⁻¹ :=
    fun k x => Subgroup.normalizerMonoidHom_apply_apply_coe (Tof p M a) (Subgroup.inclusion hA₀T k) x
  letI : MulDistribMulAction ↥(E ⊓ A : Subgroup G) ↥(Tof p M a) :=
    MulDistribMulAction.compHom (Tof p M a) α
  have hsmul : ∀ (k : ↥(E ⊓ A : Subgroup G)) (x : ↥(Tof p M a)), k • x = α k x := fun _ _ => rfl
  have hT2 : IsPGroup 2 ↥(Tof p M a) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (alphaOf p M ⊓ Cg a)
  have hndvd : ¬ p ∣ Nat.card ↥(Tof p M a) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
    intro hdvd
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p)
    (A := ↥(E ⊓ A : Subgroup G)) (H := ↥(Tof p M a)) hcardA₀ hndvd
  have hcommA : ∀ k ∈ E ⊓ A, k ∈ Cg a := fun k hk => by
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    exact (CFSG.Open.IsElemAbelian.comm hAel (Subgroup.mem_inf.1 hk).2 h.ha.1).symm
  have hCa : Cg a ≠ ⊤ := by
    intro htop
    have hcen : Subgroup.center G = ⊥ := by
      haveI : IsSimpleGroup G := h.standing.simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨x, y, hxy⟩ := h.standing.nonabelian
        have hx : x ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top x
        exact hxy (((Subgroup.mem_center_iff.1 hx) y).symm)
    have ha : a ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
      have hg : g ∈ Cg a := by rw [htop]; exact Subgroup.mem_top g
      exact ((Subgroup.mem_centralizer_iff.1 hg) a (Set.mem_singleton a)).symm
    rw [hcen, Subgroup.mem_bot] at ha
    exact h.ha.2 ha
  have hkey : ∀ k : ↥(E ⊓ A : Subgroup G), k ≠ 1 →
      CFSG.fixedPointSubgroup (Subgroup.zpowers k) ↥(Tof p M a) ≤
        (Lstar p (Cg a)).comap (Tof p M a).subtype := by
    intro k hk x hx
    have hkx : k • x = x := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff k x).1 hx
    have h1 : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
      have h1' : ((k • x : ↥(Tof p M a)) : G) = (x : G) := congrArg Subtype.val hkx
      rw [hsmul, hα] at h1'
      exact h1'
    have hxC : (x : G) ∈ Cg (k : G) := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      calc (k : G) * (x : G) = (k : G) * (x : G) * (k : G)⁻¹ * (k : G) := by group
        _ = (x : G) * (k : G) := by rw [h1]
    have hmem : (x : G) ∈ Tof p M a ⊓ Cg (k : G) := ⟨x.2, hxC⟩
    have hk1 : (k : G) ≠ 1 := fun e => hk (Subtype.ext e)
    have h2 : (x : G) ∈ CFSG.Open.pCoreOf 2 (Cg2 (k : G) a) :=
      h122i (k : G) (Subtype.property k) hk1 hmem
    have hLe : CFSG.Open.pCoreOf 2 (Cg2 (k : G) a) ≤ Lstar p (Cg a) := by
      refine (pCoreOf_two_le_lstar hp2 (Cg2 (k : G) a)).trans ?_
      rw [cg2_eq_inf]
      exact hI G p hp h.standing.kProper (Cg a) (k : G) hCa (hcommA _ (Subtype.property k))
        (hAel.2 (k : G) (Subgroup.mem_inf.1 (Subtype.property k)).2)
    exact hLe h2
  have hall : (⊤ : Subgroup ↥(Tof p M a)) ≤ (Lstar p (Cg a)).comap (Tof p M a).subtype := by
    rw [← hgen]
    exact iSup₂_le fun k hk => hkey k hk
  intro x hx
  exact hall (Subgroup.mem_top (⟨x, hx⟩ : ↥(Tof p M a)))

end Sec12a

theorem lemma122_i_ii_of_caseB (hB : Sec12a.CaseB122i) : Lemma122_i_iiStatement := by
  unfold Lemma122_i_iiStatement
  intro G _ _ m p B M E A a h
  refine ⟨fun e he he1 => ?_, lemma122_ii_of_cex h⟩
  by_cases hT : Tof p M a ≤ CFSG.Open.pCoreOf 2 M
  · exact Sec12a.lemma122_i_of_le h.pair hT he he1
  · exact hB h hT e he he1

theorem lemma122_iii_of_caseB (hB : Sec12a.CaseB122iii) : Lemma122_iiiStatement := by
  unfold Lemma122_iiiStatement
  intro G _ _ m p B M E A a h F hF
  by_cases hT : Tof p M a ≤ CFSG.Open.pCoreOf 2 M
  · exact Sec12a.lemma122_iii_of_le hT
  · exact hB h hF hT

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

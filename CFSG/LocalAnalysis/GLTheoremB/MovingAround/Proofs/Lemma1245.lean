module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma124
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop121
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped Pointwise commutatorElement

namespace Lemma1245

section Notation

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev FF (A K : Subgroup G) : Subgroup G := centBar 3 A K

noncomputable abbrev JJ (A K : Subgroup G) : Subgroup G :=
  GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))

noncomputable abbrev WW (M A K : Subgroup G) : Subgroup G :=
  ⨆ (x : G) (_ : x ∈ centBar 3 A K) (_ : x ≠ 1), M ⊓ Cg x

end Notation

@[expose] def NormClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hA4 : CFSG.Open.pRank 3 A = 4) {x : G} (_hx : x ∈ centBar 3 A K) (_hx1 : x ≠ 1)
    {I : Subgroup G} (_hI : GLAPComponent 3 (Cg x) I)
    (_hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)))
    (_hIN : E ⊓ A ≤ Subgroup.normalizer (I : Set G))
    (_hIinn : ∀ b ∈ E ⊓ A, InducesInner 3 I b)
    (_hIf : ∀ b ∈ E ⊓ A, b ∈ centBar 3 ⊤ I → b = 1),
    A ≤ Subgroup.normalizer (I : Set G) ∨ I ≤ M

@[expose] def KxClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hu₀ : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hAN : A ≤ Subgroup.normalizer (K : Set G)),
    ∀ x ∈ FF A K, x ≠ 1 →
      GLAPComponent 3 (Cg x) (Kx 3 (JJ A K) x) ∧ barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤

@[expose] def TypeClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hAN : A ≤ Subgroup.normalizer (K : Set G))
    (_hKx : ∀ x ∈ FF A K, x ≠ 1 →
      GLAPComponent 3 (Cg x) (Kx 3 (JJ A K) x) ∧ barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤),
    Subgroup.center (barOf 3 K) = ⊥

@[expose] def UniqClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hAN : A ≤ Subgroup.normalizer (K : Set G)) (_hKt : Subgroup.center (barOf 3 K) = ⊥)
    (_hcov : barX 3 K (JJ A K) = ⊤) {x : G} (_hx : x ∈ FF A K) (_hx1 : x ≠ 1)
    (_hKx : GLAPComponent 3 (Cg x) (Kx 3 (JJ A K) x))
    (_hJcov : barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤)
    {I : Subgroup G} (_hI : GLAPComponent 3 (Cg x) I)
    (_hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)))
    (_hIc : Subgroup.center (barOf 3 I) = ⊥),
    I = Kx 3 (JJ A K) x

@[expose] def VxClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hAN : A ≤ Subgroup.normalizer (K : Set G)) (_hcov : barX 3 K (JJ A K) = ⊤)
    {x : G} (_hx : x ∈ FF A K) (_hx1 : x ≠ 1) {V : Subgroup G},
    V ≤ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G) →
    V ≤ derivedInf (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V) →
    V ≤ centBar 3 ⊤ (JJ A K)

@[expose] def SClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hu₀ : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hdec : A = (A ⊓ JJ A K) ⊔ FF A K) (_hF2 : CFSG.Open.pRank 3 (FF A K) = 2),
    pCoreOf 2 (M ⊓ (JJ A K ⊔ WW M A K)) ≤ GLAPPrimeCoreOf 3 M

@[expose] def JstarClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G}
    (_h : Cex121 G m 3 B M E A a) {K : Subgroup G} (_hK : GLAPComponent 3 (Cg a) K)
    (_hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (_hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (_hu₀ : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (_hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (_hII : ∀ x ∈ FF A K, x ≠ 1 → Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G) ∧
      barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤)
    (_hJt : IsLThreeFour (barOf 3 (JJ A K)))
    (_hIV : ∃ u ∈ pCoreOf 2 M ⊓ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (JJ A K : Set G), IsUnitaryAut (barAut 3 (JJ A K) ⟨u, hu⟩))
    (_hF2 : CFSG.Open.pRank 3 (FF A K) = 2)
    (_hO3 : GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) ≤ M),
    ∃ Js : Subgroup G, GLAPComponent 3 (JJ A K ⊔ WW M A K) Js ∧ JJ A K ≤ Js ∧
      IsLThreeFour (barOf 3 Js) ∧ GLAPPrimeCoreOf 3 Js ≤ pCoreOf 2 Js

section Rank

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_four_of_inputs (h123 : Lemma123Statement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement)
    {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) :
    CFSG.Open.pRank 3 A ≤ 4 := by
  have hk : CFSG.Open.pRank 3 (E ⊓ A) = 2 := Lemma124.pRank_inter_eq_two_of_inputs h123 h
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hlt
  push Not at hlt
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hcardA : Nat.card A = 3 ^ CFSG.Open.pRank 3 A := Lemma124.card_eq_pow_pRank hAel
  obtain ⟨R, hR, hAR⟩ :=
    Lemma124.exists_isSylowIn_above_aux hAM (Lemma124.isPGroup_three_of_isElemAbelian hAel)
  obtain ⟨H5, hH5⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 3 (n := 5)
    (by rw [hcardA]; exact pow_dvd_pow 3 hlt)
  set E5 : Subgroup G := H5.map A.subtype with hE5def
  have hE5A : E5 ≤ A := Subgroup.map_subtype_le _
  have hE5card : Nat.card E5 = 3 ^ 5 := by
    rw [hE5def, Subgroup.card_map_of_injective A.subtype_injective, hH5]
  have hE5el : IsElemAbelian 3 E5 := Lemma124.isElemAbelian_of_le hE5A hAel
  obtain ⟨H3, hH3⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E5) 3 (n := 3)
    (by rw [hE5card]; exact pow_dvd_pow 3 (by norm_num))
  set E3 : Subgroup G := H3.map E5.subtype with hE3def
  have hE3E5 : E3 ≤ E5 := Subgroup.map_subtype_le _
  have hE3card : Nat.card E3 = 3 ^ 3 := by
    rw [hE3def, Subgroup.card_map_of_injective E5.subtype_injective, hH3]
  have hE3el : IsElemAbelian 3 E3 := Lemma124.isElemAbelian_of_le hE3E5 hE5el
  have hE5R : IsEkIn 3 5 R E5 := ⟨hE5A.trans hAR, hE5el, hE5card⟩
  obtain ⟨hinD0, -, -⟩ := h104iv h.toSec11.toSec10Fails h.pair hk hR
  obtain ⟨-, -, A', hA'D, hE5A'⟩ := hinD0 E5 hE5R
  have hA'el : IsElemAbelian 3 A' := hA'D.1.1.2.1
  have hSCA : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hAel hx hy
  have hcommA' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hA'el hx hy
  have hconn : IsKConnectedIn 3 (CFSG.Open.pRank 3 (E ⊓ A) + 1) ⊤ A A' := by
    rw [hk]
    refine ⟨le_top, hAel, ?_, le_top, hA'el, ?_, Or.inr ⟨E3, E3, ⟨le_top, hE3el, hE3card⟩,
      ⟨le_top, hE3el, hE3card⟩, ?_, Relation.ReflTransGen.refl, ?_⟩⟩
    · rw [hcardA]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · have h1 : Nat.card E5 ≤ Nat.card A' := Subgroup.card_le_of_le hE5A'
      rw [hE5card] at h1
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h1
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcommA y (hE3E5.trans hE5A hy) x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcommA' y hy x (hE5A' (hE3E5 hx))
  have hDA : inD 3 M A := h104iii h.toSec11.toSec10Fails h.pair hSCA hA'D hconn
  exact h.pair.1.2.1.2 hDA.2

theorem prop117c_of_cex_false (h117 : Prop117_cex_falseStatement) : Lemma124.Prop117cStatement := by
  intro G _ _ m p B M E A h a ha ha1 K hK ht
  by_contra hcon
  rw [not_or] at hcon
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb', hnn⟩ := hex
    exact h117 (⟨hb', fun _ => hnn⟩ : Cex117 G m p B M E' A' a' K')
  · exact h117 (⟨⟨h, ⟨ha, ha1⟩, hK, Or.inr (Or.inr ht), hcon.1, hcon.2⟩,
      fun hex' => absurd hex' hex⟩ : Cex117 G m p B M E A a K)

theorem pRank_eq_four_of_inputs (h122 : Lemma122_i_iiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement)
    {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K) :
    CFSG.Open.pRank 3 A = 4 :=
  le_antisymm (pRank_le_four_of_inputs h123 h104ii h104iii h104iv h)
    (Lemma124.four_le_pRank_of_inputs h123 h122 (prop117c_of_cex_false h117) h hK hK3 hKM)

end Rank

section Bar

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Timmesfeld.Balance (barHom coe_barHom)

theorem exists_barOf_equiv_of_cover {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJX : J ≤ X)
    (hcov : barX p X J = ⊤) :
    ∃ e : barOf p J ≃* barOf p X, ∀ x : ↥J,
      e (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion hJX x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmemS : ∀ z : ↥X ⧸ GLAPPrimeCore p ↥X, z ∈ barX p X J := fun z => by
    rw [hcov]
    exact Subgroup.mem_top z
  have hOS : GLAPPrimeCore p ↥(barX p X J) = ⊥ := by
    have hbij : Function.Bijective (barX p X J).subtype :=
      ⟨(barX p X J).subtype_injective, fun z => ⟨⟨z, hmemS z⟩, rfl⟩⟩
    let t : ↥(barX p X J) ≃* (↥X ⧸ GLAPPrimeCore p ↥X) := MulEquiv.ofBijective _ hbij
    have h1 := glaPPrimeCore_map_iso p t
    rw [glaPPrimeCore_quotient_eq_bot hp] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ t.injective).1 h1
  let f : ↥J →* barOf p X :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hJX)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hmemS z)
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : f.ker = GLAPPrimeCore p ↥J := by
    apply le_antisymm
    ·
      have hTcop : Nat.Coprime p (Nat.card f.ker) := by
        apply Prop115.coprime_card_of_forall_orderOf_ne
        intro z hz hzp
        have hz1 : f z = 1 := hz
        have hinc : Subgroup.inclusion hJX z ∈ GLAPPrimeCore p ↥X := by
          rw [← QuotientGroup.eq_one_iff]
          exact hz1
        have hord : orderOf (Subgroup.inclusion hJX z) = p := by
          rw [orderOf_injective (Subgroup.inclusion hJX) (Subgroup.inclusion_injective hJX) z, hzp]
        have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) := CFSG.pPrimeCore_coprime_card
        exact (Prop115.orderOf_ne_of_coprime_card hp hinc hcop) hord
      exact le_sSup ⟨inferInstance, hTcop⟩
    ·
      have hnorm : ((GLAPPrimeCore p ↥J).map f).Normal :=
        Subgroup.Normal.map inferInstance f hsurj
      have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCore p ↥J).map f)) := by
        apply Prop115.coprime_card_of_forall_orderOf_ne
        intro w hw hwp
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
        have h1 : orderOf (f z) ∣ orderOf z := orderOf_map_dvd _ _
        rw [hwp] at h1
        have h2 : orderOf z ∣ Nat.card (GLAPPrimeCore p ↥J) := by
          have h := orderOf_dvd_natCard (⟨z, hz⟩ : GLAPPrimeCore p ↥J)
          have e : orderOf (⟨z, hz⟩ : GLAPPrimeCore p ↥J) = orderOf z :=
            (Subgroup.orderOf_coe _).symm
          rwa [e] at h
        have hcopJ : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
        exact absurd (h1.trans h2) ((Nat.Prime.coprime_iff_not_dvd hp).1 hcopJ)
      have hle : (GLAPPrimeCore p ↥J).map f ≤ GLAPPrimeCore p (barOf p X) :=
        le_sSup ⟨hnorm, hcop⟩
      rw [glaPPrimeCore_quotient_eq_bot hp] at hle
      intro z hz
      exact (MonoidHom.mem_ker).2 (Subgroup.mem_bot.1 (hle (Subgroup.mem_map_of_mem f hz)))
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj), fun x => ?_⟩
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem congr_barAut_of_cover {p : ℕ} {X J : Subgroup G} (hJX : J ≤ X)
    (e : barOf p J ≃* barOf p X)
    (he : ∀ x : ↥J, e (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion hJX x))
    {u : G} (huJ : u ∈ Subgroup.normalizer (J : Set G)) (huX : u ∈ Subgroup.normalizer (X : Set G)) :
    MulAut.congr e (barAut p J ⟨u, huJ⟩) = barAut p X ⟨u, huX⟩ := by
  apply MulEquiv.ext
  intro z
  obtain ⟨y, rfl⟩ := e.surjective z
  induction y using QuotientGroup.induction_on with
  | _ x =>
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, he, he,
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  congr 1

theorem isUnitaryAut_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {φ : MulAut X}
    (h : IsUnitaryAut (MulAut.congr e φ)) : IsUnitaryAut φ := by
  obtain ⟨hord, P, hP, h9, hfix⟩ := h
  refine ⟨?_, P.map e.symm.toMonoidHom, hP.map _, ?_, ?_⟩
  · rw [← hord]
    exact ((MulAut.congr e).orderOf_eq φ).symm
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact h9
  · rintro x ⟨y, hy, rfl⟩
    have := hfix y hy
    rw [MulAut.congr_apply] at this
    have h2 : φ (e.symm y) = e.symm y := by
      have := congrArg e.symm this
      simpa using this
    exact h2

end Bar

section Decomp

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_top_of {p : ℕ} {S : Subgroup G} (hS : IsElemAbelian p S) :
    IsElemAbelian p (⊤ : Subgroup ↥S) := by
  have hcomm : ∀ a b : ↥S, a * b = b * a := fun a b => hS.1.is_comm.comm a b
  have hcomm' : ∀ a b : ↥(⊤ : Subgroup ↥S), a * b = b * a := fun a b =>
    Subtype.ext (hcomm a.1 b.1)
  refine ⟨⟨⟨hcomm'⟩⟩, fun x _ => ?_⟩
  apply Subtype.ext
  exact hS.2 x.1 x.2

theorem decomp_of_normalizes (hI7 : Input7_L34) {A K A0 : Subgroup G}
    (hAel : IsElemAbelian 3 A) (hA4 : CFSG.Open.pRank 3 A = 4)
    (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.Open.IsQuasisimple (barOf 3 K))
    (hL : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥)
    (hA0A : A0 ≤ A) (h9 : Nat.card A0 = 9) (hdisj : A0 ⊓ centBar 3 A K = ⊥) :
    A = A0 ⊔ centBar 3 A K ∧ Nat.card (centBar 3 A K : Subgroup G) = 9 ∧
      Nat.card ((barAut 3 K).comp (Subgroup.inclusion hAN)).range = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set F := centBar 3 A K with hFdef
  have hFA : F ≤ A := inf_le_right
  let φ : ↥A →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hAN)
  have hker : F.subgroupOf A = φ.ker := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hFdef, centBar, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨γ, hγ, hγx⟩, -⟩
      have hγ' : γ = ⟨x, hAN hx⟩ := Subtype.ext hγx
      rw [hγ'] at hγ
      exact MonoidHom.mem_ker.1 hγ
    · intro h
      exact ⟨⟨⟨x, hAN hx⟩, MonoidHom.mem_ker.2 h, rfl⟩, hx⟩
  have hcardF : Nat.card F = Nat.card φ.ker := by
    rw [← hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv).symm
  have hR : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_top_of hAel) φ
  have hRrank : CFSG.Open.pRank 3 φ.range ≤ 2 := hI7 (barOf 3 K) hq hL hO φ.range hR
  have hRcard : Nat.card φ.range ≤ 9 := by
    rw [Lemma124.card_eq_pow_pRank hR]
    calc 3 ^ CFSG.Open.pRank 3 φ.range ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hRrank
      _ = 9 := by norm_num
  have hAcard : Nat.card A = 81 := by
    rw [Lemma124.card_eq_of_pRank_four hAel hA4]
    norm_num
  have hmul : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hcomm : ∀ h ∈ A0, ∀ f ∈ F, h * f = f * h := fun h hh f hf =>
    CFSG.Open.IsElemAbelian.comm hAel (hA0A hh) (hFA hf)
  have hprod : Nat.card (A0 ⊔ F : Subgroup G) = Nat.card A0 * Nat.card F :=
    Lemma124.card_eq_mul_of_sup_eq hcomm rfl hdisj
  have hsupA : A0 ⊔ F ≤ A := sup_le hA0A hFA
  have hle : Nat.card (A0 ⊔ F : Subgroup G) ≤ 81 := hAcard ▸ Subgroup.card_le_of_le hsupA
  rw [h9] at hprod
  have hF9 : Nat.card F = 9 := by
    have h1 : Nat.card F ≤ 9 := by omega
    have h2 : 9 ≤ Nat.card F := by
      by_contra hlt
      push Not at hlt
      have := Nat.mul_le_mul hRcard (show Nat.card φ.ker ≤ 8 by omega)
      omega
    omega
  refine ⟨?_, hF9, ?_⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge hsupA
    rw [hprod, hF9, hAcard]
  · show Nat.card φ.range = 9
    have hF9' : Nat.card φ.ker = 9 := hcardF ▸ hF9
    rw [hF9'] at hmul
    omega

end Decomp

section Cover

variable {G : Type} [Group G] [Finite G]

theorem barX_JJ_covers {A K : Subgroup G} (hAel : IsElemAbelian 3 A)
    (hq : CFSG.Open.IsQuasisimple (barOf 3 K)) :
    barX 3 (K ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G)) (JJ A K) = ⊤ ∧
      barX 3 K (JJ A K) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  set F := FF A K with hFdef
  have hFA : F ≤ A := inf_le_right
  have hF : ∀ f ∈ F, ∃ hfN : f ∈ Subgroup.normalizer (K : Set G), barAut 3 K ⟨f, hfN⟩ = 1 := by
    intro f hf
    obtain ⟨γ, hγ, hγf⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hf).1
    have hfN : f ∈ Subgroup.normalizer (K : Set G) := hγf ▸ γ.2
    refine ⟨hfN, ?_⟩
    have : (⟨f, hfN⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγf.symm
    rw [this]
    exact MonoidHom.mem_ker.1 hγ
  have hFN : F ≤ Subgroup.normalizer (K : Set G) := fun f hf => (hF f hf).1
  have hFp : IsPGroup 3 ↥F :=
    Lemma124.isPGroup_three_of_isElemAbelian (Lemma124.isElemAbelian_of_le hFA hAel)
  have hcover : ∀ k : ↥K, ∃ c : ↥K, (c : G) ∈ Subgroup.centralizer (F : Set G) ∧
      (QuotientGroup.mk c : barOf 3 K) = QuotientGroup.mk k := by
    intro k
    have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).ker := by
      rw [QuotientGroup.ker_mk']
      exact (Nat.Prime.coprime_iff_not_dvd hp3).1 CFSG.pPrimeCore_coprime_card
    have htriv : ∀ (member : ↥F) (element : ↥K),
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨member * element * (member : G)⁻¹,
          Subgroup.le_normalizer_iff.mp hFN member member.property element element.property⟩ =
            QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) element := by
      intro member element
      obtain ⟨hfN, hbar⟩ := hF member member.2
      have := congrArg (fun φ => φ (QuotientGroup.mk element : barOf 3 K)) hbar
      simp only [MulAut.one_apply] at this
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at this
      exact this
    obtain ⟨c, hcC, hc⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_centralizer_with_same_image_of_trivial_quotient_action
        3 hp3 F K hFp hFN (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) hker htriv k
    exact ⟨c, hcC, hc⟩
  have hHK : K ⊓ Subgroup.centralizer (F : Set G) ≤ K := inf_le_left
  have hcovH : barX 3 K (K ⊓ Subgroup.centralizer (F : Set G)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨c, hcC, hc⟩ := hcover k
    exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 ⟨c.2, hcC⟩, hc⟩
  obtain ⟨e, he⟩ := exists_barOf_equiv_of_cover (p := 3) hp3 hHK hcovH
  have hqH : CFSG.Open.IsQuasisimple (barOf 3 (K ⊓ Subgroup.centralizer (F : Set G))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  set H := K ⊓ Subgroup.centralizer (F : Set G) with hHdef
  obtain ⟨S, ⟨hSH, hSsn, hScov⟩, hSmin⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup G))
    {S : Subgroup G | S ≤ H ∧ IsSubnormal S H ∧ barX 3 H S = ⊤}
    ⟨H, le_rfl, IsSubnormal.refl H, barX_self 3 H⟩
  have hScomp : GLAPComponent 3 H S := by
    refine ⟨hSH, hSsn, ?_, ?_⟩
    · show IsComponentOf (barX 3 H S) ⊤
      rw [hScov]
      exact ⟨le_top, IsSubnormal.refl _,
        CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
          Subgroup.topEquiv.symm hqH⟩
    · intro J' hJ' hJ'sn heq
      exact hSmin J' ⟨hJ'.le.trans hSH, hJ'sn, heq.trans hScov⟩ hJ'
  have hSJ : S ≤ GLAPLayer 3 H := le_sSup hScomp
  have hcovJ : barX 3 H (GLAPLayer 3 H) = ⊤ :=
    eq_top_iff.2 (hScov ▸ Lemma124.barX_mono_aux 3 hSJ)
  have hJH : GLAPLayer 3 H ≤ H := Sec12b.layer_le 3 H
  refine ⟨hcovJ, ?_⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hcC, hc⟩ := hcover k
  obtain ⟨j, hj, o, ho, hjo⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJH hcovJ
    (show (c : G) ∈ H from ⟨c.2, hcC⟩)
  obtain ⟨y, hy, hyo⟩ := Subgroup.mem_map.1 ho
  have hyK : (QuotientGroup.mk (Subgroup.inclusion hHK y) : barOf 3 K) = 1 := by
    rw [← he y, (QuotientGroup.eq_one_iff y).2 hy, map_one]
  have hyo' : (y : G) = o := hyo
  refine Subgroup.mem_map.2 ⟨⟨j, (hJH hj).1⟩, Subgroup.mem_subgroupOf.2 hj, ?_⟩
  rw [← hc]
  have hcjo : c = ⟨j, (hJH hj).1⟩ * Subgroup.inclusion hHK y := by
    apply Subtype.ext
    show (c : G) = j * (y : G)
    rw [hyo']
    exact hjo
  rw [hcjo, QuotientGroup.mk_mul, hyK, mul_one]
  rfl

theorem barX_JJ_eq_top {A K : Subgroup G} (hAel : IsElemAbelian 3 A)
    (hq : CFSG.Open.IsQuasisimple (barOf 3 K)) : barX 3 K (JJ A K) = ⊤ :=
  (barX_JJ_covers hAel hq).2

end Cover

section Core124

variable {G : Type} [Group G] [Finite G]

theorem isLThreeFour_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsLThreeFour X) :
    IsLThreeFour Y := by
  obtain ⟨F, f, fi, hc, ⟨e'⟩⟩ := h
  exact ⟨F, f, fi, hc, ⟨e.symm.trans e'⟩⟩

theorem isLThreeFour_of_center_bot {X : Type} [Group X]
    (h : IsLThreeFour (X ⧸ Subgroup.center X)) (hc : Subgroup.center X = ⊥) : IsLThreeFour X :=
  isLThreeFour_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot) h

theorem center_eq_bot_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := (Subgroup.mem_center_iff.1 hz) (e.symm g)
    have h2 := congrArg e h1
    simpa using h2
  rw [h, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e.injective (by simpa using hz'))

theorem mem_normalizer_glaPLayer' {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  have hle : ∀ (g : G) (X : Subgroup G),
      GLBConj g (GLAPLayer p X) ≤ GLAPLayer p (GLBConj g X) := by
    intro g X
    refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun L hL => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_gLBConj hL g)
  have heq : GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
    refine le_antisymm ?_ (hle g X)
    have h1 := hle g⁻¹ (GLBConj g X)
    rw [gLBConj_inv_gLBConj] at h1
    have h2 := gLBConj_mono g h1
    rwa [gLBConj_gLBConj_inv] at h2
  rw [mem_normalizer_iff_gLBConj_eq, ← heq, gLBConj_eq_of_mem_normalizer hg]

theorem mem_normalizer_JJ {A K : Subgroup G} {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G))
    (huF : u ∈ Subgroup.centralizer ((FF A K : Subgroup G) : Set G)) :
    u ∈ Subgroup.normalizer ((JJ A K : Subgroup G) : Set G) := by
  have hC : u ∈ Subgroup.normalizer
      ((Subgroup.centralizer ((FF A K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ (v g : G), (∀ f ∈ FF A K, f * v = v * f) →
        g ∈ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) →
          v * g * v⁻¹ ∈ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) := by
      intro v g hv hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro f hf
      have h1 := hg f hf
      have h2 := hv f hf
      calc f * (v * g * v⁻¹) = (f * v) * g * v⁻¹ := by group
        _ = (v * f) * g * v⁻¹ := by rw [h2]
        _ = v * (f * g) * v⁻¹ := by group
        _ = v * (g * f) * v⁻¹ := by rw [h1]
        _ = v * g * (f * v⁻¹) := by group
        _ = v * g * (v⁻¹ * f) := by
          congr 1
          have := h2
          calc f * v⁻¹ = v⁻¹ * (v * f) * v⁻¹ := by group
            _ = v⁻¹ * (f * v) * v⁻¹ := by rw [this]
            _ = v⁻¹ * f := by group
        _ = v * g * v⁻¹ * f := by group
    have hu : ∀ f ∈ FF A K, f * u = u * f := fun f hf =>
      (Subgroup.mem_centralizer_iff.1 huF f hf)
    have hu' : ∀ f ∈ FF A K, f * u⁻¹ = u⁻¹ * f := by
      intro f hf
      have := hu f hf
      calc f * u⁻¹ = u⁻¹ * (u * f) * u⁻¹ := by group
        _ = u⁻¹ * (f * u) * u⁻¹ := by rw [this]
        _ = u⁻¹ * f := by group
    constructor
    · exact fun hg => key u g hu hg
    · intro hg
      have := key u⁻¹ (u * g * u⁻¹) hu' hg
      simpa [mul_assoc] using this
  have h1 : u ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    Sec12a.mem_normalizer_inf huK hC
  exact mem_normalizer_glaPLayer' h1

theorem isLThreeFour_modCenter_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour (X ⧸ Subgroup.center X)) : IsLThreeFour (Y ⧸ Subgroup.center Y) :=
  isLThreeFour_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) h

theorem cent_le_normalizer_of_unique {x : G} {Y : Subgroup G} (hY : GLAPComponent 3 (Cg x) Y)
    (hYt : IsLThreeFour (barOf 3 Y ⧸ Subgroup.center (barOf 3 Y)))
    (hYc : Subgroup.center (barOf 3 Y) = ⊥)
    (huniq : ∀ I : Subgroup G, GLAPComponent 3 (Cg x) I →
      IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)) → Subgroup.center (barOf 3 I) = ⊥ →
        I = Y) :
    Cg x ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  have hconj : GLBConj g (Cg x) = Cg x := by
    have hg' : g⁻¹ ∈ Subgroup.normalizer ((Cg x : Subgroup G) : Set G) :=
      Subgroup.le_normalizer ((Cg x).inv_mem hg)
    exact Prop121.map_conj_eq_of_normalizes hg'
  have h1 : GLAPComponent 3 (Cg x) (GLBConj g Y) := by
    have := glaPComponent_gLBConj hY g
    rwa [hconj] at this
  have h2 : IsLThreeFour (barOf 3 (GLBConj g Y) ⧸ Subgroup.center (barOf 3 (GLBConj g Y))) :=
    isLThreeFour_modCenter_congr (conjQuotEquiv 3 g Y) hYt
  have h3 : Subgroup.center (barOf 3 (GLBConj g Y)) = ⊥ :=
    center_eq_bot_of_equiv (conjQuotEquiv 3 g Y).symm hYc
  rw [mem_normalizer_iff_gLBConj_eq]
  exact huniq _ h1 h2 h3

theorem eq_one_of_mem_F_J {A K : Subgroup G} (hAel : IsElemAbelian 3 A)
    (hJcenter : Subgroup.center (barOf 3 (JJ A K)) = ⊥) {f : G} (hfF : f ∈ FF A K)
    (hfJ : f ∈ JJ A K) : f = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfA : f ∈ A := (inf_le_right : FF A K ≤ A) hfF
  have hf3 : f ^ 3 = 1 := hAel.2 f hfA
  have hJC : JJ A K ≤ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  set f' : ↥(JJ A K) := ⟨f, hfJ⟩ with hf'
  have hcent : (QuotientGroup.mk f' : barOf 3 (JJ A K)) ∈ Subgroup.center (barOf 3 (JJ A K)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | _ j =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show (j : G) * f = f * j
    exact ((Subgroup.mem_centralizer_iff.1 (hJC j.2)) f hfF).symm
  rw [hJcenter, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcent
  by_contra hne
  have hf'1 : f' ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hf'3 : f' ^ 3 = 1 := Subtype.ext (by simpa using hf3)
  have hord : orderOf f' = 3 := orderOf_eq_prime hf'3 hf'1
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥(JJ A K))) := CFSG.pPrimeCore_coprime_card
  exact (Prop115.orderOf_ne_of_coprime_card (by norm_num) hcent hcop) hord

theorem exists_unitary_J {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex121 G m 3 B M E A a) (h122iii : Lemma122_iiiStatement) (hF : IsEkIn 3 2 A (FF A K))
    (hVx : ∀ x ∈ FF A K, x ≠ 1 → ∀ V : Subgroup G,
      V ≤ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G) →
      V ≤ derivedInf (⨆ g ∈ (alphaOf 3 M ⊓ Cg x), GLBConj g V) → V ≤ centBar 3 ⊤ (JJ A K))
    (hcov : barX 3 K (JJ A K) = ⊤) (hJK : JJ A K ≤ K)
    (hu : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩)) :
    ∃ u ∈ pCoreOf 2 M ⊓ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (JJ A K : Set G),
        IsUnitaryAut (barAut 3 (JJ A K) ⟨u, hu⟩) := by
  obtain ⟨u₁, hu₁X, hu₁N, hu₁U⟩ := hu
  obtain ⟨V, hVle, hVeq, hVinf⟩ := h122iii h hF
  set X : Subgroup G := Tof 3 M a ⊓ Subgroup.centralizer (A : Set G) with hXdef
  set S₁ : Subgroup G := X ⊓ pCoreOf 2 M with hS₁
  set S₂ : Subgroup G := X ⊓ centBar 3 ⊤ (JJ A K) with hS₂
  have hXM : X ≤ M :=
    inf_le_left.trans ((Sec12a.tof_le_alphaOf M a).trans (Sec12a.alphaOf_le_self M))
  have hXle : X ≤ S₂ ⊔ S₁ := by
    rw [sup_comm]
    refine hVeq.le.trans (sup_le le_sup_left ?_)
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
    exact le_sup_of_le_right (le_inf (hVle x hx hx1)
      (hVx x hx hx1 (V x) (hVle x hx hx1) (hVinf x hx hx1)))
  have hS₂N : S₂ ≤ Subgroup.normalizer (S₁ : Set G) := by
    intro s hs
    exact Prop121.normalizer_inf_mem (Subgroup.le_normalizer hs.1)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hXM hs.1))
  obtain ⟨z, hz, o, ho, hzo⟩ := Prop121.mem_sup_decomp hS₂N (hXle hu₁X)
  obtain ⟨γ, hγker, hγz⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hz.2).1
  have hzN : z ∈ Subgroup.normalizer ((JJ A K : Subgroup G) : Set G) := hγz ▸ γ.2
  have hu₁C : u₁ ∈ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (hF.1 : FF A K ≤ A)) hu₁X.2
  have huJ : u₁ ∈ Subgroup.normalizer ((JJ A K : Subgroup G) : Set G) :=
    mem_normalizer_JJ hu₁N hu₁C
  have hoeq : o = z⁻¹ * u₁ := by rw [hzo]; group
  have hoN : o ∈ Subgroup.normalizer ((JJ A K : Subgroup G) : Set G) := by
    rw [hoeq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzN) huJ
  have hbar : barAut 3 (JJ A K) ⟨u₁, huJ⟩ = barAut 3 (JJ A K) ⟨o, hoN⟩ := by
    have hmul : (⟨u₁, huJ⟩ : ↥(Subgroup.normalizer ((JJ A K : Subgroup G) : Set G))) =
        ⟨z, hzN⟩ * ⟨o, hoN⟩ := Subtype.ext hzo
    have hγeq : (⟨z, hzN⟩ : ↥(Subgroup.normalizer ((JJ A K : Subgroup G) : Set G))) = γ :=
      Subtype.ext hγz.symm
    have hz1 : barAut 3 (JJ A K) ⟨z, hzN⟩ = 1 := by
      rw [hγeq]
      exact MonoidHom.mem_ker.1 hγker
    rw [hmul, map_mul, hz1, one_mul]
  obtain ⟨e, he⟩ := exists_barOf_equiv_of_cover (p := 3) (by norm_num) hJK hcov
  have hcongr := congr_barAut_of_cover hJK e he huJ hu₁N
  have hUJ : IsUnitaryAut (barAut 3 (JJ A K) ⟨u₁, huJ⟩) :=
    isUnitaryAut_of_congr e (by rw [hcongr]; exact hu₁U)
  exact ⟨o, ⟨⟨ho.2, ho.1.1⟩, ho.1.2⟩, hoN, by rw [← hbar]; exact hUJ⟩

theorem mem_normalizer_centralizer_of_comm {F : Subgroup G} {u : G} (hu : ∀ f ∈ F, f * u = u * f) :
    u ∈ Subgroup.normalizer ((Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := by
  have key : ∀ (v g : G), (∀ f ∈ F, f * v = v * f) →
      g ∈ Subgroup.centralizer (F : Set G) → v * g * v⁻¹ ∈ Subgroup.centralizer (F : Set G) := by
    intro v g hv hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro f hf
    have h1 := hg f hf
    have h2 := hv f hf
    have h3 : f * v⁻¹ = v⁻¹ * f := by
      calc f * v⁻¹ = v⁻¹ * (v * f) * v⁻¹ := by group
        _ = v⁻¹ * (f * v) * v⁻¹ := by rw [h2]
        _ = v⁻¹ * f := by group
    calc f * (v * g * v⁻¹) = (f * v) * g * v⁻¹ := by group
      _ = (v * f) * g * v⁻¹ := by rw [h2]
      _ = v * (f * g) * v⁻¹ := by group
      _ = v * (g * f) * v⁻¹ := by rw [h1]
      _ = v * g * (f * v⁻¹) := by group
      _ = v * g * (v⁻¹ * f) := by rw [h3]
      _ = v * g * v⁻¹ * f := by group
  have hu' : ∀ f ∈ F, f * u⁻¹ = u⁻¹ * f := by
    intro f hf
    have := hu f hf
    calc f * u⁻¹ = u⁻¹ * (u * f) * u⁻¹ := by group
      _ = u⁻¹ * (f * u) * u⁻¹ := by rw [this]
      _ = u⁻¹ * f := by group
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => key u g hu hg
  · intro hg
    have := key u⁻¹ (u * g * u⁻¹) hu' hg
    simpa [mul_assoc] using this

theorem centBar_barAut_eq_one {A K : Subgroup G} {f : G} (hf : f ∈ centBar 3 A K) :
    ∃ hfN : f ∈ Subgroup.normalizer (K : Set G), barAut 3 K ⟨f, hfN⟩ = 1 := by
  obtain ⟨γ, hγ, hγf⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hf).1
  have hfN : f ∈ Subgroup.normalizer (K : Set G) := hγf ▸ γ.2
  refine ⟨hfN, ?_⟩
  have : (⟨f, hfN⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγf.symm
  rw [this]
  exact MonoidHom.mem_ker.1 hγ

theorem exists_unitary_cent_A {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex121 G m 3 B M E A a) (hdec : A = (E ⊓ A) ⊔ FF A K)
    (hTN : Tof 3 M a ≤ Subgroup.normalizer (K : Set G))
    (hu : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩)) :
    ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  obtain ⟨u₀, hu₀, hu₀N, hu₀U⟩ := hu
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hFA : FF A K ≤ A := inf_le_right
  have hA0A : E ⊓ A ≤ A := inf_le_right
  have hAα : A ≤ Subgroup.normalizer ((alphaOf 3 M ⊓ Cg a : Subgroup G) : Set G) := by
    intro k hk
    have hkM : k ∈ M := hAM hk
    have hkCa : k ∈ Cg a := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact CFSG.Open.IsElemAbelian.comm hAel h.ha.1 hk
    exact Sec12a.mem_normalizer_inf (le_normalizer_alphaOf 3 M hkM) (Subgroup.le_normalizer hkCa)
  have hAT : A ≤ Subgroup.normalizer ((Tof 3 M a : Subgroup G) : Set G) :=
    hAα.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (alphaOf 3 M ⊓ Cg a))
  set T₀ : Subgroup G := Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) with hT₀
  have hFT₀ : FF A K ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro f hf
    exact Prop121.normalizer_inf_mem (hAT (hFA hf))
      (mem_normalizer_centralizer_of_comm fun b hb =>
        CFSG.Open.IsElemAbelian.comm hAel (hA0A hb) (hFA hf))
  have hT₀2 : IsPGroup 2 ↥T₀ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (alphaOf 3 M ⊓ Cg a)).to_le inf_le_left
  have hT₀cop : ¬ 3 ∣ Nat.card ↥T₀ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT₀2
    rw [hn]
    intro hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow hd))
      (by norm_num)
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 hp3 (FF A K) T₀
    (Lemma124.isPGroup_three_of_isElemAbelian (Lemma124.isElemAbelian_of_le hFA hAel)) hT₀cop hFT₀
  have hu₀T : u₀ ∈ T₀ := hu₀
  have hPJ : T₀ ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((⁅T₀, FF A K⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left T₀ (FF A K))
  obtain ⟨c, hc, r, hr, hcr⟩ := Prop121.mem_sup_decomp hPJ
    (show u₀ ∈ (T₀ ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G)) ⊔ ⁅T₀, FF A K⁆ by
      rw [sup_comm, ← hfac]
      exact hu₀T)
  have hrK : ⁅T₀, FF A K⁆ ≤ centBar 3 ⊤ K := by
    refine Subgroup.commutator_le.2 fun t ht f hf => ?_
    obtain ⟨hfN, hfbar⟩ := centBar_barAut_eq_one hf
    have htN : t ∈ Subgroup.normalizer (K : Set G) := hTN ht.1
    have hγ : barAut 3 K
        ⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨f, hfN⟩⁆ = 1 := by
      rw [map_commutatorElement, hfbar, commutatorElement_one_right]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨_, MonoidHom.mem_ker.2 hγ, rfl⟩,
      Subgroup.mem_top _⟩
  obtain ⟨hrN, hrbar⟩ := centBar_barAut_eq_one (hrK hr)
  have hceq : c = u₀ * r⁻¹ := by rw [hcr]; group
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := by
    rw [hceq]
    exact Subgroup.mul_mem _ hu₀N (Subgroup.inv_mem _ hrN)
  have hcomm : ∀ b ∈ E ⊓ A, ∀ f ∈ FF A K, b * f = f * b := fun b hb f hf =>
    CFSG.Open.IsElemAbelian.comm hAel (hA0A hb) (hFA hf)
  refine ⟨c, ⟨hc.1.1, ?_⟩, hcN, ?_⟩
  · show c ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxsup : x ∈ (E ⊓ A) ⊔ FF A K := hdec ▸ hx
    obtain ⟨b, hb, f, hf, rfl⟩ := Lemma124.exists_mul_of_mem_sup hcomm hxsup
    have h1 : b * c = c * b := Subgroup.mem_centralizer_iff.1 hc.1.2 b hb
    have h2 : f * c = c * f := Subgroup.mem_centralizer_iff.1 hc.2 f hf
    calc b * f * c = b * (f * c) := by group
      _ = b * (c * f) := by rw [h2]
      _ = (b * c) * f := by group
      _ = (c * b) * f := by rw [h1]
      _ = c * (b * f) := by group
  · have hbar : barAut 3 K ⟨c, hcN⟩ = barAut 3 K ⟨u₀, hu₀N⟩ := by
      have : (⟨u₀, hu₀N⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨c, hcN⟩ * ⟨r, hrN⟩ :=
        Subtype.ext hcr
      rw [this, map_mul, hrbar, mul_one]
    rw [hbar]
    exact hu₀U

theorem mem_centBar_of_component {A K : Subgroup G} {a : G} (haA : a ∈ A) (hKC : K ≤ Cg a) :
    a ∈ centBar 3 A K := by
  have hcomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (hKC hk) a (Set.mem_singleton a)
  have haN : a ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk => (hcomm k hk).symm)
  exact Lemma1112b.mem_centBar_of_mem_top (Lemma1112b.mem_centBar_top_of_central haN hcomm) haA

end Core124

section PrintI

variable {G : Type} [Group G] [Finite G]

theorem conj_injective_of_center_bot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : z * g * z⁻¹ = g := by
      have := DFunLike.congr_fun hz g
      simpa [MulAut.conj_apply] using this
    calc g * z = (z * g * z⁻¹) * z := by rw [h1]
      _ = z * g := by group
  rw [h] at hz'
  exact Subgroup.mem_bot.1 hz'

theorem ker_coprime_aux {K S : Subgroup G} (hSK : S ≤ K) :
    Nat.Coprime 3 (Nat.card ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp
      (Subgroup.inclusion hSK)).ker) := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hSK) with hf
  have hle : f.ker.map (Subgroup.inclusion hSK) ≤ GLAPPrimeCore 3 ↥K := by
    rintro _ ⟨x, hx, rfl⟩
    have : f x = 1 := hx
    exact (QuotientGroup.eq_one_iff _).1 this
  have hcard : Nat.card f.ker = Nat.card (f.ker.map (Subgroup.inclusion hSK)) :=
    (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hSK)).symm
  have hdvd : Nat.card f.ker ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le hle
  exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card

theorem exists_inner_complement {A K : Subgroup G} (hAel : IsElemAbelian 3 A) (hSC : IsSCp 3 ⊤ A)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hcenter : Subgroup.center (barOf 3 K) = ⊥)
    (hinn : ∀ a (ha : a ∈ A), ∃ z : barOf 3 K, barAut 3 K ⟨a, hAN ha⟩ = MulAut.conj z)
    (hR9 : Nat.card ((barAut 3 K).comp (Subgroup.inclusion hAN)).range = 9) :
    ∃ S : Subgroup G, S ≤ A ∧ S ≤ K ∧ Nat.card S = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  set φ : ↥A →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hAN) with hφ
  have hφapp : ∀ a (ha : a ∈ A), φ ⟨a, ha⟩ = barAut 3 K ⟨a, hAN ha⟩ := fun a ha => rfl
  let conjH : barOf 3 K →* MulAut (barOf 3 K) := MulAut.conj
  have hconj_inj : Function.Injective conjH := conj_injective_of_center_bot hcenter
  set Pbar : Subgroup (barOf 3 K) := φ.range.comap conjH with hPbar
  have hmap : Pbar.map conjH = φ.range := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · rintro _ ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨z, hz⟩ := hinn a ha
      have hzz : conjH z = φ ⟨a, ha⟩ := by rw [hφapp]; exact hz.symm
      exact ⟨z, ⟨⟨a, ha⟩, hzz.symm⟩, hzz⟩
  have hPcard : Nat.card Pbar = 9 := by
    have := Subgroup.card_map_of_injective (K := Pbar) hconj_inj
    rw [hmap] at this
    rw [← this]
    exact hR9
  have hφcomm : ∀ x y : ↥A, φ x * φ y = φ y * φ x := fun x y => by
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm x y]
  have hPcomm : ∀ z ∈ Pbar, ∀ w ∈ Pbar, z * w = w * z := by
    intro z hz w hw
    obtain ⟨x, hx⟩ := hz
    obtain ⟨y, hy⟩ := hw
    apply hconj_inj
    rw [map_mul, map_mul]
    show conjH z * conjH w = conjH w * conjH z
    rw [← hx, ← hy]
    exact hφcomm x y
  have hPexp : ∀ z ∈ Pbar, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨x, hx⟩ := hz
    apply hconj_inj
    rw [map_pow, map_one]
    show (conjH z) ^ 3 = 1
    rw [← hx, ← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hAel.2 x.1 x.2)
    rw [this, map_one]
  let mkK : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
  set Pfull : Subgroup G := (Pbar.comap mkK).map K.subtype with hPfull
  have hPK : Pfull ≤ K := Subgroup.map_subtype_le _
  have hmemP : ∀ k : ↥K, (k : G) ∈ Pfull ↔ mkK k ∈ Pbar := by
    intro k
    constructor
    · rintro ⟨k', hk', hkk⟩
      have : k' = k := Subtype.ext hkk
      subst this
      exact hk'
    · intro h
      exact ⟨k, h, rfl⟩
  have hz_of : ∀ a (ha : a ∈ A), ∃ z ∈ Pbar, barAut 3 K ⟨a, hAN ha⟩ = MulAut.conj z := by
    intro a ha
    obtain ⟨z, hz⟩ := hinn a ha
    exact ⟨z, ⟨⟨a, ha⟩, by rw [hφapp]; exact hz⟩, hz⟩
  have htr : ∀ a (ha : a ∈ A) (k : ↥K), mkK k ∈ Pbar →
      mkK (K.normalizerMonoidHom ⟨a, hAN ha⟩ k) = mkK k := by
    intro a ha k hk
    obtain ⟨z, hzP, hz⟩ := hz_of a ha
    have h1 : mkK (K.normalizerMonoidHom ⟨a, hAN ha⟩ k) = barAut 3 K ⟨a, hAN ha⟩ (mkK k) :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 K ⟨a, hAN ha⟩ k).symm
    rw [h1, hz, MulAut.conj_apply]
    have := hPcomm z hzP (mkK k) hk
    calc z * mkK k * z⁻¹ = (mkK k * z) * z⁻¹ := by rw [this]
      _ = mkK k := by group
  have hAmemP : ∀ a (ha : a ∈ A) (y : G), y ∈ Pfull → a * y * a⁻¹ ∈ Pfull := by
    intro a ha y hy
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨K.normalizerMonoidHom ⟨a, hAN ha⟩ k, ?_, ?_⟩
    · show mkK _ ∈ Pbar
      rw [htr a ha k hk]
      exact hk
    · exact Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨a, hAN ha⟩ k
  have hANP : A ≤ Subgroup.normalizer (Pfull : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hAmemP a ha y
    · intro hy
      have := hAmemP a⁻¹ (A.inv_mem ha) _ hy
      simpa [mul_assoc] using this
  have hApgroup : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  let hP : ↥Pfull →* barOf 3 K := mkK.comp (Subgroup.inclusion hPK)
  have hkerP : ¬ 3 ∣ Nat.card hP.ker := (Nat.Prime.coprime_iff_not_dvd hp3).1 (ker_coprime_aux hPK)
  have htriv : ∀ (member : ↥A) (element : ↥Pfull), hP ⟨member * element * (member : G)⁻¹,
      Subgroup.le_normalizer_iff.mp hANP member member.property element element.property⟩ =
        hP element := by
    rintro ⟨a, ha⟩ ⟨y, hy⟩
    have hk : mkK ⟨y, hPK hy⟩ ∈ Pbar := (hmemP ⟨y, hPK hy⟩).1 hy
    exact htr a ha ⟨y, hPK hy⟩ hk
  have hfix := fun (element : ↥Pfull) =>
    CFSG.RankThreeEvenClassification.Helpers.exists_centralizer_with_same_image_of_trivial_quotient_action
      3 hp3 A Pfull hApgroup hANP hP hkerP htriv element
  set D : Subgroup G := Pfull ⊓ Subgroup.centralizer (A : Set G) with hDdef
  have hDK : D ≤ K := inf_le_left.trans hPK
  let hD : ↥D →* barOf 3 K := mkK.comp (Subgroup.inclusion hDK)
  have hDrange : hD.range = Pbar := by
    apply le_antisymm
    · rintro _ ⟨⟨d, hd⟩, rfl⟩
      exact (hmemP ⟨d, hDK hd⟩).1 hd.1
    · intro pb hpb
      obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective pb
      have hk₀ : (k₀ : G) ∈ Pfull := (hmemP k₀).2 hpb
      obtain ⟨c, hcC, hc⟩ := hfix ⟨k₀, hk₀⟩
      exact ⟨⟨(c : G), c.2, hcC⟩, hc⟩
  have hDimg : ∀ t : ↥D, hD t ∈ Pbar := fun t => hDrange ▸ ⟨t, rfl⟩
  have hNcop : Nat.Coprime (Nat.card hD.ker) hD.ker.index := by
    have hidx : hD.ker.index = 9 := by
      rw [Subgroup.index_ker, hDrange]
      exact hPcard
    rw [hidx]
    exact (Nat.Coprime.pow_left 2 (ker_coprime_aux hDK)).symm
  obtain ⟨Hc, hHc⟩ := Subgroup.exists_right_complement'_of_coprime hNcop
  have hHcard : Nat.card Hc = 9 := by
    have h1 := hHc.symm.index_eq_card
    have hidx : hD.ker.index = 9 := by
      rw [Subgroup.index_ker, hDrange]
      exact hPcard
    rw [← h1, hidx]
  have hdisj : ∀ t ∈ Hc, hD t = 1 → t = 1 := by
    intro t ht h1
    have h2 : t ∈ hD.ker ⊓ Hc := ⟨h1, ht⟩
    rw [disjoint_iff.1 hHc.disjoint] at h2
    exact Subgroup.mem_bot.1 h2
  have hHcel : IsElemAbelian 3 Hc := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hc : (a : ↥D) * b * (a : ↥D)⁻¹ * (b : ↥D)⁻¹ = 1 := by
        apply hdisj
        · exact Hc.mul_mem (Hc.mul_mem (Hc.mul_mem a.2 b.2) (Hc.inv_mem a.2)) (Hc.inv_mem b.2)
        · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          have h1 := hPcomm _ (hDimg (a : ↥D)) _ (hDimg (b : ↥D))
          calc hD a * hD b * (hD a)⁻¹ * (hD b)⁻¹ = (hD b * hD a) * (hD a)⁻¹ * (hD b)⁻¹ := by rw [h1]
            _ = 1 := by group
      have h2 : (a : ↥D) * b = b * a := by
        have h3 : (a : ↥D) * b = (a * b * (a : ↥D)⁻¹ * (b : ↥D)⁻¹) * (b * a) := by group
        rw [h3, hc, one_mul]
      exact h2
    · apply hdisj
      · exact Hc.pow_mem hx 3
      · rw [map_pow]
        exact hPexp _ (hDimg x)
  refine ⟨Hc.map D.subtype, ?_, ?_, ?_⟩
  · have hSel : IsElemAbelian 3 (Hc.map D.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hHcel D.subtype
    have hSD : Hc.map D.subtype ≤ D := Subgroup.map_subtype_le _
    have hAS : A ≤ Subgroup.centralizer ((Hc.map D.subtype : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact ((Subgroup.mem_centralizer_iff.1 (hSD hs).2) a ha).symm
    have hE : IsElemAbelian 3 (A ⊔ Hc.map D.subtype) := isElemAbelian_sup_of_commute hAel hSel hAS
    have := hSC.2.2 (A ⊔ Hc.map D.subtype) le_top hE le_sup_left
    exact this ▸ le_sup_right
  · exact (Subgroup.map_subtype_le _).trans hDK
  · rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hHcard

theorem exists_conj_of_inducesInner {K : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx : InducesInner 3 K x) :
    ∃ z : barOf 3 K, barAut 3 K ⟨x, hxN⟩ = MulAut.conj z := by
  obtain ⟨k, hk, hkx⟩ := hx
  obtain ⟨γ, hγker, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hkx).1
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  have hxe : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩ * γ := by
    apply Subtype.ext
    show x = k * (γ : G)
    have hγ' : (γ : G) = k⁻¹ * x := hγ
    rw [hγ']
    group
  rw [hxe, map_mul, MonoidHom.mem_ker.1 hγker, mul_one]
  exact l119_barAut_eq_conj (p := 3) ⟨k, hk⟩

theorem mem_JJ_of_pow_three {A K : Subgroup G}
    (hcovH : barX 3 (K ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G)) (JJ A K) = ⊤)
    {s : G} (hsH : s ∈ K ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G)) (hs3 : s ^ 3 = 1) :
    s ∈ JJ A K := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  set H := K ⊓ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) with hH
  have hJH : JJ A K ≤ H := Sec12b.layer_le 3 H
  obtain ⟨j, hj, o, ho, hjo⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJH hcovH hsH
  have hoH : o ∈ H := (Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 H ≤ H) ho
  have hJnorm : ∀ h ∈ H, ∀ y ∈ JJ A K, h * y * h⁻¹ ∈ JJ A K := fun h hh y hy =>
    (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_glaPLayer' (p := 3) (Subgroup.le_normalizer hh)) y).1 hy
  have hj1 : o * j * o⁻¹ ∈ JJ A K := hJnorm o hoH j hj
  have hj2 : o * o * j * (o * o)⁻¹ ∈ JJ A K := hJnorm (o * o) (H.mul_mem hoH hoH) j hj
  have hkey : (j * (o * j * o⁻¹) * (o * o * j * (o * o)⁻¹)) * o ^ 3 = 1 := by
    have hs3' : s * s * s = 1 := by rw [← pow_three']; exact hs3
    rw [hjo] at hs3'
    have e : j * o * (j * o) * (j * o) =
        (j * (o * j * o⁻¹) * (o * o * j * (o * o)⁻¹)) * o ^ 3 := by group
    rw [← e]
    exact hs3'
  have ho3 : o ^ 3 ∈ JJ A K := by
    have h1 : o ^ 3 = (j * (o * j * o⁻¹) * (o * o * j * (o * o)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right hkey
    rw [h1]
    exact (JJ A K).inv_mem ((JJ A K).mul_mem ((JJ A K).mul_mem hj hj1) hj2)
  have hcop : Nat.Coprime 3 (orderOf o) := by
    have hd : orderOf o ∣ Nat.card (GLAPPrimeCoreOf 3 H) := by
      have h := orderOf_dvd_natCard (⟨o, ho⟩ : GLAPPrimeCoreOf 3 H)
      have e : orderOf (⟨o, ho⟩ : GLAPPrimeCoreOf 3 H) = orderOf o := (Subgroup.orderOf_coe _).symm
      rwa [e] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp3).2
      (fun h3 => not_dvd_card_glaPPrimeCoreOf hp3 H (h3.trans hd))
  have hoJ : o ∈ JJ A K := by
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hk]
    exact (JJ A K).pow_mem ho3 k
  rw [hjo]
  exact (JJ A K).mul_mem hj hoJ

theorem lemma124_print_i_of_inputs
    (h122 : Lemma122_i_iiStatement) (h123 : Lemma123Statement) (h117 : Prop117_cex_falseStatement)
    (h104ii : Lemma104_iiStatement) (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement)
    (hI7 : Input7_L34)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hcenter : Subgroup.center (barOf 3 K) = ⊥) :
    A = (A ⊓ JJ A K) ⊔ FF A K ∧ (A ⊓ JJ A K) ⊓ FF A K = ⊥ ∧ Nat.card (A ⊓ JJ A K : Subgroup G) = 9 ∧
      Nat.card (FF A K : Subgroup G) = 9 := by
  haveI hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA4 : CFSG.Open.pRank 3 A = 4 :=
    pRank_eq_four_of_inputs h122 h123 h117 h104ii h104iii h104iv h hK hK3 hKM
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := l119_isQuasisimple_barOf (p := 3) (by norm_num) hK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) (by norm_num)
  have hdisj : (E ⊓ A) ⊓ centBar 3 A K = ⊥ := Lemma124.inter_disjoint_centBar_of_faithful hA0.2
  obtain ⟨hdec, hF9, hR9⟩ :=
    decomp_of_normalizes hI7 hAel hA4 hAN hq hK3 hO inf_le_right hA0.1 hdisj
  have hFA : FF A K ≤ A := inf_le_right
  obtain ⟨hcovH, hcov⟩ := barX_JJ_covers hAel hq
  have hJK : JJ A K ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  obtain ⟨eJ, -⟩ := exists_barOf_equiv_of_cover (p := 3) (by norm_num) hJK hcov
  have hJcenter : Subgroup.center (barOf 3 (JJ A K)) = ⊥ := center_eq_bot_of_equiv eJ hcenter
  have hcomm : ∀ b ∈ E ⊓ A, ∀ f ∈ FF A K, b * f = f * b := fun b hb f hf =>
    CFSG.Open.IsElemAbelian.comm hAel ((inf_le_right : E ⊓ A ≤ A) hb) (hFA hf)
  have hinn : ∀ x (hx : x ∈ A), ∃ z : barOf 3 K, barAut 3 K ⟨x, hAN hx⟩ = MulAut.conj z := by
    intro x hx
    have hxsup : x ∈ (E ⊓ A) ⊔ FF A K := hdec ▸ hx
    obtain ⟨b, hb, f, hf, rfl⟩ := Lemma124.exists_mul_of_mem_sup hcomm hxsup
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := hA0.2.1 hb
    obtain ⟨z, hz⟩ := exists_conj_of_inducesInner hbN (hA0.2.2.2 b hb)
    obtain ⟨hfN, hfbar⟩ := centBar_barAut_eq_one hf
    refine ⟨z, ?_⟩
    have : (⟨b * f, hAN hx⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨b, hbN⟩ * ⟨f, hfN⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, hz, hfbar, mul_one]
  have hSC : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  obtain ⟨S, hSA, hSK, hS9⟩ := exists_inner_complement hAel hSC hAN hcenter hinn hR9
  have hSJ : S ≤ JJ A K := by
    intro s hs
    have hsC : s ∈ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact CFSG.Open.IsElemAbelian.comm hAel (hFA hf) (hSA hs)
    exact mem_JJ_of_pow_three hcovH ⟨hSK hs, hsC⟩ (hAel.2 s (hSA hs))
  have hSAJ : S ≤ A ⊓ JJ A K := le_inf hSA hSJ
  have hdisjJ : (A ⊓ JJ A K) ⊓ FF A K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    exact eq_one_of_mem_F_J hAel hJcenter hf.2 hf.1.2
  have hAJcomm : ∀ x ∈ A ⊓ JJ A K, ∀ f ∈ FF A K, x * f = f * x := fun x hx f hf =>
    CFSG.Open.IsElemAbelian.comm hAel hx.1 (hFA hf)
  have hprod : Nat.card ((A ⊓ JJ A K) ⊔ FF A K : Subgroup G) = Nat.card (A ⊓ JJ A K : Subgroup G) * 9 := by
    rw [← hF9]
    exact Lemma124.card_eq_mul_of_sup_eq hAJcomm rfl hdisjJ
  have hAcard : Nat.card A = 81 := by
    rw [Lemma124.card_eq_of_pRank_four hAel hA4]
    norm_num
  have hsupA : (A ⊓ JJ A K) ⊔ FF A K ≤ A := sup_le inf_le_left hFA
  have hle : Nat.card ((A ⊓ JJ A K) ⊔ FF A K : Subgroup G) ≤ 81 := hAcard ▸ Subgroup.card_le_of_le hsupA
  have hS9' : 9 ≤ Nat.card (A ⊓ JJ A K : Subgroup G) := hS9 ▸ Subgroup.card_le_of_le hSAJ
  have hAJ9 : Nat.card (A ⊓ JJ A K : Subgroup G) = 9 := by omega
  refine ⟨?_, hdisjJ, hAJ9, hF9⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hsupA
  rw [hprod, hAJ9, hAcard]

end PrintI

section Main124

variable {G : Type} [Group G] [Finite G]

theorem lemma124_core_of_inputs
    (h122 : Lemma122_i_iiStatement) (h122iii : Lemma122_iiiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (hI7 : Input7_L34)
    (hNorm : NormClaim) (hKx : KxClaim) (hType : TypeClaim) (hUniq : UniqClaim) (hVx : VxClaim)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) :
    (A = (E ⊓ A) ⊔ FF A K ∧ (E ⊓ A) ⊓ FF A K = ⊥ ∧ A = (A ⊓ JJ A K) ⊔ FF A K ∧
        (A ⊓ JJ A K) ⊓ FF A K = ⊥ ∧ Nat.card (A ⊓ JJ A K : Subgroup G) = 9 ∧
        CFSG.Open.pRank 3 (FF A K) = 2 ∧ CFSG.Open.pRank 3 A = 4) ∧
      (∀ x ∈ FF A K, x ≠ 1 →
        Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G) ∧
          barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤) ∧
      (IsLThreeFour (barOf 3 (JJ A K)) ∧
        ∀ x ∈ FF A K, x ≠ 1 → IsLThreeFour (barOf 3 (Kx 3 (JJ A K) x))) ∧
      (∃ u ∈ pCoreOf 2 M ⊓ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
        ∃ hu : u ∈ Subgroup.normalizer (JJ A K : Set G),
          IsUnitaryAut (barAut 3 (JJ A K) ⟨u, hu⟩)) ∧
      K = Kx 3 (JJ A K) a := by
  haveI hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA4 : CFSG.Open.pRank 3 A = 4 :=
    pRank_eq_four_of_inputs h122 h123 h117 h104ii h104iii h104iv h hK hK3 hKM
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hKC : K ≤ Cg a := Lemma124.comp_le_aux hK
  have haA : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have haF : a ∈ centBar 3 A K := mem_centBar_of_component haA hKC
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rcases hNorm h hK hK3 hKM hA0 hA4 haF ha1 hK hK3 hA0.2.1 hA0.2.2.2 hA0.2.2.1 with hN | hKM'
    · exact hN
    · exfalso
      apply hKM
      exact Lemma124.barX_mono_aux 3 (le_inf hKM' hKC)
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := l119_isQuasisimple_barOf (p := 3) (by norm_num) hK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) (by norm_num)
  have hdisj : (E ⊓ A) ⊓ centBar 3 A K = ⊥ := Lemma124.inter_disjoint_centBar_of_faithful hA0.2
  obtain ⟨hdec, hF9, -⟩ := decomp_of_normalizes hI7 hAel hA4 hAN hq hK3 hO inf_le_right hA0.1 hdisj
  have hFA : FF A K ≤ A := inf_le_right
  have hFel : IsElemAbelian 3 (FF A K) := Lemma124.isElemAbelian_of_le hFA hAel
  have hFrank : CFSG.Open.pRank 3 (FF A K) = 2 := Lemma124.pRank_eq_two_of_card_nine hFel hF9
  have hKxcl := hKx h hK hK3 hKM hu₀ hA0 hAN
  have hcov : barX 3 K (JJ A K) = ⊤ := barX_JJ_eq_top hAel hq
  have hcenter : Subgroup.center (barOf 3 K) = ⊥ := hType h hK hK3 hKM hA0 hAN hKxcl
  have hKt : IsLThreeFour (barOf 3 K) := isLThreeFour_of_center_bot hK3 hcenter
  have hJK : JJ A K ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  obtain ⟨eJ, -⟩ := exists_barOf_equiv_of_cover (p := 3) (by norm_num) hJK hcov
  have hJt : IsLThreeFour (barOf 3 (JJ A K)) := isLThreeFour_congr eJ.symm hKt
  have hJcenter : Subgroup.center (barOf 3 (JJ A K)) = ⊥ := center_eq_bot_of_equiv eJ hcenter
  have hKxt : ∀ x ∈ FF A K, x ≠ 1 →
      IsLThreeFour (barOf 3 (Kx 3 (JJ A K) x) ⧸ Subgroup.center (barOf 3 (Kx 3 (JJ A K) x))) ∧
        Subgroup.center (barOf 3 (Kx 3 (JJ A K) x)) = ⊥ ∧
          IsLThreeFour (barOf 3 (Kx 3 (JJ A K) x)) := by
    intro x hx hx1
    obtain ⟨e, -⟩ := exists_barOf_equiv_of_cover (p := 3) (by norm_num)
      (Sec12b.le_kx (p := 3) x (JJ A K)) (hKxcl x hx hx1).2
    exact ⟨isLThreeFour_modCenter_congr e (isLThreeFour_modCenter_congr eJ.symm hK3),
      center_eq_bot_of_equiv e.symm hJcenter, isLThreeFour_congr e hJt⟩
  obtain ⟨hdecJ, hdisjJ, hAJ9, -⟩ := lemma124_print_i_of_inputs h122 h123 h117 h104ii h104iii h104iv hI7
    h hK hK3 hKM hA0 hAN hcenter
  have hII : ∀ x ∈ FF A K, x ≠ 1 →
      Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G) ∧
        barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤ := by
    intro x hx hx1
    obtain ⟨hcomp, hcovx⟩ := hKxcl x hx hx1
    obtain ⟨hmod, hcen, -⟩ := hKxt x hx hx1
    refine ⟨cent_le_normalizer_of_unique hcomp hmod hcen fun I hI hIt hIc => ?_, hcovx⟩
    exact hUniq h hK hK3 hKM hA0 hAN hcenter hcov hx hx1 hcomp hcovx hI hIt hIc
  obtain ⟨hcompa, hcovxa⟩ := hKxcl a haF ha1
  have huniqa : ∀ I : Subgroup G, GLAPComponent 3 (Cg a) I →
      IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)) → Subgroup.center (barOf 3 I) = ⊥ →
        I = Kx 3 (JJ A K) a :=
    fun I hI hIt hIc => hUniq h hK hK3 hKM hA0 hAN hcenter hcov haF ha1 hcompa hcovxa hI hIt hIc
  have hKa : K = Kx 3 (JJ A K) a := huniqa K hK hK3 hcenter
  have hTN : Tof 3 M a ≤ Subgroup.normalizer (K : Set G) :=
    (Sec12a.tof_le_cg M a).trans (cent_le_normalizer_of_unique hK hK3 hcenter
      fun I hI hIt hIc => (huniqa I hI hIt hIc).trans hKa.symm)
  have hFe : IsEkIn 3 2 A (FF A K) := ⟨hFA, hFel, by rw [hF9]; norm_num⟩
  have hIV := exists_unitary_J h h122iii hFe
    (fun x hx hx1 V hV1 hV2 => hVx h hK hK3 hKM hA0 hAN hcov hx hx1 hV1 hV2) hcov hJK
    (exists_unitary_cent_A h hdec hTN hu₀)
  exact ⟨⟨hdec, hdisj, hdecJ, hdisjJ, hAJ9, hFrank, hA4⟩, hII,
    ⟨hJt, fun x hx hx1 => (hKxt x hx hx1).2.2⟩, hIV, hKa⟩

end Main124

section Core125

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_decomp_of_perm {J W : Subgroup G}
    (hPW : ∀ g ∈ J, ∀ v ∈ W, ∃ v' ∈ W, ∃ g' ∈ J, g * v = v' * g') :
    ∀ x ∈ J ⊔ W, ∃ w ∈ W, ∃ j ∈ J, x = w * j := by
  let Q : Subgroup G :=
    { carrier := (W : Set G) * (J : Set G)
      mul_mem' := by
        intro a b ha hb
        obtain ⟨w₁, hw₁, j₁, hj₁, rfl⟩ := Set.mem_mul.1 ha
        obtain ⟨w₂, hw₂, j₂, hj₂, rfl⟩ := Set.mem_mul.1 hb
        obtain ⟨v', hv', g', hg', e⟩ := hPW j₁ hj₁ w₂ hw₂
        refine Set.mem_mul.2 ⟨w₁ * v', W.mul_mem hw₁ hv', g' * j₂, J.mul_mem hg' hj₂, ?_⟩
        calc w₁ * v' * (g' * j₂) = w₁ * (v' * g') * j₂ := by group
          _ = w₁ * (j₁ * w₂) * j₂ := by rw [← e]
          _ = w₁ * j₁ * (w₂ * j₂) := by group
      one_mem' := Set.mem_mul.2 ⟨1, W.one_mem, 1, J.one_mem, mul_one 1⟩
      inv_mem' := by
        intro a ha
        obtain ⟨w, hw, j, hj, rfl⟩ := Set.mem_mul.1 ha
        obtain ⟨v', hv', g', hg', e⟩ := hPW j⁻¹ (J.inv_mem hj) w⁻¹ (W.inv_mem hw)
        refine Set.mem_mul.2 ⟨v', hv', g', hg', ?_⟩
        calc v' * g' = j⁻¹ * w⁻¹ := e.symm
          _ = (w * j)⁻¹ := by group }
  have hle : J ⊔ W ≤ Q :=
    sup_le (fun j hj => Set.mem_mul.2 ⟨1, W.one_mem, j, hj, one_mul j⟩)
      (fun w hw => Set.mem_mul.2 ⟨w, hw, 1, J.one_mem, mul_one w⟩)
  intro x hx
  obtain ⟨w, hw, j, hj, e⟩ := Set.mem_mul.1 (hle hx)
  exact ⟨w, hw, j, hj, e.symm⟩

theorem perm_J_W {m : ℕ} {B M E A : Subgroup G} {K : Subgroup G} (h111 : Prop111Statement)
    {a : G} (h : Cex121 G m 3 B M E A a)
    (hII : ∀ x ∈ FF A K, x ≠ 1 → Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G) ∧
      barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤) :
    ∀ g ∈ JJ A K, ∀ v ∈ WW M A K, ∃ v' ∈ WW M A K, ∃ g' ∈ JJ A K, g * v = v' * g' := by
  have hFA : FF A K ≤ A := inf_le_right
  have hJC : JJ A K ≤ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hperm : ∀ x ∈ FF A K, x ≠ 1 → ((JJ A K : Subgroup G) : Set G) *
      ((M ⊓ Cg x : Subgroup G) : Set G) =
        ((M ⊓ Cg x : Subgroup G) : Set G) * ((JJ A K : Subgroup G) : Set G) := by
    intro x hxF hx1
    obtain ⟨hN, hcov⟩ := hII x hxF hx1
    have hO : GLAPPrimeCoreOf 3 (Cg x) ≤ M := h111 h.toSec11 (hFA hxF) hx1
    have hJx : JJ A K ≤ Subgroup.centralizer ({x} : Set G) :=
      hJC.trans (Sec12b.cent_le_cent_of_mem hxF)
    exact Sec12b.mul_eq_mul_of_cover (p := 3) (by norm_num) (Sec12b.le_kx x (JJ A K))
      (Sec12b.kx_le_cent hJx) hN hcov hO
  have hK : ∀ i, ∀ g ∈ JJ A K, ∀ k ∈ (⨆ (_ : i ∈ FF A K) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G),
      ∃ k' ∈ (⨆ (_ : i ∈ FF A K) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G), ∃ g' ∈ JJ A K,
        g * k = k' * g' := by
    intro i g hg k hk
    by_cases hi : i ∈ FF A K ∧ i ≠ 1
    · rw [iSup_pos hi.1, iSup_pos hi.2] at hk ⊢
      have hmem : g * k ∈ ((JJ A K : Subgroup G) : Set G) * ((M ⊓ Cg i : Subgroup G) : Set G) :=
        Set.mul_mem_mul hg hk
      rw [hperm i hi.1 hi.2] at hmem
      obtain ⟨c, hc, j, hj, e⟩ := Set.mem_mul.1 hmem
      exact ⟨c, hc, j, hj, e.symm⟩
    · have hbot : (⨆ (_ : i ∈ FF A K) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G) = ⊥ := by
        by_cases h1 : i ∈ FF A K
        · have h2 : ¬ i ≠ 1 := fun h2 => hi ⟨h1, h2⟩
          rw [iSup_pos h1, iSup_neg h2]
        · rw [iSup_neg h1]
      rw [hbot] at hk ⊢
      rw [Subgroup.mem_bot.1 hk]
      exact ⟨1, Subgroup.one_mem _, g, hg, by simp⟩
  exact fun g hg v hv => Sec12b.mul_mem_iSup_of_perm (JJ A K)
    (fun i => ⨆ (_ : i ∈ FF A K) (_ : i ≠ 1), M ⊓ Cg i) hK hv g hg

theorem kx_le_JW {m : ℕ} {B M E A : Subgroup G} {K : Subgroup G} (h111 : Prop111Statement)
    {a : G} (h : Cex121 G m 3 B M E A a) {x : G} (hx : x ∈ FF A K) (hx1 : x ≠ 1)
    (hN : Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G))
    (hcov : barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤) :
    Kx 3 (JJ A K) x ≤ JJ A K ⊔ WW M A K := by
  have hFA : FF A K ≤ A := inf_le_right
  have hJC : JJ A K ≤ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hJx : JJ A K ≤ Subgroup.centralizer ({x} : Set G) :=
    hJC.trans (Sec12b.cent_le_cent_of_mem hx)
  have hKxC : Kx 3 (JJ A K) x ≤ Cg x := Sec12b.kx_le_cent hJx
  have hn : ((Kx 3 (JJ A K) x).subgroupOf (Cg x)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKxC).2 hN
  have hOle : GLAPPrimeCoreOf 3 (Kx 3 (JJ A K) x) ≤ M :=
    (glaPPrimeCoreOf_le_of_normal (by norm_num) hKxC hn).trans (h111 h.toSec11 (hFA hx) hx1)
  intro k hk
  obtain ⟨j, hj, o, ho, rfl⟩ :=
    Sec12b.mem_mul_glaPPrimeCoreOf_of_barX (Sec12b.le_kx (p := 3) x (JJ A K)) hcov hk
  have hoK : o ∈ Kx 3 (JJ A K) x := (Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 _ ≤ _) ho
  have hMC : M ⊓ Cg x ≤ WW M A K :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 le_rfl))
  have hoW : o ∈ WW M A K := hMC ⟨hOle ho, hKxC hoK⟩
  exact Subgroup.mul_mem_sup hj hoW

theorem glaPPrimeCoreOf_JW_le {m : ℕ} {B M E A : Subgroup G} {K : Subgroup G}
    (h111 : Prop111Statement) {a : G} (h : Cex121 G m 3 B M E A a)
    (hdec : A = (A ⊓ JJ A K) ⊔ FF A K) (haF : a ∈ FF A K)
    (hII : ∀ x ∈ FF A K, x ≠ 1 → Cg x ≤ Subgroup.normalizer (Kx 3 (JJ A K) x : Set G) ∧
      barX 3 (Kx 3 (JJ A K) x) (JJ A K) = ⊤)
    (hrank2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A)) :
    GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have ha1 : a ≠ 1 := h.ha.2
  have haA : a ∈ A := h.ha.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hFA : FF A K ≤ A := inf_le_right
  have hFM : FF A K ≤ M := hFA.trans hAM
  have hFel : IsElemAbelian 3 (FF A K) := Lemma124.isElemAbelian_of_le hFA hAel
  have hJC : JJ A K ≤ Subgroup.centralizer ((FF A K : Subgroup G) : Set G) :=
    (Sec12b.layer_le 3 _).trans inf_le_right
  have hWM : WW M A K ≤ M := iSup_le fun x => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hFW : FF A K ≤ WW M A K := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      exact Subgroup.one_mem _
    · have hmem : f ∈ (⨆ (_ : f ∈ FF A K) (_ : f ≠ 1), M ⊓ Cg f : Subgroup G) := by
        rw [iSup_pos hf, iSup_pos hf1]
        refine ⟨hFM hf, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rfl
      exact le_iSup (fun i => ⨆ (_ : i ∈ FF A K) (_ : i ≠ 1), M ⊓ Cg i) f hmem
  have hFX : FF A K ≤ JJ A K ⊔ WW M A K := hFW.trans le_sup_right
  have hdecX := mem_sup_decomp_of_perm (perm_J_W h111 h hII)
  have hXF : ∀ x ∈ JJ A K ⊔ WW M A K, ∀ f ∈ FF A K, ⁅x, f⁆ ∈ WW M A K := by
    intro x hx f hf
    obtain ⟨w, hw, j, hj, rfl⟩ := hdecX x hx
    have hjf : j * f * j⁻¹ = f := by
      have := Subgroup.mem_centralizer_iff.1 (hJC hj) f hf
      calc j * f * j⁻¹ = (f * j) * j⁻¹ := by rw [this]
        _ = f := by group
    have hc : ⁅w * j, f⁆ = w * f * w⁻¹ * f⁻¹ := by
      rw [commutatorElement_def]
      calc w * j * f * (w * j)⁻¹ * f⁻¹ = w * (j * f * j⁻¹) * w⁻¹ * f⁻¹ := by group
        _ = w * f * w⁻¹ * f⁻¹ := by rw [hjf]
    rw [hc]
    exact (WW M A K).mul_mem ((WW M A K).mul_mem ((WW M A K).mul_mem hw (hFW hf))
      ((WW M A K).inv_mem hw)) ((WW M A K).inv_mem (hFW hf))
  have hX'le : GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) ≤ JJ A K ⊔ WW M A K :=
    Subgroup.map_subtype_le _
  have hX'cop : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) :=
    not_dvd_card_glaPPrimeCoreOf hp3 _
  have hXnorm : JJ A K ⊔ WW M A K ≤
      Subgroup.normalizer ((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 _
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 hp3 (FF A K) (GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K))
    (Lemma124.isPGroup_three_of_isElemAbelian hFel) hX'cop (hFX.trans hXnorm)
  have hcommW : ⁅GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K), FF A K⁆ ≤ WW M A K :=
    Subgroup.commutator_le.2 fun x hx f hf => hXF x (hX'le hx) f hf
  have hBJ : A ⊓ JJ A K ≤ JJ A K := inf_le_right
  have hBA : A ⊓ JJ A K ≤ A := inf_le_left
  have hBel : IsElemAbelian 3 (A ⊓ JJ A K) := Lemma124.isElemAbelian_of_le hBA hAel
  have hBX : A ⊓ JJ A K ≤ JJ A K ⊔ WW M A K := hBJ.trans le_sup_left
  have hYcop : ¬ 3 ∣ Nat.card ((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G) : Subgroup G) :=
    fun hd => hX'cop (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hBN : A ⊓ JJ A K ≤ Subgroup.normalizer (((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    intro b hb
    exact Prop121.normalizer_inf_mem (hXnorm (hBX hb))
      (mem_normalizer_centralizer_of_comm fun f hf =>
        CFSG.Open.IsElemAbelian.comm hAel (hFA hf) (hBA hb))
  have hfacY := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 hp3 (A ⊓ JJ A K) ((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G))
    (Lemma124.isPGroup_three_of_isElemAbelian hBel) hYcop hBN
  have hNA0 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M := by
    refine le_trans ?_ h.pair.1.1.2.clause_d
    exact le_sSup ⟨E ⊓ A, inf_le_left, hrank2, rfl⟩
  have hY0 : (GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((A ⊓ JJ A K : Subgroup G) : Set G) ≤ M := by
    intro y hy
    have hAy : A ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (le_of_eq hdec).trans (sup_le ?_ ?_)
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact (Subgroup.mem_centralizer_iff.1 hy.2 b hb).symm
      · intro f hf
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact (Subgroup.mem_centralizer_iff.1 hy.1.2 f hf).symm
    have hyA0 : y ∈ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.1 (hAy he.2) y (Set.mem_singleton y)).symm
    exact hNA0 (Subgroup.centralizer_le_normalizer _ hyA0)
  have hJa : JJ A K ≤ Cg a := hJC.trans (Sec12b.cent_le_cent_of_mem haF)
  have hKaC : Kx 3 (JJ A K) a ≤ Cg a := Sec12b.kx_le_cent hJa
  obtain ⟨hNa, hcova⟩ := hII a haF ha1
  have hnKa : ((Kx 3 (JJ A K) a).subgroupOf (Cg a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKaC).2 hNa
  have hOKa : GLAPPrimeCoreOf 3 (Kx 3 (JJ A K) a) ≤ M :=
    (glaPPrimeCoreOf_le_of_normal hp3 hKaC hnKa).trans (h111 h.toSec11 haA ha1)
  have hKaX : Kx 3 (JJ A K) a ≤ JJ A K ⊔ WW M A K := kx_le_JW h111 h haF ha1 hNa hcova
  have hcomm1 : ⁅(GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G), A ⊓ JJ A K⁆ ≤ M := by
    refine Subgroup.commutator_le.2 fun y hy b hb => ?_
    have hyX' : y ∈ GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) := hy.1
    have hyC : y ∈ Cg a := Sec12b.cent_le_cent_of_mem haF hy.2
    have hbKa : b ∈ Kx 3 (JJ A K) a := Sec12b.le_kx (p := 3) a (JJ A K) (hBJ hb)
    have hbN : b ∈ Subgroup.normalizer
        ((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) : Subgroup G) : Set G) := hXnorm (hBX hb)
    have hyN : y ∈ Subgroup.normalizer ((Kx 3 (JJ A K) a : Subgroup G) : Set G) := hNa hyC
    have h1 : ⁅y, b⁆ ∈ Kx 3 (JJ A K) a := by
      rw [commutatorElement_def]
      exact (Kx 3 (JJ A K) a).mul_mem ((Subgroup.mem_normalizer_iff.1 hyN b).1 hbKa)
        ((Kx 3 (JJ A K) a).inv_mem hbKa)
    have h2 : ⁅y, b⁆ ∈ GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hbN y⁻¹).1
        ((GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)).inv_mem hyX')
      have h4 := (GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)).mul_mem hyX' h3
      rw [commutatorElement_def]
      simpa [mul_assoc] using h4
    have hZ : Kx 3 (JJ A K) a ⊓ GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K) ≤
        GLAPPrimeCoreOf 3 (Kx 3 (JJ A K) a) := by
      refine sec11_le_glaPPrimeCoreOf inf_le_left ?_ ?_
      · intro k hk n hn
        have hkX := hKaX hk
        exact ⟨(Kx 3 (JJ A K) a).mul_mem ((Kx 3 (JJ A K) a).mul_mem hk hn.1)
          ((Kx 3 (JJ A K) a).inv_mem hk),
          (Subgroup.mem_normalizer_iff.1 (hXnorm hkX) n).1 hn.2⟩
      · exact (Nat.Prime.coprime_iff_not_dvd hp3).2
          (fun hd => hX'cop (hd.trans (Subgroup.card_dvd_of_le inf_le_right)))
    exact hOKa (hZ ⟨h1, h2⟩)
  have hYM : (GLAPPrimeCoreOf 3 (JJ A K ⊔ WW M A K)) ⊓
      Subgroup.centralizer ((FF A K : Subgroup G) : Set G) ≤ M := by
    refine hfacY.le.trans (sup_le hcomm1 hY0)
  exact hfac.le.trans (sup_le (hcommW.trans hWM) hYM)

theorem pCoreOf_JW_le {M F J W : Subgroup G} (hFM : F ≤ M) (hFel : IsElemAbelian 3 F)
    (hFcard : Nat.card F = 3 ^ 2) (hWdef : ∀ x ∈ F, x ≠ 1 → M ⊓ Cg x ≤ W) (hWM : W ≤ M)
    (hJW : W ≤ J ⊔ W) (hO3 : GLAPPrimeCoreOf 3 (J ⊔ W) ≤ M)
    (hS : pCoreOf 2 (M ⊓ (J ⊔ W)) ≤ GLAPPrimeCoreOf 3 M) :
    pCoreOf 2 (J ⊔ W) ≤ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3 hp3
    F (GLAPPrimeCoreOf 3 M) (fun member => Subtype.ext (by simpa using hFel.2 member.1 member.2))
    hFcard (not_dvd_card_glaPPrimeCoreOf hp3 M) (hFM.trans (le_normalizer_glaPPrimeCoreOf 3 M))
  have hOW : GLAPPrimeCoreOf 3 M ≤ W := by
    refine hgen.le.trans (iSup_le fun member => iSup_le fun hne => ?_)
    intro g hg
    have hne' : (member : G) ≠ 1 := fun h => hne (Subtype.ext h)
    exact hWdef member member.2 hne' ⟨(Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 M ≤ M) hg.1, hg.2⟩
  have hWMX : W ≤ M ⊓ (J ⊔ W) := le_inf hWM hJW
  have hS2 : IsPGroup 2 ↥(pCoreOf 2 (M ⊓ (J ⊔ W))) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hnormS : GLAPPrimeCoreOf 3 M ≤ Subgroup.normalizer ((pCoreOf 2 (M ⊓ (J ⊔ W)) : Subgroup G) : Set G) :=
    fun g hg => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M ⊓ (J ⊔ W)) (hWMX (hOW hg))
  have hS' : pCoreOf 2 (M ⊓ (J ⊔ W)) ≤ pCoreOf 2 (GLAPPrimeCoreOf 3 M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS hnormS hS2
  have hN₂M : pCoreOf 2 (GLAPPrimeCoreOf 3 M) ≤ M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.map_subtype_le _)
  have hMnorm : M ≤ Subgroup.normalizer ((pCoreOf 2 (GLAPPrimeCoreOf 3 M) : Subgroup G) : Set G) :=
    (le_normalizer_glaPPrimeCoreOf 3 M).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hN₂ : pCoreOf 2 (GLAPPrimeCoreOf 3 M) ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN₂M hMnorm
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hO2X : pCoreOf 2 (J ⊔ W) ≤ GLAPPrimeCoreOf 3 (J ⊔ W) := by
    refine sec11_le_glaPPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_ ?_
    · intro h hh n hn
      exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hh) n).1 hn
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊔ W))
      rw [hn]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp3 Nat.prime_two).2 (by norm_num))
  have hO2XS : pCoreOf 2 (J ⊔ W) ≤ pCoreOf 2 (M ⊓ (J ⊔ W)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (hO2X.trans hO3) (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact hO2XS.trans (hS'.trans hN₂)

theorem twoPrimeComp_of_glaPComponent {X Js : Subgroup G} (hJs : GLAPComponent 3 X Js)
    (hcore : GLAPPrimeCoreOf 3 Js ≤ pCoreOf 2 Js) :
    IsTwoPrimeComp X Js ∧ CFSG.pCore 2 ↥Js = GLAPPrimeCore 3 ↥Js := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hJX : Js ≤ X := hJs.1
  have hsn : IsSubnormal Js X := hJs.2.1
  have hcoreEq : CFSG.pCore 2 ↥Js = GLAPPrimeCore 3 ↥Js := by
    apply le_antisymm
    · have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥Js)) := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1
          (CFSG.pCore_isPGroup (p := 2) (G := ↥Js))
        rw [hn]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp3 Nat.prime_two).2 (by norm_num))
      unfold GLAPPrimeCore CFSG.pPrimeCore
      exact le_sSup ⟨inferInstance, hcop⟩
    · intro x hx
      have hxG : (x : G) ∈ GLAPPrimeCoreOf 3 Js := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hcore hxG)
      have : y = x := Subtype.ext hyx
      rwa [← this]
  let f : ↥Js →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hJX)
  have hrange : f.range = (Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hJX x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥Js := by
    apply le_antisymm
    ·
      have hT2 : IsPGroup 2 ↥f.ker := by
        intro t
        have ht : Subgroup.inclusion hJX t.1 ∈ CFSG.pCore 2 ↥X := by
          rw [← QuotientGroup.eq_one_iff]
          exact t.2
        have hPX : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
        obtain ⟨k, hk⟩ := hPX ⟨_, ht⟩
        have hk1 : (Subgroup.inclusion hJX t.1) ^ (2 ^ k) = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        have hk2 : t.1 ^ (2 ^ k) = 1 := by
          apply Subgroup.inclusion_injective hJX
          rw [map_pow, map_one]
          exact hk1
        exact ⟨k, Subtype.ext (by simpa using hk2)⟩
      exact le_sSup ⟨inferInstance, hT2⟩
    ·
      intro x hx
      have hsnN : IsSubnormal (pCoreOf 2 Js) X :=
        isSubnormal_trans' (Sec12a2.isSubnormal_of_normal
          (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)).2
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Js))) hsn
      have hle := Sec12a2.le_pCoreOf_of_isSubnormal hsnN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Js)
      have hxG : (x : G) ∈ pCoreOf 2 Js := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hle hxG)
      have hyx' : y = Subgroup.inclusion hJX x := Subtype.ext hyx
      show f x = 1
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rwa [← hyx']
  have hqs : CFSG.Open.IsQuasisimple (↥Js ⧸ CFSG.pCore 2 ↥Js) := by
    have h0 := l119_isQuasisimple_barOf (p := 3) hp3 hJs
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hcoreEq.symm) h0
  have hq' : CFSG.Open.IsQuasisimple
      ↥((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
    let e1 : (↥Js ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
    let e2 : ↥f.range ≃*
        ↥((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) :=
      MulEquiv.subgroupCongr hrange
    let e3 : ↥Js ⧸ CFSG.pCore 2 ↥Js ≃* ↥Js ⧸ f.ker :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((e3.trans e1).trans e2) hqs
  have hsn' : IsSubnormal ((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ⊤ := by
    have h1 := (glaPComponent_top hJs).2.1
    have h2 := isSubnormal_map' (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact ⟨⟨hJX, hsn, glaPComponent_perfect hJs, le_top, hsn', hq'⟩, hcoreEq⟩

end Core125


end Lemma1245

theorem lemma125_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    (h111 : Prop111Statement) (hS : Lemma1245.SClaim) (hJs : Lemma1245.JstarClaim) :
    Lemma125Statement := by
  intro G _ _ m p B M E A a h K hK hK3 hKM hu₀ hA0
  have h125i := lemma125_i_of_inputs h123 h124 h111 h hK hK3 hKM hu₀ hA0
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  intro F J W
  obtain ⟨⟨-, -, hdec, -, -, hFrank, -⟩, hII, ⟨hJt, -⟩, hIV⟩ := h124 h hK hK3 hKM hu₀ hA0
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have haF : a ∈ Lemma1245.FF A K := Lemma1245.mem_centBar_of_component h.ha.1 (Lemma124.comp_le_aux hK)
  have hFA : Lemma1245.FF A K ≤ A := inf_le_right
  have hFel : IsElemAbelian 3 (Lemma1245.FF A K) := Lemma124.isElemAbelian_of_le hFA hAel
  have hFcard : Nat.card (Lemma1245.FF A K) = 3 ^ 2 := by
    rw [Lemma124.card_eq_pow_pRank hFel]
    exact congrArg (3 ^ ·) hFrank
  have hO3 := Lemma1245.glaPPrimeCoreOf_JW_le h111 h hdec haF hII h.pair.1.2.2
  have hWM : Lemma1245.WW M A K ≤ M := iSup_le fun x => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hWdef : ∀ x ∈ Lemma1245.FF A K, x ≠ 1 → M ⊓ Cg x ≤ Lemma1245.WW M A K := fun x hx hx1 =>
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 le_rfl))
  refine ⟨h125i, Lemma1245.pCoreOf_JW_le (hFA.trans hAM) hFel hFcard hWdef hWM le_sup_right hO3
    (hS h hK hK3 hKM hu₀ hA0 hdec hFrank), ?_⟩
  obtain ⟨Js, hJsC, hJJs, hJst, hJscore⟩ := hJs h hK hK3 hKM hu₀ hA0 hII hJt hIV hFrank hO3
  obtain ⟨hTP, hcoreEq⟩ := Lemma1245.twoPrimeComp_of_glaPComponent hJsC hJscore
  exact ⟨Js, hTP, hJJs, Lemma1245.isLThreeFour_congr
    (QuotientGroup.quotientMulEquivOfEq hcoreEq.symm) hJst⟩

theorem lemma124_of_inputs
    (h122 : Lemma122_i_iiStatement) (h122iii : Lemma122_iiiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (hI7 : Input7_L34)
    (hNorm : Lemma1245.NormClaim) (hKx : Lemma1245.KxClaim) (hType : Lemma1245.TypeClaim)
    (hUniq : Lemma1245.UniqClaim) (hVx : Lemma1245.VxClaim) :
    Lemma124Statement := by
  intro G _ _ m p B M E A a h K hK hK3 hKM hu₀ hA0
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  obtain ⟨h1, h2, h3, h4, -⟩ := Lemma1245.lemma124_core_of_inputs h122 h122iii h123 h117 h104ii
    h104iii h104iv hI7 hNorm hKx hType hUniq hVx h hK hK3 hKM hu₀ hA0
  exact ⟨h1, h2, h3, h4⟩

theorem Lemma1245.printedKLeKx_of_inputs
    (h122 : Lemma122_i_iiStatement) (h122iii : Lemma122_iiiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (hI7 : Input7_L34)
    (hNorm : Lemma1245.NormClaim) (hKx : Lemma1245.KxClaim) (hType : Lemma1245.TypeClaim)
    (hUniq : Lemma1245.UniqClaim) (hVx : Lemma1245.VxClaim) :
    Prop121.PrintedKLeKx := by
  intro G _ _ m p B M E A a h K hK hK3 hKM hu₀ hA0
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  exact (Lemma1245.lemma124_core_of_inputs h122 h122iii h123 h117 h104ii h104iii h104iv hI7 hNorm hKx
    hType hUniq hVx h hK hK3 hKM hu₀ hA0).2.2.2.2.le

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

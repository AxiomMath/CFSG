module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

theorem ys03_catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {P : TauCeti.CFSGIndex → Prop} (h : catalogIs S P) : catalogIs S' P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem ys03_glaPPrimeCore_quot_eq_bot {p : ℕ} (hp : p.Prime) (X : Type) [Group X] [Finite X] :
    GLAPPrimeCore p (X ⧸ GLAPPrimeCore p X) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := glaPPrimeCore_map_of_surjective hp (QuotientGroup.mk' (GLAPPrimeCore p X))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact CFSG.pPrimeCore_coprime_card)
  rw [← h1]
  exact (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk'])

section PGroupFacts

variable {G : Type} [Group G] [Finite G]

theorem ys03_card_barX_of_isPGroup {p : ℕ} (hp : p.Prime) {C E : Subgroup G}
    (hE : IsPGroup p E) (hEC : E ≤ C) : Nat.card (barX p C E) = Nat.card E := by
  have hi := injective_barX_comp hp hE hEC
  have hrange : barX p C E = (⊤ : Subgroup ↥(E.subgroupOf C)).map
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype) := by
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  rw [hrange, Subgroup.card_map_of_injective hi, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv

theorem ys03_glaPPrimeCoreOf_sup_le {p : ℕ} (hp : p.Prime) {L B : Subgroup G}
    (hB : IsPGroup p B) (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    GLAPPrimeCoreOf p (L ⊔ B) ≤ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := L ⊔ B with hM
  have hLM : L ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  haveI hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMN
  set φ : ↥M →* ↥M ⧸ L.subgroupOf M := QuotientGroup.mk' (L.subgroupOf M) with hφ
  have hBp : IsPGroup p (B.subgroupOf M) := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm
  have hdecomp : ∀ m : ↥M, ∃ b : ↥M, b ∈ B.subgroupOf M ∧ φ m = φ b := by
    intro m
    have hm : (m : G) ∈ ((B : Set G) * (L : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B L hBN, sup_comm]
      exact m.2
    obtain ⟨b, hb, l, hl, hbl⟩ := Set.mem_mul.1 hm
    refine ⟨⟨b, hBM hb⟩, Subgroup.mem_subgroupOf.2 hb, ?_⟩
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show ((m : G))⁻¹ * b ∈ L
    rw [← hbl]
    have : (b * l)⁻¹ * b = l⁻¹ := by group
    rw [this]
    exact L.inv_mem hl
  have hQp : IsPGroup p (↥M ⧸ L.subgroupOf M) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, hbm⟩ := hdecomp m
    obtain ⟨k, hk⟩ := hBp ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have hk' : b ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hmb : (QuotientGroup.mk m : ↥M ⧸ L.subgroupOf M) = QuotientGroup.mk b := hbm
    rw [hmb, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have hN : ∀ n ∈ GLAPPrimeCore p ↥M, n ∈ L.subgroupOf M := by
    intro n hn
    obtain ⟨k, hk⟩ := hQp (φ n)
    have hcop0 : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥M)) :=
      CFSG.pPrimeCore_coprime_card
    have hcop : Nat.Coprime (p ^ k) (Nat.card (GLAPPrimeCore p ↥M)) :=
      Nat.Coprime.pow_left k hcop0
    have hn1 : n ^ Nat.card (GLAPPrimeCore p ↥M) = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ↥(GLAPPrimeCore p ↥M)) (x := ⟨n, hn⟩))
    have hφ1 : (φ n) ^ Nat.card (GLAPPrimeCore p ↥M) = 1 := by
      rw [← map_pow, hn1, map_one]
    have hg := (pow_gcd_eq_one (a := φ n)).2 ⟨hk, hφ1⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
    exact hg
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hx
  exact Subgroup.mem_subgroupOf.1 (hN n hn)

end PGroupFacts

section CoprimeAction

variable {G : Type} [Group G] [Finite G]

theorem ys03_exists_mul_mem_centralizer_of_coprime {p : ℕ} (hp : p.Prime) {M E : Subgroup G}
    (hEM : E ≤ M) (hE : IsPGroup p E) {l : G} (hl : l ∈ M)
    (hcomm : ∀ e ∈ E, ⁅l⁻¹, e⁆ ∈ GLAPPrimeCoreOf p M) :
    ∃ o ∈ GLAPPrimeCoreOf p M, l * o ∈ Subgroup.centralizer (E : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hOM : ∀ g ∈ M, ∀ o ∈ GLAPPrimeCoreOf p M, g * o * g⁻¹ ∈ GLAPPrimeCoreOf p M :=
    fun g hg o ho => (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p M hg) o).1 ho
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p M) := not_dvd_card_glaPPrimeCoreOf hp M
  letI act : MulAction ↥E ↥(GLAPPrimeCoreOf p M) :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), by
        have h1 : ⁅l⁻¹, (g : G)⁆ ∈ GLAPPrimeCoreOf p M := hcomm g g.2
        rw [commutatorElement_def, inv_inv] at h1
        have h2 := hOM (g : G) (hEM g.2) o o.2
        have h3 := (GLAPPrimeCoreOf p M).mul_mem h1 h2
        convert h3 using 1
        group⟩
      one_smul := fun o => Subtype.ext (by
        show l⁻¹ * (((1 : ↥E) : G) * (l * (o : G)) * (((1 : ↥E) : G))⁻¹) = o
        simp)
      mul_smul := fun g h o => Subtype.ext (by
        show l⁻¹ * (((g * h : ↥E) : G) * (l * (o : G)) * (((g * h : ↥E) : G))⁻¹) =
          l⁻¹ * (((g : ↥E) : G) * (l * (l⁻¹ * (((h : ↥E) : G) * (l * (o : G)) *
            ((h : ↥E) : G)⁻¹))) * ((g : ↥E) : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨o, ho⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card ↥(GLAPPrimeCoreOf p M) hOp
  refine ⟨o, o.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hfix : (⟨e, he⟩ : ↥E) • o = o := MulAction.mem_fixedPoints.1 ho ⟨e, he⟩
  have hval : l⁻¹ * (e * (l * (o : G)) * e⁻¹) = o := congrArg Subtype.val hfix
  calc e * (l * (o : G)) = l * (l⁻¹ * (e * (l * (o : G)) * e⁻¹)) * e := by group
    _ = l * (o : G) * e := by rw [hval]

end CoprimeAction

section QuotMap

variable {G : Type} [Group G] [Finite G]

abbrev ys03_qMap (p : ℕ) (M : Subgroup G) : ↥M →* PQuot p M :=
  QuotientGroup.mk' (GLAPPrimeCore p ↥M)

theorem ys03_qMap_eq_one_iff {p : ℕ} {M : Subgroup G} (x : ↥M) :
    ys03_qMap p M x = 1 ↔ x ∈ GLAPPrimeCore p ↥M :=
  QuotientGroup.eq_one_iff x

theorem ys03_mem_primeCoreOf_iff_qMap {p : ℕ} {M : Subgroup G} {x : G} (hx : x ∈ M) :
    x ∈ GLAPPrimeCoreOf p M ↔ ys03_qMap p M ⟨x, hx⟩ = 1 := by
  rw [ys03_qMap_eq_one_iff, GLAPPrimeCoreOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem ys03_comm_mem_primeCoreOf_iff {p : ℕ} (hp : p.Prime) {L M : Subgroup G}
    (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hsn : IsSubnormal L M)
    {l c : G} (hl : l ∈ L) (hc : c ∈ M) :
    ⁅l, c⁆ ∈ GLAPPrimeCoreOf p L ↔
      ys03_qMap p M ⟨l, hLM hl⟩ * ys03_qMap p M ⟨c, hc⟩ = ys03_qMap p M ⟨c, hc⟩ * ys03_qMap p M ⟨l, hLM hl⟩ := by
  have hlM : l ∈ M := hLM hl
  have hcomm : ⁅l, c⁆ ∈ L := by
    have h1 : ⁅l, c⁆ = l * (c * l⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h1]
    refine L.mul_mem hl ?_
    exact (Subgroup.mem_normalizer_iff.1 (hMN hc) l⁻¹).1 (L.inv_mem hl)
  have hMc : ⁅l, c⁆ ∈ M := hLM hcomm
  have hbr : ys03_qMap p M ⟨l, hlM⟩ * ys03_qMap p M ⟨c, hc⟩ = ys03_qMap p M ⟨c, hc⟩ * ys03_qMap p M ⟨l, hlM⟩ ↔
      ys03_qMap p M ⁅(⟨l, hlM⟩ : ↥M), ⟨c, hc⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have key : ys03_qMap p M ⁅(⟨l, hlM⟩ : ↥M), ⟨c, hc⟩⁆ = 1 ↔ ⁅l, c⁆ ∈ GLAPPrimeCoreOf p M := by
    rw [ys03_mem_primeCoreOf_iff_qMap hMc]
    rfl
  rw [hbr, key]
  constructor
  · intro h
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn h
  · intro h
    have h2 : ⁅l, c⁆ ∈ L ⊓ GLAPPrimeCoreOf p M := ⟨hcomm, h⟩
    rwa [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn] at h2

theorem ys03_centMod_iff_qMap {p : ℕ} (hp : p.Prime) {L M : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hsn : IsSubnormal L M) {b : G} (hb : b ∈ M) :
    CentMod p L b ↔
      ys03_qMap p M ⟨b, hb⟩ ∈ Subgroup.centralizer
        ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨_, hcomm⟩ _ hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh
    have hx' : (x : G) ∈ L := Subgroup.mem_subgroupOf.1 hx
    have hmem : ⁅(x : G), b⁆ ∈ GLAPPrimeCoreOf p L :=
      hcomm (Subgroup.commutator_mem_commutator hx' (Subgroup.mem_zpowers b))
    exact (ys03_comm_mem_primeCoreOf_iff hp hLM hMN hsn hx' hb).1 hmem
  · intro hC
    refine ⟨hMN hb, Subgroup.commutator_le.2 fun l hl c hc => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have hcM : b ^ n ∈ M := M.zpow_mem hb n
    have hCb : ys03_qMap p M ⟨b, hb⟩ ∈ Subgroup.centralizer
        ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) :=
      Subgroup.mem_centralizer_iff.2 hC
    have hpow : ys03_qMap p M ⟨b ^ n, hcM⟩ ∈ Subgroup.centralizer
        ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) := by
      have heq : ys03_qMap p M ⟨b ^ n, hcM⟩ = (ys03_qMap p M ⟨b, hb⟩) ^ n := by
        rw [← map_zpow]
        congr 1
      rw [heq]
      exact (Subgroup.centralizer _).zpow_mem hCb n
    have hlmem : ys03_qMap p M ⟨l, hLM hl⟩ ∈ (barX p M L : Subgroup (PQuot p M)) :=
      Subgroup.mem_map.2 ⟨⟨l, hLM hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hpow _ hlmem
    exact (ys03_comm_mem_primeCoreOf_iff hp hLM hMN hsn hl hcM).2 hcomm

end QuotMap

section ImageCentralizer

variable {G : Type} [Group G] [Finite G]

theorem ys03_barX_inf_centralizer_eq {p : ℕ} (hp : p.Prime) {L M E : Subgroup G}
    (hLM : L ≤ M) (hEM : E ≤ M) (hE : IsPGroup p E) (hOL : GLAPPrimeCoreOf p M ≤ L) :
    barX p M (L ⊓ Subgroup.centralizer (E : Set G)) =
      barX p M L ⊓ Subgroup.centralizer ((barX p M E : Subgroup (PQuot p M)) : Set (PQuot p M)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ L ⊓ Subgroup.centralizer (E : Set G) := Subgroup.mem_subgroupOf.1 hz
    have hzC : (z : G) ∈ Subgroup.centralizer (E : Set G) := (Subgroup.mem_inf.1 hz').2
    refine ⟨Subgroup.mem_map.2 ⟨z, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hz').1, rfl⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    have hcomm : (u : G) * (z : G) = (z : G) * (u : G) :=
      Subgroup.mem_centralizer_iff.1 hzC (u : G) (Subgroup.mem_subgroupOf.1 hu)
    rw [← map_mul, ← map_mul]
    exact congrArg (ys03_qMap p M) (Subtype.ext hcomm)
  · rintro ⟨hyL, hyC⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hyL
    have hz' : (z : G) ∈ L := Subgroup.mem_subgroupOf.1 hz
    have hzM : (z : G) ∈ M := hLM hz'
    have hMz : (z : G)⁻¹ ∈ M := M.inv_mem hzM
    have hcomm : ∀ e ∈ E, ⁅(z : G)⁻¹, e⁆ ∈ GLAPPrimeCoreOf p M := by
      intro e he
      have hem : e ∈ M := hEM he
      have heB : ys03_qMap p M ⟨e, hem⟩ ∈ (barX p M E : Subgroup (PQuot p M)) :=
        Subgroup.mem_map.2 ⟨⟨e, hem⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      have hc : ys03_qMap p M ⟨e, hem⟩ * ys03_qMap p M ⟨z, hzM⟩ = ys03_qMap p M ⟨z, hzM⟩ * ys03_qMap p M ⟨e, hem⟩ :=
        Subgroup.mem_centralizer_iff.1 hyC _ heB
      have hcM : ⁅(z : G)⁻¹, e⁆ ∈ M := by
        rw [commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem hMz hem) (M.inv_mem hMz)) (M.inv_mem hem)
      rw [ys03_mem_primeCoreOf_iff_qMap hcM]
      show ys03_qMap p M ⁅(⟨(z : G)⁻¹, hMz⟩ : ↥M), ⟨e, hem⟩⁆ = 1
      have hinv : (⟨(z : G)⁻¹, hMz⟩ : ↥M) = (⟨(z : G), hzM⟩ : ↥M)⁻¹ := rfl
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hinv, map_inv]
      calc (ys03_qMap p M ⟨z, hzM⟩)⁻¹ * ys03_qMap p M ⟨e, hem⟩
          = (ys03_qMap p M ⟨z, hzM⟩)⁻¹ * (ys03_qMap p M ⟨e, hem⟩ * ys03_qMap p M ⟨z, hzM⟩) *
              (ys03_qMap p M ⟨z, hzM⟩)⁻¹ := by group
        _ = (ys03_qMap p M ⟨z, hzM⟩)⁻¹ * (ys03_qMap p M ⟨z, hzM⟩ * ys03_qMap p M ⟨e, hem⟩) *
              (ys03_qMap p M ⟨z, hzM⟩)⁻¹ := by rw [hc]
        _ = ys03_qMap p M ⟨e, hem⟩ * (ys03_qMap p M ⟨z, hzM⟩)⁻¹ := by group
    obtain ⟨o, ho, hzo⟩ := ys03_exists_mul_mem_centralizer_of_coprime hp hEM hE hzM hcomm
    have hoM : o ∈ M := Subgroup.map_subtype_le _ ho
    have hzoL : (z : G) * o ∈ L := L.mul_mem hz' (hOL ho)
    have hzoM : (z : G) * o ∈ M := M.mul_mem hzM hoM
    refine Subgroup.mem_map.2 ⟨⟨(z : G) * o, hzoM⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hzoL, hzo⟩), ?_⟩
    have ho' : ys03_qMap p M ⟨o, hoM⟩ = 1 := (ys03_mem_primeCoreOf_iff_qMap hoM).1 ho
    show ys03_qMap p M ⟨(z : G) * o, hzoM⟩ = ys03_qMap p M ⟨(z : G), hzM⟩
    have hsplit : (⟨(z : G) * o, hzoM⟩ : ↥M) = ⟨(z : G), hzM⟩ * ⟨o, hoM⟩ := rfl
    rw [hsplit, map_mul, ho', mul_one]

end ImageCentralizer

variable {G : Type} [Group G] [Finite G]

theorem ys03_exists_component_ne_bot {p : ℕ} {X : Subgroup G}
    (h : GLAPLayer p X ≠ ⊥) : ∃ J : Subgroup G, GLAPComponent p X J ∧ J ≠ ⊥ := by
  by_contra hne
  have hall : ∀ J : Subgroup G, GLAPComponent p X J → J = ⊥ := fun J hJ =>
    by_contra fun hJ' => hne ⟨J, hJ, hJ'⟩
  apply h
  unfold GLAPLayer
  exact le_bot_iff.1 (sSup_le fun J hJ => le_bot_iff.2 (hall J hJ))

theorem ys03_coprime_inf_ker_qMap {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (A : Subgroup ↥M) : Nat.Coprime p (Nat.card ↥(A ⊓ (ys03_qMap p M).ker)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hker : (ys03_qMap p M).ker = GLAPPrimeCore p ↥M := QuotientGroup.ker_mk' _
  rw [hker]
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    CFSG.pPrimeCore_coprime_card

end CFSG.LocalAnalysis.GLTheoremA

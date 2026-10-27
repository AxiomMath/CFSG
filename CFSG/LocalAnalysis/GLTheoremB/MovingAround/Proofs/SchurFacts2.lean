module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNine

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors exists_lieModel
  center_torsion_le torsBound_le_of_five_le eq_psu_four_three_of_nine_le
  nonempty_mulEquiv_X₀_of_classical card_center_dvd_twelve)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six (thetaBar tBar Psub act A_le_Psub
  card_Psub card_range_thetaBar card_le_nine_of_fixed tBar_conj thetaBar_injective
  tBar_mem_normalizer thetaBar_comm commute_of_mem_range exists_lift_of_mem_range
  card_le_of_le_Psub)
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift (powOneSubgroup mem_powOneSubgroup)

section Cyclic

theorem isCyclic_center_of_card_roots_le {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hZ : IsPGroup p (Subgroup.center Y))
    (h : Nat.card {z : Subgroup.center Y // z ^ p = 1} ≤ p) : IsCyclic (Subgroup.center Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := hZ.exists_card_eq
  letI : CommGroup (Subgroup.center Y) :=
    { (inferInstance : Group (Subgroup.center Y)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  exact CFSG.GH74.Uniqueness.SU.SU1.isCyclic_of_card_roots_le hp e _ he h

theorem isCyclic_of_isPGroup_of_dvd_twelve {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Z : Type*}
    [Group Z] [Finite Z] (hZ : IsPGroup p Z) (h12 : Nat.card Z ∣ 12) : IsCyclic Z := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hk]
  have hk1 : k ≤ 1 := by
    by_contra hlt
    have h2 : p ^ 2 ∣ 12 := (pow_dvd_pow p (by omega)).trans (hk ▸ h12)
    have hle : p ^ 2 ≤ 12 := Nat.le_of_dvd (by norm_num) h2
    have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hp4 : p < 4 := by
      by_contra h4
      have h16 : 4 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    obtain rfl : p = 3 := by omega
    norm_num at h2
  calc p ^ k ∣ p ^ 1 := pow_dvd_pow p hk1
    _ = p := pow_one p

theorem false_of_cyclic_index {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    {hr : r.Prime} (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.cyclic r hr).Group) :
    False := by
  obtain ⟨a, b, hab⟩ := Prop1116Design.not_isCommutative_barQuot Y hq
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm (e a) (e b)

theorem torsBound_three_le_three {t : StatedLieTag} {n p f : ℕ}
    (h : ¬ 9 ≤ torsBound 3 t n p f) : torsBound 3 t n p f ≤ 3 := by
  revert h
  unfold torsBound tors
  split_ifs <;> omega

@[expose] def q3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

theorem valid_twistedA_three_q3 : (TauCeti.LieTypeIndex.twistedA 3 q3).Valid := by
  simp

@[expose] def u43Idx : TauCeti.ValidLieTypeIndex := ⟨.twistedA 3 q3, valid_twistedA_three_q3⟩

theorem nonempty_mulEquiv_u43Idx : Nonempty ((TauCeti.CFSGIndex.lie u43Idx).Group ≃* X₀) :=
  nonempty_mulEquiv_X₀_of_classical
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q3 valid_twistedA_three_q3
      (MulEquiv.refl _))

theorem isChevSimple_three_of_X₀ {S : Type} [Group S] (e : S ≃* X₀) : IsChevSimple 3 S := by
  obtain ⟨e₀⟩ := nonempty_mulEquiv_u43Idx
  have hc : onLie (fun d => d.characteristic = 3) (TauCeti.CFSGIndex.lie u43Idx) := by
    show TauCeti.LieTypeIndex.characteristic (.twistedA 3 q3) = 3
    exact TauCeti.LieTypeIndex.characteristic_twistedA 3 q3
  exact Or.inl ⟨.lie u43Idx, hc, ⟨e.trans e₀.symm⟩⟩

theorem isCyclic_center_lie (hGA : GriessAllModelsStatement) (hI196 : Lemma123.Input19_6_4)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore p Y = ⊥)
    (hnb : ¬ IsLocallyOTwoBalancedWrtP p 1 Y) (d : TauCeti.ValidLieTypeIndex)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsCyclic (Subgroup.center Y) := by
  have hZ := SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hO
  apply isCyclic_center_of_card_roots_le hp hZ
  obtain ⟨t, n, p', f, hm⟩ := exists_lieModel d
  have hle := center_torsion_le hGA hq e hm hp
  by_cases hp5 : 5 ≤ p
  · exact hle.trans (torsBound_le_of_five_le hp5 t n p' f)
  have hp3 : p = 3 := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  subst hp3
  by_cases h9 : 9 ≤ torsBound 3 t n p' f
  · exfalso
    obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_psu_four_three_of_nine_le h9
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
    · obtain ⟨e₀⟩ := nonempty_mulEquiv_X₀_of_classical hcl
      have hchev : IsChevSimple 3 (Y ⧸ Subgroup.center Y) := isChevSimple_three_of_X₀ (e.trans e₀)
      obtain ⟨A, hA, hnA⟩ : ∃ A : Subgroup (MulAut Y), CFSG.Open.IsElemAbelian 3 A ∧
          ¬ IsLocallyOTwoBalanced 3 1 A := by
        by_contra hcon
        push Not at hcon
        exact hnb hcon
      obtain ⟨-, hL, -⟩ := hI196 3 hp hp2 Y hq hO hchev A hA hnA
      have h1 := Prop1116Design.card_psl2_27_of_isL27 hL
      have h2 : Nat.card (Y ⧸ Subgroup.center Y) = 3265920 :=
        (Nat.card_congr (e.trans e₀).toEquiv).trans CFSG.LieType.Multipliers.U43.card_X₀
      omega
    · exact absurd h0 (by norm_num)
  · exact hle.trans (torsBound_three_le_three h9)

theorem isCyclic_center_of_index (hGA : GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hI196 : Lemma123.Input19_6_4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y]
    [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore p Y = ⊥)
    (hnb : ¬ IsLocallyOTwoBalancedWrtP p 1 Y) (i : TauCeti.CFSGIndex)
    (e : Y ⧸ Subgroup.center Y ≃* i.Group) : IsCyclic (Subgroup.center Y) := by
  have hZ := SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hO
  cases i with
  | cyclic r hr => exact (false_of_cyclic_index hq e).elim
  | alternating n hn =>
    have h := SchurFacts.card_center_dvd_of_isAltType hq ⟨e⟩
    refine isCyclic_of_isPGroup_of_dvd_twelve hp hp2 hZ (h.trans ?_)
    split_ifs <;> norm_num
  | lie d => exact isCyclic_center_lie hGA hI196 hp hp2 hq hO hnb d e
  | sporadic s =>
    exact isCyclic_of_isPGroup_of_dvd_twelve hp hp2 hZ (card_center_dvd_twelve hSpM hq s e)

theorem inputCyclicCentre_of_tables
    (hGA : GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hI196 : Lemma123.Input19_6_4) : Inputs123b.InputCyclicCentre := by
  intro p hp hp2 Y _ _ hq hO htype hnb
  rcases htype with ⟨q, -, hchev | hchev⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨i, -, ⟨e⟩⟩ := hchev
    exact isCyclic_center_of_index hGA hSpM hI196 hp hp2 hq hO hnb i e
  · obtain ⟨i, -, ⟨e⟩⟩ := hchev
    exact isCyclic_center_of_index hGA hSpM hI196 hp hp2 hq hO hnb i e
  · exact isCyclic_center_of_index hGA hSpM hI196 hp hp2 hq hO hnb (.alternating n hn) e
  · exact isCyclic_center_of_index hGA hSpM hI196 hp hp2 hq hO hnb (.sporadic s) e

end Cyclic

section U43

theorem isPGroup_zpowers_of_pow_eq_one {M : Type*} [Group M] {p k : ℕ} {φ : M}
    (h : φ ^ p ^ k = 1) : IsPGroup p (Subgroup.zpowers φ) := by
  rintro ⟨g, hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem sporadicMultipliers_tables (h : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
  ⟨fun s => by rw [h.1 s]; cases s <;> rfl, h.2⟩

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

variable {G : Type} [Group G]

theorem le_of_le_centerOf {K D : Subgroup G} (h : D ≤ centerOf K) : D ≤ K := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := h hx
  exact w.2

theorem subgroupOf_le_center {K D : Subgroup G} (h : D ≤ centerOf K) :
    D.subgroupOf K ≤ Subgroup.center ↥K := by
  intro x hx
  obtain ⟨w, hw, hwx⟩ := h (Subgroup.mem_subgroupOf.mp hx)
  have hwx' : w = x := Subtype.ext hwx
  exact hwx' ▸ hw

theorem u43_setup [Finite G] (hGA : GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hK : CFSG.Open.IsKGroup ↥K) {D : Subgroup G}
    (hDZ : D ≤ centerOf K) (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* X₀) ∧
      Nat.card {z : Subgroup.center ↥K // z ^ 3 = 1} = 9 ∧
      ∃ U : Subgroup ↥K, U ≤ Subgroup.center ↥K ∧ CFSG.Open.IsElemAbelian 3 U ∧
        Nat.card U = 3 ^ 2 := by
  have hUc : Nat.card (D.subgroupOf K) = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_of_le_centerOf hDZ)).toEquiv, hD9]
    norm_num
  have hUab := CFSG.Open.IsElemAbelian.subgroupOf hD K
  have hUZ := subgroupOf_le_center hDZ
  have h2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.center ↥K) :=
    CFSG.SectionRank.le_pRank (by norm_num) hUZ hUab hUc
  obtain ⟨-, he, h9, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.identify_of_two_le_pRank_center hGA hSpM hq
      hK Nat.prime_three (by norm_num) h2
  exact ⟨he, h9, D.subgroupOf K, hUZ, hUab, hUc⟩

theorem u43_one [Finite G] {K : Subgroup G}
    (h9 : Nat.card {z : Subgroup.center ↥K // z ^ 3 = 1} = 9) {D : Subgroup G}
    (hDZ : D ≤ centerOf K) (hD : CFSG.Open.IsElemAbelian 3 D) :
    Nat.card D ≤ 9 := by
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_le_torsion_center
    (CFSG.Open.IsElemAbelian.subgroupOf hD K) (subgroupOf_le_center hDZ)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_of_le_centerOf hDZ)).toEquiv, h9] at h

theorem u43_two [Finite G] (hGA : GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hK : CFSG.Open.IsKGroup ↥K)
    (hU : ∃ U : Subgroup ↥K, U ≤ Subgroup.center ↥K ∧ CFSG.Open.IsElemAbelian 3 U ∧
      Nat.card U = 3 ^ 2) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (hg3 : g ^ 3 = 1)
    {z : G} (hz : z ∈ centerOf K) : g * z = z * g := by
  set γ : ↥(Subgroup.normalizer (K : Set G)) := ⟨g, hg⟩ with hγ
  have hγ3 : γ ^ 3 = 1 := Subtype.ext (by simp [hγ, hg3])
  have hφ3 : (K.normalizerMonoidHom γ) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hγ3, map_one]
  obtain ⟨w, hw, rfl⟩ := hz
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.kernel11_6U_fixes_center hGA hSpM hq
    hK Nat.prime_three (by norm_num) hU (K.normalizerMonoidHom γ)
    (isPGroup_zpowers_of_pow_eq_one hφ3) w hw
  have h' : g * (w : G) * g⁻¹ = w := congrArg Subtype.val h
  calc g * (w : G) = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [h']

theorem u43_three [Finite G] (hkf : CFSG.AGLEmbedding.KFactCompCenterNine) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (he : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* X₀))
    {D : Subgroup G} (hDZ : D ≤ centerOf K) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) :
    ¬ ∀ z ∈ D, z ≠ 1 → ∀ w ∈ D, w ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (K : Set G), n⁻¹ * z * n = w := by
  intro htr
  obtain ⟨e⟩ := he
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hDK := le_of_le_centerOf hDZ
  set L : Subgroup ↥N := K.subgroupOf N with hL
  have eL : ↥L ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  have hLq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_mulEquiv eL.symm hq
  have hLn : L.Normal := Subgroup.normal_in_normalizer
  have hcomp : CFSG.Open.IsComponentOf L ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top (hLn.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤),
      hLq⟩
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) := by
    obtain ⟨e₀⟩ := nonempty_mulEquiv_u43Idx
    have hc : (Subgroup.center ↥L).map (eL : ↥L →* ↥K) = Subgroup.center ↥K :=
      Subgroup.map_center_eq eL
    exact ⟨.lie u43Idx, ⟨((QuotientGroup.congr _ _ eL hc).trans e).trans e₀.symm⟩⟩
  set E : Subgroup ↥N := D.subgroupOf N with hE
  have hEL : E ≤ L := fun x hx => hDK (Subgroup.mem_subgroupOf.mp hx)
  have hEc : ∀ x ∈ E, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    obtain ⟨w, hw, hwx⟩ := hDZ (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.mp hw ⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩
    have h2 : ((l : G) * w : G) = w * l := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hwx]
    exact h2.symm
  have hEab : CFSG.Open.IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.subgroupOf hD N
  have hE9 : Nat.card E = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDK.trans hKN)).toEquiv, hD9]
  obtain ⟨x, hx, hx1, y, hy, hy1, hne⟩ := hkf (↥N) L hcomp hLn hcat E hEL hEc hEab hE9
  obtain ⟨n, hn, hnxy⟩ := htr (x : G) (Subgroup.mem_subgroupOf.mp hx)
    (fun h => hx1 (Subtype.ext h)) (y : G) (Subgroup.mem_subgroupOf.mp hy)
    (fun h => hy1 (Subtype.ext h))
  apply hne ⟨n, hn⟩⁻¹
  apply Subtype.ext
  simpa using hnxy

end U43

section Sylow

open CFSG.LieType.Multipliers.U43 (F9)

theorem act_fixed_both : ∀ x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3,
    act ⟨1, 0⟩ x = x → act ⟨0, 1⟩ x = x → x.2 = (0, 0, 0) := by decide

theorem card_le_three_of_fixed {B : Subgroup X₀} (hB : B ≤ thetaBar.range)
    (h1 : ∀ b ∈ B, tBar (Multiplicative.ofAdd (⟨1, 0⟩ : F9)) * b *
      (tBar (Multiplicative.ofAdd (⟨1, 0⟩ : F9)))⁻¹ = b)
    (hi : ∀ b ∈ B, tBar (Multiplicative.ofAdd (⟨0, 1⟩ : F9)) * b *
      (tBar (Multiplicative.ofAdd (⟨0, 1⟩ : F9)))⁻¹ = b) :
    Nat.card B ≤ 3 := by
  choose g hg using fun b : B => (hB b.2 : (b : X₀) ∈ thetaBar.range)
  have hfix : ∀ s : F9, (∀ b ∈ B, tBar (Multiplicative.ofAdd s) * b *
      (tBar (Multiplicative.ofAdd s))⁻¹ = b) → ∀ b : B, act s (g b).toAdd = (g b).toAdd := by
    intro s hs b
    have h2 := tBar_conj (Multiplicative.ofAdd s) (g b)
    rw [hg b, hs b b.2] at h2
    have h3 := thetaBar_injective ((hg b).trans h2)
    exact (congrArg Multiplicative.toAdd h3).symm
  have hf : Function.Injective fun b : B => (g b).toAdd.1 := by
    intro b b' hbb'
    have e1 := act_fixed_both _ (hfix _ h1 b) (hfix _ hi b)
    have e2 := act_fixed_both _ (hfix _ h1 b') (hfix _ hi b')
    have h4 : (g b).toAdd = (g b').toAdd := Prod.ext hbb' (e1.trans e2.symm)
    apply Subtype.ext
    rw [← hg b, ← hg b', Multiplicative.toAdd.injective h4]
  calc Nat.card B ≤ Nat.card (ZMod 3) := Nat.card_le_card_of_injective _ hf
    _ = 3 := by simp

theorem eq_A_of_le_Psub {E : Subgroup X₀} (hE : CFSG.Open.IsElemAbelian 3 E) (hEP : E ≤ Psub)
    (hE81 : Nat.card E = 3 ^ 4) : E = thetaBar.range := by
  have := hE.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  by_cases hB : Nat.card (thetaBar.range ⊓ E : Subgroup X₀) ≤ 9
  · exfalso
    set A' : Subgroup ↥Psub := thetaBar.range.subgroupOf Psub with hA'
    have hA'n : A'.Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨a₀, ha₀, t, ht, hg⟩ := g.2
      have hconj : ((g * n * g⁻¹ : ↥Psub) : X₀) = a₀ * (t * n * t⁻¹) * a₀⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
        group
      rw [hconj]
      exact thetaBar.range.mul_mem (thetaBar.range.mul_mem ha₀ (tBar_mem_normalizer ht hn))
        (thetaBar.range.inv_mem ha₀)
    have hcardQ : Nat.card (↥Psub ⧸ A') = 9 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup A'
      rw [card_Psub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe A_le_Psub).toEquiv,
        card_range_thetaBar] at h
      have h' : Nat.card (↥Psub ⧸ A') * 3 ^ 4 = 9 * 3 ^ 4 := by rw [← h]; norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
    set E' : Subgroup ↥Psub := E.subgroupOf Psub with hE'
    set ρ : ↥E' →* ↥Psub ⧸ A' := (QuotientGroup.mk' A').comp E'.subtype with hρ
    have hker : Nat.card ρ.ker ≤ Nat.card (thetaBar.range ⊓ E : Subgroup X₀) := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨((x.1 : ↥Psub) : X₀), Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)),
            Subgroup.mem_subgroupOf.mp x.1.2⟩⟩ : ↥(thetaBar.range ⊓ E))) ?_
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    have hcardE' : Nat.card E' = 3 ^ 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE81]
    have hkr := Subgroup.card_ker_mul_card_range ρ
    rw [hcardE'] at hkr
    have hrange : ρ.range = ⊤ := by
      apply Subgroup.eq_top_of_le_card
      rw [hcardQ]
      by_contra hlt
      have h8 : Nat.card ρ.ker * Nat.card ρ.range ≤ 9 * 8 :=
        Nat.mul_le_mul (hker.trans hB) (by omega)
      omega
    have hlift : ∀ s : F9, ∃ e ∈ E, e⁻¹ * tBar (Multiplicative.ofAdd s) ∈ thetaBar.range := by
      intro s
      have hts : tBar (Multiplicative.ofAdd s) ∈ Psub :=
        ⟨1, thetaBar.range.one_mem, _, ⟨_, rfl⟩, (one_mul _).symm⟩
      obtain ⟨x, hx⟩ : QuotientGroup.mk' A' ⟨_, hts⟩ ∈ ρ.range := hrange ▸ Subgroup.mem_top _
      refine ⟨((x : ↥Psub) : X₀), Subgroup.mem_subgroupOf.mp x.2, ?_⟩
      have h := QuotientGroup.eq.mp hx
      exact Subgroup.mem_subgroupOf.mp h
    have hcent : ∀ s : F9, ∀ b ∈ (thetaBar.range ⊓ E : Subgroup X₀),
        tBar (Multiplicative.ofAdd s) * b * (tBar (Multiplicative.ofAdd s))⁻¹ = b := by
      intro s b hb
      obtain ⟨hbA, hbE⟩ := Subgroup.mem_inf.mp hb
      obtain ⟨e, he, hea⟩ := hlift s
      have h1 : (e⁻¹ * tBar (Multiplicative.ofAdd s)) * b =
          b * (e⁻¹ * tBar (Multiplicative.ofAdd s)) :=
        thetaBar_comm _ b hea hbA
      have h2 : e * b = b * e := hcomm e he b hbE
      calc tBar (Multiplicative.ofAdd s) * b * (tBar (Multiplicative.ofAdd s))⁻¹
          = e * ((e⁻¹ * tBar (Multiplicative.ofAdd s)) * b) *
              (e⁻¹ * tBar (Multiplicative.ofAdd s))⁻¹ * e⁻¹ := by group
        _ = e * (b * (e⁻¹ * tBar (Multiplicative.ofAdd s))) *
              (e⁻¹ * tBar (Multiplicative.ofAdd s))⁻¹ * e⁻¹ := by rw [h1]
        _ = e * b * e⁻¹ := by group
        _ = b * e * e⁻¹ := by rw [h2]
        _ = b := by group
    have h3 := card_le_three_of_fixed inf_le_left (hcent ⟨1, 0⟩) (hcent ⟨0, 1⟩)
    have hr9 : Nat.card ρ.range ≤ 9 := hcardQ ▸ Subgroup.card_le_card_group _
    have h27 : Nat.card ρ.ker * Nat.card ρ.range ≤ 3 * 9 := Nat.mul_le_mul (hker.trans h3) hr9
    omega
  · push Not at hB
    have hEA : E ≤ thetaBar.range := by
      intro e he
      obtain ⟨a, ha, t, ⟨s, rfl⟩, rfl⟩ := hEP he
      by_cases hs : s = 1
      · rw [hs, map_one, mul_one]
        exact ha
      · exfalso
        have hfix : ∀ b ∈ (thetaBar.range ⊓ E : Subgroup X₀), tBar s * b * (tBar s)⁻¹ = b := by
          rintro b ⟨hbA, hbE⟩
          have h1 := hcomm _ he b hbE
          have h2 : a * tBar s * b = b * (a * tBar s) := h1
          have h3 : tBar s * b * (tBar s)⁻¹ ∈ thetaBar.range :=
            tBar_mem_normalizer ⟨s, rfl⟩ hbA
          have h4 := thetaBar_comm a _ ha h3
          calc tBar s * b * (tBar s)⁻¹ = a * (tBar s * b * (tBar s)⁻¹) * a⁻¹ :=
                (mul_inv_eq_iff_eq_mul.mpr h4).symm
            _ = a * tBar s * b * (a * tBar s)⁻¹ := by group
            _ = b := mul_inv_eq_iff_eq_mul.mpr h2
        have := card_le_nine_of_fixed hs inf_le_left hfix
        omega
    exact Subgroup.eq_of_le_of_card_ge hEA (by rw [card_range_thetaBar, hE81])

@[expose] def HasUniqueEA {J : Type*} [Group J] (p k : ℕ) (S : Subgroup J) : Prop :=
  ∃ F : Subgroup J, F ≤ S ∧ CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ k ∧
    ∀ F' : Subgroup J, F' ≤ S → CFSG.Open.IsElemAbelian p F' → Nat.card F' = p ^ k → F' = F

theorem hasUniqueEA_map {J J' : Type*} [Group J] [Group J'] {p k : ℕ} (e : J ≃* J')
    {S₁ : Subgroup J} {S : Subgroup J'} (hS : S₁.map e.toMonoidHom = S)
    (h : HasUniqueEA p k S₁) : HasUniqueEA p k S := by
  obtain ⟨F, hFS, hFab, hFc, hu⟩ := h
  have hback : ∀ H : Subgroup J, (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    ext x
    simp
  have hfwd : ∀ H : Subgroup J', (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    ext x
    simp
  refine ⟨F.map e.toMonoidHom, hS ▸ Subgroup.map_mono hFS,
    CFSG.SectionRank.isElemAbelian_map hFab _, ?_, fun F' hF'S hF'ab hF'c => ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hFc]
  · have h1 : F'.map e.symm.toMonoidHom ≤ S₁ := by
      rw [← hback S₁, hS]
      exact Subgroup.map_mono hF'S
    have h2 := hu _ h1 (CFSG.SectionRank.isElemAbelian_map hF'ab _)
      (by rw [Subgroup.card_map_of_injective e.symm.injective, hF'c])
    rw [← hfwd F', h2]

theorem hasUniqueEA_of_subgroupOf {G : Type*} [Group G] {K S : Subgroup G} (hSK : S ≤ K)
    {p k : ℕ} (h : HasUniqueEA p k (S.subgroupOf K)) : HasUniqueEA p k S := by
  obtain ⟨F, hFS, hFab, hFc, hu⟩ := h
  refine ⟨F.map K.subtype, ?_, CFSG.SectionRank.isElemAbelian_map hFab _, ?_,
    fun F' hF'S hF'ab hF'c => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hFS hx)
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hFc]
  · have hF'K : F' ≤ K := hF'S.trans hSK
    have h1 : F'.subgroupOf K ≤ S.subgroupOf K := Subgroup.comap_mono hF'S
    have h2 := hu _ h1 (CFSG.Open.IsElemAbelian.subgroupOf hF'ab K)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'K).toEquiv, hF'c])
    rw [← h2, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hF'K]

theorem hasUniqueEA_of_map_eq_Psub {J : Type} [Group J] [Finite J] (ψ : J →* X₀)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center J)
    (h9 : Nat.card {z : Subgroup.center J // z ^ 3 = 1} = 9) (S : Sylow 3 J)
    (hS : (S : Subgroup J).map ψ = Psub) : HasUniqueEA 3 6 (S : Subgroup J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkerZ : ψ.ker ≤ Subgroup.center J := hker.le
  have hcomm : ∀ x ∈ thetaBar.range.comap ψ, ∀ y ∈ thetaBar.range.comap ψ, x * y = y * x :=
    fun x hx y hy => commute_of_mem_range hψ hkerZ hx hy
  set U := powOneSubgroup ψ thetaBar.range 3 hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (mem_powOneSubgroup.mp a.2).1 _
      (mem_powOneSubgroup.mp b.2).1)⟩⟩, fun x hx => (mem_powOneSubgroup.mp hx).2⟩
  set ρ : ↥U →* X₀ := ψ.comp U.subtype with hρ
  have hρr : ρ.range = thetaBar.range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_powOneSubgroup.mp x.2).1
    · intro ha
      obtain ⟨y, hy, hyp⟩ := exists_lift_of_mem_range hψ hkerZ ha
      exact ⟨⟨y, mem_powOneSubgroup.mpr ⟨hy ▸ ha, hyp⟩⟩, hy⟩
  have hmemZ : ∀ {y : J}, ψ y = 1 → y ∈ Subgroup.center J := fun {y} hy => by
    rw [← hker]
    exact hy
  have hmemK : ∀ {y : J}, y ∈ Subgroup.center J → ψ y = 1 := fun {y} hy => by
    rw [← hker] at hy
    exact hy
  have hρk : Nat.card ρ.ker = 9 := by
    rw [← h9]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨((x.1 : ↥U) : J), hmemZ (MonoidHom.mem_ker.mp x.2)⟩,
            Subtype.ext (mem_powOneSubgroup.mp x.1.2).2⟩
        invFun := fun z => ⟨⟨((z.1 : Subgroup.center J) : J), mem_powOneSubgroup.mpr
            ⟨by rw [hmemK z.1.2]; exact thetaBar.range.one_mem,
              congrArg Subtype.val z.2⟩⟩, MonoidHom.mem_ker.mpr (hmemK z.1.2)⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have hUc : Nat.card U = 3 ^ 6 := by
    rw [← Subgroup.card_ker_mul_card_range ρ, hρr, hρk, card_range_thetaBar]
    norm_num
  have hUS : U ≤ S := by
    intro x hx
    obtain ⟨hxA, hx3⟩ := mem_powOneSubgroup.mp hx
    have hxP : ψ x ∈ (S : Subgroup J).map ψ := hS ▸ A_le_Psub hxA
    obtain ⟨s, hs, hsx⟩ := hxP
    have hz : s⁻¹ * x ∈ Subgroup.center J := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨s, hs⟩
    have hsm : s ^ 3 ^ m = 1 := congrArg Subtype.val hm
    have hsA : s ∈ thetaBar.range.comap ψ := by
      rw [Subgroup.mem_comap, hsx]
      exact hxA
    have hcs : Commute s⁻¹ x := (show Commute s x from hcomm s hsA x hxA).inv_left
    have hzp : (s⁻¹ * x) ^ 3 ^ (m + 1) = 1 := by
      rw [hcs.mul_pow, pow_succ, pow_mul, pow_mul', inv_pow, hsm, hx3, inv_one, one_pow,
        one_pow, one_mul]
    haveI : (Subgroup.zpowers (s⁻¹ * x)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hz)
    have hle := (isPGroup_zpowers_of_pow_eq_one hzp).le_sylow_of_normal S
    have hzS : s⁻¹ * x ∈ (S : Subgroup J) := hle (Subgroup.mem_zpowers _)
    have hx' : x = s * (s⁻¹ * x) := by group
    rw [hx']
    exact (S : Subgroup J).mul_mem hs hzS
  refine ⟨U, hUS, hUab, hUc, fun F' hF'S hF' hF'c => ?_⟩
  set σ : ↥F' →* X₀ := ψ.comp F'.subtype with hσ
  have hσr : σ.range = F'.map ψ := by rw [hσ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hσk : Nat.card σ.ker ≤ 9 := by
    rw [← h9]
    refine Nat.card_le_card_of_injective (fun x => (⟨⟨((x.1 : ↥F') : J),
      hmemZ (MonoidHom.mem_ker.mp x.2)⟩, Subtype.ext (hF'.2 _ x.1.2)⟩ :
        {z : Subgroup.center J // z ^ 3 = 1})) ?_
    intro a b hab
    have h := congrArg (fun w : {z : Subgroup.center J // z ^ 3 = 1} => ((w.1 : J))) hab
    exact Subtype.ext (Subtype.ext h)
  have hmapP : F'.map ψ ≤ Psub := hS ▸ Subgroup.map_mono hF'S
  have hmapab := CFSG.SectionRank.isElemAbelian_map hF' ψ
  have hmap81 : Nat.card (F'.map ψ) = 3 ^ 4 := by
    have h1 := Subgroup.card_ker_mul_card_range σ
    rw [hσr, hF'c] at h1
    have h2 := card_le_of_le_Psub hmapab hmapP
    refine le_antisymm h2 ?_
    by_contra hlt
    have h3 : Nat.card σ.ker * Nat.card (F'.map ψ) ≤ 9 * 80 :=
      Nat.mul_le_mul hσk (by omega)
    omega
  have hmapA := eq_A_of_le_Psub hmapab hmapP hmap81
  have hF'U : F' ≤ U := fun x hx =>
    mem_powOneSubgroup.mpr ⟨hmapA ▸ Subgroup.mem_map_of_mem ψ hx, hF'.2 x hx⟩
  exact Subgroup.eq_of_le_of_card_ge hF'U (by rw [hUc, hF'c])

theorem factorization_card_X₀ : (Nat.card X₀).factorization 3 = 6 := by
  rw [CFSG.LieType.Multipliers.U43.card_X₀]
  have h6 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).1
    (by norm_num : 3 ^ 6 ∣ 3265920)
  have h7 : ¬ 7 ≤ (3265920 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).2 h)
      (by norm_num)
  omega

theorem hasUniqueEA_sylow {J : Type} [Group J] [Finite J] (ψ : J →* X₀)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center J)
    (h9 : Nat.card {z : Subgroup.center J // z ^ 3 = 1} = 9) (S : Sylow 3 J) :
    HasUniqueEA 3 6 (S : Subgroup J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P0 : Sylow 3 X₀ := Sylow.ofCard Psub (by rw [card_Psub, factorization_card_X₀])
  obtain ⟨S₁, hS₁⟩ := Sylow.mapSurjective_surjective hψ 3 P0
  have hS₁' : (S₁ : Subgroup J).map ψ = Psub :=
    congrArg (fun Q : Sylow 3 X₀ => (Q : Subgroup X₀)) hS₁
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J S₁ S
  have hmap : (S₁ : Subgroup J).map (MulAut.conj c).toMonoidHom = (S : Subgroup J) := by
    rw [← hc]
    rfl
  exact hasUniqueEA_map (MulAut.conj c) hmap (hasUniqueEA_of_map_eq_Psub ψ hψ hker h9 S₁ hS₁')

theorem u43_four {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (he : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* X₀))
    (h9 : Nat.card {z : Subgroup.center ↥K // z ^ 3 = 1} = 9) {S : Subgroup G}
    (hS : IsSylowIn 3 K S) : HasUniqueEA 3 6 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := he
  set ψ : ↥K →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hψdef
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center ↥K := by
    ext x
    simp [hψdef, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hS' := Claims11x.isSylowIn_top_subgroupOf hS
  let P : Sylow 3 ↥K :=
    { toSubgroup := S.subgroupOf K, isPGroup' := hS'.2.1,
      is_maximal' := fun {Q} hQ hle => hS'.2.2 Q le_top hQ hle }
  exact hasUniqueEA_of_subgroupOf hS.1 (hasUniqueEA_sylow ψ hψ hker h9 P)

theorem inputU43_of_tables (hGA : GriessAllModelsStatement)
    (hSp : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : Claims1113.InputU43 := by
  intro G _ _ K hq hK hD
  obtain ⟨D, hDZ, hDab, hD9⟩ := hD
  have hSpM := sporadicMultipliers_tables hSp
  obtain ⟨he, h9, hU⟩ := u43_setup hGA hSpM hq hK hDZ hDab hD9
  refine ⟨fun D' hD'Z hD' => u43_one h9 hD'Z hD',
    fun g hg hg3 z hz => u43_two hGA hSpM hq hK hU hg hg3 hz,
    fun D' hD'Z hD' hD'9 => u43_three (CFSG.AGLEmbedding.kFactCompCenterNine_of hGA hSp) hq he
      hD'Z hD' hD'9,
    fun S hS => u43_four he h9 hS⟩

end Sylow

section Holds

theorem inputCyclicCentre_holds : Inputs123b.InputCyclicCentre :=
  inputCyclicCentre_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (sporadicMultipliers_tables
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    Inputs196.input19_6_4_holds

theorem inputU43_holds : Claims1113.InputU43 :=
  inputU43_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts2

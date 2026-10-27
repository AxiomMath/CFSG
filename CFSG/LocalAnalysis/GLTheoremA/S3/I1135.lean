module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Lift
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Alpha
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Y

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem i1135_lift_rank {G : Type} [Group G] [Finite G] (X : Subgroup G)
    (E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) (hE : IsElemAbelian 3 E) {j : ℕ}
    (hj : Nat.card E = 3 ^ j) (T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :
    j ≤ GLATwoLocalRank 3 ↥X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : barX 3 X X = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) z
    exact ⟨x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  have hbot : barX 3 X (⊥ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨x, hx, rfl⟩
    have hx1 : (x : G) = 1 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 hx)
    have hx1' : x = 1 := Subtype.ext hx1
    rw [Subgroup.mem_bot, hx1', map_one]
  have hEX : E ≤ barX 3 X X := by
    rw [htop]
    exact le_top
  have hbot3 : IsPGroup 3 (⊥ : Subgroup G) := (CFSG.Open.isElemAbelian_bot 3).isPGroup
  obtain ⟨W, hWX, -, hW3, -, hWE⟩ := I113.exists_W (D := ⊥) (N := X) bot_le le_rfl hbot3 bot_le E hEX
    (fun e he => hE.2 e he) (fun z hz e _ => by
      rw [hbot, Subgroup.mem_bot] at hz
      rw [hz, one_mul, mul_one])
  have hW' : ∀ x : G, ∀ hx : x ∈ X, x ∈ W →
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨x, hx⟩ : ↥X) ∈ E := by
    intro x hxX hx
    rw [← hWE]
    exact ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hcomm : ∀ x y : G, x ∈ W → y ∈ W → x * y = y * x := by
    intro x y hx hy
    have hxX : x ∈ X := hWX hx
    have hyX : y ∈ X := hWX hy
    have hc := isElemAbelian_commute hE (hW' x hxX hx) (hW' y hyX hy)
    have hxy : (⟨x * y, X.mul_mem hxX hyX⟩ : ↥X) = ⟨y * x, X.mul_mem hyX hxX⟩ := by
      apply I113.eq_of_mk'_eq hW3 hWX (W.mul_mem hx hy) (W.mul_mem hy hx)
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨x, hxX⟩ * ⟨y, hyX⟩ : ↥X) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨y, hyX⟩ * ⟨x, hxX⟩ : ↥X)
      rw [map_mul, map_mul, hc]
    exact congrArg Subtype.val hxy
  have hexp : ∀ x : G, x ∈ W → x ^ 3 = 1 := by
    intro x hx
    have hxX : x ∈ X := hWX hx
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨x, hxX⟩ : ↥X) ^ 3 = 1 :=
      hE.2 _ (hW' x hxX hx)
    have h2 : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := by
      apply I113.eq_of_mk'_eq hW3 hWX (W.pow_mem hx 3) (W.one_mem)
      rw [map_pow, h1, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hWel : IsElemAbelian 3 W :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a b a.2 b.2)⟩⟩, fun x hx => hexp x hx⟩
  have hWcard : Nat.card W = 3 ^ j := by
    rw [← card_barX_of_isPGroup Nat.prime_three hW3 hWX, hWE, hj]
  have hW3' : IsPGroup 3 (W.subgroupOf X) := hW3.of_equiv (Subgroup.subgroupOfEquivOfLe hWX).symm
  have hAT : Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (W.subgroupOf X) ≤
      Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [show Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (W.subgroupOf X) =
      barX 3 X W from rfl, hWE]
    exact hET
  obtain ⟨S, hS, hS2, hWS⟩ := I113.exists_two_abstract (GLAPPrimeCore 3 ↥X)
    (I113.not_dvd_card_glaPPrimeCore X) hW3' T hT hT2 hAT
  have hWsub : IsElemAbelian 3 (W.subgroupOf X) := isElemAbelian_subgroupOf X hWel
  have hWsubcard : Nat.card (W.subgroupOf X) = 3 ^ j := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv, hWcard]
  have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hWS hWsub hWsubcard
  have hS2' : IsTwoLocal (Subgroup.normalizer (S : Set ↥X)) := by
    unfold IsTwoLocal
    exact ⟨S, hS, hS2, rfl⟩
  have h2 := pRank_le_glaTwoLocalRank_of_isTwoLocal Nat.prime_three hS2'
  exact h1.trans h2

private theorem i1135_qcore {G : Type} [Group G] [Finite G] {X K B' : Subgroup G}
    (hK : GLAPComponent 3 X K) (hB'X : B' ≤ X) (hB' : IsElemAbelian 3 B')
    {b : G} (hbB : b ∈ B') (hbK : b ∉ Subgroup.normalizer (K : Set G))
    (hidx : (Subgroup.normalizer (K : Set G)).relIndex B' = 3)
    (haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 K))) ≤ 2)
    (x0 : barOf 3 K) (hx0o : orderOf x0 = 3) (hx0c : x0 ∉ Subgroup.center (barOf 3 K))
    (T0 : Subgroup (barOf 3 K)) (hT0 : T0 ≠ ⊥) (hT02 : IsPGroup 2 T0)
    (hx0T : x0 ∈ Subgroup.normalizer (T0 : Set (barOf 3 K))) :
    ∃ E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsElemAbelian 3 E ∧
      Nat.card B' ≤ Nat.card E ∧ ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        E ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbX : b ∈ X := hB'X hbB
  set e : barOf 3 K ≃* ↥(barX 3 X K) := quotEquivBarX Nat.prime_three hK.1 hK.2.1 with he
  have hH9 : ∀ E : Subgroup (MulAut ↥(barX 3 X K)), IsElemAbelian 3 E → Nat.card E ≤ 9 :=
    I113.card_le_nine_of_pRank (by rw [← i112f_pRank_mulAut_of_mulEquiv e]; exact haut)
  set M : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := barX 3 X K with hMdef
  set Bq : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := barX 3 X B' with hBqdef
  set c : ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩ with hcdef
  have hTr : I113.Triple3 Bq M c :=
    { elem := isElemAbelian_barX hB'
      comp := hK.2.2.1
      mem := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.2 hbB, rfl⟩
      not_mem := fun h => hbK (by
        have h2 : (⟨b, hbX⟩ : ↥X) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf X := by
          rw [← i112f_comap_normalizer_barX hK]
          exact h
        exact Subgroup.mem_subgroupOf.1 h2)
      index := (i112f_relIndex_barX hK hB'X).trans hidx }
  set φ : barOf 3 K →* (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (barX 3 X K).subtype.comp e.toMonoidHom with hφdef
  have hφi : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφM : ∀ t : barOf 3 K, φ t ∈ M := fun t => (e t).2
  obtain ⟨s0, hs0⟩ : ∃ s : barOf 3 K, x0 * s ≠ s * x0 := by
    by_contra hcon
    push Not at hcon
    exact hx0c (Subgroup.mem_center_iff.2 fun s => (hcon s).symm)
  have hy1 : φ x0 ∈ M := hφM x0
  have ho1 : orderOf (φ x0) = 3 := by rw [orderOf_injective φ hφi x0, hx0o]
  have hnc1 : ∃ m ∈ M, φ x0 * m ≠ m * φ x0 :=
    ⟨φ s0, hφM s0, fun h => hs0 (hφi (by simpa [map_mul] using h))⟩
  have hT1ne : T0.map φ ≠ ⊥ := fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective _ hφi).1 h)
  have hT1M : T0.map φ ≤ M := by
    rintro _ ⟨t, -, rfl⟩
    exact hφM t
  have hT12 : IsPGroup 2 (T0.map φ) := hT02.map φ
  have hx1T : φ x0 ∈ Subgroup.normalizer ((T0.map φ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    Subgroup.le_normalizer_map φ ⟨x0, hx0T, rfl⟩
  obtain ⟨hYel, hYcard, hYK, hYB0⟩ := hTr.Y_spec hy1 ho1 hnc1
  have hnorm : ∀ (S L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) (f : ↥X ⧸ GLAPPrimeCore 3 ↥X),
      S ≤ L → (∀ l ∈ L, f * l = l * f) → f ∈ Subgroup.normalizer (S : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    fun S L f hSL hf => t113_mem_normalizer_of_commute fun j hj => hf j (hSL hj)
  have hB0M : ∀ z ∈ t113B0 Bq M, ∀ l ∈ M, z * l = l * z := fun z hz l hl =>
    (hTr.B0_comm_K hz l (hTr.L_le_K hl)).symm
  have hB0N : t113B0 Bq M ≤
      Subgroup.normalizer ((T0.map φ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := fun z hz => hnorm _ _ _ hT1M (hB0M z hz)
  have hYN : t113Y c (φ x0) ≤ Subgroup.normalizer ((T0.map φ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    have h1 : c⁻¹ * φ x0 * c ∈ Subgroup.normalizer ((T0.map φ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
      hnorm _ _ _ hT1M fun l hl => (hTr.comm01 l hl _ (hTr.conj1_mem hy1)).symm
    have h2 : (c ^ 2)⁻¹ * φ x0 * c ^ 2 ∈ Subgroup.normalizer ((T0.map φ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
      hnorm _ _ _ hT1M fun l hl => (hTr.comm02 l hl _ (hTr.conj2_mem hy1)).symm
    unfold t113Y
    exact sup_le (sup_le (Subgroup.zpowers_le.2 hx1T) (Subgroup.zpowers_le.2 h1))
      (Subgroup.zpowers_le.2 h2)
  have hcomm : ∀ z ∈ t113B0 Bq M, ∀ r ∈ t113Y c (φ x0), z * r = r * z :=
    fun z hz r hr => (hTr.B0_comm_K hz r (hYK hr)).symm
  have hE' : IsElemAbelian 3 (t113B0 Bq M ⊔ t113Y c (φ x0)) :=
    I1132.isElemAbelian_sup_of_commute hTr.B0_elem hYel hcomm
  have hinf : t113B0 Bq M ⊓ t113Y c (φ x0) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.2 (hYB0 z hz.2 hz.1)
  have hYB₀ : t113Y c (φ x0) ≤ Subgroup.normalizer (t113B0 Bq M : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    fun r hr => t113_mem_normalizer_of_commute fun l hl => (hcomm l hl r hr).symm
  have hcardE : Nat.card ↥(t113B0 Bq M ⊔ t113Y c (φ x0)) =
      Nat.card ↥(t113B0 Bq M) * 27 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hYB₀
    rw [hinf, Subgroup.card_bot, mul_one, hYcard] at h
    exact h
  have hBcard : Nat.card ↥Bq = Nat.card ↥B' :=
    card_barX_of_isPGroup Nat.prime_three (CFSG.Open.IsElemAbelian.isPGroup hB') hB'X
  have hBq_le : Nat.card ↥Bq ≤ Nat.card ↥(t113B0 Bq M) * 27 := by
    have hH := hH9 _ hTr.H_elem
    rw [hTr.card_B]
    calc 3 * Nat.card ↥(t113H Bq M) * Nat.card ↥(t113B0 Bq M)
        ≤ 3 * 9 * Nat.card ↥(t113B0 Bq M) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH)
      _ = Nat.card ↥(t113B0 Bq M) * 27 := by ring
  refine ⟨t113B0 Bq M ⊔ t113Y c (φ x0), hE', ?_, T0.map φ, hT1ne, hT12,
    sup_le hB0N hYN⟩
  rw [hcardE, ← hBcard]
  exact hBq_le

private theorem i1135_core {G : Type} [Group G] [Finite G] {B K : Subgroup G} {y : G} {k : ℕ}
    (hyB : y ∈ B) (hBel : IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ k)
    (hrank : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ k)
    (hK : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) K)
    (hnK : ¬ B ≤ Subgroup.normalizer (K : Set G))
    (hfull : ∀ B' : Subgroup G, IsElemAbelian 3 B' → B' ≤ Subgroup.centralizer ({y} : Set G) →
      GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ CFSG.Open.pRank 3 B' →
      ¬ B' ≤ Subgroup.normalizer (K : Set G) →
      (Subgroup.normalizer (K : Set G)).relIndex B' = 3)
    (haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 K))) ≤ 2)
    (x0 : barOf 3 K) (hx0o : orderOf x0 = 3) (hx0c : x0 ∉ Subgroup.center (barOf 3 K))
    (T0 : Subgroup (barOf 3 K)) (hT0 : T0 ≠ ⊥) (hT02 : IsPGroup 2 T0)
    (hx0T : x0 ∈ Subgroup.normalizer (T0 : Set (barOf 3 K)))
    {g : G} (hg : g ∈ Subgroup.centralizer (B : Set G)) (hgo : orderOf g = 3) (hgB : g ∉ B) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := Subgroup.centralizer ({y} : Set G) with hXdef
  have hBX : B ≤ X := le_centralizer_of_mem hBel hyB
  have hgX : g ∈ X := by
    rw [hXdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.1 hg _ hyB)
  have hcommB : ∀ b ∈ B, Commute b g := fun b hb => Subgroup.mem_centralizer_iff.1 hg b hb
  set Z : Subgroup G := Subgroup.zpowers g with hZdef
  have hZcard : Nat.card Z = 3 := by rw [hZdef, Nat.card_zpowers, hgo]
  have hZel : IsElemAbelian 3 Z :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hgo]; exact pow_orderOf_eq_one g)
  have hZN : Z ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.2 (t113_mem_normalizer_of_commute fun j hj => (hcommB j hj).symm.eq)
  have hBZ : B ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(B ⊓ Z) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : B ⊓ Z = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
      have hgmem : g ∈ B ⊓ Z := by
        rw [heq]
        exact Subgroup.mem_zpowers g
      exact hgB hgmem.1
  have hBs_el : IsElemAbelian 3 (B ⊔ Z) := by
    refine I1132.isElemAbelian_sup_of_commute hBel hZel fun p hp r hr => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact ((hcommB p hp).zpow_right n).eq
  have hBs_card : Nat.card ↥(B ⊔ Z) = 3 ^ (k + 1) := by
    have h := card_sup_mul_card_inf_of_le_normalizer hZN
    rw [hBZ, Subgroup.card_bot, mul_one, hBcard, hZcard] at h
    rw [h, pow_succ]
  have hBsX : B ⊔ Z ≤ X := sup_le hBX (Subgroup.zpowers_le.2 hgX)
  have hBs_rank : k + 1 ≤ CFSG.Open.pRank 3 (B ⊔ Z) :=
    CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hBs_el hBs_card
  have hBsnK : ¬ (B ⊔ Z) ≤ Subgroup.normalizer (K : Set G) := fun h => hnK (le_trans le_sup_left h)
  have hidx := hfull (B ⊔ Z) hBs_el hBsX (hrank.trans ((Nat.le_succ k).trans hBs_rank)) hBsnK
  obtain ⟨b, hbB, hbK⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnK fun b hb => hcon b hb
  obtain ⟨E, hE, hcardE, T, hT, hT2, hET⟩ :=
    i1135_qcore hK hBsX hBs_el ((le_sup_left : B ≤ B ⊔ Z) hbB) hbK hidx haut x0 hx0o hx0c T0 hT0 hT02 hx0T
  obtain ⟨j, hj⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have hk : k + 1 ≤ j := by
    have h1 : 3 ^ (k + 1) ≤ 3 ^ j := by
      rw [← hj, ← hBs_card]
      exact hcardE
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hlift := i1135_lift_rank X E hE hj T hT hT2 hET
  omega


theorem i1135At_holds
    {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hE : KDExcChev3) : I1135At G p := by
  unfold I1135At
  intro _ _ B y K _ hB hy hK hnK hchev
  obtain ⟨hp3, hZ, hcat⟩ := i1131At_holds hsimple hna hKP hp hp2 B y K hB hy hK hnK
  subst hp3
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  obtain ⟨i, ⟨h6, rfl⟩, ⟨f⟩⟩ := hE (PSimple 3 K) hcat hchev
  have hH6 : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatSix (barOf 3 K) := by
    unfold CFSG.HardMathSupport.Solomon.LocalBalance.IsHatSix
    exact ⟨hq.1, hZ, ⟨f⟩⟩
  obtain ⟨x0, hx0o, hx0c, T0, hT0, hT02, hx0T⟩ :=
    kd2028_holds (barOf 3 K) hq (Or.inl hH6)
  have hBX : B ≤ Subgroup.centralizer ({y} : Set G) := le_centralizer_of_mem hB.1 hy.1
  have hr : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ CFSG.Open.pRank 3 B :=
    glaTwoLocalRank_le_pRank_of_isBmax Nat.prime_three hB _
  have hrankEq := (glaIsBmax_subgroupOf_centralizer Nat.prime_three hB hy).1
  obtain ⟨-, -, -, haut, -, -⟩ := i112c_full CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
    tables112Types_holds hsimple hKP Nat.prime_three (by norm_num) hB.1 hBX hr hK hnK
  have hfull : ∀ B' : Subgroup G, IsElemAbelian 3 B' → B' ≤ Subgroup.centralizer ({y} : Set G) →
      GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ CFSG.Open.pRank 3 B' →
      ¬ B' ≤ Subgroup.normalizer (K : Set G) →
      (Subgroup.normalizer (K : Set G)).relIndex B' = 3 := fun B' h1 h2 h3 h4 =>
    (i112c_full CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional tables112Types_holds hsimple hKP
      Nat.prime_three (by norm_num) h1 h2 h3 hK h4).2.2.1
  refine ⟨hB.1, ?_⟩
  intro g hg hgo
  by_contra hgB
  exact i1135_core hy.1 hB.1 hB.2.1 hrankEq.le hK hnK hfull haut x0 hx0o hx0c T0 hT0 hT02 hx0T
    hg hgo hgB

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

theorem Hyp111.prime (h : Hyp111 G m p B x L) : p.Prime := h.mu.1.1

theorem Hyp111.ne_two (h : Hyp111 G m p B x L) : p ≠ 2 := h.mu.1.2.1

theorem Hyp111.elem (h : Hyp111 G m p B x L) : IsElemAbelian p B := h.bmax.1

theorem Hyp111.card_B (h : Hyp111 G m p B x L) : Nat.card B = p ^ m := by
  rw [h.bmax.2.1, h.mu.2.1]

theorem Hyp111.isChev2 (h : Hyp111 G m p B x L) : IsChev2 L :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) h.idiag

theorem Hyp111.card_cent (h : Hyp111 G m p B x L) : Nat.card ↥(B ⊓ centModSubgroup p L) = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have heq : B ⊓ centModSubgroup p L = Subgroup.zpowers x := by
    ext b
    constructor
    · rintro ⟨hbB, hb⟩
      exact (h.cent b hbB).1 (centMod_iff.2 hb)
    · intro hb
      have hbB : b ∈ B := (Subgroup.zpowers_le.2 h.mem) hb
      exact ⟨hbB, centMod_iff.1 ((h.cent b hbB).2 hb)⟩
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime (h.elem.2 x h.mem) h.ne_one

theorem Hyp111.pow_index_le (h : Hyp111 G m p B x L) (hm : 1 ≤ m) :
    p ^ (m - 1) * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B := by
  rw [h.card_cent, h.card_B, ← pow_succ]
  exact le_of_eq (by congr 1; omega)

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

theorem isChev2_of_innerDiag {B L : Subgroup G} (h : InnerDiagMarking B L) : IsChev2 L :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) h

theorem rquad_hyp {m p : ℕ} (hsf : StageFacts G m) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : RQuad G m p B x L) : Hyp111 G m p B x L := by
  obtain ⟨hmu, hS, hid⟩ := h
  obtain ⟨-, -, -, h5, -, -, -, h9, -⟩ := hsf p hmu
  exact ⟨hmu, hS.1.1.1.1, hS.1.1.1.2.1.1, hS.1.1.1.2.1.2.1, hS.1.1.1.2.2, hS.1.2.2,
    h5.2.1 B x L hS.1, (h9.1 B x L hS).1, hid⟩

theorem pRank_eq_of_card {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A) {k : ℕ}
    (hk : Nat.card A = p ^ k) : CFSG.Open.pRank p A = k := by
  refine le_antisymm ?_ (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hA hk)
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEA => ?_
  rw [← hk]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hE)

private theorem basic_bddAbove_twoLocal_pRank {q : ℕ} (hq : 1 < q) (K : Type) [Group K] [Finite K] :
    BddAbove {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank q H = k} := by
  refine ⟨Nat.card K, ?_⟩
  rintro k ⟨H, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq H
  have h1 : CFSG.Open.pRank q H < q ^ CFSG.Open.pRank q H := Nat.lt_pow_self hq
  have h2 : q ^ CFSG.Open.pRank q H ≤ Nat.card K := hE ▸ Subgroup.card_le_card_group E
  omega

private theorem basic_twoLocalRank_le_of_injective {q : ℕ} (hq : q.Prime) {A B : Type} [Group A]
    [Finite A] [Group B] [Finite B] (f : A →* B) (hf : Function.Injective f) :
    GLATwoLocalRank q A ≤ GLATwoLocalRank q B := by
  refine csSup_le' ?_
  rintro k ⟨H, hH, rfl⟩
  obtain ⟨P, hP, hP2, rfl⟩ := hH
  have hne : P.map f ≠ ⊥ := by
    intro h
    apply hP
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hfx : f x ∈ P.map f := Subgroup.mem_map_of_mem f hx
    rw [h, Subgroup.mem_bot] at hfx
    exact hf (hfx.trans (map_one f).symm)
  have hle : (Subgroup.normalizer (P : Set A)).map f ≤
      Subgroup.normalizer ((P.map f : Subgroup B) : Set B) := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
    have hn' := Subgroup.mem_normalizer_iff.1 hn
    refine Subgroup.mem_normalizer_iff.2 fun w => ?_
    simp only [SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨n * x * n⁻¹, (hn' x).1 hx, by simp [map_mul, map_inv]⟩
    · rintro ⟨z, hz, hzw⟩
      refine ⟨n⁻¹ * z * n, (hn' (n⁻¹ * z * n)).2 ?_, ?_⟩
      · rw [show n * (n⁻¹ * z * n) * n⁻¹ = z by group]
        exact hz
      · rw [map_mul, map_mul, map_inv, hzw]
        group
  calc CFSG.Open.pRank q (Subgroup.normalizer (P : Set A))
      ≤ CFSG.Open.pRank q ((Subgroup.normalizer (P : Set A)).map f) :=
        CFSG.SectionRank.pRank_le_map hq.one_lt f hf _
    _ ≤ CFSG.Open.pRank q (Subgroup.normalizer ((P.map f : Subgroup B) : Set B)) :=
        CFSG.SectionRank.pRank_mono hq.one_lt hle
    _ ≤ GLATwoLocalRank q B :=
        le_csSup (basic_bddAbove_twoLocal_pRank hq.one_lt B) ⟨_, ⟨P.map f, hne, hP2.map f, rfl⟩, rfl⟩

theorem twoLocalRank_mono {q : ℕ} (hq : q.Prime) {X Y : Subgroup G} (hXY : X ≤ Y) :
    GLATwoLocalRank q ↥X ≤ GLATwoLocalRank q ↥Y :=
  basic_twoLocalRank_le_of_injective hq (Subgroup.inclusion hXY) (Subgroup.inclusion_injective hXY)

theorem twoLocalRank_le_top {q : ℕ} (hq : q.Prime) (X : Subgroup G) :
    GLATwoLocalRank q ↥X ≤ GLATwoLocalRank q G :=
  basic_twoLocalRank_le_of_injective hq X.subtype Subtype.val_injective

private theorem basic_bddAbove_evenRank_set (K : Type) [Group K] [Finite K] :
    BddAbove {k | ∃ (p : ℕ) (H : Subgroup K), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
      CFSG.Open.pRank p H = k} := by
  refine ⟨Nat.card K, ?_⟩
  rintro k ⟨p, H, hp, -, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card K := hE ▸ Subgroup.card_le_card_group E
  omega

private theorem basic_twoLocalRank_le_evenRank_aux {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (K : Type)
    [Group K] [Finite K] : GLATwoLocalRank q K ≤ evenRank K := by
  refine csSup_le' ?_
  rintro k ⟨H, hH, rfl⟩
  exact le_csSup (basic_bddAbove_evenRank_set K) ⟨q, H, hq, hq2, hH, rfl⟩

theorem exists_prime_eq_evenRank {L : Subgroup G} (h : 1 ≤ evenRank ↥L) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ GLATwoLocalRank q ↥L = evenRank ↥L := by
  have hne : ({k | ∃ (p : ℕ) (H : Subgroup ↥L), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
      CFSG.Open.pRank p H = k} : Set ℕ).Nonempty := by
    rcases Set.eq_empty_or_nonempty
        ({k | ∃ (p : ℕ) (H : Subgroup ↥L), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
          CFSG.Open.pRank p H = k} : Set ℕ) with hemp | hne
    · exfalso
      have h0 : evenRank ↥L = 0 := by
        change sSup _ = 0
        rw [hemp]
        simp
      omega
    · exact hne
  have hmem : evenRank ↥L ∈ ({k | ∃ (p : ℕ) (H : Subgroup ↥L), p.Prime ∧ p ≠ 2 ∧
      IsTwoLocal H ∧ CFSG.Open.pRank p H = k} : Set ℕ) :=
    Nat.sSup_mem hne (basic_bddAbove_evenRank_set ↥L)
  obtain ⟨p, H, hp, hp2, hH, hpk⟩ := hmem
  refine ⟨p, hp, hp2, le_antisymm (basic_twoLocalRank_le_evenRank_aux hp hp2 ↥L) ?_⟩
  calc evenRank ↥L = CFSG.Open.pRank p H := hpk.symm
    _ ≤ GLATwoLocalRank p ↥L :=
        le_csSup (basic_bddAbove_twoLocal_pRank hp.one_lt ↥L) ⟨H, hH, rfl⟩

theorem twoLocalRank_le_evenRank {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (L : Subgroup G) :
    GLATwoLocalRank q ↥L ≤ evenRank ↥L :=
  basic_twoLocalRank_le_evenRank_aux hq hq2 ↥L

theorem twoLocalRank_le_pRank {q : ℕ} (hq : q.Prime) (L : Subgroup G) :
    GLATwoLocalRank q ↥L ≤ CFSG.Open.pRank q L := by
  refine csSup_le' ?_
  rintro k ⟨H, -, rfl⟩
  have hsub : H.map L.subtype ≤ L := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact x.2
  calc CFSG.Open.pRank q H ≤ CFSG.Open.pRank q (H.map L.subtype) :=
        CFSG.SectionRank.pRank_le_map hq.one_lt L.subtype Subtype.val_injective H
    _ ≤ CFSG.Open.pRank q L := CFSG.SectionRank.pRank_mono hq.one_lt hsub

theorem elemAbelian_le_of_twoLocal {p : ℕ} (hp : p.Prime) {M E : Subgroup G} (hM : IsTwoLocal M) (hEM : E ≤ M)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ GLATwoLocalRank p G := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  exact CFSG.LocalAnalysis.GLTheoremA.card_le_pow_glaTwoLocalRank hp hE hP hP2 hEM

private theorem basic_le_of_frattini {q : ℕ} (hq : q.Prime) {M H M₁ : Subgroup G} (hHM : H ≤ M)
    (hHM₁ : H ≤ M₁) (hnorm : (H.subgroupOf M₁).Normal) (h3 : 3 ≤ CFSG.Open.pRank q H)
    (hclosed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
      Subgroup.normalizer (P : Set G) ≤ M) : M₁ ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  set N : Subgroup M₁ := H.subgroupOf M₁ with hN
  haveI : N.Normal := hnorm
  set E' : Subgroup N := (E.subgroupOf M₁).subgroupOf N with hE'
  have hE'p : IsPGroup q E' := by
    intro g
    refine ⟨1, ?_⟩
    have hmem : (((g : N) : M₁) : G) ∈ E := g.2
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using hE.2 _ hmem
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow hE'p
  have hF : Subgroup.normalizer ((P : Subgroup N).map N.subtype : Set M₁) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  set T : Subgroup M₁ := (P : Subgroup N).map N.subtype with hT
  set S : Subgroup G := T.map M₁.subtype with hS
  have hSq : IsPGroup q S := (P.isPGroup'.map N.subtype).map M₁.subtype
  have hSH : S ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.1 ht
    exact n.2
  have hSM : S ≤ M := hSH.trans hHM
  have hES : E ≤ S := by
    intro e he
    have hM1 : e ∈ M₁ := hHM₁ (hEH he)
    have hNe : (⟨e, hM1⟩ : M₁) ∈ N := hEH he
    have hEP' : (⟨⟨e, hM1⟩, hNe⟩ : N) ∈ E' := he
    have hPm := hEP hEP'
    exact Subgroup.mem_map.2 ⟨⟨e, hM1⟩, Subgroup.mem_map.2 ⟨⟨⟨e, hM1⟩, hNe⟩, hPm, rfl⟩, rfl⟩
  have hS3 : 3 ≤ CFSG.Open.pRank q S :=
    h3.trans (CFSG.SectionRank.le_pRank hq.one_lt hES hE hEc)
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := hclosed S hSq hSM hS3
  intro g hg
  have hx : (⟨g, hg⟩ : M₁) ∈ (⊤ : Subgroup M₁) := Subgroup.mem_top _
  rw [← hF] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  have hgyz : ((y : M₁) : G) * ((z : M₁) : G) = g := by
    have h := congrArg Subtype.val hyz
    simpa using h
  have hyG : ((y : M₁) : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hy' := Subgroup.mem_normalizer_iff.1 hy
    constructor
    · intro hs
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
      refine Subgroup.mem_map.2 ⟨y * t * y⁻¹, (hy' t).1 ht, ?_⟩
      simp
    · intro hs
      obtain ⟨t', ht', hte⟩ := Subgroup.mem_map.1 hs
      refine Subgroup.mem_map.2 ⟨y⁻¹ * t' * y, (hy' (y⁻¹ * t' * y)).2 ?_, ?_⟩
      · simpa [mul_assoc] using ht'
      · have hte' : ((t' : M₁) : G) = (y : G) * s * (y : G)⁻¹ := hte
        show ((y⁻¹ * t' * y : M₁) : G) = s
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hte']
        group
  have hzM : ((z : M₁) : G) ∈ M := hHM (Subgroup.mem_subgroupOf.1 hz)
  have hyM : ((y : M₁) : G) ∈ M := hNS hyG
  rw [← hgyz]
  exact M.mul_mem hyM hzM

theorem le_of_subnormal_of_closed {q : ℕ} (hq : q.Prime) {M H X : Subgroup G} (hHX : IsSubnormal H X)
    (hHM : H ≤ M) (h3 : 3 ≤ CFSG.Open.pRank q H)
    (hclosed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
      Subgroup.normalizer (P : Set G) ≤ M) : X ≤ M := by
  induction hHX with
  | refl => exact hHM
  | step hHM₁ hnorm _ ih =>
    exact ih (basic_le_of_frattini hq hHM hHM₁ hnorm h3 hclosed)
      (h3.trans (CFSG.SectionRank.pRank_mono hq.one_lt hHM₁))

theorem isSC_of_le_M {p : ℕ} (hp : p.Prime) {B M : Subgroup G} (hB : GLAIsBmax p B) (hM : IsTwoLocal M)
    (hBM : B ≤ M) (hcen : ∀ g ∈ Subgroup.centralizer (B : Set G), g ∈ M) : IsSC p B := by
  refine ⟨hB.1, fun g hg hgp => ?_⟩
  have hgM : g ∈ M := hcen g hg
  have hgpow : g ^ p = 1 := by
    rw [← hgp]
    exact pow_orderOf_eq_one g
  have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers g, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute a g from Subgroup.mem_centralizer_iff.1 hg a ha).zpow_right n).eq
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers g) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hB.1 (CFSG.Open.isElemAbelian_zpowers hgpow) hcomm
  have hle : B ⊔ Subgroup.zpowers g ≤ M := sup_le hBM (Subgroup.zpowers_le.2 hgM)
  have hcard : Nat.card ↥(B ⊔ Subgroup.zpowers g) ≤ Nat.card B := by
    rw [hB.2.1]
    exact elemAbelian_le_of_twoLocal hp hM hle hE
  have heq : B = B ⊔ Subgroup.zpowers g := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact (le_sup_right : Subgroup.zpowers g ≤ B ⊔ Subgroup.zpowers g) (Subgroup.mem_zpowers g)

private theorem basic_pow_natCard_center {L : Subgroup G} {z : G} (hzL : z ∈ L)
    (hz : ∀ y ∈ L, y * z = z * y) : z ^ Nat.card (Subgroup.center ↥L) = 1 := by
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g.1 g.2)
  have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L))
    (x := (⟨⟨z, hzL⟩, hzc⟩ : ↥(Subgroup.center ↥L)))
  have h2 := congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : G)) h
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
  exact h2

private theorem basic_eq_one_of_central_pow {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {z : G} (hzL : z ∈ L)
    (hz : ∀ y ∈ L, y * z = z * y) (hzp : z ^ p = 1) : z = 1 := by
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hnoZ
  have h := pow_gcd_eq_one.2 ⟨hzp, basic_pow_natCard_center hzL hz⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

private theorem basic_mem_glaPPrimeCoreOf {p : ℕ} {L : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf p L ↔ ∃ h : g ∈ L, (⟨g, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

private theorem basic_glaPPrimeCore_ne_top {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : GLAPPrimeCore p ↥L ≠ ⊤ := by
  intro htop
  have hPQ := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hsub : Subsingleton (↥L ⧸ GLAPPrimeCore p ↥L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have hsub2 : Subsingleton ((↥L ⧸ GLAPPrimeCore p ↥L) ⧸
      Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L)) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  haveI := hPQ.2
  exact not_subsingleton _ hsub2

theorem exists_pElement_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {b : G} (hbp : b ^ p = 1)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hin : InducesInnerMod p L b) :
    ∃ a ∈ L, a ^ p = 1 ∧ ∀ y ∈ L, a⁻¹ * y * a = b⁻¹ * y * b := by
  obtain ⟨l, hl, hO⟩ := hin
  have hZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hqs inferInstance (basic_glaPPrimeCore_ne_top hp hL)
  have hcen : ∀ g ∈ GLAPPrimeCoreOf p L, g ∈ L ∧ ∀ z ∈ L, z * g = g * z := by
    intro g hg
    obtain ⟨hgL, hmem⟩ := basic_mem_glaPPrimeCoreOf.1 hg
    exact ⟨hgL, fun z hz => congrArg Subtype.val (Subgroup.mem_center_iff.1 (hZ hmem) ⟨z, hz⟩)⟩
  obtain ⟨c, hc⟩ : ∃ c : G → G, ∀ y, c y = (l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b) :=
    ⟨fun y => (l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b), fun y => rfl⟩
  have hYZ : ∀ y : G, b⁻¹ * y * b = (l⁻¹ * y * l) * c y := by
    intro y
    rw [hc]
    group
  have hcO : ∀ y ∈ L, c y ∈ GLAPPrimeCoreOf p L := fun y hy => by
    rw [hc]
    exact hO y hy
  have hcC : ∀ y ∈ L, ∀ z ∈ L, z * c y = c y * z :=
    fun y hy z hz => (hcen (c y) (hcO y hy)).2 z hz
  have hcL : ∀ y ∈ L, c y ∈ L := fun y hy => (hcen (c y) (hcO y hy)).1
  have hlconj : ∀ y ∈ L, l⁻¹ * y * l ∈ L := fun y hy =>
    L.mul_mem (L.mul_mem (L.inv_mem hl) hy) hl
  have hmul : ∀ y₁ ∈ L, ∀ y₂ ∈ L, c (y₁ * y₂) = c y₁ * c y₂ := by
    intro y₁ h₁ y₂ h₂
    have hcom : c y₁ * (l⁻¹ * y₂ * l) = (l⁻¹ * y₂ * l) * c y₁ :=
      (hcC y₁ h₁ _ (hlconj y₂ h₂)).symm
    have hprod : (l⁻¹ * y₁ * l) * (l⁻¹ * y₂ * l) * c (y₁ * y₂) =
        (l⁻¹ * y₁ * l) * (l⁻¹ * y₂ * l) * (c y₁ * c y₂) := by
      calc (l⁻¹ * y₁ * l) * (l⁻¹ * y₂ * l) * c (y₁ * y₂)
          = (l⁻¹ * (y₁ * y₂) * l) * c (y₁ * y₂) := by group
        _ = b⁻¹ * (y₁ * y₂) * b := (hYZ (y₁ * y₂)).symm
        _ = (b⁻¹ * y₁ * b) * (b⁻¹ * y₂ * b) := by group
        _ = ((l⁻¹ * y₁ * l) * c y₁) * ((l⁻¹ * y₂ * l) * c y₂) := by rw [hYZ y₁, hYZ y₂]
        _ = (l⁻¹ * y₁ * l) * (c y₁ * (l⁻¹ * y₂ * l)) * c y₂ := by group
        _ = (l⁻¹ * y₁ * l) * ((l⁻¹ * y₂ * l) * c y₁) * c y₂ := by rw [hcom]
        _ = (l⁻¹ * y₁ * l) * (l⁻¹ * y₂ * l) * (c y₁ * c y₂) := by group
    exact mul_left_cancel hprod
  obtain ⟨cH, hcH⟩ : ∃ cH : ↥L →* G, ∀ y : ↥L, cH y = c y :=
    ⟨MonoidHom.mk' (fun y : ↥L => c y) (fun a b => hmul a a.2 b b.2), fun y => rfl⟩
  have hcomm : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ cH.ker := by
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hcH, hcH]
    exact (hcC (g : G) g.2 (c (h : G)) (hcL (h : G) h.2)).symm
  have htop : ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ := hqs.1
  rw [htop] at hcomm
  have hc1 : ∀ y ∈ L, c y = 1 := fun y hy => by
    have h := MonoidHom.mem_ker.1 (hcomm (Subgroup.mem_top (⟨y, hy⟩ : ↥L)))
    rw [hcH] at h
    exact h
  have hconj : ∀ y ∈ L, b⁻¹ * y * b = l⁻¹ * y * l := fun y hy => by
    have h := hYZ y
    rw [hc1 y hy, mul_one] at h
    exact h
  have hgC : b * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * (b * l⁻¹) = b * (b⁻¹ * y * b) * l⁻¹ := by group
      _ = b * (l⁻¹ * y * l) * l⁻¹ := by rw [hconj y hy]
      _ = b * l⁻¹ * y := by group
  have hcommgl : Commute (b * l⁻¹) l := (Subgroup.mem_centralizer_iff.1 hgC l hl).symm
  have hgl : b * l⁻¹ * l = b := by group
  have hgp : (b * l⁻¹) ^ p * l ^ p = 1 := by
    rw [← hcommgl.mul_pow p, hgl, hbp]
  have hlp : l ^ p ∈ Subgroup.centralizer (L : Set G) := by
    rw [← inv_eq_of_mul_eq_one_right hgp]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hgC p)
  have hlpL : l ^ p ∈ L := L.pow_mem hl p
  have hpn : (l ^ p) ^ Nat.card (Subgroup.center ↥L) = 1 :=
    basic_pow_natCard_center hlpL (fun y hy => Subgroup.mem_centralizer_iff.1 hlp y hy)
  have hlpN : l ^ (p * Nat.card (Subgroup.center ↥L)) = 1 := by
    rw [pow_mul]
    exact hpn
  have hcop : IsCoprime (Nat.card (Subgroup.center ↥L) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnoZ).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨l ^ (u * (Nat.card (Subgroup.center ↥L) : ℤ)), L.zpow_mem hl _, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have hexp : u * (Nat.card (Subgroup.center ↥L) : ℤ) * (p : ℤ) =
        ((p * Nat.card (Subgroup.center ↥L) : ℕ) : ℤ) * u := by
      push_cast
      ring
    rw [hexp, zpow_mul, zpow_natCast, hlpN, one_zpow]
  · intro y hy
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = (l ^ (p : ℤ)) ^ (-v) := ⟨_, rfl⟩
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := by
      rw [hzdef]
      exact Subgroup.zpow_mem _ (by rw [zpow_natCast]; exact hlp) _
    have hexp : u * (Nat.card (Subgroup.center ↥L) : ℤ) = 1 + (p : ℤ) * (-v) := by
      linear_combination huv
    have ha_eq : l ^ (u * (Nat.card (Subgroup.center ↥L) : ℤ)) = l * z := by
      rw [hzdef, hexp, zpow_add, zpow_one, zpow_mul]
    rw [ha_eq, hconj y hy]
    have hcomm2 : (l⁻¹ * y * l) * z = z * (l⁻¹ * y * l) :=
      Subgroup.mem_centralizer_iff.1 hzC _ (hlconj y hy)
    calc (l * z)⁻¹ * y * (l * z) = z⁻¹ * (l⁻¹ * y * l) * z := by group
      _ = z⁻¹ * ((l⁻¹ * y * l) * z) := by group
      _ = z⁻¹ * (z * (l⁻¹ * y * l)) := by rw [hcomm2]
      _ = l⁻¹ * y * l := by group

private theorem basic_eq_of_same_action {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L)
    (hap : a ^ p = 1) (ha'p : a' ^ p = 1) (hact : ∀ y ∈ L, a⁻¹ * y * a = a'⁻¹ * y * a') :
    a = a' := by
  have hs : ∀ y ∈ L, (a⁻¹ * a') * y = y * (a⁻¹ * a') := by
    intro y hy
    have hy' : a * y * a⁻¹ ∈ L := L.mul_mem (L.mul_mem ha hy) (L.inv_mem ha)
    have h1 := hact (a * y * a⁻¹) hy'
    have h2 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
    rw [h2] at h1
    have h3 : a' * y = a * y * a⁻¹ * a' := by
      calc a' * y = a' * (a'⁻¹ * (a * y * a⁻¹) * a') := congrArg (a' * ·) h1
        _ = a * y * a⁻¹ * a' := by group
    calc (a⁻¹ * a') * y = a⁻¹ * (a' * y) := by group
      _ = a⁻¹ * (a * y * a⁻¹ * a') := by rw [h3]
      _ = y * (a⁻¹ * a') := by group
  have hsL : a⁻¹ * a' ∈ L := L.mul_mem (L.inv_mem ha) ha'
  have hcomm : Commute a (a⁻¹ * a') := (hs a ha).symm
  have hsp : (a⁻¹ * a') ^ p = 1 := by
    have h4 : (a * (a⁻¹ * a')) ^ p = a ^ p * (a⁻¹ * a') ^ p := hcomm.mul_pow p
    have h5 : a * (a⁻¹ * a') = a' := by group
    rw [h5, hap, one_mul] at h4
    rw [← h4]
    exact ha'p
  have hs1 : a⁻¹ * a' = 1 :=
    basic_eq_one_of_central_pow hp hnoZ hsL (fun y hy => (hs y hy).symm) hsp
  exact inv_mul_eq_one.1 hs1

private theorem basic_act_mul {L : Subgroup G} {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ L) (ha₂ : a₂ ∈ L)
    (hb₁ : b₁ ∈ Subgroup.normalizer (L : Set G)) (hact₁ : ∀ y ∈ L, a₁⁻¹ * y * a₁ = b₁⁻¹ * y * b₁)
    (hact₂ : ∀ y ∈ L, a₂⁻¹ * y * a₂ = b₂⁻¹ * y * b₂) :
    ∀ y ∈ L, (a₁ * a₂)⁻¹ * y * (a₁ * a₂) = (b₁ * b₂)⁻¹ * y * (b₁ * b₂) := by
  intro y hy
  have hy1 : b₁⁻¹ * y * b₁ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb₁) y).1 hy
    simpa using this
  calc (a₁ * a₂)⁻¹ * y * (a₁ * a₂) = a₂⁻¹ * (a₁⁻¹ * y * a₁) * a₂ := by group
    _ = a₂⁻¹ * (b₁⁻¹ * y * b₁) * a₂ := by rw [hact₁ y hy]
    _ = b₂⁻¹ * (b₁⁻¹ * y * b₁) * b₂ := hact₂ _ hy1
    _ = (b₁ * b₂)⁻¹ * y * (b₁ * b₂) := by group

private theorem basic_mul_comm_of_act {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ L) (ha₂ : a₂ ∈ L)
    (hap₁ : a₁ ^ p = 1) (hb₁ : b₁ ∈ Subgroup.normalizer (L : Set G))
    (hb₂ : b₂ ∈ Subgroup.normalizer (L : Set G))
    (hact₁ : ∀ y ∈ L, a₁⁻¹ * y * a₁ = b₁⁻¹ * y * b₁)
    (hact₂ : ∀ y ∈ L, a₂⁻¹ * y * a₂ = b₂⁻¹ * y * b₂) (hbb : b₁ * b₂ = b₂ * b₁) :
    a₁ * a₂ = a₂ * a₁ := by
  have hEq : ∀ y ∈ L, (a₁ * a₂)⁻¹ * y * (a₁ * a₂) = (a₂ * a₁)⁻¹ * y * (a₂ * a₁) := by
    intro y hy
    rw [basic_act_mul ha₁ ha₂ hb₁ hact₁ hact₂ y hy, basic_act_mul ha₂ ha₁ hb₂ hact₂ hact₁ y hy,
      hbb]
  obtain ⟨r, hr_def⟩ : ∃ r : G, r = (a₂ * a₁) * (a₁ * a₂)⁻¹ := ⟨_, rfl⟩
  have hrL : r ∈ L := by
    rw [hr_def]
    exact L.mul_mem (L.mul_mem ha₂ ha₁) (L.inv_mem (L.mul_mem ha₁ ha₂))
  have hrC : ∀ y ∈ L, r * y = y * r := by
    intro y hy
    have h := hEq y hy
    have h' : (a₁ * a₂)⁻¹ * y = (a₂ * a₁)⁻¹ * y * (a₂ * a₁) * (a₁ * a₂)⁻¹ := by
      calc (a₁ * a₂)⁻¹ * y = ((a₁ * a₂)⁻¹ * y * (a₁ * a₂)) * (a₁ * a₂)⁻¹ := by group
        _ = ((a₂ * a₁)⁻¹ * y * (a₂ * a₁)) * (a₁ * a₂)⁻¹ := by rw [h]
    calc r * y = (a₂ * a₁) * ((a₁ * a₂)⁻¹ * y) := by rw [hr_def]; group
      _ = (a₂ * a₁) * ((a₂ * a₁)⁻¹ * y * (a₂ * a₁) * (a₁ * a₂)⁻¹) := by rw [h']
      _ = y * r := by rw [hr_def]; group
  have hrp : r ^ p = 1 := by
    have hconjr : r * a₁ = a₂ * a₁ * a₂⁻¹ := by
      rw [hr_def]
      group
    have h7 : r ^ p * a₁ ^ p = 1 := by
      rw [← (show Commute r a₁ from hrC a₁ ha₁).mul_pow, hconjr, conj_pow, hap₁, mul_one,
        mul_inv_cancel]
    rwa [hap₁, mul_one] at h7
  have hr1 : r = 1 :=
    basic_eq_one_of_central_pow hp hnoZ hrL (fun y hy => (hrC y hy).symm) hrp
  rw [hr_def] at hr1
  exact (mul_inv_eq_one.1 hr1).symm

private theorem basic_lift_mul_aux {L : Subgroup G} {a₁ a₂ b₁ b₂ : G} (ha₂ : a₂ ∈ L)
    (hc₁ : a₁⁻¹ * b₁ ∈ Subgroup.centralizer (L : Set G)) :
    (a₁ * a₂)⁻¹ * (b₁ * b₂) = (a₁⁻¹ * b₁) * (a₂⁻¹ * b₂) := by
  have hcomm : a₂⁻¹ * (a₁⁻¹ * b₁) = (a₁⁻¹ * b₁) * a₂⁻¹ :=
    ((show Commute a₂ (a₁⁻¹ * b₁) from Subgroup.mem_centralizer_iff.1 hc₁ a₂ ha₂).inv_left).eq
  calc (a₁ * a₂)⁻¹ * (b₁ * b₂) = a₂⁻¹ * (a₁⁻¹ * b₁) * b₂ := by group
    _ = (a₁⁻¹ * b₁) * a₂⁻¹ * b₂ := by rw [hcomm]
    _ = (a₁⁻¹ * b₁) * (a₂⁻¹ * b₂) := by group

theorem exists_lift_hom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L B : Subgroup G} (hL : GLAPComponent p X L)
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hB : IsElemAbelian p B)
    (hnorm : B ≤ Subgroup.normalizer (L : Set G)) (hin : ∀ b ∈ B, InducesInnerMod p L b) :
    ∃ c : ↥B →* G, (∀ b : ↥B, c b ∈ Subgroup.centralizer (L : Set G)) ∧
      ∀ b : ↥B, (b : G) * (c b)⁻¹ ∈ L ∧ ((b : G) * (c b)⁻¹) ^ p = 1 := by
  have key : ∀ b ∈ B, ∃ a ∈ L, a ^ p = 1 ∧ ∀ y ∈ L, a⁻¹ * y * a = b⁻¹ * y * b :=
    fun b hb => exists_pElement_lift hp hp2 hL hqs hnoZ (hB.2 b hb) (hnorm hb) (hin b hb)
  choose! A hAL hAp hAact using key
  have hmulA : ∀ b₁ ∈ B, ∀ b₂ ∈ B, A (b₁ * b₂) = A b₁ * A b₂ := by
    intro b₁ h₁ b₂ h₂
    have hcomm := basic_mul_comm_of_act hp hnoZ (hAL b₁ h₁) (hAL b₂ h₂) (hAp b₁ h₁)
      (hnorm h₁) (hnorm h₂) (hAact b₁ h₁) (hAact b₂ h₂) (isElemAbelian_commute hB h₁ h₂)
    refine basic_eq_of_same_action hp hnoZ (hAL _ (B.mul_mem h₁ h₂))
      (L.mul_mem (hAL b₁ h₁) (hAL b₂ h₂)) (hAp _ (B.mul_mem h₁ h₂)) ?_ ?_
    · rw [Commute.mul_pow (show Commute (A b₁) (A b₂) from hcomm) p, hAp b₁ h₁, hAp b₂ h₂,
        mul_one]
    · intro y hy
      exact (hAact _ (B.mul_mem h₁ h₂) y hy).trans
        (basic_act_mul (hAL b₁ h₁) (hAL b₂ h₂) (hnorm h₁) (hAact b₁ h₁) (hAact b₂ h₂) y hy).symm
  have hcC : ∀ β : ↥B, (A (β : G))⁻¹ * (β : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro β
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hAact (β : G) β.2 (A (β : G) * y * (A (β : G))⁻¹)
      (L.mul_mem (L.mul_mem (hAL _ β.2) hy) (L.inv_mem (hAL _ β.2)))
    have h2 : (β : G)⁻¹ * (A (β : G) * y * (A (β : G))⁻¹) * (β : G) = y := by
      rw [← h1]
      group
    calc y * ((A (β : G))⁻¹ * (β : G))
        = ((A (β : G))⁻¹ * (β : G)) * ((β : G)⁻¹ * (A (β : G) * y * (A (β : G))⁻¹) * (β : G)) := by
          group
      _ = ((A (β : G))⁻¹ * (β : G)) * y := by rw [h2]
  refine ⟨MonoidHom.mk' (fun β : ↥B => (A (β : G))⁻¹ * (β : G)) ?_, ?_, ?_⟩
  · intro β₁ β₂
    show (A ((β₁ * β₂ : ↥B) : G))⁻¹ * ((β₁ * β₂ : ↥B) : G) =
      ((A (β₁ : G))⁻¹ * (β₁ : G)) * ((A (β₂ : G))⁻¹ * (β₂ : G))
    rw [Subgroup.coe_mul, hmulA _ β₁.2 _ β₂.2]
    exact basic_lift_mul_aux (hAL _ β₂.2) (hcC β₁)
  · intro β
    exact hcC β
  · intro β
    have e : (β : G) * ((A (β : G))⁻¹ * (β : G))⁻¹ = A (β : G) := by group
    show (β : G) * ((A (β : G))⁻¹ * (β : G))⁻¹ ∈ L ∧
      ((β : G) * ((A (β : G))⁻¹ * (β : G))⁻¹) ^ p = 1
    rw [e]
    exact ⟨hAL _ β.2, hAp _ β.2⟩

private theorem basic_isPGroup_zpowers_of_pow {p : ℕ} {t : G} {v : ℕ} (h : t ^ (p ^ v) = 1) :
    IsPGroup p (Subgroup.zpowers t) := by
  intro g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨v, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, h, one_zpow]

private theorem basic_exists_pPart_pow {p : ℕ} (hp : p.Prime) (g : G) :
    ∃ m : ℕ, ¬ p ∣ m ∧ ∃ v : ℕ, (g ^ m) ^ (p ^ v) = 1 := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨orderOf g / p ^ (orderOf g).factorization p,
    (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_ordCompl hp hn),
    (orderOf g).factorization p, ?_⟩
  have hm0 : orderOf g / p ^ (orderOf g).factorization p ≠ 0 :=
    (Nat.ordCompl_pos p hn).ne'
  have hord : orderOf (g ^ (orderOf g / p ^ (orderOf g).factorization p)) =
      p ^ (orderOf g).factorization p := by
    rw [orderOf_pow_of_dvd hm0 (Nat.ordCompl_dvd _ _)]
    exact Nat.div_eq_of_eq_mul_left (Nat.ordCompl_pos p hn)
      (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  have hpow := pow_orderOf_eq_one (g ^ (orderOf g / p ^ (orderOf g).factorization p))
  rw [hord] at hpow
  exact hpow

private theorem basic_pow_mul_inv_mem_coset {L : Subgroup G} {b l : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) :
    ∀ k : ℕ, ∃ l' ∈ L, (b * l⁻¹) ^ k = b ^ k * l' := by
  intro k
  induction k with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨l₁, hl₁, hk⟩ := ih
    refine ⟨b⁻¹ * l₁ * b * l⁻¹, ?_, ?_⟩
    · have hconj : b⁻¹ * l₁ * b ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) l₁).1 hl₁
        simpa using this
      exact L.mul_mem hconj (L.inv_mem hl)
    · rw [pow_succ, hk]
      group

private theorem basic_closure_pair_form {x t : G} (hc : Commute x t) :
    ∀ s ∈ Subgroup.closure ({x, t} : Set G), ∃ a b : ℤ, s = x ^ a * t ^ b := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨a, b, rfl⟩ := ihy
    obtain ⟨c, d, rfl⟩ := ihz
    refine ⟨a + c, b + d, ?_⟩
    have h1 : t ^ b * x ^ c = x ^ c * t ^ b := ((hc.symm).zpow_zpow b c).eq
    calc x ^ a * t ^ b * (x ^ c * t ^ d) = x ^ a * (t ^ b * x ^ c) * t ^ d := by group
      _ = x ^ a * (x ^ c * t ^ b) * t ^ d := by rw [h1]
      _ = x ^ (a + c) * t ^ (b + d) := by rw [zpow_add, zpow_add]; group
  | inv y _ ih =>
    obtain ⟨a, b, rfl⟩ := ih
    refine ⟨-a, -b, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact ((hc.symm).zpow_zpow (-b) (-a)).eq

private theorem basic_not_mem_of_centralizes {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) : x ∉ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hxmem
  have hcen : (⟨x, hxmem⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hxL g.2) x (Set.mem_singleton x)
    simpa using this.symm
  have hord : orderOf (⟨⟨x, hxmem⟩, hcen⟩ : ↥(Subgroup.center ↥L)) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hdvd := orderOf_dvd_natCard (⟨⟨x, hxmem⟩, hcen⟩ : ↥(Subgroup.center ↥L))
  rw [hord] at hdvd
  exact hnoZ hdvd

private theorem basic_mul_inv_mem_centModSubgroup {p : ℕ} {L : Subgroup G} {b l : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L)
    (h : ∀ y ∈ L, (l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b) ∈ GLAPPrimeCoreOf p L) :
    b * l⁻¹ ∈ centModSubgroup p L := by
  refine mem_centModSubgroup.2 ⟨Subgroup.mul_mem _ hb (Subgroup.inv_mem _
    (Subgroup.le_normalizer hl)), fun y hy => ?_⟩
  have hO0 := h y hy
  have hbO : b * ((l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b)) * b⁻¹ ∈ GLAPPrimeCoreOf p L :=
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hb) _).1 hO0
  have hyO : y * (b * ((l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b)) * b⁻¹) * y⁻¹ ∈ GLAPPrimeCoreOf p L :=
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L
      (Subgroup.le_normalizer hy)) _).1 hbO
  have heq : ⁅y, b * l⁻¹⁆ = y * (b * ((l⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b)) * b⁻¹) * y⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact hyO

private theorem basic_zpow_eq_one_of_mem {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxL' : x ∉ L) {e : ℤ} (he : x ^ e ∈ L) : x ^ e = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hf : x ^ (e % (p : ℤ)) = x ^ e := by
    have := zpow_mod_orderOf x e
    rwa [hord] at this
  rw [← hf] at he ⊢
  by_cases h0 : e % (p : ℤ) = 0
  · rw [h0, zpow_zero]
  · exfalso
    have hnd : ¬ (p : ℤ) ∣ e % (p : ℤ) := by
      intro hd
      have hlo : 0 ≤ e % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)
      have hhi : e % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
      exact h0 (Int.eq_zero_of_dvd_of_nonneg_of_lt hlo hhi hd)
    have hcop : IsCoprime (e % (p : ℤ)) (p : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hnd).symm
    obtain ⟨u, v, huv⟩ := hcop
    apply hxL'
    have hsum : e % (p : ℤ) * u + (p : ℤ) * v = 1 := by rw [mul_comm, mul_comm (p : ℤ)]; exact huv
    have hx : x = (x ^ (e % (p : ℤ))) ^ u * (x ^ (p : ℤ)) ^ v := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, hsum, zpow_one]
    have hxp' : x ^ (p : ℤ) = 1 := by rw [zpow_natCast, hxp]
    rw [hx, hxp', one_zpow, mul_one]
    exact L.zpow_mem he u

theorem bdecomp_of_cyc {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L B : Subgroup G} {x : G} (hL : GLAPComponent p X L)
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hnorm : B ≤ Subgroup.normalizer (L : Set G))
    (hcent : CentModEqZpowers p B L x) (hin : ∀ b ∈ B, InducesInnerMod p L b) (hcyc : CycModSylow p L) :
    IsDirectZpowersInf B x L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hxL' : x ∉ L := basic_not_mem_of_centralizes hp hx1 hxp hxL hnoZ
  have hxcL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hxL hl) x (Set.mem_singleton x)
  have hcommx : ∀ b ∈ B, x * b = b * x := fun b hb => isElemAbelian_commute hB hxB hb
  have hxW : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hxcL l hl).symm
  have key : ∀ b ∈ B, ∃ e : ℤ, (x ^ e)⁻¹ * b ∈ L := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hnorm hb
    obtain ⟨l, hl, hinl⟩ := hin b hb
    have hgW : b * l⁻¹ ∈ centModSubgroup p L := basic_mul_inv_mem_centModSubgroup hbN hl hinl
    have hxg : Commute x (b * l⁻¹) := by
      show x * (b * l⁻¹) = (b * l⁻¹) * x
      have hxl : x * l⁻¹ = l⁻¹ * x := hxcL l⁻¹ (L.inv_mem hl)
      calc x * (b * l⁻¹) = (x * b) * l⁻¹ := (mul_assoc _ _ _).symm
        _ = (b * x) * l⁻¹ := by rw [hcommx b hb]
        _ = b * (x * l⁻¹) := mul_assoc _ _ _
        _ = b * (l⁻¹ * x) := by rw [hxl]
        _ = (b * l⁻¹) * x := (mul_assoc _ _ _).symm
    obtain ⟨m, hmp, v, hv⟩ := basic_exists_pPart_pow hp (b * l⁻¹)
    obtain ⟨t, ht⟩ : ∃ t : G, t = (b * l⁻¹) ^ m := ⟨_, rfl⟩
    have htW : t ∈ centModSubgroup p L := by
      rw [ht]
      exact (centModSubgroup p L).pow_mem hgW m
    have hxt : Commute x t := by
      rw [ht]
      exact hxg.pow_right m
    have htpv : t ^ (p ^ v) = 1 := by
      rw [ht]
      exact hv
    obtain ⟨lt, hlt, hteq⟩ := basic_pow_mul_inv_mem_coset hbN hl m
    have h2 : t = b ^ m * lt := by rw [ht, hteq]
    have htp : t ^ p ∈ L := by
      obtain ⟨l'', hl'', hm⟩ := basic_pow_mul_inv_mem_coset hbN hl (m * p)
      have hbmp : b ^ (m * p) = 1 := by rw [pow_mul', hB.2 b hb, one_pow]
      have hT : (b * l⁻¹) ^ (m * p) = t ^ p := by rw [ht, pow_mul]
      rw [← hT, hm, hbmp, one_mul]
      exact hl''
    obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = Subgroup.closure ({x, t} : Set G) := ⟨_, rfl⟩
    have hxS : x ∈ S := by
      rw [hS]
      exact Subgroup.subset_closure (by simp)
    have htS : t ∈ S := by
      rw [hS]
      exact Subgroup.subset_closure (by simp)
    have hSW : S ≤ centModSubgroup p L := by
      rw [hS, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact hxW
      · exact htW
    have htn : t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (hxt.zpow_left n).eq
    have hpx : IsPGroup p (Subgroup.zpowers x) :=
      basic_isPGroup_zpowers_of_pow (v := 1) (by rw [pow_one]; exact hxp)
    have hpt : IsPGroup p (Subgroup.zpowers t) := basic_isPGroup_zpowers_of_pow htpv
    have hSeq : Subgroup.closure ({x, t} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers t := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
        Set.singleton_union]
    have hSp : IsPGroup p S := by
      rw [hS, hSeq]
      exact IsPGroup.to_sup_of_normal_left' hpx hpt (Subgroup.zpowers_le.2 htn)
    have hcycS : IsCyclic S := hcyc S (fun g hg => centMod_iff.2 (hSW hg)) hSp
    haveI := hcycS
    have hexp : ∀ s ∈ S, s ^ p ∈ L := by
      intro s hs
      rw [hS] at hs
      obtain ⟨a, b', rfl⟩ := basic_closure_pair_form hxt s hs
      rw [(hxt.zpow_zpow a b').mul_pow]
      have h1 : (x ^ a) ^ p = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
      have h2' : (t ^ b') ^ p ∈ L := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        exact L.zpow_mem htp b'
      rw [h1, one_mul]
      exact h2'
    obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := ↥S)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨x, hxS⟩)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨t, htS⟩)
    have hxj : (c : G) ^ j = x := by
      have := congrArg Subtype.val hj
      simpa using this
    have hti : (c : G) ^ i = t := by
      have := congrArg Subtype.val hi
      simpa using this
    have hcp : (c : G) ^ p ∈ L := hexp _ c.2
    have hpj : IsCoprime j (p : ℤ) := by
      refine ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 ?_).symm
      rintro ⟨q, rfl⟩
      apply hxL'
      rw [← hxj, zpow_mul, zpow_natCast]
      exact L.zpow_mem hcp q
    obtain ⟨u, w, huw⟩ := hpj
    obtain ⟨l0, hl0def⟩ : ∃ l0 : G, l0 = ((c : G) ^ (p : ℤ)) ^ w := ⟨_, rfl⟩
    have hl0 : l0 ∈ L := by
      rw [hl0def, zpow_natCast]
      exact L.zpow_mem hcp w
    have hcxl : (c : G) = x ^ u * l0 := by
      calc (c : G) = (c : G) ^ (j * u + (p : ℤ) * w) := by
            rw [show j * u + (p : ℤ) * w = u * j + w * p by ring, huw, zpow_one]
        _ = ((c : G) ^ j) ^ u * ((c : G) ^ (p : ℤ)) ^ w := by rw [zpow_add, zpow_mul, zpow_mul]
        _ = x ^ u * l0 := by rw [hxj, hl0def]
    have hcom : Commute (x ^ u) l0 := (show Commute x l0 from hxcL l0 hl0).zpow_left u
    have htform : t = x ^ (u * i) * l0 ^ i := by
      rw [← hti, hcxl, hcom.mul_zpow, ← zpow_mul]
    have hlam0 : (x ^ (u * i))⁻¹ * b ^ m ∈ L := by
      have h3 : b ^ m = t * lt⁻¹ := by rw [h2]; group
      have h4 : (x ^ (u * i))⁻¹ * b ^ m = l0 ^ i * lt⁻¹ := by rw [h3, htform]; group
      rw [h4]
      exact L.mul_mem (L.zpow_mem hl0 i) (L.inv_mem hlt)
    obtain ⟨lam, hlamL, hlamdef⟩ : ∃ lam ∈ L, b ^ m = x ^ (u * i) * lam :=
      ⟨(x ^ (u * i))⁻¹ * b ^ m, hlam0, by group⟩
    have hcopm : IsCoprime (m : ℤ) (p : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 (by exact_mod_cast hmp)).symm
    obtain ⟨r, s, hrs⟩ := hcopm
    have hbp : b ^ (p : ℤ) = 1 := by rw [zpow_natCast, hB.2 b hb]
    have hbr : b = (b ^ m) ^ r := by
      calc b = b ^ ((m : ℤ) * r + (p : ℤ) * s) := by
            rw [show (m : ℤ) * r + (p : ℤ) * s = r * m + s * p by ring, hrs, zpow_one]
        _ = (b ^ m) ^ r * (b ^ (p : ℤ)) ^ s := by
            rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast]
        _ = (b ^ m) ^ r := by rw [hbp, one_zpow, mul_one]
    have hxlam : Commute x lam := show x * lam = lam * x from hxcL lam hlamL
    have hbx : b = x ^ (u * i * r) * lam ^ r := by
      calc b = (b ^ m) ^ r := hbr
        _ = (x ^ (u * i) * lam) ^ r := by rw [hlamdef]
        _ = x ^ (u * i * r) * lam ^ r := by
            rw [(hxlam.zpow_left (u * i)).mul_zpow r, ← zpow_mul]
    refine ⟨u * i * r, ?_⟩
    have h5 : (x ^ (u * i * r))⁻¹ * b = lam ^ r := by
      rw [hbx]
      group
    rw [h5]
    exact L.zpow_mem hlamL r
  unfold IsDirectZpowersInf
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro b hb
      obtain ⟨e, he⟩ := key b hb
      have hxe : x ^ e ∈ B := B.zpow_mem hxB e
      have hmem : (x ^ e)⁻¹ * b ∈ B ⊓ L := ⟨B.mul_mem (B.inv_mem hxe) hb, he⟩
      have hb' : b = x ^ e * ((x ^ e)⁻¹ * b) := by group
      rw [hb']
      exact Subgroup.mul_mem_sup ((Subgroup.zpowers x).zpow_mem (Subgroup.mem_zpowers x) e) hmem
    · exact sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
  · rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
    rw [Subgroup.mem_bot]
    exact basic_zpow_eq_one_of_mem hp hxp hx1 hxL' hy2.2

theorem bdecomp_of_sc {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L B : Subgroup G} {x : G} (hL : GLAPComponent p X L)
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnoZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hB : IsSC p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hnorm : B ≤ Subgroup.normalizer (L : Set G))
    (hcent : CentModEqZpowers p B L x) (hin : ∀ b ∈ B, InducesInnerMod p L b) :
    IsDirectZpowersInf B x L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcC, hcL⟩ := exists_lift_hom hp hp2 hL hqs hnoZ hB.1 hnorm hin
  have hxp : x ^ p = 1 := hB.1.2 x hxB
  have hxL' : x ∉ L := basic_not_mem_of_centralizes hp hx1 hxp hxL hnoZ
  have hcom : ∀ β β' : ↥B, c β * c β' = c β' * c β := by
    intro β β'
    have hbb : β * β' = β' * β := Subtype.ext (isElemAbelian_commute hB.1 β.2 β'.2)
    rw [← map_mul, ← map_mul, hbb]
  have hcB : ∀ β β' : ↥B, c β * (β' : G) = (β' : G) * c β := by
    intro β β'
    obtain ⟨a', ha'L, ha'eq⟩ : ∃ a' ∈ L, (β' : G) = a' * c β' :=
      ⟨(β' : G) * (c β')⁻¹, (hcL β').1, by group⟩
    rw [ha'eq]
    have h1 : a' * c β = c β * a' := Subgroup.mem_centralizer_iff.1 (hcC β) a' ha'L
    calc c β * (a' * c β') = (c β * a') * c β' := by group
      _ = (a' * c β) * c β' := by rw [h1]
      _ = a' * (c β * c β') := by group
      _ = a' * (c β' * c β) := by rw [hcom β β']
      _ = a' * c β' * c β := by group
  have key : ∀ b ∈ B, ∃ e : ℤ, (x ^ e)⁻¹ * b ∈ L := by
    intro b hb
    obtain ⟨β, rfl⟩ : ∃ β : ↥B, (β : G) = b := ⟨⟨b, hb⟩, rfl⟩
    have hgcent : c β ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun b' hb' => (hcB β ⟨b', hb'⟩).symm
    have hgp : (c β) ^ p = 1 := by
      have h1 : β ^ p = 1 := Subtype.ext (by simpa using hB.1.2 (β : G) β.2)
      rw [← map_pow, h1, map_one]
    have hgB : c β ∈ B := by
      by_cases hg1 : c β = 1
      · rw [hg1]
        exact B.one_mem
      · exact hB.2 (c β) hgcent (orderOf_eq_prime hgp hg1)
    have hgCM : CentMod p L (c β) := centMod_of_mem_centralizer (hcC β)
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 ((hcent (c β) hgB).1 hgCM)
    refine ⟨e, ?_⟩
    have hba : (β : G) * (c β)⁻¹ ∈ L := (hcL β).1
    have hcom' : ((β : G) * (c β)⁻¹) * c β = c β * ((β : G) * (c β)⁻¹) :=
      Subgroup.mem_centralizer_iff.1 (hcC β) _ hba
    rw [he]
    have hb_eq : (c β)⁻¹ * (β : G) = (β : G) * (c β)⁻¹ := by
      calc (c β)⁻¹ * (β : G) = (c β)⁻¹ * (((β : G) * (c β)⁻¹) * c β) := by group
        _ = (c β)⁻¹ * (c β * ((β : G) * (c β)⁻¹)) := by rw [hcom']
        _ = (β : G) * (c β)⁻¹ := by group
    rw [hb_eq]
    exact hba
  unfold IsDirectZpowersInf
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro b hb
      obtain ⟨e, he⟩ := key b hb
      have hxe : x ^ e ∈ B := B.zpow_mem hxB e
      have hmem : (x ^ e)⁻¹ * b ∈ B ⊓ L := ⟨B.mul_mem (B.inv_mem hxe) hb, he⟩
      have hb' : b = x ^ e * ((x ^ e)⁻¹ * b) := by group
      rw [hb']
      exact Subgroup.mul_mem_sup ((Subgroup.zpowers x).zpow_mem (Subgroup.mem_zpowers x) e) hmem
    · exact sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
  · rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
    rw [Subgroup.mem_bot]
    exact basic_zpow_eq_one_of_mem hp hxp hx1 hxL' hy2.2

theorem not_mem_of_direct {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {x : G} (hx1 : x ≠ 1)
    (hxB : x ∈ B) (hd : IsDirectZpowersInf B x L) : x ∉ L := by
  intro hxL
  have h1 : x ∈ Subgroup.zpowers x ⊓ (B ⊓ L) := ⟨Subgroup.mem_zpowers x, hxB, hxL⟩
  rw [hd.2] at h1
  exact hx1 (Subgroup.mem_bot.1 h1)

theorem card_inf_of_direct {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {x : G} (hB : IsElemAbelian p B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hd : IsDirectZpowersInf B x L) :
    Nat.card ↥(B ⊓ L) * p = Nat.card B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : B ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro g hg
    have hc : x * g = g * x := (isElemAbelian_commute hB hg.1 hxB).symm
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute x g from hc) n).eq
  have h1 := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hcomm
  rw [← hd.1, hd.2, Subgroup.card_bot, Nat.card_zpowers] at h1
  rw [orderOf_eq_prime (hB.2 x hxB) hx1] at h1
  linarith

theorem card_inf_eq (h : Hyp111 G m p B x L) (hd : IsDirectZpowersInf B x L) :
    Nat.card ↥(B ⊓ L) = p ^ (m - 1) := by
  have hp := h.prime
  have h1 := card_inf_of_direct hp h.elem h.mem h.ne_one hd
  rw [h.card_B] at h1
  have hm : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero] at h1
    have hp1 := hp.one_lt
    nlinarith [Nat.card_pos (α := ↥(B ⊓ L))]
  have : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ]; congr 1; omega
  rw [this] at h1
  exact Nat.eq_of_mul_eq_mul_right hp.pos h1

end S11

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Contra
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LinearAlgebra.SL2CoprimeOrder
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_mono {q : ℕ} (hq : q.Prime) {P P' : Subgroup G} (h : P ≤ P') :
    CFSG.Open.pRank q P ≤ CFSG.Open.pRank q P' := by
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt P
  exact CFSG.SectionRank.le_pRank hq.one_lt (hEP.trans h) hE hcard

theorem normalizer_le_weakCore {q : ℕ} (hq : q.Prime) {R Q : Subgroup G} (hQR : Q ≤ R)
    (h3 : 3 ≤ CFSG.Open.pRank q Q) : Subgroup.normalizer (Q : Set G) ≤ GLAWeakCore q R := by
  unfold GLAWeakCore rankThreeAschCore
  refine le_sSup ⟨Q, hQR, by omega, ?_, rfl⟩
  exact h3.trans (pRank_mono hq le_sup_left)

private theorem isPGroup_subgroupOf_of_isPGroup {q : ℕ} {H K : Subgroup G} (hH : IsPGroup q H) :
    IsPGroup q (H.subgroupOf K) := by
  intro g
  obtain ⟨k, hk⟩ := hH ⟨((g : K) : G), Subgroup.mem_subgroupOf.1 g.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun x : ↥H => (x : G)) hk
  simpa using h

open scoped Pointwise in
theorem normalizer_le_of_le_M {q : ℕ} (hq : q.Prime) (R : Sylow q G) {M : Subgroup G}
    (hRM : (R : Subgroup G) ≤ M)
    (hnorm : ∀ Q : Subgroup G, Q ≤ (R : Subgroup G) → 3 ≤ CFSG.Open.pRank q Q →
      Subgroup.normalizer (Q : Set G) ≤ M)
    {P : Subgroup G} (hP : IsPGroup q P) (hPM : P ≤ M) (h3 : 3 ≤ CFSG.Open.pRank q P) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  let RM : Sylow q M :=
    { toSubgroup := (R : Subgroup G).subgroupOf M
      isPGroup' := isPGroup_subgroupOf_of_isPGroup R.isPGroup'
      is_maximal' := by
        intro Q hQ hRQ
        have hQ' : IsPGroup q (Q.map M.subtype) := hQ.map M.subtype
        have hR' : (R : Subgroup G) ≤ Q.map M.subtype := by
          intro x hx
          exact Subgroup.mem_map.2 ⟨⟨x, hRM hx⟩, hRQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have hEq : Q.map M.subtype = R := R.is_maximal' hQ' hR'
        calc Q = (Q.map M.subtype).comap M.subtype :=
              (Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q).symm
          _ = (R : Subgroup G).subgroupOf M := by rw [hEq]; rfl }
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow (isPGroup_subgroupOf_of_isPGroup (K := M) hP)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) Q₀ RM
  have hS : MulAut.conj g • (Q₀ : Subgroup ↥M) = (RM : Subgroup ↥M) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hconj : ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ ∈ (R : Subgroup G) := by
    intro x hx
    have hxQ : (⟨x, hPM hx⟩ : ↥M) ∈ Q₀ := hQ₀ (Subgroup.mem_subgroupOf.2 hx)
    have hmem := Subgroup.smul_mem_pointwise_smul (⟨x, hPM hx⟩ : ↥M) (MulAut.conj g) _ hxQ
    rw [hS] at hmem
    have := Subgroup.mem_subgroupOf.1 hmem
    simpa [MulAut.conj_apply] using this
  set Q : Subgroup G := P.map (MulAut.conj (g : G)).toMonoidHom with hQdef
  have hmemQ : ∀ y, y ∈ Q ↔ ∃ x ∈ P, (g : G) * x * (g : G)⁻¹ = y := by
    intro y
    simp only [hQdef, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hQR : Q ≤ (R : Subgroup G) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemQ y).1 hy
    exact hconj x hx
  have hpQ : 3 ≤ CFSG.Open.pRank q Q := by
    obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt P
    have hinj : Function.Injective (MulAut.conj (g : G)).toMonoidHom :=
      (MulAut.conj (g : G)).injective
    have hEQ : E.map (MulAut.conj (g : G)).toMonoidHom ≤ Q := Subgroup.map_mono hEP
    have hE' := CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj (g : G)).toMonoidHom
    have hc' : Nat.card (E.map (MulAut.conj (g : G)).toMonoidHom) = q ^ CFSG.Open.pRank q P := by
      rw [Subgroup.card_map_of_injective hinj, hcard]
    have := CFSG.SectionRank.le_pRank hq.one_lt hEQ hE' hc'
    exact h3.trans this
  have hNQ := hnorm Q hQR hpQ
  intro x hx
  rw [Subgroup.mem_normalizer_iff] at hx
  have hz : (g : G) * x * (g : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨p, hp, rfl⟩ := (hmemQ y).1 hy
      refine (hmemQ _).2 ⟨x * p * x⁻¹, (hx p).1 hp, ?_⟩
      group
    · intro hy
      obtain ⟨p, hp, hpy⟩ := (hmemQ _).1 hy
      refine (hmemQ y).2 ⟨x⁻¹ * p * x, ?_, ?_⟩
      · exact (hx (x⁻¹ * p * x)).2 (by simpa [mul_assoc] using hp)
      · calc (g : G) * (x⁻¹ * p * x) * (g : G)⁻¹
            = ((g : G) * x * (g : G)⁻¹)⁻¹ * ((g : G) * p * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹) := by
              group
          _ = ((g : G) * x * (g : G)⁻¹)⁻¹ * (((g : G) * x * (g : G)⁻¹) * y *
                ((g : G) * x * (g : G)⁻¹)⁻¹) * ((g : G) * x * (g : G)⁻¹) := by rw [hpy]
          _ = y := by group
  have hzM := hNQ hz
  have hgM : (g : G) ∈ M := g.2
  have : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hzM) hgM

theorem le_M_of_chain {q : ℕ} (hq : q.Prime) {M : Subgroup G} {Q₂ Q₃ : Subgroup G}
    (hclosed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
      Subgroup.normalizer (P : Set G) ≤ M)
    (hQ₂M : Q₂ ≤ M) (h3 : 3 ≤ CFSG.Open.pRank q Q₂) (hQ₂₃ : Q₂ ≤ Q₃) (hQ₃ : IsPGroup q Q₃) :
    Q₃ ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, ⟨hQ₂P, hPQ₃, hPM⟩, hmax⟩ := Set.exists_max_image
    {P : Subgroup G | Q₂ ≤ P ∧ P ≤ Q₃ ∧ P ≤ M} (fun P : Subgroup G => Nat.card P) (Set.toFinite _)
    ⟨Q₂, le_rfl, hQ₂₃, hQ₂M⟩
  have hP3 : 3 ≤ CFSG.Open.pRank q P := h3.trans (pRank_mono hq hQ₂P)
  have hPp : IsPGroup q P := hQ₃.to_le hPQ₃
  have hPeq : P = Q₃ := by
    by_contra hne
    have hlt : P < Q₃ := lt_of_le_of_ne hPQ₃ hne
    have hPQ3 : P.subgroupOf Q₃ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact hne (le_antisymm hPQ₃ htop)
    haveI hnil : Group.IsNilpotent ↥Q₃ := IsPGroup.isNilpotent hQ₃
    obtain ⟨x, hx, hxn⟩ := (SetLike.lt_iff_le_and_exists.1
      (Group.normalizerCondition_of_isNilpotent (P.subgroupOf Q₃) hPQ3)).2
    have hfwd : ∀ w : ↥Q₃, w ∈ Subgroup.normalizer ((P.subgroupOf Q₃ : Subgroup ↥Q₃) : Set ↥Q₃) →
        ∀ h : G, h ∈ P → (w : G) * h * (w : G)⁻¹ ∈ P := by
      intro w hw h hh
      have := (Subgroup.mem_normalizer_iff.1 hw ⟨h, hPQ₃ hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hfwd x hx h hh
      · intro hh
        have hx' := inv_mem hx
        have h' := hfwd x⁻¹ hx' _ hh
        simpa [mul_assoc] using h'
    have hxM : (x : G) ∈ M := hclosed P hPp hPM hP3 hxN
    have hxQ3 : (x : G) ∈ Q₃ := x.2
    have hsup : P ⊔ Subgroup.zpowers (x : G) ∈ {P : Subgroup G | Q₂ ≤ P ∧ P ≤ Q₃ ∧ P ≤ M} :=
      ⟨hQ₂P.trans le_sup_left, sup_le hPQ₃ (Subgroup.zpowers_le.2 hxQ3),
        sup_le hPM (Subgroup.zpowers_le.2 hxM)⟩
    have hle := hmax _ hsup
    have hxP : (x : G) ∉ P := fun h => hxn (Subgroup.mem_subgroupOf.2 h)
    have hlt2 : P < P ⊔ Subgroup.zpowers (x : G) := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply hxP
      have hmem : (x : G) ∈ P ⊔ Subgroup.zpowers (x : G) :=
        (le_sup_right (a := P) (b := Subgroup.zpowers (x : G))) (Subgroup.mem_zpowers _)
      rw [← heq] at hmem
      exact hmem
    have hcard := Subgroup.card_lt_of_lt hlt2
    omega
  rw [← hPeq]
  exact hPM

theorem weakCore_closure {q : ℕ} (hq : q.Prime) (R : Sylow q G) {M : Subgroup G}
    (hW : GLAWeakCore q (R : Subgroup G) ≤ M) (hR3 : 3 ≤ CFSG.Open.pRank q (R : Subgroup G))
    {Q₂ Q₃ : Subgroup G} (hQ₂R : Q₂ ≤ (R : Subgroup G)) (h3 : 3 ≤ CFSG.Open.pRank q Q₂)
    (hQ₂₃ : Q₂ ≤ Q₃) (hQ₃ : IsPGroup q Q₃) :
    Q₃ ≤ M ∧ Subgroup.normalizer (Q₃ : Set G) ≤ M := by
  have hnorm : ∀ Q : Subgroup G, Q ≤ (R : Subgroup G) → 3 ≤ CFSG.Open.pRank q Q →
      Subgroup.normalizer (Q : Set G) ≤ M :=
    fun Q hQR h3Q => (normalizer_le_weakCore hq hQR h3Q).trans hW
  have hRM : (R : Subgroup G) ≤ M :=
    (Subgroup.le_normalizer (H := (R : Subgroup G))).trans (hnorm _ le_rfl hR3)
  have hclosed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
      Subgroup.normalizer (P : Set G) ≤ M :=
    fun P hP hPM h3P => normalizer_le_of_le_M hq R hRM hnorm hP hPM h3P
  have hQ₃M : Q₃ ≤ M := le_M_of_chain hq hclosed (hQ₂R.trans hRM) h3 hQ₂₃ hQ₃
  exact ⟨hQ₃M, hclosed Q₃ hQ₃ hQ₃M (h3.trans (pRank_mono hq hQ₂₃))⟩


private theorem card_comap_quotient_mk' {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (S : Subgroup (X ⧸ N)) :
    Nat.card (S.comap (QuotientGroup.mk' N)) = Nat.card S * Nat.card N := by
  have h1 := (S.comap (QuotientGroup.mk' N)).card_mul_index
  have h2 := S.card_mul_index
  have h3 : (S.comap (QuotientGroup.mk' N)).index = S.index :=
    Subgroup.index_comap_of_surjective S (QuotientGroup.mk'_surjective N)
  have h4 : Nat.card X = Nat.card (X ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [h3] at h1
  have hS0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hS0)
  rw [h1, h4, ← h2]
  ring

private theorem eq_bot_of_normal_coprime_quotient {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    [Finite H] (K : Subgroup (H ⧸ GLAPPrimeCore p H)) [K.Normal]
    (hcop : Nat.Coprime p (Nat.card K)) : K = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard := card_comap_quotient_mk' (GLAPPrimeCore p H) K
  have hcop' : Nat.Coprime p (Nat.card (K.comap (QuotientGroup.mk' (GLAPPrimeCore p H)))) := by
    rw [hcard]
    exact Nat.Coprime.mul_right hcop pPrimeCore_coprime_card
  have hle : K.comap (QuotientGroup.mk' (GLAPPrimeCore p H)) ≤ GLAPPrimeCore p H :=
    le_sSup ⟨inferInstance, hcop'⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p H) x
  have hy : y ∈ GLAPPrimeCore p H := hle hx
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff y).2 hy)

private theorem pow_eq_one_of_mem_center_quotient {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    [Finite H] {z : H ⧸ GLAPPrimeCore p H} (hz : z ∈ Subgroup.center (H ⧸ GLAPPrimeCore p H)) :
    ∃ k : ℕ, z ^ (p ^ k) = 1 := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.one_lt.ne'
  have hw : (z ^ (p ^ e)) ^ m = 1 := by
    rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hwc : z ^ (p ^ e) ∈ Subgroup.center (H ⧸ GLAPPrimeCore p H) := Subgroup.pow_mem _ hz _
  have hle : Subgroup.zpowers (z ^ (p ^ e)) ≤ Subgroup.center (H ⧸ GLAPPrimeCore p H) := by
    rw [Subgroup.zpowers_le]
    exact hwc
  haveI hnorm : (Subgroup.zpowers (z ^ (p ^ e))).Normal := Subgroup.normal_of_le_center hle
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z ^ (p ^ e)))) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hw)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hbot := eq_bot_of_normal_coprime_quotient hp (Subgroup.zpowers (z ^ (p ^ e))) hcop
  have hw1 : z ^ (p ^ e) = 1 := by
    have hmem : z ^ (p ^ e) ∈ Subgroup.zpowers (z ^ (p ^ e)) := Subgroup.mem_zpowers _
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact ⟨e, hw1⟩

private theorem center_ne_top_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : Subgroup.center Q ≠ ⊤ := by
  intro h
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    rw [h]
    exact QuotientGroup.subsingleton_quotient_top
  haveI := hQ.2
  exact (not_nontrivial_iff_subsingleton.2 hsub) inferInstance

private theorem center_center_quotient_eq_bot {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with h | h
  · exact h
  · exfalso
    have hab : (⁅(⊤ : Subgroup (Q ⧸ Subgroup.center Q)), ⊤⁆ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      have ha : a ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
        rw [h]
        exact Subgroup.mem_top a
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact Subgroup.mem_center_iff.1 ha b
    have hperf : (⁅(⊤ : Subgroup (Q ⧸ Subgroup.center Q)), ⊤⁆ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊤ := by
      have hm := Subgroup.map_commutator (H₁ := (⊤ : Subgroup Q)) (H₂ := (⊤ : Subgroup Q))
        (QuotientGroup.mk' (Subgroup.center Q))
      have hq : (⁅(⊤ : Subgroup Q), ⊤⁆ : Subgroup Q) = ⊤ := hQ.1
      rw [hq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hm
      exact hm.symm
    rw [hab] at hperf
    have hall : ∀ x : Q ⧸ Subgroup.center Q, x = 1 := fun x => Subgroup.mem_bot.1 (hperf ▸ Subgroup.mem_top x)
    exact (not_nontrivial_iff_subsingleton.2 ⟨fun a b => (hall a).trans (hall b).symm⟩) inferInstance

private theorem pCore_pQuot_eq_center {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : CFSG.pCore p (PQuot p J) = Subgroup.center (PQuot p J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : IsSimpleGroup (PQuot p J ⧸ Subgroup.center (PQuot p J)) := hQ.2
  haveI : Nontrivial (PQuot p J) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J))).nontrivial
  apply le_antisymm
  · apply sSup_le
    rintro N ⟨hN, hNp⟩
    by_cases htop : N = ⊤
    · exfalso
      subst htop
      have hpg : IsPGroup p (PQuot p J) := by
        intro g
        obtain ⟨k, hk⟩ := hNp ⟨g, Subgroup.mem_top g⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      haveI : Group.IsNilpotent (PQuot p J) := hpg.isNilpotent
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot p J)
      rw [hQ.1] at hlt
      exact lt_irrefl _ hlt
    · exact le_center_of_normal_of_isQuasisimple hQ hN htop
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    intro g
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_center_quotient hp g.2
    exact ⟨k, Subtype.ext hk⟩

theorem pComponent_basic {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    (∀ g : ↥J, (g : G) ∈ oPPrimeP p J ↔
        (QuotientGroup.mk g : PQuot p J) ∈ Subgroup.center (PQuot p J)) ∧
      ¬ J ≤ oPPrimeP p J ∧
      (∀ z ∈ Subgroup.center (PQuot p J), ∃ k : ℕ, z ^ (p ^ k) = 1) ∧
      Subgroup.center (PSimple p J) = ⊥ := by
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hkey : ∀ g : ↥J, (g : G) ∈ oPPrimeP p J ↔
      (QuotientGroup.mk g : PQuot p J) ∈ CFSG.pCore p (PQuot p J) := by
    intro g
    unfold oPPrimeP
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyg⟩
      have hyeq : y = g := Subtype.ext hyg
      subst hyeq
      exact hy
    · intro h
      exact ⟨g, h, rfl⟩
  rw [pCore_pQuot_eq_center hp hJ] at hkey
  refine ⟨hkey, ?_, fun z hz => pow_eq_one_of_mem_center_quotient hp hz, center_center_quotient_eq_bot hQ⟩
  intro hle
  apply center_ne_top_of_quasisimple hQ
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact (hkey g).1 (hle g.2)

theorem isSimple_pSimple {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    IsSimpleGroup (PSimple p J) :=
  (isQuasisimple_pQuot_of_glaPComponent hp hJ).2

theorem pSimple_nonabelian {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    ∃ a b : PSimple p J, a * b ≠ b * a := by
  haveI := isSimple_pSimple hp hJ
  obtain ⟨-, -, -, hZ⟩ := pComponent_basic hp hJ
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center (PSimple p J) = ⊤ := by
    ext g
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    intro h
    exact hcon h g
  rw [hZ] at htop
  exact bot_ne_top htop

theorem isKGroup_of_le_cx {p : ℕ} (hc : S9Ctx G p) {x : G} (hx : x ≠ 1) {X : Subgroup G}
    (hX : X ≤ cx x) : CFSG.Open.IsKGroup ↥X := by
  refine isKGroup_of_isKProper hc.ctx.kProper ?_
  intro htop
  exact (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx)
    (top_le_iff.1 (htop ▸ hX))

private theorem isElemAbelian_closure_pairwise {P : Type*} [Group P] {q : ℕ} {S : Set P}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hexp : ∀ x ∈ S, x ^ q = 1) :
    CFSG.Open.IsElemAbelian q (Subgroup.closure S) := by
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm (fun x hx y hy _ => hcomm x hx y hy)
  refine ⟨⟨⟨fun a b => mul_comm a b⟩⟩, fun x hx => ?_⟩
  refine Subgroup.closure_induction (p := fun x _ => x ^ q = 1) (fun x hx => hexp x hx)
    (one_pow q) (fun x y hx hy hxq hyq => ?_) (fun x _ hxq => by rw [inv_pow, hxq, inv_one]) hx
  have hc : x * y = y * x := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
  have hc' : Commute x y := hc
  rw [hc'.mul_pow, hxq, hyq, one_mul]

private theorem commutatorElement_mul_of_central {P : Type*} [Group P] {x g h d : P}
    (hd : d = x * h * x⁻¹ * h⁻¹) (hc : ∀ y : P, y * d = d * y) :
    x * (g * h) * x⁻¹ * (g * h)⁻¹ = (x * g * x⁻¹ * g⁻¹) * d := by
  have h1 : x⁻¹ * d = h * x⁻¹ * h⁻¹ := by rw [hd]; group
  have hgd : g * d * g⁻¹ = d := by rw [hc g]; group
  calc x * (g * h) * x⁻¹ * (g * h)⁻¹ = x * g * (h * x⁻¹ * h⁻¹) * g⁻¹ := by group
    _ = x * g * (x⁻¹ * d) * g⁻¹ := by rw [h1]
    _ = (x * g * x⁻¹ * g⁻¹) * (g * d * g⁻¹) := by group
    _ = (x * g * x⁻¹ * g⁻¹) * d := by rw [hgd]

private theorem triple_sub_eq {K : Type*} [CommGroup K] (a e c a' e' c' : K) :
    (a * a'⁻¹) * (e * e'⁻¹) * (c * c'⁻¹) = (a * e * c) * (a' * e' * c')⁻¹ := by
  simp only [mul_inv]
  ac_rfl

private theorem index_commutator_le_P {P : Type*} [Group P] [Finite P] {q : ℕ} [hq : Fact q.Prime]
    (hq2 : q ≠ 2) (hexp : ∀ x : P, x ^ q = 1)
    (hcl : ∀ a b c : P, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hrank : ∀ E : Subgroup P, CFSG.Open.IsElemAbelian q E → ∀ k : ℕ, Nat.card E = q ^ k → k ≤ 2) :
    (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P).index ≤ q ^ 2 := by
  have hq1 : 1 < q := hq.out.one_lt
  have hqpos : 0 < q := hq.out.pos
  have hPg : ∀ H : Subgroup P, IsPGroup q H := fun H x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hexp x.1)⟩
  have hcen : ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.center P := fun a b =>
    Subgroup.mem_center_iff.2 (fun g => (hcl a b g).symm)
  set Cm : Subgroup P := ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ with hCm
  set Z : Subgroup P := Subgroup.center P with hZ
  have hCZ : Cm ≤ Z := Subgroup.commutator_le.2 (fun a _ b _ => hcen a b)
  by_cases hab : Cm = ⊥
  ·
    have hcomm : ∀ a b : P, a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈ Cm := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hab, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hTel : CFSG.Open.IsElemAbelian q (⊤ : Subgroup P) :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hexp x⟩
    obtain ⟨k, hk⟩ := (hPg ⊤).exists_card_eq
    have hk' : Nat.card P = q ^ k := by rw [← Subgroup.card_top]; exact hk
    rw [hab, Subgroup.index_bot, hk']
    exact Nat.pow_le_pow_right hqpos (hrank ⊤ hTel k (by rw [Subgroup.card_top]; exact hk'))
  ·
    obtain ⟨a₀, b₀, hab0⟩ : ∃ a b : P, ⁅a, b⁆ ≠ 1 := by
      by_contra h
      push Not at h
      apply hab
      rw [eq_bot_iff]
      exact Subgroup.commutator_le.2 (fun a _ b _ => Subgroup.mem_bot.2 (h a b))
    have hZne : Z ≠ ⊥ := by
      intro h
      apply hab
      rw [h] at hCZ
      exact le_bot_iff.1 hCZ
    have ha0 : a₀ ∉ Z := by
      intro h
      apply hab0
      exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 h b₀).symm
    have ha0pow : a₀ ^ q = 1 := hexp a₀
    have hH_eq : ∀ e : P, Z ⊔ Subgroup.zpowers e = Subgroup.closure ((Z : Set P) ∪ {e}) := by
      intro e
      rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
    have hH_el : ∀ e : P, e ^ q = 1 → CFSG.Open.IsElemAbelian q (Z ⊔ Subgroup.zpowers e) := by
      intro e he
      rw [hH_eq e]
      refine isElemAbelian_closure_pairwise (fun x hx y hy => ?_) (fun x hx => ?_)
      · rcases hx with hx | hx
        · exact (Subgroup.mem_center_iff.1 hx y).symm
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          rcases hy with hy | hy
          · exact Subgroup.mem_center_iff.1 hy e
          · rw [Set.mem_singleton_iff] at hy
            rw [hy]
      · rcases hx with hx | hx
        · exact hexp x
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact he
    have hH_card : ∀ e : P, e ∉ Z → e ^ q = 1 →
        Nat.card ↥(Z ⊔ Subgroup.zpowers e) = Nat.card Z * q := by
      intro e he heq
      have hne : e ≠ 1 := fun h => he (h ▸ Subgroup.one_mem _)
      have hzp : Nat.card (Subgroup.zpowers e) = q := by
        rw [Nat.card_zpowers, orderOf_eq_prime heq hne]
      have hinf : Z ⊓ Subgroup.zpowers e = ⊥ := by
        have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers e) ∣ q := by
          rw [← hzp]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hq.out).1 hdvd with h1 | h1
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq2 : Z ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hzp])
          have hmem : e ∈ Z ⊓ Subgroup.zpowers e := by
            rw [heq2]
            exact Subgroup.mem_zpowers e
          exact he hmem.1
      have h := card_sup_mul_card_inf_of_normal Z (Subgroup.zpowers e)
      rw [hinf, Subgroup.card_bot, hzp, mul_one] at h
      exact h
    obtain ⟨nZ, hnZ⟩ := (hPg Z).exists_card_eq
    have hnZ1 : nZ = 1 := by
      have h1 := hrank _ (hH_el a₀ ha0pow) (nZ + 1)
        (by rw [hH_card a₀ ha0 ha0pow, hnZ, ← pow_succ])
      have h2 : nZ ≠ 0 := by
        rintro rfl
        apply hZne
        exact Subgroup.eq_bot_of_card_eq _ (by rw [hnZ, pow_zero])
      omega
    have hZcard : Nat.card Z = q := by rw [hnZ, hnZ1, pow_one]
    have hCZeq : Cm = Z := by
      obtain ⟨m, hm⟩ := (hPg Cm).exists_card_eq
      have hm1 : m = 1 := by
        have hdvd : Nat.card Cm ∣ Nat.card Z := Subgroup.card_dvd_of_le hCZ
        rw [hm, hZcard] at hdvd
        have hm_le : m ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hq1).1 (by rw [pow_one]; exact hdvd)
        have hm_ne : m ≠ 0 := by
          rintro rfl
          apply hab
          exact Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero])
        omega
      exact Subgroup.eq_of_le_of_card_ge hCZ (by rw [hm, hm1, pow_one, hZcard])
    rw [hCZeq]
    by_contra hlt
    push Not at hlt
    obtain ⟨N, hN⟩ := (hPg ⊤).exists_card_eq
    have hN' : Nat.card P = q ^ N := by rw [← Subgroup.card_top]; exact hN
    have hZI : Nat.card Z * Z.index = Nat.card P := Subgroup.card_mul_index Z
    have hIdvd : Z.index ∣ q ^ N := ⟨q, by rw [← hN', ← hZI, hZcard, mul_comm]⟩
    obtain ⟨j, -, hIj⟩ := (Nat.dvd_prime_pow hq.out).1 hIdvd
    have hj3 : 3 ≤ j := by
      by_contra h
      push Not at h
      have h1 : q ^ j ≤ q ^ 2 := Nat.pow_le_pow_right hqpos (by omega)
      rw [hIj] at hlt
      exact absurd (lt_of_lt_of_le hlt h1) (lt_irrefl _)
    have hI3 : q ^ 3 ≤ Z.index := by
      rw [hIj]
      exact Nat.pow_le_pow_right hqpos hj3
    let φ : P →* ↥Z :=
      { toFun := fun g => ⟨⁅a₀, g⁆, hcen a₀ g⟩
        map_one' := by
          apply Subtype.ext
          simp [commutatorElement_def]
        map_mul' := fun g h => by
          apply Subtype.ext
          have hd := hcen a₀ h
          simp only [Subgroup.coe_mul, commutatorElement_def]
          exact commutatorElement_mul_of_central rfl (fun y => Subgroup.mem_center_iff.1 hd y) }
    have hCidx : (φ.ker).index ≤ q := by
      rw [Subgroup.index_ker]
      exact (Subgroup.card_le_card_group φ.range).trans hZcard.le
    have hIC : Z.index ≤ Nat.card φ.ker := by
      have h1 : q * Z.index ≤ q * Nat.card φ.ker := by
        calc q * Z.index = Nat.card P := by rw [← hZI, hZcard]
          _ = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index _).symm
          _ ≤ Nat.card φ.ker * q := Nat.mul_le_mul_left _ hCidx
          _ = q * Nat.card φ.ker := mul_comm _ _
      exact Nat.le_of_mul_le_mul_left h1 hqpos
    have hH2 : Nat.card ↥(Z ⊔ Subgroup.zpowers a₀) = q ^ 2 := by
      rw [hH_card a₀ ha0 ha0pow, hZcard, sq]
    obtain ⟨e₂, he₂C, he₂H⟩ : ∃ e₂ ∈ φ.ker, e₂ ∉ Z ⊔ Subgroup.zpowers a₀ := by
      by_contra hcon
      push Not at hcon
      have hle : φ.ker ≤ Z ⊔ Subgroup.zpowers a₀ := fun x hx => hcon x hx
      have h1 := Subgroup.card_le_of_le hle
      rw [hH2] at h1
      have h2 : q ^ 3 ≤ Nat.card φ.ker := le_trans hI3 hIC
      have h3 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq1 (by norm_num)
      exact absurd (lt_of_lt_of_le h3 (h2.trans h1)) (lt_irrefl _)
    have he₂Z : e₂ ∉ Z := fun h => he₂H (Subgroup.mem_sup_left h)
    have he₂pow : e₂ ^ q = 1 := hexp e₂
    have hcomm12 : a₀ * e₂ = e₂ * a₀ := by
      have h1 : φ e₂ = 1 := MonoidHom.mem_ker.1 he₂C
      have h2 : ⁅a₀, e₂⁆ = 1 := congrArg Subtype.val h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
    obtain ⟨c, hcZ, hc1⟩ : ∃ c ∈ Z, c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hZne
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hcon x hx)
    have hcpow : c ^ q = 1 := hexp c
    have hcorder : orderOf c = q := orderOf_eq_prime hcpow hc1
    have hcc : ∀ y : P, y * c = c * y := fun y => Subgroup.mem_center_iff.1 hcZ y
    have hindep : ∀ x y z : ℤ, a₀ ^ x * e₂ ^ y * c ^ z = 1 →
        (q : ℤ) ∣ x ∧ (q : ℤ) ∣ y ∧ (q : ℤ) ∣ z := by
      intro x y z hxyz
      have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq.out
      have hcop : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → IsCoprime (q : ℤ) n := fun n hn =>
        (Irreducible.coprime_iff_not_dvd hqZ.irreducible).2 hn
      have hczc : ∀ w : P, w * c ^ z = c ^ z * w := fun w =>
        Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hcZ z) w
      have hcZz : c ^ z ∈ Z := Subgroup.zpow_mem _ hcZ z
      have hHa : a₀ ^ x ∈ Z ⊔ Subgroup.zpowers a₀ :=
        Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a₀) x)
      have hy : (q : ℤ) ∣ y := by
        by_contra hy
        obtain ⟨u, v, huv⟩ := hcop y hy
        have h1 : a₀ ^ x * c ^ z * e₂ ^ y = 1 := by
          rw [mul_assoc, ← hczc (e₂ ^ y), ← mul_assoc, hxyz]
        have hw : e₂ ^ y = (a₀ ^ x * c ^ z)⁻¹ := eq_inv_of_mul_eq_one_right h1
        have hwH : e₂ ^ y ∈ Z ⊔ Subgroup.zpowers a₀ := by
          rw [hw]
          exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hHa (Subgroup.mem_sup_left hcZz))
        have h2 : e₂ ^ (u * (q : ℤ) + v * y) = e₂ := by rw [huv, zpow_one]
        have h3 : e₂ ^ (u * (q : ℤ)) = 1 := by
          rw [mul_comm, zpow_mul, zpow_natCast, he₂pow, one_zpow]
        rw [zpow_add, h3, one_mul] at h2
        have he2 : e₂ = (e₂ ^ y) ^ v := by
          rw [← zpow_mul, mul_comm y v]
          exact h2.symm
        apply he₂H
        rw [he2]
        exact Subgroup.zpow_mem _ hwH v
      obtain ⟨t, ht⟩ := hy
      have hy1 : e₂ ^ y = 1 := by
        rw [ht, zpow_mul, zpow_natCast, he₂pow, one_zpow]
      have hxz : a₀ ^ x * c ^ z = 1 := by
        rw [hy1, mul_one] at hxyz
        exact hxyz
      have hxZ : a₀ ^ x ∈ Z := by
        have h1 : a₀ ^ x = (c ^ z)⁻¹ := eq_inv_of_mul_eq_one_left hxz
        rw [h1]
        exact Subgroup.inv_mem _ hcZz
      have hx : (q : ℤ) ∣ x := by
        by_contra hx
        obtain ⟨u, v, huv⟩ := hcop x hx
        have h2 : a₀ ^ (u * (q : ℤ) + v * x) = a₀ := by rw [huv, zpow_one]
        have h3 : a₀ ^ (u * (q : ℤ)) = 1 := by
          rw [mul_comm, zpow_mul, zpow_natCast, ha0pow, one_zpow]
        rw [zpow_add, h3, one_mul, mul_comm v x, zpow_mul] at h2
        apply ha0
        rw [← h2]
        exact Subgroup.zpow_mem _ hxZ v
      obtain ⟨s, hs⟩ := hx
      have hx1 : a₀ ^ x = 1 := by
        rw [hs, zpow_mul, zpow_natCast, ha0pow, one_zpow]
      have hz1 : c ^ z = 1 := by
        rw [hx1, one_mul] at hxz
        exact hxz
      have hz : (q : ℤ) ∣ z := by
        have h1 : (orderOf c : ℤ) ∣ z := orderOf_dvd_iff_zpow_eq_one.2 hz1
        rw [hcorder] at h1
        exact_mod_cast h1
      exact ⟨⟨s, hs⟩, ⟨t, ht⟩, hz⟩
    set S : Set P := {a₀, e₂, c} with hS
    have hSpair : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hcomm12 | exact hcomm12.symm | exact hcc _ | exact (hcc _).symm
    have hpair : S.Pairwise Commute := fun x hx y hy _ => hSpair x hx y hy
    set A : Subgroup P := Subgroup.closure S with hA
    letI : CommGroup A := Subgroup.closureCommGroupOfComm hpair
    have hAel : CFSG.Open.IsElemAbelian q A := isElemAbelian_closure_pairwise hSpair (by
      intro x hx
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact ha0pow
      · exact he₂pow
      · exact hcpow)
    have memA : ∀ x ∈ S, x ∈ A := fun x hx => Subgroup.subset_closure hx
    let a' : A := ⟨a₀, memA a₀ (by simp [hS])⟩
    let e' : A := ⟨e₂, memA e₂ (by simp [hS])⟩
    let c' : A := ⟨c, memA c (by simp [hS])⟩
    let ψ : ZMod q × ZMod q × ZMod q → A := fun x =>
      a' ^ ((x.1.val : ℕ) : ℤ) * e' ^ ((x.2.1.val : ℕ) : ℤ) * c' ^ ((x.2.2.val : ℕ) : ℤ)
    have hψinj : Function.Injective ψ := by
      rintro ⟨i1, i2, i3⟩ ⟨j1, j2, j3⟩ hij
      have hdiff : a' ^ (((i1.val : ℕ) : ℤ) - ((j1.val : ℕ) : ℤ)) *
          e' ^ (((i2.val : ℕ) : ℤ) - ((j2.val : ℕ) : ℤ)) *
          c' ^ (((i3.val : ℕ) : ℤ) - ((j3.val : ℕ) : ℤ)) = 1 := by
        have hij' : a' ^ ((i1.val : ℕ) : ℤ) * e' ^ ((i2.val : ℕ) : ℤ) * c' ^ ((i3.val : ℕ) : ℤ) =
            a' ^ ((j1.val : ℕ) : ℤ) * e' ^ ((j2.val : ℕ) : ℤ) * c' ^ ((j3.val : ℕ) : ℤ) := hij
        have key : (a' ^ ((i1.val : ℕ) : ℤ) * e' ^ ((i2.val : ℕ) : ℤ) * c' ^ ((i3.val : ℕ) : ℤ)) *
            (a' ^ ((j1.val : ℕ) : ℤ) * e' ^ ((j2.val : ℕ) : ℤ) * c' ^ ((j3.val : ℕ) : ℤ))⁻¹ = 1 := by
          rw [hij', mul_inv_cancel]
        have hT := triple_sub_eq (K := A) (a' ^ ((i1.val : ℕ) : ℤ)) (e' ^ ((i2.val : ℕ) : ℤ))
          (c' ^ ((i3.val : ℕ) : ℤ)) (a' ^ ((j1.val : ℕ) : ℤ)) (e' ^ ((j2.val : ℕ) : ℤ))
          (c' ^ ((j3.val : ℕ) : ℤ))
        rw [zpow_sub, zpow_sub, zpow_sub]
        exact hT.trans key
      have hP1 : a₀ ^ (((i1.val : ℕ) : ℤ) - ((j1.val : ℕ) : ℤ)) *
          e₂ ^ (((i2.val : ℕ) : ℤ) - ((j2.val : ℕ) : ℤ)) *
          c ^ (((i3.val : ℕ) : ℤ) - ((j3.val : ℕ) : ℤ)) = 1 := by
        have := congrArg Subtype.val hdiff
        simpa [a', e', c'] using this
      have hb : ∀ u v : ZMod q, |((u.val : ℕ) : ℤ) - ((v.val : ℕ) : ℤ)| < (q : ℤ) := by
        intro u v
        have hu := ZMod.val_lt u
        have hv := ZMod.val_lt v
        rw [abs_lt]
        constructor <;> omega
      obtain ⟨d1, d2, d3⟩ := hindep _ _ _ hP1
      have z1 := Int.eq_zero_of_abs_lt_dvd d1 (hb i1 j1)
      have z2 := Int.eq_zero_of_abs_lt_dvd d2 (hb i2 j2)
      have z3 := Int.eq_zero_of_abs_lt_dvd d3 (hb i3 j3)
      have f1 : i1 = j1 := ZMod.val_injective q (by omega)
      have f2 : i2 = j2 := ZMod.val_injective q (by omega)
      have f3 : i3 = j3 := ZMod.val_injective q (by omega)
      rw [f1, f2, f3]
    have hcardT : Nat.card (ZMod q × ZMod q × ZMod q) = q ^ 3 := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
      ring
    have h3A : q ^ 3 ≤ Nat.card A := by
      rw [← hcardT]
      exact Nat.card_le_card_of_injective ψ hψinj
    obtain ⟨mA, hmA⟩ := (hPg A).exists_card_eq
    have hmA3 : 3 ≤ mA := by
      by_contra h
      push Not at h
      have h1 : q ^ mA ≤ q ^ 2 := Nat.pow_le_pow_right hqpos (by omega)
      rw [← hmA] at h1
      exact absurd (lt_of_lt_of_le (Nat.pow_lt_pow_right hq1 (by norm_num : 2 < 3)) (h3A.trans h1))
        (lt_irrefl _)
    exact absurd (hrank A hAel mA hmA) (by omega)


theorem index_commutator_le_of_pRank_le_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G}
    (hexp : ∀ g ∈ Q, g ^ q = 1) (hcl : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hr : CFSG.Open.pRank q Q ≤ 2) : ((⁅Q, Q⁆ : Subgroup G).subgroupOf Q).index ≤ q ^ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  have hexpQ : ∀ x : ↥Q, x ^ q = 1 := fun x => Subtype.ext (by simpa using hexp x.1 x.2)
  have hclQ : ∀ a b c : ↥Q, ⁅a, b⁆ * c = c * ⁅a, b⁆ := fun a b c =>
    Subtype.ext (hcl a.1 a.2 b.1 b.2 c.1 c.2)
  have hrankQ : ∀ E : Subgroup ↥Q, CFSG.Open.IsElemAbelian q E → ∀ k : ℕ,
      Nat.card E = q ^ k → k ≤ 2 := by
    intro E hE k hk
    have hE' := CFSG.SectionRank.isElemAbelian_map hE Q.subtype
    have hcard : Nat.card (E.map Q.subtype) = q ^ k := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hk]
    exact (CFSG.SectionRank.le_pRank hq1 (Subgroup.map_subtype_le E) hE' hcard).trans hr
  have hcommQ : (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q).map Q.subtype =
      (⁅Q, Q⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hsub : (⁅Q, Q⁆ : Subgroup G).subgroupOf Q = ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [← hcommQ] at hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
      have hzeq : z = x := Subtype.ext hzx
      rw [← hzeq]
      exact hz
    · intro hx
      rw [← hcommQ]
      exact Subgroup.mem_map_of_mem _ hx
  rw [hsub]
  exact index_commutator_le_P hq2 hexpQ hclQ hrankQ

section EndToGL2

variable {F : Type*} [Field F]

private def embedCoord (d : ℕ) : (Fin d → F) →ₗ[F] (Fin 2 → F) :=
  LinearMap.pi (fun i : Fin 2 => if h : (i : ℕ) < d then LinearMap.proj (R := F)
    (φ := fun _ : Fin d => F) ⟨i, h⟩ else 0)

private def projCoord {d : ℕ} (hd : d ≤ 2) : (Fin 2 → F) →ₗ[F] (Fin d → F) :=
  LinearMap.pi (fun k : Fin d => LinearMap.proj (R := F) (φ := fun _ : Fin 2 => F) (Fin.castLE hd k))

private theorem projCoord_embedCoord {d : ℕ} (hd : d ≤ 2) (v : Fin d → F) :
    projCoord hd (embedCoord d v) = v := by
  funext k
  simp only [projCoord, embedCoord, LinearMap.pi_apply, LinearMap.proj_apply]
  have hk : ((Fin.castLE hd k : Fin 2) : ℕ) < d := by
    simp
  simp [hk]

private def embedEnd {d : ℕ} (hd : d ≤ 2) (L : (Fin d → F) →ₗ[F] (Fin d → F)) :
    (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
  embedCoord d ∘ₗ L ∘ₗ projCoord hd + (LinearMap.id - embedCoord d ∘ₗ projCoord hd)

private theorem embedEnd_apply {d : ℕ} (hd : d ≤ 2) (L : (Fin d → F) →ₗ[F] (Fin d → F))
    (w : Fin 2 → F) :
    embedEnd hd L w = embedCoord d (L (projCoord hd w)) + (w - embedCoord d (projCoord hd w)) := by
  simp [embedEnd]

private theorem embedEnd_mul {d : ℕ} (hd : d ≤ 2) (L M : (Fin d → F) →ₗ[F] (Fin d → F)) :
    embedEnd hd (L * M) = embedEnd hd L * embedEnd hd M := by
  apply LinearMap.ext
  intro w
  have hπx : projCoord hd (embedEnd hd M w) = M (projCoord hd w) := by
    rw [embedEnd_apply, map_add, map_sub, projCoord_embedCoord, projCoord_embedCoord, sub_self,
      add_zero]
  rw [Module.End.mul_apply, embedEnd_apply, embedEnd_apply, hπx, Module.End.mul_apply]
  rw [embedEnd_apply]
  abel

private theorem embedEnd_one {d : ℕ} (hd : d ≤ 2) : embedEnd hd (1 : (Fin d → F) →ₗ[F] (Fin d → F)) = 1 := by
  apply LinearMap.ext
  intro w
  rw [embedEnd_apply, Module.End.one_apply]
  abel

private theorem embedEnd_injective {d : ℕ} (hd : d ≤ 2) (L : (Fin d → F) →ₗ[F] (Fin d → F))
    (hL : embedEnd hd L = 1) : L = 1 := by
  apply LinearMap.ext
  intro v
  have h1 : embedCoord d (L v) = embedCoord d v := by
    have h := LinearMap.congr_fun hL (embedCoord d v)
    rw [embedEnd_apply, projCoord_embedCoord, Module.End.one_apply, sub_self, add_zero] at h
    exact h
  have h2 := congrArg (projCoord hd) h1
  rw [projCoord_embedCoord, projCoord_embedCoord] at h2
  simpa using h2

private theorem exists_GL2_hom_of_end {G₁ : Type*} [Group G₁] {d : ℕ} (hd : d ≤ 2)
    (ρ : G₁ →* ((Fin d → F) →ₗ[F] (Fin d → F))) :
    ∃ φ : G₁ →* Matrix.GeneralLinearGroup (Fin 2) F, ∀ g : G₁, φ g = 1 ↔ ρ g = 1 := by
  let M : Module.End F (Fin d → F) → Matrix (Fin 2) (Fin 2) F :=
    fun L => LinearMap.toMatrix' (embedEnd hd L)
  have hM_mul : ∀ L N, M (L * N) = M L * M N := fun L N => by
    simp only [M, embedEnd_mul, LinearMap.toMatrix'_mul]
  have hT1' : LinearMap.toMatrix' (1 : Module.End F (Fin 2 → F)) = 1 := by
    rw [Module.End.one_eq_id, LinearMap.toMatrix'_id]
  have hM_one : M 1 = 1 := by
    simp only [M, embedEnd_one]
    exact hT1'
  have hM_inj : ∀ L, M L = 1 → L = 1 := by
    intro L hL
    apply embedEnd_injective hd L
    apply LinearMap.toMatrix'.injective
    rw [hT1']
    exact hL
  let φ : G₁ →* Matrix.GeneralLinearGroup (Fin 2) F :=
    { toFun := fun g => Units.mk (M (ρ g)) (M (ρ g⁻¹))
        (by rw [← hM_mul, ← map_mul, mul_inv_cancel, map_one, hM_one])
        (by rw [← hM_mul, ← map_mul, inv_mul_cancel, map_one, hM_one])
      map_one' := Units.ext (by simp [hM_one])
      map_mul' := fun g h => Units.ext (by simp [hM_mul]) }
  refine ⟨φ, fun g => ?_⟩
  constructor
  · intro h
    have h' : M (ρ g) = 1 := by
      have := congrArg Units.val h
      simpa [φ] using this
    exact hM_inj _ h'
  · intro h
    apply Units.ext
    simp [φ, h, hM_one]

end EndToGL2

private theorem ex36_card_eq (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    [Finite V] : Nat.card V = Nat.card K ^ Module.finrank K V := by
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  rw [Nat.card_congr (Module.finBasis K V).equivFun.toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin (Module.finrank K V)), Fintype.card_fin]

private theorem ex36_GL2 (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    [Finite V] {G₁ : Type*} [Group G₁] (hd : Module.finrank K V ≤ 2)
    (ρ : G₁ →* Units (Module.End K V)) :
    ∃ φ : G₁ →* Matrix.GeneralLinearGroup (Fin 2) K, ∀ g : G₁, φ g = 1 ↔ ρ g = 1 := by
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  let b := Module.finBasis K V
  let T : Module.End K V →* Module.End K (Fin (Module.finrank K V) → K) :=
    { toFun := fun f => b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap
      map_one' := LinearMap.ext fun v => b.equivFun.apply_symm_apply v
      map_mul' := fun f f' => LinearMap.ext fun v => by
        show b.equivFun (f (f' (b.equivFun.symm v))) =
          b.equivFun (f (b.equivFun.symm (b.equivFun (f' (b.equivFun.symm v)))))
        rw [LinearEquiv.symm_apply_apply] }
  have hT : ∀ f : Module.End K V, T f = 1 ↔ f = 1 := by
    intro f
    constructor
    · intro hf
      apply LinearMap.ext
      intro v
      apply b.equivFun.injective
      have h2 : b.equivFun (f (b.equivFun.symm (b.equivFun v))) = b.equivFun v :=
        LinearMap.congr_fun hf (b.equivFun v)
      rw [LinearEquiv.symm_apply_apply] at h2
      exact h2
    · intro hf
      rw [hf]
      exact map_one T
  obtain ⟨φ, hφ⟩ := exists_GL2_hom_of_end hd ((T.comp (Units.coeHom (Module.End K V))).comp ρ)
  exact ⟨φ, fun g => (hφ g).trans ((hT ↑(ρ g)).trans Units.val_eq_one)⟩

theorem exists_hom_action {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {J Q : Subgroup G}
    (hexp : ∀ g ∈ Q, g ^ q = 1) (hQJ : J ≤ Subgroup.normalizer (Q : Set G))
    (hidx : ((⁅Q, Q⁆ : Subgroup G).subgroupOf Q).index ≤ q ^ 2) :
    ∃ φ : ↥J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod q), ∀ g : ↥J,
      φ g = 1 ↔ ∀ y ∈ Q, ⁅y, (g : G)⁆ ∈ (⁅Q, Q⁆ : Subgroup G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  have hexpQ : ∀ x : ↥Q, x ^ q = 1 := fun x => Subtype.ext (by simpa using hexp x.1 x.2)
  have hPp : IsPGroup q ↥Q := fun x => ⟨1, by rw [pow_one]; exact hexpQ x⟩
  haveI : Fact (IsPGroup q ↥Q) := ⟨hPp⟩
  have hcommQ : (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q).map Q.subtype =
      (⁅Q, Q⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hsub : (⁅Q, Q⁆ : Subgroup G).subgroupOf Q = ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [← hcommQ] at hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
      have hzeq : z = x := Subtype.ext hzx
      rw [← hzeq]
      exact hz
    · intro hx
      rw [← hcommQ]
      exact Subgroup.mem_map_of_mem _ hx
  have hΦC : frattini ↥Q = ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ := by
    apply le_antisymm
    · rw [frattini_eq_closure_commutator_union_powers (p := q)]
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | ⟨y, rfl⟩)
      · exact hx
      · simp [hexpQ]
    · exact CFSG.commutator_le_frattini_of_isPGroup (p := q) (R := ↥Q)
  have hmemC : ∀ z : ↥Q, z ∈ frattini ↥Q ↔ (z : G) ∈ (⁅Q, Q⁆ : Subgroup G) := by
    intro z
    rw [hΦC, ← hsub, Subgroup.mem_subgroupOf]
  have hindex : (frattini ↥Q).index ≤ q ^ 2 := by
    rw [hΦC, ← hsub]
    exact hidx
  obtain ⟨hchar, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := q) hPp
  haveI hN : (frattini ↥Q).Normal := inferInstance
  letI : CommGroup (↥Q ⧸ frattini ↥Q) := IsMulCommutative.instCommGroup
  have hexpA : ∀ x : Additive (↥Q ⧸ frattini ↥Q), q • x = 0 := fun x => by
    have h1 : Additive.ofMul ((Additive.toMul x) ^ q) = q • x := ofMul_pow q (Additive.toMul x)
    rw [hpow, ofMul_one] at h1
    exact h1.symm
  letI : Module (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)) := AddCommGroup.zmodModule hexpA
  haveI : Finite (Additive (↥Q ⧸ frattini ↥Q)) := inferInstanceAs (Finite (↥Q ⧸ frattini ↥Q))
  have hcardV : Nat.card (Additive (↥Q ⧸ frattini ↥Q)) =
      q ^ Module.finrank (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)) := by
    rw [ex36_card_eq (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)), Nat.card_zmod]
  have hd : Module.finrank (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)) ≤ 2 := by
    have h1 : q ^ Module.finrank (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)) ≤ q ^ 2 := by
      rw [← hcardV]
      exact hindex
    exact (Nat.pow_le_pow_iff_right hq1).1 h1
  let conjQ : ↥J →* MulAut ↥Q := (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQJ)
  have hconj_val : ∀ (g : ↥J) (x : ↥Q), ((conjQ g x : ↥Q) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
    fun g x => rfl
  let act : ↥J →* MulAut (↥Q ⧸ frattini ↥Q) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q)).comp conjQ
  have hact_mk : ∀ (g : ↥J) (x : ↥Q),
      act g (QuotientGroup.mk' (frattini ↥Q) x) = QuotientGroup.mk' (frattini ↥Q) (conjQ g x) :=
    fun g x => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ _ _
  let ρ0 := (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation q act).asGroupHom
  have hker : ρ0.ker = act.ker :=
    CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_kernel q act
  have hρ1 : ∀ g : ↥J, ρ0 g = 1 ↔ act g = 1 := by
    intro g
    have h3 : g ∈ ρ0.ker ↔ g ∈ act.ker := by rw [hker]
    simpa only [MonoidHom.mem_ker] using h3
  have hkey : ∀ (g : ↥J) (x : ↥Q),
      QuotientGroup.mk' (frattini ↥Q) (conjQ g x) = QuotientGroup.mk' (frattini ↥Q) x ↔
        ⁅(x : G), (g : G)⁆ ∈ (⁅Q, Q⁆ : Subgroup G) := by
    intro g x
    have h1 : ⁅(x : G), (g : G)⁆ = ((x * (conjQ g x)⁻¹ : ↥Q) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hconj_val, commutatorElement_def]
      group
    rw [h1, ← hmemC, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    constructor
    · intro h
      have := hN.conj_mem _ h (conjQ g x)
      convert this using 1
      group
    · intro h
      have := hN.conj_mem _ h (conjQ g x)⁻¹
      convert this using 1
      group
  have hact_one : ∀ g : ↥J, act g = 1 ↔ ∀ y ∈ Q, ⁅y, (g : G)⁆ ∈ (⁅Q, Q⁆ : Subgroup G) := by
    intro g
    constructor
    · intro h y hy
      have h1 : act g (QuotientGroup.mk' (frattini ↥Q) ⟨y, hy⟩) =
          QuotientGroup.mk' (frattini ↥Q) ⟨y, hy⟩ := by
        simp [h]
      rw [hact_mk] at h1
      exact (hkey g ⟨y, hy⟩).1 h1
    · intro h
      refine MulEquiv.ext fun z => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥Q) z
      simp only [hact_mk, MulAut.one_apply]
      exact (hkey g x).2 (h x x.2)
  obtain ⟨φ, hφ⟩ := ex36_GL2 (ZMod q) (Additive (↥Q ⧸ frattini ↥Q)) hd ρ0
  refine ⟨φ, fun g => ?_⟩
  rw [hφ g, hρ1 g, hact_one g]


theorem pow_mem_centralizer_of_acts_trivially {q : ℕ} (hq : q.Prime) {Q : Subgroup G}
    (hexp : ∀ g ∈ Q, g ^ q = 1) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hact : ∀ y ∈ Q, ⁅y, g⁆ ∈ (⁅Q, Q⁆ : Subgroup G)) :
    ∃ n : ℕ, g ^ (q ^ n) ∈ Subgroup.centralizer (Q : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hP : IsPGroup q ↥Q := by
    intro x
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hexp x.1 x.2)⟩
  haveI : Fact (IsPGroup q ↥Q) := ⟨hP⟩
  have hconj : ∀ x : ↥Q, (g : G) * (x : G) * (g : G)⁻¹ ∈ Q := fun x =>
    (Subgroup.mem_normalizer_iff.1 hg (x : G)).1 x.2
  have hconj' : ∀ x : ↥Q, (g : G)⁻¹ * (x : G) * (g : G) ∈ Q := fun x => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (x : G)).1 x.2
    simpa [inv_inv] using this
  let σ : MulAut ↥Q :=
    { toFun := fun x => ⟨(g : G) * (x : G) * (g : G)⁻¹, hconj x⟩
      invFun := fun x => ⟨(g : G)⁻¹ * (x : G) * (g : G), hconj' x⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hσ : ∀ x : ↥Q, (((σ x : ↥Q)) : G) = (g : G) * (x : G) * (g : G)⁻¹ := fun x => rfl
  have hcommQ : (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q).map Q.subtype =
      (⁅Q, Q⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hmemc : ∀ z : ↥Q, (z : G) ∈ (⁅Q, Q⁆ : Subgroup G) → z ∈ frattini ↥Q := by
    intro z hz
    rw [← hcommQ] at hz
    obtain ⟨z', hz', hzz⟩ := Subgroup.mem_map.1 hz
    have hz'eq : z' = z := Subtype.ext hzz
    rw [← hz'eq]
    exact (CFSG.commutator_le_frattini_of_isPGroup (p := q) (R := ↥Q)) hz'
  have hker1 : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q) σ = 1 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥Q) z
    have hw : (((σ x)⁻¹ * x : ↥Q) : G) ∈ (⁅Q, Q⁆ : Subgroup G) := by
      have h1 := (⁅Q, Q⁆ : Subgroup G).inv_mem (hact ((x : G))⁻¹ (Q.inv_mem x.2))
      have h2 : (((σ x)⁻¹ * x : ↥Q) : G) = ⁅(x : G)⁻¹, (g : G)⁆⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
        group
      rw [h2]
      exact h1
    show QuotientGroup.mk' (frattini ↥Q) (σ x) = QuotientGroup.mk' (frattini ↥Q) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hmemc _ hw
  obtain ⟨n, hn⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hP).2 ⟨σ, MonoidHom.mem_ker.2 hker1⟩
  have hσn : σ ^ (q ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨n, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  have hpow : ∀ m : ℕ, ∀ x : ↥Q, (((σ ^ m) x : ↥Q) : G) = (g : G) ^ m * (x : G) * ((g : G) ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hσ, ih x]
      group
  intro h hh
  have hx := congrArg (fun y : MulAut ↥Q => (((y ⟨h, hh⟩ : ↥Q)) : G)) hσn
  simp only [MulAut.one_apply] at hx
  rw [hpow] at hx
  have key : (g : G) ^ (q ^ n) * h * ((g : G) ^ (q ^ n))⁻¹ = h := hx
  calc h * (g : G) ^ (q ^ n) = ((g : G) ^ (q ^ n) * h * ((g : G) ^ (q ^ n))⁻¹) * (g : G) ^ (q ^ n) := by
        rw [key]
    _ = (g : G) ^ (q ^ n) * h := by group

theorem le_oPPrimeP_of_pow_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {X J Q : Subgroup G}
    (hJ : GLAPComponent p X J) (hC : J ⊓ Subgroup.centralizer (Q : Set G) ≤ oPPrimeP p J)
    (K : Subgroup ↥J) [K.Normal]
    (hpow : ∀ k ∈ K, ∃ n : ℕ, ((k : ↥J) : G) ^ (q ^ n) ∈ Subgroup.centralizer (Q : Set G)) :
    ∀ k ∈ K, ((k : ↥J) : G) ∈ oPPrimeP p J := by
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥J →* PSimple p J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ g : ↥J, π g = 1 ↔ (g : G) ∈ oPPrimeP p J := by
    intro g
    rw [(pComponent_basic hp hJ).1 g]
    exact (QuotientGroup.eq_one_iff _)
  have hqel : ∀ s ∈ K.map π, ∃ n : ℕ, s ^ (q ^ n) = 1 := by
    rintro s ⟨k, hk, rfl⟩
    obtain ⟨n, hn⟩ := hpow k hk
    refine ⟨n, ?_⟩
    rw [← map_pow]
    refine (hker _).2 ?_
    have hmem : ((k : ↥J) : G) ^ (q ^ n) ∈ oPPrimeP p J :=
      hC (Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ k.2 _, hn⟩)
    simpa using hmem
  haveI : IsSimpleGroup (PSimple p J) := isSimple_pSimple hp hJ
  have hKn : (K.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with hbot | htop
  · intro k hk
    rw [← hker k]
    have hmem : π k ∈ K.map π := Subgroup.mem_map_of_mem π hk
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  ·
    exfalso
    have hqgroup : IsPGroup q (PSimple p J) := by
      intro s
      have hs : s ∈ K.map π := by
        rw [htop]
        exact Subgroup.mem_top s
      exact hqel s hs
    haveI : Nontrivial (Subgroup.center (PSimple p J)) := IsPGroup.center_nontrivial hqgroup
    have hcenter := IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSimple p J))
    obtain ⟨a, b, hab⟩ := pSimple_nonabelian hp hJ
    rcases hcenter with hc | hc
    · obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (PSimple p J))
      apply hz
      apply Subtype.ext
      have hzbot : (z : PSimple p J) ∈ (⊥ : Subgroup (PSimple p J)) := by
        rw [← hc]
        exact z.2
      simpa using Subgroup.mem_bot.1 hzbot
    · have ha : a ∈ Subgroup.center (PSimple p J) := by
        rw [hc]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem exists_hom_GL2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) {X J Q : Subgroup G}
    (hJ : GLAPComponent p X J) (hexp : ∀ g ∈ Q, g ^ q = 1) (hQJ : J ≤ Subgroup.normalizer (Q : Set G))
    (hidx : ((⁅Q, Q⁆ : Subgroup G).subgroupOf Q).index ≤ q ^ 2)
    (hC : J ⊓ Subgroup.centralizer (Q : Set G) ≤ oPPrimeP p J) :
    ∃ φ : ↥J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod q), ∀ g : ↥J, φ g = 1 → (g : G) ∈ oPPrimeP p J := by
  obtain ⟨φ, hφ⟩ := exists_hom_action hq hq2 hexp hQJ hidx
  refine ⟨φ, fun g hg => ?_⟩
  have hpow : ∀ k ∈ φ.ker, ∃ n : ℕ, ((k : ↥J) : G) ^ (q ^ n) ∈ Subgroup.centralizer (Q : Set G) := by
    intro k hk
    exact pow_mem_centralizer_of_acts_trivially hq hexp (hQJ k.2)
      ((hφ k).1 (MonoidHom.mem_ker.1 hk))
  exact le_oPPrimeP_of_pow_mem hp hq hJ hC φ.ker hpow g (MonoidHom.mem_ker.2 hg)

theorem involvedSL2_of_hom {p q : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J)
    (φ : ↥J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod q))
    (hker : ∀ g : ↥J, φ g = 1 → (g : G) ∈ oPPrimeP p J) : InvolvedSL2 q (PSimple p J) := by
  obtain ⟨hmem, -, -, -⟩ := pComponent_basic hp hJ
  let π : ↥J →* PSimple p J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hle : φ.ker ≤ π.ker := by
    intro g hg
    have h1 : (g : G) ∈ oPPrimeP p J := hker g (MonoidHom.mem_ker.1 hg)
    have h2 := (hmem g).1 h1
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 h2
  have hrs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hle' : (φ.rangeRestrict).ker ≤ π.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hle
  refine ⟨φ.range, MonoidHom.liftOfSurjective φ.rangeRestrict hrs ⟨π, hle'⟩, ?_⟩
  intro s
  obtain ⟨g, hg⟩ := hπs s
  refine ⟨φ.rangeRestrict g, ?_⟩
  exact (MonoidHom.liftOfRightInverse_comp_apply φ.rangeRestrict (Function.surjInv hrs)
    (Function.rightInverse_surjInv hrs) ⟨π, hle'⟩ g).trans hg

private theorem mat2_eq_neg_one_of_invol {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (M : Matrix (Fin 2) (Fin 2) (ZMod q)) (hM : M * M = 1) (hne : M ≠ 1) (hdetM : M.det = 1) :
    M = -1 := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    have hdvd := (ZMod.natCast_eq_zero_iff 2 q).1 h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hdvd)
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdetM
  have hfin : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = -1 ∧ M 1 1 = -1 := by
    by_cases hs : M 0 0 + M 1 1 = 0
    · exfalso
      apply h2
      linear_combination -(e00 + hdetM) + M 0 0 * hs
    · have hb : M 0 1 = 0 := by
        have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
        exact (mul_eq_zero.1 this).resolve_right hs
      have hc : M 1 0 = 0 := by
        have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
        exact (mul_eq_zero.1 this).resolve_right hs
      have ha2 : M 0 0 * M 0 0 = 1 := by
        rw [hb, hc] at e00
        linear_combination e00
      have hd2 : M 1 1 * M 1 1 = 1 := by
        rw [hb, hc] at e11
        linear_combination e11
      have hdet' : M 0 0 * M 1 1 = 1 := by
        rw [hb, hc] at hdetM
        linear_combination hdetM
      have had : M 0 0 = M 1 1 := by
        calc M 0 0 = M 0 0 * (M 1 1 * M 1 1) := by rw [hd2, mul_one]
          _ = (M 0 0 * M 1 1) * M 1 1 := by ring
          _ = M 1 1 := by rw [hdet', one_mul]
      rcases mul_self_eq_one_iff.1 ha2 with h1 | h1
      · exfalso
        apply hne
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← had]
      · exact ⟨hb, hc, h1, by rw [← had]; exact h1⟩
  obtain ⟨hb, hc, ha, hd⟩ := hfin
  ext i j
  fin_cases i <;> fin_cases j
  · simp [ha]
  · simp [hb, Matrix.neg_apply, Matrix.one_apply] <;> exact neg_zero.symm
  · simp [hc, Matrix.neg_apply, Matrix.one_apply] <;> exact neg_zero.symm
  · simp [hd]

theorem commutator_top_of_perfect {J : Subgroup G} (h : (⁅J, J⁆ : Subgroup G) = J) :
    (⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ : Subgroup ↥J) = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, h]

private theorem gl2_eq_neg_one_of_invol {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1)
    (hdet : Matrix.GeneralLinearGroup.det g = 1) : g = -1 := by
  have hM : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := by
    have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) =>
      (u : Matrix (Fin 2) (Fin 2) (ZMod q))) hg2
    simpa [sq] using this
  have hdetM : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := by
    have := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hne : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) ≠ 1 := fun h => hg1 (Units.ext h)
  apply Units.ext
  rw [Units.val_neg, Units.val_one]
  exact mat2_eq_neg_one_of_invol hq2 _ hM hne hdetM

theorem exists_central_involution_of_perfect {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) (hperf : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    ∃ h ∈ H, h ≠ 1 ∧ h ^ 2 = 1 ∧ ∀ k ∈ H, k * h = h * k := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hSL : H ≤ (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) →*
      (ZMod q)ˣ).ker := by
    rw [← hperf]
    apply Subgroup.commutator_le.2
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  have heven : Even (Nat.card H) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial H
    change (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) < ⊤ at hlt
    rw [commutator_top_of_perfect hperf] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  set g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) := (x : Matrix.GeneralLinearGroup (Fin 2) (ZMod q))
    with hg
  have hg2 : g ^ 2 = 1 := by
    rw [hg, ← Subgroup.coe_pow, hx2]
    rfl
  have hg1 : g ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hdet : Matrix.GeneralLinearGroup.det g = 1 := MonoidHom.mem_ker.1 (hSL x.2)
  have hgneg : g = -1 := gl2_eq_neg_one_of_invol hq2 hg2 hg1 hdet
  refine ⟨g, x.2, hg1, hg2, fun k _ => ?_⟩
  rw [hgneg]
  simp

private theorem pSimple_proj_spec {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) :
    ∃ π : ↥J →* PSimple p J, Function.Surjective π ∧
      ∀ g : ↥J, π g = 1 ↔ (g : G) ∈ oPPrimeP p J := by
  refine ⟨(QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp
    (QuotientGroup.mk' (GLAPPrimeCore p ↥J)), ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  · intro g
    rw [(pComponent_basic hp hJ).1 g]
    exact QuotientGroup.eq_one_iff _

theorem even_card_core_of_central_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) {H : Type} [Group H] (φ : ↥J →* H)
    (hker : ∀ g : ↥J, φ g = 1 → (g : G) ∈ oPPrimeP p J) {g : ↥J} (hg1 : φ g ≠ 1) (hg2 : φ g ^ 2 = 1)
    (hgc : ∀ k : ↥J, φ k * φ g = φ g * φ k) : Even (Nat.card (GLAPPrimeCoreOf p J)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, hπs, hkerπ⟩ := pSimple_proj_spec hp hJ
  have hcentral : π g = 1 := by
    have hcomm : ∀ k : ↥J, π g * π k = π k * π g := by
      intro k
      have hφc : φ ⁅g, k⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (hgc k).symm
      have hπc : π ⁅g, k⁆ = 1 := (hkerπ _).2 (hker _ hφc)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hπc
      exact hπc
    have hmem : π g ∈ Subgroup.center (PSimple p J) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨k, rfl⟩ := hπs s
      exact (hcomm k).symm
    have hbot := (pComponent_basic hp hJ).2.2.2
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hgmem : (g : G) ∈ oPPrimeP p J := (hkerπ g).1 hcentral
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 2 (by norm_num)
  set t : ↥J := g ^ m with ht
  have ht2 : t ^ (2 ^ e) = 1 := by
    rw [ht, ← pow_mul, show m * 2 ^ e = orderOf g by rw [hn]; ring, pow_orderOf_eq_one]
  have hφt : φ t = φ g := by
    obtain ⟨c, hc⟩ : ∃ c, m = 2 * c + 1 := ⟨m / 2, by omega⟩
    rw [ht, map_pow, hc, pow_succ, pow_mul, hg2, one_pow, one_mul]
  have htne : t ≠ 1 := fun h => hg1 (by rw [← hφt, h, map_one])
  have htmem : ((t : ↥J) : G) ∈ oPPrimeP p J := by
    rw [ht]
    simpa using Subgroup.pow_mem _ hgmem m
  have htcent := (pComponent_basic hp hJ).1 t |>.1 htmem
  have htbar : (QuotientGroup.mk t : PQuot p J) = 1 := by
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_center_quotient hp htcent
    have h2 : (QuotientGroup.mk t : PQuot p J) ^ (2 ^ e) = 1 := by
      rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (p ^ k) (2 ^ e) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hord : orderOf (QuotientGroup.mk t : PQuot p J) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hk
      have h1' := orderOf_dvd_of_pow_eq_one h2
      have hg := Nat.dvd_gcd h1 h1'
      rw [Nat.Coprime.gcd_eq_one hcop] at hg
      exact Nat.dvd_one.1 hg
    exact orderOf_eq_one_iff.1 hord
  have htN : t ∈ GLAPPrimeCore p ↥J := (QuotientGroup.eq_one_iff t).1 htbar
  have hτ : ((t : ↥J) : G) ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype htN
  let τ : ↥(GLAPPrimeCoreOf p J) := ⟨(t : G), hτ⟩
  have hτ2 : τ ^ (2 ^ e) = 1 := by
    apply Subtype.ext
    have := congrArg (fun x : ↥J => (x : G)) ht2
    simpa [τ] using this
  have hτne : τ ≠ 1 := by
    intro h
    apply htne
    apply Subtype.ext
    have := congrArg (fun x : ↥(GLAPPrimeCoreOf p J) => (x : G)) h
    simpa [τ] using this
  have hdvd : orderOf τ ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hτ2
  obtain ⟨i, -, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hτne
    exact orderOf_eq_one_iff.1 (by simpa using hoi)
  have h2 : 2 ∣ orderOf τ := by
    rw [hoi]
    exact dvd_pow_self 2 hi0
  exact even_iff_two_dvd.2 (h2.trans (orderOf_dvd_natCard τ))

theorem even_core_of_hom {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    {X J : Subgroup G} (hJ : GLAPComponent p X J)
    (φ : ↥J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod q))
    (hker : ∀ g : ↥J, φ g = 1 → (g : G) ∈ oPPrimeP p J) :
    Even (Nat.card (GLAPPrimeCoreOf p J)) := by
  obtain ⟨-, hnle, -, -⟩ := pComponent_basic hp hJ
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      commutator_top_of_perfect (glaPComponent_perfect hJ)]
  have hne : φ.range ≠ ⊥ := by
    intro hbot
    apply hnle
    intro g hg
    refine hker ⟨g, hg⟩ ?_
    have : φ ⟨g, hg⟩ ∈ φ.range := ⟨⟨g, hg⟩, rfl⟩
    rw [hbot] at this
    exact (Subgroup.mem_bot.1 this)
  obtain ⟨h, ⟨g, rfl⟩, h1, h2, h3⟩ := exists_central_involution_of_perfect hq hq2 φ.range hperf hne
  exact even_card_core_of_central_lift hp hp2 hJ φ hker h1 h2 (fun k => h3 (φ k) ⟨k, rfl⟩)

section SL2Field

variable {F : Type*} [Field F]

private def NonScalar2 (X : Matrix (Fin 2) (Fin 2) F) : Prop :=
  X 0 1 ≠ 0 ∨ X 1 0 ≠ 0 ∨ X 0 0 ≠ X 1 1

private theorem comm_affine_two {X Y : Matrix (Fin 2) (Fin 2) F} (hX : NonScalar2 X)
    (hXY : X * Y = Y * X) : ∃ α β : F, Y = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X := by
  have c00 : X 0 1 * Y 1 0 = Y 0 1 * X 1 0 := by
    have h := congrFun (congrFun hXY 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have c01 : Y 0 1 * (X 0 0 - X 1 1) = X 0 1 * (Y 0 0 - Y 1 1) := by
    have h := congrFun (congrFun hXY 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have c10 : Y 1 0 * (X 0 0 - X 1 1) = X 1 0 * (Y 0 0 - Y 1 1) := by
    have h := congrFun (congrFun hXY 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination -h
  have key : ∃ α β : F, Y 0 1 = β * X 0 1 ∧ Y 1 0 = β * X 1 0 ∧
      Y 0 0 = α + β * X 0 0 ∧ Y 1 1 = α + β * X 1 1 := by
    rcases hX with hb | hc | hd
    · refine ⟨Y 0 0 - Y 0 1 / X 0 1 * X 0 0, Y 0 1 / X 0 1, ?_, ?_, ?_, ?_⟩
      · rw [div_mul_cancel₀ _ hb]
      · rw [div_mul_eq_mul_div, eq_div_iff hb]
        linear_combination c00
      · ring
      · have h : Y 0 1 / X 0 1 * (X 0 0 - X 1 1) = Y 0 0 - Y 1 1 := by
          rw [div_mul_eq_mul_div, div_eq_iff hb]
          linear_combination c01
        linear_combination h
    · refine ⟨Y 0 0 - Y 1 0 / X 1 0 * X 0 0, Y 1 0 / X 1 0, ?_, ?_, ?_, ?_⟩
      · rw [div_mul_eq_mul_div, eq_div_iff hc]
        linear_combination -c00
      · rw [div_mul_cancel₀ _ hc]
      · ring
      · have h : Y 1 0 / X 1 0 * (X 0 0 - X 1 1) = Y 0 0 - Y 1 1 := by
          rw [div_mul_eq_mul_div, div_eq_iff hc]
          linear_combination c10
        linear_combination h
    · have hd' : X 0 0 - X 1 1 ≠ 0 := sub_ne_zero.2 hd
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1) * X 0 0,
        (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1), ?_, ?_, ?_, ?_⟩
      · rw [div_mul_eq_mul_div, eq_div_iff hd']
        linear_combination c01
      · rw [div_mul_eq_mul_div, eq_div_iff hd']
        linear_combination c10
      · ring
      · have h : (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1) * (X 0 0 - X 1 1) = Y 0 0 - Y 1 1 :=
          div_mul_cancel₀ _ hd'
        linear_combination h
  obtain ⟨α, β, h01, h10, h00, h11⟩ := key
  refine ⟨α, β, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, h11]

private theorem affine_unique_two {X : Matrix (Fin 2) (Fin 2) F} (hX : NonScalar2 X)
    {α β α' β' : F} (h : α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X =
      α' • (1 : Matrix (Fin 2) (Fin 2) F) + β' • X) : α = α' ∧ β = β' := by
  have e01 : β * X 0 1 = β' * X 0 1 := by
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), mul_zero, zero_add] at h01
    exact h01
  have e10 : β * X 1 0 = β' * X 1 0 := by
    have h10 := congrFun (congrFun h 1) 0
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, zero_add] at h10
    exact h10
  have e00 : α + β * X 0 0 = α' + β' * X 0 0 := by
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one] at h00
    exact h00
  have e11 : α + β * X 1 1 = α' + β' * X 1 1 := by
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one] at h11
    exact h11
  have hββ : β = β' := by
    rcases hX with hb | hc | hd
    · exact mul_right_cancel₀ hb e01
    · exact mul_right_cancel₀ hc e10
    · have : (β - β') * (X 0 0 - X 1 1) = 0 := by linear_combination e00 - e11
      rcases mul_eq_zero.1 this with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd (sub_eq_zero.1 h1) hd
  subst hββ
  exact ⟨by linear_combination e00, rfl⟩

private theorem affine_mul_two (X : Matrix (Fin 2) (Fin 2) F)
    (hXX : X * X = X.trace • X - 1) (α β α' β' : F) :
    (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X) * (α' • (1 : Matrix (Fin 2) (Fin 2) F) + β' • X) =
      (α * α' - β * β') • (1 : Matrix (Fin 2) (Fin 2) F) +
        (α * β' + β * α' + β * β' * X.trace) • X := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hXX]
  module

private theorem det_affine_two (X : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X).det =
      α * α + α * β * X.trace + β * β * X.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp
  ring

private theorem affine_pow_of_sq_zero (ε : F) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0)
    (m : ℕ) : (ε • (1 : Matrix (Fin 2) (Fin 2) F) + N) ^ (m + 1) =
      ε ^ (m + 1) • (1 : Matrix (Fin 2) (Fin 2) F) + (((m : F) + 1) * ε ^ m) • N := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hN,
      smul_zero, add_zero]
    module

private theorem false_of_trace_two_mul {X : Matrix (Fin 2) (Fin 2) F} (hX : NonScalar2 X)
    (hdet : X.det = 1) {ε : F} (hε : ε * ε = 1) (htr : X.trace = 2 * ε) {p : ℕ} (hp : 0 < p)
    (hpow : X ^ p = 1) (hp0 : (p : F) ≠ 0) : False := by
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hXX : X * X = X.trace • X - 1 := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one X hdet
  set N : Matrix (Fin 2) (Fin 2) F := X - ε • (1 : Matrix (Fin 2) (Fin 2) F) with hNdef
  have hNN : N * N = 0 := by
    have h1 : N * N = X * X - (2 * ε) • X + (ε * ε) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hNdef]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
      module
    rw [h1, hXX, htr, hε]
    module
  have hXN : X = ε • (1 : Matrix (Fin 2) (Fin 2) F) + N := by
    rw [hNdef]
    abel
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [hXN, affine_pow_of_sq_zero ε N hNN m] at hpow
  set c : F := ((m : F) + 1) * ε ^ m with hcdef
  have hc : c ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ hε0)
    intro h
    apply hp0
    push_cast
    exact h
  have h2 : c • N = 1 - ε ^ (m + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hpow
  have hNs : N = (c⁻¹ * (1 - ε ^ (m + 1))) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc N = c⁻¹ • (c • N) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • (1 - ε ^ (m + 1) • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h2]
      _ = (c⁻¹ * (1 - ε ^ (m + 1))) • (1 : Matrix (Fin 2) (Fin 2) F) := by module
  have hXs : X = (ε + c⁻¹ * (1 - ε ^ (m + 1))) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hXN, hNs]
    module
  rw [hXs] at hX
  rcases hX with h | h | h <;> simp [Matrix.one_apply] at h

private theorem exists_theta_sq_ne_one {X : Matrix (Fin 2) (Fin 2) F} (hX : NonScalar2 X)
    (hdet : X.det = 1) {p : ℕ} (hp : 0 < p) (hpow : X ^ p = 1) (hp0 : (p : F) ≠ 0) :
    ∃ θ : AlgebraicClosure F, θ * θ = algebraMap F (AlgebraicClosure F) X.trace * θ - 1 ∧
      θ * θ ≠ 1 := by
  set t : AlgebraicClosure F := algebraMap F (AlgebraicClosure F) X.trace with ht
  have hdeg2 : (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 :
      Polynomial (AlgebraicClosure F)).degree = 2 := by
    compute_degree!
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 :
      Polynomial (AlgebraicClosure F)).degree ≠ 0 := by
    rw [hdeg2]
    norm_num
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root _ hdeg
  have hquad : θ * θ = t * θ - 1 := by
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one] at hθ
    linear_combination hθ
  refine ⟨θ, hquad, fun h1 => ?_⟩
  rcases mul_self_eq_one_iff.1 h1 with h2 | h2
  ·
    have ht2 : t = 2 := by
      rw [h2] at hquad
      linear_combination -hquad
    have htr : X.trace = 2 * 1 := by
      rw [mul_one]
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [map_ofNat]
      exact ht2
    exact false_of_trace_two_mul hX hdet (by norm_num) htr hp hpow hp0
  ·
    have ht2 : t = -2 := by
      rw [h2] at hquad
      linear_combination hquad
    have htr : X.trace = 2 * (-1) := by
      rw [show (2 : F) * (-1) = -2 by ring]
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [map_neg, map_ofNat]
      exact ht2
    exact false_of_trace_two_mul hX hdet (by norm_num) htr hp hpow hp0

private theorem exists_injective_eigen_hom {X : Matrix (Fin 2) (Fin 2) F} (hX : NonScalar2 X)
    (hdet : X.det = 1) {θ : AlgebraicClosure F}
    (hquad : θ * θ = algebraMap F (AlgebraicClosure F) X.trace * θ - 1) (hθ2 : θ * θ ≠ 1)
    (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hcomm : ∀ Y ∈ S, X * (Y : Matrix (Fin 2) (Fin 2) F) = (Y : Matrix (Fin 2) (Fin 2) F) * X) :
    ∃ φ : S →* (AlgebraicClosure F)ˣ, Function.Injective φ := by
  classical
  have hXX : X * X = X.trace • X - 1 := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one X hdet
  have hex : ∀ Y : S, ∃ α β : F,
      (Y : Matrix (Fin 2) (Fin 2) F) = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • X :=
    fun Y => comm_affine_two hX (hcomm Y Y.2)
  choose α β hαβ using hex
  set T : AlgebraicClosure F := algebraMap F (AlgebraicClosure F) X.trace with hT
  have hθ0 : θ ≠ 0 := by
    intro h
    rw [h] at hquad
    simp at hquad
  have hθi : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
  have hsum : θ + θ⁻¹ = T := by
    field_simp
    linear_combination hquad
  have hne : θ ≠ θ⁻¹ := by
    intro h
    apply hθ2
    calc θ * θ = θ * θ⁻¹ := by rw [← h]
      _ = 1 := hθi
  have hdetK : ∀ Y : S, algebraMap F (AlgebraicClosure F) (α Y) * algebraMap F (AlgebraicClosure F) (α Y) +
      algebraMap F (AlgebraicClosure F) (α Y) * algebraMap F (AlgebraicClosure F) (β Y) * T +
      algebraMap F (AlgebraicClosure F) (β Y) * algebraMap F (AlgebraicClosure F) (β Y) = 1 := by
    intro Y
    have hd : (Y : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe (Y : Matrix.SpecialLinearGroup (Fin 2) F)
      exact this
    rw [hαβ Y, det_affine_two, hdet] at hd
    have := congrArg (algebraMap F (AlgebraicClosure F)) hd
    simp only [map_add, map_mul, map_one, hT] at this ⊢
    linear_combination this
  let μ : S → AlgebraicClosure F := fun Y => algebraMap F (AlgebraicClosure F) (α Y) + algebraMap F (AlgebraicClosure F) (β Y) * θ
  let ν : S → AlgebraicClosure F := fun Y => algebraMap F (AlgebraicClosure F) (α Y) + algebraMap F (AlgebraicClosure F) (β Y) * θ⁻¹
  have hμν : ∀ Y : S, μ Y * ν Y = 1 := by
    intro Y
    have h := hdetK Y
    simp only [μ, ν]
    linear_combination h + (algebraMap F (AlgebraicClosure F) (α Y) * algebraMap F (AlgebraicClosure F) (β Y)) * hsum
      + (algebraMap F (AlgebraicClosure F) (β Y) * algebraMap F (AlgebraicClosure F) (β Y)) * hθi
  have hμ0 : ∀ Y : S, μ Y ≠ 0 := fun Y h => by
    have := hμν Y
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hμmul : ∀ Y Y' : S, μ (Y * Y') = μ Y * μ Y' := by
    intro Y Y'
    have hprod : (Y * Y' : S) = Y * Y' := rfl
    have hYY : ((Y * Y' : S) : Matrix (Fin 2) (Fin 2) F) =
        (Y : Matrix (Fin 2) (Fin 2) F) * (Y' : Matrix (Fin 2) (Fin 2) F) := rfl
    have hmat : ((Y * Y' : S) : Matrix (Fin 2) (Fin 2) F) =
        (α Y * α Y' - β Y * β Y') • (1 : Matrix (Fin 2) (Fin 2) F) +
          (α Y * β Y' + β Y * α Y' + β Y * β Y' * X.trace) • X := by
      rw [hYY, hαβ Y, hαβ Y', affine_mul_two X hXX]
    have huniq := affine_unique_two hX ((hαβ (Y * Y')).symm.trans hmat)
    simp only [μ]
    rw [huniq.1, huniq.2]
    simp only [map_add, map_mul, map_sub, hT]
    linear_combination (-(algebraMap F (AlgebraicClosure F) (β Y) * algebraMap F (AlgebraicClosure F) (β Y'))) * hquad
  have hμinj : ∀ Y : S, μ Y = 1 → Y = 1 := by
    intro Y h1
    have h2 : ν Y = 1 := by
      have := hμν Y
      rw [h1, one_mul] at this
      exact this
    have hb : algebraMap F (AlgebraicClosure F) (β Y) * (θ - θ⁻¹) = 0 := by
      simp only [μ, ν] at h1 h2
      linear_combination h1 - h2
    have hb0 : algebraMap F (AlgebraicClosure F) (β Y) = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hne
    have ha : algebraMap F (AlgebraicClosure F) (α Y) = 1 := by
      simp only [μ] at h1
      rw [hb0, zero_mul, add_zero] at h1
      exact h1
    have hβ : β Y = 0 := by
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [hb0, map_zero]
    have hα : α Y = 1 := by
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [ha, map_one]
    apply Subtype.ext
    apply Subtype.ext
    rw [hαβ Y, hβ, hα, zero_smul, one_smul, add_zero]
    rfl
  let φ : S →* (AlgebraicClosure F)ˣ :=
    { toFun := fun Y => Units.mk0 (μ Y) (hμ0 Y)
      map_one' := by
        ext
        simp only [Units.val_one, Units.val_mk0]
        have hm : μ 1 = 1 := by
          have hu := affine_unique_two hX ((hαβ 1).symm.trans
            (show ((1 : S) : Matrix (Fin 2) (Fin 2) F) = (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) +
              (0 : F) • X by simp))
          simp only [μ]
          rw [hu.1, hu.2]
          simp
        exact hm
      map_mul' := fun Y Y' => by
        ext
        simp only [Units.val_mul, Units.val_mk0]
        exact hμmul Y Y' }
  refine ⟨φ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro Y hY
  apply hμinj Y
  have := congrArg Units.val hY
  simpa [φ] using this

end SL2Field

theorem isCyclic_of_isPGroup_SL2 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) (hP : IsPGroup p P) : IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  by_cases hpq : p = q
  ·
    subst hpq
    obtain ⟨m, hm⟩ := hP.exists_card_eq
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
      rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
      have h2 : p ^ 2 - p = p * (p - 1) := by
        rw [sq, Nat.mul_sub_one]
      have hpos : 0 < p - 1 := by have := hp.two_le; omega
      simp only [pow_zero, pow_one, Fin.val_zero, Fin.val_one]
      rw [h2, show (p ^ 2 - 1) * (p * (p - 1)) = (p * (p ^ 2 - 1)) * (p - 1) by ring,
        Nat.mul_div_cancel _ hpos]
    have hdvd : p ^ m ∣ p * (p ^ 2 - 1) := by
      rw [← hm, ← hSL]
      exact Subgroup.card_subgroup_dvd_card P
    have hm1 : m ≤ 1 := by
      by_contra h
      push Not at h
      have h2 : p ^ 2 ∣ p * (p ^ 2 - 1) := (pow_dvd_pow p h).trans hdvd
      have h3 : p ∣ p ^ 2 - 1 := by
        have h2' : p * p ∣ p * (p ^ 2 - 1) := by
          rw [← sq]
          exact h2
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos h2'
      have h4 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have h5 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h4 h3
      have h6 : p ^ 2 - (p ^ 2 - 1) = 1 := by
        have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
        omega
      rw [h6] at h5
      exact hp.one_lt.ne' (Nat.dvd_one.1 h5)
    interval_cases m
    ·
      have h1 : Nat.card P = 1 := by rw [hm, pow_zero]
      haveI : Subsingleton P := Nat.card_eq_one_iff_unique.1 h1 |>.1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by rw [hm, pow_one])
  ·
    by_cases htriv : Subsingleton P
    · exact isCyclic_of_subsingleton
    have hnt : Nontrivial P := not_subsingleton_iff_nontrivial.1 htriv
    have hZp : IsPGroup p (Subgroup.center P) := fun x => by
      obtain ⟨k, hk⟩ := hP x.1
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    haveI : Nontrivial (Subgroup.center P) := by
      haveI := hP.center_nontrivial
      exact this
    obtain ⟨kZ, hkZ⟩ := hZp.exists_card_eq
    have hpdvd : p ∣ Nat.card (Subgroup.center P) := by
      rw [hkZ]
      apply dvd_pow_self p
      rintro rfl
      rw [pow_zero] at hkZ
      exact not_subsingleton _ (Nat.card_eq_one_iff_unique.1 hkZ).1
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    set z : P := (w : P) with hzdef
    have hzc : z ∈ Subgroup.center P := w.2
    have hzord : orderOf z = p := (Subgroup.orderOf_coe w).trans hw
    have hzpow : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzord
      exact hp.one_lt.ne' hzord.symm
    set X : Matrix (Fin 2) (Fin 2) (ZMod q) :=
      ((z : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) with hXdef
    have hdet : X.det = 1 := Matrix.SpecialLinearGroup.det_coe _
    have hzSL : (z : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) ^ p = 1 := by
      have h := congrArg (fun g : P => (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) hzpow
      simpa using h
    have hXpow : X ^ p = 1 := by
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) =>
        (g : Matrix (Fin 2) (Fin 2) (ZMod q))) hzSL
      simpa [Matrix.SpecialLinearGroup.coe_pow] using h
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro h
      have hdvd := (ZMod.natCast_eq_zero_iff p q).1 h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd).symm
    have hns : NonScalar2 X := by
      by_contra hcon
      have h01 : X 0 1 = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h10 : X 1 0 = 0 := by
        by_contra h
        exact hcon (Or.inr (Or.inl h))
      have h00 : X 0 0 = X 1 1 := by
        by_contra h
        exact hcon (Or.inr (Or.inr h))
      have hXs : X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]
      have hc2 : X 0 0 * X 0 0 = 1 := by
        have h := hdet
        rw [hXs, Matrix.det_smul, Matrix.det_one, mul_one] at h
        simpa [sq] using h
      have hcp : X 0 0 ^ p = 1 := by
        have h := hXpow
        rw [hXs, smul_pow, one_pow] at h
        have h' := congrFun (congrFun h 0) 0
        simpa using h'
      have hc1 : X 0 0 = 1 := by
        rcases mul_self_eq_one_iff.1 hc2 with h | h
        · exact h
        · rw [h, Odd.neg_one_pow hodd] at hcp
          rw [h]
          exact hcp
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      change X = ((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
      rw [hXs, hc1, one_smul]
      rfl
    have hcomm : ∀ Y ∈ P, X * (Y : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        (Y : Matrix (Fin 2) (Fin 2) (ZMod q)) * X := by
      intro Y hY
      have h := Subgroup.mem_center_iff.1 hzc ⟨Y, hY⟩
      have h2 := congrArg (fun g : P =>
        ((g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))) h
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
      exact h2.symm
    obtain ⟨θ, hquad, hθ2⟩ := exists_theta_sq_ne_one hns hdet hp.pos hXpow hp0
    obtain ⟨φ, hφinj⟩ := exists_injective_eigen_hom hns hdet hquad hθ2 P hcomm
    haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
    exact isCyclic_of_injective φ.rangeRestrict (fun a b h => hφinj (congrArg Subtype.val h))

theorem pRank_le_one_of_involvedSL2 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (hinv : InvolvedSL2 q S) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨H, φ, hφ⟩ := hinv
  have hperfS : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have hm : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.1 hm
    · exact h
  have hcs : ∀ s : S, ∃ y ∈ (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H), φ y = s := by
    intro s
    have hmap : (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H).map φ = ⊤ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ, hperfS]
    have hs : s ∈ (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H).map φ := by
      rw [hmap]
      exact Subgroup.mem_top s
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 hs
    exact ⟨y, hy, hys⟩
  have hdetH : ∀ y ∈ (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H),
      Matrix.GeneralLinearGroup.det (y : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) = 1 := by
    have hle : (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) ≤
        (Matrix.GeneralLinearGroup.det.comp H.subtype).ker := by
      apply Subgroup.commutator_le.2
      intro a _ b _
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_commutatorElement, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    intro y hy
    exact MonoidHom.mem_ker.1 (hle hy)
  have hE_bound : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ 1 := by
    intro E hE
    let M : Subgroup H :=
      Subgroup.comap φ E ⊓ (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H)
    let f : M →* E := (φ.comp M.subtype).codRestrict E (fun m => (Subgroup.mem_inf.1 m.2).1)
    have hsurj : Function.Surjective f := by
      intro e
      obtain ⟨y, hy, hye⟩ := hcs e.1
      refine ⟨⟨y, Subgroup.mem_inf.2 ⟨?_, hy⟩⟩, Subtype.ext hye⟩
      rw [Subgroup.mem_comap, hye]
      exact e.2
    obtain ⟨Sy⟩ : Nonempty (Sylow p M) := Sylow.nonempty
    let Q : Sylow p E := Sylow.mapSurjective hsurj Sy
    have hTop : IsPGroup p (⊤ : Subgroup E) := fun x => by
      refine ⟨1, ?_⟩
      rw [pow_one]
      apply Subtype.ext
      apply Subtype.ext
      simpa using hE.2 _ x.1.2
    have hQtop : (Q : Subgroup E) = ⊤ := (Q.is_maximal' hTop le_top).symm
    have hmapTop : (Sy : Subgroup M).map f = ⊤ := by
      have h1 : (Q : Subgroup E) = (Sy : Subgroup M).map f := by
        rw [show (Q : Subgroup E) = ((Sylow.mapSurjective hsurj Sy : Sylow p E) : Subgroup E) from rfl,
          Sylow.coe_mapSurjective]
      rw [← h1]
      exact hQtop
    have hdetM : ∀ x : (Sy : Subgroup M),
        Matrix.GeneralLinearGroup.det ((x.1.1 : H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) = 1 :=
      fun x => hdetH _ (Subgroup.mem_inf.1 x.1.2).2
    have hSLmem : ∀ x : (Sy : Subgroup M),
        ((((x.1.1 : H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) :
          Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := by
      intro x
      have h := congrArg Units.val (hdetM x)
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
      exact h
    let ψ : (Sy : Subgroup M) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
      { toFun := fun x => ⟨(((x.1.1 : H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)), hSLmem x⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun x y => Subtype.ext rfl }
    have hψinj : Function.Injective ψ := by
      intro x y hxy
      have h1 : ((x.1.1 : H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) =
          ((y.1.1 : H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :=
        Units.ext (congrArg Subtype.val hxy)
      have h2 : x.1.1 = y.1.1 := Subtype.ext h1
      exact Subtype.ext (Subtype.ext h2)
    have hψpow : ∀ x : (Sy : Subgroup M), ∃ k : ℕ, ψ x ^ (p ^ k) = 1 := by
      intro x
      obtain ⟨k, hk⟩ := Sy.isPGroup' x
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hPsp : IsPGroup p ↥ψ.range := by
      rintro ⟨g, hg⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hg
      obtain ⟨k, hk⟩ := hψpow x
      exact ⟨k, Subtype.ext hk⟩
    have hcycPs : IsCyclic ↥ψ.range := isCyclic_of_isPGroup_SL2 hp hp2 hq ψ.range hPsp
    have hcycSy : IsCyclic ↥(Sy : Subgroup M) :=
      isCyclic_of_injective ψ.rangeRestrict (fun a b h => hψinj (congrArg Subtype.val h))
    have hcycE : IsCyclic E := by
      haveI := hcycSy
      let g : (Sy : Subgroup M) →* E := f.comp (Sy : Subgroup M).subtype
      have hg : Function.Surjective g := by
        intro e
        have he : e ∈ (Sy : Subgroup M).map f := by
          rw [hmapTop]
          exact Subgroup.mem_top e
        obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.1 he
        exact ⟨⟨m, hm⟩, hme⟩
      exact isCyclic_of_surjective g hg
    obtain ⟨gE, hgE⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hcycE
    have hgpow : gE ^ p = 1 := by
      apply Subtype.ext
      simpa using hE.2 _ gE.2
    have hdvd : orderOf gE ∣ p := orderOf_dvd_of_pow_eq_one hgpow
    rw [pow_one, ← hgE]
    exact Nat.le_of_dvd hp.pos hdvd
  exact CFSG.SectionRank.pRank_le hp.one_lt (k := 1) (fun E _ hE => hE_bound E hE)

theorem card_le_pow_pRank_aut {p : ℕ} (hp : p.Prime) {X L B : Subgroup G} (hL : GLAPComponent p X L)
    (hB : IsElemAbelian p B) (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card B ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) *
      Nat.card ↥(B ⊓ centModSubgroup p L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  let φ : ↥B' →* MulAut (PSimple p L) := (L62.phiC p L).domRestrict B'
  have hker : ∀ b : ↥B', b ∈ φ.ker ↔ (((b : ↥N) : G) ∈ centModSubgroup p L) := by
    intro b
    rw [MonoidHom.mem_ker, ← centMod_iff]
    exact L62.phiC_eq_one_iff hp hL (b : ↥N).2
  have hkercard : Nat.card φ.ker = Nat.card ↥(B ⊓ centModSubgroup p L) := by
    have hinj : Function.Injective (N.subtype.comp B'.subtype) :=
      N.subtype_injective.comp B'.subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    congr 2
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(Subgroup.mem_subgroupOf.1 b.2), (hker b).1 hb⟩
    · rintro ⟨hgB, hgc⟩
      have hgN : g ∈ N := hgc.1
      exact ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, (hker _).2 hgc, rfl⟩
  have hB'card : Nat.card ↥B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥B' := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  have hA : IsElemAbelian p φ.range := by
    rw [MonoidHom.domRestrict_range]
    exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hB N) (L62.phiC p L)
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hA hk
  rw [hkercard, hB'card] at h1
  rw [← h1, hk, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos hkle)

theorem three_le_pRank_Q₁ {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G p)
    (h713 : GL83.I_7_13_1) (hC : Contra92 p B x L q Q₁) : 3 ≤ CFSG.Open.pRank q Q₁ := by
  by_contra hlt
  push Not at hlt
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hq : q.Prime := hC.setup.prime
  have hq2 : q ≠ 2 := hC.setup.ne_two
  have hidx := index_commutator_le_of_pRank_le_two hq hq2 hC.setup.exp hC.setup.class_two (by omega)
  have hQJ : L ≤ Subgroup.normalizer (Q₁ : Set G) :=
    fun l hl => hC.setup.char (Subgroup.le_normalizer hl)
  obtain ⟨φ, hφ⟩ := exists_hom_GL2 hp hq hq2 hC.h.comp hC.setup.exp hQJ hidx hC.setup.cent
  have hinv := involvedSL2_of_hom hp hC.h.comp φ hφ
  have hS : IsSimpleGroup (PSimple p L) := isSimple_pSimple hp hC.h.comp
  have hnc : ∃ a b : PSimple p L, a * b ≠ b * a := pSimple_nonabelian hp hC.h.comp
  have hpr := pRank_le_one_of_involvedSL2 hp hp2 hq hq2 hS hnc hinv
  have hcat : IsCatalogGroup (PSimple p L) := by
    rcases hC.h.chev2 with ⟨i, -, hf⟩ | ⟨i, -, hf⟩
    · exact ⟨i, hf⟩
    · exact ⟨i, hf⟩
  have h2 := (h713 p hp hp2 (PSimple p L) hS hnc hcat hpr).2
  have h3 := card_le_pow_pRank_aut hp hC.h.comp hC.h.bmax.1 hC.h.norm
  have h4 := hC.h.pow_four_le hc
  rw [hC.h.card_inf_centMod hp] at h3
  have h5 : p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) ≤ p ^ 2 :=
    Nat.pow_le_pow_right hp.pos h2
  have h6 : Nat.card B ≤ p ^ 2 * p := h3.trans (Nat.mul_le_mul_right _ h5)
  have h7 : p ^ 4 ≤ p ^ 2 * p := h4.trans h6
  have h8 : p ^ 2 * p = p ^ 3 := by ring
  rw [h8] at h7
  have := Nat.pow_lt_pow_right hp.one_lt (show 3 < 4 by norm_num)
  omega

end CFSG.LocalAnalysis.GLTheoremA.S9

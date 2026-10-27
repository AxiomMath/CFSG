module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

@[expose] def I2611Printed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ K B : Subgroup X,
    K = GLAPLayer p (⊤ : Subgroup X) →
    IsKHat (PQuot p K) → Odd (Nat.card (GLAPPrimeCoreOf p K)) →
    IsElemAbelian p B → K ⊔ B = ⊤ →
    (∃ T : Subgroup X, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set X)) →
    Nat.card B = p ^ GLATwoLocalRank p X → 4 ≤ GLATwoLocalRank p X →
    (∃ b ∈ B, b ≠ 1 ∧ CentMod p K b) → CFSG.Open.pRank p (oPPrimeP p K) ≤ 1 →
    IsGB p B K ∨ ∃ A : Subgroup X, GLAIsBmax p A ∧ ¬ (A ⊓ K ≤ oPPrimeP p K) ∧
      ∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ K, a = u * v

@[expose] def I2611Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ K B : Subgroup X, K.Normal →
    GLAPPrimeCore p ↥K = ⊥ → IsKHat ↥K → IsCyclic (Subgroup.center ↥K) →
    IsElemAbelian p B → Nat.card B = p ^ GLATwoLocalRank p X → 4 ≤ GLATwoLocalRank p X →
    (∃ T : Subgroup X, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set X)) →
    (∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (K : Set X)) →
    IsGB p B K ∨ ∃ A : Subgroup X, GLAIsBmax p A ∧ (∃ u ∈ A ⊓ K, ∃ y ∈ K, u * y ≠ y * u) ∧
      ∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ K, a = u * v

namespace I2611

section Aux

variable {G : Type} [Group G] [Finite G]

theorem commutator_top_le_of_sup_eq_top {M : Type*} [Group M] {K B : Subgroup M} [K.Normal]
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hKB : K ⊔ B = ⊤) :
    ⁅(⊤ : Subgroup M), ⊤⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ K ⊔ B := hKB ▸ Subgroup.mem_top x
  have hy : y ∈ K ⊔ B := hKB ▸ Subgroup.mem_top y
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx hy
  obtain ⟨k₁, hk₁, b₁, hb₁, rfl⟩ := hx
  obtain ⟨k₂, hk₂, b₂, hb₂, rfl⟩ := hy
  have h1 : QuotientGroup.mk' K k₁ = 1 := (QuotientGroup.eq_one_iff _).2 hk₁
  have h2 : QuotientGroup.mk' K k₂ = 1 := (QuotientGroup.eq_one_iff _).2 hk₂
  have h3 : QuotientGroup.mk' K b₁ * QuotientGroup.mk' K b₂ =
      QuotientGroup.mk' K b₂ * QuotientGroup.mk' K b₁ := by
    rw [← map_mul, ← map_mul, hB b₁ hb₁ b₂ hb₂]
  rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, commutatorElement_def]
  simp only [map_mul, map_inv, h1, h2, one_mul]
  rw [h3]
  group

theorem glaPLayer_top_subgroupOf {p : ℕ} (hp : p.Prime) {J B : Subgroup G}
    (hJ : GLAPComponent p (J ⊔ B) J) (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) :
    GLAPLayer p (⊤ : Subgroup ↥(J ⊔ B)) = J.subgroupOf (J ⊔ B) := by
  set H := J ⊔ B with hH
  have hJH : J ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hBJ
  haveI : (J.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).2 hHN
  have hKB : J.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJH,
      Subgroup.map_subgroupOf_eq_of_le hBH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hBc : ∀ a ∈ B.subgroupOf H, ∀ b ∈ B.subgroupOf H, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hB a (Subgroup.mem_subgroupOf.1 ha) b (Subgroup.mem_subgroupOf.1 hb))
  have hc := commutator_top_le_of_sup_eq_top (K := J.subgroupOf H) hBc hKB
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    calc L = ⁅L, L⁆ := (glaPComponent_perfect hL).symm
      _ ≤ ⁅(⊤ : Subgroup ↥H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ _ := hc
  · exact le_sSup (glaPComponent_top_subgroupOf hp hJ)

theorem glaIsBmax_map_subtype {p : ℕ} {H : Subgroup G} {A : Subgroup ↥H} (hA : GLAIsBmax p A)
    (hrank : GLATwoLocalRank p ↥H = GLATwoLocalRank p G) : GLAIsBmax p (A.map H.subtype) := by
  obtain ⟨hAel, hAcard, U, hU, hU2, hAU⟩ := hA
  refine ⟨CFSG.SectionRank.isElemAbelian_map hAel H.subtype, ?_, U.map H.subtype, ?_,
    hU2.map _, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hAcard, hrank]
  · intro h
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U H.subtype_injective).1 h)
  · exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map H.subtype)

theorem glaPLayer_map_ne_bot {A A' : Type*} [Group A] [Group A'] [Finite A] {p : ℕ}
    (hp : p.Prime) (f : A →* A') (hf : Function.Injective f) {Y : Subgroup A}
    (h : GLAPLayer p Y ≠ ⊥) : GLAPLayer p (Y.map f) ≠ ⊥ := by
  intro h0
  apply h
  rw [eq_bot_iff]
  refine sSup_le fun L hL => ?_
  have hker : Nat.Coprime p (Nat.card ↥(Y ⊓ f.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have h1 := glaPComponent_map hp f hker hL
  have h2 : L.map f ≤ ⊥ := h0 ▸ le_sSup h1
  have h3 : L.map f = ⊥ := le_bot_iff.1 h2
  exact (Subgroup.map_eq_bot_iff_of_injective L hf).1 h3 ▸ le_rfl

theorem card_le_of_pow_eq_one_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {p : ℕ}
    (hp : 0 < p) (S : Subgroup Z) (hS : ∀ x ∈ S, x ^ p = 1) : Nat.card S ≤ p := by
  haveI : IsCyclic S := Subgroup.isCyclic S
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S)
  have h1 : Nat.card S = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hS g g.2))
  exact h1 ▸ Nat.le_of_dvd hp h2

theorem subgroupOf_sup_sup_eq_top (J B : Subgroup G) :
    J.subgroupOf (J ⊔ B) ⊔ B.subgroupOf (J ⊔ B) = ⊤ := by
  apply Subgroup.map_injective (J ⊔ B).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_oPPrimeP_of_central {p : ℕ} {K : Subgroup G} {k : G} (hk : k ∈ K)
    (hc : ∀ y ∈ K, k * y = y * k) (hp : k ^ p = 1) : k ∈ oPPrimeP p K := by
  set z : PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨k, hk⟩ with hz
  have hzc : ∀ y : PQuot p K, z * y = y * z := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      show QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨k, hk⟩ * QuotientGroup.mk' _ y =
        QuotientGroup.mk' _ y * QuotientGroup.mk' _ ⟨k, hk⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hc y y.2))
  have hzp : z ^ p = 1 := by
    rw [hz, ← map_pow]
    have : (⟨k, hk⟩ : ↥K) ^ p = 1 := Subtype.ext (by simpa using hp)
    rw [this, map_one]
  have hnorm : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h := (Commute.zpow_left (show Commute z g from hzc g) m).eq
    rw [← h, mul_inv_cancel_right]
    exact hn
  have hpg : IsPGroup p (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  have hle : Subgroup.zpowers z ≤ CFSG.pCore p (PQuot p K) := le_sSup ⟨hnorm, hpg⟩
  exact ⟨⟨k, hk⟩, hle (Subgroup.mem_zpowers z), rfl⟩

theorem pCore_le_center_of_isQuasisimple {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    (hq : CFSG.Open.IsQuasisimple Q) : CFSG.pCore p Q ≤ Subgroup.center Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_center_of_normal_of_isQuasisimple hq inferInstance ?_
  intro htop
  have hPG : IsPGroup p Q := by
    have h1 := CFSG.pCore_isPGroup (p := p) (G := Q)
    rw [htop] at h1
    exact h1.of_equiv Subgroup.topEquiv
  haveI : Nontrivial Q := isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect Q := ⟨hq.1⟩
  haveI : Group.IsNilpotent Q := hPG.isNilpotent
  exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem pRank_oPPrimeP_le_one {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot p K)) (hcyc : IsCyclic (Subgroup.center (PQuot p K))) :
    CFSG.Open.pRank p (oPPrimeP p K) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hcyc
  set Q := PQuot p K with hQ
  have hpc : CFSG.pCore p Q ≤ Subgroup.center Q := pCore_le_center_of_isQuasisimple hp hq
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEle hEel => ?_
  rw [pow_one]
  have hEK : E ≤ K := hEle.trans (Subgroup.map_subtype_le _)
  set φ : ↥E →* Q := (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hEK) with hφ
  have hφc : ∀ e : ↥E, φ e ∈ Subgroup.center Q := by
    intro e
    apply hpc
    obtain ⟨k, hk, hke⟩ := hEle e.2
    have : k = Subgroup.inclusion hEK e := Subtype.ext hke
    rw [this] at hk
    exact hk
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at he
    set k : ↥K := Subgroup.inclusion hEK e with hk
    have hkp : k ^ p = 1 := Subtype.ext (by
      have := hEel.2 (e : G) e.2
      simpa [hk] using this)
    have h1 : orderOf k ∣ p := orderOf_dvd_of_pow_eq_one hkp
    have h2 : orderOf k ∣ Nat.card (GLAPPrimeCore p ↥K) := by
      have := Subgroup.orderOf_dvd_natCard (GLAPPrimeCore p ↥K) he
      simpa using this
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
    have h3 : orderOf k = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h4 : k = 1 := orderOf_eq_one_iff.1 h3
    rw [Subgroup.mem_bot]
    apply Subgroup.inclusion_injective hEK
    rw [map_one]
    exact h4
  set g : ↥E →* ↥(Subgroup.center Q) := φ.codRestrict _ hφc with hg
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hcard : Nat.card E = Nat.card g.range :=
    Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
  rw [hcard]
  refine card_le_of_pow_eq_one_of_isCyclic hp.pos _ ?_
  rintro _ ⟨e, rfl⟩
  rw [← map_pow]
  have : e ^ p = 1 := Subtype.ext (by simpa using hEel.2 (e : G) e.2)
  rw [this, map_one]

theorem isCatalogGroup_center_quotient' {Y : Type*} [Group Y] (hY : CFSG.Open.IsKGroup Y)
    (hq : CFSG.Open.IsQuasisimple Y) : IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  refine hY.isCatalogGroup_of_surjective ⊤
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq)
    ((QuotientGroup.mk' (Subgroup.center Y)).comp (⊤ : Subgroup Y).subtype) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩

end Aux

section Coprime

variable {A Q : Type*} [Group A] [Group Q]

theorem exists_mem_ker_mul_commute_of_isPGroup {p : ℕ} (hp : p.Prime) (ψ : A →* Q)
    (hN : ¬ p ∣ Nat.card ψ.ker) {E : Subgroup A} (hE : IsPGroup p E) {k : A}
    (hk : ∀ e ∈ E, ψ k * ψ e = ψ e * ψ k) : ∃ n ∈ ψ.ker, ∀ e ∈ E, k * n * e = e * (k * n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ g ∈ E, ∀ o ∈ ψ.ker, k⁻¹ * (g * (k * o) * g⁻¹) ∈ ψ.ker := by
    intro g hg o ho
    rw [MonoidHom.mem_ker] at ho ⊢
    have h1 : ψ g * ψ k * (ψ g)⁻¹ = ψ k := by
      rw [← hk g hg, mul_inv_cancel_right]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ho, mul_one, h1, inv_mul_cancel]
  letI act : MulAction E ψ.ker :=
    { smul := fun g o => ⟨k⁻¹ * ((g : A) * (k * (o : A)) * (g : A)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show k⁻¹ * (((1 : E) : A) * (k * (o : A)) *
          ((1 : E) : A)⁻¹) = (o : A) by simp)
      mul_smul := fun g h o => Subtype.ext (show k⁻¹ * (((g * h : E) : A) * (k * (o : A)) *
          ((g * h : E) : A)⁻¹) = k⁻¹ * ((g : A) * (k * (k⁻¹ * ((h : A) * (k * (o : A)) *
          (h : A)⁻¹))) * (g : A)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨o, ho⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card ψ.ker hN
  refine ⟨o, o.2, fun e he => ?_⟩
  have hfa : k⁻¹ * (e * (k * (o : A)) * e⁻¹) = o :=
    congrArg Subtype.val (ho ⟨e, he⟩)
  have h2 : e * (k * (o : A)) * e⁻¹ = k * o := by
    calc e * (k * (o : A)) * e⁻¹ = k * (k⁻¹ * (e * (k * (o : A)) * e⁻¹)) := by group
      _ = k * o := by rw [hfa]
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

theorem map_inf_centralizer_of_isPGroup {p : ℕ} (hp : p.Prime) {ψ : A →* Q}
    (hN : ¬ p ∣ Nat.card ψ.ker) {K E : Subgroup A} (hK : ψ.ker ≤ K) (hE : IsPGroup p E) :
    K.map ψ ⊓ Subgroup.centralizer ((E.map ψ : Subgroup Q) : Set Q) =
      (K ⊓ Subgroup.centralizer (E : Set A)).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hk, rfl⟩, hC⟩
    obtain ⟨n, hn, hkn⟩ := exists_mem_ker_mul_commute_of_isPGroup hp ψ hN hE (k := k) (fun e he =>
      (Subgroup.mem_centralizer_iff.1 hC (ψ e) ⟨e, he, rfl⟩).symm)
    refine ⟨k * n, ⟨K.mul_mem hk (hK hn), Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩, ?_⟩
    · exact (hkn e he).symm
    · rw [map_mul, MonoidHom.mem_ker.1 hn, mul_one]
  · rintro _ ⟨c, ⟨hcK, hcC⟩, rfl⟩
    refine ⟨⟨c, hcK, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hcC e he)]

end Coprime

section Helpers

theorem glaPLayer_top_normal (p : ℕ) {X : Type} [Group X] [Finite X] :
    (GLAPLayer p (⊤ : Subgroup X)).Normal := by
  have hle : ∀ g : X, GLBConj g (GLAPLayer p (⊤ : Subgroup X)) ≤ GLAPLayer p (⊤ : Subgroup X) := by
    intro g
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 := glaPComponent_gLBConj hL g
    have e : GLBConj g (⊤ : Subgroup X) = ⊤ :=
      top_unique fun y _ => mem_gLBConj.2 (Subgroup.mem_top _)
    rw [e] at h1
    exact le_sSup h1
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ ∈ GLBConj g⁻¹ (GLAPLayer p (⊤ : Subgroup X)) := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hn
  exact hle g⁻¹ h1

theorem card_map_eq_of_disjoint_ker {A Q : Type*} [Group A] [Group Q] (ψ : A →* Q)
    {S : Subgroup A} (h : Disjoint S ψ.ker) : Nat.card (S.map ψ) = Nat.card S := by
  have hinj : Function.Injective (ψ.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have h1 : (s : A) ∈ S ⊓ ψ.ker := ⟨s.2, hs⟩
    rw [h.eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hr : (ψ.comp S.subtype).range = S.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isElemAbelian_of_disjoint_ker {A Q : Type*} [Group A] [Group Q] (ψ : A →* Q) {p : ℕ}
    {S : Subgroup A} (h : Disjoint S ψ.ker) (hS : IsElemAbelian p (S.map ψ)) :
    IsElemAbelian p S := by
  have hS1 := hS.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hab : ∀ x ∈ S, ∀ y ∈ S, ψ x * ψ y = ψ y * ψ x := by
      intro x hx y hy
      have := mul_comm' (⟨ψ x, x, hx, rfl⟩ : ↥(S.map ψ)) ⟨ψ y, y, hy, rfl⟩
      simpa using congrArg Subtype.val this
    show (a : A) * b = b * a
    have h1 : ψ ((a : A) * b * ((b : A) * a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hab a a.2 b b.2]
      group
    have h3 : ((a : A) * b * ((b : A) * a)⁻¹ : A) ∈ S ⊓ ψ.ker :=
      ⟨S.mul_mem (S.mul_mem a.2 b.2) (S.inv_mem (S.mul_mem b.2 a.2)), h1⟩
    rw [h.eq_bot, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  · have h1 : ψ (x ^ p) = 1 := by
      rw [map_pow]
      exact hS.2 (ψ x) ⟨x, hx, rfl⟩
    have h3 : x ^ p ∈ S ⊓ ψ.ker := ⟨S.pow_mem hx p, h1⟩
    rw [h.eq_bot, Subgroup.mem_bot] at h3
    exact h3

theorem glaPLayer_ne_bot_of_map {A A' : Type*} [Group A] [Group A'] [Finite A] {p : ℕ}
    (hp : p.Prime) (ψ : A →* A') {Y : Subgroup A} (hker : Nat.Coprime p (Nat.card ↥(Y ⊓ ψ.ker)))
    (h : GLAPLayer p (Y.map ψ) ≠ ⊥) : GLAPLayer p Y ≠ ⊥ := by
  intro h0
  apply h
  rw [eq_bot_iff]
  refine sSup_le fun L' hL' => ?_
  obtain ⟨L, hL, hLmap⟩ := exists_glaPComponent_map_eq hp ψ hker hL'
  have h1 : L ≤ ⊥ := h0 ▸ le_sSup hL
  rw [le_bot_iff.1 h1, Subgroup.map_bot] at hLmap
  exact hLmap ▸ le_rfl

theorem mem_normalizer_inf' {A : Type*} [Group A] {S T : Subgroup A} {g : A}
    (hS : g ∈ Subgroup.normalizer (S : Set A)) (hT : g ∈ Subgroup.normalizer (T : Set A)) :
    g ∈ Subgroup.normalizer ((S ⊓ T : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hS hT ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hS h) (hT h)

end Helpers

section Quot

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_center_of_pPrimeCore_eq_bot' {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (h : CFSG.pPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  intro z
  obtain ⟨a, m, hpm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (z : Y)).ne' p hp.ne_one
  refine ⟨a, Subtype.ext ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Y, y = (z : Y) ^ p ^ a := ⟨_, rfl⟩
  have hyc : y ∈ Subgroup.center Y := hy ▸ Subgroup.pow_mem _ z.2 _
  have hym : y ^ m = 1 := by rw [hy, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hym)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hN : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ Subgroup.center Y := (Subgroup.zpowers_le.2 hyc) hn
    rw [Subgroup.mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn
  have hle : Subgroup.zpowers y ≤ CFSG.pPrimeCore p Y := le_sSup ⟨hN, hcop⟩
  rw [h] at hle
  have h1 : y = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers y))
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, h1]

theorem isPGroup_center_pQuot' {p : ℕ} (hp : p.Prime) (K : Subgroup X) :
    IsPGroup p (Subgroup.center (PQuot p K)) :=
  isPGroup_center_of_pPrimeCore_eq_bot' hp (glaPPrimeCore_quotient_eq_bot hp)

theorem exists_elemAbelian_center_pQuot' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Subgroup X) (hnc : ¬ IsCyclic (Subgroup.center (PQuot p K))) :
    ∃ U : Subgroup (PQuot p K), U ≤ Subgroup.center (PQuot p K) ∧ IsElemAbelian p U ∧
      Nat.card U = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p (Subgroup.center (PQuot p K))) := ⟨isPGroup_center_pQuot' hp K⟩
  obtain ⟨E, -, hcard, hE⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hE
  haveI : CFSG.IsElementaryAbelian p (E.map (Subgroup.center (PQuot p K)).subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  refine ⟨E.map (Subgroup.center (PQuot p K)).subtype, Subgroup.map_subtype_le E,
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]

theorem isCyclic_center_pQuot_of_pRank_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (h : CFSG.Open.pRank p (oPPrimeP p K) ≤ 1) :
    IsCyclic (Subgroup.center (PQuot p K)) := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hUc, hUel, hUcard⟩ := exists_elemAbelian_center_pQuot' hp hp2 K hnc
  have hNc : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥K) hNc hUel
  have hZle : Subgroup.center (PQuot p K) ≤ CFSG.pCore p (PQuot p K) :=
    le_sSup ⟨inferInstance, isPGroup_center_pQuot' hp K⟩
  have hle : S.map K.subtype ≤ oPPrimeP p K := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) s ∈ U := hSmap ▸ ⟨s, hs, rfl⟩
    exact ⟨s, hZle (hUc h1), rfl⟩
  have h3 : 2 ≤ CFSG.Open.pRank p (oPPrimeP p K) :=
    CFSG.SectionRank.le_pRank hp.one_lt hle (CFSG.SectionRank.isElemAbelian_map hSel K.subtype)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective, hScard, hUcard])
  omega

theorem map_mem_center_of_mem_oPPrimeP {p : ℕ} (hp : p.Prime) {K : Subgroup X} {K' : Type*}
    [Group K'] (f : ↥K →* K') (hf : Function.Surjective f) (hker : f.ker = GLAPPrimeCore p ↥K)
    (hq : CFSG.Open.IsQuasisimple (PQuot p K)) {w : X} (hw : w ∈ oPPrimeP p K) :
    ∃ hwK : w ∈ K, f ⟨w, hwK⟩ ∈ Subgroup.center K' := by
  obtain ⟨k, hk, rfl⟩ := hw
  refine ⟨k.2, ?_⟩
  have hc : QuotientGroup.mk' (GLAPPrimeCore p ↥K) k ∈ Subgroup.center (PQuot p K) :=
    pCore_le_center_of_isQuasisimple hp hq hk
  rw [Subgroup.mem_center_iff]
  intro y'
  obtain ⟨y, rfl⟩ := hf y'
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⁅y, k⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk' (GLAPPrimeCore p ↥K) y)
    rw [this]
    group
  have h2 : ⁅y, k⁆ ∈ f.ker := by
    rw [hker]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have h3 : f ⁅y, k⁆ = 1 := h2
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  have h4 : f y * f k * (f y)⁻¹ = f k := mul_inv_eq_one.1 h3
  calc f y * f k = f y * f k * (f y)⁻¹ * f y := by group
    _ = f k * f y := by rw [h4]

end Quot

section Lift

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_normal {N : Subgroup X} [N.Normal] (g : X) :
    g ∈ Subgroup.normalizer (N : Set X) :=
  (Subgroup.normalizer_eq_top_iff.2 ‹N.Normal›).symm ▸ Subgroup.mem_top g

theorem lift_isGB {p : ℕ} (hp : p.Prime) {K B N : Subgroup X} [N.Normal] (hNK : N ≤ K)
    (hNp : ¬ p ∣ Nat.card N) (hBel : IsElemAbelian p B) [hKn : K.Normal]
    (h : IsGB p (B.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N))) : IsGB p B K := by
  obtain ⟨Eb, hEbB, hEbel, hEbc, hEbN, hEbL⟩ := h
  set π := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hBdisj : Disjoint B π.ker := by
    rw [hker]
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hBel
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp))
  set E : Subgroup X := B ⊓ Eb.comap π with hE
  have hEB : E ≤ B := inf_le_left
  have hEmap : E.map π = Eb := by
    apply le_antisymm
    · rintro _ ⟨e, ⟨-, he⟩, rfl⟩
      exact he
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hEbB hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hEel : IsElemAbelian p E := isElemAbelian_mono hBel hEB
  have hEcard : Nat.card E = p ^ 3 := by
    rw [← hEbc, ← hEmap]
    exact (card_map_eq_of_disjoint_ker π (hBdisj.mono_left hEB)).symm
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEel
  refine ⟨E, hEB, hEel, hEcard, fun g _ => mem_normalizer_of_normal g, ?_⟩
  have hcent := map_inf_centralizer_of_isPGroup hp (ψ := π) (by rw [hker]; exact hNp) (K := K)
    (E := E) (by rw [hker]; exact hNK) hEp
  rw [hEmap] at hcent
  have h1 : GLAPLayer p ((K ⊓ Subgroup.centralizer (E : Set X)).map π) ≠ ⊥ := by
    rw [← hcent]
    exact hEbL
  refine glaPLayer_ne_bot_of_map hp π ?_ h1
  rw [hker]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
    hNp (hd.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem lift_bmax {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B N : Subgroup X} [N.Normal]
    [hKn : K.Normal] (hNK : N ≤ K) (hNp : ¬ p ∣ Nat.card N) (hBel : IsElemAbelian p B)
    (hrk : GLATwoLocalRank p (X ⧸ N) = GLATwoLocalRank p X)
    (hZ : ∀ w ∈ oPPrimeP p K, ∀ y ∈ K.map (QuotientGroup.mk' N),
      y * QuotientGroup.mk' N w = QuotientGroup.mk' N w * y)
    {Ab : Subgroup (X ⧸ N)} (hAb : GLAIsBmax p Ab)
    (hnc : ∃ u ∈ Ab ⊓ K.map (QuotientGroup.mk' N), ∃ y ∈ K.map (QuotientGroup.mk' N),
      u * y ≠ y * u)
    (hdec : ∀ a ∈ Ab, ∃ u ∈ Ab ⊓ B.map (QuotientGroup.mk' N),
      ∃ v ∈ Ab ⊓ K.map (QuotientGroup.mk' N), a = u * v) :
    ∃ A : Subgroup X, GLAIsBmax p A ∧ ¬ (A ⊓ K ≤ oPPrimeP p K) ∧
      ∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ K, a = u * v := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  haveI hKbn : (K.map π).Normal := Subgroup.Normal.map hKn π hsurj
  obtain ⟨hAel, hAcard, Ub, hUb, hUb2, hAUb⟩ := hAb
  have hmemN : ∀ n ∈ N, π n = 1 := fun n hn => (QuotientGroup.eq_one_iff n).2 hn
  set D : Subgroup X := B ⊓ Ab.comap π with hD
  set E' : Subgroup X := (Ab ⊓ K.map π).comap π with hE'
  have hDB : D ≤ B := inf_le_left
  have hDp : IsPGroup p D := isPGroup_of_isElemAbelian (isElemAbelian_mono hBel hDB)
  have hOE : N ≤ E' := fun n hn => by
    show π n ∈ Ab ⊓ K.map π
    rw [hmemN n hn]
    exact (Ab ⊓ K.map π).one_mem
  have hEN : E' ≤ Subgroup.normalizer (N : Set X) := fun g _ => mem_normalizer_of_normal g
  have hEp : ∀ e ∈ E', ∃ k : ℕ, e ^ (p ^ k) ∈ N := by
    intro e he
    refine ⟨1, ?_⟩
    have h1 : (π e) ^ p = 1 := hAel.2 (π e) he.1
    rw [pow_one, ← hker, MonoidHom.mem_ker, map_pow]
    exact h1
  have hDE : D ≤ Subgroup.normalizer (E' : Set X) := by
    intro d hd
    have h1 : d ∈ Subgroup.normalizer ((Ab.comap π : Subgroup X) : Set X) :=
      Subgroup.le_normalizer hd.2
    haveI : ((K.map π).comap π).Normal := Subgroup.Normal.comap hKbn π
    have h2 : d ∈ Subgroup.normalizer (((K.map π).comap π : Subgroup X) : Set X) :=
      mem_normalizer_of_normal d
    have hE'eq : E' = Ab.comap π ⊓ (K.map π).comap π := Subgroup.comap_inf _ _ _
    rw [hE'eq]
    exact mem_normalizer_inf' h1 h2
  have hENO : E' ≤ K ⊔ N := by
    intro e he
    obtain ⟨k, hk, hke⟩ := he.2
    have h1 : k⁻¹ * e ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hke, inv_mul_cancel]
    have h2 : e = k * (k⁻¹ * e) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup hk h1
  obtain ⟨W, hWle, hWp, hDW, hWsup⟩ := exists_pGroup_lift hp hNp hOE hEN hEp hDp hDE
    (fun g _ => mem_normalizer_of_normal g) (fun g _ => mem_normalizer_of_normal g) hENO
  have hWK : W ≤ K := (hWle : W ≤ K ⊓ E').trans inf_le_left
  have hπW : W.map π = Ab ⊓ K.map π := by
    have h1 : (W ⊔ N).map π = W.map π ⊔ N.map π := Subgroup.map_sup _ _ _
    have h2 : N.map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 hker.ge
    have h3 : E'.map π = Ab ⊓ K.map π := Subgroup.map_comap_eq_self_of_surjective hsurj _
    rw [← h3, ← hWsup, h1, h2, sup_bot_eq]
  set A : Subgroup X := D ⊔ W with hA
  have hDA : D ≤ A := le_sup_left
  have hWA : W ≤ A := le_sup_right
  have hApow : ∃ c : ℕ, Nat.card A = p ^ c := by
    obtain ⟨w, hw⟩ := hWp.exists_card_eq
    obtain ⟨d, hd⟩ := hDp.exists_card_eq
    have h1 := card_sup_mul_card_inf_of_le_normalizer hDW
    rw [hw, hd, ← pow_add] at h1
    have h2 : Nat.card (W ⊔ D : Subgroup X) ∣ p ^ (w + d) := Dvd.intro _ h1
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 h2
    exact ⟨c, by rw [hA, sup_comm]; exact hc⟩
  obtain ⟨c, hc⟩ := hApow
  have hAdisj : Disjoint A π.ker := by
    rw [hker]
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hc]
      exact Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp))
  have hπA : A.map π = Ab := by
    apply le_antisymm
    · rw [hA, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨d, hd, rfl⟩
        exact hd.2
      · rw [hπW]
        exact inf_le_left
    · intro a ha
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec a ha
      refine Subgroup.mul_mem _ ?_ ?_
      · obtain ⟨b, hb, hbu⟩ := hu.2
        refine ⟨b, hDA ⟨hb, ?_⟩, hbu⟩
        show π b ∈ Ab
        rw [hbu]
        exact hu.1
      · have hv' : v ∈ W.map π := hπW ▸ hv
        obtain ⟨w, hw, hwv⟩ := hv'
        exact ⟨w, hWA hw, hwv⟩
  have hAelem : IsElemAbelian p A := isElemAbelian_of_disjoint_ker π hAdisj (hπA ▸ hAel)
  have hAcardeq : Nat.card A = p ^ GLATwoLocalRank p X := by
    rw [← hrk, ← hAcard, ← hπA]
    exact (card_map_eq_of_disjoint_ker π hAdisj).symm
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hAelem
  set T' : Subgroup X := Ub.comap π with hT'
  have hNT' : N ≤ T' := fun n hn => by
    show π n ∈ Ub
    rw [hmemN n hn]
    exact Ub.one_mem
  have hNT : N < T' := by
    refine lt_of_le_of_ne hNT' fun h => hUb ?_
    have h1 : Ub = T'.map π := (Subgroup.map_comap_eq_self_of_surjective hsurj Ub).symm
    rw [h1, ← h]
    exact (Subgroup.map_eq_bot_iff _).2 hker.ge
  have hT'2 : ∀ t ∈ T', ∃ k : ℕ, t ^ (2 ^ k) ∈ N := by
    intro t ht
    obtain ⟨k, hk⟩ := hUb2 ⟨π t, ht⟩
    refine ⟨k, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_pow]
    simpa using congrArg Subtype.val hk
  have hAT' : A ≤ Subgroup.normalizer (T' : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show π h ∈ Ub ↔ π (a * h * a⁻¹) ∈ Ub
    rw [map_mul, map_mul, map_inv]
    have haA : π a ∈ Subgroup.normalizer (Ub : Set (X ⧸ N)) := hAUb (hπA ▸ ⟨a, ha, rfl⟩)
    exact Subgroup.mem_normalizer_iff.1 haA (π h)
  obtain ⟨T, -, hT1, hT2, hAT⟩ := exists_two_subgroup_lift hp hp2 hNp hNT
    (fun g _ => mem_normalizer_of_normal g) hT'2 hAp hAT'
  refine ⟨A, ⟨hAelem, hAcardeq, T, hT1, hT2, hAT⟩, ?_, ?_⟩
  ·
    intro hle
    obtain ⟨u, hu, y, hy, hne⟩ := hnc
    have hu' : u ∈ W.map π := hπW ▸ hu
    obtain ⟨w, hw, rfl⟩ := hu'
    exact hne (hZ w (hle ⟨hWA hw, hWK hw⟩) y hy).symm
  · intro a ha
    rw [hA, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D W hDW] at ha
    obtain ⟨d, hd, w, hw, rfl⟩ := ha
    exact ⟨d, ⟨hDA hd, hDB hd⟩, w, ⟨hWA hw, hWK hw⟩, rfl⟩

end Lift

section Basic

theorem card_eq_card_inf_ker_mul_card_map {A Q : Type*} [Group A] [Group Q] (ψ : A →* Q)
    (S : Subgroup A) : Nat.card S = Nat.card ↥(S ⊓ ψ.ker) * Nat.card ↥(S.map ψ) := by
  have h := Subgroup.card_ker_mul_card_range (ψ.comp S.subtype)
  have hr : (ψ.comp S.subtype).range = S.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥(ψ.comp S.subtype).ker ≃ ↥(S ⊓ ψ.ker) :=
    { toFun := fun x => ⟨(x.1 : A), x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [hr] at h
  rw [← h, Nat.card_congr e]

variable {X : Type} [Group X] [Finite X]

theorem exists_glaIsBmax' {p : ℕ} (hp : 1 < p) (h : 0 < GLATwoLocalRank p X) :
    ∃ B : Subgroup X, GLAIsBmax p B := by
  classical
  set S : Set ℕ := {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}
  have hS : GLATwoLocalRank p X = sSup S := rfl
  have hne : S.Nonempty := by
    by_contra hS'
    rw [Set.not_nonempty_iff_eq_empty] at hS'
    rw [hS, hS'] at h
    simp at h
  obtain ⟨H, hH, hHk⟩ := Nat.sSup_mem hne (bddAbove_twoLocalPRanks hp)
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp H
  obtain ⟨P, hP, hP2, rfl⟩ := hH
  refine ⟨E, hE, ?_, P, hP, hP2, hEH⟩
  rw [hEc, hHk, ← hS]

theorem ker_conjNormal (K : Subgroup X) [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut ↥K => (φ ⟨y, hy⟩ : X)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    ext ⟨y, hy⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h y hy).symm

theorem conjNormal_eq_conj_iff (K : Subgroup X) [K.Normal] (x : X) (k : ↥K) :
    MulAut.conjNormal (H := K) x = MulAut.conj k ↔ ∀ y ∈ K, x * y * x⁻¹ = (k : X) * y * (k : X)⁻¹ := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut ↥K => (φ ⟨y, hy⟩ : X)) h
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using h1
  · intro h
    ext ⟨y, hy⟩
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using h y hy

theorem le_normalizer_of_commute {S T : Subgroup X} (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    S ≤ Subgroup.normalizer (T : Set X) := fun s hs => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : s * h * s⁻¹ = h := by rw [mul_inv_eq_iff_eq_mul]; exact hc s hs h hh
    rw [this]
    exact hh
  · intro hh
    have h1 : s * (s * h * s⁻¹) * s⁻¹ = s * h * s⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]; exact hc s hs _ hh
    have h2 : s * h * s⁻¹ = h := by
      have h3 : s * (s * h * s⁻¹ * s⁻¹) = s * (h * s⁻¹) := by
        calc s * (s * h * s⁻¹ * s⁻¹) = s * (s * h * s⁻¹) * s⁻¹ := by group
          _ = s * h * s⁻¹ := h1
          _ = s * (h * s⁻¹) := by group
      exact mul_right_cancel (mul_left_cancel h3)
    rw [← h2]
    exact hh

theorem isElemAbelian_sup_of_commute {p : ℕ} {S T : Subgroup X} (hS : IsElemAbelian p S)
    (hT : IsElemAbelian p T) (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    IsElemAbelian p (S ⊔ T) := by
  have hST := le_normalizer_of_commute hc
  have hS1 := hS.1
  have hT1 := hT.1
  have hmem : ∀ x ∈ S ⊔ T, ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S T hST] at hx
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    exact ⟨s, hs, t, ht, rfl⟩
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨s, hs, t, ht, hab⟩ := hmem a a.2
    obtain ⟨s', hs', t', ht', hbb⟩ := hmem b b.2
    show (a : X) * b = b * a
    have e1 : s * s' = s' * s := mul_comm' (⟨s, hs⟩ : ↥S) ⟨s', hs'⟩ |> fun h => by simpa using congrArg Subtype.val h
    have e2 : t * t' = t' * t := mul_comm' (⟨t, ht⟩ : ↥T) ⟨t', ht'⟩ |> fun h => by simpa using congrArg Subtype.val h
    rw [hab, hbb]
    calc s * t * (s' * t') = s * (t * s') * t' := by group
      _ = s * (s' * t) * t' := by rw [← hc s' hs' t ht]
      _ = (s * s') * (t * t') := by group
      _ = (s' * s) * (t' * t) := by rw [e1, e2]
      _ = s' * (s * t') * t := by group
      _ = s' * (t' * s) * t := by rw [hc s hs t' ht']
      _ = s' * t' * (s * t) := by group
  · obtain ⟨s, hs, t, ht, rfl⟩ := hmem x hx
    have hcomm : Commute s t := hc s hs t ht
    rw [hcomm.mul_pow, hS.2 s hs, hT.2 t ht, one_mul]

theorem card_le_of_le_center {K S : Subgroup X} (hcyc : IsCyclic (Subgroup.center ↥K)) {p : ℕ}
    (hp : 0 < p) (hSK : S ≤ K) (hSc : S ≤ Subgroup.centralizer (K : Set X))
    (hS : ∀ s ∈ S, s ^ p = 1) : Nat.card S ≤ p := by
  haveI := hcyc
  set S' : Subgroup ↥K := S.subgroupOf K with hS'
  have hS'c : S' ≤ Subgroup.center ↥K := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_centralizer_iff.1 (hSc (Subgroup.mem_subgroupOf.1 hs)) g g.2
    exact Subtype.ext h1
  have h1 : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have h2 : Nat.card (S'.subgroupOf (Subgroup.center ↥K)) = Nat.card S' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'c).toEquiv
  rw [← h1, ← h2]
  refine card_le_of_pow_eq_one_of_isCyclic hp _ ?_
  intro x hx
  have h3 : ((x : ↥(Subgroup.center ↥K)) : ↥K) ∈ S' := hx
  have h4 : (((x : ↥(Subgroup.center ↥K)) : ↥K) : X) ∈ S := Subgroup.mem_subgroupOf.1 h3
  apply Subtype.ext
  apply Subtype.ext
  simpa using hS _ h4

structure CoreCtx (p : ℕ) (K B : Subgroup X) [K.Normal] : Prop where
  prime : p.Prime
  odd : p ≠ 2
  core : GLAPPrimeCore p ↥K = ⊥
  hat : IsKHat ↥K
  cyc : IsCyclic (Subgroup.center ↥K)
  elem : IsElemAbelian p B
  card : Nat.card B = p ^ GLATwoLocalRank p X
  four : 4 ≤ GLATwoLocalRank p X
  two : ∃ T : Subgroup X, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set X)
  cent : ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (K : Set X)

namespace CoreCtx

variable {p : ℕ} {K B : Subgroup X} [K.Normal]

abbrev B0 (K B : Subgroup X) : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X)

theorem B0_elem (c : CoreCtx p K B) : IsElemAbelian p (B0 K B) := isElemAbelian_mono c.elem inf_le_left

theorem center_isPGroup (c : CoreCtx p K B) : IsPGroup p (Subgroup.center ↥K) :=
  isPGroup_center_of_pPrimeCore_eq_bot' c.prime c.core

theorem p_dvd_card (c : CoreCtx p K B) : p ∣ Nat.card ↥K := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  by_contra h
  have hcop : Nat.Coprime p (Nat.card ↥(⊤ : Subgroup ↥K)) := by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd c.prime).2 h
  have hle : (⊤ : Subgroup ↥K) ≤ GLAPPrimeCore p ↥K := le_sSup ⟨inferInstance, hcop⟩
  rw [c.core] at hle
  haveI : Nontrivial ↥K := isQuasisimple_nontrivial c.hat.1
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥K
  exact hab (by
    have ha := Subgroup.mem_bot.1 (hle (Subgroup.mem_top a))
    have hb := Subgroup.mem_bot.1 (hle (Subgroup.mem_top b))
    rw [ha, hb])

theorem glaPLayer_ne_bot (c : CoreCtx p K B) : GLAPLayer p K ≠ ⊥ := by
  have hq : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq c.core).trans QuotientGroup.quotientBot).symm c.hat.1
  have h := (glaPLayer_of_isQuasisimple hq).2.2
  intro h0
  rw [h0] at h
  have h1 : barX p K (⊥ : Subgroup X) = ⊥ := by
    unfold barX
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [h1] at h
  haveI : Nontrivial (↥K ⧸ GLAPPrimeCore p ↥K) := isQuasisimple_nontrivial hq
  exact bot_ne_top h

end CoreCtx

theorem core_isGB_of_card_ge {p : ℕ} {K B : Subgroup X} [K.Normal] (c : CoreCtx p K B)
    (h : p ^ 3 ≤ Nat.card (CoreCtx.B0 K B)) : IsGB p B K := by
  have hB0p : IsPGroup p (CoreCtx.B0 K B) := isPGroup_of_isElemAbelian c.B0_elem
  obtain ⟨H', -, hH'⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card c.prime hB0p
    (H := (⊤ : Subgroup ↥(CoreCtx.B0 K B))) (by rwa [Subgroup.card_top])
  set E : Subgroup X := H'.map (CoreCtx.B0 K B).subtype with hE
  have hEle : E ≤ CoreCtx.B0 K B := Subgroup.map_subtype_le H'
  refine ⟨E, hEle.trans inf_le_left, isElemAbelian_mono c.B0_elem hEle, ?_,
    fun g _ => mem_normalizer_of_normal g, ?_⟩
  · rw [hE, Subgroup.card_map_of_injective (CoreCtx.B0 K B).subtype_injective, hH']
  · have : K ⊓ Subgroup.centralizer (E : Set X) = K := by
      refine inf_eq_left.2 fun k hk => Subgroup.mem_centralizer_iff.2 fun e he => ?_
      exact (Subgroup.mem_centralizer_iff.1 (hEle he).2 k hk).symm
    rw [this]
    exact c.glaPLayer_ne_bot

theorem core_rank_le {p : ℕ} {K B : Subgroup X} [K.Normal] (c : CoreCtx p K B) :
    p ^ GLATwoLocalRank p ↥K ≤ p * Nat.card ↥(B.map (MulAut.conjNormal (H := K))) := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  set D : Subgroup (MulAut ↥K) := B.map (MulAut.conjNormal (H := K)) with hD
  set B₀ := CoreCtx.B0 K B with hB₀
  have hcard : Nat.card B = Nat.card B₀ * Nat.card D := by
    have := card_eq_card_inf_ker_mul_card_map (MulAut.conjNormal (H := K)) B
    rwa [ker_conjNormal K] at this
  have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  rcases Nat.eq_zero_or_pos (GLATwoLocalRank p ↥K) with hr | hr
  · rw [hr, pow_zero]
    exact Nat.mul_pos c.prime.pos hDpos
  obtain ⟨F, hF⟩ := exists_glaIsBmax' c.prime.one_lt hr
  obtain ⟨hFel, hFcard, U, hU, hU2, hFU⟩ := hF
  set F' : Subgroup X := F.map K.subtype with hF'
  set U' : Subgroup X := U.map K.subtype with hU'
  have hF'K : F' ≤ K := Subgroup.map_subtype_le F
  have hU'K : U' ≤ K := Subgroup.map_subtype_le U
  have hF'el : IsElemAbelian p F' := CFSG.SectionRank.isElemAbelian_map hFel K.subtype
  have hF'card : Nat.card F' = p ^ GLATwoLocalRank p ↥K := by
    rw [hF', Subgroup.card_map_of_injective K.subtype_injective, hFcard]
  have hU'1 : U' ≠ ⊥ := fun h0 =>
    hU ((Subgroup.map_eq_bot_iff_of_injective U K.subtype_injective).1 h0)
  have hU'2 : IsPGroup 2 U' := hU2.map _
  have hF'U' : F' ≤ Subgroup.normalizer (U' : Set X) :=
    (Subgroup.map_mono hFU).trans (Subgroup.le_normalizer_map _)
  have hB₀U' : B₀ ≤ Subgroup.normalizer (U' : Set X) := fun b hb =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (s := (U' : Set X)) (t := (K : Set X)) hU'K hb.2)
  have hcomm : ∀ f ∈ F', ∀ b ∈ B₀, f * b = b * f := fun f hf b hb =>
    Subgroup.mem_centralizer_iff.1 hb.2 f (hF'K hf)
  have hE₂el : IsElemAbelian p (F' ⊔ B₀) := isElemAbelian_sup_of_commute hF'el c.B0_elem hcomm
  have hE₂ : Nat.card ↥(F' ⊔ B₀) ≤ p ^ GLATwoLocalRank p X :=
    card_le_pow_glaTwoLocalRank c.prime hE₂el hU'1 hU'2 (sup_le hF'U' hB₀U')
  have hinf : Nat.card ↥(F' ⊓ B₀) ≤ p :=
    card_le_of_le_center c.cyc c.prime.pos (inf_le_left.trans hF'K)
      (inf_le_right.trans inf_le_right) fun s hs => hF'el.2 s hs.1
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := F') (B := B₀)
    (le_normalizer_of_commute fun b hb f hf => (hcomm f hf b hb).symm)
  rw [hF'card] at hprod
  have key : p ^ GLATwoLocalRank p ↥K * Nat.card B₀ ≤ (p * Nat.card D) * Nat.card B₀ := by
    calc p ^ GLATwoLocalRank p ↥K * Nat.card B₀
        = Nat.card ↥(F' ⊔ B₀) * Nat.card ↥(F' ⊓ B₀) := hprod.symm
      _ ≤ Nat.card B * p := Nat.mul_le_mul (c.card ▸ hE₂) hinf
      _ = (p * Nat.card D) * Nat.card B₀ := by rw [hcard]; ring
  exact Nat.le_of_mul_le_mul_right key hB₀pos

theorem inf_centralizer_sup_zpowers_eq {K S : Subgroup X}
    (hS : S ≤ Subgroup.centralizer (K : Set X)) (b : X) :
    K ⊓ Subgroup.centralizer ((S ⊔ Subgroup.zpowers b : Subgroup X) : Set X) =
      K ⊓ Subgroup.centralizer ({b} : Set X) := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, Subgroup.centralizer_le (Set.singleton_subset_iff.2
      (SetLike.mem_coe.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))) hc⟩
  · rintro ⟨hx, hb⟩
    refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hle : S ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set X) := by
      refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hS hs) x hx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem inf_centralizer_singleton_eq_map (K : Subgroup X) [K.Normal] (b : X) :
    K ⊓ Subgroup.centralizer ({b} : Set X) =
      (fixSub (MulAut.conjNormal (H := K) b)).map K.subtype := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show (MulAut.conjNormal (H := K) b) ⟨x, hx⟩ = ⟨x, hx⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (MulAut.conjNormal (H := K) b) k = k := hk
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm

theorem exists_quot_elemAbelian {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] {p : ℕ}
    {D : Subgroup (MulAut K)} (hD : IsElemAbelian p D) (hDI : D ⊓ inner K = ⊥) :
    ∃ D' : Subgroup (MulAut (K ⧸ Subgroup.center K)), IsElemAbelian p D' ∧
      Nat.card D' = Nat.card D ∧ D' ⊓ inner (K ⧸ Subgroup.center K) = ⊥ := by
  set φ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K with hφ
  have hinj : Function.Injective φ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  refine ⟨D.map φ, CFSG.SectionRank.isElemAbelian_map hD φ,
    Subgroup.card_map_of_injective hinj, ?_⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨α, hα, rfl⟩, hα'⟩
  have h1 : α ∈ D ⊓ inner K := ⟨hα, mem_inner_of_centerQuotientHom_mem hα'⟩
  rw [hDI, Subgroup.mem_bot] at h1
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem card_sup_zpowers {p : ℕ} (hp : p.Prime) {B S : Subgroup X} (hB : IsElemAbelian p B)
    (hSB : S ≤ B) {b : X} (hb : b ∈ B) (hbS : b ∉ S) :
    Nat.card ↥(S ⊔ Subgroup.zpowers b) = Nat.card S * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hbS (h ▸ S.one_mem)
  have hord : orderOf b = p := orderOf_eq_prime (hB.2 b hb) hb1
  have hz : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hord]
  have hSN : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set X) := by
    refine le_normalizer_of_commute fun t ht s hs => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact (Commute.zpow_left (show Commute b s from isElemAbelian_commute hB hb (hSB hs)) n).eq
  have hprod := card_sup_mul_card_inf_of_le_normalizer hSN
  have hinf : Nat.card ↥(S ⊓ Subgroup.zpowers b) = 1 := by
    have hdvd : Nat.card ↥(S ⊓ Subgroup.zpowers b) ∣ p := hz ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : S ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hz])
      have hmem : b ∈ S ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbS hmem.1
  rw [hinf, mul_one, hz] at hprod
  exact hprod

theorem card_le_mul_card_of_quot {B C : Subgroup X} (hCB : C ≤ B) {Y : Type*} [Finite Y]
    (f : ↥B → Y) (hf : ∀ a b : ↥B, f a = f b ↔ a⁻¹ * b ∈ C.subgroupOf B) :
    Nat.card B ≤ Nat.card Y * Nat.card C := by
  let g : ↥B ⧸ C.subgroupOf B → Y := Quotient.lift f fun a b hab =>
    (hf a b).2 (QuotientGroup.leftRel_apply.1 hab)
  have hg : Function.Injective g := by
    intro q q'
    induction q using QuotientGroup.induction_on with
    | H a =>
      induction q' using QuotientGroup.induction_on with
      | H b =>
        intro h
        exact QuotientGroup.eq.2 ((hf a b).1 h)
  have h1 : Nat.card (↥B ⧸ C.subgroupOf B) ≤ Nat.card Y := Nat.card_le_card_of_injective g hg
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf B)
  have h3 : Nat.card (C.subgroupOf B) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
  rw [h2, h3]
  exact Nat.mul_le_mul_right _ h1

def omegaCenter (K : Subgroup X) (p : ℕ) : Subgroup X where
  carrier := {x | x ∈ K ∧ (∀ y ∈ K, x * y = y * x) ∧ x ^ p = 1}
  one_mem' := ⟨K.one_mem, fun y _ => by simp, one_pow p⟩
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨haK, hac, hap⟩ := ha
    obtain ⟨hbK, hbc, hbp⟩ := hb
    refine ⟨K.mul_mem haK hbK, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [(show Commute a b from hac b hbK).mul_pow, hap, hbp, one_mul]
  inv_mem' := fun {a} ha => by
    obtain ⟨haK, hac, hap⟩ := ha
    refine ⟨K.inv_mem haK, fun y hy => ?_, ?_⟩
    · have := hac y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
        _ = y * a⁻¹ := by group
    · rw [inv_pow, hap, inv_one]

theorem card_omegaCenter_le {K : Subgroup X} (hcyc : IsCyclic (Subgroup.center ↥K)) {p : ℕ}
    (hp : 0 < p) : Nat.card (omegaCenter K p) ≤ p :=
  card_le_of_le_center hcyc hp (fun x hx => hx.1)
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hx.2.1 y hy).symm)
    (fun x hx => hx.2.2)

theorem isElemAbelian_zpowers {p : ℕ} {u : X} (hup : u ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers u) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hup, one_zpow]

theorem step2_mem_omega {p : ℕ} {K B : Subgroup X} [K.Normal] (hB : IsElemAbelian p B) {b u : X}
    (hbB : b ∈ B) (huK : u ∈ K) (hup : u ^ p = 1)
    (hbu : ∀ y ∈ K, b * y * b⁻¹ = u * y * u⁻¹) {c : X} (hc : c ∈ B) :
    u⁻¹ * (c * u * c⁻¹) ∈ omegaCenter K p := by
  have hcb : c * b * c⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact isElemAbelian_commute hB hc hbB
  have hw : ∀ y ∈ K, (c * u * c⁻¹) * y * (c * u * c⁻¹)⁻¹ = u * y * u⁻¹ := by
    intro y hy
    have hy' : c⁻¹ * y * c ∈ K := by
      have := Subgroup.Normal.conj_mem inferInstance y hy c⁻¹
      simpa using this
    have h1 := hbu (c⁻¹ * y * c) hy'
    calc (c * u * c⁻¹) * y * (c * u * c⁻¹)⁻¹ = c * (u * (c⁻¹ * y * c) * u⁻¹) * c⁻¹ := by group
      _ = c * (b * (c⁻¹ * y * c) * b⁻¹) * c⁻¹ := by rw [h1]
      _ = (c * b * c⁻¹) * y * (c * b * c⁻¹)⁻¹ := by group
      _ = b * y * b⁻¹ := by rw [hcb]
      _ = u * y * u⁻¹ := hbu y hy
  have hwK : c * u * c⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance u huK c
  have hzc : ∀ y ∈ K, (u⁻¹ * (c * u * c⁻¹)) * y = y * (u⁻¹ * (c * u * c⁻¹)) := by
    intro y hy
    have h1 := hw y hy
    calc u⁻¹ * (c * u * c⁻¹) * y
        = u⁻¹ * ((c * u * c⁻¹) * y * (c * u * c⁻¹)⁻¹) * (c * u * c⁻¹) := by group
      _ = u⁻¹ * (u * y * u⁻¹) * (c * u * c⁻¹) := by rw [h1]
      _ = y * (u⁻¹ * (c * u * c⁻¹)) := by group
  refine ⟨K.mul_mem (K.inv_mem huK) hwK, hzc, ?_⟩
  have hcomm : Commute u (u⁻¹ * (c * u * c⁻¹)) := (hzc u huK).symm
  have hwp : (c * u * c⁻¹) ^ p = 1 := by rw [conj_pow, hup]; group
  have hw_eq : c * u * c⁻¹ = u * (u⁻¹ * (c * u * c⁻¹)) := by group
  rw [hw_eq, hcomm.mul_pow, hup, one_mul] at hwp
  exact hwp

theorem pow_mul_eq_of_comm {M : Type*} [Group M] (x y z : M) (hz : y * x = z * (x * y))
    (hzx : z * x = x * z) (hzy : z * y = y * z) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * z ^ (∑ i ∈ Finset.range n, i) := by
  have cx : ∀ k : ℕ, Commute (z ^ k) x := fun k => (show Commute z x from hzx).pow_left k
  have cy : ∀ k : ℕ, Commute (z ^ k) y := fun k => (show Commute z y from hzy).pow_left k
  have hyx : ∀ k : ℕ, y ^ k * x = z ^ k * (x * y ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * x = y * (z ^ k * (x * y ^ k)) := by rw [pow_succ', mul_assoc, ih]
        _ = (z ^ k * y) * (x * y ^ k) := by rw [← mul_assoc, ← (cy k).eq]
        _ = z ^ k * ((y * x) * y ^ k) := by simp only [mul_assoc]
        _ = z ^ k * ((z * (x * y)) * y ^ k) := by rw [hz]
        _ = z ^ (k + 1) * (x * y ^ (k + 1)) := by
            rw [pow_succ z k, pow_succ' y k]
            simp only [mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    set T := ∑ i ∈ Finset.range n, i with hT
    have hcT : Commute (z ^ T) (x * y) := (cx T).mul_right (cy T)
    have hxn : Commute (z ^ n) (x ^ n) := (show Commute z x from hzx).pow_pow n n
    have hcn : Commute (z ^ n) (x ^ (n + 1)) := (show Commute z x from hzx).pow_pow n (n + 1)
    have hcn' : Commute (z ^ n) (y ^ (n + 1)) := (show Commute z y from hzy).pow_pow n (n + 1)
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * (z ^ T * (x * y)) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ n * y ^ n * ((x * y) * z ^ T) := by rw [hcT.eq]
      _ = x ^ n * (y ^ n * x) * y * z ^ T := by simp only [mul_assoc]
      _ = x ^ n * (z ^ n * (x * y ^ n)) * y * z ^ T := by rw [hyx n]
      _ = (x ^ n * z ^ n) * x * (y ^ n * y) * z ^ T := by simp only [mul_assoc]
      _ = (z ^ n * x ^ n) * x * (y ^ n * y) * z ^ T := by rw [hxn.eq.symm]
      _ = z ^ n * (x ^ (n + 1) * y ^ (n + 1)) * z ^ T := by
          rw [pow_succ x n, pow_succ y n]; simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * z ^ n * z ^ T := by
          rw [(hcn.mul_right hcn').eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * (z ^ n * z ^ T) := by rw [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * z ^ (∑ i ∈ Finset.range (n + 1), i) := by
          have hs : ∑ i ∈ Finset.range (n + 1), i = n + T := by
            rw [hT, Finset.sum_range_succ, add_comm]
          rw [hs, pow_add z n T]

theorem prime_dvd_sum_range {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ ∑ i ∈ Finset.range p, i := by
  have h := Finset.sum_range_id_mul_two p
  have h1 : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
    rw [h]
    exact Dvd.intro _ rfl
  exact (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd))) h1)

open scoped IsMulCommutative in
theorem card_le_of_pow_central {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcyc : IsCyclic (Subgroup.center M)) {Dh : Subgroup M}
    (hcD : Subgroup.center M ≤ Dh) (ha : ∀ k ∈ Dh, k ^ p ∈ Subgroup.center M)
    (hb : ∀ k ∈ Dh, ∀ k' ∈ Dh, ⁅k, k'⁆ ∈ Subgroup.center M)
    (hc : ∀ k ∈ Dh, k ^ p = 1 → k ∈ Subgroup.center M) :
    Nat.card Dh ≤ p * Nat.card (Subgroup.center M) := by
  haveI := hcyc
  have hcentral : ∀ z ∈ Subgroup.center M, ∀ g : M, z * g = g * z := fun z hz g =>
    (Subgroup.mem_center_iff.1 hz g).symm
  have hz_pow : ∀ k ∈ Dh, ∀ k' ∈ Dh, ⁅k', k⁆ ^ p = 1 := by
    intro k hk k' hk'
    have hzc := hb k' hk' k hk
    have h1 : Commute k' ⁅k', k⁆ := (hcentral _ hzc k').symm
    rw [h1.commutatorElement_pow_left]
    exact commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 (ha k' hk') k).symm
  have hmul : ∀ k ∈ Dh, ∀ k' ∈ Dh, (k * k') ^ p = k ^ p * k' ^ p := by
    intro k hk k' hk'
    have hzc := hb k' hk' k hk
    have key := pow_mul_eq_of_comm k k' ⁅k', k⁆ (by rw [commutatorElement_def]; group)
      (hcentral _ hzc k) (hcentral _ hzc k') p
    have hS : ⁅k', k⁆ ^ (∑ i ∈ Finset.range p, i) = 1 := by
      obtain ⟨t, ht⟩ := prime_dvd_sum_range hp hp2
      rw [ht, pow_mul, hz_pow k hk k' hk', one_pow]
    rw [key, hS, mul_one]
  let pw : ↥Dh →* ↥(Subgroup.center M) :=
    { toFun := fun k => ⟨(k : M) ^ p, ha k k.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun k k' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact hmul k k.2 k' k'.2) }
  let R : Subgroup ↥(Subgroup.center M) := (powMonoidHom (α := ↥(Subgroup.center M)) p).range
  let Θ : ↥Dh →* ↥(Subgroup.center M) ⧸ R := (QuotientGroup.mk' R).comp pw
  have hRq : IsCyclic (↥(Subgroup.center M) ⧸ R) :=
    isCyclic_of_surjective (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
  have hrange : Nat.card Θ.range ≤ p := by
    refine card_le_of_pow_eq_one_of_isCyclic hp.pos Θ.range ?_
    rintro _ ⟨k, rfl⟩
    show (QuotientGroup.mk' R (pw k)) ^ p = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨pw k, rfl⟩
  have hker : Θ.ker ≤ (Subgroup.center M).subgroupOf Dh := by
    intro k hk
    have h1 : QuotientGroup.mk' R (pw k) = 1 := hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨z, hz⟩ := h1
    have hzp : (z : M) ^ p = (k : M) ^ p := congrArg Subtype.val hz
    have hzD : (z : M) ∈ Dh := hcD z.2
    have hkz : (k : M) * (z : M)⁻¹ ∈ Dh := Dh.mul_mem k.2 (Dh.inv_mem hzD)
    have hcomm : Commute (k : M) (z : M)⁻¹ :=
      Subgroup.mem_center_iff.1 ((Subgroup.center M).inv_mem z.2) k
    have hp1 : ((k : M) * (z : M)⁻¹) ^ p = 1 := by
      rw [hcomm.mul_pow, inv_pow, hzp, mul_inv_cancel]
    have hcen := hc _ hkz hp1
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.center M).mul_mem hcen z.2
    simpa using this
  have hkcard : Nat.card Θ.ker ≤ Nat.card (Subgroup.center M) := by
    refine (Subgroup.card_le_of_le hker).trans ?_
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcD).toEquiv).le
  calc Nat.card Dh = Nat.card Θ.ker * Nat.card Θ.range := (Subgroup.card_ker_mul_card_range Θ).symm
    _ ≤ Nat.card (Subgroup.center M) * p := Nat.mul_le_mul hkcard hrange
    _ = p * Nat.card (Subgroup.center M) := mul_comm _ _

end Basic

theorem conj_ker_eq_center (M : Type*) [Group M] :
    (MulAut.conj : M →* MulAut M).ker = Subgroup.center M := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 := congrArg (fun φ : MulAut M => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem core_card_inner_le {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} [K.Normal]
    (c : CoreCtx p K B)
    (hno : ∀ b ∈ B, ∀ u ∈ K, u ^ p = 1 → (∀ y ∈ K, b * y * b⁻¹ = u * y * u⁻¹) →
      ∀ y ∈ K, u * y = y * u) :
    Nat.card ↥(B.map (MulAut.conjNormal (H := K)) ⊓ inner ↥K) ≤ p := by
  set act : X →* MulAut ↥K := MulAut.conjNormal (H := K) with hact
  set D : Subgroup (MulAut ↥K) := B.map act with hD
  set I : Subgroup (MulAut ↥K) := D ⊓ inner ↥K with hI
  set cj : ↥K →* MulAut ↥K := MulAut.conj with hcj
  set Dh : Subgroup ↥K := I.comap cj with hDh
  have hker : cj.ker = Subgroup.center ↥K := conj_ker_eq_center ↥K
  have hcD : Subgroup.center ↥K ≤ Dh := by
    intro z hz
    have : cj z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
    show cj z ∈ I
    rw [this]
    exact I.one_mem
  have hwit : ∀ k ∈ Dh, ∃ b ∈ B, act b = cj k := fun k hk => by
    obtain ⟨b, hb, hbk⟩ := (show cj k ∈ I from hk).1
    exact ⟨b, hb, hbk⟩
  have hbp : ∀ b ∈ B, b ^ p = 1 := fun b hb => c.elem.2 b hb
  have ha : ∀ k ∈ Dh, k ^ p ∈ Subgroup.center ↥K := by
    intro k hk
    obtain ⟨b, hb, hbk⟩ := hwit k hk
    rw [← hker, MonoidHom.mem_ker, map_pow, ← hbk, ← map_pow, hbp b hb, map_one]
  have hb : ∀ k ∈ Dh, ∀ k' ∈ Dh, ⁅k, k'⁆ ∈ Subgroup.center ↥K := by
    intro k hk k' hk'
    obtain ⟨b, hb, hbk⟩ := hwit k hk
    obtain ⟨b', hb', hbk'⟩ := hwit k' hk'
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement, ← hbk, ← hbk', ← map_commutatorElement,
      commutatorElement_eq_one_iff_commute.2 (isElemAbelian_commute c.elem hb hb'), map_one]
  have hc : ∀ k ∈ Dh, k ^ p = 1 → k ∈ Subgroup.center ↥K := by
    intro k hk hkp
    obtain ⟨b, hb, hbk⟩ := hwit k hk
    have h1 := (conjNormal_eq_conj_iff K b k).1 hbk
    have h2 : (k : X) ^ p = 1 := by simpa using congrArg Subtype.val hkp
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hno b hb k k.2 h2 h1 g g.2).symm
  haveI := c.cyc
  have h1 := card_le_of_pow_central c.prime c.odd c.cyc hcD ha hb hc
  have h2 := card_eq_card_inf_ker_mul_card_map cj Dh
  have h3 : Dh ⊓ cj.ker = Subgroup.center ↥K := by
    rw [hker]
    exact inf_eq_right.2 hcD
  have h4 : Dh.map cj = I := by
    ext α
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hα
      obtain ⟨k, hk⟩ := hα.2
      exact ⟨k, by show cj k ∈ I; rw [hk]; exact hα, hk⟩
  rw [h3, h4] at h2
  have hZpos : 0 < Nat.card (Subgroup.center ↥K) := Nat.card_pos
  have : Nat.card I * Nat.card (Subgroup.center ↥K) ≤ p * Nat.card (Subgroup.center ↥K) := by
    rw [mul_comm (Nat.card I)]
    rw [← h2]
    exact h1
  exact Nat.le_of_mul_le_mul_right this hZpos

theorem fixSub_conj {M : Type*} [Group M] (d : M) :
    fixSub (MulAut.conj d) = Subgroup.centralizer ({d} : Set M) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show (MulAut.conj d) x = x ↔ x * d = d * x
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end I2611

open I2611

section Lemma91

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem i2611UsedAt_of_printed (h : I2611Printed) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : I2611UsedAt G p := by
  intro B x J hB hx hJ hBJ hodd hT hcyc h4
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := le_centralizer_of_mem hB.1 hx.1
  have hJH : J ≤ J ⊔ B := le_sup_left
  have hBH : B ≤ J ⊔ B := le_sup_right
  have hHC : J ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := sup_le hJ.1 hBC
  have hJp : GLAPComponent p (J ⊔ B) J := glaPComponent_of_le hp hJ hJH hHC
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_commute hB.1 ha hb
  have hlayer := (glaPLayer_top_subgroupOf hp hJp hBc hBJ).symm
  have hCtop : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one hsimple hnonab hx.2.1
  have hKC : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hKP hCtop
  have hKJ : CFSG.Open.IsKGroup ↥J := CFSG.Open.IsKGroup.of_le hKC hJ.1
  have hKq : CFSG.Open.IsKGroup (PQuot p J) := CFSG.Open.IsKGroup.quotient hKJ _
  have hqJ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hhat : IsKHat (PQuot p J) := ⟨hqJ, isCatalogGroup_center_quotient' hKq hqJ⟩
  obtain ⟨eK⟩ := nonempty_pQuot_equiv_subgroupOf p hJH
  have hhatK : IsKHat (PQuot p (J.subgroupOf (J ⊔ B))) := IsKHat.of_mulEquiv eK.symm hhat
  have hcycK : IsCyclic (Subgroup.center (PQuot p (J.subgroupOf (J ⊔ B)))) :=
    (MulEquiv.isCyclic (Subgroup.centerCongr eK)).2 hcyc
  have hodd' : Odd (Nat.card (GLAPPrimeCoreOf p (J.subgroupOf (J ⊔ B)))) := by
    rw [← map_subtype_glaPPrimeCoreOf_subgroupOf p hJH,
      Subgroup.card_map_of_injective (J ⊔ B).subtype_injective] at hodd
    exact hodd
  have hB'el : IsElemAbelian p (B.subgroupOf (J ⊔ B)) := isElemAbelian_subgroupOf _ hB.1
  obtain ⟨T, hTJ, hT2, hBT, hTB⟩ := hT
  have hTH : T ≤ J ⊔ B := hTJ.trans hJH
  have hT1 : T ≠ ⊥ := fun h0 => hTB (by rw [h0]; exact Subgroup.commutator_bot_left B)
  have hT'1 : T.subgroupOf (J ⊔ B) ≠ ⊥ := fun h0 => hT1 (by
    have := congrArg (Subgroup.map (J ⊔ B).subtype) h0
    rwa [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_bot] at this)
  have hT'2 : IsPGroup 2 ↥(T.subgroupOf (J ⊔ B)) :=
    hT2.comap_of_injective (J ⊔ B).subtype (J ⊔ B).subtype_injective
  have hB'T' : B.subgroupOf (J ⊔ B) ≤
      Subgroup.normalizer ((T.subgroupOf (J ⊔ B) : Subgroup ↥(J ⊔ B)) : Set ↥(J ⊔ B)) :=
    (le_normalizer_subgroupOf_iff hTH hBH).2 hBT
  have hcardB' : Nat.card (B.subgroupOf (J ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hrk : GLATwoLocalRank p ↥(J ⊔ B) = GLATwoLocalRank p G := by
    refine le_antisymm (glaTwoLocalRank_subgroup_le hp _) ?_
    have h1 : GLATwoLocalRank p G ≤ CFSG.Open.pRank p (B.subgroupOf (J ⊔ B)) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'el (by rw [hcardB']; exact hB.2.1)
    exact h1.trans (pRank_le_glaTwoLocalRank_of_normalizes hp hT'1 hT'2 hB'T')
  have hx' : x ∈ J ⊔ B := hBH hx.1
  have hxc : (⟨x, hx'⟩ : ↥(J ⊔ B)) ∈
      Subgroup.centralizer ((J.subgroupOf (J ⊔ B) : Subgroup ↥(J ⊔ B)) : Set ↥(J ⊔ B)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 (Subgroup.mem_subgroupOf.1 hk))
    exact Subtype.ext this
  have hmain := h ↥(J ⊔ B) p hp hp2 (J.subgroupOf (J ⊔ B)) (B.subgroupOf (J ⊔ B)) hlayer hhatK
    hodd' hB'el (subgroupOf_sup_sup_eq_top J B)
    ⟨T.subgroupOf (J ⊔ B), fun t ht => Subgroup.mem_subgroupOf.2
      (hTJ (Subgroup.mem_subgroupOf.1 ht)), hT'1, hT'2, hB'T'⟩
    (by rw [hcardB', hB.2.1, hrk]) (hrk ▸ h4)
    ⟨⟨x, hx'⟩, Subgroup.mem_subgroupOf.2 hx.1, fun h1 => hx.2.1 (congrArg Subtype.val h1),
      centMod_of_mem_centralizer hxc⟩
    (pRank_oPPrimeP_le_one hp hhatK.1 hcycK)
  rcases hmain with hGB | ⟨A', hA', hAnot, hAdec⟩
  ·
    obtain ⟨E', hE'B', hE'el, hE'c, hE'N, hE'L⟩ := hGB
    refine Or.inl ⟨E'.map (J ⊔ B).subtype, ?_, CFSG.SectionRank.isElemAbelian_map hE'el _, ?_,
      ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hE'B' he)
    · rw [Subgroup.card_map_of_injective (J ⊔ B).subtype_injective, hE'c]
    · rintro _ ⟨e, he, rfl⟩
      have h1 : e ∈ (Subgroup.normalizer (J : Set G)).subgroupOf (J ⊔ B) := by
        rw [Subgroup.subgroupOf_normalizer_eq hJH]
        exact hE'N he
      exact Subgroup.mem_subgroupOf.1 h1
    · have hEq : (J.subgroupOf (J ⊔ B) ⊓ Subgroup.centralizer (E' : Set ↥(J ⊔ B))).map
          (J ⊔ B).subtype = J ⊓ Subgroup.centralizer ((E'.map (J ⊔ B).subtype : Subgroup G) : Set G) := by
        ext y
        constructor
        · rintro ⟨k, ⟨hkJ, hkC⟩, rfl⟩
          refine ⟨Subgroup.mem_subgroupOf.1 hkJ, ?_⟩
          refine Subgroup.mem_centralizer_iff.2 ?_
          rintro _ ⟨e, he, rfl⟩
          exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hkC e he)
        · rintro ⟨hyJ, hyC⟩
          have hyH : y ∈ J ⊔ B := hJH hyJ
          refine ⟨⟨y, hyH⟩, ⟨Subgroup.mem_subgroupOf.2 hyJ, ?_⟩, rfl⟩
          refine Subgroup.mem_centralizer_iff.2 ?_
          intro e he
          exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyC e ⟨e, he, rfl⟩)
      have := glaPLayer_map_ne_bot hp (J ⊔ B).subtype (J ⊔ B).subtype_injective hE'L
      rwa [hEq] at this
  ·
    refine Or.inr ⟨A'.map (J ⊔ B).subtype, glaIsBmax_map_subtype hA' hrk,
      Subgroup.map_subtype_le A', ?_, ?_, ?_⟩
    · obtain ⟨-, -, U', hU', hU'2, hAU'⟩ := hA'
      refine ⟨U'.map (J ⊔ B).subtype, Subgroup.map_subtype_le U', ?_, hU'2.map _, ?_⟩
      · intro h0
        exact hU' ((Subgroup.map_eq_bot_iff_of_injective U' (J ⊔ B).subtype_injective).1 h0)
      · exact (Subgroup.map_mono hAU').trans (Subgroup.le_normalizer_map _)
    · rintro _ ⟨a', ha', rfl⟩
      obtain ⟨u', hu', v', hv', hav⟩ := hAdec a' ha'
      refine ⟨(u' : G), ⟨⟨u', hu'.1, rfl⟩, Subgroup.mem_subgroupOf.1 hu'.2⟩, (v' : G),
        ⟨⟨v', hv'.1, rfl⟩, Subgroup.mem_subgroupOf.1 hv'.2⟩, ?_⟩
      rw [hav]
      rfl
    · intro hle
      apply hAnot
      intro z hz
      have hzJ : (z : G) ∈ A'.map (J ⊔ B).subtype ⊓ J :=
        ⟨⟨z, hz.1, rfl⟩, Subgroup.mem_subgroupOf.1 hz.2⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hle hzJ)
      refine mem_oPPrimeP_of_central (p := p) hz.2 ?_ ?_
      · intro y hy
        have hz' : z = (⟨x, hx'⟩ : ↥(J ⊔ B)) ^ n := Subtype.ext (by rw [← hn]; rfl)
        rw [hz']
        exact ((Commute.zpow_left (Subgroup.mem_centralizer_iff.1 hxc y hy).symm n)).eq.symm ▸ rfl
      · have hxp : (⟨x, hx'⟩ : ↥(J ⊔ B)) ^ p = 1 := Subtype.ext (by simpa using hB.1.2 x hx.1)
        have hz' : z = (⟨x, hx'⟩ : ↥(J ⊔ B)) ^ n := Subtype.ext (by rw [← hn]; rfl)
        rw [hz', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

end Lemma91

theorem i2611Printed_of_core (hcore : I2611Core) : I2611Printed := by
  intro X _ _ p hp hp2 K B hK hhat hodd hBel _hKB hT hcard h4 he1 he2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hKn : K.Normal := hK ▸ glaPLayer_top_normal p
  set N : Subgroup X := GLAPPrimeCoreOf p K with hNdef
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hNp : ¬ p ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf hp K
  haveI hNn : N.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K
    rw [Subgroup.normalizer_eq_top_iff.2 hKn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  set f : ↥K →* ↥(K.map π) := π.subgroupMap K with hf
  have hfsurj : Function.Surjective f := π.subgroupMap_surjective K
  have hfker : f.ker = GLAPPrimeCore p ↥K := by
    rw [hf, Subgroup.ker_subgroupMap, hker]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hNcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
  let e₀ : PQuot p K ≃* ↥(K.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)
  have hhat' : IsKHat ↥(K.map π) := IsKHat.of_mulEquiv e₀ hhat
  haveI hKbn : (K.map π).Normal := hKn.map π hsurj
  have hcore' : GLAPPrimeCore p ↥(K.map π) = ⊥ := by
    have h1 := glaPPrimeCore_map_of_surjective hp f hfsurj (by rw [hfker]; exact hNcop)
    rw [← h1, ← hfker]
    exact (Subgroup.map_eq_bot_iff _).2 le_rfl
  have hcyc' : IsCyclic (Subgroup.center ↥(K.map π)) :=
    (MulEquiv.isCyclic (Subgroup.centerCongr e₀)).1
      (isCyclic_center_pQuot_of_pRank_le_one hp hp2 he2)
  obtain ⟨kB, hkB⟩ := exists_card_eq_pow_of_isElemAbelian hp hBel
  have hBdisj : Disjoint B π.ker := by
    rw [hker]
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hkB]
      exact Nat.Coprime.pow_left kB ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp))
  have hBcard : Nat.card (B.map π) = Nat.card B := card_map_eq_of_disjoint_ker π hBdisj
  have hBel' : IsElemAbelian p (B.map π) := CFSG.SectionRank.isElemAbelian_map hBel π
  obtain ⟨T, hTK, hT1, hT2, hBT⟩ := hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTdisj : Disjoint T π.ker := by
    rw [hker]
    obtain ⟨kT, hkT⟩ := hT2.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hkT]
      exact Nat.Coprime.pow_left kT (Nat.coprime_two_left.2 hodd))
  have hTcard : Nat.card (T.map π) = Nat.card T := card_map_eq_of_disjoint_ker π hTdisj
  have hT1' : T.map π ≠ ⊥ := by
    intro h
    apply hT1
    rw [h, Subgroup.card_bot] at hTcard
    exact Subgroup.eq_bot_of_card_eq T hTcard.symm
  have hT2' : IsPGroup 2 (T.map π) := hT2.map π
  have hBT' : B.map π ≤ Subgroup.normalizer ((T.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map π)
  have hrk : GLATwoLocalRank p (X ⧸ N) = GLATwoLocalRank p X := by
    refine le_antisymm (glaTwoLocalRank_quotient_le hp hp2 N hNp) ?_
    have h1 : Nat.card (B.map π) ≤ p ^ GLATwoLocalRank p (X ⧸ N) :=
      card_le_pow_glaTwoLocalRank hp hBel' hT1' hT2' hBT'
    rw [hBcard, hcard] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  obtain ⟨b, hbB, hb1, hbC⟩ := he1
  have hb' : π b ≠ 1 := by
    intro h
    have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).1 h
    have h1 : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one (hBel.2 b hbB)
    have h2 : orderOf b ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hbN
    have h3 : orderOf b = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp) h1 h2
    exact hb1 (orderOf_eq_one_iff.1 h3)
  have hbc : π b ∈ Subgroup.centralizer ((K.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ⁅k, b⁆ ∈ N :=
      hbC.2 (Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers b))
    have h2 : π ⁅k, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)
  have hres := hcore (X ⧸ N) p hp hp2 (K.map π) (B.map π) hKbn hcore' hhat' hcyc' hBel'
    (by rw [hBcard, hcard, hrk]) (by rw [hrk]; exact h4)
    ⟨T.map π, Subgroup.map_mono hTK, hT1', hT2', hBT'⟩ ⟨π b, ⟨b, hbB, rfl⟩, hb', hbc⟩
  rcases hres with hGB | ⟨Ab, hAb, hnc, hdec⟩
  · exact Or.inl (lift_isGB hp hNK hNp hBel hGB)
  · refine Or.inr (lift_bmax hp hp2 hNK hNp hBel hrk ?_ hAb hnc hdec)
    intro w hw y hy
    obtain ⟨hwK, hmem⟩ := map_mem_center_of_mem_oPPrimeP hp f hfsurj hfker hhat.1 hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hmem ⟨y, hy⟩)

theorem i2611_step1 (hKD26a : KD26a) (hKD26bc : KD26bc) (hKD26d : KD26d) {X : Type} [Group X]
    [Finite X] {p : ℕ} {K B : Subgroup X} [K.Normal] (c : CoreCtx p K B)
    (hI : B.map (MulAut.conjNormal (H := K)) ⊓ inner ↥K = ⊥) : IsGB p B K := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  set D : Subgroup (MulAut ↥K) := B.map (MulAut.conjNormal (H := K)) with hD
  set B₀ := CoreCtx.B0 K B with hB₀
  have hDel : IsElemAbelian p D := CFSG.SectionRank.isElemAbelian_map c.elem _
  have hcard : Nat.card B = Nat.card B₀ * Nat.card D := by
    have := card_eq_card_inf_ker_mul_card_map (MulAut.conjNormal (H := K)) B
    rwa [ker_conjNormal K] at this
  by_cases hB3 : p ^ 3 ≤ Nat.card B₀
  · exact core_isGB_of_card_ge c hB3
  have hD2 : Nat.card D ≤ p ^ 2 := by
    have := hKD26a ↥K c.hat p c.prime c.odd D hDel
    rw [hI, Subgroup.card_bot, mul_one] at this
    exact this
  have hB02 : Nat.card B₀ ≤ p ^ 2 := by
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian c.prime c.B0_elem
    rw [hk] at hB3 ⊢
    have : k < 3 := by
      by_contra h
      exact hB3 (Nat.pow_le_pow_right c.prime.pos (by omega))
    exact Nat.pow_le_pow_right c.prime.pos (by omega)
  have h4 : p ^ 4 ≤ Nat.card B := by
    rw [c.card]
    exact Nat.pow_le_pow_right c.prime.pos c.four
  have hp4 : p ^ 4 = p ^ 2 * p ^ 2 := by ring
  have hB0pos : 0 < Nat.card B₀ := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hB0eq : Nat.card B₀ = p ^ 2 := by
    by_contra hne
    have hlt : Nat.card B₀ < p ^ 2 := lt_of_le_of_ne hB02 hne
    rw [hcard, hp4] at h4
    nlinarith
  have hDeq : Nat.card D = p ^ 2 := by
    by_contra hne
    have hlt : Nat.card D < p ^ 2 := lt_of_le_of_ne hD2 hne
    rw [hcard, hp4] at h4
    nlinarith
  by_cases hU : p = 3 ∧ IsLnEps (↥K ⧸ Subgroup.center ↥K) 3 8 false
  · exfalso
    obtain ⟨hp3, hS⟩ := hU
    haveI : Group.IsPerfect ↥K := ⟨c.hat.1.1⟩
    obtain ⟨D', hD'el, hD'card, hD'I⟩ := exists_quot_elemAbelian hDel hI
    subst hp3
    obtain ⟨x, hx, hx1⟩ := hKD26d (↥K ⧸ Subgroup.center ↥K) hS D' hD'el
      (by rw [hD'card, hDeq]; norm_num)
    rw [hD'I, Subgroup.mem_bot] at hx
    exact hx1 hx
  obtain ⟨y, hyD, hy1, hyL⟩ := hKD26bc ↥K c.hat p c.prime c.odd c.p_dvd_card hU D hDel hDeq hI
  obtain ⟨b, hbB, rfl⟩ := hyD
  have hbB₀ : b ∉ B₀ := fun hb => hy1 (by
    have : b ∈ (MulAut.conjNormal (H := K)).ker := by rw [ker_conjNormal K]; exact hb.2
    exact MonoidHom.mem_ker.1 this)
  have hEcard : Nat.card ↥(B₀ ⊔ Subgroup.zpowers b) = p ^ 3 := by
    rw [card_sup_zpowers c.prime c.elem inf_le_left hbB hbB₀, hB0eq]
    ring
  have hEB : B₀ ⊔ Subgroup.zpowers b ≤ B := sup_le inf_le_left (Subgroup.zpowers_le.2 hbB)
  refine ⟨B₀ ⊔ Subgroup.zpowers b, hEB, isElemAbelian_mono c.elem hEB, hEcard,
    fun g _ => mem_normalizer_of_normal g, ?_⟩
  rw [inf_centralizer_sup_zpowers_eq inf_le_right b, inf_centralizer_singleton_eq_map K b]
  exact glaPLayer_map_ne_bot c.prime K.subtype K.subtype_injective hyL

theorem i2611_step2 {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} [K.Normal]
    (c : CoreCtx p K B) {b u : X} (hbB : b ∈ B) (huK : u ∈ K)
    (huZ : ∃ y ∈ K, u * y ≠ y * u) (hup : u ^ p = 1)
    (hbu : ∀ y ∈ K, b * y * b⁻¹ = u * y * u⁻¹) :
    ∃ A : Subgroup X, GLAIsBmax p A ∧ (∃ w ∈ A ⊓ K, ∃ y ∈ K, w * y ≠ y * w) ∧
      ∀ a ∈ A, ∃ v ∈ A ⊓ B, ∃ w ∈ A ⊓ K, a = v * w := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  obtain ⟨T, hTK, hT1, hT2, hBT⟩ := c.two
  set C : Subgroup X := B ⊓ Subgroup.centralizer ({u} : Set X) with hC
  have hCel : IsElemAbelian p C := isElemAbelian_mono c.elem inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers u, ∀ c' ∈ C, x * c' = c' * x := by
    intro x hx c' hc'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 : u * c' = c' * u := (Subgroup.mem_centralizer_singleton_iff.1 hc'.2).symm
    exact (Commute.zpow_left (show Commute u c' from h1) n).eq
  set A : Subgroup X := Subgroup.zpowers u ⊔ C with hA
  have hAel : IsElemAbelian p A :=
    isElemAbelian_sup_of_commute (isElemAbelian_zpowers hup) hCel hcomm
  have hAu : u ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hu_norm : u ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [← hbu t (hTK ht)]
      exact (Subgroup.mem_normalizer_iff.1 (hBT hbB) t).1 ht
    · intro h
      have htK : t ∈ K := by
        have := Subgroup.Normal.conj_mem inferInstance (u * t * u⁻¹) (hTK h) u⁻¹
        simpa [mul_assoc] using this
      rw [← hbu t htK] at h
      exact (Subgroup.mem_normalizer_iff.1 (hBT hbB) t).2 h
  have hAT : A ≤ Subgroup.normalizer (T : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hu_norm) (inf_le_left.trans hBT)
  have hmem : ∀ c' : ↥B, u⁻¹ * ((c' : X) * u * (c' : X)⁻¹) ∈ omegaCenter K p := fun c' =>
    step2_mem_omega c.elem hbB huK hup hbu c'.2
  let f : ↥B → ↥(omegaCenter K p) := fun c' => ⟨u⁻¹ * ((c' : X) * u * (c' : X)⁻¹), hmem c'⟩
  have hf : ∀ a b' : ↥B, f a = f b' ↔ a⁻¹ * b' ∈ C.subgroupOf B := by
    intro a b'
    rw [Subgroup.mem_subgroupOf, Subtype.mk.injEq]
    constructor
    · intro h
      have h' := mul_left_cancel h
      refine ⟨(a⁻¹ * b').2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc ((a⁻¹ * b' : ↥B) : X) * u = (a : X)⁻¹ * ((b' : X) * u * (b' : X)⁻¹) * (b' : X) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = (a : X)⁻¹ * ((a : X) * u * (a : X)⁻¹) * (b' : X) := by rw [h']
        _ = u * ((a⁻¹ * b' : ↥B) : X) := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    · intro h
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 h.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      congr 1
      calc (a : X) * u * (a : X)⁻¹ = (a : X) * (((a : X)⁻¹ * b') * u) * (b' : X)⁻¹ := by
            rw [h1]; group
        _ = (b' : X) * u * (b' : X)⁻¹ := by group
  have hidx : Nat.card B ≤ p * Nat.card C := by
    have := card_le_mul_card_of_quot (B := B) (C := C) inf_le_left f hf
    exact this.trans (by
      rw [mul_comm p]
      exact Nat.mul_le_mul_right _ (card_omegaCenter_le c.cyc c.prime.pos) |> fun h => by
        simpa [mul_comm] using h)
  have hAB : Nat.card B ≤ Nat.card A := by
    by_cases huB : u ∈ B
    · have hBC : B ≤ C := fun x hx =>
        ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute c.elem hx huB)⟩
      exact Subgroup.card_le_of_le (hBC.trans le_sup_right)
    · have huC : u ∉ C := fun h => huB h.1
      have h1 : Nat.card ↥(C ⊔ Subgroup.zpowers u) = Nat.card C * p :=
        card_sup_zpowers c.prime hAel (le_sup_right) hAu huC
      rw [hA, sup_comm, h1]
      calc Nat.card B ≤ p * Nat.card C := hidx
        _ = Nat.card C * p := mul_comm _ _
  have hAle : Nat.card A ≤ p ^ GLATwoLocalRank p X :=
    card_le_pow_glaTwoLocalRank c.prime hAel hT1 hT2 hAT
  have hAeq : Nat.card A = p ^ GLATwoLocalRank p X := le_antisymm hAle (c.card ▸ hAB)
  refine ⟨A, ⟨hAel, hAeq, T, hT1, hT2, hAT⟩, ⟨u, ⟨hAu, huK⟩, huZ⟩, ?_⟩
  intro a ha
  have hznorm : Subgroup.zpowers u ≤ Subgroup.normalizer (C : Set X) := le_normalizer_of_commute hcomm
  rw [hA, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hznorm] at ha
  obtain ⟨x, hx, c', hc', rfl⟩ := ha
  have hxA : x ∈ A := Subgroup.mem_sup_left hx
  have hc'A : c' ∈ A := Subgroup.mem_sup_right hc'
  have hxK : x ∈ K := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact K.zpow_mem huK n
  exact ⟨c', ⟨hc'A, hc'.1⟩, x, ⟨hxA, hxK⟩, hcomm x hx c' hc'⟩

theorem i2611_step3 (hKD26a : KD26a) (hKD26e : KD26e) (hKD26f : KD26f) (hKD26g : KD26g)
    (hKD26h : KD26h) {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} [K.Normal]
    (c : CoreCtx p K B) (hB3 : ¬ p ^ 3 ≤ Nat.card (CoreCtx.B0 K B))
    (hI : B.map (MulAut.conjNormal (H := K)) ⊓ inner ↥K ≠ ⊥)
    (hno : ∀ b ∈ B, ∀ u ∈ K, u ^ p = 1 → (∀ y ∈ K, b * y * b⁻¹ = u * y * u⁻¹) →
      ∀ y ∈ K, u * y = y * u) : IsGB p B K := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hp := c.prime
  have hp2 := c.odd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  set act : X →* MulAut ↥K := MulAut.conjNormal (H := K) with hact
  set D : Subgroup (MulAut ↥K) := B.map act with hD
  set I : Subgroup (MulAut ↥K) := D ⊓ inner ↥K with hIdef
  set B₀ := CoreCtx.B0 K B with hB₀
  set cj : ↥K →* MulAut ↥K := MulAut.conj with hcj
  have hDel : IsElemAbelian p D := CFSG.SectionRank.isElemAbelian_map c.elem _
  have hIel : IsElemAbelian p I := isElemAbelian_mono hDel inf_le_left
  have hcard : Nat.card B = Nat.card B₀ * Nat.card D := by
    have := card_eq_card_inf_ker_mul_card_map act B
    rwa [hact, ker_conjNormal K] at this
  obtain ⟨b0, hb0⟩ := exists_card_eq_pow_of_isElemAbelian hp c.B0_elem
  obtain ⟨dd, hdd⟩ := exists_card_eq_pow_of_isElemAbelian hp hDel
  obtain ⟨ii, hii⟩ := exists_card_eq_pow_of_isElemAbelian hp hIel
  have hpos : 1 < p := hp.one_lt
  have hIle : Nat.card I ≤ p := core_card_inner_le c hno
  have hi1 : ii = 1 := by
    have h1 : p ^ ii ≤ p ^ 1 := by rw [← hii, pow_one]; exact hIle
    have h2 : ii ≤ 1 := (Nat.pow_le_pow_iff_right hpos).1 h1
    have h3 : ii ≠ 0 := by
      rintro rfl
      exact hI (Subgroup.eq_bot_of_card_eq I (by rw [hii, pow_zero]))
    omega
  have hmexp : GLATwoLocalRank p X = b0 + dd := by
    have h1 : p ^ GLATwoLocalRank p X = p ^ (b0 + dd) := by
      rw [← c.card, hcard, hb0, hdd, pow_add]
    exact Nat.pow_right_injective hp.two_le h1
  have hb02 : b0 ≤ 2 := by
    by_contra h
    exact hB3 (hb0 ▸ Nat.pow_le_pow_right hp.pos (by omega))
  have h4 := c.four
  have hdd3 : dd ≤ 3 := by
    have h1 := hKD26a ↥K c.hat p hp hp2 D hDel
    rw [hdd, hii, hi1, ← pow_add] at h1
    have h2 := (Nat.pow_le_pow_iff_right hpos).1 h1
    omega
  have hdd2 : 2 ≤ dd := by omega
  have hr : GLATwoLocalRank p ↥K ≤ 1 + dd := by
    have h1 := core_rank_le c
    rw [hdd, ← pow_succ'] at h1
    have h2 := (Nat.pow_le_pow_iff_right hpos).1 h1
    omega
  obtain ⟨⟨α, hαI⟩, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hI
  obtain ⟨⟨b₁, hb₁B, hb₁α⟩, ⟨d, hdα⟩⟩ := hαI
  have hα1' : α ≠ 1 := fun h => hα1 (Subtype.ext h)
  have hb₁d : act b₁ = cj d := hb₁α.trans hdα.symm
  have hdZ : d ∉ Subgroup.center ↥K := fun hd => hα1' (by
    rw [← hdα]
    have : d ∈ cj.ker := by rw [conj_ker_eq_center]; exact hd
    exact MonoidHom.mem_ker.1 this)
  have hb₁p : b₁ ^ p = 1 := c.elem.2 b₁ hb₁B
  have hdp : d ^ p ∈ Subgroup.center ↥K := by
    rw [← conj_ker_eq_center, MonoidHom.mem_ker, map_pow, ← hb₁d, ← map_pow, hb₁p, map_one]
  have hbd : ∀ y ∈ K, b₁ * y * b₁⁻¹ = (d : X) * y * (d : X)⁻¹ :=
    (conjNormal_eq_conj_iff K b₁ d).1 hb₁d
  have hd1 : d ^ p ≠ 1 := fun h => hdZ (by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hno b₁ hb₁B d d.2 (by simpa using congrArg Subtype.val h) hbd g g.2).symm)
  have hZp : IsPGroup p (Subgroup.center ↥K) := c.center_isPGroup
  have hZdvd : p ∣ Nat.card (Subgroup.center ↥K) := by
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq _ (by rw [hj, h0, pow_zero])
      apply hd1
      have := hdp
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · rw [hj]
      exact dvd_pow_self p (by omega)
  have hDnotI : ¬ D ≤ I := by
    intro hle
    have heq : I = D := le_antisymm inf_le_left hle
    have : Nat.card D = Nat.card I := by rw [heq]
    rw [hdd, hii, hi1] at this
    have := Nat.pow_right_injective hp.two_le this
    omega
  obtain ⟨α₂, hα₂D, hα₂I⟩ := SetLike.not_le_iff_exists.1 hDnotI
  have hα₂in : α₂ ∉ inner ↥K := fun h => hα₂I ⟨hα₂D, h⟩
  have hα₂p : α₂ ^ p = 1 := by
    obtain ⟨b₂, hb₂, rfl⟩ := hα₂D
    rw [← map_pow, c.elem.2 b₂ hb₂, map_one]
  have hZ1 : Subgroup.center ↥K ≠ ⊥ := fun h => hd1 (by
    have := hdp
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hfinal : ∀ hb0' : b0 = 2, GLAPLayer p (Subgroup.centralizer ({d} : Set ↥K)) ≠ ⊥ →
      IsGB p B K := by
    intro hb0' hL
    have hbB₀ : b₁ ∉ B₀ := fun hb => hα1' (by
      rw [← hdα, ← hb₁d]
      have : b₁ ∈ (MulAut.conjNormal (H := K)).ker := by rw [ker_conjNormal K]; exact hb.2
      exact MonoidHom.mem_ker.1 this)
    have hEcard : Nat.card ↥(B₀ ⊔ Subgroup.zpowers b₁) = p ^ 3 := by
      rw [card_sup_zpowers hp c.elem inf_le_left hb₁B hbB₀, hb0, hb0']
      ring
    have hEB : B₀ ⊔ Subgroup.zpowers b₁ ≤ B :=
      sup_le inf_le_left (Subgroup.zpowers_le.2 hb₁B)
    refine ⟨B₀ ⊔ Subgroup.zpowers b₁, hEB, isElemAbelian_mono c.elem hEB, hEcard,
      fun g _ => mem_normalizer_of_normal g, ?_⟩
    rw [inf_centralizer_sup_zpowers_eq inf_le_right b₁, inf_centralizer_singleton_eq_map K b₁,
      ← hact, hb₁d, fixSub_conj]
    exact glaPLayer_map_ne_bot hp K.subtype K.subtype_injective hL
  rcases hKD26e ↥K c.hat p hp hp2 hZp hZdvd ⟨α₂, hα₂p, hα₂in⟩ with
    ⟨n, q, lin, hS, hpg, hZg⟩ | ⟨q, lin, hS, hp3', h3, hZ3⟩
  ·
    have hn1 := hS.one_le
    obtain ⟨hg1, hg2⟩ := (hKD26g ↥K c.hat.1 p hp hp2 hZp hZdvd).1 n q lin hS hpg
    have hn3 : p ≤ n := Nat.le_of_dvd (by omega) (hpg.trans (Nat.gcd_dvd_left _ _))
    have hn7 : n ≤ 7 := by omega
    have hgle : Nat.gcd n (qEps lin q) ≤ 7 := (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)).trans hn7
    have hgpos : 0 < Nat.gcd n (qEps lin q) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hnd : ¬ p ^ 2 ∣ Nat.gcd n (qEps lin q) := fun h => by
      have := Nat.le_of_dvd hgpos h
      nlinarith
    have hdd' : dd ≤ 2 := by
      have h1 := hKD26f ↥K c.hat p hp hp2 (Or.inl ⟨n, q, lin, hS, hpg, hnd⟩) D hDel
      rw [hdd, hii, hi1, pow_one, ← pow_two] at h1
      have h2 := (Nat.pow_le_pow_iff_right hpos).1 h1
      omega
    have hb0' : b0 = 2 := by omega
    have hr3 : GLATwoLocalRank p ↥K ≤ 3 := by omega
    have hZeq : Nat.card (Subgroup.center ↥K) = p := by
      obtain ⟨j, hj⟩ := hZp.exists_card_eq
      have hj1 : 1 ≤ j := by
        by_contra h0
        have : j = 0 := by omega
        rw [this, pow_zero] at hj
        exact hZ1 (Subgroup.eq_bot_of_card_eq _ hj)
      have hj2 : j ≤ 1 := by
        by_contra h2
        have h3 : p ^ 2 ∣ p ^ j := pow_dvd_pow p (by omega)
        rw [← hj] at h3
        exact hnd (h3.trans hZg)
      have : j = 1 := by omega
      rw [hj, this, pow_one]
    have hfac : (Nat.gcd n (qEps lin q)).factorization p = 1 := by
      have h1 : 1 ≤ (Nat.gcd n (qEps lin q)).factorization p :=
        (hp.pow_dvd_iff_le_factorization hgpos.ne').1 (by rwa [pow_one])
      have h2 : ¬ 2 ≤ (Nat.gcd n (qEps lin q)).factorization p :=
        fun h => hnd ((hp.pow_dvd_iff_le_factorization hgpos.ne').2 h)
      omega
    have hn2 := hg2 (by rw [hZeq, hfac, pow_one])
    have hn5 : n ≤ 5 := by omega
    have hnp : n = p := by
      obtain ⟨t, ht⟩ := hpg.trans (Nat.gcd_dvd_left _ _)
      have ht1 : t ≠ 0 := by rintro rfl; omega
      have ht2 : t = 1 := by
        by_contra h
        have : 2 ≤ t := by omega
        nlinarith
      rw [ht, ht2, mul_one]
    subst hnp
    have hpq : n ∣ qEps lin q := (Nat.dvd_gcd_iff.1 hpg).2
    exact hfinal hb0' (hKD26h ↥K c.hat.1 n hp hp2 q lin hS hpq hZeq d hdp hd1)
  ·
    exfalso
    have h4' := (hKD26g ↥K c.hat.1 p hp hp2 hZp hZdvd).2 q lin hS hp3' h3
    have hdd' : dd ≤ 2 := by
      have h1 := hKD26f ↥K c.hat p hp hp2 (Or.inr ⟨q, lin, hS, hp3', h3⟩) D hDel
      rw [hdd, hii, hi1, pow_one, ← pow_two] at h1
      have h2 := (Nat.pow_le_pow_iff_right hpos).1 h1
      omega
    omega

theorem i2611Core_of_kd (hKD26a : KD26a) (hKD26bc : KD26bc) (hKD26d : KD26d) (hKD26e : KD26e)
    (hKD26f : KD26f) (hKD26g : KD26g) (hKD26h : KD26h) : I2611Core := by
  intro X _ _ p hp hp2 K B hKn hcore hhat hcyc hBel hcard h4 hT hB0
  haveI := hKn
  have c : CoreCtx p K B := ⟨hp, hp2, hcore, hhat, hcyc, hBel, hcard, h4, hT, hB0⟩
  by_cases h1 : p ^ 3 ≤ Nat.card (CoreCtx.B0 K B)
  · exact Or.inl (core_isGB_of_card_ge c h1)
  by_cases h2 : B.map (MulAut.conjNormal (H := K)) ⊓ inner ↥K = ⊥
  · exact Or.inl (i2611_step1 hKD26a hKD26bc hKD26d c h2)
  by_cases h3 : ∃ b ∈ B, ∃ u ∈ K, u ^ p = 1 ∧ (∀ y ∈ K, b * y * b⁻¹ = u * y * u⁻¹) ∧
      ∃ y ∈ K, u * y ≠ y * u
  · obtain ⟨b, hb, u, huK, hup, hbu, y, hy, hne⟩ := h3
    exact Or.inr (i2611_step2 c hb huK ⟨y, hy, hne⟩ hup hbu)
  · refine Or.inl (i2611_step3 hKD26a hKD26e hKD26f hKD26g hKD26h c h1 h2 ?_)
    intro b hb u huK hup hbu y hy
    by_contra hne
    exact h3 ⟨b, hb, u, huK, hup, hbu, y, hy, hne⟩

theorem i2611Printed_of_kd (hKD26a : KD26a) (hKD26bc : KD26bc) (hKD26d : KD26d)
    (hKD26e : KD26e) (hKD26f : KD26f) (hKD26g : KD26g) (hKD26h : KD26h) : I2611Printed :=
  i2611Printed_of_core (i2611Core_of_kd hKD26a hKD26bc hKD26d hKD26e hKD26f hKD26g hKD26h)

theorem i2611UsedAt_of_kd (hKD26a : KD26a) (hKD26bc : KD26bc) (hKD26d : KD26d)
    (hKD26e : KD26e) (hKD26f : KD26f) (hKD26g : KD26g) (hKD26h : KD26h) {G : Type} [Group G]
    [Finite G] (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I2611UsedAt G p :=
  i2611UsedAt_of_printed (i2611Printed_of_kd hKD26a hKD26bc hKD26d hKD26e hKD26f hKD26g hKD26h)
    hsimple hnonab hKP hp hp2

end CFSG.LocalAnalysis.GLTheoremA

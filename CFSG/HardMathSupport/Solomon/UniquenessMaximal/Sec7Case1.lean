module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Perm
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_gammaOneThree_of_normalized (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {Y : Subgroup G} (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ 3 ∣ Nat.card Y) : Y ≤ gammaOneThree B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card B = 3 ^ (3 + 1) := hS.card_eq hB
  have := hS.nontrivial hB
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY hY).trans
    (iSup₂_le fun K hK => inf_le_right.trans ?_)
  have hKcard : Nat.card K = 3 ^ 3 := card_eq_of_index_eq Nat.prime_three hK.1 hK.2 hcard
  exact le_iSup₂_of_le K ⟨hK.1, isElemAbelian_mono hB.1.1 hK.1, hKcard⟩ le_rfl

theorem gammaOneThree_le_glbCore (B : Subgroup G) : gammaOneThree B ≤ GLBCore 3 3 B := by
  refine iSup₂_le fun E hE => ?_
  have h3 : 3 ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hE.2.1 hE.2.2
  exact (Subgroup.centralizer_le_normalizer _).trans
    (le_sSup ⟨E, hE.1, h3, rfl⟩ : Subgroup.normalizer (E : Set G) ≤ GLBCore 3 3 B)

theorem le_glbCore_of_normalized (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {Y : Subgroup G} (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ 3 ∣ Nat.card Y) : Y ≤ GLBCore 3 3 B :=
  (le_gammaOneThree_of_normalized hS hB hBY hY).trans (gammaOneThree_le_glbCore B)

omit [Finite G] in
theorem le_centralizer_of_mem {B : Subgroup G} (hB : IsElemAbelian 3 B) {b : G} (hb : b ∈ B) :
    B ≤ Subgroup.centralizer ({b} : Set G) := fun _ hb' =>
  Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hb' hb)

omit [Finite G] in
theorem le_centralizer_self {B : Subgroup G} (hB : IsElemAbelian 3 B) :
    B ≤ Subgroup.centralizer (B : Set G) := fun _ hb' =>
  Subgroup.mem_centralizer_iff.2 fun _ hc => elemAbelian_comm hB hc hb'

theorem lambdaStar_le_of_lambdaOf_le (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {N : Subgroup G} (hN : GLBCore 3 3 B ≤ N) {x : G} (hx : x ∈ B)
    (h : lambdaOf 3 B x ≤ N) : lambdaStar 3 B x ≤ N := by
  refine sup_le (sup_le h ?_) ?_
  · exact (le_glbCore_of_normalized hS hB
      ((le_centralizer_of_mem hB.1.1 hx).trans (le_normalizer_glaPPrimeCoreOf 3 _))
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _)).trans hN
  · exact (le_glbCore_of_normalized hS hB
      ((le_centralizer_self hB.1.1).trans (le_normalizer_glaPPrimeCoreOf 3 _))
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _)).trans hN

theorem exists_isHSet_of_no_preUniqueness (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h67 : Prop67Out B)
    (hno : ¬ ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M) : ∃ K : Subgroup G, IsHSet B K := by
  by_contra hH
  push Not at hH
  refine hno ⟨M₀, ?_, h63.1, h63.2⟩
  refine iSup₂_le fun x hx => iSup_le fun hx1 => ?_
  refine lambdaStar_le_of_lambdaOf_le hS hB h63.1 hx ?_
  refine sSup_le fun L hL => ?_
  by_contra hLM
  exact hH L (h67 x hx hx1 L hL.1 hL.2 fun h => hLM (h.trans h63.1))

omit [Finite G] in
theorem glaPLayer_le (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem kZeroOf_le (B K : Subgroup G) : kZeroOf B K ≤ K :=
  (glaPLayer_le 3 _).trans inf_le_left

theorem le_gammaOneThree_self (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B) :
    B ≤ gammaOneThree B := by
  have hcard : Nat.card B = 3 ^ 4 := hS.card_eq hB
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 3 (n := 3)
    (show 3 ^ 3 ∣ Nat.card B from hcard ▸ pow_dvd_pow 3 (by norm_num))
  have hE : IsEkIn 3 3 B (F.map B.subtype) := by
    refine ⟨Subgroup.map_subtype_le F, ?_, ?_⟩
    · exact isElemAbelian_mono hB.1.1 (Subgroup.map_subtype_le F)
    · rw [Subgroup.card_map_of_injective B.subtype_injective, hF]
  refine le_iSup₂_of_le _ hE ?_
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact elemAbelian_comm hB.1.1 (hE.1 he) hb

omit [Finite G] in
theorem exists_ne_one_mem_inf {B E A : Subgroup G} (hBc : Nat.card B = 81) (hE : E ≤ B)
    (hA : A ≤ B) (hEc : 27 ≤ Nat.card E) (hAc : Nat.card A = 9) : ∃ a ∈ E ⊓ A, a ≠ 1 := by
  have h1 := Subgroup.relIndex_mul_card E B
  rw [inf_eq_left.2 hE] at h1
  have h2 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.2 hA] at h2
  have h3 := Subgroup.relIndex_mul_card (E ⊓ A) B
  rw [inf_eq_left.2 (inf_le_left.trans hE)] at h3
  have h4 : (E ⊓ A).relIndex B ≤ E.relIndex B * A.relIndex B := Subgroup.relIndex_inf_le
  rw [hBc] at h1 h2 h3
  rw [hAc] at h2
  have hE3 : E.relIndex B ≤ 3 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hA9 : A.relIndex B = 9 := by omega
  have hle : (E ⊓ A).relIndex B ≤ 27 := by
    calc (E ⊓ A).relIndex B ≤ E.relIndex B * A.relIndex B := h4
      _ ≤ 3 * 9 := by rw [hA9]; exact Nat.mul_le_mul_right 9 hE3
  by_contra hcon
  push Not at hcon
  have hbot : E ⊓ A = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun a ha => hcon a ha
  have h5 : Nat.card ↥(E ⊓ A) = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [h5] at h3
  omega

omit [Finite G] in
theorem le_normalizer_glaPPrimeCoreOf_of_le' {p : ℕ} {X M : Subgroup G}
    (h : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  intro g hg
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (h hg)
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, h1]

theorem card_eq_81 (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B) :
    Nat.card B = 81 := by
  have := hS.card_eq hB
  norm_num at this
  exact this

theorem gammaOneThree_ne_top (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (h63 : Prop63Out B M₀) : gammaOneThree B ≠ ⊤ := by
  have := hS.simple
  intro htop
  have hM0 : M₀ ≠ ⊤ := Proving.ne_top_of_even_card_glaPPrimeCoreOf (G := G) Nat.prime_three
    hS.beta.2.2.1 h63.2
  exact hM0 (top_le_iff.1 (htop ▸ (gammaOneThree_le_glbCore B).trans h63.1))

theorem permutable_gammaOneThree (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B)
    {K : Subgroup G} (hK : IsHSet B K) :
    Permutable K (gammaOneThree B) ∧ K ⊔ gammaOneThree B ≠ ⊤ := by
  have := hS.simple
  have hfacts := h68 K hK
  have hB81 := card_eq_81 hS hB
  have step1 : ∀ a ∈ centralizerQuot B K, a ≠ 1 →
      GLAPPrimeCoreOf 3 (bClosureIa K a) ≤ gammaOneThree B ⊓ Subgroup.centralizer ({a} : Set G) ∧
      Permutable (kZeroOf B K) (gammaOneThree B ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1
    have hI := hfacts.ia a ha ha1
    have hBa : B ≤ Subgroup.centralizer ({a} : Set G) :=
      le_centralizer_of_mem hB.1.1 (hfacts.aK.1 ha)
    have hBI : B ≤ Subgroup.normalizer (bClosureIa K a : Set G) := hBa.trans hI.normal
    have hO : GLAPPrimeCoreOf 3 (bClosureIa K a) ≤
        gammaOneThree B ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine le_inf (le_gammaOneThree_of_normalized hS hB
        (le_normalizer_glaPPrimeCoreOf_of_le' hBI) (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _))
        ((Subgroup.map_subtype_le _).trans hI.component.1)

    exact ⟨hO, permutable_of_normalizes hI.kZero_le hI.le_kZero_sup
      (le_normalizer_glaPPrimeCoreOf 3 _) (inf_le_right.trans hI.normal) hO⟩
  let Mstar : Subgroup G := ⨆ a : {a : G // a ∈ centralizerQuot B K ∧ a ≠ 1},
    gammaOneThree B ⊓ Subgroup.centralizer ({a.1} : Set G)
  have step2 : Permutable (kZeroOf B K) Mstar :=
    Permutable.iSup fun a => (step1 a.1 a.2.1 a.2.2).2
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, hnM⟩ := hK
  have hxA : x ∈ centralizerQuot B K := by
    refine Subgroup.subset_closure ⟨hxB, fun k hk => ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hxK.1 hk)
    have : x * k * x⁻¹ * k⁻¹ = 1 := by rw [← h]; group
    rw [this]; exact Subgroup.one_mem _
  have hIx := hfacts.ia x hxA hx1
  have hIxK : bClosureIa K x = K :=
    hU x hxB hx1 _ K hIx.component hxK
      ((le_centralizer_of_mem hB.1.1 hxB).trans hIx.normal) hfacts.normalizes
      hIx.lThreeFour hfacts.lThreeFour hfacts.fK
  have hOK : GLAPPrimeCoreOf 3 K ≤ Mstar := by
    have := (step1 x hxA hx1).1
    rw [hIxK] at this
    exact this.trans (le_iSup (fun a : {a : G // a ∈ centralizerQuot B K ∧ a ≠ 1} =>
      gammaOneThree B ⊓ Subgroup.centralizer ({a.1} : Set G)) ⟨x, hxA, hx1⟩)
  have hKle : K ≤ kZeroOf B K ⊔ GLAPPrimeCoreOf 3 K := by
    have := hIx.le_kZero_sup
    rwa [hIxK] at this
  have step3 : Permutable K Mstar :=
    permutable_of_le_sup (kZeroOf_le B K) hKle (le_normalizer_glaPPrimeCoreOf 3 K) hOK step2
  have hMstar : Mstar = gammaOneThree B := by
    refine le_antisymm (iSup_le fun a => inf_le_left) ?_
    refine iSup₂_le fun E hE => ?_
    obtain ⟨a, haEA, ha1⟩ := exists_ne_one_mem_inf hB81 hE.1 hfacts.aK.1
      (by rw [hE.2.2]; norm_num) (by rw [hfacts.aK.2.2]; norm_num)
    refine le_trans ?_ (le_iSup (fun a : {a : G // a ∈ centralizerQuot B K ∧ a ≠ 1} =>
      gammaOneThree B ⊓ Subgroup.centralizer ({a.1} : Set G)) ⟨a, haEA.2, ha1⟩)
    exact le_inf (le_iSup₂_of_le E hE le_rfl)
      (Subgroup.centralizer_le (by simpa using haEA.1))
  rw [hMstar] at step3
  refine ⟨step3, ?_⟩
  exact sup_ne_top_of_permutable step3 (gammaOneThree_ne_top hS h63)
    (le_gammaOneThree_self hS hB hxB) hx1 hxK.1

omit [Finite G] in
theorem mem_centralizerQuot_of_le_centralizer {B K : Subgroup G} {x : G} (hxB : x ∈ B)
    (hK : K ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ centralizerQuot B K := by
  refine Subgroup.subset_closure ⟨hxB, fun k hk => ?_⟩
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
  have : x * k * x⁻¹ * k⁻¹ = 1 := by rw [← h]; group
  rw [this]; exact Subgroup.one_mem _

theorem glaPPrimeCoreOf_le_gammaOneThree (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {K : Subgroup G} (hBK : B ≤ Subgroup.normalizer (K : Set G)) :
    GLAPPrimeCoreOf 3 K ≤ gammaOneThree B :=
  le_gammaOneThree_of_normalized hS hB (le_normalizer_glaPPrimeCoreOf_of_le' hBK)
    (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _)

theorem le_kZeroOf_sup_of_isHSet {B : Subgroup G} (hBel : IsElemAbelian 3 B) (h68 : Prop68Out B)
    (hU : UniqComp B) {K : Subgroup G} (hK : IsHSet B K) :
    K ≤ kZeroOf B K ⊔ GLAPPrimeCoreOf 3 K := by
  have hf := h68 K hK
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := hK
  have hxA : x ∈ centralizerQuot B K := mem_centralizerQuot_of_le_centralizer hxB hxK.1
  have hIx := hf.ia x hxA hx1
  have hIxK : bClosureIa K x = K :=
    hU x hxB hx1 _ K hIx.component hxK
      ((le_centralizer_of_mem hBel hxB).trans hIx.normal) hf.normalizes
      hIx.lThreeFour hf.lThreeFour hf.fK
  have := hIx.le_kZero_sup
  rwa [hIxK] at this

theorem le_sup_gammaOneThree_of_case1 (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) (h68 : Prop68Out B) (hU : UniqComp B) (hC : Case1Hyp B)
    {K K₁ : Subgroup G} (hK : IsHSet B K) (hK₁ : IsHSet B K₁) : K₁ ≤ K ⊔ gammaOneThree B := by
  have hf := h68 K hK
  have hf₁ := h68 K₁ hK₁
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK₁
  have hxA : x ∈ centralizerQuot B K := by
    rw [← hC K₁ K hK₁ hK]
    exact mem_centralizerQuot_of_le_centralizer hxB hxK.1
  have hI := hf.ia x hxA hx1
  have hIK : bClosureIa K x = K₁ :=
    hU x hxB hx1 _ K₁ hI.component hxK
      ((le_centralizer_of_mem hB.1.1 hxB).trans hI.normal) hf₁.normalizes
      hI.lThreeFour hf₁.lThreeFour hf₁.fK
  have h1 : K₁ ≤ kZeroOf B K ⊔ GLAPPrimeCoreOf 3 K₁ := by
    have := hI.le_kZero_sup
    rwa [hIK] at this
  exact h1.trans (sup_le_sup (kZeroOf_le B K) (glaPPrimeCoreOf_le_gammaOneThree hS hB hf₁.normalizes))

omit [Finite G] in
theorem gLBConj_centralizer_singleton (g a : G) :
    GLBConj g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
  ext w
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc w * (g⁻¹ * a * g) = g⁻¹ * ((g * w * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * w * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * a * g) * w := by group
  · intro h
    calc g * w * g⁻¹ * a = g * (w * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * w) * g⁻¹ := by rw [h]
      _ = a * (g * w * g⁻¹) := by group

theorem IsLThreeFour.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y := by
  obtain ⟨F, _, _, hc, ⟨f⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, ⟨e.symm.trans f⟩⟩

theorem exists_elemAbelian_ge_of_le_pRank {Q : Subgroup G} {k : ℕ} (hk : 0 < k)
    (h : k ≤ CFSG.Open.pRank 3 Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian 3 E ∧ ∃ j : ℕ, k ≤ j ∧ Nat.card E = 3 ^ j := by
  set S : Set ℕ := {j | ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ j} with hS
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro n ⟨F, -, -, hF⟩
    have h1 : n < 3 ^ n := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : CFSG.Open.pRank 3 Q = 0 := by
      unfold CFSG.Open.pRank
      rw [← hS, hne]
      simp
    omega
  obtain ⟨E, hEQ, hEel, hEc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEQ, hEel, _, h, hEc⟩

theorem permutable_glbCore_of_case1 (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B)
    (hC : Case1Hyp B) {K : Subgroup G} (hK : IsHSet B K) :
    Permutable K (GLBCore 3 3 B) ∧ K ⊔ GLBCore 3 3 B ≠ ⊤ := by
  have := hS.simple
  have hf := h68 K hK
  have hB81 := card_eq_81 hS hB
  have h74 := permutable_gammaOneThree hS hB h63 h68 hU hK
  have hKle := le_kZeroOf_sup_of_isHSet hB.1.1 h68 hU hK
  have hM2M1 := gammaOneThree_le_glbCore B
  have hnM : ¬ K ≤ GLBCore 3 3 B := hK.2.2
  have hOK : GLAPPrimeCoreOf 3 K ≤ GLBCore 3 3 B :=
    (glaPPrimeCoreOf_le_gammaOneThree hS hB hf.normalizes).trans hM2M1
  have key : ∀ Q : Subgroup G, Q ≤ B → 3 ≤ CFSG.Open.pRank 3 Q → ∀ y ∈ Subgroup.normalizer (Q : Set G),
      ∀ k ∈ K, ∃ m ∈ GLBCore 3 3 B, ∃ k' ∈ K, k * y = m * k' := by
    intro Q hQB hQ3 y hy k hk
    have hyM1 : y ∈ GLBCore 3 3 B :=
      (le_sSup ⟨Q, hQB, hQ3, rfl⟩ : Subgroup.normalizer (Q : Set G) ≤ GLBCore 3 3 B) hy
    obtain ⟨E, hEQ, hEel, j, hj, hEc⟩ := exists_elemAbelian_ge_of_le_pRank (by norm_num) hQ3
    obtain ⟨a, haEA, ha1⟩ := exists_ne_one_mem_inf hB81 (hEQ.trans hQB) hf.aK.1
      (by
        rw [hEc]
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj)
      (by rw [hf.aK.2.2]; norm_num)
    have haA : a ∈ centralizerQuot B K := (Subgroup.mem_inf.1 haEA).2
    have haQ : a ∈ Q := hEQ (Subgroup.mem_inf.1 haEA).1
    have haB : a ∈ B := hQB haQ
    have hIa := hf.ia a haA ha1
    have hIaM : ¬ bClosureIa K a ≤ GLBCore 3 3 B := fun hle =>
      hnM (hKle.trans (sup_le ((hIa.kZero_le).trans hle) hOK))
    have hIay : IsHSet B (GLBConj y (bClosureIa K a)) := by
      have ha'Q : y⁻¹ * a * y ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) a).1 haQ
        simpa using this
      have ha'1 : y⁻¹ * a * y ≠ 1 := by
        intro h
        apply ha1
        calc a = y * (y⁻¹ * a * y) * y⁻¹ := by group
          _ = 1 := by rw [h]; group
      have hcomp := glaPComponent_gLBConj hIa.component y
      rw [gLBConj_centralizer_singleton] at hcomp
      refine ⟨⟨_, hQB ha'Q, ha'1, hcomp⟩,
        Or.inl (IsLThreeFour.of_mulEquiv (conjQuotEquiv 3 y (bClosureIa K a)) hIa.lThreeFour), ?_⟩
      intro hle
      apply hIaM
      have h1 := gLBConj_mono y⁻¹ hle
      rw [gLBConj_inv_gLBConj, gLBConj_eq_of_mem_normalizer
        (Subgroup.inv_mem _ (Subgroup.le_normalizer hyM1))] at h1
      exact h1
    have h77 := le_sup_gammaOneThree_of_case1 hS hB h68 hU hC hK hIay
    have hk1 : k ∈ ((GLAPPrimeCoreOf 3 K ⊔ (bClosureIa K a ⊓ K) : Subgroup G) : Set G) := by
      have : K ≤ GLAPPrimeCoreOf 3 K ⊔ (bClosureIa K a ⊓ K) :=
        hKle.trans (sup_le (le_sup_of_le_right (le_inf hIa.kZero_le (kZeroOf_le B K)))
          le_sup_left)
      exact this hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (le_normalizer_glaPPrimeCoreOf 3 K))] at hk1
    obtain ⟨o, ho, i, hi, rfl⟩ := hk1
    have hi' : y⁻¹ * i * y ∈ ((gammaOneThree B ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm]
      refine h77 ?_
      rw [mem_gLBConj]
      have h3 : y * (y⁻¹ * i * y) * y⁻¹ = i := by group
      rw [h3]
      exact (Subgroup.mem_inf.1 hi).1
    rw [h74.1.symm.coe_sup] at hi'
    obtain ⟨m₂, hm₂, k'', hk'', e⟩ := hi'
    have e : m₂ * k'' = y⁻¹ * i * y := e
    refine ⟨o * y * m₂, mul_mem (mul_mem (hOK ho) hyM1) (hM2M1 hm₂), k'', hk'', ?_⟩
    calc o * i * y = o * y * (y⁻¹ * i * y) := by group
      _ = o * y * (m₂ * k'') := by rw [e]
      _ = o * y * m₂ * k'' := by group
  have hM1 : GLBCore 3 3 B = ⨆ s : {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ B ∧
      3 ≤ CFSG.Open.pRank 3 Q ∧ N = Subgroup.normalizer (Q : Set G)}, (s : Subgroup G) :=
    sSup_eq_iSup' _
  have hperm : Permutable K (GLBCore 3 3 B) := by
    rw [hM1]
    refine permutable_iSup_of_forall _ (fun s y hy k hk => ?_)
    obtain ⟨Q, hQB, hQ3, hs⟩ := s.2
    have hy' : y ∈ Subgroup.normalizer (Q : Set G) := by
      have : y ∈ (s : Subgroup G) := hy
      rwa [hs] at this
    obtain ⟨m, hm, k', hk', e⟩ := key Q hQB hQ3 y hy' k hk
    exact ⟨m, by rw [← hM1]; exact hm, k', hk', e⟩
  refine ⟨hperm, ?_⟩
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK
  have hM1ne : GLBCore 3 3 B ≠ ⊤ := fun htop =>
    Proving.ne_top_of_even_card_glaPPrimeCoreOf (G := G) Nat.prime_three hS.beta.2.2.1 h63.2
      (top_le_iff.1 (htop ▸ h63.1))
  exact sup_ne_top_of_permutable hperm hM1ne
    (hM2M1 (le_gammaOneThree_self hS hB hxB)) hx1 hxK.1

theorem le_glaPLayer_self {X K : Subgroup G} (hK : GLAPComponent 3 X K) : K ≤ GLAPLayer 3 K :=
  le_sSup (glaPComponent_of_le Nat.prime_three hK le_rfl hK.1)

theorem exists_preUniqueness_of_case1 (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h67 : Prop67Out B) (h68 : Prop68Out B)
    (hU : UniqComp B) (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B) (hC : Case1Hyp B)
    (hH : ∃ K : Subgroup G, IsHSet B K) : ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M := by
  obtain ⟨K, hK⟩ := hH
  have := hS.simple
  obtain ⟨-, hne⟩ := permutable_glbCore_of_case1 hS hB h63 h68 hU hC hK
  have hM2M1 := gammaOneThree_le_glbCore B
  have hBM1 : B ≤ GLBCore 3 3 B := (le_gammaOneThree_self hS hB).trans hM2M1
  have hKN : K ⊔ gammaOneThree B ≤ K ⊔ GLBCore 3 3 B := sup_le_sup_left hM2M1 K
  refine ⟨K ⊔ GLBCore 3 3 B, ?_, le_sup_right, ?_⟩
  · refine iSup₂_le fun x hx => iSup_le fun hx1 => ?_
    refine lambdaStar_le_of_lambdaOf_le hS hB le_sup_right hx ?_
    refine sSup_le fun L hL => ?_
    by_cases hLM : L ≤ GLBCore 3 3 B
    · exact hLM.trans le_sup_right
    · exact (le_sup_gammaOneThree_of_case1 hS hB h68 hU hC hK
        (h67 x hx hx1 L hL.1 hL.2 hLM)).trans hKN
  · obtain ⟨⟨x, -, -, hxK⟩, -, -⟩ := id hK
    have hcov : Covers3 (K ⊔ GLBCore 3 3 B) K :=
      le_sup_of_le_left (le_inf le_sup_left le_rfl)
    have h5 := h75 K hK (K ⊔ GLBCore 3 3 B) hne (hBM1.trans le_sup_right) hcov
    have hKl : GLAPLayer 3 (K ⊓ (K ⊔ GLBCore 3 3 B)) = K := by
      rw [inf_eq_left.2 le_sup_left]
      exact le_antisymm (glaPLayer_le 3 K) (le_glaPLayer_self hxK)
    rw [hKl] at h5
    obtain ⟨I, hI, hIbar⟩ := exists_glaPComponent_barX_eq (p := 3) (K ⊔ GLBCore 3 3 B) h5
    have h6 := h76 K hK (K ⊔ GLBCore 3 3 B) hne hKN I hI hIbar
    have hcomm : ⁅I, GLAPPrimeCoreOf 3 (K ⊔ GLBCore 3 3 B)⁆ ≤
        GLAPPrimeCoreOf 3 (K ⊔ GLBCore 3 3 B) := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      have h1 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf 3 (K ⊔ GLBCore 3 3 B) (hI.1 ha)) b).1 hb
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hb)
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 h6).trans (Subgroup.card_dvd_of_le hcomm))

theorem not_case1_of_no_preUniqueness (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h67 : Prop67Out B) (h68 : Prop68Out B)
    (hU : UniqComp B) (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B)
    (hno : ¬ ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M) : ¬ Case1Hyp B := fun hC =>
  hno (exists_preUniqueness_of_case1 hS hB h63 h67 h68 hU h75 h76 hC
    (exists_isHSet_of_no_preUniqueness hS hB h63 h67 hno))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem sec9_exists_subgroup_card_eq_of_dvd_comm :
    ∀ (n : ℕ) (H : Type) [Group H] [Finite H], (∀ x y : H, x * y = y * x) →
      ∀ d : ℕ, Nat.card H = n → d ∣ n → ∃ K : Subgroup H, Nat.card K = d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hc d hn hd
  have hpos : 0 < Nat.card H := Nat.card_pos
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · interval_cases d
    · rw [zero_dvd_iff] at hd
      omega
    · exact ⟨⊥, Subgroup.card_bot⟩
  · have hqp : (Nat.minFac d).Prime := Nat.minFac_prime (by omega)
    have hqd : Nat.minFac d ∣ d := Nat.minFac_dvd d
    set q := Nat.minFac d with hq_def
    have hq2 : 2 ≤ q := hqp.two_le
    have hq0 : 0 < q := by omega
    haveI : Fact q.Prime := ⟨hqp⟩
    have hdH : d ∣ Nat.card H := by rw [hn]; exact hd
    have hqn : q ∣ Nat.card H := hqd.trans hdH
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqn
    set N : Subgroup H := Subgroup.zpowers x with hN_def
    have hNcard : Nat.card N = q := by rw [hN_def, Nat.card_zpowers, hx]
    haveI hNnormal : N.Normal :=
      ⟨fun n hn g => by
        have : g * n * g⁻¹ = n := by rw [hc g n, mul_inv_cancel_right]
        rw [this]; exact hn⟩
    have hQc : ∀ a b : H ⧸ N, a * b = b * a := by
      intro a b
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    have hmq : Nat.card (H ⧸ N) * q = Nat.card H := by
      have h1 := Subgroup.index_mul_card (H := N)
      rw [hNcard, Subgroup.index_eq_card] at h1
      exact h1
    have hmpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
    have hmn : Nat.card (H ⧸ N) < n := by
      rw [← hn, ← hmq]
      nlinarith
    obtain ⟨c, hc'⟩ := hd
    have hdm : d / q ∣ Nat.card (H ⧸ N) := by
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hq0 ?_⟩
      rw [mul_comm q, hmq, hn.trans hc', ← mul_assoc, Nat.mul_div_cancel' hqd]
    obtain ⟨Kb, hKb⟩ := ih (Nat.card (H ⧸ N)) hmn (H ⧸ N) hQc (d / q) rfl hdm
    refine ⟨Kb.comap (QuotientGroup.mk' N), ?_⟩
    have hKidx : (Kb.comap (QuotientGroup.mk' N)).index = Kb.index :=
      Subgroup.index_comap_of_surjective (H := Kb) (QuotientGroup.mk'_surjective N)
    have hK1 : (Kb.comap (QuotientGroup.mk' N)).index * Nat.card (Kb.comap (QuotientGroup.mk' N)) =
        Nat.card H := Subgroup.index_mul_card _
    have hKb1 : Kb.index * Nat.card Kb = Nat.card (H ⧸ N) := Subgroup.index_mul_card _
    have hk0 : Kb.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hK1' : Kb.index * Nat.card (Kb.comap (QuotientGroup.mk' N)) = Nat.card H := by
      rw [← hKidx]; exact hK1
    have key : Kb.index * Nat.card (Kb.comap (QuotientGroup.mk' N)) = Kb.index * d := by
      rw [hK1', ← hmq, ← hKb1, hKb, mul_assoc, Nat.div_mul_cancel hqd]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) key

theorem sec9_exists_isPPlane_le {G : Type} [Group G] [Finite G] {p : ℕ} {Q : Subgroup G}
    (hQ : 2 ≤ CFSG.Open.pRank p Q) : ∃ D : Subgroup G, D ≤ Q ∧ IsPPlane p D := by
  unfold CFSG.Open.pRank at hQ
  set S : Set ℕ := {k | ∃ E : Subgroup G, E ≤ Q ∧ CFSG.Open.IsElemAbelian p E ∧
    Nat.card E = p ^ k} with hS
  have hbdd : BddAbove S := by
    by_contra hb
    rw [csSup_of_not_bddAbove hb, csSup_empty] at hQ
    simp at hQ
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty] at hQ
    simp at hQ
  obtain ⟨E, hEQ, hEa, hEc⟩ := Nat.sSup_mem hne hbdd
  have hdvd : p ^ 2 ∣ Nat.card E := by
    rw [hEc]
    exact pow_dvd_pow p hQ
  obtain ⟨K, hK⟩ := sec9_exists_subgroup_card_eq_of_dvd_comm (Nat.card E) E
    (fun x y => Subtype.ext (elemAbelian_comm hEa x.2 y.2)) (p ^ 2) rfl hdvd
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEQ, ?_⟩
  unfold IsPPlane
  refine ⟨?_, ?_⟩
  · exact isElemAbelian_mono hEa (Subgroup.map_subtype_le K)
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem sec9_gLBConj_commutator {G : Type*} [Group G] (g : G) (X Y : Subgroup G) :
    GLBConj g ⁅X, Y⁆ = ⁅GLBConj g X, GLBConj g Y⁆ := by
  unfold GLBConj
  rw [Subgroup.map_commutator]

theorem sec9_gLBConj_inf {G : Type*} [Group G] (g : G) (X Y : Subgroup G) :
    GLBConj g (X ⊓ Y) = GLBConj g X ⊓ GLBConj g Y := by
  ext z
  simp only [mem_gLBConj, Subgroup.mem_inf]

theorem sec9_gLBConj_le_of_mem {G : Type*} [Group G] {N X : Subgroup G} {y : G} (hy : y ∈ N)
    (hX : X ≤ N) : GLBConj y X ≤ N := by
  intro g hg
  rw [mem_gLBConj] at hg
  have h1 := N.mul_mem (N.mul_mem (N.inv_mem hy) (hX hg)) hy
  have e : y⁻¹ * (y * g * y⁻¹) * y = g := by group
  rwa [e] at h1

theorem sec9_gLBConj_eq_self {G : Type} [Group G] {N : Subgroup G} (hN : GLAIsMaxTwoLocal N)
    {z : G} (hz : z ∈ N) : GLBConj z N = N := by
  obtain ⟨⟨P, -, -, hPN⟩, -⟩ := hN
  subst hPN
  rw [← normalizer_gLBConj, gLBConj_eq_of_mem_normalizer hz]

theorem sec9_isElemAbelian_gLBConj {G : Type*} [Group G] {p : ℕ} (g : G) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.Open.IsElemAbelian p (GLBConj g E) :=
  CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj g⁻¹).toMonoidHom

theorem sec9_card_gLBConj {G : Type*} [Group G] (g : G) (E : Subgroup G) :
    Nat.card (GLBConj g E) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem sec9_pRank_gLBConj {G : Type} [Group G] [Finite G] (p : ℕ) (g : G) (H : Subgroup G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H := by
  have key : ∀ (g : G) (H : Subgroup G),
      {k : ℕ | ∃ E : Subgroup G, E ≤ GLBConj g H ∧ CFSG.Open.IsElemAbelian p E ∧
        Nat.card E = p ^ k} ⊆
      {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    intro g H k hk
    obtain ⟨E, hE, hEa, hEc⟩ := hk
    refine ⟨GLBConj g⁻¹ E, ?_, sec9_isElemAbelian_gLBConj g⁻¹ hEa, ?_⟩
    · have := gLBConj_mono g⁻¹ hE
      rwa [gLBConj_inv_gLBConj] at this
    · rw [sec9_card_gLBConj]
      exact hEc
  unfold CFSG.Open.pRank
  refine congrArg sSup (Set.Subset.antisymm (key g H) ?_)
  have := key g⁻¹ (GLBConj g H)
  rwa [gLBConj_inv_gLBConj] at this

theorem sec9_map_conjEquiv_subgroupOf {G : Type*} [Group G] (g : G) (X K : Subgroup G) :
    (K.subgroupOf X).map (conjEquiv g X).toMonoidHom = (GLBConj g K).subgroupOf (GLBConj g X) := by
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.1 ht
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf, mem_gLBConj, ← hxt]
    have e : g * (((conjEquiv g X).toMonoidHom x : ↥(GLBConj g X)) : G) * g⁻¹ = (x : G) := by
      show g * (((conjEquiv g X x) : ↥(GLBConj g X)) : G) * g⁻¹ = (x : G)
      rw [coe_conjEquiv]
      group
    rw [e]
    exact hx
  · intro ht
    rw [Subgroup.mem_subgroupOf, mem_gLBConj] at ht
    refine Subgroup.mem_map.2 ⟨(conjEquiv g X).symm t, ?_, (conjEquiv g X).apply_symm_apply t⟩
    rw [Subgroup.mem_subgroupOf, coe_conjEquiv_symm]
    exact ht

noncomputable def sec9QuotPCore {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    (↥X ⧸ CFSG.pCore 2 ↥X) ≃* (↥(GLBConj g X) ⧸ CFSG.pCore 2 ↥(GLBConj g X)) :=
  QuotientGroup.congr _ _ (conjEquiv g X)
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g X))

theorem sec9_map_quot_pCore {G : Type*} [Group G] (g : G) (X K : Subgroup G) :
    ((K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map
        (sec9QuotPCore g X : (↥X ⧸ CFSG.pCore 2 ↥X) →*
          (↥(GLBConj g X) ⧸ CFSG.pCore 2 ↥(GLBConj g X))) =
      ((GLBConj g K).subgroupOf (GLBConj g X)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(GLBConj g X))) := by
  rw [Subgroup.map_map, ← sec9_map_conjEquiv_subgroupOf, Subgroup.map_map]
  congr 1

theorem sec9_isTwoPrimeComp_gLBConj {G : Type*} [Group G] (g : G) {X J : Subgroup G}
    (h : IsTwoPrimeComp X J) : IsTwoPrimeComp (GLBConj g X) (GLBConj g J) := by
  unfold IsTwoPrimeComp at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨gLBConj_mono g h1, isSubnormal_gLBConj h2 g, ?_, ?_⟩
  · rw [← sec9_gLBConj_commutator, h3]
  · have hc := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (sec9QuotPCore g X) h4
    have htop : (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)).map
        (sec9QuotPCore g X : (↥X ⧸ CFSG.pCore 2 ↥X) →*
          (↥(GLBConj g X) ⧸ CFSG.pCore 2 ↥(GLBConj g X))) = ⊤ :=
      Subgroup.map_top_of_surjective _ (sec9QuotPCore g X).surjective
    rw [htop, sec9_map_quot_pCore] at hc
    exact hc

theorem sec9_isLThreeFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y := by
  obtain ⟨K, hK, hf, hcard, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, hcard, ⟨e.symm.trans f⟩⟩

theorem sec9_isSLThreeFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLThreeFour X) : IsSLThreeFour Y := by
  obtain ⟨K, hK, hf, hcard, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, hcard, ⟨e.symm.trans f⟩⟩

theorem sec9_isHatSeven_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsHatSeven X) : IsHatSeven Y := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

theorem sec9_alphaOf_gLBConj_le {G : Type*} [Group G] (p : ℕ) (g : G) (M : Subgroup G) :
    alphaOf p (GLBConj g M) ≤ GLBConj g (alphaOf p M) := by
  have hsup : ∀ X : Subgroup G, alphaOf p X = pCoreOf 2 X ⊔
      ⨆ (J : Subgroup G) (_ : p = 3 ∧ J ≤ X ∧ IsSubnormal J X ∧ ⁅J, J⁆ = J ∧
        IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)), J := fun X => rfl
  rw [hsup (GLBConj g M)]
  refine sup_le ?_ ?_
  · have hpc : pCoreOf 2 M ≤ alphaOf p M := by
      rw [hsup M]
      exact le_sup_left
    rw [pCoreOf_gLBConj]
    exact gLBConj_mono g hpc
  · refine iSup_le fun J => iSup_le fun hJ => ?_
    obtain ⟨hp3, hJM, hJs, hJc, hJh⟩ := hJ
    have hJ'le : GLBConj g⁻¹ J ≤ alphaOf p M := by
      rw [hsup M]
      refine le_sup_of_le_right (le_iSup_of_le (GLBConj g⁻¹ J)
        (le_iSup_of_le ⟨hp3, ?_, ?_, ?_, ?_⟩ le_rfl))
      · have := gLBConj_mono g⁻¹ hJM
        rwa [gLBConj_inv_gLBConj] at this
      · have := isSubnormal_gLBConj hJs g⁻¹
        rwa [gLBConj_inv_gLBConj] at this
      · rw [← sec9_gLBConj_commutator, hJc]
      · have Φ : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* (↥(GLBConj g⁻¹ J) ⧸ CFSG.pCore 2 ↥(GLBConj g⁻¹ J)) :=
          QuotientGroup.congr _ _ (conjEquiv g⁻¹ J)
            (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g⁻¹ J))
        exact sec9_isHatSeven_of_mulEquiv Φ hJh
    have := gLBConj_mono g hJ'le
    rwa [gLBConj_gLBConj_inv] at this

theorem sec9_alphaOf_gLBConj {G : Type*} [Group G] (p : ℕ) (g : G) (M : Subgroup G) :
    alphaOf p (GLBConj g M) = GLBConj g (alphaOf p M) :=
  gLBConj_eq_of_forall_le (F := alphaOf p) (fun g M => sec9_alphaOf_gLBConj_le p g M) g M

theorem clause_d_of_clause_c_holds : Clause_d_of_clause_cStatement := by
  unfold Clause_d_of_clause_cStatement
  intro G _ _ p A N _hN _hAN _hA hA2 hc
  unfold GLBCore
  refine sSup_le ?_
  rintro _ ⟨Q, hQA, hQ2, rfl⟩
  obtain ⟨D₀, hD₀Q, hD₀⟩ := sec9_exists_isPPlane_le hQ2
  have hD₀A : D₀ ≤ A := hD₀Q.trans hQA
  set T : Subgroup G := ⨅ (D : Subgroup G) (_ : D ≤ Q ∧ IsPPlane p D), gammaStar p D with hT
  have hTmem : ∀ g : G, g ∈ T ↔
      ∀ D : Subgroup G, D ≤ Q → IsPPlane p D → g ∈ gammaStar p D := by
    intro g
    simp only [hT, Subgroup.mem_iInf]
    constructor
    · intro h D h1 h2
      exact h D ⟨h1, h2⟩
    · intro h D hD
      exact h D hD.1 hD.2
  have hcoreT : pCoreOf 2 N ≤ T :=
    le_iInf₂ fun D hD => (hc D (hD.1.trans hQA) hD.2).1
  have hTD₀ : T ≤ gammaStar p D₀ := iInf₂_le D₀ ⟨hD₀Q, hD₀⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ N :=
    (hc D₀ hD₀A hD₀).2 T hcoreT hTD₀
  have key : ∀ x ∈ Subgroup.normalizer (Q : Set G), ∀ g ∈ T, x * g * x⁻¹ ∈ T := by
    intro x hx g hg
    rw [hTmem] at hg ⊢
    intro D hDQ hDP
    have hxQ : GLBConj x D ≤ Q := by
      intro v hv
      rw [mem_gLBConj] at hv
      exact (Subgroup.mem_normalizer_iff.1 hx v).2 (hDQ hv)
    have h1 := hg (GLBConj x D) hxQ (isPPlane_gLBConj x hDP)
    rw [gammaStar_gLBConj, mem_gLBConj] at h1
    exact h1
  have hnorm : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key x hx g, fun hgx => ?_⟩
    have := key x⁻¹ (inv_mem hx) _ hgx
    simpa [mul_assoc] using this
  exact hnorm.trans hNT

theorem isUniquenessTwoLocal_conj_holds : IsUniquenessTwoLocal_conjStatement := by
  unfold IsUniquenessTwoLocal_conjStatement
  intro G _ _ p A N h y hy
  have hyN : GLBConj y N = N := sec9_gLBConj_eq_self h.maxTwoLocal hy
  have hyN' : GLBConj y⁻¹ N = N := sec9_gLBConj_eq_self h.maxTwoLocal (N.inv_mem hy)
  have hα : GLBConj y (alphaOf p N) = alphaOf p N := by
    rw [← sec9_alphaOf_gLBConj, hyN]
  have hP : GLBConj y (pCoreOf 2 N) = pCoreOf 2 N := by
    rw [← pCoreOf_gLBConj, hyN]
  have hP' : GLBConj y⁻¹ (pCoreOf 2 N) = pCoreOf 2 N := by
    rw [← pCoreOf_gLBConj, hyN']
  have hdecomp : ∀ a ∈ GLBConj y A, a ≠ 1 → ∃ a₀ ∈ A, a₀ ≠ 1 ∧ a = y⁻¹ * a₀ * y := by
    intro a ha ha1
    refine ⟨y * a * y⁻¹, mem_gLBConj.1 ha, ?_, by group⟩
    intro h1
    apply ha1
    have e : a = y⁻¹ * (y * a * y⁻¹) * y := by group
    rw [e, h1]
    group
  refine ⟨h.maxTwoLocal, sec9_gLBConj_le_of_mem hy h.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map h.elemAbelian (MulAut.conj y⁻¹).toMonoidHom
  · rw [sec9_pRank_gLBConj]
    exact h.two_le_rank
  · intro a ha ha1
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hdecomp a ha ha1
    rw [centralizer_singleton_gLBConj, glaPPrimeCoreOf_gLBConj, piOf_gLBConj]
    have h1 := h.clause_a a₀ ha₀ ha₀1
    exact sup_le (sec9_gLBConj_le_of_mem hy (le_sup_left.trans h1))
      (sec9_gLBConj_le_of_mem hy (le_sup_right.trans h1))
  · intro a ha ha1
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hdecomp a ha ha1
    have e2 : alphaOf p N ⊓ Subgroup.centralizer ({y⁻¹ * a₀ * y} : Set G) =
        GLBConj y (alphaOf p N ⊓ Subgroup.centralizer ({a₀} : Set G)) := by
      rw [centralizer_singleton_gLBConj, sec9_gLBConj_inf, hα]
    rw [e2, centralizer_singleton_gLBConj, pCoreOf_gLBConj, pCoreOf_gLBConj]
    exact gLBConj_mono y (h.clause_b a₀ ha₀ ha₀1)
  · intro D hDA hDP
    have hD'A : GLBConj y⁻¹ D ≤ A := by
      have := gLBConj_mono y⁻¹ hDA
      rwa [gLBConj_inv_gLBConj] at this
    obtain ⟨hc1, hc2⟩ := h.clause_c (GLBConj y⁻¹ D) hD'A (isPPlane_gLBConj y⁻¹ hDP)
    have hgs : gammaStar p D = GLBConj y (gammaStar p (GLBConj y⁻¹ D)) := by
      have := gammaStar_gLBConj p y (GLBConj y⁻¹ D)
      rwa [gLBConj_gLBConj_inv] at this
    constructor
    · rw [hgs]
      calc pCoreOf 2 N = GLBConj y (pCoreOf 2 N) := hP.symm
        _ ≤ GLBConj y (gammaStar p (GLBConj y⁻¹ D)) := gLBConj_mono y hc1
    · intro T hT1 hT2
      have hT'1 : pCoreOf 2 N ≤ GLBConj y⁻¹ T := by
        calc pCoreOf 2 N = GLBConj y⁻¹ (pCoreOf 2 N) := hP'.symm
          _ ≤ GLBConj y⁻¹ T := gLBConj_mono y⁻¹ hT1
      have hT'2 : GLBConj y⁻¹ T ≤ gammaStar p (GLBConj y⁻¹ D) := by
        have := gLBConj_mono y⁻¹ hT2
        rwa [hgs, gLBConj_inv_gLBConj] at this
      have hN' := hc2 (GLBConj y⁻¹ T) hT'1 hT'2
      have hnorm := normalizer_gLBConj y (GLBConj y⁻¹ T)
      rw [gLBConj_gLBConj_inv] at hnorm
      rw [hnorm]
      exact sec9_gLBConj_le_of_mem hy hN'
  · unfold GLBCore
    refine sSup_le ?_
    rintro _ ⟨Q, hQA, hQ2, rfl⟩
    have hQ'A : GLBConj y⁻¹ Q ≤ A := by
      have := gLBConj_mono y⁻¹ hQA
      rwa [gLBConj_inv_gLBConj] at this
    have hQ'2 : 2 ≤ CFSG.Open.pRank p (GLBConj y⁻¹ Q) := by
      rw [sec9_pRank_gLBConj]
      exact hQ2
    have hle : Subgroup.normalizer ((GLBConj y⁻¹ Q : Subgroup G) : Set G) ≤
        GLBCore p 2 A := by
      unfold GLBCore
      exact le_sSup ⟨GLBConj y⁻¹ Q, hQ'A, hQ'2, rfl⟩
    have hN : GLBCore p 2 A ≤ N := h.clause_d
    have e : Subgroup.normalizer (Q : Set G) =
        GLBConj y (Subgroup.normalizer ((GLBConj y⁻¹ Q : Subgroup G) : Set G)) := by
      have := normalizer_gLBConj y (GLBConj y⁻¹ Q)
      rwa [gLBConj_gLBConj_inv] at this
    rw [e]
    exact sec9_gLBConj_le_of_mem hy (hle.trans hN)
  · intro hp3 a ha ha1 L hL hLt
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hdecomp a ha ha1
    rw [centralizer_singleton_gLBConj] at hL
    have hL' : GLAPComponent 3 (Subgroup.centralizer ({a₀} : Set G)) (GLBConj y⁻¹ L) := by
      have := glaPComponent_gLBConj hL y⁻¹
      rwa [gLBConj_inv_gLBConj] at this
    have hLt' : IsLThreeFour (↥(GLBConj y⁻¹ L) ⧸ GLAPPrimeCore 3 ↥(GLBConj y⁻¹ L)) ∨
        IsSLThreeFour (↥(GLBConj y⁻¹ L) ⧸ GLAPPrimeCore 3 ↥(GLBConj y⁻¹ L)) := by
      rcases hLt with h1 | h1
      · exact Or.inl (sec9_isLThreeFour_of_mulEquiv (conjQuotEquiv 3 y⁻¹ L) h1)
      · exact Or.inr (sec9_isSLThreeFour_of_mulEquiv (conjQuotEquiv 3 y⁻¹ L) h1)
    have hLN := h.clause_e hp3 a₀ ha₀ ha₀1 (GLBConj y⁻¹ L) hL' hLt'
    have e : GLBConj y (GLBConj y⁻¹ L) = L := gLBConj_gLBConj_inv y L
    rw [← e]
    exact sec9_gLBConj_le_of_mem hy hLN
  · intro hp3 a ha ha1 J hJ
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hdecomp a ha ha1
    have e2 : alphaOf p N ⊓ Subgroup.centralizer ({y⁻¹ * a₀ * y} : Set G) =
        GLBConj y (alphaOf p N ⊓ Subgroup.centralizer ({a₀} : Set G)) := by
      rw [centralizer_singleton_gLBConj, sec9_gLBConj_inf, hα]
    rw [e2] at hJ
    rw [centralizer_singleton_gLBConj]
    have hJ' := sec9_isTwoPrimeComp_gLBConj y⁻¹ hJ
    rw [gLBConj_inv_gLBConj] at hJ'
    have hC := h.clause_f hp3 a₀ ha₀ ha₀1 (GLBConj y⁻¹ J) hJ'
    have := sec9_isTwoPrimeComp_gLBConj y hC
    rwa [gLBConj_gLBConj_inv] at this

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

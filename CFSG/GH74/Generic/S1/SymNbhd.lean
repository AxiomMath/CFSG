module

public import CFSG.GH74.Generic.S1.SymSystem
public import CFSG.GH74.Generic.S1.SymMain
public import CFSG.GH74.Generic.S1.SymBlocksLin
public import CFSG.GH74.Generic.S1.SymBlocksUni

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

@[expose] def S1LargeModel {C : Type} [Group C] (K : Subgroup C) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 4 = 3 ∧ 3 < Nat.card F ∧
      Nonempty (↥K ≃* ↥(StatedSL 4 F))) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      Nonempty (↥K ≃* ↥(StatedSU 4 q F)))

@[expose] def S1LiftCentralProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ n ∈ liftL x K, proj x n = 1 → ∀ l ∈ liftL x K, n * l = l * n

@[expose] def S1SchurOddProp : Prop :=
  ∀ (K L : Type) [Group K] [Group L] [Finite L], IsSL4Model K → ∀ a : L →* K,
    Function.Surjective a → Group.IsPerfect L → a.ker ≤ Subgroup.center L →
      (∀ k ∈ a.ker, Odd (orderOf k)) → a.ker = ⊥

@[expose] def S1LiftExactProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → LiftExact x K

@[expose] def S1NormalizerSym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ y ∈ symJ (symX x u) 1, orderOf y = 2 → (∀ a ∈ symJ (symX x u) 1, a * y = y * a) →
          ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ Subgroup.closure {x, y} →
            Subgroup.normalizer (Q : Set G) ≤
              Subgroup.normalizer ((⨆ i, symJ (symX x u) i : Subgroup G) : Set G)

@[expose] def S1NbhdQ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u → ∀ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 3 → Nonempty (↥K ≃* ↥(StatedSL 4 F)) → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem s1LiftExact_of_central_schur (hC : S1LiftCentralProp) (hS : S1SchurOddProp) :
    S1LiftExactProp := by
  intro G _ _ x K hset hfront
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hset.comp.1.1
  have hLperf : Group.IsPerfect ↥(liftL x K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect (K.comap (proj x))
  have hcentral : (piL x K).ker ≤ Subgroup.center ↥(liftL x K) := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have hn1 : proj x (n : ↥(centralizer ({x} : Set G))) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
      exact this
    exact Subtype.ext (hC G x K hset hfront _ n.2 hn1 _ g.2).symm
  have hodd : ∀ k ∈ (piL x K).ker, Odd (orderOf k) := by
    intro k hk
    have hk1 : proj x (k : ↥(centralizer ({x} : Set G))) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      exact this
    have h1 := proj_odd x _ hk1
    rwa [Subgroup.orderOf_coe] at h1
  have hker := hS ↥K ↥(liftL x K) hset.shape.1 (piL x K) (piL_surjective hKperf) hLperf hcentral hodd
  intro l hl hl1
  have hmem : (⟨l, hl⟩ : ↥(liftL x K)) ∈ (piL x K).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hl1
  rw [hker] at hmem
  exact congrArg (fun z : ↥(liftL x K) => ((z : ↥(centralizer ({x} : Set G))))) (Subgroup.mem_bot.1 hmem)

theorem sym_layerData (hExact : S1LiftExactProp) (x : G) (u : Fin 4 → G) {F : Type} [Field F]
    {S : Subgroup (GL (Fin 4) F)}
    (hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G))
    (hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥S, ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j)) :
    ∀ e : Fin 5, ∃ D : LayerData (symX x u e) S,
      D.K = layer (CentralizerBar (symX x u e)) ∧
        ∀ j, ActsAsReflOn D.iso (barOf (hw e j)) (reflDiag F j) := by
  intro e
  obtain ⟨K', hw', hset', hfront', iso, hiso⟩ := hloc e
  have hn : K'.Normal := normal_of_layer_eq hfront'.layer_eq
  exact ⟨⟨K', Subgroup.isPerfect_iff.mp hset'.comp.1.1, hn,
    fun P hP => hfront'.good_le P (Or.inl hP), hExact G _ K' hset' hfront', iso⟩,
    hfront'.layer_eq.symm, hiso⟩

omit [Finite G] in
theorem S1LinkedLin.congr {x : G} {K K' : Subgroup (CentralizerBar x)} (h : K' = K) {F : Type}
    [Field F] [Finite F] {J : Fin 4 → Subgroup G} (hJ : S1LinkedLin x K' F J) :
    S1LinkedLin x K F J := h ▸ hJ

theorem s1Nbhd_lin_of_exact (hExact : S1LiftExactProp) (hNorm : S1NormalizerSym)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (hsym : S1SymFrame x u) {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) (hlin : S1SymFrameLin x u F) (ops : BlockOps F (StatedSL 4 F))
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥(StatedSL 4 F), (linKind F).Pair W (ops.blk a b) (ops.blk b c))
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSL 4 F),
      (linKind F).Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W)
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, ⟨z, hz, hz2, hzc⟩⟩ :=
    symSystem ops (symX x u) D hw hDact (linKind F) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  have eK : ↥K ≃* ↥(StatedSL 4 F) := by
    have h : (D 4).K = K := hK
    subst h
    exact (D 4).iso
  have hbigK : S1LargeModel K := Or.inl ⟨F, inferInstance, inferInstance, hF, h4, ⟨eK⟩⟩
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hlink : S1LinkedLin x (D 4).K F (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  exact ⟨symJ (symX x u), Or.inl ⟨p, f, F, inferInstance, inferInstance, hpp, hcard,
    by rw [← hcard]; omega, ⟨hcomm, hpair⟩, hlink.congr hK⟩,
    ⟨z, hz, hz2, hzc, fun Q hQ hQle =>
      hNorm G x K hset hfront hbigK u hu hf hsym z hz hz2 hzc Q hQ hQle⟩⟩

omit [Finite G] in
theorem S1LinkedUni.congr {x : G} {K K' : Subgroup (CentralizerBar x)} (h : K' = K) {F : Type}
    [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {J : Fin 4 → Subgroup G}
    (hJ : S1LinkedUni x K' F p f J) : S1LinkedUni x K F p f J := h ▸ hJ

theorem s1Nbhd_uni_of_exact (hExact : S1LiftExactProp) (hNorm : S1NormalizerSym)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (hsym : S1SymFrame x u) {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (huni : S1SymFrameUni x u q F) (ops : BlockOps F (StatedSU 4 q F))
    (p f : ℕ) [Fact p.Prime] [CharP F p] (hqpf : q = p ^ f)
    (hstd : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥(StatedSU 4 q F), (uniKind F p f).Pair W (ops.blk a b) (ops.blk b c))
    (hchain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSU 4 q F),
      (uniKind F p f).Chain (fun i : Fin 3 => ops.blk i.castSucc i.succ) W)
    (hcen : ∃ z ∈ ops.blk 0 1, orderOf z = 2 ∧ ∀ g ∈ ops.blk 0 1, g * z = z * g) :
    ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSU 4 q F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, ⟨z, hz, hz2, hzc⟩⟩ :=
    symSystem ops (symX x u) D hw hDact (uniKind F p f) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  have eK : ↥K ≃* ↥(StatedSU 4 q F) := by
    have h : (D 4).K = K := hK
    subst h
    exact (D 4).iso
  have hbigK : S1LargeModel K := Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq, ⟨eK⟩⟩
  have hlink : S1LinkedUni x (D 4).K F p f (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hq5 : 5 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    have hq1 : 1 < q := by
      by_contra hle
      have hle' : q ≤ 1 := by omega
      interval_cases q <;> simp at h1
    rw [← hqpf]
    omega
  exact ⟨symJ (symX x u), Or.inr ⟨p, f, F, inferInstance, inferInstance, inferInstance, inferInstance,
    by rw [← hqpf]; exact hF, hq5, ⟨hcomm, hpair⟩, hlink.congr hK⟩,
    ⟨z, hz, hz2, hzc, fun Q hQ hQle =>
      hNorm G x K hset hfront hbigK u hu hf hsym z hz hz2 hzc Q hQ hQle⟩⟩

omit [Finite G] in
theorem sym_model_four {x : G} {K : Subgroup (CentralizerBar x)} [Finite G] (hfront : S1Front G x K)
    {u : Fin 4 → G} {F : Type} [Field F] (hlin : S1SymFrameLin x u F) :
    Nonempty (↥K ≃* ↥(StatedSL 4 F)) := by
  obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin 4
  have h : K' = K := hfront'.layer_eq.symm.trans hfront.layer_eq
  subst h
  exact ⟨e'⟩

theorem s1NbhdSym_of_props (hExact : S1LiftExactProp) (hNorm : S1NormalizerSym) (hQ3 : S1NbhdQ3) :
    S1NbhdSym := by
  intro G _ _ x K hset hfront u hu hf hsym
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · by_cases h3 : Nat.card F = 3
    · exact hQ3 G x K hset hfront u hu hf hsym F inferInstance inferInstance h3
        (sym_model_four hfront hlin)
    · have h4 : 3 < Nat.card F := by
        have hpos : 0 < Nat.card F := Nat.card_pos
        omega
      exact s1Nbhd_lin_of_exact hExact hNorm hset hfront hf hsym hF h4 hlin (linBlockOps hF h4)
        (fun a b c hab hac hbc => lin_std hF h4 a b c hab hac hbc) (lin_chain hF h4)
        (lin_blk_center hF h4)
  · obtain ⟨p, f, hud, hqpf, -⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    exact s1Nbhd_uni_of_exact hExact hNorm hset hfront hf hsym hF hq huni (uniBlockOps hF hq) p f
      hqpf (fun a b c hab hac hbc => uni_std hF hq hqpf a b c hab hac hbc) (uni_chain hF hq hqpf)
      (uni_blk_center hF hq)

end CFSG.GH74.Generic.S1

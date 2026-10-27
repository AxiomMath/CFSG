module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Elem

variable {G : Type*} [Group G]

theorem isPGroup_three_of_isElemAbelian_three {E : Subgroup G} (h : IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup h

theorem isElemAbelian_three_closure_of_pairwise {S : Set G} (hS : S.Pairwise Commute)
    (h3 : ∀ s ∈ S, s ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure S) :=
  ⟨Subgroup.isMulCommutative_closure hS, fun _ hx =>
    CFSG.AGLEmbedding.ParabHub.pow_eq_one_of_mem_closure hS h3 hx⟩

theorem isElemAbelian_of_conj {E U : Subgroup G} (h : IsElemAbelian 3 E) (g : G)
    (hU : ∀ u ∈ U, g⁻¹ * u * g ∈ E) : IsElemAbelian 3 U := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hc := h.1.is_comm.comm ⟨_, hU a a.2⟩ ⟨_, hU b b.2⟩
    have hc' : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := by
      simpa using congrArg Subtype.val hc
    have e1 : ((a * b : U) : G) = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    have e2 : ((b * a : U) : G) = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e1, e2, hc']
  · have h1 := h.2 _ (hU x hx)
    have e : (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e] at h1
    calc x ^ 3 = g * (g⁻¹ * x ^ 3 * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem isElemAbelian_of_le_of_card_dvd [Finite G] {J E : Subgroup G} (hEJ : E ≤ J)
    (hE : IsElemAbelian 3 E) {a : ℕ} (hdvd : Nat.card J ∣ 2 ^ a * Nat.card E) :
    ∀ U : Subgroup G, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hUJ hU
  set E' : Subgroup J := E.subgroupOf J with hE'
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  have hE3 : IsPGroup 3 E := isPGroup_three_of_isElemAbelian_three hE
  obtain ⟨b, hb⟩ := hE3.exists_card_eq
  have hJpos : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hEJdvd : Nat.card E ∣ Nat.card J := hcardE' ▸ Subgroup.card_subgroup_dvd_card E'
  have hfac : Nat.card E' = 3 ^ (Nat.card J).factorization 3 := by
    rw [hcardE', hb]
    congr 1
    apply le_antisymm
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJpos, ← hb]
      exact hEJdvd
    · have h1 : 3 ^ (Nat.card J).factorization 3 ∣ 2 ^ a * 3 ^ b :=
        (Nat.ordProj_dvd _ _).trans (hb ▸ hdvd)
      have h2 : Nat.Coprime (3 ^ (Nat.card J).factorization 3) (2 ^ a) :=
        Nat.Coprime.pow _ _ (by norm_num)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (h2.dvd_of_dvd_mul_left h1)
  let P : Sylow 3 J := Sylow.ofCard E' hfac
  have hU' : IsPGroup 3 (U.subgroupOf J) :=
    hU.of_injective (Subgroup.subgroupOfEquivOfLe hUJ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUJ).injective
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P Q
  refine isElemAbelian_of_conj hE (g : G) fun u hu => ?_
  have hmem : (⟨u, hUJ hu⟩ : J) ∈ (Q : Subgroup J) := hQ hu
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have h2 : ((MulAut.conj g)⁻¹ • (⟨u, hUJ hu⟩ : J) : J) = g⁻¹ * ⟨u, hUJ hu⟩ * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  have h3 : ((P : Sylow 3 J) : Subgroup J) = E' := rfl
  rw [h2, h3, hE', Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

end Elem

section Two

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_of_card_two {X : Subgroup G} (hX : Nat.card X = 2) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) (ha1 : a ≠ 1) : b = 1 ∨ b = a := by
  classical
  by_contra hne
  push Not at hne
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite X
  have h3 : ({⟨1, X.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hne.2 (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hne.1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_univ ({⟨1, X.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩} : Finset X)
  rw [h3, ← Nat.card_eq_fintype_card, hX] at this
  omega

theorem conj_eq_self_of_card_two {X : Subgroup G} (hX : Nat.card X = 2) {g : G}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {x : G} (hx : x ∈ X) : g * x * g⁻¹ = x := by
  by_cases hx1 : x = 1
  · rw [hx1]
    group
  · rcases eq_one_or_eq_of_mem_of_card_two hX hx (hg x hx) hx1 with h | h
    · exfalso
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h

theorem eq_one_of_sq_eq_one_of_cube_eq_one {z : G} (h2 : z ^ 2 = 1) (h3 : z ^ 3 = 1) : z = 1 :=
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3]; group

theorem mem_normalizer_closure_of_forall_conj_mem [Finite G] {S : Set G} {g : G}
    (hg : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hle : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hg s hs
  exact Subgroup.mem_normalizer_fintype fun z hz => hle ⟨z, hz, rfl⟩

end Two

section Clauses

variable {W : Type*} [Group W]

@[expose] def ThreeSylowClauses (J : Subgroup W) : Prop :=
  (∀ Q : Sylow 3 J, IsCyclic (Q : Subgroup J) → Nat.card Q ≤ 3) ∧
    (∀ u ∈ J, ∀ v ∈ J, orderOf u = 9 → orderOf v = 9 → Commute u v →
      Subgroup.zpowers u ⊓ Subgroup.zpowers v ≠ ⊥) ∧
    (∀ N B : Subgroup W, N ≤ B → B ≤ J → J ≤ Subgroup.normalizer (N : Set W) →
      J ≤ Subgroup.normalizer (B : Set W) → Nat.Coprime 3 (Nat.card N) →
      (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N) → (∀ j ∈ J, ∃ e : ℕ, j ^ 2 ^ e ∈ B) →
      ∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧
    (IsMulCommutative ↥(CFSG.pCore 3 (↥J ⧸ primeComplementCore (G := ↥J) 3)) →
      ∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U)

@[expose] def HasThreePair (J : Subgroup W) : Prop :=
  ∃ N B : Subgroup W, N ≤ B ∧ B ≤ J ∧ J ≤ Subgroup.normalizer (N : Set W) ∧
    J ≤ Subgroup.normalizer (B : Set W) ∧ Nat.Coprime 3 (Nat.card N) ∧
    (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N) ∧ ∀ j ∈ J, ∃ e : ℕ, j ^ 2 ^ e ∈ B

@[expose] def IsThreeExceptional (J : Subgroup W) : Prop :=
  (∀ u ∈ J, ∀ v ∈ J, orderOf u = 9 → orderOf v = 9 → Commute u v →
      Subgroup.zpowers u ⊓ Subgroup.zpowers v ≠ ⊥) ∧ ¬ HasThreePair J ∧
    ∃ R V N : Subgroup W, R ≤ N ∧ V ≤ N ∧ N ≤ J ∧ J ≤ Subgroup.normalizer (V : Set W) ∧
      J ≤ Subgroup.normalizer (N : Set W) ∧ Nat.Coprime 3 (Nat.card V) ∧
      (∀ x ∈ N, ∃ e : ℕ, x ^ 3 ^ e ∈ V) ∧ IsPGroup 3 R ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a

@[expose] def ThreeDichotomy (J : Subgroup W) : Prop :=
  (∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U) ∨ IsThreeExceptional J

end Clauses

section Dichotomy

variable {W : Type*} [Group W] [Finite W]

omit [Finite W] in
theorem eq_one_of_mem_of_coprime_three {V : Subgroup W} (hV : Nat.Coprime 3 (Nat.card V))
    {x : W} (hx : x ∈ V) {e : ℕ} (he : x ^ 3 ^ e = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left e hV)
    (orderOf_dvd_of_pow_eq_one he) (Subgroup.orderOf_dvd_natCard V hx))

theorem ThreeDichotomy.clauses {J : Subgroup W} (h : ThreeDichotomy J) : ThreeSylowClauses J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with hE | ⟨hnine, hpair, R, V, N, hRN, hVN, hNJ, hJV, hJN, hV3, hNV, hR3, a, ha, b, hb,
    hab⟩
  · refine ⟨fun Q hQ => ?_, fun u hu v hv hu9 hv9 _ => ?_,
      fun _ _ _ _ _ _ _ _ _ U hUJ hU => ?_, fun _ => hE⟩
    · have hU := hE ((Q : Subgroup J).map J.subtype) (Subgroup.map_subtype_le _)
        (Q.isPGroup'.map _)
      obtain ⟨g, hg⟩ := hQ.exists_generator
      have h3 : g ^ 3 = 1 := by
        have := hU.2 ((g : J) : W) ⟨g, g.2, rfl⟩
        exact Subtype.ext (Subtype.ext (by simpa using this))
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
    · exfalso
      have hz : IsPGroup 3 (Subgroup.zpowers u) :=
        IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu9]; norm_num)
      have h3 := (hE _ ((Subgroup.zpowers_le).2 hu) hz).2 u (Subgroup.mem_zpowers u)
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hu9] at this
      norm_num at this
    · intro x hx y hy
      exact congrArg Subtype.val ((hE U hUJ hU).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · refine ⟨fun Q hQ => ?_, hnine, fun N' B' h1 h2 h3 h4 h5 h6 h7 => ?_, fun hcomm => ?_⟩
    · exfalso
      have hR' : IsPGroup 3 (R.subgroupOf J) :=
        hR3.of_injective (Subgroup.subgroupOfEquivOfLe (hRN.trans hNJ)).toMonoidHom
          (Subgroup.subgroupOfEquivOfLe (hRN.trans hNJ)).injective
      obtain ⟨P, hP⟩ := hR'.exists_le_sylow
      have : IsCyclic (P : Subgroup J) :=
        isCyclic_of_surjective (Sylow.equiv Q P).toMonoidHom (Sylow.equiv Q P).surjective
      have hc := (IsCyclic.commGroup (α := (P : Subgroup J))).mul_comm
        ⟨⟨a, hNJ (hRN ha)⟩, hP ha⟩ ⟨⟨b, hNJ (hRN hb)⟩, hP hb⟩
      exact hab (congrArg (fun z : (P : Subgroup J) => ((z : J) : W)) hc)
    · exact (hpair ⟨N', B', h1, h2, h3, h4, h5, h6, h7⟩).elim
    · exfalso
      set O : Subgroup J := primeComplementCore (G := J) 3 with hO
      set q : J →* J ⧸ O := QuotientGroup.mk' O with hq
      have hqs : Function.Surjective q := QuotientGroup.mk'_surjective O
      have hVO : V.subgroupOf J ≤ O :=
        normal_coprime_le_primeComplementCore 3 _ (Subgroup.normal_subgroupOf_of_le_normalizer hJV)
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hVN.trans hNJ)).toEquiv])
      have hK : (N.subgroupOf J).map q ≤ CFSG.pCore 3 (J ⧸ O) := by
        refine le_sSup ⟨(Subgroup.normal_subgroupOf_of_le_normalizer hJN).map q hqs, ?_⟩
        rintro ⟨_, x, hx, rfl⟩
        obtain ⟨e, he⟩ := hNV x hx
        refine ⟨e, Subtype.ext ?_⟩
        change q x ^ 3 ^ e = 1
        rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hVO he
      set a' : J := ⟨a, hNJ (hRN ha)⟩
      set b' : J := ⟨b, hNJ (hRN hb)⟩
      have hqa : q a' ∈ CFSG.pCore 3 (J ⧸ O) := hK ⟨a', hRN ha, rfl⟩
      have hqb : q b' ∈ CFSG.pCore 3 (J ⧸ O) := hK ⟨b', hRN hb, rfl⟩
      have hc := hcomm.is_comm.comm ⟨q a', hqa⟩ ⟨q b', hqb⟩
      have hc' : q (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
        group
      have hmemO : a' * b' * a'⁻¹ * b'⁻¹ ∈ O := by
        rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
      have hmemR : a * b * a⁻¹ * b⁻¹ ∈ R :=
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      obtain ⟨e, he⟩ := hR3 ⟨_, hmemR⟩
      have he' : (a' * b' * a'⁻¹ * b'⁻¹) ^ 3 ^ e = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val he)
      have h1 := eq_one_of_mem_of_coprime_three (primeComplementCore_coprime 3) hmemO he'
      apply hab
      have h2 : a * b * a⁻¹ * b⁻¹ = 1 := by simpa using congrArg Subtype.val h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h2, one_mul]

end Dichotomy

end CFSG.AGLEmbedding

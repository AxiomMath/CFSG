module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Characteristic

variable {Y : Type*} [Group Y]

private theorem mem_normalizer_map_subtype_of_char [Finite Y] {P : Subgroup Y} {C : Subgroup P}
    (hC : C.Characteristic) {g : Y} (hg : g ∈ Subgroup.normalizer (P : Set Y)) :
    g ∈ Subgroup.normalizer ((C.map P.subtype : Subgroup Y) : Set Y) := by
  refine mem_normalizer_of_conj_map_le ?_
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  set φ : MulAut P := P.normalizerMonoidHom ⟨g, hg⟩
  have hφ : φ c ∈ C := by
    have h1 : c ∈ C.comap φ.toMonoidHom := by rw [hC.fixed φ]; exact hc
    exact h1
  exact ⟨φ c, hφ, rfl⟩

theorem characteristic_comap_mk_of_characteristic {P : Type*} [Group P] (O : Subgroup P)
    [O.Normal] (hO : O.Characteristic) (D : Subgroup (P ⧸ O)) (hD : D.Characteristic) :
    (D.comap (QuotientGroup.mk' O)).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  have hOφ : O.map φ.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp hO φ
  set ψ := QuotientGroup.congr O O φ hOφ with hψ
  have hDψ : D.map ψ.toMonoidHom = D := Subgroup.characteristic_iff_map_eq.mp hD ψ
  rintro _ ⟨x, hx, rfl⟩
  change QuotientGroup.mk' O (φ x) ∈ D
  rw [← QuotientGroup.congr_mk' O O φ hOφ, ← hDψ]
  exact Subgroup.mem_map_of_mem _ hx

end Characteristic

section Orders

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_barM_dvd {M X : Subgroup G} (hXM : X ≤ M) : Nat.card (barM M X) ∣ Nat.card X := by
  rw [barM, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
  exact Subgroup.card_map_dvd _ _

theorem coprime_three_card_of_barM {M W : Subgroup G} (hWM : W ≤ M)
    (hW : Nat.Coprime 3 (Nat.card (barM M W))) : Nat.Coprime 3 (Nat.card W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at hW ⊢
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hwo : orderOf (w : G) = 3 := by rw [Subgroup.orderOf_coe, hw]
  have hZ : Subgroup.zpowers (w : G) ≤ W := (Subgroup.zpowers_le).mpr w.2
  have h3 : IsPGroup 3 (Subgroup.zpowers (w : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo, pow_one])
  obtain ⟨e⟩ := nonempty_mulEquiv_barM (hZ.trans hWM) h3
  apply hW
  have hc : Nat.card (barM M (Subgroup.zpowers (w : G))) = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zpowers, hwo]
  rw [← hc]
  exact Subgroup.card_dvd_of_le (barM_mono hZ)

omit [Finite G] in
private theorem commutator_mem_of_mem_sup {X N : Subgroup G} (hX : IsMulCommutative X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) {a b : G} (ha : a ∈ X ⊔ N) (hb : b ∈ X ⊔ N) :
    a * b * a⁻¹ * b⁻¹ ∈ N := by
  have ha' : a ∈ ((X ⊔ N : Subgroup G) : Set G) := ha
  have hb' : b ∈ ((X ⊔ N : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X N hXN] at ha' hb'
  obtain ⟨x₁, hx₁, n₁, hn₁, rfl⟩ := ha'
  obtain ⟨x₂, hx₂, n₂, hn₂, rfl⟩ := hb'
  have hc : x₁ * x₂ = x₂ * x₁ :=
    congrArg Subtype.val ((isMulCommutative_iff.mp hX) ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩)
  have hconj : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (hXN hx) n).mp hn
  have hconj' : ∀ x ∈ X, ∀ n ∈ N, x⁻¹ * n * x ∈ N := fun x hx n hn => by
    simpa using hconj x⁻¹ (X.inv_mem hx) n hn
  have key : x₁ * n₁ * (x₂ * n₂) * (x₁ * n₁)⁻¹ * (x₂ * n₂)⁻¹ =
      x₂ * (x₁ * ((x₂⁻¹ * n₁ * x₂) * n₂ * n₁⁻¹) * x₁⁻¹ * n₂⁻¹) * x₂⁻¹ := by
    calc x₁ * n₁ * (x₂ * n₂) * (x₁ * n₁)⁻¹ * (x₂ * n₂)⁻¹
        = (x₁ * x₂) * ((x₂⁻¹ * n₁ * x₂) * n₂ * n₁⁻¹) * x₁⁻¹ * n₂⁻¹ * x₂⁻¹ := by group
      _ = (x₂ * x₁) * ((x₂⁻¹ * n₁ * x₂) * n₂ * n₁⁻¹) * x₁⁻¹ * n₂⁻¹ * x₂⁻¹ := by rw [hc]
      _ = x₂ * (x₁ * ((x₂⁻¹ * n₁ * x₂) * n₂ * n₁⁻¹) * x₁⁻¹ * n₂⁻¹) * x₂⁻¹ := by group
  rw [key]
  refine hconj x₂ hx₂ _ (N.mul_mem (hconj x₁ hx₁ _ ?_) (N.inv_mem hn₂))
  exact N.mul_mem (N.mul_mem (hconj' x₂ hx₂ n₁ hn₁) hn₂) (N.inv_mem hn₁)

end Orders

section A9MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}

theorem D1A9DataCore.isMulCommutative_pCore_blockPL (h : D1A9DataCore P M H R X σ z)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hKL : H ⊓ M ≤ Subgroup.normalizer (L : Set G)) :
    IsMulCommutative ↥(CFSG.pCore 3 (↥(blockPL M (pCoreOf 2 H) L) ⧸
      primeComplementCore (G := ↥(blockPL M (pCoreOf 2 H) L)) 3)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  set S := pCoreOf 2 H with hS
  set N := GLBPrimeCore 3 H with hN
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set J : Subgroup G := Subgroup.normalizer (S : Set G) ⊓ L with hJ
  set PL := blockPL M S L with hPL
  set O := primeComplementCore (G := ↥PL) 3 with hO
  set Q := CFSG.pCore 3 (↥PL ⧸ O) with hQ
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hJM : J ≤ M := inf_le_right.trans hL.le
  have hJK : J ≤ H ⊓ M := fun x hx => hKeq ▸ ⟨hJM hx, hx.1⟩
  have hPLn : ∀ k (hk : k ∈ H ⊓ M), mk ⟨k, hk.2⟩ ∈ Subgroup.normalizer (PL : Set _) := by
    intro k hk
    have hkJ : k ∈ Subgroup.normalizer (J : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hKeq ▸ hk).2, hKL hk⟩
    exact Subgroup.le_normalizer_map _
      (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap M.subtype hkJ))
  have hOc : O.Characteristic := primeComplementCore_characteristic 3
  have hQc : (Q.comap (QuotientGroup.mk' O)).Characteristic :=
    characteristic_comap_mk_of_characteristic O hOc Q inferInstance
  set Ob : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := O.map PL.subtype with hOb
  set Qb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := (Q.comap (QuotientGroup.mk' O)).map PL.subtype
    with hQb
  set Oh : Subgroup G := H ⊓ M ⊓ (Ob.comap mk).map M.subtype with hOh
  set Qh : Subgroup G := H ⊓ M ⊓ (Qb.comap mk).map M.subtype with hQh
  have hpre : ∀ (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (k : G) (hk : k ∈ H ⊓ M),
      mk ⟨k, hk.2⟩ ∈ Subgroup.normalizer (T : Set _) →
      k ∈ Subgroup.normalizer ((H ⊓ M ⊓ (T.comap mk).map M.subtype : Subgroup G) : Set G) :=
    fun T k hk hkT => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk,
      Subgroup.le_normalizer_map M.subtype (Subgroup.mem_map_of_mem _
        (Subgroup.le_normalizer_comap mk hkT))⟩
  have hOn : H ⊓ M ≤ Subgroup.normalizer (Oh : Set G) := fun k hk =>
    hpre Ob k hk (mem_normalizer_map_subtype_of_char hOc (hPLn k hk))
  have hQn : H ⊓ M ≤ Subgroup.normalizer (Qh : Set G) := fun k hk =>
    hpre Qb k hk (mem_normalizer_map_subtype_of_char hQc (hPLn k hk))
  have hOcop : Nat.Coprime 3 (Nat.card Oh) := by
    refine coprime_three_card_of_barM (inf_le_left.trans inf_le_right) ?_
    refine Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (barM_le_of_le_preimage inf_le_right)) ?_
    rw [hOb, Subgroup.card_map_of_injective PL.subtype_injective]
    exact primeComplementCore_coprime 3
  have hON : Oh ≤ N := by
    rcases h.surv.normal_dichotomy Oh inf_le_left hOn with hle | hXO
    · exact hle
    · exfalso
      have hXc : Nat.Coprime 3 (Nat.card X) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXO) hOcop
      rw [h.card_X] at hXc
      exact absurd hXc (by decide)
  have hQ3 : ∀ y ∈ Qh, ∃ e : ℕ, y ^ 3 ^ e ∈ N := by
    rintro _ ⟨hyK, m, ⟨p, hp, hpm⟩, rfl⟩
    obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥PL ⧸ O)) ⟨_, hp⟩
    have hpO : p ^ 3 ^ e ∈ O := by
      have h1 : (QuotientGroup.mk' O p) ^ 3 ^ e = 1 := congrArg Subtype.val he
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    refine ⟨e, hON ⟨(H ⊓ M).pow_mem hyK _, m ^ 3 ^ e, ⟨p ^ 3 ^ e, hpO, ?_⟩, ?_⟩⟩
    · change ((p ^ 3 ^ e : ↥PL) : ↥M ⧸ CFSG.pCore 2 ↥M) = mk (m ^ 3 ^ e)
      rw [map_pow, Subgroup.coe_pow]
      exact congrArg (· ^ 3 ^ e) hpm
    · simp
  have hQX : Qh ≤ X ⊔ N := h.pcore_le Qh inf_le_left hQn hQ3
  have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
    (h.surv.le_R.trans h3.le_H).trans (le_normalizer_glbPrimeCore 3 H)
  have hNJ : barM M (N ⊓ J) ≤ PL := barM_mono inf_le_right
  have hNbO : (barM M (N ⊓ J)).subgroupOf PL ≤ O := by
    refine normal_coprime_le_primeComplementCore 3 _ ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNJ]
      rintro _ ⟨m, hm, rfl⟩
      have hmJ : (m : G) ∈ J := Subgroup.mem_subgroupOf.mp hm
      have hmN : (m : G) ∈ Subgroup.normalizer ((N ⊓ J : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_glbPrimeCore 3 H (hJK hmJ).1, Subgroup.le_normalizer hmJ⟩
      exact Subgroup.le_normalizer_map _
        (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap M.subtype hmN))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv]
      exact Nat.Coprime.coprime_dvd_right ((card_barM_dvd (inf_le_right.trans hJM)).trans
        (Subgroup.card_dvd_of_le inf_le_left)) (glbPrimeCore_coprime 3 H)
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  obtain ⟨pa, hpa⟩ := QuotientGroup.mk'_surjective O (a : ↥PL ⧸ O)
  obtain ⟨pb, hpb⟩ := QuotientGroup.mk'_surjective O (b : ↥PL ⧸ O)
  obtain ⟨ma, hma, hmpa⟩ := pa.2
  obtain ⟨mb, hmb, hmpb⟩ := pb.2
  have hya : (ma : G) ∈ Qh := ⟨hJK (Subgroup.mem_subgroupOf.mp hma), ma,
    ⟨pa, show QuotientGroup.mk' O pa ∈ Q from hpa ▸ a.2, hmpa.symm⟩, rfl⟩
  have hyb : (mb : G) ∈ Qh := ⟨hJK (Subgroup.mem_subgroupOf.mp hmb), mb,
    ⟨pb, show QuotientGroup.mk' O pb ∈ Q from hpb ▸ b.2, hmpb.symm⟩, rfl⟩
  have hc := commutator_mem_of_mem_sup h.elem.1 hXN (hQX hya) (hQX hyb)
  have hcJ : ((ma * mb * ma⁻¹ * mb⁻¹ : M) : G) ∈ N ⊓ J := by
    refine ⟨by simpa using hc, ?_⟩
    have ha' := Subgroup.mem_subgroupOf.mp hma
    have hb' := Subgroup.mem_subgroupOf.mp hmb
    simpa using J.mul_mem (J.mul_mem (J.mul_mem ha' hb') (J.inv_mem ha')) (J.inv_mem hb')
  have hcO : pa * pb * pa⁻¹ * pb⁻¹ ∈ O := by
    refine hNbO (Subgroup.mem_subgroupOf.mpr ⟨ma * mb * ma⁻¹ * mb⁻¹,
      Subgroup.mem_subgroupOf.mpr hcJ, ?_⟩)
    simp only [map_mul, map_inv, hmpa, hmpb, Subgroup.coe_mul, Subgroup.coe_inv]
  have h1 : QuotientGroup.mk' O (pa * pb * pa⁻¹ * pb⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcO
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpa, hpb] at h1
  calc (a : ↥PL ⧸ O) * b = ((a : ↥PL ⧸ O) * b * (a : ↥PL ⧸ O)⁻¹ * (b : ↥PL ⧸ O)⁻¹) *
        ((b : ↥PL ⧸ O) * a) := by group
    _ = b * a := by rw [h1, one_mul]

end A9MSide

end CFSG.AGLEmbedding

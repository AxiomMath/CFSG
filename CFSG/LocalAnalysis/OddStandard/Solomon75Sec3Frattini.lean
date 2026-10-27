module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Equiv
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Frattini

theorem mem_smul_sylow_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) (g x : G) :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : g⁻¹ * (MulAut.conj g • a) * g = a := by
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [h1]
    exact ha
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

variable {X : Type} [Group X] [Finite X]

theorem exists_mul_mem_normalizer_of_isSylowTwoIn {A C Z : Subgroup X} (hAC : A ≤ C)
    (hAn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hZ : IsSylowTwoIn A Z) {c : X} (hc : c ∈ C) :
    ∃ a ∈ A, ∃ m ∈ normalizer (Z : Set X) ⊓ C, c = a * m := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZA, hZp, hZidx⟩ := hZ
  let φc : X ≃* X := MulAut.conj c
  let Zc : Subgroup X := Z.map φc.toMonoidHom
  have hZcA : Zc ≤ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact hAn c hc z (hZA hz)
  have hZc_p : IsPGroup 2 ↥Zc := hZp.of_equiv (Subgroup.equivMapOfInjective Z _ φc.injective)
  have hcard : Nat.card (Zc.subgroupOf A) = Nat.card (Z.subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZcA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv,
      Nat.card_congr (Subgroup.equivMapOfInjective Z _ φc.injective).toEquiv.symm]
  have hidx : (Zc.subgroupOf A).index = (Z.subgroupOf A).index := by
    have h1 := Subgroup.index_mul_card (Zc.subgroupOf A)
    have h2 := Subgroup.index_mul_card (Z.subgroupOf A)
    rw [hcard] at h1
    have hpos : 0 < Nat.card (Z.subgroupOf A) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  let P : Sylow 2 ↥A := IsPGroup.toSylow (P := Z.subgroupOf A)
    (hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZA).symm) hZidx
  let Q : Sylow 2 ↥A := IsPGroup.toSylow (P := Zc.subgroupOf A)
    (hZc_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZcA).symm) (by
      show ¬ 2 ∣ (Zc.subgroupOf A).index
      rw [hidx]
      exact hZidx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥A) P Q
  have hle : Z.map (MulAut.conj ((g : X)⁻¹ * c)).toMonoidHom ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    have hy : c * z * c⁻¹ ∈ A := hZcA ⟨z, hz, by simp [φc, MulAut.conj_apply]⟩
    have hmem : (⟨c * z * c⁻¹, hy⟩ : ↥A) ∈ ((g • P : Sylow 2 ↥A) : Subgroup ↥A) := by
      rw [hg]
      exact ⟨z, hz, by simp [φc, MulAut.conj_apply]⟩
    rw [mem_smul_sylow_iff] at hmem
    have h2 : (g : X)⁻¹ * (c * z * c⁻¹) * g ∈ Z := hmem
    have h3 : (MulAut.conj ((g : X)⁻¹ * c)).toMonoidHom z = (g : X)⁻¹ * (c * z * c⁻¹) * g := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [h3]
    exact h2
  have hcardZ : Nat.card (Z.map (MulAut.conj ((g : X)⁻¹ * c)).toMonoidHom) = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj ((g : X)⁻¹ * c)).injective
  have heq : Z.map (MulAut.conj ((g : X)⁻¹ * c)).toMonoidHom = Z :=
    Subgroup.eq_of_le_of_card_ge hle hcardZ.ge
  have hn : (g : X)⁻¹ * c ∈ normalizer (Z : Set X) := mem_normalizer_of_map_conj_eq heq
  have hmC : (g : X)⁻¹ * c ∈ C := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC g.2)) hc
  exact ⟨(g : X), g.2, (g : X)⁻¹ * c, ⟨hn, hmC⟩, by group⟩

end Frattini

section ZStar

theorem exists_pow_two_pow_mem_pPrimeCore {Q : Type} [Group Q] [Finite Q] {a : Q}
    (ha : ∀ q : Q, ⁅q, a⁆ ∈ pPrimeCore 2 Q) : ∃ k : ℕ, a ^ (2 ^ k) ∈ pPrimeCore 2 Q := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup Q := pPrimeCore 2 Q
  let ā : Q ⧸ N := (a : Q ⧸ N)
  have hc : ∀ x : Q ⧸ N, x * ā = ā * x := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : (QuotientGroup.mk' N) ⁅q, a⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (ha q)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf ā) (orderOf_pos ā).ne'
  refine ⟨k, ?_⟩
  set y : Q ⧸ N := ā ^ (2 ^ k) with hy
  have hyord : orderOf y = o := by
    rw [hy, orderOf_pow_of_dvd (by positivity) ⟨o, hko⟩, hko]
    exact Nat.mul_div_cancel_left o (by positivity)
  have hyc : ∀ x : Q ⧸ N, x * y = y * x := fun x => (Commute.pow_right (hc x) (2 ^ k))
  have hnorm : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : Commute g (y ^ m) := (Commute.zpow_right (hyc g) m)
    rw [this.eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hyord]
    exact Nat.coprime_two_left.2 ho
  have hle : Subgroup.zpowers y ≤ pPrimeCore 2 (Q ⧸ N) := le_sSup ⟨hnorm, hcop⟩
  have hbot : pPrimeCore 2 (Q ⧸ N) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hy1 : y = 1 := by
    have := hle (Subgroup.mem_zpowers y)
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact hy1

variable {X : Type} [Group X] [Finite X]

theorem exists_relIndex_zStar_eq_two_pow (K : Subgroup X) :
    ∃ e : ℕ, (pPrimeCoreOf 2 K).relIndex (zStar K) = 2 ^ e := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK : zStar K ≤ K := inf_le_left
  let f : ↥(zStar K) →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hAK)
  have hmemP : ∀ x : ↥K, (x : X) ∈ pPrimeCoreOf 2 K ↔ x ∈ pPrimeCore 2 ↥K := by
    intro x
    constructor
    · rintro ⟨w, hw, hwx⟩
      have : w = x := Subtype.ext hwx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hker : f.ker = (pPrimeCoreOf 2 K).subgroupOf (zStar K) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion hAK a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (hmemP (Subgroup.inclusion hAK a)).symm
  have hidx : (pPrimeCoreOf 2 K).relIndex (zStar K) = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker]
    exact Subgroup.index_ker f
  have hp : IsPGroup 2 ↥f.range := by
    rintro ⟨_, a, rfl⟩
    have ha : ∀ q : ↥K, ⁅q, Subgroup.inclusion hAK a⁆ ∈ pPrimeCore 2 ↥K := by
      intro q
      have h1 := a.2.2.2.2 (q : X) q.2
      rw [← hmemP]
      exact h1
    obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_pPrimeCore ha
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (f a) ^ (2 ^ k) = 1
    rw [← map_pow]
    show (QuotientGroup.mk' (pPrimeCore 2 ↥K)) ((Subgroup.inclusion hAK a) ^ (2 ^ k)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨e, he⟩ := hp.exists_card_eq
  exact ⟨e, hidx.trans he⟩

end ZStar

section Assembly

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem zStar_le_pPrimeCoreOf_sup {K Z : Subgroup X} (hZ : IsSylowTwoIn (zStar K) Z) :
    zStar K ≤ pPrimeCoreOf 2 K ⊔ Z := by
  obtain ⟨e, he⟩ := exists_relIndex_zStar_eq_two_pow K
  have h1 : (pPrimeCoreOf 2 K ⊔ Z).relIndex (zStar K) ∣ 2 ^ e :=
    he ▸ Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  have h2 : (pPrimeCoreOf 2 K ⊔ Z).relIndex (zStar K) ∣ Z.relIndex (zStar K) :=
    Subgroup.relIndex_dvd_of_le_left _ le_sup_right
  have h3 : Nat.Coprime (2 ^ e) (Z.relIndex (zStar K)) :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hZ.2.2)
  exact Subgroup.relIndex_eq_one.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

omit [Finite X] in
theorem conj_mem_zStar {K : Subgroup X} {c : X} (hc : c ∈ normalizer (K : Set X)) {a : X}
    (ha : a ∈ zStar K) : c * a * c⁻¹ ∈ zStar K := by
  have hP : (pPrimeCoreOf 2 K).map (MulAut.conj c).toMonoidHom = pPrimeCoreOf 2 K := by
    rw [← pPrimeCoreOf_map_mulEquiv, map_conj_eq_of_mem_normalizer hc]
  have hcP : c ∈ normalizer (pPrimeCoreOf 2 K : Set X) := mem_normalizer_of_map_conj_eq hP
  obtain ⟨haK, -, haP, hcomm⟩ := ha
  have hc' : c⁻¹ ∈ normalizer (K : Set X) := (normalizer (K : Set X)).inv_mem hc
  have hcP' : c⁻¹ ∈ normalizer (pPrimeCoreOf 2 K : Set X) :=
    (normalizer (pPrimeCoreOf 2 K : Set X)).inv_mem hcP
  have hcaK : c * a * c⁻¹ ∈ K := ((Subgroup.mem_normalizer_iff.1 hc) a).1 haK
  refine ⟨hcaK, Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (Subgroup.le_normalizer haK)) hc', ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcP haP) hcP'
  · intro k hk
    have hk' : c⁻¹ * k * c ∈ K := by
      have := ((Subgroup.mem_normalizer_iff.1 hc') k).1 hk
      simpa using this
    have h1 : ⁅k, c * a * c⁻¹⁆ = c * ⁅c⁻¹ * k * c, a⁆ * c⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact ((Subgroup.mem_normalizer_iff.1 hcP) _).1 (hcomm _ hk')

theorem centralizer_eq_oddCoreOf_sup_of_isSylowTwoIn {Z : Subgroup X} {s : X}
    (hsyl : IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Z) :
    centralizer ({s} : Set X) = oddCoreOf (centralizer ({s} : Set X)) ⊔
      (normalizer (Z : Set X) ⊓ centralizer ({s} : Set X)) := by
  set C := centralizer ({s} : Set X) with hC
  set K := K0 X n C with hK
  have hKC : K ≤ C := K0_le n C
  have hCn : ∀ c ∈ C, c ∈ normalizer (K : Set X) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_mem_K0 n (Subgroup.le_normalizer hc) hy
    · intro hy
      have := conj_mem_K0 n (Subgroup.le_normalizer (C.inv_mem hc)) hy
      simpa [mul_assoc] using this
  have hAC : zStar K ≤ C := inf_le_left.trans hKC
  have hAn : ∀ c ∈ C, ∀ a ∈ zStar K, c * a * c⁻¹ ∈ zStar K := fun c hc a ha =>
    conj_mem_zStar (hCn c hc) ha
  have hZC : Z ≤ C := (hsyl.1.trans hAC)
  have hKsub : (K.subgroupOf C).IsSubnormal := by
    have : (K.subgroupOf C).Normal := by
      refine ⟨fun k hk c => ?_⟩
      have hk' : (k : X) ∈ K := hk
      show (c : X) * k * (c : X)⁻¹ ∈ K
      exact conj_mem_K0 n (Subgroup.le_normalizer c.2) hk'
    exact this.isSubnormal
  have hPO : pPrimeCoreOf 2 K ≤ oddCoreOf C := pPrimeCoreOf_le_oddCoreOf hKC hKsub
  refine le_antisymm (fun c hc => ?_) (sup_le (oddCoreOf_le C) inf_le_right)
  obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hAC hAn hsyl hc
  have hle : pPrimeCoreOf 2 K ⊔ Z ≤ oddCoreOf C ⊔ (normalizer (Z : Set X) ⊓ C) :=
    sup_le_sup hPO (le_inf Subgroup.le_normalizer hZC)
  exact Subgroup.mul_mem _ (hle (zStar_le_pPrimeCoreOf_sup hsyl ha)) (Subgroup.mem_sup_right hm)

theorem lemma33a_of_isSylowTwoIn {Z : Subgroup X}
    (h : ∀ s : X, s ∈ normalizer (Z : Set X) → orderOf s = 2 →
      (∀ k ∈ K0 X n (normalizer (Z : Set X)),
        ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) →
      IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Z) :
    Lemma33a X n Z :=
  fun s hs hs2 hks => centralizer_eq_oddCoreOf_sup_of_isSylowTwoIn (h s hs hs2 hks)

end Assembly

end CFSG.OddStandard.Solomon75

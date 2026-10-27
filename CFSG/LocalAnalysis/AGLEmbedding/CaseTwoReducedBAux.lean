module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

theorem commute_of_mem_normalizer_zpowers_of_pow_prime_pow {p : ℕ} (hp : p.Prime) {t v : Y}
    (ht : orderOf t = p) (hv : v ∈ Subgroup.normalizer (Subgroup.zpowers t : Set Y)) {k : ℕ}
    (hvk : v ^ p ^ k = 1) : Commute v t := by
  set φ := (Subgroup.zpowers t).normalizerMonoidHom ⟨v, hv⟩ with hφ
  have h1 : orderOf φ ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have hv' : (⟨v, hv⟩ : Subgroup.normalizer (Subgroup.zpowers t : Set Y)) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hvk)
    rw [hφ, ← map_pow, hv', map_one]
  have h2 : orderOf φ ∣ p - 1 := by
    have := orderOf_dvd_natCard φ
    rwa [IsCyclic.card_mulAut, Nat.card_zpowers, ht, Nat.totient_prime hp] at this
  have hcop : Nat.Coprime (p ^ k) (p - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos)))
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hconj := congrArg (fun f : MulAut (Subgroup.zpowers t) =>
    ((f ⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t) : Y)) hφ1
  simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at hconj
  calc v * t = v * t * v⁻¹ * v := by group
    _ = t * v := by rw [hconj]

omit [Finite Y] in
theorem mem_centralizer_of_isPGroup_stabilizer {p : ℕ} {L : Subgroup Y} {t : L}
    (hst : IsPGroup p (MulAction.stabilizer (MulAut L) t)) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (L : Set Y))
    (hct : c ∈ Subgroup.centralizer ({(t : Y)} : Set Y)) (hcop : (orderOf c).Coprime p) :
    c ∈ Subgroup.centralizer (L : Set Y) := by
  set φ := L.normalizerMonoidHom ⟨c, hcN⟩ with hφ
  have hφt : φ ∈ MulAction.stabilizer (MulAut L) t := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    apply Subtype.ext
    rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have htc := Subgroup.mem_centralizer_singleton_iff.mp hct
    calc c * (t : Y) * c⁻¹ = (t : Y) * c * c⁻¹ := by rw [htc]
      _ = t := by group
  obtain ⟨k, hk⟩ := hst ⟨φ, hφt⟩
  have h2 : orderOf φ ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h1 : orderOf φ ∣ orderOf c := by
    have := orderOf_map_dvd L.normalizerMonoidHom ⟨c, hcN⟩
    rwa [Subgroup.orderOf_mk] at this
  have hφ1 : φ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_right k) h1 h2)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconj := congrArg (fun f : MulAut L => ((f ⟨x, hx⟩ : L) : Y)) hφ1
  simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at hconj
  calc x * c = c * x * c⁻¹ * c := by rw [hconj]
    _ = c * x := by group

theorem le_sup_of_forall_coprime_mem {p : ℕ} [Fact p.Prime] (P : Sylow p Y) {A K : Subgroup Y}
    (hPA : (P : Subgroup Y) ≤ A) (hKA : K ≤ A) (hAK : A ≤ Subgroup.normalizer (K : Set Y))
    (hcop : ∀ a ∈ A, (orderOf a).Coprime p → a ∈ K) : A ≤ (P : Subgroup Y) ⊔ K := by
  have hp : p.Prime := Fact.out
  have : (K.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mpr hAK
  have hQ : IsPGroup p (A ⧸ K.subgroupOf A) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨e, m, hm, hord⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (a : Y)).ne' p hp.ne_one
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      apply hcop _ (A.pow_mem a.2 _)
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hord ▸ dvd_mul_right _ _), hord,
        Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  let PQ : Sylow p (A ⧸ K.subgroupOf A) :=
    (P.subtype hPA).mapSurjective (QuotientGroup.mk'_surjective _)
  have htop : (PQ : Subgroup (A ⧸ K.subgroupOf A)) = ⊤ :=
    (PQ.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  intro a ha
  have hmem : QuotientGroup.mk' (K.subgroupOf A) ⟨a, ha⟩ ∈ (PQ : Subgroup _) :=
    htop ▸ Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective, Sylow.coe_subtype] at hmem
  obtain ⟨r, hr, hra⟩ := hmem
  have hrk : r⁻¹ * ⟨a, ha⟩ ∈ K.subgroupOf A := QuotientGroup.eq.mp hra
  have e : a = (r : Y) * ((r⁻¹ * ⟨a, ha⟩ : A) : Y) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hr) (Subgroup.mem_subgroupOf.mp hrk)

theorem mem_normalizer_of_mem_centralizer_of_component {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) {t c : Y} (htL : t ∈ L) (htC : t ∉ Subgroup.centralizer (L : Set Y))
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) : c ∈ Subgroup.normalizer (L : Set Y) := by
  by_contra hcN
  have hL' : IsComponentOf (L.map (MulAut.conj c).toMonoidHom) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj c) L).mpr hL
  have hne : L.map (MulAut.conj c).toMonoidHom ≠ L := fun heq =>
    hcN (mem_normalizer_of_conj_map_le heq.le)
  have htc := Subgroup.mem_centralizer_singleton_iff.mp hc
  have htmem : t ∈ L.map (MulAut.conj c).toMonoidHom := by
    refine ⟨t, htL, ?_⟩
    change c * t * c⁻¹ = t
    rw [htc]
    group
  exact htC (le_centralizer_of_component_ne hL' hL hne htmem)

end Abstract

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.sylow_le_centralizer_of_isCyclic
    (h : ReducedNongeneration p Y Rb Y₀) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {t : Y}
    (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) :
    (Rb : Subgroup Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
  intro v hv
  obtain ⟨k, hk⟩ := Rb.isPGroup' ⟨v, hv⟩
  have hvk : v ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm := commute_of_mem_normalizer_zpowers_of_pow_prime_pow h.prime htp
    (mem_normalizer_zpowers_of_mem_zpowers (h.conj_mem_zpowers_of_component hL hcyc ht hv)) hvk
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq

theorem ReducedNongeneration.eq_one_of_mem_centralizer_of_isCyclic
    (h : ReducedNongeneration p Y Rb Y₀) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {a : Y} (haL : a ∈ L)
    (haC : a ∈ Subgroup.centralizer (L : Set Y)) : a = 1 := by
  have hmem : (⟨a, haL⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp haC k k.2)
  rw [h.center_eq_bot_of_isCyclic hL hcyc, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem ReducedNongeneration.not_mem_centralizer_of_isCyclic
    (h : ReducedNongeneration p Y Rb Y₀) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {t : Y} (htL : t ∈ L)
    (htp : orderOf t = p) : t ∉ Subgroup.centralizer (L : Set Y) := by
  intro htC
  have ht1 := h.eq_one_of_mem_centralizer_of_isCyclic hL hcyc htL htC
  rw [ht1, orderOf_one] at htp
  exact h.prime.one_lt.ne htp

theorem ReducedNongeneration.mem_centralizer_of_coprime_of_caseTwo
    (h : ReducedNongeneration p Y Rb Y₀) (hKL : KFactCaseTwoLocal) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hiso : IsCaseTwoGroup p L)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {t : Y}
    (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (hcop : (orderOf c).Coprime p) :
    c ∈ Subgroup.centralizer (L : Set Y) := by
  have hcN := mem_normalizer_of_mem_centralizer_of_component hL ht.2
    (h.not_mem_centralizer_of_isCyclic hL hcyc ht.2 htp) hc
  have hst := (hKL p L hiso).2.1 ⟨t, ht.2⟩ (by rw [Subgroup.orderOf_mk, htp])
  exact mem_centralizer_of_isPGroup_stabilizer hst hcN hc hcop

end Reduced

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

section Quotient

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

omit [N.Normal] in
private theorem glue618_inf_eq_bot (hN : Nat.Coprime 3 (Nat.card N)) {A : Subgroup X}
    (hA : IsPGroup 3 A) : A ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_left k hN

private theorem glue618_card_map (hN : Nat.Coprime 3 (Nat.card N)) {A : Subgroup X}
    (hA : IsPGroup 3 A) : Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap A) := by
    intro a b hab
    have hab' : QuotientGroup.mk' N (a : X) = QuotientGroup.mk' N (b : X) :=
      congrArg Subtype.val hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab'
    have h : (a : X)⁻¹ * b ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem a.2) b.2, hab'⟩
    rw [glue618_inf_eq_bot hN hA, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact Subtype.ext h
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective A⟩)).symm

private theorem glue618_coprime_comap (hN : Nat.Coprime 3 (Nat.card N))
    {Q : Subgroup (X ⧸ N)} (hQ : Nat.Coprime 3 (Nat.card Q)) :
    Nat.Coprime 3 (Nat.card (Q.comap (QuotientGroup.mk' N))) := by
  have h1 := (Q.comap (QuotientGroup.mk' N)).card_mul_index
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
  have h2 := Q.card_mul_index
  have h3 := N.card_eq_card_quotient_mul_card_subgroup
  have hidx : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card (Q.comap (QuotientGroup.mk' N)) = Nat.card Q * Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_right hidx
    rw [h1, h3, ← h2]
    ring
  rw [hcard]
  exact Nat.Coprime.mul_right hQ hN

private theorem glue618_map_normalizer (hN : Nat.Coprime 3 (Nat.card N)) {P : Subgroup X}
    (hP : IsPGroup 3 P) :
    (normalizer (P : Set X)).map (QuotientGroup.mk' N) =
      normalizer ((P.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
  refine le_antisymm (le_normalizer_map _) (fun y hy => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hN3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN
  have hcardW : Nat.card (P ⊔ N : Subgroup X) = Nat.card N * Nat.card P := by
    have h1 := relIndex_mul_card N (P ⊔ N)
    rw [inf_eq_left.2 le_sup_right, relIndex_sup_right] at h1
    have h2 := relIndex_mul_card N P
    rw [inf_comm, glue618_inf_eq_bot hN hP, card_bot, mul_one] at h2
    rw [← h1, h2, mul_comm]
  have hP'W : P.map (MulAut.conj x).toMonoidHom ≤ P ⊔ N := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : QuotientGroup.mk' N (x * a * x⁻¹) ∈ P.map (QuotientGroup.mk' N) := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 hy _).1 ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbe⟩ := h1
    have h2 : b⁻¹ * (x * a * x⁻¹) ∈ N := QuotientGroup.eq.1 hbe
    have e : x * a * x⁻¹ = b * (b⁻¹ * (x * a * x⁻¹)) := by group
    change x * a * x⁻¹ ∈ P ⊔ N
    rw [e]
    exact mul_mem (mem_sup_left hb) (mem_sup_right h2)
  have hsyl : ∀ Q : Subgroup X, Q ≤ P ⊔ N → Nat.card Q = Nat.card P →
      ¬ 3 ∣ (Q.subgroupOf (P ⊔ N)).index := by
    intro Q hQW hQ
    have h1 := relIndex_mul_card Q (P ⊔ N)
    rw [inf_eq_left.2 hQW, hQ, hcardW] at h1
    have : Q.relIndex (P ⊔ N) = Nat.card N := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    change ¬ 3 ∣ Q.relIndex (P ⊔ N)
    rw [this]
    exact hN3
  have hpg : ∀ Q : Subgroup X, IsPGroup 3 Q → IsPGroup 3 (Q.subgroupOf (P ⊔ N)) :=
    fun Q hQ => hQ.comap_of_injective _ (P ⊔ N).subtype_injective
  have hP' : IsPGroup 3 (P.map (MulAut.conj x).toMonoidHom) := hP.map _
  let S₁ : Sylow 3 (P ⊔ N : Subgroup X) := (hpg P hP).toSylow (hsyl P le_sup_left rfl)
  let S₂ : Sylow 3 (P ⊔ N : Subgroup X) := (hpg _ hP').toSylow
    (hsyl _ hP'W (card_map_of_injective (MulAut.conj x).injective))
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq (P ⊔ N : Subgroup X) S₂ S₁
  have hle : P.map (MulAut.conj ((w : X) * x)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have hxa' : x * a * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h1 : (⟨x * a * x⁻¹, hP'W hxa'⟩ : (P ⊔ N : Subgroup X)) ∈
        (S₂ : Subgroup (P ⊔ N : Subgroup X)) := mem_subgroupOf.2 hxa'
    have h2 : (MulAut.conj w) • (⟨x * a * x⁻¹, hP'W hxa'⟩ : (P ⊔ N : Subgroup X)) ∈
        (S₁ : Subgroup (P ⊔ N : Subgroup X)) := by
      rw [← hw, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    have h3 := mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply, mul_assoc] using h3
  have heq : P.map (MulAut.conj ((w : X) * x)).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj _).injective])
  have hwx : (w : X) * x ∈ normalizer (P : Set X) := by
    generalize (w : X) * x = g at heq ⊢
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← heq]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← heq] at ha
      obtain ⟨b, hb, hbe⟩ := ha
      have : b = a := (MulAut.conj g).injective hbe
      rwa [← this]
  obtain ⟨b, hb, h₀, hh₀, hbh⟩ := mem_sup_of_normal_right.1 w.2
  refine ⟨h₀ * x, ?_, ?_⟩
  · have : h₀ * x = b⁻¹ * ((w : X) * x) := by rw [← hbh]; group
    rw [this]
    exact mul_mem (inv_mem (le_normalizer hb)) hwx
  · rw [map_mul, (QuotientGroup.mk'_apply N h₀), (QuotientGroup.eq_one_iff h₀).2 hh₀, one_mul]

omit [Finite X] in
private theorem glue618_isKGroup_quotient (hX : CFSG.IsKGroup X) : CFSG.IsKGroup (X ⧸ N) :=
  hX.quotient N

private theorem glue618_core (hN : Nat.Coprime 3 (Nat.card N))
    (hNmax : ∀ Q : Subgroup X, Q.Normal → Nat.Coprime 3 (Nat.card Q) → Q ≤ N)
    (Q : Subgroup (X ⧸ N)) (hQn : Q.Normal) (hQ : Nat.Coprime 3 (Nat.card Q)) : Q = ⊥ := by
  have hle : Q.comap (QuotientGroup.mk' N) ≤ N :=
    hNmax _ (hQn.comap _) (glue618_coprime_comap hN hQ)
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Q,
    eq_bot_iff]
  refine (Subgroup.map_mono hle).trans ?_
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']

omit [Finite X] [N.Normal] in
private theorem glue618_isElemAbelian_map {X' : Type} [Group X'] (f : X →* X')
    {A : Subgroup X} (hA : IsElemAbelian 3 A) : IsElemAbelian 3 (A.map f) :=
  CFSG.Open.IsElemAbelian.map hA _

private theorem glue618_data (hX : CFSG.IsKGroup X) (hN : Nat.Coprime 3 (Nat.card N))
    (hNmax : ∀ Q : Subgroup X, Q.Normal → Nat.Coprime 3 (Nat.card Q) → Q ≤ N)
    {B Z M : Subgroup X} (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBi : ¬ 3 ∣ B.index) (hZB : Z ≤ B) (hZ3 : Nat.card Z = 3)
    (hBZ : normalizer (B : Set X) ≤ normalizer (Z : Set X)) (hZM : normalizer (Z : Set X) ≤ M)
    (hNM : N ≤ M) (hM : M ≠ ⊤) :
    Data618 (B.map (QuotientGroup.mk' N)) (Z.map (QuotientGroup.mk' N))
      (M.map (QuotientGroup.mk' N)) := by
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hZ3' : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3]; norm_num)
  refine ⟨glue618_isKGroup_quotient hX, glue618_core hN hNmax, glue618_isElemAbelian_map _ hB,
    by rw [glue618_card_map hN hB3, hB9], fun h => hBi (h.trans (Subgroup.index_map_dvd B
      (QuotientGroup.mk'_surjective N))), Subgroup.map_mono hZB,
    by rw [glue618_card_map hN hZ3', hZ3], ?_, ?_, ?_⟩
  · rw [← glue618_map_normalizer hN hB3]
    exact (Subgroup.map_mono hBZ).trans (le_normalizer_map _)
  · rw [← glue618_map_normalizer hN hZ3']
    exact Subgroup.map_mono hZM
  · intro htop
    apply hM
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' N) M
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hNM] at h
    exact h.symm

omit [Finite X] in
private theorem glue618_map_normalClosure {Z : Subgroup X} {L : Subgroup (X ⧸ N)} [L.Normal]
    [IsSimpleGroup L] (hZL : Z.map (QuotientGroup.mk' N) ≤ L)
    (hZ : Z.map (QuotientGroup.mk' N) ≠ ⊥) :
    (normalClosure (Z : Set X)).map (QuotientGroup.mk' N) = L := by
  rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective N), ← Subgroup.coe_map]
  have hCL := normalClosure_le_normal (N := L) hZL
  have : ((normalClosure ((Z.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
      Set (X ⧸ N))).subgroupOf L).Normal := (normalClosure_normal).subgroupOf L
  rcases Subgroup.Normal.eq_bot_or_eq_top ((normalClosure ((Z.map (QuotientGroup.mk' N) :
      Subgroup (X ⧸ N)) : Set (X ⧸ N))).subgroupOf L) with h | h
  · exact absurd (eq_bot_iff.2 (Subgroup.le_normalClosure.trans
      ((subgroupOf_eq_bot.1 h).eq_bot_of_le hCL).le)) hZ
  · exact le_antisymm hCL (subgroupOf_eq_top.1 h)

omit [Finite X] in
private theorem glue618_commutator_eq (hN : Nat.Coprime 3 (Nat.card N)) {Z : Subgroup X}
    (hZ3 : ∀ w ∈ Z, w ^ 3 = 1) {L : Subgroup (X ⧸ N)}
    (hKL : (normalClosure (Z : Set X)).map (QuotientGroup.mk' N) = L) (hLL : ⁅L, L⁆ = L) :
    ⁅normalClosure (Z : Set X), normalClosure (Z : Set X)⁆ = normalClosure (Z : Set X) := by
  set K := normalClosure (Z : Set X)
  set D := ⁅K, K⁆ with hD
  have hDmap : D.map (QuotientGroup.mk' N) = L := by
    rw [hD, Subgroup.map_commutator, hKL, hLL]
  refine le_antisymm (commutator_le_left K K) (normalClosure_le_normal fun w hw => ?_)
  have hwK : w ∈ K := subset_normalClosure hw
  obtain ⟨c, hcD, hc⟩ : QuotientGroup.mk' N w ∈ D.map (QuotientGroup.mk' N) := by
    rw [hDmap, ← hKL]
    exact ⟨w, hwK, rfl⟩
  have ho : c⁻¹ * w ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc
    exact hc
  have hψ : QuotientGroup.mk' D w = QuotientGroup.mk' D (c⁻¹ * w) := by
    rw [map_mul, map_inv, QuotientGroup.mk'_apply D c, (QuotientGroup.eq_one_iff c).2 hcD,
      inv_one, one_mul]
  have h1 : orderOf (QuotientGroup.mk' D w) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hZ3 w hw, map_one])
  have h2 : orderOf (QuotientGroup.mk' D w) ∣ Nat.card N := by
    rw [hψ]
    exact (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard N ho)
  have h3 := Nat.eq_one_of_dvd_coprimes hN h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

omit [Finite X] in
private theorem glue618_maximal {K : Subgroup X} {L : Subgroup (X ⧸ N)} [IsSimpleGroup L]
    (hKL : K.map (QuotientGroup.mk' N) = L) {R : Subgroup X} (hRK : R ≤ K)
    (hKR : K ≤ normalizer (R : Set X)) (hNR : K ⊓ N ≤ R) : R ≤ N ∨ K ≤ R := by
  have hle : R.map (QuotientGroup.mk' N) ≤ L := hKL ▸ Subgroup.map_mono hRK
  have hnorm : ((R.map (QuotientGroup.mk' N)).subgroupOf L).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hle, ← hKL]
    exact (Subgroup.map_mono hKR).trans (le_normalizer_map _)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((R.map (QuotientGroup.mk' N)).subgroupOf L)
    with h | h
  · left
    have h' : R.map (QuotientGroup.mk' N) = ⊥ := (subgroupOf_eq_bot.1 h).eq_bot_of_le hle
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h'
    exact h'
  · right
    intro k hk
    obtain ⟨n, hn, hnk⟩ : QuotientGroup.mk' N k ∈ R.map (QuotientGroup.mk' N) :=
      subgroupOf_eq_top.1 h (hKL ▸ ⟨k, hk, rfl⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
    have h' : n⁻¹ * k ∈ R := hNR ⟨K.mul_mem (K.inv_mem (hRK hn)) hk, hnk⟩
    simpa using R.mul_mem hn h'

private theorem glue618_card_le_three (hN : Nat.Coprime 3 (Nat.card N)) {K : Subgroup X}
    {L Q : Subgroup (X ⧸ N)} (hKL : K.map (QuotientGroup.mk' N) = L)
    (hQ : Nat.card (L ⊓ Q : Subgroup (X ⧸ N)) = 3) (hQi : ¬ 3 ∣ (L ⊓ Q).relIndex L)
    {E : Subgroup X} (hEK : E ≤ K) (hE : IsPGroup 3 E) : Nat.card E ≤ 3 := by
  rw [← glue618_card_map hN hE]
  have hEL : E.map (QuotientGroup.mk' N) ≤ L := hKL ▸ Subgroup.map_mono hEK
  obtain ⟨j, hj⟩ := (hE.map (QuotientGroup.mk' N)).exists_card_eq
  have hL : Nat.card L = (L ⊓ Q).relIndex L * 3 := by
    have h := Subgroup.relIndex_mul_card (L ⊓ Q) L
    rw [inf_eq_left.2 inf_le_left, hQ] at h
    exact h.symm
  have hdvd : 3 ^ j ∣ 3 * (L ⊓ Q).relIndex L := by
    rw [← hj, mul_comm, ← hL]
    exact Subgroup.card_dvd_of_le hEL
  have hcop : Nat.Coprime (3 ^ j) ((L ⊓ Q).relIndex L) :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQi)
  rw [hj]
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)

omit [Finite X] in
private theorem glue618_commutator_mem {K : Subgroup X} {L : Subgroup (X ⧸ N)}
    (hKL : K.map (QuotientGroup.mk' N) = L) {b : X}
    (hb : ∀ l ∈ L, QuotientGroup.mk' N b * l = l * QuotientGroup.mk' N b) {g : X}
    (hg : g ∈ zpowers b) {k : X} (hk : k ∈ K) : ⁅g, k⁆ ∈ N := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  have hl : QuotientGroup.mk' N k ∈ L := hKL ▸ ⟨k, hk, rfl⟩
  have hc : Commute (QuotientGroup.mk' N (b ^ n)) (QuotientGroup.mk' N k) := by
    rw [map_zpow]
    exact Commute.zpow_left (hb _ hl) n
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact hc

end Quotient

private theorem glue618_commutator_self {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsQuasisimple L) : ⁅L, L⁆ = L := by
  have h := Subgroup.map_commutator (⊤ : Subgroup L) ⊤ L.subtype
  rw [← commutator_def, hL.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.symm

section Ambient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem glue618_card_subgroupOf {A H : Subgroup G} (h : A ≤ H) :
    Nat.card (A.subgroupOf H) = Nat.card A :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

omit [Finite G] in
private theorem glue618_isElemAbelian_subgroupOf {A H : Subgroup G} (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hA H

omit [Finite G] in
private theorem glue618_le_primeCore (H : Subgroup G) (Q : Subgroup H) (hQn : Q.Normal)
    (hQ : Nat.Coprime 3 (Nat.card Q)) : Q ≤ (rankThreePrimeCore 3 H).subgroupOf H := by
  have hsub : (Q.map H.subtype).subgroupOf H = Q :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q
  have hle : Q.map H.subtype ≤ rankThreePrimeCore 3 H := by
    refine le_sSup ⟨Subgroup.map_subtype_le Q, by rw [hsub]; exact hQn, ?_⟩
    rwa [Subgroup.card_map_of_injective H.subtype_injective]
  intro q hq
  exact mem_subgroupOf.2 (hle ⟨q, hq, rfl⟩)

private theorem glue618_pRank_eq_one {K : Subgroup G} {z : G} (hzK : zpowers z ≤ K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hK : ∀ E : Subgroup G, E ≤ K → ∀ k : ℕ, Nat.card E = 3 ^ k → Nat.card E ≤ 3) :
    CFSG.Open.pRank 3 K = 1 := by
  unfold CFSG.Open.pRank
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨E, hEK, -, hEk⟩
    have h := hK E hEK k hEk
    rw [hEk] at h
    by_contra hk
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · apply le_csSup (pRank_set_bddAbove 3 (by norm_num) K)
    refine ⟨zpowers z, hzK, ⟨isMulCommutative_iff.2 fun a b => ?_, fun w hw => ?_⟩, ?_⟩
    · obtain ⟨m, hm⟩ := mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 b.2
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn]
      exact (Commute.zpow_zpow_self z m n).eq
    · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, hz3, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, pow_one]

omit [Finite G] in
private theorem glue618_le_normalizer {H : Subgroup G} (K : Subgroup H) [K.Normal] :
    H ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have hsub : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).1 (by rw [hsub]; infer_instance)

omit [Finite G] in
private theorem glue618_maximal_lift {H O : Subgroup G} [(O.subgroupOf H).Normal]
    {K : Subgroup H} {L : Subgroup (H ⧸ O.subgroupOf H)} [IsSimpleGroup L]
    (hKL : K.map (QuotientGroup.mk' (O.subgroupOf H)) = L) (R : Subgroup G)
    (hRK : R ≤ K.map H.subtype) (hRn : (R.subgroupOf (K.map H.subtype)).Normal)
    (hOR : K.map H.subtype ⊓ O ≤ R) : R = K.map H.subtype ⊓ O ∨ R = K.map H.subtype := by
  have hsub : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  have hRH : R ≤ H := hRK.trans (map_subtype_le K)
  have hKR : K.map H.subtype ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRK).1 hRn
  have h1 : R.subgroupOf H ≤ K := hsub ▸ comap_mono hRK
  have h2 : K ≤ normalizer ((R.subgroupOf H : Subgroup H) : Set H) := by
    rw [← subgroupOf_normalizer_eq hRH, ← hsub]
    exact comap_mono hKR
  have h3 : K ⊓ O.subgroupOf H ≤ R.subgroupOf H := fun w hw =>
    mem_subgroupOf.2 (hOR ⟨⟨w, hw.1, rfl⟩, mem_subgroupOf.1 hw.2⟩)
  rcases glue618_maximal hKL h1 h2 h3 with h | h
  · left
    refine le_antisymm (le_inf hRK fun r hr => ?_) hOR
    exact mem_subgroupOf.1 (h (show (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H from hr))
  · right
    refine le_antisymm hRK fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := hk
    exact mem_subgroupOf.1 (h hk')

omit [Finite G] in
private theorem glue618_centralizes {H O B Z : Subgroup G} [(O.subgroupOf H).Normal]
    {K : Subgroup H} {L : Subgroup (H ⧸ O.subgroupOf H)}
    (hKL : K.map (QuotientGroup.mk' (O.subgroupOf H)) = L) {c : H ⧸ O.subgroupOf H}
    (hc : c ∈ (B.subgroupOf H).map (QuotientGroup.mk' (O.subgroupOf H)))
    (hcZ : c ∉ (Z.subgroupOf H).map (QuotientGroup.mk' (O.subgroupOf H)))
    (hcL : ∀ l ∈ L, c * l = l * c) :
    ∃ b ∈ B, b ∉ Z ∧ ⁅zpowers b, K.map H.subtype⁆ ≤ O := by
  obtain ⟨b, hbB, rfl⟩ := hc
  refine ⟨b, mem_subgroupOf.1 hbB, fun hbZ => hcZ ⟨b, mem_subgroupOf.2 hbZ, rfl⟩, ?_⟩
  rw [Subgroup.commutator_le]
  intro g hg k hk
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  obtain ⟨k', hk', rfl⟩ := hk
  have h := glue618_commutator_mem hKL hcL (zpow_mem (mem_zpowers b) n) hk'
  have he : ⁅(b : G) ^ n, H.subtype k'⁆ = H.subtype ⁅b ^ n, k'⁆ := by
    rw [map_commutatorElement, map_zpow]
    rfl
  rw [he]
  exact mem_subgroupOf.1 h

end Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_prop614Component (hS : Setting G) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H S : Subgroup G}
    (hext : Prop614Extremal M (zpowers x ⊔ zpowers z) H S)
    (h0 : ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H)
    (h6 : rankThreePrimeCore 3 H ≤ M) :
    ∃ K : Subgroup G, Prop614Component M H K x z := by
  have : IsSimpleGroup G := hS.simple
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  obtain ⟨hOH, hHO, hO3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 H
  have hBH : zpowers x ⊔ zpowers z ≤ H := hext.pair.le
  have hZB : zpowers z ≤ zpowers x ⊔ zpowers z := le_sup_right
  have hZH : zpowers z ≤ H := hZB.trans hBH
  have hzH : z ∈ H := hZH (mem_zpowers z)
  have : ((rankThreePrimeCore 3 H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOH).2 hHO
  have hO3' : Nat.Coprime 3 (Nat.card ((rankThreePrimeCore 3 H).subgroupOf H)) := by
    rwa [glue618_card_subgroupOf hOH]
  have hz3 : Nat.card (zpowers z) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz.pow_eq_one hz.ne_one]
  have hKH : CFSG.IsKGroup H :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper) H
      (twoLocal_ne_top hS.nonab H hext.pair.isTwoLocal)
  have hBZ : normalizer (((zpowers x ⊔ zpowers z).subgroupOf H : Subgroup H) : Set H) ≤
      normalizer (((zpowers z).subgroupOf H : Subgroup H) : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH, ← subgroupOf_normalizer_eq hZH]
    exact comap_mono (normalizer_plane_le_normalizer_zpowers hS hsit hx hz)
  have hZM : normalizer (((zpowers z).subgroupOf H : Subgroup H) : Set H) ≤ M.subgroupOf H := by
    rw [← subgroupOf_normalizer_eq hZH]
    exact comap_mono (normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA
      hsit.isCoreMaxLocal hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one
      hz.pow_eq_one)
  have d := glue618_data (B := (zpowers x ⊔ zpowers z).subgroupOf H)
    (Z := (zpowers z).subgroupOf H) (M := M.subgroupOf H) hKH hO3' (glue618_le_primeCore H)
    (glue618_isElemAbelian_subgroupOf hB.isElemAbelian)
    (by rw [glue618_card_subgroupOf hBH, hB.card_eq]; norm_num) h0 (comap_mono hZB)
    (by rw [glue618_card_subgroupOf hZH, hz3]) hBZ hZM (comap_mono h6)
    (fun h => hext.pair.not_le (subgroupOf_eq_top.1 h))
  obtain ⟨L, hLn, hLc, hLs, hLB, hLi, hZL, hLY, c, hc, hcZ, hcL⟩ :=
    exists_normal_component hKF1 hKF2 d
  have hZne : ((zpowers z).subgroupOf H).map
      (QuotientGroup.mk' ((rankThreePrimeCore 3 H).subgroupOf H)) ≠ ⊥ := by
    intro h
    have h' := d.card_Z
    rw [h, Subgroup.card_bot] at h'
    omega
  have hKL := glue618_map_normalClosure hZL hZne
  have hZ3 : ∀ w ∈ (zpowers z).subgroupOf H, w ^ 3 = 1 := fun w hw =>
    Subtype.ext (by simpa using hB.isElemAbelian.2 _ (hZB (mem_subgroupOf.1 hw)))
  have hperf := glue618_commutator_eq hO3' hZ3 hKL (glue618_commutator_self hLc.2.2)
  set K := normalClosure (((zpowers z).subgroupOf H : Subgroup H) : Set H)
  have hsub : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  have hzK : zpowers z ≤ K.map H.subtype :=
    zpowers_le.2 ⟨⟨z, hzH⟩, subset_normalClosure (mem_subgroupOf.2 (mem_zpowers z)), rfl⟩
  refine ⟨K.map H.subtype, map_subtype_le K, glue618_le_normalizer K, fun h => hLY ?_, hzK,
    glue618_pRank_eq_one hzK hz.pow_eq_one hz.ne_one fun E hEK k hEk => ?_,
    by rw [← Subgroup.map_commutator, hperf], lt_of_le_of_ne inf_le_left fun h => ?_,
    glue618_maximal_lift hKL, glue618_centralizes hKL hc hcZ hcL⟩
  · rw [← hKL]
    exact Subgroup.map_mono fun k hk => mem_subgroupOf.2 (h ⟨k, hk, rfl⟩)
  · have hEH : E ≤ H := hEK.trans (map_subtype_le K)
    have hE3 : IsPGroup 3 (E.subgroupOf H) :=
      IsPGroup.of_card (n := k) (by rw [glue618_card_subgroupOf hEH, hEk])
    rw [← glue618_card_subgroupOf hEH]
    exact glue618_card_le_three hO3' hKL hLB hLi (hsub ▸ comap_mono hEK) hE3
  · have hzKO : z ∈ K.map H.subtype ⊓ rankThreePrimeCore 3 H := by
      rw [h]
      exact hzK (mem_zpowers z)
    have hzO : z ∈ rankThreePrimeCore 3 H := hzKO.2
    have h3 := Subgroup.orderOf_dvd_natCard _ hzO
    rw [orderOf_eq_prime hz.pow_eq_one hz.ne_one] at h3
    exact absurd (Nat.Coprime.eq_one_of_dvd hO3 h3) (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC

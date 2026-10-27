module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndexResidue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.LineTransitive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentralProduct
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageOdd
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbedding CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barM_blocks_commute {M S L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M S L₁) (h₂ : IsWeakSBlock M S L₂) (hne : barM M L₁ ≠ barM M L₂) :
    ∀ x ∈ barM M L₁, ∀ y ∈ barM M L₂, x * y = y * x := by
  intro x hx y hy
  have hbot := CFSG.ComponentClassification.LocalComponents.commute_of_ne
    (barM M L₁) (barM M L₂) h₁.component h₂.component hne
  have h1 : ⁅x, y⁆ ∈ ⁅barM M L₁, barM M L₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem isPGroup_three_sup_zpowers {Q : Type*} [Group Q] {a b : Q} (hab : Commute a b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Q) := by
  intro g
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab.zpow_zpow k l).eq
  obtain ⟨x, hx, y, hy, hg⟩ := exists_mul_of_mem_sup hcomm g.2
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute (a ^ k) (b ^ l) := hab.zpow_zpow k l
  have hA : (a ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hB : (b ^ l) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [show (g : Q) = a ^ k * b ^ l from hg, hc.mul_pow, hA, hB, one_mul]

theorem exists_conj_mem_of_sylow_set {X R : Subgroup G} (hR : IsPGroup 3 R)
    (hidx : ¬ 3 ∣ R.relIndex X) {E : Subgroup G} (hEX : E ≤ X) (hE : IsPGroup 3 E) :
    ∃ h ∈ X, ∀ x ∈ E, h⁻¹ * x * h ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR'p : IsPGroup 3 (R.subgroupOf X) := hR.comap_of_injective X.subtype X.subtype_injective
  set S₀ : Sylow 3 ↥X := hR'p.toSylow hidx
  have hE' : IsPGroup 3 (E.subgroupOf X) := hE.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨Q', hQ⟩ := hE'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥X S₀ Q'
  refine ⟨(h : G), h.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hEX hx⟩ : ↥X) ∈ (Q' : Subgroup ↥X) :=
    hQ (Subgroup.mem_subgroupOf.mpr hx)
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hmem : h⁻¹ * ⟨x, hEX hx⟩ * h ∈ R.subgroupOf X := by
    have := (IsPGroup.mem_toSylow hR'p hidx).mp hxQ
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

theorem mem_map_conj_iff' {Q : Type*} [Group Q] {K : Subgroup Q} {h z : Q} :
    z ∈ K.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * z * h ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem card_eq_three_of_mem' {Q : Type*} [Group Q] [Finite Q] {R A : Subgroup Q}
    (hR9 : Nat.card R = 9) (hA : A ≤ R) {a b : Q} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ R) (hbA : b ∉ A) : Nat.card A = 3 := by
  have hdvd : Nat.card A ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hR9]
    exact Subgroup.card_dvd_of_le hA
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases m
  · exfalso
    have h1 : Nat.card A = 1 := by simpa using hm'
    have hbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A h1
    exact ha1 (by simpa [hbot] using ha)
  · simpa using hm'
  · exfalso
    have hAR : A = R := Subgroup.eq_of_le_of_card_ge hA (by rw [hR9]; simp [hm', show (3 : ℕ) ^ 2 = 9 by norm_num])
    exact hbA (hAR ▸ hb)

theorem isElemAbelian_map_conj' {p : ℕ} {Q : Type*} [Group Q] {K : Subgroup Q} {h : Q}
    (hK : IsElemAbelian p K) : IsElemAbelian p (K.map (MulAut.conj h).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hK _

theorem transitive_map_conj' {Q : Type*} [Group Q] {N K : Subgroup Q} {h : Q}
    (htr : TransitiveOnNonidentity N K) :
    TransitiveOnNonidentity (N.map (MulAut.conj h).toMonoidHom)
      (K.map (MulAut.conj h).toMonoidHom) := by
  intro x hx y hy hx1 hy1
  rw [mem_map_conj_iff'] at hx hy
  have hx1' : h⁻¹ * x * h ≠ 1 := fun e => hx1 (by
    calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hy1' : h⁻¹ * y * h ≠ 1 := fun e => hy1 (by
    calc y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨n, hn, hnx⟩ := htr _ hx _ hy hx1' hy1'
  refine ⟨h * n * h⁻¹, Subgroup.mem_map.mpr ⟨n, hn, rfl⟩, ?_⟩
  calc h * n * h⁻¹ * x * (h * n * h⁻¹)⁻¹ = h * (n * (h⁻¹ * x * h) * n⁻¹) * h⁻¹ := by group
    _ = h * (h⁻¹ * y * h) * h⁻¹ := by rw [hnx]
    _ = y := by group

theorem map_conj_le_normalizer' {Q : Type*} [Group Q] {N K : Subgroup Q} {h : Q}
    (hNK : N ≤ Subgroup.normalizer (K : Set Q)) :
    N.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer ((K.map (MulAut.conj h).toMonoidHom : Subgroup Q) : Set Q) :=
  le_trans (Subgroup.map_mono hNK) (Subgroup.le_normalizer_map _)

theorem false_of_line_pair {Q : Type*} [Group Q] [Finite Q] {K N : Subgroup Q}
    (hK : IsElemAbelian 3 K) (hK9 : Nat.card K = 9) (hNK : N ≤ Subgroup.normalizer (K : Set Q))
    (htr : TransitiveOnNonidentity N K) {Λ₁ Λ₂ : Subgroup Q}
    (hperm : ∀ n ∈ N, Λ₁.map (MulAut.conj n).toMonoidHom = Λ₁ ∨
      Λ₁.map (MulAut.conj n).toMonoidHom = Λ₂)
    {a b a' b' : Q} (haK : a ∈ K) (haΛ : a ∈ Λ₁) (ha1 : a ≠ 1)
    (hbK : b ∈ K) (hbΛ : b ∉ Λ₁)
    (ha'K : a' ∈ K) (ha'Λ : a' ∈ Λ₂) (ha'1 : a' ≠ 1)
    (hb'K : b' ∈ K) (hb'Λ : b' ∉ Λ₂) : False := by
  have hA3 : Nat.card (K ⊓ Λ₁ : Subgroup Q) = 3 :=
    card_eq_three_of_mem' (A := K ⊓ Λ₁) hK9 (show K ⊓ Λ₁ ≤ K from inf_le_left)
      (show a ∈ K ⊓ Λ₁ from ⟨haK, haΛ⟩) ha1 hbK (fun h => hbΛ h.2)
  have hB3 : Nat.card (K ⊓ Λ₂ : Subgroup Q) = 3 :=
    card_eq_three_of_mem' (A := K ⊓ Λ₂) hK9 (show K ⊓ Λ₂ ≤ K from inf_le_left)
      (show a' ∈ K ⊓ Λ₂ from ⟨ha'K, ha'Λ⟩) ha'1 hb'K (fun h => hb'Λ h.2)
  refine false_of_transitive_of_pair (N := N) (R := K) (A := K ⊓ Λ₁) (B := K ⊓ Λ₂)
    hK hK9 hNK htr (show K ⊓ Λ₁ ≤ K from inf_le_left) hA3
    (show K ⊓ Λ₂ ≤ K from inf_le_left) hB3 ?_
  intro n hn
  have hKn : K.map (MulAut.conj n).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNK hn)
  have key : ∀ x : Q, x ∈ K ↔ n⁻¹ * x * n ∈ K := fun x => by
    rw [← mem_map_conj_iff', hKn]
  have hmap : ∀ Λ : Subgroup Q, (K ⊓ Λ).map (MulAut.conj n).toMonoidHom =
      K ⊓ Λ.map (MulAut.conj n).toMonoidHom := fun Λ => by
    ext x
    rw [mem_map_conj_iff', Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj_iff', ← key]
  rcases hperm n hn with h1 | h2
  · left
    rw [hmap, h1]
  · right
    rw [hmap, h2]

omit [Finite G] in
theorem barM_le_normalizer_barM_of_le {M X R : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (R : Set G)) :
    barM M X ≤ Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := mem_barM_iff.mp hx
  have hRm : R.map (MulAut.conj (m : G)).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX hm)
  have e := barM_map_conj m.2 R
  rw [hRm] at e
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e.symm

omit [Finite G] in
theorem barM_perm_of_blocks {M H L₁ L₂ : Subgroup G}
    (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    {ν : ↥M ⧸ CFSG.pCore 2 ↥M} (hν : ν ∈ barM M H) :
    (barM M L₁).map (MulAut.conj ν).toMonoidHom = barM M L₁ ∨
      (barM M L₁).map (MulAut.conj ν).toMonoidHom = barM M L₂ := by
  obtain ⟨m, hm, rfl⟩ := mem_barM_iff.mp hν
  have hnS : (m : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [hH]
    exact hm
  have hW := hL₁.map_conj m.2 hnS
  have e : barM M (L₁.map (MulAut.conj (m : G)).toMonoidHom) =
      (barM M L₁).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m)).toMonoidHom :=
    barM_map_conj m.2 L₁
  rcases hk2 _ hW with h | h
  · left
    rw [← e, h]
  · right
    rw [← e, h]

theorem PairStrongCtx.false_of_twoImages_of_transitive {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hRel : IsElemAbelian 3 R) (hR9 : Nat.card R = 9)
    (htr : TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R)
    {L₁ L₂ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L', IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hy₁ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy₂ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  have hpr := hctx.pair
  have hH := hpr.normalizer_twoCore_H
  have hidx : ¬ 3 ∣ (barM M R).relIndex (barM M H) := by
    have := not_three_dvd_relIndex_barM hctx
    rwa [hH] at this
  have hRbP : IsPGroup 3 (barM M R) := by
    have hc9 : Nat.card (barM M R) = 9 :=
      (card_barM_of_isPGroup_three hpr.isPGroup_R hpr.le_M).trans hR9
    exact IsPGroup.of_card (n := 2) (by rw [hc9]; norm_num)
  obtain ⟨y₁, hy₁mem, hy₁3, hy₁C⟩ := hy₁
  obtain ⟨y₂, hy₂mem, hy₂3, hy₂C⟩ := hy₂
  have hy₁H : y₁ ∈ barM M H := by
    have h : y₁ ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
      barM_mono inf_le_left hy₁mem
    rwa [hH] at h
  have hy₂H : y₂ ∈ barM M H := by
    have h : y₂ ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
      barM_mono inf_le_left hy₂mem
    rwa [hH] at h
  have hy₁Λ : y₁ ∈ barM M L₁ := barM_mono inf_le_right hy₁mem
  have hy₂Λ : y₂ ∈ barM M L₂ := barM_mono inf_le_right hy₂mem
  have hy₁1 : y₁ ≠ 1 := fun h => hy₁C (h ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h => hy₂C (h ▸ Subgroup.one_mem _)
  have hcomm : Commute y₁ y₂ := barM_blocks_commute hL₁ hL₂ hne y₁ hy₁Λ y₂ hy₂Λ
  have hy₂notΛ₁ : y₂ ∉ barM M L₁ := fun h => hy₂C (Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (barM_blocks_commute hL₁ hL₂ hne y₂ h z hz).symm)
  have hy₁notΛ₂ : y₁ ∉ barM M L₂ := fun h => hy₁C (Subgroup.mem_centralizer_iff.mpr fun z hz =>
    barM_blocks_commute hL₁ hL₂ hne z hz y₁ h)
  have hE : IsPGroup 3 (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ :
      Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    isPGroup_three_sup_zpowers hcomm hy₁3 hy₂3
  have hEX : (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ :
      Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ barM M H :=
    sup_le (Subgroup.zpowers_le.mpr hy₁H) (Subgroup.zpowers_le.mpr hy₂H)
  obtain ⟨c, hcX, hconj⟩ := exists_conj_mem_of_sylow_set hRbP hidx hEX hE
  have hyK : ∀ x ∈ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ :
      Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
      x ∈ (barM M R).map (MulAut.conj c).toMonoidHom := fun x hx =>
    mem_map_conj_iff'.mpr (hconj x hx)
  have hy₁K := hyK y₁ (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁))
  have hy₂K := hyK y₂ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂))
  have hK : IsElemAbelian 3 ((barM M R).map (MulAut.conj c).toMonoidHom) :=
    isElemAbelian_map_conj' (CFSG.AGLEmbedding.isElemAbelian_barM hRel)
  have hK9 : Nat.card ((barM M R).map (MulAut.conj c).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact (card_barM_of_isPGroup_three hpr.isPGroup_R hpr.le_M).trans hR9
  have hsub : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤ H := fun x hx => hx.1.1
  have hNK0 : barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) ≤
      Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM_of_le (fun x hx => hx.2)
  have hNK := map_conj_le_normalizer' (h := c) hNK0
  have htrb : TransitiveOnNonidentity (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)))
      (barM M R) := transitive_barM (M := M) htr
  have htrb' := transitive_map_conj' (h := c) htrb
  have hperm : ∀ n ∈ (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))).map
      (MulAut.conj c).toMonoidHom,
      (barM M L₁).map (MulAut.conj n).toMonoidHom = barM M L₁ ∨
        (barM M L₁).map (MulAut.conj n).toMonoidHom = barM M L₂ := by
    intro n hn
    have h1 : c⁻¹ * n * c ∈ barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) :=
      mem_map_conj_iff'.mp hn
    have h2 : c⁻¹ * n * c ∈ barM M H := (barM_mono (M := M) hsub) h1
    have h3 : n ∈ barM M H := by
      have e : n = c * (c⁻¹ * n * c) * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcX h2) (Subgroup.inv_mem _ hcX)
    exact barM_perm_of_blocks hL₁ hk2 hH h3
  exact false_of_line_pair hK hK9 hNK htrb' hperm hy₁K hy₁Λ hy₁1 hy₂K hy₂notΛ₁ hy₂K hy₂Λ hy₂1
    hy₁K hy₁notΛ₂

theorem oddTwoImageKill_proved : OddTwoImageKill := by
  intro G _ _ P M A H R hctx hRel hR9 htr L₁ L₂ hL₁ hL₂ hne hk2 hy₁ hy₂
  exact PairStrongCtx.false_of_twoImages_of_transitive hctx hRel hR9 htr hL₁ hL₂ hne hk2 hy₁ hy₂

end CFSG.AGLEmbeddingD2.McLaughlin

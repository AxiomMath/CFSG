module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67a
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPCtx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem kl_pgroup_zpowers {x : G} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have hd : orderOf x ∣ 2 ^ 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hx)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)

theorem kl_mem_B_or {B : Subgroup G} {t' : G} (ht2 : t' * t' = 1)
    (hcomm : ∀ b ∈ B, b * t' = t' * b) {x : G} (hx : x ∈ B ⊔ zpowers t') :
    x ∈ B ∨ x * t' ∈ B := by
  obtain ⟨b, hb, i, rfl⟩ := (mem_sup_zpowers_iff_of_commute hcomm).1 hx
  rcases sec10D_eq_one_or_of_mem_zpowers ht2 (Subgroup.zpow_mem_zpowers t' i) with h | h
  · left
    rw [h, mul_one]
    exact hb
  · right
    rw [h]
    have e : b * t' * t' = b := by rw [mul_assoc, ht2, mul_one]
    rw [e]
    exact hb

theorem kl_mem_normalizer_zpowers {n t' : G} (h : n ∈ centralizer ({t'} : Set G)) :
    n ∈ normalizer (zpowers t' : Set G) := by
  refine sec10C_mem_normalizer_of_comm fun x hx => ?_
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_left
    (show Commute t' n from (Subgroup.mem_centralizer_singleton_iff.mp h).symm) i).eq

theorem kl_inn_le [Finite G] (hb5 : Asc82FactB5) {L' B : Subgroup G} {t' : G} (hL' : IsPSp43 L')
    (hLC : L' ⊓ centralizer (L' : Set G) = ⊥) (ht2 : orderOf t' = 2) (ht'L : t' ∉ L')
    (hL't : L' ≤ centralizer ({t'} : Set G)) (hBE : CFSG.Open.IsElemAbelian 2 B)
    (hB16 : Nat.card B = 16) (hBt : B ≤ centralizer ({t'} : Set G)) (ht'B : t' ∉ B)
    (htwo : ∀ w ∈ centralizer ({t'} : Set G), w ∈ centralizer (L' : Set G) →
      IsPGroup 2 (zpowers w) → w ∈ zpowers t')
    (hinner : ∀ b ∈ B, InnerOn L' b)
    (h1010 : ∀ n ∈ normalizer ((B ⊔ zpowers t' : Subgroup G) : Set G), ∀ b ∈ B,
      n * b * n⁻¹ ∈ B) :
    B ≤ L' ∧ ∃ φ' : (Fin 5 → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ' B (L' ⊓ normalizer (B : Set G)) (alternatingGroup (Fin 5)) ∧
      (∀ v, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L' (φ' v)) ∧
      (∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L' (φ' v)) := by
  classical
  have htt : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [ht2, pow_two] at this
  have hcomm : ∀ b ∈ B, b * t' = t' * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hBt hb)
  have hdec : ∀ b ∈ B, ∃ l ∈ L', ∃ c ∈ zpowers t', b = l * c := by
    intro b hb
    obtain ⟨l, hl, c, hcC, hbl⟩ := innerOn_decompose (hinner b hb)
    have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcC l hl
    have hct : c ∈ centralizer ({t'} : Set G) := by
      have e : c = l⁻¹ * b := by rw [hbl]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL't hl)) (hBt hb)
    have hbb : b * b = 1 := hBE.mul_self_eq_one hb
    have h1 : l * l * (c * c) = 1 := by
      calc l * l * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hlc]
        _ = (l * c) * (l * c) := by group
        _ = b * b := by rw [hbl]
        _ = 1 := hbb
    have hll : l * l = 1 := by
      have hmem : l * l ∈ L' ⊓ centralizer (L' : Set G) := by
        refine ⟨Subgroup.mul_mem _ hl hl, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hcC hcC)
      rw [hLC] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hcc : c * c = 1 := by
      rw [hll, one_mul] at h1
      exact h1
    exact ⟨l, hl, c, htwo c hct hcC (kl_pgroup_zpowers hcc), hbl⟩
  obtain ⟨hAE, hAcard⟩ := sec67_card_sup_zpowers hBE ht2 ht'B hcomm
  obtain ⟨Bb, hBbdef⟩ : ∃ Bb : Subgroup G, Bb = (B ⊔ zpowers t') ⊓ L' := ⟨_, rfl⟩
  have hBbA : Bb ≤ B ⊔ zpowers t' := by rw [hBbdef]; exact inf_le_left
  have hBbL : Bb ≤ L' := by rw [hBbdef]; exact inf_le_right
  have hBbE : CFSG.Open.IsElemAbelian 2 Bb := hAE.mono hBbA
  have hdecBb : ∀ b ∈ B, ∃ l ∈ Bb, ∃ c ∈ zpowers t', b = l * c := by
    intro b hb
    obtain ⟨l, hl, c, hcz, hbl⟩ := hdec b hb
    refine ⟨l, ?_, c, hcz, hbl⟩
    have e : l = b * c⁻¹ := by rw [hbl]; group
    have hlA : l ∈ B ⊔ zpowers t' := by
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hcz))
    rw [hBbdef]
    exact ⟨hlA, hl⟩
  have hAeq : B ⊔ zpowers t' = Bb ⊔ zpowers t' := by
    refine le_antisymm (sup_le (fun b hb => ?_) le_sup_right) (sup_le hBbA le_sup_right)
    obtain ⟨l, hl, c, hcz, rfl⟩ := hdecBb b hb
    exact Subgroup.mul_mem_sup hl hcz
  have ht'Bb : t' ∉ Bb := fun h => ht'L (hBbL h)
  have hcommBb : ∀ e ∈ Bb, e * t' = t' * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hL't (hBbL he))
  obtain ⟨-, hAcard'⟩ := sec67_card_sup_zpowers hBbE ht2 ht'Bb hcommBb
  have hcardBb : Nat.card Bb = 16 := by
    rw [← hAeq, hAcard, hB16] at hAcard'
    omega
  obtain ⟨Q, hQ, hBbQ⟩ := exists_isSylow2Of_ge hBbE.isPGroup hBbL
  obtain ⟨B'', -, -, huniq, -, φ', hperm, h4, h2, -⟩ := hb5 G L' hL' Q hQ
  have hBbeq : Bb = B'' := huniq Bb hBbQ hBbE.1 (by rw [hcardBb]; norm_num)
  rw [← hBbeq] at hperm
  obtain ⟨hadd, hinj, himg, hact, hsurj⟩ := hperm
  have hmemBb : ∀ v, IsEvenVec v → φ' v ∈ Bb := fun v hv => (himg _).2 ⟨v, hv, rfl⟩
  have hall : ∀ v, IsEvenVec v → φ' v ∈ B := by
    refine kl_no_hyperplane (fun v => φ' v ∈ B) ?_ ?_ ?_
    · intro v w hv hw hpv hpw
      show φ' (v + w) ∈ B
      rw [hadd v w hv hw]
      exact Subgroup.mul_mem _ hpv hpw
    · intro v w hv hw hpv hpw
      have hv' := kl_mem_B_or htt hcomm (hBbA (hmemBb v hv))
      have hw' := kl_mem_B_or htt hcomm (hBbA (hmemBb w hw))
      have hvt : φ' v * t' ∈ B := hv'.resolve_left hpv
      have hwt : φ' w * t' ∈ B := hw'.resolve_left hpw
      have hcw : t' * φ' w = φ' w * t' :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hL't (hBbL (hmemBb w hw)))).symm
      have e : φ' (v + w) = (φ' v * t') * (φ' w * t') := by
        rw [hadd v w hv hw]
        calc φ' v * φ' w = φ' v * φ' w * (t' * t') := by rw [htt, mul_one]
          _ = φ' v * (φ' w * t') * t' := by group
          _ = φ' v * (t' * φ' w) * t' := by rw [hcw]
          _ = (φ' v * t') * (φ' w * t') := by group
      show φ' (v + w) ∈ B
      rw [e]
      exact Subgroup.mul_mem _ hvt hwt
    · intro σ hσ v hv hpv
      obtain ⟨n, hn, hnact⟩ := hsurj σ hσ
      have hnA : n ∈ normalizer ((B ⊔ zpowers t' : Subgroup G) : Set G) := by
        rw [hAeq]
        exact kl_mem_normalizer_sup hn.2 (kl_mem_normalizer_zpowers (hL't hn.1))
      have := h1010 n hnA (φ' v) hpv
      rw [hnact v hv] at this
      exact this
  have hBbB : Bb ≤ B := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := (himg x).1 hx
    exact hall v hv
  have hBBb : B ≤ Bb := by
    intro b hb
    obtain ⟨l, hl, c, hcz, hbl⟩ := hdecBb b hb
    have hcB : c ∈ B := by
      have e : c = l⁻¹ * b := by rw [hbl]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBbB hl)) hb
    rcases sec10D_eq_one_or_of_mem_zpowers htt hcz with h1 | h1
    · rw [hbl, h1, mul_one]
      exact hl
    · exact absurd (h1 ▸ hcB) ht'B
  have hBeq : B = Bb := le_antisymm hBBb hBbB
  refine ⟨hBBb.trans hBbL, φ', ?_, h4, h2⟩
  rw [hBeq]
  exact ⟨hadd, hinj, himg, hact, hsurj⟩

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec12_normalizer_commutator {Y1 Y2 : Subgroup G} {g : G}
    (h1 : g ∈ normalizer (Y1 : Set G)) (h2 : g ∈ normalizer (Y2 : Set G)) :
    g ∈ normalizer ((⁅Y1, Y2⁆ : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (Y1 : Set G) → g ∈ normalizer (Y2 : Set G) →
      ∀ x ∈ ⁅Y1, Y2⁆, g * x * g⁻¹ ∈ ⁅Y1, Y2⁆ := by
    intro g hg1 hg2 x hx
    have hmap : (⁅Y1, Y2⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅Y1, Y2⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg1 y).mp hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg2 y).mp hy
    simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem _ hx)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h1 h2 x, fun hx => ?_⟩
  have hinv1 : g⁻¹ ∈ normalizer (Y1 : Set G) := (normalizer (Y1 : Set G)).inv_mem h1
  have hinv2 : g⁻¹ ∈ normalizer (Y2 : Set G) := (normalizer (Y2 : Set G)).inv_mem h2
  have h := key hinv1 hinv2 _ hx
  have h' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h'] at h

theorem sec12_S_le_secN (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E : Subgroup G} [Finite G] (hctx : Sec12Ctx G t L S z K1 K2 E) :
    S ≤ secN (secV t S L E) := by
  intro s hs
  have hsM : s ∈ secM t S L :=
    hp.r10.l109 G t L S z K1 K2 hctx.toSec10Ctx (Subgroup.le_normalizer hs)
  have hsL : s ∈ normalizer (L : Set G) := (hp.basic G t L S z hctx.toSec10Z).2.2.2.2.1 hs
  have hsM' : s ∈ normalizer ((secM t S L : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hsM
  have hsML : s ∈ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hsM' hsL ⊢
    intro x
    simp only [Subgroup.mem_inf, hsM' x, hsL x]
  exact sec12_normalizer_commutator (hctx.S_norm hs) hsML

theorem sec12_relIndex_inf_eq_two {P M M₀ : Subgroup G} (hPM : P ≤ M) (hM₀ : M₀ ≤ M)
    (hidx : M₀.relIndex M = 2) {t : G} (htP : t ∈ P) (htM₀ : t ∉ M₀) :
    (P ⊓ M₀).relIndex P = 2 := by
  have htM : t ∈ M := hPM htP
  have hidx2 : (M₀.subgroupOf M).index = 2 := hidx
  have hxor : ∀ b ∈ P, Xor (b * t ∈ M₀) (b ∈ M₀) := by
    intro b hbP
    have hbM : b ∈ M := hPM hbP
    have hiff : (b * t ∈ M₀) ↔ (b ∈ M₀ ↔ t ∈ M₀) :=
      Subgroup.mul_mem_iff_of_index_two (H := M₀.subgroupOf M) hidx2
        (a := (⟨b, hbM⟩ : ↥M)) (b := (⟨t, htM⟩ : ↥M))
    rw [hiff]
    by_cases hb : b ∈ M₀ <;> simp [htM₀, hb, Xor]
  have h2 : M₀.relIndex P = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    exact ⟨t, htP, hxor⟩
  rw [inf_comm P M₀, Subgroup.inf_relIndex_right]
  exact h2

theorem sec12_oTwoRes_le_of_squares {N : Subgroup G} (hsq : ∀ x : G, x ^ 2 ∈ N) :
    oTwoRes (⊤ : Subgroup G) ≤ N := by
  change Subgroup.closure {a : G | a ∈ (⊤ : Subgroup G) ∧ Odd (orderOf a)} ≤ N
  rw [Subgroup.closure_le]
  rintro x ⟨-, m, hm⟩
  have hx1 : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
  have hx : x = (x ^ (m + 1)) ^ 2 := by
    rw [← pow_mul]
    calc x = x ^ (2 * m + 1) * x := by rw [hx1, one_mul]
      _ = x ^ ((m + 1) * 2) := by rw [← pow_succ]; congr 1; ring
  rw [hx]
  exact hsq _

theorem asc82Lemma1210_of (hp : Asc82Pre11) (h126 : Asc82Lemma126) (h129 : Asc82Lemma129)
    (hN : Asc82Step1210N) : Asc82Lemma1210 := by
  intro G _ _ t L S z K1 K2 E hctx
  obtain ⟨N0, hN0le, hN0n, hN0idx, htN0⟩ := hN G t L S z K1 K2 E hctx
  obtain ⟨R0, hR0syl, hSR0⟩ :=
    exists_isSylow2Of_ge hctx.sylow.2.1 (sec12_S_le_secN hp hctx)
  obtain ⟨-, hR0G⟩ := h129 G t L S z K1 K2 E hctx R0 hSR0 hR0syl
  have htS : t ∈ S := (hp.basic G t L S z hctx.toSec10Z).2.2.2.1
  have htR0 : t ∈ R0 := hSR0 htS
  have hR0N : R0 ≤ secN (secV t S L E) := hR0syl.1
  have hQidx : (R0 ⊓ N0).relIndex R0 = 2 :=
    sec12_relIndex_inf_eq_two hR0N hN0le hN0idx htR0 htN0
  have hQu : ∀ x ∈ (⊤ : Subgroup G), x⁻¹ * t * x ∉ R0 ⊓ N0 := by
    intro x _ hx
    obtain ⟨hxR0, hxN0⟩ := hx
    obtain ⟨-, n, hn, hn_eq⟩ := h126 G t L S z K1 K2 E hctx x (hR0N hxR0)
    have hconj : n * (x⁻¹ * t * x) * n⁻¹ ∈ N0 := by
      simpa using (Subgroup.normal_subgroupOf_iff hN0le).mp hN0n (x⁻¹ * t * x) n hxN0 hn
    have ht_eq : n * (x⁻¹ * t * x) * n⁻¹ = t := by rw [← hn_eq]; group
    exact htN0 (ht_eq ▸ hconj)
  have ht2 : orderOf t = 2 := hctx.involution
  obtain ⟨N, -, -, hsq, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
    (X := ⊤) (P := R0) (Q := R0 ⊓ N0) le_top hR0G.2.1 hR0G.2.2 inf_le_left hQidx
    (Subgroup.mem_top t) ht2 hQu
  intro htO
  exact htN (sec12_oTwoRes_le_of_squares (fun x => hsq x (Subgroup.mem_top x)) htO)

end CFSG.OddStandard.SmallF3.Omega

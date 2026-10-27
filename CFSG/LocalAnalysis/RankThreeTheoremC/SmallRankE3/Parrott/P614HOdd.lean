module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HRad
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (pElementSubgroup pElementSubgroup_le)

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

theorem exists_conj_le_of_maximal {p : ℕ} [Fact p.Prime] {Y S T₀ : Subgroup G} (hSY : S ≤ Y)
    (hS : IsPGroup p S)
    (hmax : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup p Q → S ≤ Q → Q = S) (hT₀Y : T₀ ≤ Y)
    (hT₀ : IsPGroup p T₀) : ∃ g ∈ Y, ∀ t ∈ T₀, g⁻¹ * t * g ∈ S := by
  let S' : Sylow p Y :=
    { toSubgroup := S.subgroupOf Y
      isPGroup' := hS.comap_subtype
      is_maximal' := fun {Q} hQ hSQ => by
        have hle : S ≤ Q.map Y.subtype := fun s hs => ⟨⟨s, hSY hs⟩, hSQ hs, rfl⟩
        have h := hmax (Q.map Y.subtype) (map_subtype_le Q) (hQ.map _) hle
        rw [← h]
        exact (comap_map_eq_self_of_injective Y.subtype_injective Q).symm }
  obtain ⟨P', hP'⟩ := (hT₀.comap_subtype (K := Y)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S' P'
  refine ⟨g, g.2, fun t ht => ?_⟩
  have hmem : (⟨t, hT₀Y ht⟩ : Y) ∈ ((g • S' : Sylow p Y) : Subgroup Y) := by
    rw [hg]
    exact hP' ht
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have h2 : (g⁻¹ * ⟨t, hT₀Y ht⟩ * g : Y) ∈ (S' : Subgroup Y) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmem
  have h3 : ((g⁻¹ * ⟨t, hT₀Y ht⟩ * g : Y) : G) ∈ S := h2
  simpa using h3

theorem mem_normalizer_inf_kPar {g : G}
    (hg : g ∈ normalizer (K : Set G) ⊓ normalizer (pCoreOf 2 H : Set G) ⊓
      normalizer (S : Set G)) : g ∈ normalizer ((K ⊓ kPar H S K : Subgroup G) : Set G) := by
  obtain ⟨⟨hK, hO⟩, hS⟩ := hg
  have h1 : g ∈ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_sup K (pCoreOf 2 H) ⟨hK, hO⟩
  have h2 : g ∈ normalizer (kRad H S K : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hS, h1⟩
  have h3 : g ∈ normalizer (kPar H S K : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨h1, le_normalizer h2⟩
  exact inf_normalizer_le_normalizer_inf ⟨hK, h3⟩

theorem mem_normalizer_pElementSubgroup {g : G}
    (hg : g ∈ normalizer (K : Set G) ⊓ normalizer (pCoreOf 2 H : Set G) ⊓
      normalizer (S : Set G)) :
    g ∈ normalizer (pElementSubgroup 2 (K ⊓ kPar H S K) : Set G) := by
  have key : ∀ c : G, c ∈ normalizer ((K ⊓ kPar H S K : Subgroup G) : Set G) →
      ∀ y ∈ {y : G | y ∈ K ⊓ kPar H S K ∧ ∃ k : ℕ, orderOf y = 2 ^ k},
        c * y * c⁻¹ ∈ {y : G | y ∈ K ⊓ kPar H S K ∧ ∃ k : ℕ, orderOf y = 2 ^ k} := by
    rintro c hc y ⟨hy, k, hk⟩
    refine ⟨(mem_normalizer_iff.mp hc y).mp hy, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  have h1 := mem_normalizer_inf_kPar hg
  have h2 := mem_normalizer_inf_kPar (inv_mem hg)
  exact mem_normalizer_closure (key g h1) (by simpa using key g⁻¹ h2)

theorem le_pElementSubgroup_sup (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    {T₀ : Subgroup G} (hT₀ : T₀ ≤ kPar H S K) (hT₀2 : IsPGroup 2 T₀) :
    T₀ ≤ pElementSubgroup 2 (K ⊓ kPar H S K) ⊔ pCoreOf 2 H := by
  intro t ht
  have hO := pCoreOf_le_kPar (K := K) hyp
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup h618 (kPar_le_sup (hT₀ ht))
  have hkP : k ∈ kPar H S K := by
    have h := mul_mem (hT₀ ht) (inv_mem (hO ho))
    rwa [mul_inv_cancel_right] at h
  obtain ⟨n, hn⟩ := hT₀2 ⟨k * o, ht⟩
  have htn : (k * o) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have htN : k * o ∈ normalizer (pCoreOf 2 H : Set G) :=
    sup_le_normalizer_pCoreOf h618 (kPar_le_sup (hT₀ ht))
  obtain ⟨o', ho', h1⟩ := exists_mul_pow_eq htN (inv_mem ho) (2 ^ n)
  rw [mul_inv_cancel_right, htn, one_mul] at h1
  obtain ⟨j, hj⟩ := exists_orderOf_eq_two_pow (isPGroup_pCoreOf 2 H) (h1 ▸ ho')
  have hkX : k ∈ pElementSubgroup 2 (K ⊓ kPar H S K) := subset_closure ⟨⟨hk, hkP⟩, j, hj⟩
  exact mul_mem (mem_sup_left hkX) (mem_sup_right ho)

theorem not_dvd_card_pElementSubgroup (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (h3 : ¬ 3 ∣ Nat.card
      (pElementSubgroup 2 (normalizer (bar K (kRad H S K) : Set (Kbar K))))) :
    ¬ 3 ∣ Nat.card (pElementSubgroup 2 (K ⊓ kPar H S K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := pElementSubgroup 2 (K ⊓ kPar H S K) with hXdef
  set P₂ := pElementSubgroup 2 (normalizer (bar K (kRad H S K) : Set (Kbar K))) with hP₂def
  have hXK : X ≤ K := (pElementSubgroup_le _).trans inf_le_left
  have hmap : (X.subgroupOf K).map (kbarMk K) ≤ P₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyX : (y : G) ∈ X := hy
    have hle : X ≤ (P₂.comap (kbarMk K)).map K.subtype := by
      rw [hXdef, pElementSubgroup, closure_le]
      rintro w ⟨⟨hwK, hwP⟩, k, hk⟩
      refine ⟨⟨w, hwK⟩, subset_closure ⟨?_, ?_⟩, rfl⟩
      · exact (mk_mem_normalizer_bar_kRad_iff hyp h618 ⟨w, hwK⟩).2 hwP
      · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          ((orderOf_map_dvd (kbarMk K) ⟨w, hwK⟩).trans
            (by rw [Subgroup.orderOf_mk, hk]))
        exact ⟨j, hj⟩
    obtain ⟨y', hy', hyy'⟩ := hle hyX
    rw [show y = y' from Subtype.ext hyy'.symm]
    exact hy'
  have hcard : Nat.card X = Nat.card ((X.subgroupOf K).map (kbarMk K)) *
      Nat.card ((kbarMk K).ker ⊓ X.subgroupOf K : Subgroup K) := by
    rw [← relIndex_ker, relIndex_mul_card, Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv]
  have hker : ¬ 3 ∣ Nat.card ((kbarMk K).ker ⊓ X.subgroupOf K : Subgroup K) := by
    intro h
    have h1 : Nat.card ((kbarMk K).ker ⊓ X.subgroupOf K : Subgroup K) ∣
        Nat.card (CFSG.pPrimeCore 3 K) := by
      have hk : (kbarMk K).ker = CFSG.pPrimeCore 3 K := QuotientGroup.ker_mk' _
      exact card_dvd_of_le (inf_le_left.trans hk.le)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := K)) (h.trans h1)
  rw [hcard]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h' | h'
  · exact h3 (h'.trans (card_dvd_of_le hmap))
  · exact hker h'

theorem three_dvd_card_pElementSubgroup (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (hL : LieCase M H S K x z) :
    3 ∣ Nat.card (pElementSubgroup 2 (normalizer (bar K (kRad H S K) : Set (Kbar K)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h3
  have hX := not_dvd_card_pElementSubgroup hyp h618 h3
  set X := pElementSubgroup 2 (K ⊓ kPar H S K) with hXdef
  have hSH : S ≤ H := S_le hyp
  have hS2 : IsPGroup 2 S := hyp.optimal.maxInv.1.2.1
  have hBS : zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) := hyp.optimal.maxInv.1.2.2
  have hBH : zpowers x ⊔ zpowers z ≤ H := hyp.optimal.ext.pair.le
  have hHN : H ≤ normalizer (K : Set G) ⊓ normalizer (pCoreOf 2 H : Set G) :=
    le_inf h618.comp.normal (le_normalizer_pCoreOf 2 H)
  have hSX : S ≤ normalizer (X : Set G) := fun s hs =>
    mem_normalizer_pElementSubgroup ⟨hHN (hSH hs), le_normalizer hs⟩
  have hBX : zpowers x ⊔ zpowers z ≤ normalizer (X : Set G) := fun b hb =>
    mem_normalizer_pElementSubgroup ⟨hHN (hBH hb), hBS hb⟩
  have hY : ¬ 3 ∣ Nat.card (X ⊔ S : Subgroup G) := by
    intro h
    have h1 := h.trans (card_sup_dvd_of_le_normalizer hSX)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h' | h'
    · exact hX h'
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_three_of_isPGroup_two hS2) h'
  have hBY : zpowers x ⊔ zpowers z ≤ normalizer ((X ⊔ S : Subgroup G) : Set G) :=
    fun b hb => inf_normalizer_le_normalizer_sup X S ⟨hBX hb, hBS hb⟩
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (SmallRankPlane.of_situation hyp.setting hyp.situation hyp.point
      hyp.central).card_eq
  have hYH : X ⊔ S ≤ H :=
    sup_le ((pElementSubgroup_le _).trans (inf_le_left.trans h618.comp.le)) hSH
  obtain ⟨T, hT, hST, hBT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hY hBY le_sup_right hS2 hBS
  have hTS : T = S := hyp.optimal.maxInv.2 T ⟨hT.1.trans hYH, hT.2.1, hBT⟩ hST
  have hmax : ∀ Q : Subgroup G, Q ≤ X ⊔ S → IsPGroup 2 Q → S ≤ Q → Q = S := by
    intro Q hQ hQ2 hSQ
    rw [← hTS]
    exact hT.2.2 Q hQ hQ2 (hTS ▸ hSQ)
  obtain ⟨T₀, hT₀, hT₀2, hT₀odd⟩ := hL.par_sylow
  have hT₀Y : T₀ ≤ X ⊔ S :=
    (le_pElementSubgroup_sup hyp h618 hT₀ hT₀2).trans
      (sup_le le_sup_left (hyp.optimal.core_le.trans le_sup_right))
  obtain ⟨g, hgY, hg⟩ := exists_conj_le_of_maximal le_sup_right hS2 hmax hT₀Y hT₀2
  have hgH : g ∈ H := hYH hgY
  have hgN : g⁻¹ ∈ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_sup K (pCoreOf 2 H) (hHN (inv_mem hgH))
  have hconj : T₀.map (MulAut.conj g⁻¹).toMonoidHom ≤ kRad H S K := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := hg t ht
      simpa using h
    · have h := (mem_normalizer_iff.mp hgN t).mp (kPar_le_sup (hT₀ ht))
      simpa using h
  have hdvd : Nat.card T₀ ∣ Nat.card (kRad H S K) := by
    rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
      (K := T₀)]
    exact card_dvd_of_le hconj
  have hc1 := relIndex_mul_card T₀ (K ⊔ pCoreOf 2 H)
  have hc2 := relIndex_mul_card (kRad H S K) (K ⊔ pCoreOf 2 H)
  rw [inf_eq_left.mpr (hT₀.trans kPar_le_sup)] at hc1
  rw [inf_eq_left.mpr kRad_le_sup] at hc2
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  have hkey : (kRad H S K).relIndex (K ⊔ pCoreOf 2 H) * m = T₀.relIndex (K ⊔ pCoreOf 2 H) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hc1, mul_assoc, mul_comm m, ← hm, hc2]
  have h1 : 2 ∣ (kRad H S K).relIndex (K ⊔ pCoreOf 2 H) * m :=
    dvd_mul_of_dvd_left hL.rad_not_sylow m
  rw [hkey] at h1
  exact hT₀odd h1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

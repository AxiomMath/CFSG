module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneC
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique CFSG.Open Subgroup

theorem charTwo_of_normalized_two_subgroup {M : Type*} [Group M] {D S : Subgroup M}
    (hM : CharTwo (⊤ : Subgroup M)) (hSD : S ≤ D) (hS2 : IsPGroup 2 S)
    (hSn : ∀ d ∈ D, ∀ s ∈ S, d * s * d⁻¹ ∈ S) (hO : pCoreOf 2 (⊤ : Subgroup M) ≤ S) :
    CharTwo D := by
  have hSP : S ≤ pCoreOf 2 D := by
    have hnorm : (S.subgroupOf D).Normal := ⟨fun n hn g => hSn g g.2 n hn⟩
    have hle : S.subgroupOf D ≤ CFSG.pCore 2 D := le_sSup ⟨hnorm, hS2.comap_subtype⟩
    calc S = (S.subgroupOf D).map D.subtype := (map_subgroupOf_eq_of_le hSD).symm
      _ ≤ pCoreOf 2 D := map_mono hle
  intro x hx
  have hxc : x ∈ centralizer (pCoreOf 2 (⊤ : Subgroup M) : Set M) :=
    centralizer_le (fun y hy => hSP (hO hy)) hx.2
  exact hSP (hO (hM ⟨mem_top x, hxc⟩))

theorem exists_threePrime_overgroup {M : Type*} [Group M] [Finite M] {T W A : Subgroup M}
    [W.Normal] [A.Normal] (hM : CharTwo (⊤ : Subgroup M)) (hT : IsSylowTwoOf T ⊤)
    (hWA : W ≤ A) (hOW : pCoreOf 2 (⊤ : Subgroup M) ≤ W) (h3 : ¬ 3 ∣ W.relIndex A) :
    ∃ D : Subgroup M, T ≤ D ∧ ¬ 3 ∣ Nat.card D ∧ CharTwo D ∧ A ≤ D ⊔ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hTi'⟩ := hT
  have hTi : ¬ 2 ∣ T.index := by
    rw [← relIndex_top_right]
    exact hTi'
  set S : Subgroup M := T ⊓ W with hSdef
  have hS2 : IsPGroup 2 S := hT2.to_inf_left
  have hSW : S ≤ W := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hSodd : ¬ 2 ∣ S.relIndex W := not_dvd_relIndex_inf_normal hTi
  have hfr : normalizer (S : Set M) ⊔ W = ⊤ := normalizer_sup_eq_top_of_sylow hSW hS2 hSodd
  set AT : Subgroup M := A ⊔ T with hATdef
  have hAAT : A ≤ AT := le_sup_left
  have hTAT : T ≤ AT := le_sup_right
  set B : Subgroup M := AT ⊓ normalizer (S : Set M) with hBdef
  have hBAT : B ≤ AT := inf_le_left
  have hBN : B ≤ normalizer (S : Set M) := inf_le_right
  have hATB : AT ≤ B ⊔ W := by
    intro x hx
    have hx' : x ∈ (↑(normalizer (S : Set M) ⊔ W) : Set M) := by
      rw [hfr]
      exact mem_top x
    rw [Subgroup.mul_normal] at hx'
    obtain ⟨b, hb, w, hw, rfl⟩ := hx'
    have hbAT : b ∈ AT := by
      have : b * w * w⁻¹ ∈ AT := AT.mul_mem hx (AT.inv_mem (hAAT (hWA hw)))
      simpa using this
    exact mul_mem_sup ⟨hbAT, hb⟩ hw
  have hWB : W ⊔ B = AT :=
    le_antisymm (sup_le (hWA.trans hAAT) hBAT) (hATB.trans (le_of_eq (sup_comm _ _)))
  have hSB : S ≤ W ⊓ B := le_inf hSW (le_inf (hST.trans hTAT) le_normalizer)
  have hSn : ∀ k ∈ B, ∀ s ∈ S, k * s * k⁻¹ ∈ S := fun k hk s hs =>
    (mem_set_normalizer_iff.1 (hBN hk) s).1 hs
  have hBn : ∀ k ∈ B, ∀ b ∈ W ⊓ B, k * b * k⁻¹ ∈ W ⊓ B := fun k hk b hb =>
    ⟨Normal.conj_mem inferInstance b hb.1 k, B.mul_mem (B.mul_mem hk hb.2) (B.inv_mem hk)⟩
  have hSdvd : ¬ 2 ∣ S.relIndex (W ⊓ B) := fun h =>
    hSodd (h.trans (Dvd.intro _ (relIndex_mul_relIndex S (W ⊓ B) W hSB inf_le_left)))
  have h3B : ¬ 3 ∣ (W ⊓ B).relIndex B := by
    rw [inf_relIndex_right, ← relIndex_sup_left (K := W) (H := B), hWB,
      ← relIndex_mul_relIndex W A AT hWA hAAT]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h3 h
    · rw [relIndex_sup_left] at h
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      have hd : A.relIndex T ∣ 2 ^ k := hk ▸ relIndex_dvd_card A T
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h.trans hd)) (by norm_num)
  obtain ⟨D₂, hSD₂, hD₂B, hD₂3, hsup, hD₂odd⟩ := exists_threePrime_cover_of_normalizes
    (K := B) (S := S) (B₀ := W ⊓ B) hSB inf_le_right hSn hBn hS2 hSdvd h3B
  have hBodd : ¬ 2 ∣ B.index := by
    rw [← relIndex_mul_index hBAT]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · have e : B.relIndex (W ⊔ B) = (W ⊓ B).relIndex W := relIndex_sup_left_of_normal W B
      rw [← hWB, e] at h
      exact hSodd (h.trans (relIndex_dvd_of_le_left W hSB))
    · exact hTi (h.trans (index_dvd_of_le hTAT))
  have hD₂idx : ¬ 2 ∣ D₂.index := by
    rw [← relIndex_mul_index hD₂B]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact hD₂odd h
    · exact hBodd h
  obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index hT2 hTi hD₂idx
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hmapmem : ∀ (X : Subgroup M) (x : M),
      x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
    intro X x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro h
      exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine ⟨D₂.map (MulAut.conj g).toMonoidHom, fun x hx => (hmapmem D₂ x).2 (hg x hx), ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (D₂.equivMapOfInjective _ hinj).toEquiv]
    exact hD₂3
  ·
    have hOe : pCoreOf 2 (⊤ : Subgroup M) = CFSG.pCore 2 M :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2
    haveI hOn : (CFSG.pCore 2 M).Normal := inferInstance
    have hOT : CFSG.pCore 2 M ≤ T := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal (hT2.toSylow hTi)
      rwa [IsPGroup.toSylow_coe] at this
    refine charTwo_of_normalized_two_subgroup hM (S := S.map (MulAut.conj g).toMonoidHom)
      (map_mono hSD₂) (hS2.map _) ?_ ?_
    · intro d hd s hs
      rw [hmapmem] at hd hs ⊢
      have e : g⁻¹ * (d * s * d⁻¹) * g = (g⁻¹ * d * g) * (g⁻¹ * s * g) * (g⁻¹ * d * g)⁻¹ := by
        group
      rw [e]
      exact hSn _ (hD₂B hd) _ hs
    · intro x hx
      rw [hmapmem]
      have hx' : x ∈ CFSG.pCore 2 M := by rwa [hOe] at hx
      have h1 : g⁻¹ * x * g ∈ CFSG.pCore 2 M := by
        simpa using hOn.conj_mem x hx' g⁻¹
      exact ⟨hOT h1, hOW (by rwa [hOe])⟩
  · intro a ha
    have hgA : g⁻¹ * a * g ∈ A := by simpa using Normal.conj_mem inferInstance a ha g⁻¹
    have hBD : B ≤ D₂ ⊔ W := by
      calc B = (W ⊓ B) ⊔ D₂ := hsup.symm
        _ ≤ D₂ ⊔ W := sup_le (inf_le_left.trans le_sup_right) le_sup_left
    have h1 : g⁻¹ * a * g ∈ (↑(D₂ ⊔ W) : Set M) :=
      sup_le hBD le_sup_right (hATB (hAAT hgA))
    rw [Subgroup.mul_normal] at h1
    obtain ⟨y, hy, w, hw, hyw⟩ := h1
    have hyw' : y * w = g⁻¹ * a * g := hyw
    have ha' : a = (g * y * g⁻¹) * (g * w * g⁻¹) := by
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = g * (y * w) * g⁻¹ := by rw [hyw']
        _ = (g * y * g⁻¹) * (g * w * g⁻¹) := by group
    rw [ha']
    exact mul_mem_sup ((hmapmem D₂ _).2 (by simpa [mul_assoc] using hy))
      (Normal.conj_mem inferInstance w hw g)

end CFSG.LocalAnalysis.RankThreeUC.S15

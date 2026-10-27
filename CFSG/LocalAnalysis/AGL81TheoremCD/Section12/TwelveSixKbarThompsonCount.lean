module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Gen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem map_conj_eq_self {B : Subgroup Y} {k : Y} (hk : k ∈ B) :
    B.map (MulAut.conj k).toMonoidHom = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact B.mul_mem (B.mul_mem hk hy) (B.inv_mem hk)
  · intro hx
    refine ⟨k⁻¹ * x * k, B.mul_mem (B.mul_mem (B.inv_mem hk) hx) hk, ?_⟩
    show k * (k⁻¹ * x * k) * k⁻¹ = x
    group

private theorem exists_conj_mem_of_le {P : Sylow 3 Y} {B V : Subgroup Y}
    (hPB : (P : Subgroup Y) ≤ B) (hVB : V ≤ B) (hV : IsPGroup 3 V) :
    ∃ k ∈ B, ∀ v ∈ V, k * v * k⁻¹ ∈ (P : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := (hV.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥B) S (P.subtype hPB)
  refine ⟨k, k.2, fun v hv => ?_⟩
  have h1 : MulAut.conj k ⟨v, hVB hv⟩ ∈ ((k • S : Sylow 3 ↥B) : Subgroup ↥B) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul_iff.2 (hS hv)
  rw [hk, Sylow.coe_subtype, mem_subgroupOf] at h1
  simpa [MulAut.conj_apply] using h1

theorem eq_normalizer_thompsonSubgroup (P : Sylow 3 Y) (e : ↥(P : Subgroup Y) ≃* W3)
    (hcard : Nat.card (normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y)) ∣ 648)
    (hmax : ∀ B : Subgroup Y, normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ≤ B →
      B = normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) ∨ B = ⊤)
    {B V : Subgroup Y} (hB : B ≠ ⊤) (hNB : normalizer ((P : Subgroup Y) : Set Y) ≤ B)
    (hVB : V ≤ B) (hV : IsElemAbelian 3 V) (hV27 : Nat.card V = 27)
    (h4 : 4 ∣ (B ⊓ centralizer (V : Set Y)).relIndex (B ⊓ normalizer (V : Set Y))) :
    B = normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₁ := normalizer (CFSG.Open.thompsonSubgroup (P : Subgroup Y) : Set Y) with hN₁
  have hPB : (P : Subgroup Y) ≤ B := le_normalizer.trans hNB
  have hPN₁ : normalizer ((P : Subgroup Y) : Set Y) ≤ N₁ :=
    CFSG.normalizer_le_normalizer_ambientMaxCardThompson _
  have hVp : IsPGroup 3 V := IsPGroup.of_card (n := 3) (by rw [hV27]; norm_num)
  obtain ⟨k, hkB, hk⟩ := exists_conj_mem_of_le hPB hVB hVp
  set V' := V.map (MulAut.conj k).toMonoidHom with hV'
  have hV'J : V' = CFSG.Open.thompsonSubgroup (P : Subgroup Y) := by
    rw [thompsonSubgroup_eq_baseIn e]
    refine eq_baseIn_of_comm e ?_ ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hk v hv
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : a * b = b * a := congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [← map_mul, ← map_mul, hab]
    · rw [card_map_of_injective (MulAut.conj k).injective, hV27]
  have hX : (B ⊓ normalizer (V : Set Y)).map (MulAut.conj k).toMonoidHom = B ⊓ N₁ := by
    rw [map_inf_eq _ _ _ (MulAut.conj k).injective, map_conj_eq_self hkB,
      map_equiv_normalizer_eq, ← hV', hV'J]
  have h4X : 4 ∣ Nat.card (B ⊓ N₁ : Subgroup Y) := by
    rw [← hX, card_map_of_injective (MulAut.conj k).injective]
    exact h4.trans (Subgroup.index_dvd_card _)
  have hNX : normalizer ((P : Subgroup Y) : Set Y) ≤ B ⊓ N₁ := le_inf hNB hPN₁
  have hXN₁ : B ⊓ N₁ ≤ N₁ := inf_le_right
  have hr : (B ⊓ N₁).relIndex N₁ ≡ 1 [MOD 3] := by
    have h₀ := CFSG.Sp43.index_mod_of_normalizer_le P hNX
    have h₁ := CFSG.Sp43.index_mod_of_normalizer_le P hPN₁
    have h := Nat.ModEq.mul_left ((B ⊓ N₁).relIndex N₁) h₁
    rw [mul_one, relIndex_mul_index hXN₁] at h
    exact h.symm.trans h₀
  have hcardX : Nat.card (B ⊓ N₁ : Subgroup Y) * (B ⊓ N₁).relIndex N₁ = Nat.card N₁ := by
    have h := card_mul_index ((B ⊓ N₁).subgroupOf N₁)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hXN₁).toEquiv] at h
  have h81 : 81 ∣ Nat.card (B ⊓ N₁ : Subgroup Y) := by
    rw [← card_of_equiv e]
    exact card_dvd_of_le (le_normalizer.trans hNX)
  have h324 : 324 ∣ Nat.card (B ⊓ N₁ : Subgroup Y) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 81 4) h81 h4X
  have hr2 : (B ⊓ N₁).relIndex N₁ ∣ 2 := by
    obtain ⟨c, hc⟩ := h324
    have h := hcard
    rw [← hcardX, hc, mul_assoc, show (648 : ℕ) = 324 * 2 by norm_num] at h
    have h' := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 324) h
    exact (Dvd.intro_left _ rfl).trans h'
  have hr1 : (B ⊓ N₁).relIndex N₁ = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hr2
    have hpos : 0 < (B ⊓ N₁).relIndex N₁ := Nat.pos_of_dvd_of_pos hr2 (by norm_num)
    unfold Nat.ModEq at hr
    interval_cases h : (B ⊓ N₁).relIndex N₁
    · rfl
    · norm_num at hr
  have hN₁B : N₁ ≤ B := (relIndex_eq_one.1 hr1).trans inf_le_left
  exact (hmax B hN₁B).resolve_right hB

omit [Finite Y] in
theorem normalizer_facts_of_embedding {G' : Type} [Group G'] (φ : Y →* G')
    (hφ : Function.Injective φ) {S : Subgroup Y} {U : Subgroup G'} (hSU : S.map φ = U)
    (hcard : Nat.card (normalizer (U : Set G') ⊓ φ.range : Subgroup G') ∣ 648)
    (hmax : ∀ M : Subgroup G', normalizer (U : Set G') ⊓ φ.range ≤ M → M ≤ φ.range →
      M = normalizer (U : Set G') ⊓ φ.range ∨ M = φ.range) :
    Nat.card (normalizer (S : Set Y)) ∣ 648 ∧
      ∀ B : Subgroup Y, normalizer (S : Set Y) ≤ B → B = normalizer (S : Set Y) ∨ B = ⊤ := by
  have key : (normalizer (S : Set Y)).map φ = normalizer (U : Set G') ⊓ φ.range := by
    refine le_antisymm (le_inf (hSU ▸ le_normalizer_map φ) (map_le_range φ _)) ?_
    rintro x ⟨hxN, y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have h := le_normalizer_comap (H := U) φ hxN
    rwa [← hSU, comap_map_eq_self_of_injective hφ] at h
  refine ⟨?_, fun B hB => ?_⟩
  · rw [← card_map_of_injective hφ, key]
    exact hcard
  · rcases hmax (B.map φ) (key ▸ map_mono hB) (map_le_range φ B) with h | h
    · left
      exact map_injective hφ (h.trans key.symm)
    · right
      exact map_injective hφ (h.trans (MonoidHom.range_eq_map φ))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarThompson

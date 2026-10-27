
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsConj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenterBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

namespace IsQSetting

variable {E : Type*} [Group E] [Finite E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem card_kerOmega
    (h : IsQSetting q l) (h16 : Nat.card q.ker = 16)
    {K : Subgroup E} (hK : ∀ z, z ∈ K ↔ z ∈ q.ker ∧ z * z = 1) : Nat.card K = 4 := by
  have hle : Nat.card K ≤ 4 := by
    refine le_trans (le_of_eq (Nat.card_congr ?_)) h.card_omega_ker_le
    exact Equiv.subtypeEquivRight hK
  have hge : 2 < Nat.card K := by
    by_contra hle2
    push Not at hle2
    have hcyc := isCyclic_of_card_le_two h.ker_le (fun z hz => pow_four_of_ker' h hz) hK hle2
    exact not_isCyclic_of_card h16 (fun z => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_four_of_ker' h z.2]
      rfl)) hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 K := fun k => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact ((hK _).1 k.2).2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := K)).1 hKp
  rw [hm] at hle hge ⊢
  have hm2 : m = 2 := by
    rcases Nat.lt_or_ge m 2 with h' | h'
    · interval_cases m <;> simp at hge
    · rcases Nat.lt_or_ge m 3 with h'' | h''
      · omega
      · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h''
        omega
  rw [hm2]
  rfl

theorem exists_inner_F
    (h : IsQSetting q l) (h16 : Nat.card q.ker = 16) {e₀ : E}
    (he₀ : q e₀ = 1 ∨ q e₀ = wordPerm (tg 4)) :
    ∃ F : Subgroup E, IsElemTwo F ∧ Nat.card F = 16 ∧ Nat.card ↥(F ⊓ q.ker) = 4 ∧
      ∀ f ∈ F, e₀ * f = f * e₀ := by
  obtain ⟨K, hK⟩ := exists_kerOmega h.ker_le
  have hK4 := h.card_kerOmega h16 hK
  have hKc : ∀ x, ∀ y ∈ K, x * y = y * x := fun x y hy =>
    mem_center_iff.mp (h.ker_le ((hK y).1 hy).1) x
  have hKe : IsElemTwo K := ⟨fun x _ y hy => hKc x y hy, fun z hz => ((hK z).1 hz).2⟩
  have h4sq := h.ilift_mul_self (d := (4, 1, 1, 1)) (by decide)
  have h8sq := h.ilift_mul_self (d := (8, 1, 0, 0)) (by decide)
  have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := h.q_ilift (by norm_num)
  have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := h.q_ilift (by norm_num)
  have hc48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
    h.ilift_comm (by
      rw [← map_mul, cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl, map_mul])
  have hE4K := (isElemTwo_zpowers h4sq).sup hKe fun x _ y hy => hKc x y hy
  have h8c : ∀ x ∈ zpowers (ilift l (8, 1, 0, 0)),
      ∀ y ∈ zpowers (ilift l (4, 1, 1, 1)) ⊔ K, x * y = y * x :=
    commute_sup_right (commute_zpowers_zpowers hc48.symm) fun x _ y hy => hKc x y hy
  set F := zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ K) with hF
  have hFe : IsElemTwo F := (isElemTwo_zpowers h8sq).sup hE4K h8c
  have h4n : ilift l (4, 1, 1, 1) ∉ K := fun hm => by
    have := ((hK _).1 hm).1
    rw [MonoidHom.mem_ker, hq4, ← wordPerm_tg_zero] at this
    exact absurd (tg_injective (by norm_num) (by norm_num) this) (by norm_num)
  have h8n : ilift l (8, 1, 0, 0) ∉ zpowers (ilift l (4, 1, 1, 1)) ⊔ K := fun hm => by
    have hle : zpowers (ilift l (4, 1, 1, 1)) ⊔ K ≤ (zpowers (wordPerm (tg 4))).comap q :=
      sup_le (zpowers_le.2 (by rw [mem_comap, hq4]; exact mem_zpowers _)) fun z hz => by
        rw [mem_comap, MonoidHom.mem_ker.mp ((hK z).1 hz).1]
        exact one_mem _
    have := hle hm
    rw [mem_comap, hq8] at this
    exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h.tg_mul_self_of_ilift (d := (4, 1, 1, 1)) (by decide) (by norm_num)) this
  have hcard : Nat.card F = 16 := by
    rw [hF, card_zpowers_sup_eq h8sq
      (mem_normalizer_of_commute fun y hy => h8c _ (mem_zpowers _) y hy) h8n,
      card_zpowers_sup_eq h4sq (mem_normalizer_of_commute fun y hy => hKc _ y hy) h4n, hK4]
  have hFK : F ⊓ q.ker = K := by
    refine le_antisymm (fun z hz => (hK z).2 ⟨(mem_inf.mp hz).2, hFe.2 z (mem_inf.mp hz).1⟩)
      fun z hz => mem_inf.mpr ⟨mem_sup_right (mem_sup_right hz), ((hK z).1 hz).1⟩
  refine ⟨F, hFe, hcard, by rw [hFK, hK4], ?_⟩
  have hc : ∀ y ∈ F, y * e₀ = e₀ * y := by
    rcases he₀ with he | he
    · intro y _
      exact (mem_center_iff.mp (h.ker_le he) y)
    · have hz : (ilift l (4, 1, 1, 1))⁻¹ * e₀ ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hq4, he, inv_mul_cancel]
      have hzc := mem_center_iff.mp (h.ker_le hz)
      have he' : e₀ = ilift l (4, 1, 1, 1) * ((ilift l (4, 1, 1, 1))⁻¹ * e₀) := by group
      intro y hy
      have hy4 := hFe.1 y hy _ (mem_sup_right (mem_sup_left (mem_zpowers _)))
      rw [he']
      generalize (ilift l (4, 1, 1, 1))⁻¹ * e₀ = w at hzc
      calc y * (ilift l (4, 1, 1, 1) * w) = (y * ilift l (4, 1, 1, 1)) * w := by group
        _ = (ilift l (4, 1, 1, 1) * y) * w := by rw [hy4]
        _ = ilift l (4, 1, 1, 1) * (y * w) := by group
        _ = ilift l (4, 1, 1, 1) * (w * y) := by rw [hzc y]
        _ = ilift l (4, 1, 1, 1) * w * y := by group
  exact fun f hf => (hc f hf).symm

end IsQSetting

theorem exists_inner_frame
    {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {e₀ : Jhat J}
    (he₀ : e₀ * e₀ ∈ center (Jhat J)) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J), IsQSetting q l ∧
      (q e₀ = 1 ∨ q e₀ = wordPerm (tg 4)) := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  have hs2 : q e₀ * q e₀ = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hqker]
    exact he₀
  obtain ⟨c, hcS, hc⟩ : ∃ c ∈ S, c * q e₀ * c⁻¹ = 1 ∨ c * q e₀ * c⁻¹ = wordPerm (tg 4) := by
    by_cases h1 : q e₀ = 1
    · exact ⟨1, S.one_mem, Or.inl (by rw [h1]; group)⟩
    · obtain ⟨g, hgS, hgT⟩ := exists_conj_mem_T0 (hqS e₀) hs2
      have hg2 : (g⁻¹ * q e₀ * g) * (g⁻¹ * q e₀ * g) = 1 := by
        calc (g⁻¹ * q e₀ * g) * (g⁻¹ * q e₀ * g) = g⁻¹ * (q e₀ * q e₀) * g := by group
          _ = 1 := by rw [hs2]; group
      have hg1 : g⁻¹ * q e₀ * g ≠ 1 := fun h => h1 (by
        calc q e₀ = g * (g⁻¹ * q e₀ * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group)
      rcases involution_mem_U hgT hg2 with hU | hU
      · obtain ⟨s, hs, hsv⟩ := exists_conj_tg4_U1 hU hg1
        refine ⟨s * g⁻¹, S.mul_mem (closure_wordSet_le _ hs) (S.inv_mem hgS), Or.inr ?_⟩
        rw [← hsv]
        group
      · obtain ⟨s, hs, hsv⟩ := exists_conj_tg4_U2 hU hg1
        refine ⟨s * g⁻¹, S.mul_mem (closure_wordSet_le _ hs) (S.inv_mem hgS), Or.inr ?_⟩
        rw [← hsv]
        group
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (S_le_R hcS)
  have hker'' : ((MulAut.conj c).toMonoidHom.comp q).ker = center (Jhat J) := by
    rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) _ hS' hsurj' (hker'' ▸ le_refl _)
  refine ⟨_, l, ⟨hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls⟩, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hc

end CFSG.ComponentClassification.GrSLit.L34Facts

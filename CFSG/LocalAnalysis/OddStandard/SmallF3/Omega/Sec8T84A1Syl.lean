module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Pre
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Tau
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

theorem sec8t84a1_sylow_core (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B) {K : Subgroup G}
    (hK : IsSylow2Of K (Nsub8 t B ⊓ centralizer (B : Set G))) (hAK : Asub8 t B ≤ K) :
    K ⊔ oddCoreIn (Nsub8 t B) = Nsub8 t B ⊓ centralizer (B : Set G) ∧
      K ⊓ (oddCoreIn (Nsub8 t B) ⊔ Asub8 t B) = Asub8 t B ∧
      ∃ φ : ↥K →* ↥B,
        (∀ k : ↥K, ((φ k : ↥B) : G) = (k : G) * t * (k : G)⁻¹ * t⁻¹) ∧
          Function.Surjective φ ∧ φ.ker = (Asub8 t B).subgroupOf K := by
  classical
  obtain ⟨τ, hτ, hker⟩ := sec8t84a1_exists_tau h8A h8B hctx
  have htop : τ.range = ⊤ := sec8t84a1_range_top h8B h6 hctx τ hτ
  have hK0 : Asub8 t B ⊔ oddCoreIn (Nsub8 t B) ≤ Nsub8 t B ⊓ centralizer (B : Set G) :=
    sec8t84a1_AO_le_C h8A hctx
  have hidx : ∃ k : ℕ,
      (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)).relIndex
        (Nsub8 t B ⊓ centralizer (B : Set G)) = 2 ^ k := by
    refine ⟨4, ?_⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, htop, Subgroup.card_top]
    exact hctx.B_e16.2
  have hsup : K ⊔ (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)) =
      Nsub8 t B ⊓ centralizer (B : Set G) :=
    sec9f_sylow_sup hK hK0 hidx
  have hKO : K ⊔ oddCoreIn (Nsub8 t B) = Nsub8 t B ⊓ centralizer (B : Set G) := by
    have h1 : K ⊔ oddCoreIn (Nsub8 t B) =
        K ⊔ (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)) := by
      rw [← sup_assoc, sup_eq_left.mpr hAK]
    rw [h1, hsup]
  have hAO : ∀ a ∈ Asub8 t B, ∀ o ∈ oddCoreIn (Nsub8 t B),
      a * o * a⁻¹ ∈ oddCoreIn (Nsub8 t B) :=
    fun a ha o ho => sec8t84a1_O_norm a (sec8t84a1_A_le_N ha) o ho
  have hinf : K ⊓ (oddCoreIn (Nsub8 t B) ⊔ Asub8 t B) = Asub8 t B :=
    sec9f_inf_eq hK.2.1 hAK (sec8t84a1_O_odd) hAO
  have hsup' : K.subgroupOf (Nsub8 t B ⊓ centralizer (B : Set G)) ⊔ τ.ker = ⊤ := by
    rw [hker, ← Subgroup.subgroupOf_sup hK.1 hK0, hsup, Subgroup.subgroupOf_self]
  have hφtop : (τ.comp (Subgroup.inclusion hK.1)).range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact (sec9f_map_eq_range τ
      (K.subgroupOf (Nsub8 t B ⊓ centralizer (B : Set G))) hsup').trans htop
  have hsurj : Function.Surjective (τ.comp (Subgroup.inclusion hK.1)) :=
    MonoidHom.range_eq_top.mp hφtop
  have hkerφ : (τ.comp (Subgroup.inclusion hK.1)).ker = (Asub8 t B).subgroupOf K := by
    have h1 : (τ.comp (Subgroup.inclusion hK.1)).ker =
        (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)).subgroupOf K := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
      constructor
      · intro hx
        have hxker : Subgroup.inclusion hK.1 x ∈ τ.ker := hx
        rw [hker, Subgroup.mem_subgroupOf] at hxker
        simpa using hxker
      · intro hx
        have hxker : Subgroup.inclusion hK.1 x ∈ τ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          simpa using hx
        exact hxker
    rw [h1, Subgroup.subgroupOf_inj, inf_comm (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)) K,
      inf_eq_left.mpr hAK, sup_comm (Asub8 t B) (oddCoreIn (Nsub8 t B))]
    exact hinf
  exact ⟨hKO, hinf, τ.comp (Subgroup.inclusion hK.1), fun k => hτ (Subgroup.inclusion hK.1 k),
    hsurj, hkerφ⟩

theorem sec8t84a1_exists_pre (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B) :
    ∃ K : Subgroup G, Sec8T84A1Pre G t L S z g B K := by
  classical
  obtain ⟨hAel, hAcard⟩ := sec8t84a1_A_elem hctx
  have hAp : IsPGroup 2 (Asub8 t B) := CFSG.Open.IsElemAbelian.isPGroup hAel
  have hAleC : Asub8 t B ≤ Nsub8 t B ⊓ centralizer (B : Set G) :=
    le_inf sec8t84a1_A_le_N (sec8t84a1_A_le_centB hctx)
  obtain ⟨K, hKsyl, hAK⟩ := sec68_exists_sylow_ge hAp hAleC
  obtain ⟨-, -, φ, hφ, hsurj, hkerφ⟩ :=
    sec8t84a1_sylow_core h8A h8B h6 hctx hKsyl hAK
  have hcardker : Nat.card φ.ker = 2 ^ 5 := by
    rw [hkerφ]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hAcard
  have hcard : Nat.card K = 2 ^ 9 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    rw [hcardker, sec8t84a1_B_card hctx] at h
    calc Nat.card K = 2 ^ 5 * 16 := h.symm
      _ = 2 ^ 9 := by norm_num
  have hA_le_cent : Asub8 t B ≤ centralizer ({t} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sec8t84a1_A_comm hctx ha sec8t84a1_t_mem_A
  have hcent : K ⊓ centralizer ({t} : Set G) = Asub8 t B := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxK, hxcent⟩ := hx
      have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxcent
      have hxker : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        rw [hφ, Subgroup.coe_one]
        rw [hcomm]
        group
      rw [hkerφ, Subgroup.mem_subgroupOf] at hxker
      simpa using hxker
    · exact le_inf hAK hA_le_cent
  refine ⟨K, hctx, hKsyl.1, hKsyl, hAK, hcard, hcent, ?_⟩
  intro b hb
  obtain ⟨k, hk⟩ := hsurj ⟨b, hb⟩
  exact ⟨k, k.2, by rw [← hφ k, hk]⟩

theorem sec8t84a1_pre_center {K : Subgroup G} (hK : Sec8T84A1Pre G t L S z g B K) :
    ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔ k ∈ B := by
  intro k hkK
  constructor
  · intro hkcent
    have hkt : k * t = t * k := hkcent t (hK.A_le sec8t84a1_t_mem_A)
    have hkcent_t : k ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hkt
    have hkA : k ∈ Asub8 t B := by
      rw [← hK.cent_t]
      exact ⟨hkK, hkcent_t⟩
    rcases sec8t84a1_mem_A hK.ctx hkA with hkB | ⟨b0, hb0B, hk_eq⟩
    · exact hkB
    · exfalso
      have hb0sq : b0 * b0 = 1 := sec8t84a1_B_sq hK.ctx hb0B
      have ht_eq : t = k * b0 := by rw [hk_eq, mul_assoc, hb0sq, mul_one]
      have hcomm : ∀ k' ∈ K, t * k' = k' * t := by
        intro k' hk'K
        have hb0k' : b0 * k' = k' * b0 :=
          Subgroup.mem_centralizer_iff.mp (hK.le_C hk'K).2 b0 hb0B
        have hkk' : k * k' = k' * k := hkcent k' hk'K
        calc t * k' = k * b0 * k' := by rw [ht_eq]
          _ = k * (b0 * k') := by group
          _ = k * (k' * b0) := by rw [hb0k']
          _ = (k * k') * b0 := by group
          _ = (k' * k) * b0 := by rw [hkk']
          _ = k' * (k * b0) := by group
          _ = k' * t := by rw [← ht_eq]
      have hBne : B ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card B = 1 := by rw [hbot]; exact Subgroup.card_bot
        have h16 := sec8t84a1_B_card hK.ctx
        omega
      obtain ⟨b', hb'B, hb'ne⟩ := (Subgroup.bot_or_exists_ne_one B).resolve_left hBne
      obtain ⟨k', hk'K, hk'eq⟩ := hK.tau b' hb'B
      have htriv : k' * t * k'⁻¹ * t⁻¹ = 1 := by
        have h := hcomm k' hk'K
        rw [← h]; group
      rw [← hk'eq, htriv] at hb'ne
      exact hb'ne rfl
  · intro hkB k' hk'K
    exact Subgroup.mem_centralizer_iff.mp (hK.le_C hk'K).2 k hkB

theorem sec8t84a1_pre_sup (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    {K : Subgroup G} (hK : Sec8T84A1Pre G t L S z g B K) :
    K ⊔ oddCoreIn (Nsub8 t B) = Nsub8 t B ⊓ centralizer (B : Set G) :=
  (sec8t84a1_sylow_core h8A h8B h6 hK.ctx hK.syl hK.A_le).1

end CFSG.OddStandard.SmallF3.Omega

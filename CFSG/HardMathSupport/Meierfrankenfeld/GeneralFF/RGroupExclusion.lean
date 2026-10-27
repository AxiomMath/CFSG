module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.JSubgroup
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Interfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

section Core

variable {X : Type} [Group X] [Finite X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
variable {ρ : Representation (ZMod 2) X W}

theorem false_of_moving_rGroup (hρ : Function.Injective ρ) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {K A : Subgroup X} (hK : IsPGroup r K) (hKbot : K ≠ ⊥) (hA2 : CFSG.IsElementaryAbelian 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set X)) (hKA : ⁅K, A⁆ = K)
    (hb : IsBestOffenderOn ρ A ⊤) : False := by
  classical
  have hKnt : ¬ K ≤ cenOn ρ K ⊤ := by
    intro hle
    apply hKbot
    refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => hρ ?_
    refine LinearMap.ext fun v => ?_
    rw [map_one]
    exact (hle hk).2 v Submodule.mem_top
  obtain ⟨B, hBA, hinv, hKU, hBU, hbest, -, hmove, hstrict⟩ :=
    exists_strictMin_moving K A hA2 hAK hKA hKnt hb
  set U : Submodule (ZMod 2) W := commOn ρ K ⊤ with hUdef
  set H : Subgroup X := K ⊔ B with hHdef
  have hKH : K ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (K : Set X) :=
    sup_le Subgroup.le_normalizer (hBA.trans hAK)
  have hfr : Fact r.Prime := ⟨hr⟩
  have hfU : Finite ↥U := inferInstance
  have hfGL : Finite (U ≃ₗ[ZMod 2] U) :=
    Finite.of_injective (fun f : U ≃ₗ[ZMod 2] U => (f : U → U)) DFunLike.coe_injective
  have hFG : imgGL ρ H U hinv K ≤ imgGL ρ H U hinv H := imgGL_mono hKH
  have hFn : ((imgGL ρ H U hinv K).subgroupOf (imgGL ρ H U hinv H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFG).2 (imgGL_le_normalizer hHN)
  have hKp : IsPGroup r ↥(imgGL ρ H U hinv K) := by
    have h1 : IsPGroup r ↥(K.subgroupOf H) :=
      hK.of_injective (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKH).injective
    exact h1.of_surjective _ (MonoidHom.subgroupMap_surjective (resGL ρ H U hinv) _)
  obtain ⟨m, hm⟩ := hKp.exists_card_eq
  have hnil : Group.IsNilpotent ↥(imgGL ρ H U hinv K) := hKp.isNilpotent
  have hodd : Odd (Nat.card ↥(imgGL ρ H U hinv K)) := by
    rw [hm]
    exact Odd.pow (hr.odd_of_ne_two (by omega))
  have hAG : imgGL ρ H U hinv B ≤ imgGL ρ H U hinv H := imgGL_mono hBH
  have hAel : CFSG.IsElementaryAbelian 2 (imgGL ρ H U hinv B) :=
    isElementaryAbelian_imgGL hBH hA2 hBA
  have hAne : imgGL ρ H U hinv B ≠ ⊥ := fun h => hBU ((imgGL_eq_bot_iff hBH).1 h)
  have hcpos : 0 < Nat.card (cenOn ρ B U) := Nat.card_pos
  have hoff : Nat.card U ≤ weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) (imgGL ρ H U hinv B) := by
    rw [weight_imgGL hBH]
    have h1 := hbest.isOffenderOn.2
    rw [← card_imgGL_mul_card_cenOn (hU := hinv) hBH, mul_assoc, mul_comm (Nat.card (cenOn ρ B U)),
      ← mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_right h1 hcpos
  have hstr : ∀ B₂ : Subgroup (U ≃ₗ[ZMod 2] U), ⊥ < B₂ → B₂ < imgGL ρ H U hinv B →
      weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) B₂ <
        weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) (imgGL ρ H U hinv B) := by
    intro B₂ hbot hlt
    obtain ⟨B', hB'B, hcB', hB'⟩ := exists_imgGL_eq (hU := hinv) hBH hlt.le
    have hB'H : B' ≤ H := hB'B.trans hBH
    have hne : B' ≠ B := by
      rintro rfl
      exact hlt.ne hB'.symm
    have hnc : ¬ B' ≤ cenOn ρ B U := by
      intro h
      have : imgGL ρ H U hinv B' = ⊥ := (imgGL_eq_bot_iff hB'H).2 fun b hb => ⟨hb, (h hb).2⟩
      rw [hB'] at this
      exact hbot.ne' this
    have key := hstrict B' hcB' (lt_of_le_of_ne hB'B hne) hnc
    have hc : cenOn ρ B' U = cenOn ρ B U := by
      rw [cenOn_eq_inf_of_le hB'B]
      exact inf_eq_right.2 hcB'
    have h1 := card_imgGL_mul_card_cenOn (hU := hinv) hB'H
    have h2 := card_imgGL_mul_card_cenOn (hU := hinv) hBH
    rw [hc] at h1
    rw [← h1, ← h2] at key
    have key' : Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U) <
        Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U) := by
      have : Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U)) <
          Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U)) := by
        calc _ = Nat.card (imgGL ρ H U hinv B') * Nat.card (cenOn ρ B U) *
              Nat.card (fixOn ρ B' U) := by ring
          _ < Nat.card (imgGL ρ H U hinv B) * Nat.card (cenOn ρ B U) *
              Nat.card (fixOn ρ B U) := key
          _ = _ := by ring
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    have e1 := weight_imgGL (hU := hinv) hB'H
    rw [hB'] at e1
    rw [e1, weight_imgGL hBH, ← hB']
    exact key'
  have hcomm : ⁅imgGL ρ H U hinv K, imgGL ρ H U hinv B⁆ ≠ ⊥ := by
    intro h
    obtain ⟨b, hbB, hbc⟩ := Set.not_subset.1 (fun h' : (B : Set X) ⊆ cenOn ρ B U => hBU h')
    obtain ⟨k, hkK, u, hu, hne⟩ := hmove b hbB hbc
    have hx : resGL ρ H U hinv ⟨k, hKH hkK⟩ ∈ imgGL ρ H U hinv K := resGL_mem_imgGL hkK _
    have hy : resGL ρ H U hinv ⟨b, hBH hbB⟩ ∈ imgGL ρ H U hinv B := resGL_mem_imgGL hbB _
    have h1 : ⁅resGL ρ H U hinv ⟨k, hKH hkK⟩, resGL ρ H U hinv ⟨b, hBH hbB⟩⁆ = 1 := by
      have : ⁅resGL ρ H U hinv ⟨k, hKH hkK⟩, resGL ρ H U hinv ⟨b, hBH hbB⟩⁆ ∈
          (⊥ : Subgroup (U ≃ₗ[ZMod 2] U)) := h ▸ Subgroup.commutator_mem_commutator hx hy
      simpa using this
    have h2 : resGL ρ H U hinv ⟨k, hKH hkK⟩ * resGL ρ H U hinv ⟨b, hBH hbB⟩ =
        resGL ρ H U hinv ⟨b, hBH hbB⟩ * resGL ρ H U hinv ⟨k, hKH hkK⟩ :=
      commutator_eq_one_iff.1 h1
    have h3 := congrArg (fun f : U ≃ₗ[ZMod 2] U => ((f ⟨u, hu⟩ : U) : W)) h2
    exact hne h3.symm
  have hres := CFSG.QuasithinUnique.Setup.Layer.nilpotent_offender_natural_S3_factors.{0, 0, 0}
    (k := ZMod 2) (V := ↥U) hFG hFn (hodd := hodd) hAG hAel hAne hoff hstr hcomm
  have hcard := hres.2.2.2.1
  have hdvd : Nat.card ↥(⁅imgGL ρ H U hinv K, imgGL ρ H U hinv B⁆ : Subgroup (U ≃ₗ[ZMod 2] U)) ∣
      Nat.card ↥(imgGL ρ H U hinv K) :=
    Subgroup.card_dvd_of_le
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAG.trans (imgGL_le_normalizer hHN)))
  rw [hcard, hm] at hdvd
  have h3r : 3 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h3r
  omega

end Core

theorem oddPrimeCoreExclusion :
    CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.OddPrimeCoreExclusion := by
  intro X _ _ W _ _ _ ρ hρ _ r hr hr5 R A hR hRn hA2 hAb
  have hAN : A ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hRn]
    exact le_top
  by_contra hne
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := fun a _ h =>
    hρ (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ A ⊤ := (isBestOffender_iff_on ρ A hfaith).1 ⟨hA2, hAb⟩
  have hfr : Fact r.Prime := ⟨hr⟩
  have hRle : ⁅R, A⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hK : IsPGroup r ↥(⁅R, A⁆ : Subgroup X) := hR.to_le hRle
  have hAK : A ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup X) : Set X) := fun a ha =>
    Subgroup.mem_normalizer_iff.2 fun h =>
      ⟨fun hh => commutator_conj_mem ha hh, fun hh => by
        have := commutator_conj_mem (A.inv_mem ha) hh
        simpa [mul_assoc] using this⟩
  have h2R : ¬ 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    intro h
    have h2 : 2 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2
    omega
  have hKA : ⁅⁅R, A⁆, A⁆ = ⁅R, A⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2 Nat.prime_two A R
      (CFSG.IsElementaryAbelian.isPGroup 2 A) h2R hAN
  exact false_of_moving_rGroup hρ hr hr5 hK hne hA2 hAK hKA hb

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

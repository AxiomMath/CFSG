module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutPrime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem false_of_relIndex_prime_normal_sylow {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (I H : Subgroup A) [I.Normal] (hIH : I ≤ H)
    (hI : I ≤ ⁅H, H⁆) (hindex : I.relIndex H = p) (hdvd : p ∣ Nat.card I)
    (hndvd : ¬ p ^ 2 ∣ Nat.card I)
    (hfix : ∀ S : Subgroup A, S ≤ I → Nat.card S = p → ∀ α ∈ H, α ^ p = 1 →
      (∀ s ∈ S, α * s = s * α) → α ∈ I) : False := by
  have hcard : Nat.card (I.subgroupOf H) = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIH).toEquiv
  refine false_of_prime_index_normal_sylow hp hp2 (I.subgroupOf H) ?_ hindex (hcard ▸ hdvd)
    (hcard ▸ hndvd) ?_
  · intro x hx
    have hx' : (x : A) ∈ ⁅H, H⁆ := hI hx
    have hcomm : ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, H.range_subtype]
    rw [hcomm] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    have : y = x := Subtype.ext hxy
    exact this ▸ hy
  · intro S' hS' hcardS α' hα' hcomm
    have hmap : Nat.card (S'.map H.subtype) = p := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hcardS]
    have hle : S'.map H.subtype ≤ I := by
      rintro _ ⟨s, hs, rfl⟩
      exact hS' hs
    have hα : (α' : A) ^ p = 1 := by
      have := congrArg Subtype.val hα'
      simpa using this
    have := hfix (S'.map H.subtype) hle hmap α'.1 α'.2 hα (by
      rintro _ ⟨s, hs, rfl⟩
      exact congrArg Subtype.val (hcomm s hs))
    exact this

theorem not_dvd_card_outer_of_sylow_card_eq_prime
    (hRed : CFSG.AGLEmbedding.OuterSylow.ReducedOuterSylow)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup K)
    (hS : ∀ S : Sylow p K, Nat.card S = p) :
    ¬ p ∣ Nat.card (Outer K) := by
  classical
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot K hnab
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have h1 : ∀ z : K, a * z * a⁻¹ = b * z * b⁻¹ := fun z => by
      have := congrArg (fun f : MulAut K => f z) hab
      simpa [MulAut.conj_apply] using this
    have hc : b⁻¹ * a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h2 : (b⁻¹ * a) * z * (b⁻¹ * a)⁻¹ = z := by
        calc (b⁻¹ * a) * z * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * z * a⁻¹) * b := by group
          _ = b⁻¹ * (b * z * b⁻¹) * b := by rw [h1 z]
          _ = z := by group
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  obtain ⟨S0⟩ : Nonempty (Sylow p K) := inferInstance
  have hS0 : Nat.card S0 = p := hS S0
  have hpK : p ∣ Nat.card K := hS0 ▸ Subgroup.card_subgroup_dvd_card (S0 : Subgroup K)
  have hp2K : ¬ p ^ 2 ∣ Nat.card K := by
    intro h2
    have hle : 2 ≤ (Nat.card K).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Nat.card_pos).ne').1 h2
    have := Sylow.card_eq_multiplicity S0
    rw [hS0] at this
    have h3 : p ^ 2 ≤ p ^ (Nat.card K).factorization p := Nat.pow_le_pow_right hp.pos hle
    rw [← this] at h3
    nlinarith [hp.two_le]
  have hcardI : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner K) =
      Nat.card K := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set I : Subgroup (MulAut K) := CFSG.ComponentClassification.OuterAutomorphisms.inner K with hI
  set H : Subgroup (MulAut K) := (Subgroup.zpowers x).comap (QuotientGroup.mk' I) with hH
  have hIH : I ≤ H := by
    intro a ha
    rw [hH, Subgroup.mem_comap]
    have : QuotientGroup.mk' I a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    rw [this]
    exact Subgroup.one_mem _
  have hindex : I.relIndex H = p := by
    have h1 := Subgroup.relIndex_ker (K := H) (QuotientGroup.mk' I)
    rw [QuotientGroup.ker_mk'] at h1
    rw [h1, hH, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective I),
      Nat.card_zpowers, hx]
  have hperf : I ≤ ⁅H, H⁆ := by
    have h1 : ⁅I, I⁆ = I := by
      have h2 : I = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
        rw [hI]
        unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
        exact MonoidHom.range_eq_map _
      have h3 : (⊤ : Subgroup K) = ⁅(⊤ : Subgroup K), ⊤⁆ := by
        rw [← commutator_def]
        exact (CFSG.ComponentClassification.Helpers.commutator_eq_top K hnab).symm
      calc ⁅I, I⁆ = ⁅(⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K),
            (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K)⁆ := by rw [← h2]
        _ = ((⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K)).map (MulAut.conj : K →* MulAut K) :=
            (Subgroup.map_commutator _ _ _).symm
        _ = I := by rw [← h3, h2]
    calc I = ⁅I, I⁆ := h1.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hIH hIH
  have hfix : ∀ S : Subgroup (MulAut K), S ≤ I → Nat.card S = p → ∀ α ∈ H, α ^ p = 1 →
      (∀ s ∈ S, α * s = s * α) → α ∈ I := by
    intro S hSI hScard α hαH hαp hαcomm
    set S₁ : Subgroup K := S.comap (MulAut.conj : K →* MulAut K) with hS₁
    have hS₁map : S₁.map (MulAut.conj : K →* MulAut K) = S := by
      rw [hS₁]
      refine Subgroup.map_comap_eq_self ?_
      intro a ha
      exact (show a ∈ (MulAut.conj : K →* MulAut K).range from hSI ha)
    have hS₁card : Nat.card S₁ = p := by
      rw [← Subgroup.card_map_of_injective hinj, hS₁map, hScard]
    have hP : IsPGroup p S₁ := IsPGroup.of_card (n := 1) (by rw [hS₁card, pow_one])
    have hidx : ¬ p ∣ S₁.index := by
      intro hd
      apply hp2K
      have := Subgroup.card_mul_index S₁
      rw [hS₁card] at this
      rw [← this, pow_two]
      exact Nat.mul_dvd_mul_left p hd
    have hcyc : IsCyclic S₁ := isCyclic_of_prime_card hS₁card
    have hfixα : ∀ s ∈ S₁, α s = s := by
      intro s hs
      have hmem : (MulAut.conj s : MulAut K) ∈ S := by
        rw [← hS₁map]
        exact ⟨s, hs, rfl⟩
      have hc := hαcomm _ hmem
      have key : ∀ z : K, α s * z * (α s)⁻¹ = s * z * s⁻¹ := by
        intro z
        obtain ⟨y, rfl⟩ := α.surjective z
        have := congrArg (fun β : MulAut K => β y) hc
        simpa [MulAut.conj_apply, map_mul, map_inv] using this
      have hcen : s⁻¹ * α s ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h1 : (s⁻¹ * α s) * z * (s⁻¹ * α s)⁻¹ = z := by
          calc (s⁻¹ * α s) * z * (s⁻¹ * α s)⁻¹ = s⁻¹ * (α s * z * (α s)⁻¹) * s := by group
            _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [key z]
            _ = z := by group
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm
      rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
      exact hcen.symm
    exact hRed K inferInstance hnab hcat p hp hp2 hpK S₁ hP hidx hcyc α hαp hfixα
  exact false_of_relIndex_prime_normal_sylow hp hp2 I H hIH hperf hindex
    (hcardI ▸ hpK) (hcardI ▸ hp2K) hfix

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

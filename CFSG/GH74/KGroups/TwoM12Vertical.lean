module

public import CFSG.GH74.KGroups.TwoM12Fixed
public import CFSG.GH74.GLS.TwoThin.G.C2Vertical

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open CFSG.GH74.E2 (Shape2M12)

theorem exists_noncomm_of_isQuasisimple {K : Type} [Group K] (hK : CFSG.IsQuasisimple K) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem twoThinC2VerticalG_2M12
    : TwoThinC2VerticalG_2M12 := by
  classical
  intro L _ _ hL σ I K₀ _ hσ hI hK₀ hφ
  obtain ⟨φ, hφs, hφo⟩ := hφ
  have : Finite K₀ := Finite.of_surjective φ hφs
  have hK₀q : CFSG.IsQuasisimple K₀ := hK₀.1.1
  have hσ2 : (σ : MulAut L) * σ = 1 := MulEquiv.ext fun l => hσ l
  by_cases h1 : (σ : MulAut L) = 1
  ·
    have hfix : ∀ l : L, l ∈ TwoThin.fixedSubgroup σ := fun l => by
      rw [TwoThin.mem_fixedSubgroup]
      have := congrArg (fun f : MulAut L => f l) h1
      simpa using this
    have hfixtop : TwoThin.fixedSubgroup σ = ⊤ := eq_top_iff.2 fun l _ => hfix l
    let eF : ↥(TwoThin.fixedSubgroup σ) ≃* L :=
      (MulEquiv.subgroupCongr hfixtop).trans Subgroup.topEquiv
    have hQF : CFSG.IsQuasisimple ↥(TwoThin.fixedSubgroup σ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm hL.1
    obtain ⟨K', -, hsub, -, -⟩ := hI.2
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQF hsub with
      htop | hcent
    ·
      have hIF : TwoThin.fixedSubgroup σ ≤ I := Subgroup.subgroupOf_eq_top.1 htop
      have hItop : I = ⊤ := eq_top_iff.2 (hfixtop ▸ hIF)
      let eI : ↥I ≃* L := (MulEquiv.subgroupCongr hItop).trans Subgroup.topEquiv
      have hQI : CFSG.IsQuasisimple ↥I := CFSG.LocalCores.isQuasisimple_of_mulEquiv eI.symm hL.1
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQI φ.normal_ker with hker | hker
      ·
        obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hK₀q
        apply hab
        have h1' : ∀ k : K₀, k = 1 := fun k => by
          obtain ⟨x, rfl⟩ := hφs k
          have : x ∈ φ.ker := by rw [hker]; trivial
          exact this
        rw [h1' a, h1' b]
      ·
        have hcz : Nat.card ↥(center ↥I) = 2 := by
          rw [CFSG.GH74.E2.card_center_eq_of_mulEquiv eI]
          exact hL.2.1
        have hdvd : Nat.card φ.ker ∣ 2 := hcz ▸ Subgroup.card_dvd_of_le hker
        have hker1 : Nat.card φ.ker = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
          · exact h
          · exact absurd hφo (by rw [h]; decide)
        have hbot : φ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hker1
        have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hbot
        let eφ : ↥I ≃* K₀ := MulEquiv.ofBijective φ ⟨hinj, hφs⟩
        exact not_inB2_of_card_two_M12 hL.2.1 hL.2.2 (inB2_of_mulEquiv (eI.symm.trans eφ).symm hK₀)
    ·
      obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hK₀q
      apply hab
      obtain ⟨a', rfl⟩ := hφs a
      obtain ⟨b', rfl⟩ := hφs b
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hcomm := Subgroup.mem_center_iff.1
        (hcent (Subgroup.mem_subgroupOf.2 a'.2 : (⟨(a' : L), hI.1 a'.2⟩ : ↥(TwoThin.fixedSubgroup σ)) ∈
          I.subgroupOf (TwoThin.fixedSubgroup σ))) ⟨(b' : L), hI.1 b'.2⟩
      exact (congrArg Subtype.val hcomm).symm
  ·
    have hIfix : ∀ x ∈ I, σ x = x := fun x hx => hI.1 hx
    have hKtop : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤ := by
      rw [← _root_.commutator_def]
      exact Group.isPerfect_def.1 hK₀q.1
    obtain ⟨J, hJ, hJmin⟩ : ∃ J : Subgroup ↥I, J.map φ = ⊤ ∧
        ∀ J' : Subgroup ↥I, J'.map φ = ⊤ → Nat.card J ≤ Nat.card J' := by
      have hex : ∃ n : ℕ, ∃ J : Subgroup ↥I, J.map φ = ⊤ ∧ Nat.card J = n :=
        ⟨_, ⊤, by rw [Subgroup.map_top]; exact MonoidHom.range_eq_top.2 hφs, rfl⟩
      obtain ⟨J, hJ, hJc⟩ := Nat.find_spec hex
      refine ⟨J, hJ, fun J' hJ' => ?_⟩
      rw [hJc]
      exact Nat.find_min' hex ⟨J', hJ', rfl⟩
    have hJperf : ⁅J, J⁆ = J := by
      have hmap : (⁅J, J⁆).map φ = ⊤ := by
        rw [Subgroup.map_commutator, hJ, hKtop]
      have hle : ⁅J, J⁆ ≤ J := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
      exact Subgroup.eq_of_le_of_card_ge hle (hJmin _ hmap)
    set J' : Subgroup L := J.map I.subtype with hJ'
    have hJ'perf : ⁅J', J'⁆ = J' := by rw [hJ', ← Subgroup.map_commutator, hJperf]
    have hJ'fix : ∀ x ∈ J', σ x = x := by
      rintro _ ⟨y, hy, rfl⟩
      exact hIfix y y.2
    have hcardJ' : Nat.card J' = Nat.card J := Subgroup.card_map_of_injective I.subtype_injective
    have h60 := CFSG.GH74.KGroups.TwoM12.card_le_sixty_of_fixed hL σ hσ2 h1 hJ'perf hJ'fix
    have hKJ : Nat.card K₀ ≤ Nat.card J := by
      have hsurj : Function.Surjective (fun x : J => φ x) := by
        intro k
        have hk : k ∈ J.map φ := by rw [hJ]; trivial
        obtain ⟨x, hx, rfl⟩ := hk
        exact ⟨⟨x, hx⟩, rfl⟩
      exact Nat.card_le_card_of_surjective _ hsurj
    have h120 := card_ge_of_inB2 hK₀
    omega

end CFSG.GH74.KGroups.TwoM12

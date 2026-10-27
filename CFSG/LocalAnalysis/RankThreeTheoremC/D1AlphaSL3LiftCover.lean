module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Lift

open CFSG.LieType.Steinberg

theorem exists_surjective_lift {S K Q : Type*} [Group S] [Group K] [Group Q]
    {β : S →* Q} {η : K →* Q} (hK : commutator K = ⊤) (hβ : Function.Surjective β)
    (hcen : η.ker ≤ Subgroup.center K)
    (hsec : ∃ σ : S →* pullback β η, ∀ s, pullbackFst β η (σ s) = s) :
    ∃ α : S →* K, (∀ s, η (α s) = β s) ∧ Function.Surjective α := by
  obtain ⟨σ, hσ⟩ := hsec
  let α : S →* K := ((MonoidHom.snd S K).comp (pullback β η).subtype).comp σ
  have hα : ∀ s, η (α s) = β s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback β η) : S × K).1 = s := hσ s
    change η ((σ s : pullback β η) : S × K).2 = β s
    rw [← hmem, h1]
  have hdecomp : ∀ x : K, ∃ s, x * (α s)⁻¹ ∈ Subgroup.center K := fun x => by
    obtain ⟨s, hs⟩ := hβ (η x)
    refine ⟨s, hcen ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hs, mul_inv_cancel]
  refine ⟨α, hα, fun x => ?_⟩
  have hcomm : commutator K ≤ α.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ := hdecomp x
    obtain ⟨t, ht⟩ := hdecomp y
    have e : ⁅x, y⁆ = ⁅α s, α t⁆ := by
      have h := commutatorElement_mul_mul_of_mem_center hs ht (α s) (α t)
      rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  exact hcomm (by rw [hK]; exact Subgroup.mem_top x)

theorem exists_section_pullback {k : Type} [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4) {K Q : Type} [Group K] [Group Q]
    {β : SpecialLinearGroup (Fin 3) k →* Q} {η : K →* Q} (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center K) :
    ∃ σ : SpecialLinearGroup (Fin 3) k →* pullback β η, ∀ s, pullbackFst β η (σ s) = s := by
  have h2 : Nat.card k ≠ 2 := by
    intro h
    rw [h] at h3
    omega
  have hsep := CentralExt.SLClosed.separating_of_card (m := 2) (F := k) (by norm_num) h2
    (fun h => h4 h.2) (fun h => absurd h.1 (by norm_num))
  exact CentralExt.SLClosed.sl_exists_section_of_separating (m := 2) (by norm_num) hsep
    (pullbackFst_surjective hη) (ker_pullbackFst_le_center hcen)

end Lift

theorem ker_eq_bot_of_card_dvd_prime {S K : Type*} [Group S] [Group K] {p : ℕ} (hp : p.Prime)
    (α : S →* K) {C : Subgroup S} (hker : α.ker ≤ C) (hC : Nat.card C ∣ p)
    (hne : ∃ s ∈ C, α s ≠ 1) : α.ker = ⊥ := by
  have hdvd : Nat.card α.ker ∣ Nat.card C := Subgroup.card_dvd_of_le hker
  rcases (Nat.dvd_prime hp).1 (hdvd.trans hC) with h1 | hpk
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have hCp : Nat.card C = p := Nat.dvd_antisymm hC (hpk ▸ hdvd)
    have : Finite C := Nat.finite_of_card_ne_zero (hCp ▸ hp.ne_zero)
    obtain ⟨s, hsC, hs⟩ := hne
    have hCker : α.ker = C := Subgroup.eq_of_le_of_card_ge hker (hCp.trans hpk.symm).le
    exact hs (MonoidHom.mem_ker.1 (hCker ▸ hsC))

theorem exists_mulEquiv_specialLinear {k : Type} [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL 3 k)
    (hz : Subgroup.center K ≠ ⊥) :
    Nonempty (SpecialLinearGroup (Fin 3) k ≃* K) := by
  let β : SpecialLinearGroup (Fin 3) k →* LinearFlag.projectiveSL 3 k := LinearFlag.proj 3 k
  let η : K →* LinearFlag.projectiveSL 3 k :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hβ : Function.Surjective β := LinearFlag.proj_surjective 3 k
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : ∀ z, η z = 1 ↔ z ∈ Subgroup.center K := fun z => by
    change e (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hcen : η.ker ≤ Subgroup.center K := fun z hz => (hηker z).1 hz
  obtain ⟨α, hα, hαsurj⟩ :=
    exists_surjective_lift hK hβ hcen (exists_section_pullback h3 h4 hη hcen)
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨s, hs⟩ := hαsurj z
  have hβker : β.ker = Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    rw [LinearFlag.ker_proj, LinearFlag.scalars_eq_center]
  have hsker : s ∈ β.ker := by
    rw [MonoidHom.mem_ker, ← hα, hs]
    exact (hηker z).2 hzc
  have hαker : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    intro t ht
    rw [← hβker, MonoidHom.mem_ker, ← hα, MonoidHom.mem_ker.1 ht, map_one]
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) k)) ∣ 3 :=
    (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by norm_num) k).trans
      (Nat.gcd_dvd_left _ _)
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact ker_eq_bot_of_card_dvd_prime Nat.prime_three α hαker hcard
      ⟨s, hβker ▸ hsker, by rw [hs]; exact hz1⟩
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαsurj⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

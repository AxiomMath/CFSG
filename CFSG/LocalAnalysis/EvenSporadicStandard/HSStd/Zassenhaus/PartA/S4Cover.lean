module

public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers
open scoped commutatorElement

section Computation

variable {P : Type*} [Group P]

theorem commutator_mul_central {d d' z z' : P} (h1 : Commute z (d' * z')) (h2 : Commute d z') :
    ⁅d * z, d' * z'⁆ = ⁅d, d'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq, commutatorElement_mul_right_eq_mul_conj,
    h2.commutator_eq]
  simp

theorem commutator_perfect_of_central {H : Type*} [Group H] (π : P →* H) (Q : Subgroup P)
    (hcen : ∀ z ∈ Q, π z = 1 → ∀ g ∈ Q, g * z = z * g)
    (hQ : ⁅Q.map π, Q.map π⁆ = Q.map π) :
    ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ = ⁅Q, Q⁆ ∧ ⁅Q, Q⁆.map π = Q.map π := by
  have hmap : ⁅Q, Q⁆.map π = Q.map π := by rw [map_commutator, hQ]
  refine ⟨le_antisymm (commutator_le_self _) ?_, hmap⟩
  have hsplit : ∀ g ∈ Q, ∃ d ∈ ⁅Q, Q⁆, ∃ z ∈ Q, π z = 1 ∧ g = d * z := by
    intro g hg
    have : π g ∈ ⁅Q, Q⁆.map π := hmap ▸ ⟨g, hg, rfl⟩
    obtain ⟨d, hd, hdg⟩ := this
    refine ⟨d, hd, d⁻¹ * g, Q.mul_mem (Q.inv_mem (commutator_le_self Q hd)) hg, ?_, by group⟩
    rw [map_mul, map_inv, hdg, inv_mul_cancel]
  rw [commutator_le]
  intro g hg h hh
  obtain ⟨d, hd, z, hz, hπz, rfl⟩ := hsplit g hg
  obtain ⟨d', hd', z', hz', hπz', rfl⟩ := hsplit h hh
  have hdQ := commutator_le_self Q hd
  have hd'Q := commutator_le_self Q hd'
  rw [commutator_mul_central]
  · exact commutator_mem_commutator hd hd'
  · exact (hcen z hz hπz _ (Q.mul_mem hd'Q hz')).symm
  · exact (hcen z' hz' hπz' d hdQ)

end Computation

section Cover

variable {P : Type} [Group P]

theorem ker_eq_bot_of_odd_five (hP : Group.IsPerfect P)
    {π : P →* alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin 5))) (hopfLift π hs hk)
  rw [map_hopfMultiplier_hopfLift π hs hk, hopfMultiplier_alternatingGroup_five.2] at h
  have h1 : Nat.card π.ker = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  exact (Subgroup.card_eq_one).1 h1

theorem eq_one_of_mem_perfect_five
    {π : P →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)}
    (hk : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker))
    (D : Subgroup P) (hD : ⁅D, D⁆ = D) (f : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
      alternatingGroup (Fin 5)) (hf : ∀ d ∈ D, f (π d) = 1 → π d = 1)
    (hsurj : ∀ a, ∃ d ∈ D, f (π d) = a) :
    ∀ d ∈ D, π d = 1 → d = 1 := by
  have hperf : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hD
  let π₁ : ↥D →* alternatingGroup (Fin 5) := f.comp (π.comp D.subtype)
  have hs : Function.Surjective π₁ := by
    intro a
    obtain ⟨d, hd, hda⟩ := hsurj a
    exact ⟨⟨d, hd⟩, hda⟩
  have hker : π₁.ker ≤ center ↥D := by
    intro d hd
    have h1 : f (π d) = 1 := hd
    have h2 : π d = 1 := hf d d.2 h1
    have hz : (d : P) ∈ center P := hk h2
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    exact Subtype.ext (hz g)
  have hoddk : Odd (Nat.card π₁.ker) := by
    refine Odd.of_dvd_nat hodd ?_
    refine Subgroup.card_dvd_of_injective
      (f := ((D.subtype.comp π₁.ker.subtype).codRestrict π.ker ?_)) ?_
    · intro d
      have h1 : f (π d.1) = 1 := d.2
      exact hf d.1.1 d.1.2 h1
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
  have hbot := ker_eq_bot_of_odd_five hperf hs hker hoddk
  intro d hd hπd
  have : (⟨d, hd⟩ : ↥D) ∈ π₁.ker := by
    change f (π d) = 1
    rw [hπd, map_one]
  rw [hbot] at this
  exact congrArg Subtype.val (Subgroup.mem_bot.1 this)

theorem ker_eq_bot_of_odd_five_sq (hP : Group.IsPerfect P)
    {π : P →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)} (hs : Function.Surjective π)
    (hk : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hA : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hAc : ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ =
      ⊤ := by
    have := hA.1
    rwa [commutator_def] at this
  set T1 : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := (⊤ : Subgroup (alternatingGroup (Fin 5))).prod ⊥ with hT1
  set T2 : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := (⊥ : Subgroup (alternatingGroup (Fin 5))).prod ⊤ with hT2
  set Q₁ : Subgroup P := T1.comap π with hQ1
  set Q₂ : Subgroup P := T2.comap π with hQ2
  have hT1perf : ⁅T1, T1⁆ = T1 := by
    rw [hT1, commutator_prod_prod, hAc, commutator_bot_left]
  have hT2perf : ⁅T2, T2⁆ = T2 := by
    rw [hT2, commutator_prod_prod, hAc, commutator_bot_left]
  have hQ1m : Q₁.map π = T1 := Subgroup.map_comap_eq_self_of_surjective hs T1
  have hQ2m : Q₂.map π = T2 := Subgroup.map_comap_eq_self_of_surjective hs T2
  have hcen : ∀ (Q : Subgroup P), ∀ z ∈ Q, π z = 1 → ∀ g ∈ Q, g * z = z * g := by
    intro Q z _ hz g _
    exact ((Subgroup.mem_center_iff.1 (hk hz)) g)
  obtain ⟨hD1, hD1m⟩ := commutator_perfect_of_central π Q₁ (hcen Q₁) (by rw [hQ1m, hT1perf])
  obtain ⟨hD2, hD2m⟩ := commutator_perfect_of_central π Q₂ (hcen Q₂) (by rw [hQ2m, hT2perf])
  set D₁ : Subgroup P := ⁅Q₁, Q₁⁆ with hD1def
  set D₂ : Subgroup P := ⁅Q₂, Q₂⁆ with hD2def
  have hD1T : ∀ d ∈ D₁, π d ∈ T1 := fun d hd => by
    have : d ∈ Q₁ := commutator_le_self Q₁ hd
    exact this
  have hD2T : ∀ d ∈ D₂, π d ∈ T2 := fun d hd => by
    have : d ∈ Q₂ := commutator_le_self Q₂ hd
    exact this
  have key1 : ∀ d ∈ D₁, (π d).2 = 1 := fun d hd => by
    have := hD1T d hd
    rw [hT1, Subgroup.mem_prod] at this
    exact Subgroup.mem_bot.1 this.2
  have key2 : ∀ d ∈ D₂, (π d).1 = 1 := fun d hd => by
    have := hD2T d hd
    rw [hT2, Subgroup.mem_prod] at this
    exact Subgroup.mem_bot.1 this.1
  have h1 : ∀ d ∈ D₁, π d = 1 → d = 1 := by
    refine eq_one_of_mem_perfect_five hk hodd D₁ hD1 (MonoidHom.fst _ _) ?_ ?_
    · intro d hd hf
      exact Prod.ext hf (key1 d hd)
    · intro a
      have : ((a, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ D₁.map π := by
        rw [hD1m, hQ1m, hT1, Subgroup.mem_prod]
        exact ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
      obtain ⟨d, hd, hda⟩ := this
      exact ⟨d, hd, by simp [hda]⟩
  have h2 : ∀ d ∈ D₂, π d = 1 → d = 1 := by
    refine eq_one_of_mem_perfect_five hk hodd D₂ hD2 (MonoidHom.snd _ _) ?_ ?_
    · intro d hd hf
      exact Prod.ext (key2 d hd) hf
    · intro a
      have : ((1, a) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ D₂.map π := by
        rw [hD2m, hQ2m, hT2, Subgroup.mem_prod]
        exact ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
      obtain ⟨d, hd, hda⟩ := this
      exact ⟨d, hd, by simp [hda]⟩
  have hcz : ⁅D₁, D₂⁆ ≤ center P := by
    rw [commutator_le]
    intro a ha b hb
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have e1 := key1 a ha
    have e2 := key2 b hb
    refine Prod.ext ?_ ?_
    · simp [commutatorElement_def, e2]
    · simp [commutatorElement_def, e1]
  have hzero : ∀ X : Subgroup P, X ≤ center P → ∀ Y : Subgroup P, ⁅X, Y⁆ = ⊥ := by
    intro X hX Y
    rw [eq_bot_iff]
    calc ⁅X, Y⁆ ≤ ⁅center P, Y⁆ := commutator_mono_left hX
      _ = ⊥ := commutator_center_left Y
      _ ≤ ⊥ := le_rfl
  have hD1D2 : ⁅D₁, D₂⁆ = ⊥ := by
    have hcz' : ⁅D₂, D₁⁆ ≤ center P := by rw [commutator_comm]; exact hcz
    have h3 : ⁅⁅D₁, D₁⁆, D₂⁆ = ⊥ :=
      commutator_commutator_eq_bot_of_rotate (hzero _ hcz D₁) (hzero _ hcz' D₁)
    rwa [hD1] at h3
  have hdec : ∀ g : P, ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, π (d₁ * d₂) = π g := by
    intro g
    have e1 : ((( π g).1, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ D₁.map π := by
      rw [hD1m, hQ1m, hT1, Subgroup.mem_prod]
      exact ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
    have e2 : ((1, (π g).2) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ D₂.map π := by
      rw [hD2m, hQ2m, hT2, Subgroup.mem_prod]
      exact ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
    obtain ⟨d₁, hd₁, hd₁'⟩ := e1
    obtain ⟨d₂, hd₂, hd₂'⟩ := e2
    refine ⟨d₁, hd₁, d₂, hd₂, ?_⟩
    rw [map_mul, hd₁', hd₂']
    simp
  have hS : D₁ ⊔ D₂ = ⊤ := by
    rw [eq_top_iff]
    have hperf : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
      have := hP.1
      rwa [commutator_def] at this
    rw [← hperf, commutator_le]
    intro g _ h _
    obtain ⟨d₁, hd₁, d₂, hd₂, hg⟩ := hdec g
    obtain ⟨d₁', hd₁', d₂', hd₂', hh⟩ := hdec h
    have hzg : (d₁ * d₂)⁻¹ * g ∈ center P := hk (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel])
    have hzh : (d₁' * d₂')⁻¹ * h ∈ center P := hk (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hh, inv_mul_cancel])
    have eg : g = (d₁ * d₂) * ((d₁ * d₂)⁻¹ * g) := by group
    have eh : h = (d₁' * d₂') * ((d₁' * d₂')⁻¹ * h) := by group
    rw [eg, eh, commutator_mul_central]
    · exact Subgroup.commutator_le_self (D₁ ⊔ D₂)
        (commutator_mem_commutator (mul_mem_sup hd₁ hd₂) (mul_mem_sup hd₁' hd₂'))
    · exact ((Subgroup.mem_center_iff.1 hzg) _).symm
    · exact ((Subgroup.mem_center_iff.1 hzh) _)
  rw [eq_bot_iff]
  intro z hz
  have hzS : z ∈ D₁ ⊔ D₂ := hS ▸ Subgroup.mem_top z
  have : Q₂.Normal := Subgroup.Normal.comap (by rw [hT2]; infer_instance) π
  have : D₂.Normal := inferInstance
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hzS
  have hπ : π a * π b = 1 := by rw [← map_mul]; exact hz
  have ea : π a = 1 := by
    refine Prod.ext ?_ (key1 a ha)
    have := congrArg Prod.fst hπ
    simpa [key2 b hb] using this
  have eb : π b = 1 := by
    refine Prod.ext (key2 b hb) ?_
    have := congrArg Prod.snd hπ
    simpa [key1 a ha] using this
  rw [h1 a ha ea, h2 b hb eb]
  simp

end Cover


end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

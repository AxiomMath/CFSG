module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G]

theorem ker_isCyclic_card_of_std {J P Z : Subgroup G} (hP : IsSylowTwoIn P J)
    (hZ : ∀ g, g ∈ Z ↔ g ∈ P ∧ g ∈ zStarIn J) (hZc : IsCyclic ↥Z) (hZ4 : Nat.card ↥Z = 4)
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqker : q.ker = center (Jhat J))
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) :
    IsCyclic ↥q.ker ∧ Nat.card ↥q.ker = 4 := by
  have hP2 : IsPGroup 2 P := isPGroup_of_isSylowTwoIn hP
  have hPJ : P ≤ J := hP.1
  have hmem : ∀ z : ↥Z, jq J ⟨z, hPJ ((hZ z).1 z.2).1⟩ ∈ q.ker := fun z => by
    rw [hqker]
    exact (mem_zStarIn_iff _).1 ((hZ z).1 z.2).2
  let f : ↥Z →* ↥q.ker :=
    { toFun := fun z => ⟨jq J ⟨z, hPJ ((hZ z).1 z.2).1⟩, hmem z⟩
      map_one' := Subtype.ext (map_one (jq J))
      map_mul' := fun z z' => Subtype.ext
        (map_mul (jq J) ⟨z, hPJ ((hZ z).1 z.2).1⟩ ⟨z', hPJ ((hZ z').1 z'.2).1⟩) }
  have hinj : Function.Injective f := fun z z' h => Subtype.ext
    (eq_of_jq_eq hPJ hP2 ((hZ z).1 z.2).1 ((hZ z').1 z'.2).1 (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    have he1 : q e ∈ T0 := by
      rw [MonoidHom.mem_ker.mp he]
      exact one_mem _
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he1
    have hpZ : p ∈ zStarIn J := by
      rw [mem_zStarIn_iff hpJ, ← hqker]
      exact he
    exact ⟨⟨p, (hZ p).2 ⟨hpP, hpZ⟩⟩, rfl⟩
  refine ⟨isCyclic_of_surjective f hsurj, ?_⟩
  rw [← hZ4]
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv).symm

omit [Finite G] in
theorem realization_eq_of_mem {J H : Subgroup G}
    (hHN : H ≤ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {ψ : ↥H →* Equiv.Perm (Fin 42)} (hψR : ∀ h, ψ h ∈ R)
    (hψ : ∀ (h : ↥H) e, q (betaHat J (hHN h.2) e) = (ψ h)⁻¹ * q e * ψ h) (h : ↥H)
    (hJ : (h : G) ∈ J) : ψ h = q (jq J ⟨h, hJ⟩) := by
  have e1 : ∀ e, q (betaHat J (hHN h.2) e) =
      (q (jq J ⟨h, hJ⟩))⁻¹ * q e * ((q (jq J ⟨h, hJ⟩))⁻¹)⁻¹ := by
    intro e
    obtain ⟨j, rfl⟩ := jq_surjective J e
    rw [betaHat_jq, inv_inv]
    have hc : conjJ J (hHN h.2) j = (⟨h, hJ⟩ : ↥J)⁻¹ * j * ⟨h, hJ⟩ := Subtype.ext (by
      rw [coe_conjJ]
      rfl)
    rw [hc]
    simp only [map_mul, map_inv]
  have := realization_unique hqsurj (R.inv_mem (hψR h)) (R.inv_mem (S_le_R (hqS _)))
    (fun e => by rw [hψ, inv_inv]) e1
  exact inv_injective this

omit [Finite G] in
theorem inv_mul_mem_T0_of_realization {J P H : Subgroup G} (hHN : H ≤ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {ψ : ↥H →* Equiv.Perm (Fin 42)}
    (hψ : ∀ (h : ↥H) e, q (betaHat J (hHN h.2) e) = (ψ h)⁻¹ * q e * ψ h) (h : ↥H)
    (hhP : (h : G) ∈ normalizer (P : Set G)) : ∀ t ∈ T0, (ψ h)⁻¹ * t * ψ h ∈ T0 := by
  intro t ht
  obtain ⟨e, rfl⟩ := hqsurj t (T0_le_S ht)
  obtain ⟨p, hpP, hpJ, rfl⟩ := (hT _).1 ht
  rw [← hψ, betaHat_jq]
  exact (hT _).2 ⟨_, conj_mem_of_mem_normalizer hhP hpP, _, rfl⟩

omit [Finite G] in
theorem mul_inv_mem_T0_of_realization {J P H : Subgroup G} (hHN : H ≤ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {ψ : ↥H →* Equiv.Perm (Fin 42)}
    (hψ : ∀ (h : ↥H) e, q (betaHat J (hHN h.2) e) = (ψ h)⁻¹ * q e * ψ h) (h : ↥H)
    (hhP : (h : G) ∈ normalizer (P : Set G)) : ∀ t ∈ T0, ψ h * t * (ψ h)⁻¹ ∈ T0 := by
  intro t ht
  have h1 := inv_mul_mem_T0_of_realization hHN hqsurj hT hψ h⁻¹ (inv_mem hhP) t ht
  rwa [map_inv, inv_inv] at h1

omit [Finite G] in
theorem mem_withKernel_of_realization_mem_S {J H : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hHN : H ≤ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {ψ : ↥H →* Equiv.Perm (Fin 42)}
    (hψ : ∀ (h : ↥H) e, q (betaHat J (hHN h.2) e) = (ψ h)⁻¹ * q e * ψ h) (h : ↥H)
    (hS : ψ h ∈ S) : (h : G) ∈ withKernel J := by
  obtain ⟨e₀, he₀⟩ := hqsurj _ (S.inv_mem hS)
  exact mem_withKernel_of_realization hJ (hHN h.2) hqker (e₀ := e₀) fun e => by
    rw [hψ, he₀, inv_inv]

theorem mem_of_mem_withKernel {S J : Subgroup G} (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hinv : ∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) {y : G} (hyS : y ∈ S)
    (hyW : y ∈ withKernel J) (hyy : y * y = 1) : y ∈ J :=
  (mem_inf.mp (hinv y (inf_withKernel_le hS (mem_inf.mpr ⟨hyS, hyW⟩)) hyy)).2

end CFSG.ComponentClassification.GrSLit.GrS4

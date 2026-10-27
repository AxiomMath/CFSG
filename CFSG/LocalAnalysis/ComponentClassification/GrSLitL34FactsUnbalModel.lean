module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem mem_normalizer_of_closure [Finite G] {J : Subgroup G} {X : Set G}
    (h : closure {y | ∃ j ∈ J, ∃ d ∈ X, y = j⁻¹ * d⁻¹ * j * d} = J) {d : G} (hd : d ∈ X) :
    d ∈ normalizer (J : Set G) := by
  have hc : ∀ j ∈ J, d⁻¹ * j * d ∈ J := by
    intro j hj
    have h1 : j⁻¹ * d⁻¹ * j * d ∈ J := h ▸ subset_closure ⟨j, hj, d, hd, rfl⟩
    have := J.mul_mem hj h1
    rwa [show j * (j⁻¹ * d⁻¹ * j * d) = d⁻¹ * j * d by group] at this
  let φ : ↥J → ↥J := fun j => ⟨d⁻¹ * j * d, hc j j.2⟩
  have hinj : Function.Injective φ := fun a b hab => by
    have h1 : d⁻¹ * (a : G) * d = d⁻¹ * (b : G) * d := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨j, hj⟩ := hsurj ⟨g, hg⟩
    have hjg : d⁻¹ * (j : G) * d = g := congrArg Subtype.val hj
    rw [← hjg, show d * (d⁻¹ * (j : G) * d) * d⁻¹ = j by group]
    exact j.2
  · intro hg
    have := hc _ hg
    rwa [show d⁻¹ * (d * g * d⁻¹) * d = g by group] at this

theorem not_le_zStarIn [Finite G] {J : Subgroup G}
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) : ¬ J ≤ zStarIn J := by
  intro hle
  obtain ⟨q, -, hqsurj, hqker, -⟩ := exists_jq hL
  have hr₁ : r₁ ≠ 1 := fun h => by
    have := orderOf_r₁R
    have h1 : r₁R = 1 := Subtype.ext h
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨e, he⟩ := hqsurj r₁ r₁_mem_S
  obtain ⟨j, rfl⟩ := jq_surjective J e
  have hz := (mem_zStarIn_iff j.2).1 (hle j.2)
  rw [← hqker, MonoidHom.mem_ker] at hz
  exact hr₁ (he.symm.trans hz)

theorem false_of_closure_le [Finite G] {J : Subgroup G}
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {X : Set G}
    (h : closure {y | ∃ j ∈ J, ∃ d ∈ X, y = j⁻¹ * d⁻¹ * j * d} = J)
    (hX : ∀ d ∈ X, ∀ j ∈ J, j⁻¹ * d⁻¹ * j * d ∈ zStarIn J) : False := by
  apply not_le_zStarIn hL
  intro y hy
  rw [← h] at hy
  refine (closure_le (zStarIn J)).2 ?_ hy
  rintro _ ⟨j, hj, d, hd, rfl⟩
  exact hX d hd j hj

variable {J : Subgroup G} {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem comm_mem_zStarIn_of_realization (hqker : q.ker = center (Jhat J)) {d : G}
    (hd : d ∈ normalizer (J : Set G)) (h1 : ∀ e, q (betaHat J hd e) = q e) {j : G}
    (hj : j ∈ J) : j⁻¹ * d⁻¹ * j * d ∈ zStarIn J := by
  have hmem : j⁻¹ * d⁻¹ * j * d ∈ J := by
    have := conj_mem_of_mem_normalizer hd hj
    rw [show j⁻¹ * d⁻¹ * j * d = j⁻¹ * (d⁻¹ * j * d) by group]
    exact J.mul_mem (J.inv_mem hj) this
  rw [mem_zStarIn_iff hmem, ← hqker, MonoidHom.mem_ker]
  have e1 : (⟨j⁻¹ * d⁻¹ * j * d, hmem⟩ : J) = (⟨j, hj⟩ : J)⁻¹ * conjJ J hd ⟨j, hj⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, map_mul, map_inv, ← betaHat_jq, h1, inv_mul_cancel]

theorem eq_conj_of_realization (hJ : ⁅J, J⁆ = J) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat J)) {β : Jhat J ≃* Jhat J} {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ S) (hβ : ∀ e, q (β e) = s * q e * s⁻¹) :
    ∃ e₀ : Jhat J, q e₀ = s ∧ ∀ e, β e = e₀ * e * e₀⁻¹ := by
  obtain ⟨e₀, he₀⟩ := hqsurj s hs
  refine ⟨e₀, he₀, fun e => ?_⟩
  have hext : β.toMonoidHom = (MulAut.conj e₀).toMonoidHom := by
    apply hom_ext_of_central (commutator_jhat hJ) q (hqker ▸ le_refl _)
    refine MonoidHom.ext fun e => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    rw [hβ, he₀]
  have := DFunLike.congr_fun hext e
  simpa using this

theorem card_set_eq_of_realization [Finite G] {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {r : Equiv.Perm (Fin 42)} (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) :
    Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} =
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) * Nat.card (zStarIn J) := by
  set φ : ↥J →* Equiv.Perm (Fin 42) := q.comp (jq J) with hφ
  set C := centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S with hC
  have hCφ : C ≤ φ.range := by
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, he⟩
  have h1 := card_comap_eq φ C hCφ
  have hker : Nat.card φ.ker = Nat.card (zStarIn J) := by
    have hk : φ.ker = Open.fusionZStar J := by
      ext j
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hqker,
        ← mem_zStarIn_iff j.2, zStarIn, mem_map]
      constructor
      · rintro ⟨j', hj', hjj⟩
        rwa [Subtype.ext hjj] at hj'
      · intro hj
        exact ⟨j, hj, rfl⟩
    rw [hk, zStarIn, Subgroup.card_map_of_injective Subtype.val_injective]
  have hset : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = Nat.card (C.comap φ) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun j => ?_
    have hmem : (j : G)⁻¹ * x⁻¹ * j * x ∈ J := by
      have := conj_mem_of_mem_normalizer hxN j.2
      rw [show (j : G)⁻¹ * x⁻¹ * j * x = (j : G)⁻¹ * (x⁻¹ * j * x) by group]
      exact J.mul_mem (J.inv_mem j.2) this
    rw [mem_zStarIn_iff hmem]
    have e1 : (⟨(j : G)⁻¹ * x⁻¹ * j * x, hmem⟩ : J) = j⁻¹ * conjJ J hxN j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, ← hqker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, ← betaHat_jq, hr,
      mem_comap, hC, mem_inf, mem_centralizer_singleton_iff, inv_mul_conj_eq_one_iff]
    simp only [hφ, MonoidHom.comp_apply]
    exact ⟨fun h => ⟨h, hqS _⟩, fun h => h.1⟩
  rw [hset, h1, hker]


theorem realization_unique (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {β : Jhat J ≃* Jhat J}
    {ρ ρ' : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R) (hρ' : ρ' ∈ R)
    (h : ∀ e, q (β e) = ρ * q e * ρ⁻¹) (h' : ∀ e, q (β e) = ρ' * q e * ρ'⁻¹) : ρ = ρ' := by
  have hc : ρ⁻¹ * ρ' ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem (R.inv_mem hρ) hρ'⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have h1 := (h e).symm.trans (h' e)
    calc q e * (ρ⁻¹ * ρ') = ρ⁻¹ * (ρ * q e * ρ⁻¹) * ρ' := by group
      _ = ρ⁻¹ * (ρ' * q e * ρ'⁻¹) * ρ' := by rw [h1]
      _ = ρ⁻¹ * ρ' * q e := by group
  rw [centralizer_S_inf_R, mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem realization_comm (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {g h : G}
    (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G)) (hgh : g * h = h * g)
    {ρ σ : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R) (hσ : σ ∈ R)
    (hgρ : ∀ e, q (betaHat J hg e) = ρ * q e * ρ⁻¹)
    (hhσ : ∀ e, q (betaHat J hh e) = σ * q e * σ⁻¹) : ρ * σ = σ * ρ := by
  have h1 : ∀ e, q (betaHat J (mul_mem hg hh) e) = σ * ρ * q e * (σ * ρ)⁻¹ := by
    intro e
    rw [betaHat_mul J hg hh, hhσ, hgρ]
    group
  have h2 : ∀ e, q (betaHat J (mul_mem hg hh) e) = ρ * σ * q e * (ρ * σ)⁻¹ := by
    intro e
    rw [betaHat_congr J (mul_mem hg hh) (mul_mem hh hg) hgh, betaHat_mul J hh hg, hgρ, hhσ]
    group
  exact (realization_unique hqsurj (R.mul_mem hρ hσ) (R.mul_mem hσ hρ) h2 h1)

theorem realization_pow_odd [Finite G] (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {d : G}
    (hd : d ∈ normalizer (J : Set G)) (hodd : Nat.Coprime 2 (orderOf d))
    {ρ : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R) (hdρ : ∀ e, q (betaHat J hd e) = ρ * q e * ρ⁻¹) :
    ρ ^ 945 = 1 := by
  have hρn : ρ ^ orderOf d = 1 := by
    have h1 : ∀ e, q (betaHat J (pow_mem hd (orderOf d)) e) = 1 * q e * 1⁻¹ := by
      intro e
      rw [betaHat_eq_self J _ (pow_orderOf_eq_one d)]
      group
    exact (realization_unique hqsurj (pow_mem hρ _) R.one_mem (betaHat_pow hd hdρ _) h1)
  have hdvd : orderOf (⟨ρ, hρ⟩ : R) ∣ orderOf d := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hρn))
  have hR : orderOf (⟨ρ, hρ⟩ : R) ∣ 2 ^ 8 * 945 := by
    have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : R)
    rwa [card_R] at this
  have hcop : Nat.Coprime (orderOf (⟨ρ, hρ⟩ : R)) (2 ^ 8) :=
    Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_right 8 hodd.symm)
  have h945 : orderOf (⟨ρ, hρ⟩ : R) ∣ 945 := hcop.dvd_of_dvd_mul_left hR
  have := orderOf_dvd_iff_pow_eq_one.1 h945
  simpa using congrArg Subtype.val this

end CFSG.ComponentClassification.GrSLit.L34Facts

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutR1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutFacts

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal]

theorem fi24OutR_twoAdic_map_subtype (H : Subgroup G) (S : Subgroup H) :
    twoAdic (S.map H.subtype) = twoAdic S := by
  unfold twoAdic
  rw [Subgroup.card_map_of_injective H.subtype_injective]

theorem fi24OutR_std_of (hM : AutModel N (⊤ : Subgroup G)) {t : G} (ht : t * t = 1)
    (hidx : ∀ a : G, a ∉ N → a * t ∈ N)
    (hfus : ∀ w : G, w * w = 1 → ∃ n ∈ N, w * (n * t * n⁻¹) = n * t * n⁻¹ * w)
    (hpair : ∃ n ∈ N, t * n * t⁻¹ * n⁻¹ ≠ 1 ∧
      t * n * t⁻¹ * n⁻¹ * t = t * (t * n * t⁻¹ * n⁻¹) ∧
      twoAdic (N ⊓ centralizer {t} ⊓ centralizer {t * n * t⁻¹ * n⁻¹}) =
        twoAdic (N ⊓ centralizer {t}))
    (hco : IsCoatom ((N ⊓ centralizer {t}).subgroupOf N))
    (hinner : AllInner ↥(N ⊓ centralizer {t})) (hZ : center ↥(N ⊓ centralizer {t}) = ⊥)
    (hcard : Nat.card ↥(N ⊓ centralizer {t}) ≤ 4089470473293004800) :
    Fi24OutFacts N (MulAut.conjNormal t) := by
  refine ⟨by rw [← map_mul, ht, map_one], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨w, rfl⟩ := fi24OutR_conjNormal_surjective hM σ
    have hw : w * w = 1 := fi24OutR_conjNormal_injective hM (by rw [map_mul, hσ, map_one])
    obtain ⟨n, hn, hwn⟩ := hfus w hw
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [fi24OutR_conj_mul_conjNormal, ← map_mul, ← map_mul]
    exact congrArg _ hwn.symm
  · obtain ⟨n, hn, h1, h2, h3⟩ := hpair
    have hm : ((MulAut.conjNormal t ⟨n, hn⟩ * (⟨n, hn⟩ : N)⁻¹ : N) : G) =
        t * n * t⁻¹ * n⁻¹ := by
      rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
    refine ⟨⟨n, hn⟩, fun h => h1 (by rw [← hm, h]; rfl),
      (fi24OutR_mem_fixSubgroup_iff t _).2 (by rw [hm]; exact h2), ?_⟩
    rw [← fi24OutR_twoAdic_map_subtype N, ← fi24OutR_twoAdic_map_subtype N (fixSubgroup _),
      Subgroup.map_inf _ _ _ N.subtype_injective, fi24OutR_map_fixSubgroup,
      fi24OutR_map_centralizer, hm]
    have e : N ⊓ centralizer {t} ⊓ (N ⊓ centralizer {t * n * t⁻¹ * n⁻¹}) =
        N ⊓ centralizer {t} ⊓ centralizer {t * n * t⁻¹ * n⁻¹} := by
      ext x
      simp only [mem_inf]
      tauto
    rw [e]
    exact h3
  · intro α hα
    obtain ⟨r, rfl⟩ := fi24OutR_conjNormal_surjective hM α
    have hrt : r * t = t * r :=
      fi24OutR_conjNormal_injective hM (by rw [map_mul, map_mul, hα])
    by_cases hr : r ∈ N
    · exact ⟨⟨r, hr⟩, (fi24OutR_mem_fixSubgroup_iff t _).2 hrt,
        Or.inl (fi24OutR_conjNormal_coe ⟨r, hr⟩)⟩
    · refine ⟨⟨r * t, hidx r hr⟩, (fi24OutR_mem_fixSubgroup_iff t _).2 ?_, Or.inr ?_⟩
      · show r * t * t = t * (r * t)
        rw [← mul_assoc, ← hrt]
      · rw [← fi24OutR_conjNormal_coe, ← map_mul]
        congr 1
        show r = t * (r * t)
        calc r = r * (t * t) := by rw [ht, mul_one]
          _ = r * t * t := by rw [mul_assoc]
          _ = t * r * t := by rw [hrt]
          _ = t * (r * t) := by rw [mul_assoc]
  · rw [fi24OutR_fixSubgroup_eq_subgroupOf]
    exact hco
  · exact AllInner.of_mulEquiv (fi24OutR_fixEquiv t).symm hinner
  · exact fi24out_center_eq_bot_of_equiv (fi24OutR_fixEquiv t).symm hZ
  · rw [Nat.card_congr (fi24OutR_fixEquiv t).toEquiv]
    exact hcard

theorem fi24OutR_false_of_commute [Finite G] {t : G} (ht : t * t = 1) (htN : t ∉ N)
    (hidx2 : ∀ a b : G, a ∉ N → b ∉ N → a * b ∈ N) (hZ : center ↥(N ⊓ centralizer {t}) = ⊥)
    {n₁ n₂ : G} (hne : n₁ * t * n₁⁻¹ ≠ n₂ * t * n₂⁻¹)
    (hc : n₁ * t * n₁⁻¹ * (n₂ * t * n₂⁻¹) = n₂ * t * n₂⁻¹ * (n₁ * t * n₁⁻¹))
    {S : Subgroup G} (hSN : S ≤ N) (hS₁ : ∀ s ∈ S, s * (n₁ * t * n₁⁻¹) = n₁ * t * n₁⁻¹ * s)
    (hS₂ : ∀ s ∈ S, s * (n₂ * t * n₂⁻¹) = n₂ * t * n₂⁻¹ * s)
    (hcard : Nat.card ↥(N ⊓ centralizer {t}) ≤ Nat.card S) : False := by
  have hnorm : N.Normal := inferInstance
  have hS'le : S.map (MulAut.conj n₁⁻¹).toMonoidHom ≤ N ⊓ centralizer {t} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hnorm.conj_mem s (hSN hs) n₁⁻¹, mem_centralizer_singleton_iff.2 ?_⟩
    show n₁⁻¹ * s * n₁⁻¹⁻¹ * t = t * (n₁⁻¹ * s * n₁⁻¹⁻¹)
    calc n₁⁻¹ * s * n₁⁻¹⁻¹ * t = n₁⁻¹ * (s * (n₁ * t * n₁⁻¹)) * n₁ := by group
      _ = n₁⁻¹ * (n₁ * t * n₁⁻¹ * s) * n₁ := by rw [hS₁ s hs]
      _ = t * (n₁⁻¹ * s * n₁⁻¹⁻¹) := by group
  have hEq : S.map (MulAut.conj n₁⁻¹).toMonoidHom = N ⊓ centralizer {t} :=
    Subgroup.eq_of_le_of_card_ge hS'le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj n₁⁻¹).injective]
      exact hcard)
  obtain ⟨y, hy⟩ : ∃ y : G, y = n₁⁻¹ * (n₂ * t * n₂⁻¹) * n₁ := ⟨_, rfl⟩
  have hyN : y ∉ N := fun h => htN (by
    have h' := hnorm.conj_mem y h (n₂⁻¹ * n₁)
    rwa [show n₂⁻¹ * n₁ * y * (n₂⁻¹ * n₁)⁻¹ = t by rw [hy]; group] at h')
  have hyt : y ≠ t := fun h => hne (by
    calc n₁ * t * n₁⁻¹ = n₁ * y * n₁⁻¹ := by rw [h]
      _ = n₂ * t * n₂⁻¹ := by rw [hy]; group)
  have hyc : y * t = t * y := by
    calc y * t = n₁⁻¹ * (n₂ * t * n₂⁻¹ * (n₁ * t * n₁⁻¹)) * n₁ := by rw [hy]; group
      _ = n₁⁻¹ * (n₁ * t * n₁⁻¹ * (n₂ * t * n₂⁻¹)) * n₁ := by rw [hc]
      _ = t * y := by rw [hy]; group
  have hall : ∀ m ∈ N ⊓ centralizer {t}, m * y = y * m := by
    intro m hm
    rw [← hEq] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    show n₁⁻¹ * s * n₁⁻¹⁻¹ * y = y * (n₁⁻¹ * s * n₁⁻¹⁻¹)
    calc n₁⁻¹ * s * n₁⁻¹⁻¹ * y = n₁⁻¹ * (s * (n₂ * t * n₂⁻¹)) * n₁ := by rw [hy]; group
      _ = n₁⁻¹ * (n₂ * t * n₂⁻¹ * s) * n₁ := by rw [hS₂ s hs]
      _ = y * (n₁⁻¹ * s * n₁⁻¹⁻¹) := by rw [hy]; group
  have hzC : y * t ∈ centralizer {t} := mem_centralizer_singleton_iff.2 (by
    calc y * t * t = t * y * t := by rw [hyc]
      _ = t * (y * t) := by group)
  have hz : (⟨y * t, hidx2 y t hyN htN, hzC⟩ : ↥(N ⊓ centralizer {t})) ∈
      center ↥(N ⊓ centralizer {t}) := by
    rw [mem_center_iff]
    intro m
    apply Subtype.ext
    show (m : G) * (y * t) = y * t * m
    have h2 : (m : G) * t = t * m := mem_centralizer_singleton_iff.1 (mem_inf.1 m.2).2
    calc (m : G) * (y * t) = m * y * t := by group
      _ = y * m * t := by rw [hall m m.2]
      _ = y * (m * t) := by group
      _ = y * (t * m) := by rw [h2]
      _ = y * t * m := by group
  rw [hZ, mem_bot] at hz
  have h1 : y * t = 1 := congrArg Subtype.val hz
  exact hyt (by calc y = y * t * t := by rw [mul_assoc, ht, mul_one]
    _ = t := by rw [h1, one_mul])

theorem fi24OutR_class_of [Finite G] (hM : AutModel N (⊤ : Subgroup G)) {t : G} (ht : t * t = 1)
    (htN : t ∉ N) (hidx2 : ∀ a b : G, a ∉ N → b ∉ N → a * b ∈ N)
    (hstd : Fi24OutFacts N (MulAut.conjNormal t)) (hZ : center ↥(N ⊓ centralizer {t}) = ⊥)
    (hcardC : Nat.card ↥(N ⊓ centralizer {t}) = 4089470473293004800)
    (hcases : ∀ w : G, w * w = 1 → w ∉ N → (∃ n ∈ N, w = n * t * n⁻¹) ∨
      ∃ n₁ n₂ x₃ : G, n₁ * t * n₁⁻¹ ≠ n₂ * t * n₂⁻¹ ∧
        n₁ * t * n₁⁻¹ * (n₂ * t * n₂⁻¹) = n₂ * t * n₂⁻¹ * (n₁ * t * n₁⁻¹) ∧
        ∀ c : G, c * w = w * c → ∀ x ∈ ({n₁ * t * n₁⁻¹, n₂ * t * n₂⁻¹, x₃} : Set G),
          c * x * c⁻¹ ∈ ({n₁ * t * n₁⁻¹, n₂ * t * n₂⁻¹, x₃} : Set G))
    {ν : MulAut N} (hν : ν * ν = 1) (hnot : ¬ ∃ g : N, ν = MulAut.conj g) {B : Subgroup N}
    (hB : B ≤ fixSubgroup ν) (hperf : ⁅B, B⁆ = B) (hcard : 4089470473293004800 ≤ Nat.card B) :
    Fi24OutFacts N ν ∧ B = fixSubgroup ν := by
  obtain ⟨τ, rfl⟩ := fi24OutR_conjNormal_surjective hM ν
  have hττ : τ * τ = 1 := fi24OutR_conjNormal_injective hM (by rw [map_mul, hν, map_one])
  have hτN : τ ∉ N := fun h => hnot ⟨⟨τ, h⟩, fi24OutR_conjNormal_coe ⟨τ, h⟩⟩
  rcases hcases τ hττ hτN with ⟨n, hn, hτ⟩ | ⟨n₁, n₂, x₃, hne, hc, hperm⟩
  · have e : (MulAut.conjNormal τ : MulAut N) =
        MulAut.conj (⟨n, hn⟩ : N) * MulAut.conjNormal t * (MulAut.conj (⟨n, hn⟩ : N))⁻¹ := by
      rw [fi24OutR_conj_mul_conjNormal, hτ]
    have F : Fi24OutFacts N (MulAut.conjNormal τ) := by
      rw [e]
      exact hstd.conj _
    exact ⟨F, Subgroup.eq_of_le_of_card_ge hB (F.card_le.trans hcard)⟩
  · exfalso
    have hB'τ : ∀ b ∈ B.map N.subtype, b * τ = τ * b := by
      rintro _ ⟨p, hp, rfl⟩
      exact (fi24OutR_mem_fixSubgroup_iff τ p).1 (hB hp)
    have hperf' : ⁅B.map N.subtype, B.map N.subtype⁆ = B.map N.subtype := by
      rw [← Subgroup.map_commutator, hperf]
    have hfix := fi24OutR_conj_eq_of_perfect hperf' fun b hb x hx => hperm b (hB'τ b hb) x hx
    have hcomm : ∀ b ∈ B.map N.subtype,
        ∀ x ∈ ({n₁ * t * n₁⁻¹, n₂ * t * n₂⁻¹, x₃} : Set G), b * x = x * b := by
      intro b hb x hx
      calc b * x = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [hfix b hb x hx]
    refine fi24OutR_false_of_commute ht htN hidx2 hZ hne hc (S := B.map N.subtype) ?_
      (fun s hs => hcomm s hs _ (Set.mem_insert _ _))
      (fun s hs => hcomm s hs _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) ?_
    · rintro _ ⟨p, -, rfl⟩
      exact p.2
    · rw [hcardC, Subgroup.card_map_of_injective N.subtype_injective]
      exact hcard

theorem fi24OutR_class_transport {Y P : Type} [Group Y] [Group P] (e : Y ≃* P)
    (hclass : ∀ ν : MulAut P, ν * ν = 1 → (¬ ∃ g : P, ν = MulAut.conj g) → ∀ B : Subgroup P,
      B ≤ fixSubgroup ν → ⁅B, B⁆ = B → 4089470473293004800 ≤ Nat.card B →
        Fi24OutFacts P ν ∧ B = fixSubgroup ν)
    {ν : MulAut Y} (hν : ν * ν = 1) (hnot : ¬ ∃ g : Y, ν = MulAut.conj g) {B : Subgroup Y}
    (hB : B ≤ fixSubgroup ν) (hperf : ⁅B, B⁆ = B) (hcard : 4089470473293004800 ≤ Nat.card B) :
    Fi24OutFacts Y ν ∧ B = fixSubgroup ν := by
  have hν' : MulAut.congr e ν * MulAut.congr e ν = 1 := by rw [← map_mul, hν, map_one]
  have hnot' : ¬ ∃ g : P, MulAut.congr e ν = MulAut.conj g := by
    rintro ⟨g, hg⟩
    refine hnot ⟨e.symm g, (MulAut.congr e).injective ?_⟩
    rw [hg, fi24out_congr_conj, e.apply_symm_apply]
  have hB' : B.map e.toMonoidHom ≤ fixSubgroup (MulAut.congr e ν) := by
    rw [fi24out_fixSubgroup_congr]
    exact Subgroup.map_mono hB
  have hperf' : ⁅B.map e.toMonoidHom, B.map e.toMonoidHom⁆ = B.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hcard' : 4089470473293004800 ≤ Nat.card (B.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  obtain ⟨hF, hBeq⟩ := hclass _ hν' hnot' _ hB' hperf' hcard'
  refine ⟨?_, ?_⟩
  · have h := hF.of_mulEquiv e.symm
    have hνν : MulAut.congr e.symm (MulAut.congr e ν) = ν := by
      ext y
      simp [MulAut.congr_apply]
    rwa [hνν] at h
  · rw [fi24out_fixSubgroup_congr] at hBeq
    exact Subgroup.map_injective e.injective hBeq

end CFSG.EvenSporadicStandard.Induction

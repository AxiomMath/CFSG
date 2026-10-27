module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section
namespace CFSG.AGLEmbedding

open CFSG.RankThreeCoreUniqueness.Helpers

section Cover

variable {B : Type*} [Group B] [Finite B]

omit [Finite B] in
theorem le_perfectResidualOf_of_perfect' {H Q : Subgroup B} (hQH : Q ≤ H) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ perfectResidualOf H := by
  have hQ' : ⁅Q.subgroupOf H, Q.subgroupOf H⁆ = Q.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQH, hQ]
  have hd : ∀ n : ℕ, Q.subgroupOf H ≤ derivedSeries H n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hQ']
      exact Subgroup.commutator_mono ih ih
  intro q hq
  refine ⟨⟨q, hQH hq⟩, ?_, rfl⟩
  exact Subgroup.mem_iInf.mpr fun n => hd n (Subgroup.mem_subgroupOf.mpr hq)

omit [Finite B] in
theorem pow_dvd_card_of_le_sup {p k : ℕ} {D N V : Subgroup B} [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hV : V ≤ D ⊔ N) (hk : p ^ k ∣ Nat.card V) :
    p ^ k ∣ Nat.card D := by
  have h1 : Nat.card (D ⊔ N : Subgroup B) = N.relIndex D * Nat.card N := by
    rw [← Subgroup.relIndex_sup_right D N, ← Subgroup.relIndex_mul_card N (D ⊔ N),
      inf_of_le_left le_sup_right]
  have h2 : p ^ k ∣ N.relIndex D * Nat.card N :=
    h1 ▸ hk.trans (Subgroup.card_dvd_of_le hV)
  exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k hN) h2).trans
    (Subgroup.relIndex_dvd_card N D)

omit [Finite B] in
theorem mem_of_mul_mem_of_coprime_of_normalizer {p : ℕ} {D : Subgroup B} {d n : B} (hd : d ∈ D)
    (hnD : n ∈ Subgroup.normalizer (D : Set B)) (hn : Nat.Coprime p (orderOf n))
    (hx : (d * n) ^ p = 1) : d * n ∈ D := by
  have hpow : ∀ k : ℕ, ∃ d' ∈ D, (d * n) ^ k = d' * n ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, D.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨d', hd', he⟩ := ih
      have hconj : n ^ k * d * (n ^ k)⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hnD k) d).mp hd
      refine ⟨d' * (n ^ k * d * (n ^ k)⁻¹), D.mul_mem hd' hconj, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨d', hd', he⟩ := hpow p
  have hnp : n ^ p ∈ D := by
    have h1 : n ^ p = d'⁻¹ := by
      rw [hx] at he
      exact (eq_inv_of_mul_eq_one_right he.symm)
    rw [h1]
    exact D.inv_mem hd'
  have hnD' : n ∈ D :=
    (Subgroup.zpowers_le.mpr hnp) (mem_zpowers_pow_iff.mpr hn)
  exact D.mul_mem hd hnD'

theorem exists_perfect_centralizer_cover {p : ℕ} [Fact p.Prime] (N : Subgroup B) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (A : Subgroup B) (hA : IsPGroup p A) :
    ∃ D : Subgroup B, ⁅D, D⁆ = D ∧ D ≤ Subgroup.centralizer (A : Set B) ∧
      (∀ V : Subgroup B, ⁅V, V⁆ = V →
        V.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer
          ((A.map (QuotientGroup.mk' N) : Subgroup (B ⧸ N)) : Set (B ⧸ N)) →
        V ≤ D ⊔ N) ∧
      ∀ x ∈ Subgroup.centralizer (A : Set B), x ^ p = 1 →
        ∀ V : Subgroup B, ⁅V, V⁆ = V →
          V.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer
            ((A.map (QuotientGroup.mk' N) : Subgroup (B ⧸ N)) : Set (B ⧸ N)) →
          QuotientGroup.mk' N x ∈ V.map (QuotientGroup.mk' N) → x ∈ D := by
  set π := QuotientGroup.mk' N with hπ
  set Γ := Subgroup.centralizer ((A.map π : Subgroup (B ⧸ N)) : Set (B ⧸ N)) with hΓ
  set Γi := perfectResidualOf Γ with hΓi
  set Y := Subgroup.centralizer (A : Set B) ⊓ Γi.comap π with hY
  set D := perfectResidualOf Y with hD
  have hlift := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p N hN A hA
  have hΓiΓ : Γi ≤ Γ := Subgroup.map_subtype_le _
  set ψ : Y →* Γi := (π.comp Y.subtype).codRestrict Γi (fun y => y.2.2) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨γ, hγ⟩
    have hγΓ : γ ∈ (Subgroup.centralizer (A : Set B)).map π := by
      rw [hlift]
      exact hΓiΓ hγ
    obtain ⟨c, hc, hcγ⟩ := hγΓ
    refine ⟨⟨c, hc, ?_⟩, Subtype.ext ?_⟩
    · change π c ∈ Γi
      rw [hcγ]
      exact hγ
    · exact hcγ
  have hΓip : Group.IsPerfect Γi := finite_perfectResidualOf_isPerfect Γ
  have hsurj := finite_perfectResidual_surjects_to_perfect_image ψ hψs
  have hπD : D.map π = Γi := by
    have e1 : D.map π = ((perfectResidual Y).map ψ).map Γi.subtype := by
      rw [hD, perfectResidualOf, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [e1, hsurj, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDp : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect Y)
  have hDY : D ≤ Y := Subgroup.map_subtype_le _
  have hVΓi : ∀ V : Subgroup B, ⁅V, V⁆ = V → V.map π ≤ Γ → V.map π ≤ Γi := fun V hV hVΓ =>
    le_perfectResidualOf_of_perfect' hVΓ (by rw [← Subgroup.map_commutator, hV])
  refine ⟨D, hDp, hDY.trans inf_le_left, fun V hV hVΓ => ?_, fun x hxA hxp V hV hVΓ hxV => ?_⟩
  · intro v hv
    have hπv : π v ∈ D.map π := hπD ▸ hVΓi V hV hVΓ ⟨v, hv, rfl⟩
    obtain ⟨d, hd, hdv⟩ := hπv
    have hn : d⁻¹ * v ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hdv, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hd hn
    rwa [mul_inv_cancel_left] at this
  · have hxi : π x ∈ Γi := hVΓi V hV hVΓ hxV
    have hxY : x ∈ Y := ⟨hxA, hxi⟩
    obtain ⟨d, hd, hdx⟩ := (hπD ▸ hxi : π x ∈ D.map π)
    set n := d⁻¹ * x with hn
    have hnN : n ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    have hnY : n ∈ Y := Y.mul_mem (Y.inv_mem (hDY hd)) hxY
    have hnD : n ∈ Subgroup.normalizer (D : Set B) :=
      perfectResidualOf_normalizer_contains Y (Subgroup.le_normalizer hnY)
    have hcop : Nat.Coprime p (orderOf n) :=
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hnN)
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN))
    have hdn : d * n = x := by rw [hn, mul_inv_cancel_left]
    have := mem_of_mul_mem_of_coprime_of_normalizer hd hnD hcop (by rw [hdn]; exact hxp)
    rwa [hdn] at this

end Cover

end CFSG.AGLEmbedding

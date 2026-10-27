module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.TwoNormalized.Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.A6Model

namespace TwoNormalized

theorem exists_model_elements {K : Type} [Group K] [Finite K] (hK : IsRankThreeA6 K)
    (Q : Sylow 3 K) :
    (∀ t ∈ (Q : Subgroup K), t ≠ 1 → ∀ k : K, k * t = t * k → k ∈ (Q : Subgroup K)) ∧
    ∃ u ∈ (Q : Subgroup K), u ≠ 1 ∧ ∃ n ∈ normalizer ((Q : Subgroup K) : Set K),
      ∃ w : K, w ∉ normalizer ((Q : Subgroup K) : Set K) ∧ w * n = n⁻¹ * w ∧
        (w * u) ^ 3 = 1 ∧ ∀ y : K, y * n = n⁻¹ * y → (y * u) ^ 3 = 1 → y = w := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_of_sylow hK Q
  have hmemQ : ∀ x : PSL29, Φ x ∈ (Q : Subgroup K) ↔ x ∈ uHom.range := by
    intro x
    rw [hΦ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmemN : ∀ x : PSL29, Φ x ∈ normalizer ((Q : Subgroup K) : Set K) ↔
      x ∈ normalizer (uHom.range : Set PSL29) := by
    intro x
    rw [hΦ, ← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
  refine ⟨fun t ht ht1 k hk => ?_, Φ (ut 1), (hmemQ _).mpr (mem_range_iff.mpr ⟨1, rfl⟩), ?_,
    Φ hb, (hmemN _).mpr hb_mem_normalizer, Φ wb,
    fun h => wb_not_mem_normalizer ((hmemN _).mp h), ?_, ?_, fun y hy1 hy2 => ?_⟩
  · obtain ⟨x, rfl⟩ := Φ.surjective t
    obtain ⟨a, rfl⟩ := mem_range_iff.mp ((hmemQ x).mp ht)
    have ha : a ≠ 0 := by
      rintro rfl
      exact ht1 (by rw [ut_zero, map_one])
    obtain ⟨g, rfl⟩ := Φ.surjective k
    rw [← map_mul, ← map_mul] at hk
    exact (hmemQ g).mpr (mem_range_of_commute ha (Φ.injective hk))
  · rw [Ne, MulEquiv.map_eq_one_iff]
    intro h
    exact one_ne_zero (ut_inj (h.trans ut_zero.symm))
  · rw [← map_inv, ← map_mul, ← map_mul, wb_mul_hb]
  · rw [← map_mul, ← map_pow, wb_ut_cube, map_one]
  · obtain ⟨g, rfl⟩ := Φ.surjective y
    rw [← map_inv, ← map_mul, ← map_mul] at hy1
    rw [← map_mul, ← map_pow, MulEquiv.map_eq_one_iff] at hy2
    rw [eq_wb (Φ.injective hy1) hy2]

theorem mulAut_eq_one {K : Type} [Group K] [Finite K] (hK : IsRankThreeA6 K) (Q : Sylow 3 K)
    (ψ : MulAut K) (hψ : ∀ x, ψ (ψ x) = x) (hfix : ∀ t ∈ (Q : Subgroup K), ψ t = t) :
    ψ = 1 := by
  obtain ⟨hcent, u, huQ, hu1, n, hnN, w, hwN, hwn, hwu, huniq⟩ := exists_model_elements hK Q
  obtain ⟨hQel, -, hmax⟩ := a6SylowData_proved K hK Q
  have hN : ∀ m ∈ normalizer ((Q : Subgroup K) : Set K), ψ m = m := by
    intro m hm
    have h1 : m * u * m⁻¹ ∈ (Q : Subgroup K) := (mem_normalizer_iff.mp hm u).mp huQ
    have h2 : ψ m * u * (ψ m)⁻¹ = m * u * m⁻¹ := by
      have := hfix _ h1
      rwa [map_mul, map_mul, map_inv, hfix u huQ] at this
    set c := m⁻¹ * ψ m with hc
    have hcQ : c ∈ (Q : Subgroup K) := by
      refine hcent u huQ hu1 _ ?_
      calc m⁻¹ * ψ m * u = m⁻¹ * (ψ m * u * (ψ m)⁻¹) * ψ m := by group
        _ = m⁻¹ * (m * u * m⁻¹) * ψ m := by rw [h2]
        _ = u * (m⁻¹ * ψ m) := by group
    have hψc : ψ c = c := hfix _ hcQ
    have hmc : ψ m = m * c := by rw [hc]; group
    have hc2 : c * c = 1 := by
      have h3 := hψ m
      rw [hmc, map_mul, hmc, hψc] at h3
      calc c * c = m⁻¹ * (m * c * c) := by group
        _ = 1 := by rw [h3]; group
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c * c)⁻¹ := by group
        _ = 1 := by rw [hQel.2 c hcQ, hc2]; group
    rw [hmc, hc1, mul_one]
  have hψn : ψ n = n := hN n hnN
  have hψw : ψ w = w := by
    refine huniq (ψ w) ?_ ?_
    · have := congrArg ψ hwn
      rwa [map_mul, map_mul, map_inv, hψn] at this
    · have := congrArg ψ hwu
      rwa [map_pow, map_mul, hfix u huQ, map_one] at this
  let F : Subgroup K := MonoidHom.eqLocus ψ.toMonoidHom (MonoidHom.id K)
  have hmemF : ∀ x, x ∈ F ↔ ψ x = x := fun x => Iff.rfl
  have hNF : normalizer ((Q : Subgroup K) : Set K) ≤ F := fun m hm => (hmemF m).mpr (hN m hm)
  rcases hmax F hNF with h | h
  · exact absurd (h ▸ (hmemF w).mpr hψw) hwN
  · ext x
    exact (hmemF x).mp (h ▸ Subgroup.mem_top x)

end TwoNormalized

open TwoNormalized in
theorem kFactA6TwoNormalized_holds : KFactA6TwoNormalized := by
  intro X _ _ K hKn hC hKA T hTsyl S hS hTS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : K.Normal := hKn
  have hTp : IsPGroup 3 T := hTsyl.isPGroup
  have hTK : T ≤ K := hTsyl.le
  obtain ⟨Q, hQ⟩ := hTsyl
  obtain ⟨hcent, -⟩ := exists_model_elements hKA Q
  obtain ⟨-, hQcard, -⟩ := a6SylowData_proved ↥K hKA Q
  have hK360 : Nat.card K = 360 := by
    obtain ⟨e⟩ := nonempty_equiv hKA
    rw [Nat.card_congr e.toEquiv, psl29_card]
  have hTmem : ∀ x : X, x ∈ T ↔ ∃ t ∈ (Q : Subgroup ↥K), (t : X) = x := by
    intro x
    rw [← hQ, Subgroup.mem_map]
    rfl
  have hSK : ∀ r ∈ S, r ∈ K → r = 1 := by
    intro r hrS hrK
    by_contra hr1
    have hconj : ∀ t : (Q : Subgroup ↥K), ((t : ↥K) : X) * r * ((t : ↥K) : X)⁻¹ ∈ S ⊓ K := by
      intro t
      have htT : ((t : ↥K) : X) ∈ T := (hTmem _).mpr ⟨t, t.2, rfl⟩
      exact ⟨(mem_normalizer_iff.mp (hTS htT) r).mp hrS,
        K.mul_mem (K.mul_mem (t : ↥K).2 hrK) (K.inv_mem (t : ↥K).2)⟩
    let f : ↥(Q : Subgroup ↥K) → ↥(S ⊓ K : Subgroup X) := fun t => ⟨_, hconj t⟩
    have hf : Function.Injective f := by
      intro t₁ t₂ h12
      have h : ((t₁ : ↥K) : X) * r * ((t₁ : ↥K) : X)⁻¹ =
          ((t₂ : ↥K) : X) * r * ((t₂ : ↥K) : X)⁻¹ := congrArg Subtype.val h12
      by_contra hne
      have hτ1 : (t₂ : ↥K)⁻¹ * (t₁ : ↥K) ≠ 1 := by
        intro h1
        exact hne (Subtype.ext (inv_mul_eq_one.mp h1).symm)
      have hτQ : (t₂ : ↥K)⁻¹ * (t₁ : ↥K) ∈ (Q : Subgroup ↥K) := Q.mul_mem (Q.inv_mem t₂.2) t₁.2
      have hcomm : (⟨r, hrK⟩ : ↥K) * ((t₂ : ↥K)⁻¹ * t₁) = ((t₂ : ↥K)⁻¹ * t₁) * ⟨r, hrK⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc r * (((t₂ : ↥K) : X)⁻¹ * ((t₁ : ↥K) : X))
            = ((t₂ : ↥K) : X)⁻¹ * (((t₂ : ↥K) : X) * r * ((t₂ : ↥K) : X)⁻¹) *
                ((t₁ : ↥K) : X) := by group
          _ = ((t₂ : ↥K) : X)⁻¹ * (((t₁ : ↥K) : X) * r * ((t₁ : ↥K) : X)⁻¹) *
                ((t₁ : ↥K) : X) := by rw [h]
          _ = (((t₂ : ↥K) : X)⁻¹ * ((t₁ : ↥K) : X)) * r := by group
      have hrT : r ∈ T := (hTmem r).mpr ⟨_, hcent _ hτQ hτ1 _ hcomm, rfl⟩
      exact hr1 (Subgroup.disjoint_def.mp
        (IsPGroup.disjoint_of_ne 2 3 (by norm_num) S T hS hTp) hrS hrT)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [hQcard] at h1
    have h2 : Nat.card (S ⊓ K : Subgroup X) ≤ 8 := by
      obtain ⟨k, hk⟩ := (hS.to_inf_left (K := K)).exists_card_eq
      have hdvd : Nat.card (S ⊓ K : Subgroup X) ∣ 360 := by
        rw [← hK360]
        exact Subgroup.card_dvd_of_le inf_le_right
      rw [hk] at hdvd ⊢
      have hk3 : k ≤ 3 := by
        by_contra hk3
        have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
        have := h16.trans hdvd
        norm_num at this
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    omega
  have hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    have htK : t ∈ K := hTK ht
    have hc : s * t * s⁻¹ * t⁻¹ = 1 := by
      refine hSK _ ?_ (K.mul_mem (hKn.conj_mem t htK s) (K.inv_mem htK))
      have h1 : t * s⁻¹ * t⁻¹ ∈ S := (mem_normalizer_iff.mp (hTS ht) s⁻¹).mp (S.inv_mem hs)
      have h2 := S.mul_mem hs h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [hc, one_mul]
  have hinv : ∀ s ∈ S, s * s = 1 → s = 1 := by
    intro s hs hs2
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hψ : ∀ x : ↥K, MulAut.conjNormal s (MulAut.conjNormal s x) = x := by
      intro x
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, hsi]
      calc s * (s * (x : X) * s) * s = (s * s) * (x : X) * (s * s) := by group
        _ = x := by rw [hs2]; group
    have hfix : ∀ t ∈ (Q : Subgroup ↥K), MulAut.conjNormal s t = t := by
      intro t ht
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      rw [hST s hs _ ((hTmem _).mpr ⟨t, ht, rfl⟩)]
      group
    have h1 := mulAut_eq_one hKA Q (MulAut.conjNormal s) hψ hfix
    have hsC : s ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro k hk
      have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc k * s = (s * k * s⁻¹) * s := by rw [h2]
        _ = s * k := by group
    rw [hC] at hsC
    exact Subgroup.mem_bot.mp hsC
  by_contra hne
  have hcard : Nat.card S ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (hS.card_eq_or_dvd.resolve_left hcard)
  have hx2 : (x : X) * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg Subtype.val h
  have hx1 : x = 1 := Subtype.ext (hinv x x.2 hx2)
  rw [hx1, orderOf_one] at hx
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.A6

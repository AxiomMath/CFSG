module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Setting

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_three_elt {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hK : SecProp K A (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) :
    ∃ k ∈ K, orderOf k = 3 := by
  obtain ⟨hn, ⟨e⟩⟩ := hK
  have hcard : Nat.card (↥K ⧸ A.subgroupOf K) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hdvd : 3 ∣ Nat.card ↥K := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf K)
    rw [hcard] at h
    rw [h]
    exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _
  obtain ⟨k₀, hk₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥K) 3 (hp := ⟨Nat.prime_three⟩) hdvd
  exact ⟨k₀, k₀.2, (Subgroup.orderOf_coe k₀).trans hk₀⟩

lemma fpf_of_trans' {G : Type} [Group G] [Finite G] {F : Subgroup G} {z k : G}
    (hz2 : orderOf z = 2) (hzc : ∀ f ∈ F, f * z = z * f) (hF8 : Nat.card F = 8)
    (hk3 : k ^ 3 = 1) (hkz : k * z * k⁻¹ = z)
    (htrans : ActsTransitively (zpowers k) F (zpowers z)) :
    ∀ f ∈ F, f⁻¹ * (k * f * k⁻¹) ∈ zpowers z → f ∈ zpowers z := by
  intro f hfF hc
  set c : G := f⁻¹ * (k * f * k⁻¹) with hc_def
  have hcZ : c ∈ zpowers z := hc
  have hkf : k * f * k⁻¹ = f * c := by rw [hc_def]; group
  have hkz_comm : k * z = z * k := by
    have h := congrArg (· * k) hkz
    simpa [mul_assoc] using h
  have hzCk : zpowers z ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hkz_comm.symm
  have hc_comm : k * c * k⁻¹ = c := by
    have hck : c * k = k * c := Subgroup.mem_centralizer_singleton_iff.mp (hzCk hcZ)
    rw [← hck, mul_assoc, mul_inv_cancel, mul_one]
  have hind : ∀ j : ℕ, ((MulAut.conj k) ^ j) f = f * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hφf : MulAut.conj k f = f * c := by rw [MulAut.conj_apply]; exact hkf
        have hφc : MulAut.conj k c = c := by rw [MulAut.conj_apply]; exact hc_comm
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφf, hφc, pow_succ']
        rw [mul_assoc]
  have h3 := hind 3
  have hφ3 : (MulAut.conj k) ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
  have hcf : f = f * c ^ 3 := by
    have h := congrArg (fun ψ : MulAut G => ψ f) hφ3
    simp only [MulAut.one_apply] at h
    rw [h] at h3
    exact h3
  have hc3 : c ^ 3 = 1 := by
    have h : f * 1 = f * c ^ 3 := by rw [mul_one]; exact hcf
    exact (mul_left_cancel h).symm
  have hc2 : c ^ 2 = 1 := by
    have hle : zpowers c ≤ zpowers z := Subgroup.zpowers_le.mpr hcZ
    have hdvd : Nat.card ↥(zpowers c) ∣ Nat.card ↥(zpowers z) := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hz2] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hc1 : c = 1 := by
    calc c = c * c ^ 2 := by rw [hc2, mul_one]
      _ = c ^ 3 := by rw [pow_succ' c 2]
      _ = 1 := hc3
  have hkf' : k * f * k⁻¹ = f := by rw [hkf, hc1, mul_one]
  by_contra hfZ
  have hfix : zpowers k ≤ Subgroup.centralizer ({f} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    have hcomm : k * f = f * k := by
      have h := congrArg (· * k) hkf'
      simpa [mul_assoc] using h
    exact hcomm
  have hsub : (F : Set G) ⊆
      (zpowers z : Set G) ∪ ((fun w => f * w) '' (zpowers z : Set G)) := by
    intro v hvF
    by_cases hvZ : v ∈ zpowers z
    · exact Or.inl hvZ
    · right
      obtain ⟨κ, hκ, hκv⟩ := htrans.2.2 f hfF hfZ v hvF hvZ
      have hκf : κ * f * κ⁻¹ = f := by
        have hcomm : κ * f = f * κ :=
          Subgroup.mem_centralizer_singleton_iff.mp (hfix hκ)
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have hvf : v⁻¹ * f ∈ zpowers z := by
        have h := hκv
        rw [hκf] at h
        exact h
      exact ⟨(v⁻¹ * f)⁻¹, Subgroup.inv_mem _ hvf, by group⟩
  have hZcard : (zpowers z : Set G).ncard = 2 := by
    show Nat.card (zpowers z) = 2
    rw [Nat.card_zpowers, hz2]
  have hTcard : ((fun w => f * w) '' (zpowers z : Set G)).ncard ≤ 2 := by
    calc ((fun w => f * w) '' (zpowers z : Set G)).ncard ≤ (zpowers z : Set G).ncard :=
          Set.ncard_image_le
      _ = 2 := hZcard
  have hFcard : (F : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hF8
  have hle : (F : Set G).ncard ≤ (zpowers z : Set G).ncard +
      ((fun w => f * w) '' (zpowers z : Set G)).ncard :=
    (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  omega

lemma map_conj_zpowers_le {G : Type} [Group G] {x u : G}
    (h : x * u * x⁻¹ ∈ zpowers u) : (zpowers u).map (MulAut.conj x) ≤ zpowers u := by
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨z, hz, rfl⟩
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  simpa [MulAut.conj_apply, Subgroup.zpowers_eq_closure] using h

lemma mem_normalizer_zpowers_of_conj_mem {G : Type} [Group G] [Finite G] {x u : G}
    (h : x * u * x⁻¹ ∈ zpowers u) : x ∈ normalizer (zpowers u : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge (map_conj_zpowers_le h) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

lemma y6b_conj_u_of_mem_E (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {e : G} (he : e ∈ y6bE c.toCtx5) :
    e * (c.d * c.s.t) * e⁻¹ = c.d * c.s.t ∨
      e * (c.d * c.s.t) * e⁻¹ = (c.d * c.s.t)⁻¹ := by
  have hcfg := c.y6cfg hH
  have hFc : ∀ f ∈ c.s.fr.F, f * (c.d * c.s.t) * f⁻¹ = c.d * c.s.t := by
    intro f hf
    have h := hcfg.u_cent f (s3_F_le_A c.s hf)
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hGc : c.g * (c.d * c.s.t) * c.g⁻¹ = c.d * c.s.t := by
    have hgd : c.g * c.d * c.g⁻¹ = c.d := (c.g_spec hRT).2.2.2.2
    have hgt : c.g * c.s.t * c.g⁻¹ = c.s.t := by
      rw [y6b_g_comm_t c.toCtx5 hRT]; group
    calc c.g * (c.d * c.s.t) * c.g⁻¹
        = (c.g * c.d * c.g⁻¹) * (c.g * c.s.t * c.g⁻¹) := by group
      _ = c.d * c.s.t := by rw [hgd, hgt]
  have ht : c.s.t * (c.d * c.s.t) * c.s.t⁻¹ = (c.d * c.s.t)⁻¹ := hcfg.t_inv
  rw [y6b_mem_E c.toCtx5 hH hRT] at he
  obtain ⟨f, hf, h | h | h | h⟩ := he
  · rw [h]; exact Or.inl (hFc f hf)
  · rw [h]; exact Or.inl (by
      calc f * c.g * (c.d * c.s.t) * (f * c.g)⁻¹
          = f * (c.g * (c.d * c.s.t) * c.g⁻¹) * f⁻¹ := by group
        _ = f * (c.d * c.s.t) * f⁻¹ := by rw [hGc]
        _ = c.d * c.s.t := hFc f hf)
  · rw [h]; exact Or.inr (by
      calc f * c.s.t * (c.d * c.s.t) * (f * c.s.t)⁻¹
          = f * (c.s.t * (c.d * c.s.t) * c.s.t⁻¹) * f⁻¹ := by group
        _ = f * (c.d * c.s.t)⁻¹ * f⁻¹ := by rw [ht]
        _ = (f * (c.d * c.s.t) * f⁻¹)⁻¹ := by group
        _ = (c.d * c.s.t)⁻¹ := by rw [hFc f hf])
  · rw [h]; exact Or.inr (by
      have hgt' : c.g * c.s.t * (c.d * c.s.t) * (c.g * c.s.t)⁻¹ = (c.d * c.s.t)⁻¹ := by
        calc c.g * c.s.t * (c.d * c.s.t) * (c.g * c.s.t)⁻¹
            = c.g * (c.s.t * (c.d * c.s.t) * c.s.t⁻¹) * c.g⁻¹ := by group
          _ = c.g * (c.d * c.s.t)⁻¹ * c.g⁻¹ := by rw [ht]
          _ = (c.g * (c.d * c.s.t) * c.g⁻¹)⁻¹ := by group
          _ = (c.d * c.s.t)⁻¹ := by rw [hGc]
      calc f * (c.g * c.s.t) * (c.d * c.s.t) * (f * (c.g * c.s.t))⁻¹
          = f * (c.g * c.s.t * (c.d * c.s.t) * (c.g * c.s.t)⁻¹) * f⁻¹ := by group
        _ = f * (c.d * c.s.t)⁻¹ * f⁻¹ := by rw [hgt']
        _ = (f * (c.d * c.s.t) * f⁻¹)⁻¹ := by group
        _ = (c.d * c.s.t)⁻¹ := by rw [hFc f hf])

end CFSG.OddStandard.HigherRank.YamadaG23

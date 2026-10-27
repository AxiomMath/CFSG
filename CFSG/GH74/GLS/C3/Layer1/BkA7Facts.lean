module

public import CFSG.GH74.GLS.C3.Layer1.BkS4A7
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem perm_zero_decomp (τ : Equiv.Perm (Fin 7)) (h0 : τ 0 = 0) :
    ∃ e : Equiv.Perm (Fin 6), τ = Equiv.Perm.decomposeFin.symm (0, e) := by
  refine ⟨(Equiv.Perm.decomposeFin τ).2, ?_⟩
  set d := Equiv.Perm.decomposeFin τ with hd
  have hd1 : d.1 = 0 := by
    have : Equiv.Perm.decomposeFin.symm d 0 = d.1 := by
      rw [show d = (d.1, d.2) from rfl, Equiv.Perm.decomposeFin_symm_apply_zero]
    rw [← this, hd, Equiv.symm_apply_apply, h0]
  rw [← hd1, show (d.1, d.2) = d from rfl, hd, Equiv.symm_apply_apply]

section Alt7

open CFSG.LieType.SteinbergBR.SmallAlt in
theorem exists_conj_model {X : Subgroup (alternatingGroup (Fin 7))} (hX : Nat.card ↥X = 8) :
    ∃ c : alternatingGroup (Fin 7),
      (∀ y ∈ finSubgroup a7P a7P_mul a7P_inv a7P_one, c * y * c⁻¹ ∈ X) ∧
      (∀ x ∈ X, c⁻¹ * x * c ∈ finSubgroup a7P a7P_mul a7P_inv a7P_one) := by
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcardY : Nat.card (finSubgroup a7P a7P_mul a7P_inv a7P_one) = 8 :=
    card_finSubgroup _ _ _ _ a7P_injective fun i =>
      (Equiv.Perm.mem_alternatingGroup).2 (a7P_sign i)
  have hsyl : ∀ Y : Subgroup (alternatingGroup (Fin 7)), Nat.card ↥Y = 8 →
      Nat.card ↥Y = 2 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 2 := by
    intro Y hY
    rw [hY, hA, factorization_twentyFiveTwenty]
    norm_num
  let SY : Sylow 2 (alternatingGroup (Fin 7)) :=
    Sylow.ofCard (finSubgroup a7P a7P_mul a7P_inv a7P_one) (hsyl _ hcardY)
  let SX : Sylow 2 (alternatingGroup (Fin 7)) := Sylow.ofCard X (hsyl _ hX)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) SY SX
  refine ⟨c, fun y hy => ?_, fun x hx => ?_⟩
  · have h2 : c * y * c⁻¹ ∈ ((c • SY : Sylow 2 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨y, hy, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hc] at h2
    exact h2
  · have h2 : x ∈ ((c • SY : Sylow 2 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [hc]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, hy, rfl⟩ := h2
    have e : c⁻¹ * (MulAut.conj c • y) * c = y := by
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [e]
    exact hy

open CFSG.LieType.SteinbergBR.SmallAlt in
theorem alt7_centralizer_sq {X : Subgroup (alternatingGroup (Fin 7))} (hX : Nat.card ↥X = 8)
    (σ : Equiv.Perm (Fin 7))
    (hσ : ∀ y ∈ X, σ * (y : Equiv.Perm (Fin 7)) = (y : Equiv.Perm (Fin 7)) * σ) : σ * σ = 1 := by
  have hcheck6 : ∀ e : Equiv.Perm (Fin 6),
      (∀ i : Fin 8, Equiv.Perm.decomposeFin.symm (0, e) * a7P i =
        a7P i * Equiv.Perm.decomposeFin.symm (0, e)) →
      Equiv.Perm.decomposeFin.symm (0, e) * Equiv.Perm.decomposeFin.symm (0, e) = 1 := by
    decide +kernel
  have hcheck : ∀ τ : Equiv.Perm (Fin 7), (∀ i : Fin 8, τ * a7P i = a7P i * τ) → τ * τ = 1 := by
    intro τ hτ
    have hτ0 : τ 0 = 0 := by
      have h4 := congrArg (fun f : Equiv.Perm (Fin 7) => f 0) (hτ 4)
      simp only [Equiv.Perm.mul_apply] at h4
      rw [a7P_fix_zero 4] at h4
      exact a7P_four_fix _ h4.symm
    obtain ⟨e, he⟩ := perm_zero_decomp τ hτ0
    rw [he] at hτ ⊢
    exact hcheck6 e hτ
  obtain ⟨c, hconj, -⟩ := exists_conj_model hX
  set τ : Equiv.Perm (Fin 7) := (c : Equiv.Perm (Fin 7))⁻¹ * σ * (c : Equiv.Perm (Fin 7)) with hτ
  have hτc : ∀ i : Fin 8, τ * a7P i = a7P i * τ := by
    intro i
    have hyi : (⟨a7P i, (Equiv.Perm.mem_alternatingGroup).2 (a7P_sign i)⟩ :
        alternatingGroup (Fin 7)) ∈ finSubgroup a7P a7P_mul a7P_inv a7P_one := ⟨i, rfl⟩
    have h1 := hσ _ (hconj _ hyi)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc τ * a7P i = (c : Equiv.Perm (Fin 7))⁻¹ * (σ * ((c : Equiv.Perm (Fin 7)) * a7P i *
          (c : Equiv.Perm (Fin 7))⁻¹)) * (c : Equiv.Perm (Fin 7)) := by rw [hτ]; group
      _ = (c : Equiv.Perm (Fin 7))⁻¹ * (((c : Equiv.Perm (Fin 7)) * a7P i *
          (c : Equiv.Perm (Fin 7))⁻¹) * σ) * (c : Equiv.Perm (Fin 7)) := by rw [h1]
      _ = a7P i * τ := by rw [hτ]; group
  have h1 := hcheck τ hτc
  calc σ * σ = (c : Equiv.Perm (Fin 7)) * (τ * τ) * (c : Equiv.Perm (Fin 7))⁻¹ := by
        rw [hτ]; group
    _ = 1 := by rw [h1]; group

end Alt7

theorem lemma113d_alt {G : Type} [Group G] {K M : Subgroup G} (hKM : K ≤ M)
    (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : kBar K ≃* alternatingGroup (Fin n)) :
    ∃ ψ : ↥M →* Equiv.Perm (Fin n), ψ.ker = (CMK M K).subgroupOf M ∧
      ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKM hk⟩ =
        ((e (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : alternatingGroup (Fin n)) :
          Equiv.Perm (Fin n)) := by
  let c : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)
  refine ⟨c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (actHom hnorm)), ?_, ?_⟩
  · rw [← actHom_ker hnorm]
    ext m
    simp [MonoidHom.mem_ker]
  · intro k hk
    show c.symm (MulAut.congr e (actHom hnorm ⟨k, hKM hk⟩)) = _
    rw [actHom_of_mem hnorm hk (hKM hk), MulEquiv.symm_apply_eq]
    ext y
    simp [c, MulAut.congr_apply, MulAut.conj_apply]

theorem card_ker_comp_inclusion {G : Type} [Group G] [Finite G] {K M T : Subgroup G}
    (hTM : T ≤ M) (ψ₀ : ↥M →* Equiv.Perm (Fin 7))
    (hker : ψ₀.ker = (CMK M K).subgroupOf M) (hQ4 : Nat.card ↥(T ⊓ CMK M K) = 4) :
    Nat.card (ψ₀.comp (Subgroup.inclusion hTM)).ker = 4 := by
  have hkerf : (ψ₀.comp (Subgroup.inclusion hTM)).ker = (T ⊓ CMK M K).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ₀ (Subgroup.inclusion hTM t) = 1 ↔ (t : G) ∈ CMK M K := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    show ψ₀ (Subgroup.inclusion hTM t) = 1 ↔ _
    rw [h1]
    exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
  rw [hkerf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hQ4]

theorem card_range_mul_four_of_alt7 {G : Type} [Group G] [Finite G] {K M T : Subgroup G}
    (hTM : T ≤ M) (ψ₀ : ↥M →* Equiv.Perm (Fin 7))
    (hker : ψ₀.ker = (CMK M K).subgroupOf M) (hQ4 : Nat.card ↥(T ⊓ CMK M K) = 4) :
    Nat.card ↥(ψ₀.comp (Subgroup.inclusion hTM)).range * 4 = Nat.card ↥T := by
  have h := Subgroup.card_ker_mul_card_range (ψ₀.comp (Subgroup.inclusion hTM))
  rw [card_ker_comp_inclusion hTM ψ₀ hker hQ4] at h
  omega

theorem card_le_sixtyfour_of_alt7 {G : Type} [Group G] [Finite G] {K M T : Subgroup G}
    (hT2 : IsPGroup 2 ↥T) (hTM : T ≤ M) (ψ₀ : ↥M →* Equiv.Perm (Fin 7))
    (hker : ψ₀.ker = (CMK M K).subgroupOf M) (hQ4 : Nat.card ↥(T ⊓ CMK M K) = 4) :
    Nat.card ↥T ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥T →* Equiv.Perm (Fin 7) := ψ₀.comp (Subgroup.inclusion hTM) with hf
  have hrangeP : IsPGroup 2 f.range :=
    hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hrangeP
  have hdvd : Nat.card f.range ∣ 5040 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_perm, Nat.card_fin] at this
  have hn4 : n ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h32 : 2 ^ 5 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hcon
    rw [← hn] at h32
    have := h32.trans hdvd
    norm_num [Nat.factorial] at this
  have h := card_range_mul_four_of_alt7 hTM ψ₀ hker hQ4
  rw [hn] at h
  have h16 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
  omega

theorem inf_embeds_alt7 {G : Type} [Group G] [Finite G] {T K : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hP : IsSylowOf 2 (T ⊓ K) K) (e7 : kBar K ≃* alternatingGroup (Fin 7)) :
    ∃ ι : ↥(T ⊓ K) →* alternatingGroup (Fin 7), Function.Injective ι ∧ Nat.card ↥ι.range = 8 ∧
      ∀ p : ↥(T ⊓ K), ι p = e7 (QuotientGroup.mk (⟨(p : G), p.2.2⟩ : ↥K)) := by
  refine ⟨e7.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
    (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K))), ?_, ?_, fun p => rfl⟩
  · set ι : ↥(T ⊓ K) →* alternatingGroup (Fin 7) :=
      e7.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
        (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K))) with hι
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    have hp1 : e7 ((QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p)) = 1 :=
      hp
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p) = 1 :=
      e7.injective (hp1.trans (map_one e7).symm)
    have h2 : Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K) p ∈ pPrimeCore 2 ↥K :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ((p : G)) ∈ T ⊓ pPrimeCoreOf 2 K :=
      ⟨p.2.1, Setup91.mem_pPrimeCoreOf_iff.2 ⟨p.2.2, h2⟩⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hT2, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  · have hinj : Function.Injective (e7.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
        (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K)))) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro p hp
      have hp1 : e7 ((QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p)) = 1 :=
        hp
      have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p) = 1 :=
        e7.injective (hp1.trans (map_one e7).symm)
      have h2 : Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K) p ∈ pPrimeCore 2 ↥K :=
        (QuotientGroup.eq_one_iff _).1 h1
      have h3 : ((p : G)) ∈ T ⊓ pPrimeCoreOf 2 K :=
        ⟨p.2.1, Setup91.mem_pPrimeCoreOf_iff.2 ⟨p.2.2, h2⟩⟩
      rw [Setup91.inf_pPrimeCoreOf_eq_bot K hT2, Subgroup.mem_bot] at h3
      exact Subgroup.mem_bot.2 (Subtype.ext h3)
    have hPcard : Nat.card ↥(T ⊓ K) = 8 := by
      rw [hP.card_eq, factorization_two_card_of_equiv_A7 e7]
      norm_num
    rw [← hPcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isD8_of_inf_alt7 {G : Type} [Group G] [Finite G] {T K : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hP : IsSylowOf 2 (T ⊓ K) K) (e7 : kBar K ≃* alternatingGroup (Fin 7)) : IsD8 (T ⊓ K) := by
  obtain ⟨ι, hι, hcard, -⟩ := inf_embeds_alt7 hT2 hP e7
  obtain ⟨d⟩ := isD8_of_card_eight_alt7 hcard
  exact ⟨(MonoidHom.ofInjective hι).trans d⟩

end CFSG.GH74.GLS.C3.Layer1.Bk

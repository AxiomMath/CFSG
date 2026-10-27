module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27HaradaLocal
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27OrdersArith
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGroups.U33
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.Assembly.LowTwoRank

private lemma prime_dvd_M {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  rcases prime_dvd_GL8 hp h with h | h | h | h | h | h | h
  · exact absurd h hp2
  all_goals tauto

theorem l2_arith (p f r q0 : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : Even r)
    (hr0 : r ≠ 0) (hq0 : q0 ^ r = p ^ f)
    (hdvd : (p ^ f * ((p ^ f) ^ 2 - 1) / 2) ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127)
    (h5 : 5 ∣ q0 * (q0 ^ 2 - 1)) : False := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hNodd : Odd ((p ^ f) ^ 2) := (hpodd.pow).pow
  have h2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hNodd
    omega
  have hNM : p ^ f ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
    refine dvd_trans ?_ hdvd
    rw [Nat.mul_div_assoc _ h2]
    exact Dvd.intro _ rfl
  have hr2 : r % 2 = 0 := Nat.even_iff.1 hr
  have hr2' : 2 ≤ r := by omega
  have hq0dvd : q0 ∣ p ^ f := by
    rw [← hq0]
    exact dvd_pow_self q0 hr0
  obtain ⟨j, hjf, rfl⟩ := (Nat.dvd_prime_pow hp).1 hq0dvd
  have hjr : j * r = f := by
    rw [← pow_mul] at hq0
    exact Nat.pow_right_injective hp.two_le hq0
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      simp at hjr
      omega
    · exact h
  have hrf : r ≤ f := hjr ▸ Nat.le_mul_of_pos_left r hj1
  have hf2 : 2 ≤ f := by omega
  have hpM : p ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
    (dvd_pow_self p (by omega : f ≠ 0)).trans hNM
  rcases prime_dvd_M hp hp2 hpM with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hf5 : f ≤ 5 := by
      by_contra hlt
      have h6 : 3 ^ 6 ∣ 3 ^ f := pow_dvd_pow 3 (by omega)
      have := h6.trans hNM
      norm_num at this
    have hr4 : r = 2 ∨ r = 4 := by omega
    rcases hr4 with rfl | rfl
    · have hj : j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl
      · norm_num at h5
      · obtain rfl : f = 4 := by omega
        norm_num at hdvd
    · obtain rfl : j = 1 := by omega
      norm_num at h5
  ·
    have hf5 : f ≤ 2 := by
      by_contra hlt
      have h6 : 5 ^ 3 ∣ 5 ^ f := pow_dvd_pow 5 (by omega)
      have := h6.trans hNM
      norm_num at this
    obtain rfl : f = 2 := by omega
    norm_num at hdvd
  ·
    have hf5 : f ≤ 2 := by
      by_contra hlt
      have h6 : 7 ^ 3 ∣ 7 ^ f := pow_dvd_pow 7 (by omega)
      have := h6.trans hNM
      norm_num at this
    obtain rfl : f = 2 := by omega
    obtain rfl : r = 2 := by omega
    obtain rfl : j = 1 := by omega
    norm_num at h5
  ·
    have hf5 : f ≤ 1 := by
      by_contra hlt
      have h6 : 17 ^ 2 ∣ 17 ^ f := pow_dvd_pow 17 (by omega)
      have := h6.trans hNM
      norm_num at this
    omega
  ·
    have hf5 : f ≤ 1 := by
      by_contra hlt
      have h6 : 31 ^ 2 ∣ 31 ^ f := pow_dvd_pow 31 (by omega)
      have := h6.trans hNM
      norm_num at this
    omega
  ·
    have hf5 : f ≤ 1 := by
      by_contra hlt
      have h6 : 127 ^ 2 ∣ 127 ^ f := pow_dvd_pow 127 (by omega)
      have := h6.trans hNM
      norm_num at this
    omega

theorem notL28 : NotL28 := by
  intro N _ _ X t o h
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  have hdvd := card_dvd_mulAut (K := layer N) o.cent_bot
  rw [CFSG.GH74.KGroups.L28.card_mulAut h] at hdvd
  have h60 : 60 ∣ Nat.card N := by
    rw [← o.loc.card_eq_sixty]
    exact Subgroup.card_subgroup_dvd_card X
  have := h60.trans hdvd
  norm_num at this

theorem notU33 :
    NotU33 := by
  intro N _ _ X t o h
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  have hdvd := card_dvd_mulAut (K := layer N) o.cent_bot
  rw [CFSG.GH74.KGroups.U33.card_mulAut e] at hdvd
  have h60 : 60 ∣ Nat.card N := by
    rw [← o.loc.card_eq_sixty]
    exact Subgroup.card_subgroup_dvd_card X
  have := h60.trans hdvd
  norm_num at this

theorem notL2Odd :
    NotL2Odd := by
  intro N _ _ X t o m p f hp hp2 hf h
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  rcases h with ⟨-, hadm, F, hFld, hFfin, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  ·
    have hFodd : Odd (Nat.card F) := by
      rw [hF]; exact (hp.odd_of_ne_two hp2).pow
    have hF3 : 3 < Nat.card F := by
      have h1 : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h2 | h2
        · exact absurd h2 hp2
        · have := hp.two_le
          rcases h2 with ⟨k, hk⟩
          omega
      have h2 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      have h3 : p ^ f ≠ 3 := by
        intro h3
        exact hadm.2.2.2.2 (by rw [h3])
      rw [hF]
      omega
    have hL2F : L2Field F := ⟨hFodd, hF3⟩
    have hKcard : Nat.card ↥(layer N) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      ivk_1_2b F hL2F ↥(layer N) e
    have hdvdM : Nat.card ↥(layer N) ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
      (Subgroup.card_subgroup_dvd_card (layer N)).trans m.card_dvd
    rw [hKcard, hF] at hdvdM
    let I : Subgroup ↥(layer N) := X.subgroupOf (layer N)
    have hIX : ↥I ≃* ↥X := Subgroup.subgroupOfEquivOfLe o.X_le
    obtain ⟨eA⟩ := o.loc.exists_equiv_alt
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hK5 : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 5 1) (Or.inr (by rw [hK5, pow_one]))
    have hI : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) :=
      ⟨GaloisField 5 1, inferInstance, inferInstance, ⟨by rw [hK5]; decide, by rw [hK5]; decide⟩,
        ⟨hIX.trans (eA.trans e5.symm)⟩⟩
    obtain ⟨⟨e', -, hcent⟩, -⟩ := Proofs2.ivk_1_4h F hL2F ↥(layer N) e I hI
    have hinj := conjNormal_injective_of_centralizer_eq_bot (K := layer N) o.cent_bot
    let τ : MulAut ↥(layer N) := MulAut.conjNormal t
    have hτ2 : orderOf τ = 2 := by
      rw [orderOf_injective (MulAut.conjNormal : N →* MulAut ↥(layer N)) hinj t, o.loc.t_order]
    have hτx : ∀ x ∈ I, τ x = x := by
      intro x hx
      apply Subtype.ext
      change t * (x : N) * t⁻¹ = x
      have := o.loc.t_cent (x : N) hx
      calc t * (x : N) * t⁻¹ = (x : N) * t * t⁻¹ := by rw [← this]
        _ = x := by group
    have hτcent : τ ∈ centralizer ((I.map (MulAut.conj : ↥(layer N) →* MulAut ↥(layer N)) :
        Subgroup (MulAut ↥(layer N))) : Set (MulAut ↥(layer N))) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      ext y
      have hxt : ((x : ↥(layer N)) : N) * t = t * (x : N) := o.loc.t_cent (x : N) hx
      have hxt' : ((x : ↥(layer N)) : N)⁻¹ * t⁻¹ = t⁻¹ * (x : N)⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hxt]
      change ((x * (τ y) * x⁻¹ : ↥(layer N)) : N) = ((τ (x * y * x⁻¹) : ↥(layer N)) : N)
      change (x : N) * (t * (y : N) * t⁻¹) * (x : N)⁻¹ = t * ((x : N) * (y : N) * (x : N)⁻¹) * t⁻¹
      calc (x : N) * (t * (y : N) * t⁻¹) * (x : N)⁻¹
          = ((x : N) * t) * (y : N) * (t⁻¹ * (x : N)⁻¹) := by group
        _ = (t * (x : N)) * (y : N) * ((x : N)⁻¹ * t⁻¹) := by rw [hxt, hxt']
        _ = t * ((x : N) * (y : N) * (x : N)⁻¹) * t⁻¹ := by group
    have hτF : τ ∈ fieldAutSub e' := hcent hτcent
    obtain ⟨σ, hσ⟩ := hτF
    have : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
      DFunLike.coe_injective
    have hσ0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
    have hσeven : Even (orderOf σ) := by
      have h2 : orderOf (fieldAutHom e' σ) ∣ orderOf σ := orderOf_map_dvd _ _
      rw [hσ, hτ2] at h2
      exact even_iff_two_dvd.2 h2
    obtain ⟨F₀, _, _, hq0, ⟨eP⟩⟩ := (ivk_1_4a F hL2F ↥(layer N) e' σ).2.2 hσeven
    have hIfix : I ≤ fixedSubgroup ↥(layer N) (fieldAutHom e' σ) := by
      intro x hx
      change (fieldAutHom e' σ) x = x
      rw [hσ]
      exact hτx x hx
    have hI60 : Nat.card I = 60 := by
      rw [Nat.card_congr hIX.toEquiv]
      exact o.loc.card_eq_sixty
    have h60 : 60 ∣ Nat.card (PGL2 F₀) := by
      rw [← Nat.card_congr eP.toEquiv, ← hI60]
      exact Subgroup.card_dvd_of_le hIfix
    rw [pgl2_card_formula] at h60
    have h5 : 5 ∣ Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := (by norm_num : 5 ∣ 60).trans h60
    rw [hF] at hq0
    exact l2_arith p f (orderOf σ) (Nat.card F₀) hp hp2 hf hσeven hσ0 hq0 hdvdM h5
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)

end CFSG.OddStandard.Seitz77

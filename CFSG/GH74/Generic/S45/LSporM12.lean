module

public import CFSG.GH74.Generic.S45.LSporCommon
public import CFSG.GH74.Generic.S45.LSporM12Data
public import CFSG.GH74.Generic.S45.LRed
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.GH74.Generic.S45.LAltCore

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.ComponentClassification.M12Cover

theorem false_of_card_dvd_192 {N q : ℕ} (hN : N ∣ 192) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (h : N * 2 = q * (q ^ 2 - 1)) : False := by
  have hN192 : N ≤ 192 := Nat.le_of_dvd (by norm_num) hN
  have hq7 : q ≤ 7 := by
    by_contra hgt
    push Not at hgt
    have h1 : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 8 * (8 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  obtain ⟨k, hk⟩ := hqodd
  interval_cases q
  · norm_num at h
    have : N = 60 := by omega
    subst this
    norm_num at hN
  · omega
  · norm_num at h
    have : N = 168 := by omega
    subst this
    norm_num at hN

theorem spor_m12
    {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K} (hyp : Hyp1310 K y L)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.M12) : Concl1310 K y L := by
  classical
  have hKq : CFSG.Assembly.IsQuasisimple K := ⟨hyp.1.1.1.commutator_eq_top, hyp.1.1.2.1⟩
  obtain ⟨hKp, hz2, hy, hLfix, hno4, hLs, hLnab, hLinv, q, hq5, hqodd, hqcard, hmodel⟩ := hyp.data
  obtain ⟨yb, hyb, hyb1, hyb2⟩ := LAlt.exists_induced_quotient hKp y hy
  let ya : NativeSporadic.M12 ≃* NativeSporadic.M12 := (MulAut.congr e) yb
  let π : K →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hπy : ∀ k : K, π (y k) = ya (π k) := by
    intro k
    show e (QuotientGroup.mk (y k)) = (MulAut.congr e yb) (e (QuotientGroup.mk k))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hyb]
  have hya1 : ya ≠ 1 := fun h => hyb1 ((MulAut.congr e).injective (by rw [map_one]; exact h))
  have hya2 : ya * ya = 1 := by
    show (MulAut.congr e) yb * (MulAut.congr e) yb = 1
    rw [← map_mul, hyb2, map_one]
  have hLinj : Function.Injective (π.comp L.subtype) := LAlt.inj_restrict π hπker hLs hLnab
  have hLfixed : ∀ l ∈ L, ya (π l) = π l := fun l hl => by rw [← hπy, hLfix l hl]
  have hcongr : ∀ s : K ⧸ Subgroup.center K, (MulAut.congr e) (MulAut.conj s) = MulAut.conj (e s) := by
    intro s
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := exists_conj_or_conj_mul_beta ya
  rcases hg with hin | hout
  ·
    exfalso
    have hgg : g * g = 1 := by
      have h1 : MulAut.conj (g * g) = 1 := by rw [map_mul, ← hin, hya2]
      have hc : g * g ∈ Subgroup.center NativeSporadic.M12 := by
        rw [Subgroup.mem_center_iff]
        intro x
        have := congrArg (fun a : MulAut NativeSporadic.M12 => a x) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * (g * g) = (g * g * x * (g * g)⁻¹) * (g * g) := by rw [this]
          _ = g * g * x := by group
      rw [m12_center, Subgroup.mem_bot] at hc
      exact hc
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hya1 (by rw [hin, map_one])
    have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
    have hLC : ∀ l ∈ L, π l ∈ Subgroup.centralizer ({g} : Set NativeSporadic.M12) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hLfixed l hl
      rw [hin, MulAut.conj_apply] at h1
      calc π l * g = (g * π l * g⁻¹) * g := by rw [h1]
        _ = g * π l := by group
    have hdvd : Nat.card ↥L ∣ Nat.card (Subgroup.centralizer ({g} : Set NativeSporadic.M12)) :=
      LAlt.card_dvd_of_map_le π hLinj _ hLC
    rcases LAlt.m12_involution_data g hgord with hc192 | ⟨hc240, hfix0, g₄, hg₄C, hg₄ord⟩
    · rw [hc192] at hdvd
      exact false_of_card_dvd_192 hdvd hq5 hqodd hqcard
    · by_cases hZ : Subgroup.center K = ⊥
      · have hinj : Function.Injective π :=
          (MonoidHom.ker_eq_bot_iff π).1 (by rw [hπker]; exact hZ)
        obtain ⟨k₄, hk₄⟩ := hπsurj g₄
        have hyk : y k₄ = k₄ := by
          apply hinj
          rw [hπy, hk₄, hin, MulAut.conj_apply]
          have := Subgroup.mem_centralizer_singleton_iff.1 hg₄C
          calc g * g₄ * g⁻¹ = (g₄ * g) * g⁻¹ := by rw [this]
            _ = g₄ := by group
        have h4 : 4 ∣ orderOf k₄ := by
          have h1 := orderOf_injective π hinj k₄
          rw [hk₄, hg₄ord] at h1
          rw [← h1]
        exact hno4 k₄ hyk h4
      · have hcard2 : Nat.card (Subgroup.center K) ≤ 2 :=
          CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound K hKq hz2
            (Or.inl ⟨e⟩)
        obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
        have hcard : Nat.card (Subgroup.center K) = 2 := by
          have := (Subgroup.one_lt_card_iff_ne_bot _).2 hZ
          omega
        have hasq : a ^ 2 = 1 := by
          have := pow_card_eq_one' (G := Subgroup.center K) (x := a)
          rwa [hcard] at this
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hζord : orderOf (a : K) = 2 := by
          rw [Subgroup.orderOf_coe]
          exact orderOf_eq_prime hasq ha1
        have hcenZ : Subgroup.center K = Subgroup.zpowers (a : K) :=
          (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 a.2)
            (by rw [Nat.card_zpowers, hζord, hcard])).symm
        have hker : π.ker = Subgroup.zpowers (a : K) := hπker.trans hcenZ
        obtain ⟨kh, hkh⟩ := hπsurj g
        have hlift := (m12_double_cover_involution_lift_orders hKq hζord hcenZ π hπsurj hker).2.2
          kh (by rw [hkh, hgord]) (by rw [hkh]; exact hfix0)
        have hybc : yb = MulAut.conj (QuotientGroup.mk kh) := by
          apply (MulAut.congr e).injective
          show ya = (MulAut.congr e) (MulAut.conj (QuotientGroup.mk kh))
          rw [hcongr]
          have : e (QuotientGroup.mk kh) = g := hkh
          rw [this, hin]
        have hyc : y = MulAut.conj kh := LAlt.eq_conj_of_induced_eq_conj hKp y yb hyb kh hybc
        have hyk : y kh = kh := by
          rw [hyc, MulAut.conj_apply]
          group
        exact hno4 kh hyk (by rw [hlift.2])
  ·
    have hout' : ya ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M12 := by
      intro hmem
      apply beta_not_mem_inner
      have : beta = (MulAut.conj g)⁻¹ * ya := by
        rw [hout]
        group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨g, rfl⟩) hmem
    obtain ⟨γ, hγ⟩ := LAlt.m12_outer_involution ya hya2 hout'
    let π' : K →* NativeSporadic.M12 := γ⁻¹.toMonoidHom.comp π
    have hπ'inj : Function.Injective (π'.comp L.subtype) := fun a b hab =>
      hLinj (γ⁻¹.injective hab)
    have hLfb : ∀ l ∈ L, π' l ∈ CFSG.Sporadic.Schreier.fixSub beta := by
      intro l hl
      rw [CFSG.Sporadic.Schreier.mem_fixSub]
      have h1 := hLfixed l hl
      rw [hγ] at h1
      simp only [MulAut.mul_apply] at h1
      show beta (γ⁻¹ (π l)) = γ⁻¹ (π l)
      apply γ.injective
      rw [MulAut.apply_inv_self]
      exact h1
    have hdvd : Nat.card ↥L ∣ Nat.card (CFSG.Sporadic.Schreier.fixSub beta) :=
      LAlt.card_dvd_of_map_le π' hπ'inj _ hLfb
    rw [card_fixSub_beta] at hdvd
    have hq : q = 5 := eq_five_of_card_dvd_120 hdvd hq5 hqodd hqcard
    refine ⟨hmodel _ hq, Or.inr (Or.inr (Or.inl ⟨e⟩)), fun _ => ?_⟩
    rintro ⟨k, hk⟩
    apply hout'
    have hybc : yb = MulAut.conj (QuotientGroup.mk k) := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective x
      rw [hyb, ← hk]
      simp [MulAut.conj_apply]
    refine ⟨e (QuotientGroup.mk k), ?_⟩
    rw [← hcongr, ← hybc]

end CFSG.GH74.Generic.S45

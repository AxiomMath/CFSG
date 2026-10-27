module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma23
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalTightCommuting
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting

variable {G : Type*} [Group G]

theorem asc76Lemma23 :
    ∀ (G : Type) [Group G] [Finite G] (S R T : Subgroup G), IsPGroup 2 S → R ≤ S →
      TightlyEmbedded (R.subgroupOf S) → T ≤ S → R ≤ normalizer (T : Set G) →
      Nat.card T ≤ Nat.card R → R ⊓ T = ⊥ → ⁅R, T⁆ = ⊥ :=
  fun _ _ _ _ _ _ hS hRS hR hTS hRT hcard hRT1 => lemma23 hS hRS hR hTS hRT hcard hRT1

structure TIFamily (S : Subgroup G) (Δ : Set (Subgroup G)) : Prop where
  pGroup : IsPGroup 2 S
  le_S : ∀ R ∈ Δ, R ≤ S
  conj_mem : ∀ R ∈ Δ, ∀ s ∈ S, rightConjugate R s ∈ Δ
  card_eq : ∀ R ∈ Δ, ∀ T ∈ Δ, Nat.card R = Nat.card T
  frattini_ne : ∀ R ∈ Δ, frattini R ≠ ⊥
  inf_eq_bot : ∀ R ∈ Δ, ∀ T ∈ Δ, R ≠ T → R ⊓ T = ⊥

namespace TIFamily

variable {S : Subgroup G} {Δ : Set (Subgroup G)}

theorem isPGroup_of_mem (hF : TIFamily S Δ) {R : Subgroup G} (hR : R ∈ Δ) : IsPGroup 2 R :=
  hF.pGroup.to_le (hF.le_S R hR)

theorem ne_bot_of_mem (hF : TIFamily S Δ) {R : Subgroup G} (hR : R ∈ Δ) : R ≠ ⊥ := by
  intro h
  apply hF.frattini_ne R hR
  rw [eq_bot_iff]
  intro x _
  have : (x : G) ∈ (⊥ : Subgroup G) := h ▸ x.2
  rw [mem_bot] at this
  rw [mem_bot]
  exact Subtype.ext this

theorem inf_eq_bot_of_mem (hF : TIFamily S Δ) {R₁ R₂ : Subgroup G} (h₁ : R₁ ∈ Δ)
    (h₂ : R₂ ∈ Δ) (hne : R₁ ≠ R₂) : R₁ ⊓ R₂ = ⊥ :=
  hF.inf_eq_bot R₁ h₁ R₂ h₂ hne

theorem mem_normalizer_of_mem (hF : TIFamily S Δ) {R : Subgroup G} (hR : R ∈ Δ)
    {X : Subgroup G} (hXR : X ≤ R) (hX : X ≠ ⊥) {s : G} (hsS : s ∈ S)
    (hsX : s ∈ normalizer (X : Set G)) : s ∈ normalizer (R : Set G) := by
  by_contra hsR
  have hne : R ≠ rightConjugate R s :=
    fun h => hsR ((rightConjugate_eq_self_iff R s).mp h.symm)
  have hinf := hF.inf_eq_bot R hR _ (hF.conj_mem R hR s hsS) hne
  apply hX
  rw [eq_bot_iff, ← hinf]
  intro x hx
  refine mem_inf.mpr ⟨hXR hx, ?_⟩
  rw [mem_rightConjugate_iff]
  exact hXR ((mem_normalizer_iff.mp hsX x).mp hx)

theorem commutes_of_mem [Finite G] (hF : TIFamily S Δ) {R₁ R₂ : Subgroup G} (h₁ : R₁ ∈ Δ)
    (h₂ : R₂ ∈ Δ) (hne : R₁ ≠ R₂) (hN : R₂ ≤ normalizer (R₁ : Set G)) : Commutes R₁ R₂ := by
  have hinf := hF.inf_eq_bot R₁ h₁ R₂ h₂ hne
  have hXS : R₂ ⊔ R₁ ≤ S := sup_le (hF.le_S R₂ h₂) (hF.le_S R₁ h₁)
  have hprod := card_sup_mul_card_inf hN
  rw [inf_comm, hinf, card_bot, mul_one] at hprod
  have hXcard : Nat.card (R₂ ⊔ R₁ : Subgroup G) ≤ Nat.card R₂ * Nat.card R₂ := by
    rw [hprod, hF.card_eq R₁ h₁ R₂ h₂]
  have hTI : ∀ x ∈ R₂ ⊔ R₁, x ∉ normalizer (R₂ : Set G) → R₂ ⊓ rightConjugate R₂ x = ⊥ :=
    fun x hx hxN => hF.inf_eq_bot R₂ h₂ _ (hF.conj_mem R₂ h₂ x (hXS hx))
      (fun h => hxN ((rightConjugate_eq_self_iff R₂ x).mp h.symm))
  have hXN := normalizes_of_card_le (hF.pGroup.to_le hXS) le_sup_left hTI hXcard
  intro a ha b hb
  have hc : a * b * a⁻¹ * b⁻¹ ∈ R₁ ⊓ R₂ := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ R₁ := (mem_normalizer_iff.mp (hN hb) a⁻¹).mp (inv_mem ha)
      have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [this]
      exact mul_mem ha h1
    · have h1 : a * b * a⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hXN (mem_sup_right ha)) b).mp hb
      exact mul_mem h1 (inv_mem hb)
  rw [hinf, mem_bot] at hc
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

variable [Finite G]

theorem commutes_of_permutes (hF : TIFamily S Δ) {Γ : Set (Subgroup G)} (hΓ : Γ ⊆ Δ)
    (hcomm : ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → Commutes R₁ R₂) {T : Subgroup G}
    (hT : T ∈ Δ) (hTΓ : T ∉ Γ)
    (hperm : ∀ t ∈ T, ∀ R ∈ Γ, rightConjugate R t ∈ Γ) :
    ∀ R ∈ Γ, Commutes T R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := ⨆ R : Γ, (R : Subgroup G) with hW
  have hRW : ∀ R ∈ Γ, R ≤ W := fun R hR => le_iSup (fun R : Γ => (R : Subgroup G)) ⟨R, hR⟩
  have hWN : ∀ R ∈ Γ, W ≤ normalizer (R : Set G) := by
    intro R hR
    refine iSup_le fun R' => ?_
    by_cases hR' : (R' : Subgroup G) = R
    · rw [hR']
      exact le_normalizer
    · exact (hcomm R' R'.2 R hR hR').le_normalizer
  have hTW : ∀ t ∈ T, t ∈ normalizer (W : Set G) := by
    intro t ht
    rw [← rightConjugate_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [rightConjugate_card])
    change W.map (MulAut.conj t⁻¹).toMonoidHom ≤ W
    rw [hW, Subgroup.map_iSup]
    exact iSup_le fun R => hRW _ (hperm t ht R R.2)
  have hTS : T ≤ S := hF.le_S T hT
  have hT2 : IsPGroup 2 T := hF.isPGroup_of_mem hT
  intro R hRΓ
  have hRΔ := hΓ hRΓ
  have hRS : R ≤ S := hF.le_S R hRΔ
  have hTR : T ≠ R := fun h => hTΓ (h ▸ hRΓ)
  by_contra hTRc
  have hstar : T ⊓ normalizer (R : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyT, hyN⟩
    rw [mem_bot]
    by_contra hy1
    obtain ⟨z, hzR, hz1, hzc, hzy⟩ := exists_center_commute (hF.isPGroup_of_mem hRΔ)
      (hF.ne_bot_of_mem hRΔ) hyN (hT2.to_le ((zpowers_le).mpr hyT))
    have hzW : ∀ w ∈ W, w * z = z * w := by
      have hle : W ≤ centralizer ({z} : Set G) := by
        refine iSup_le fun R' => ?_
        intro w hw
        rw [mem_centralizer_singleton_iff]
        by_cases hR' : (R' : Subgroup G) = R
        · rw [hR'] at hw
          exact (hzc w hw).symm
        · exact hcomm R' R'.2 R hRΓ hR' w hw z hzR
      intro w hw
      exact mem_centralizer_singleton_iff.mp (hle hw)
    have hzNT : z ∈ normalizer (T : Set G) :=
      hF.mem_normalizer_of_mem hT ((zpowers_le).mpr hyT) (zpowers_ne_bot_of_ne_one hy1)
        (hRS hzR) (mem_normalizer_zpowers_of_commute hzy)
    by_cases hcase : ∀ t' ∈ T, z * t' * z⁻¹ * t'⁻¹ = 1
    · have hTN : T ≤ normalizer (R : Set G) := by
        intro t' ht'
        have htz : t' * z = z * t' := by
          have h1 := hcase t' ht'
          calc t' * z = (z * t' * z⁻¹ * t'⁻¹)⁻¹ * (z * t') := by group
            _ = z * t' := by rw [h1, inv_one, one_mul]
        exact hF.mem_normalizer_of_mem hRΔ ((zpowers_le).mpr hzR) (zpowers_ne_bot_of_ne_one hz1)
          (hTS ht') (mem_normalizer_zpowers_of_commute htz)
      exact hTRc (hF.commutes_of_mem hRΔ hT (Ne.symm hTR) hTN).symm
    · push Not at hcase
      obtain ⟨t', ht', hc1⟩ := hcase
      set c := z * t' * z⁻¹ * t'⁻¹ with hc
      have hcT : c ∈ T := by
        have := (mem_normalizer_iff.mp hzNT t').mp ht'
        exact mul_mem this (inv_mem ht')
      have hcW : ∀ w ∈ W, w * c = c * w := by
        intro w hw
        have hw' : t'⁻¹ * w * t' ∈ W := by
          have := (mem_normalizer_iff.mp (inv_mem (hTW t' ht')) w).mp hw
          simpa using this
        have h1 := hzW w hw
        have h2 := hzW _ hw'
        have h3 : w * (t' * z⁻¹ * t'⁻¹) = (t' * z⁻¹ * t'⁻¹) * w := by
          have h2' : (t'⁻¹ * w * t') * z⁻¹ = z⁻¹ * (t'⁻¹ * w * t') := by
            calc (t'⁻¹ * w * t') * z⁻¹ = z⁻¹ * (z * (t'⁻¹ * w * t')) * z⁻¹ := by group
              _ = z⁻¹ * ((t'⁻¹ * w * t') * z) * z⁻¹ := by rw [h2]
              _ = z⁻¹ * (t'⁻¹ * w * t') := by group
          calc w * (t' * z⁻¹ * t'⁻¹) = t' * ((t'⁻¹ * w * t') * z⁻¹) * t'⁻¹ := by group
            _ = t' * (z⁻¹ * (t'⁻¹ * w * t')) * t'⁻¹ := by rw [h2']
            _ = (t' * z⁻¹ * t'⁻¹) * w := by group
        calc w * c = (w * z) * (t' * z⁻¹ * t'⁻¹) := by rw [hc]; group
          _ = (z * w) * (t' * z⁻¹ * t'⁻¹) := by rw [h1]
          _ = z * (w * (t' * z⁻¹ * t'⁻¹)) := by group
          _ = z * ((t' * z⁻¹ * t'⁻¹) * w) := by rw [h3]
          _ = c * w := by rw [hc]; group
      have hRN : R ≤ normalizer (T : Set G) := by
        intro r hr
        exact hF.mem_normalizer_of_mem hT ((zpowers_le).mpr hcT) (zpowers_ne_bot_of_ne_one hc1)
          (hRS hr) (mem_normalizer_zpowers_of_commute (hcW r (hRW R hRΓ hr)))
      exact hTRc (hF.commutes_of_mem hT hRΔ hTR hRN)
  have hTW1 : ∀ w ∈ T, w ∈ W → w = 1 := by
    intro w hwT hwW
    have : w ∈ T ⊓ normalizer (R : Set G) := ⟨hwT, hWN R hRΓ hwW⟩
    rw [hstar, mem_bot] at this
    exact this
  have hWS : W ≤ S := iSup_le fun R' => hF.le_S _ (hΓ R'.2)
  obtain ⟨y, hyT, hy4⟩ := exists_orderOf_eq_four hT2 (hF.frattini_ne T hT)
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy4
    norm_num at hy4
  have hnorm : ∀ g ∈ T, g ∈ normalizer (R : Set G) → g = 1 := fun g hg hgN => by
    have : g ∈ T ⊓ normalizer (R : Set G) := ⟨hg, hgN⟩
    rw [hstar, mem_bot] at this
    exact this
  set t := y * y with ht
  have htT : t ∈ T := mul_mem hyT hyT
  have htt : t * t = 1 := by
    calc t * t = y ^ 4 := by rw [ht]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hy4'
  have ht1 : t ≠ 1 := by
    intro h
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hy4] at this
    norm_num at this
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, htt]
  have hy3 : y * y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc y * y * y * y = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := hy4'
  have hy3' : y⁻¹ * y⁻¹ * y⁻¹ = y := by
    calc y⁻¹ * y⁻¹ * y⁻¹ = (y * y * y)⁻¹ := by group
      _ = y⁻¹⁻¹ := by rw [hy3]
      _ = y := inv_inv y
  set R1 := rightConjugate R y with hR1
  set R2 := rightConjugate R t with hR2
  have hR1Γ : R1 ∈ Γ := hperm y hyT R hRΓ
  have hR2Γ : R2 ∈ Γ := hperm t htT R hRΓ
  have hR01 : R ≠ R1 :=
    fun h => hy1 (hnorm y hyT ((rightConjugate_eq_self_iff R y).mp h.symm))
  have hR02 : R ≠ R2 :=
    fun h => ht1 (hnorm t htT ((rightConjugate_eq_self_iff R t).mp h.symm))
  have hR12 : R1 ≠ R2 := by
    intro h
    apply hR01
    have h' := congrArg (fun B => rightConjugate B y⁻¹) h
    simp only [hR1, hR2, ht, rightConjugate_mul] at h'
    rw [show y * y⁻¹ = 1 by group, show y * y * y⁻¹ = y by group, rightConjugate_one] at h'
    exact h'
  have h2R : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hF.isPGroup_of_mem hRΔ)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hF.ne_bot_of_mem hRΔ (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2R
  set u : G := (u' : G) with hu
  have huR : u ∈ R := u'.2
  have huo : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hu'
  have huu : u * u = 1 := by rw [← pow_two, ← huo]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    norm_num at huo
  set a1 := y⁻¹ * u * y with ha1
  set a2 := t⁻¹ * u * t with ha2
  have ha1R : a1 ∈ R1 := conj_mem_rightConjugate huR y
  have ha2R : a2 ∈ R2 := conj_mem_rightConjugate huR t
  have c01 : u * a1 = a1 * u := hcomm R hRΓ R1 hR1Γ hR01 u huR a1 ha1R
  have c02 : u * a2 = a2 * u := hcomm R hRΓ R2 hR2Γ hR02 u huR a2 ha2R
  have c12 : a1 * a2 = a2 * a1 := hcomm R1 hR1Γ R2 hR2Γ hR12 a1 ha1R a2 ha2R
  have ha11 : a1 * a1 = 1 := by
    calc a1 * a1 = y⁻¹ * (u * u) * y := by rw [ha1]; group
      _ = 1 := by rw [huu]; group
  have ha22 : a2 * a2 = 1 := by
    calc a2 * a2 = t⁻¹ * (u * u) * t := by rw [ha2]; group
      _ = 1 := by rw [huu]; group
  have ha2' : a2 = t * u * t := by rw [ha2, htinv]
  have hC : ∀ c ∈ W, t * c = c * t → y * c = c * y := by
    intro c hcW hct
    have hcNT : c ∈ normalizer (T : Set G) :=
      hF.mem_normalizer_of_mem hT ((zpowers_le).mpr htT) (zpowers_ne_bot_of_ne_one ht1)
        (hWS hcW) (mem_normalizer_zpowers_of_commute hct.symm)
    have hkT : y * c * y⁻¹ * c⁻¹ ∈ T := by
      have h1 := (mem_normalizer_iff.mp hcNT y⁻¹).mp (inv_mem hyT)
      have h2 := mul_mem hyT h1
      simpa [mul_assoc] using h2
    have hkW : y * c * y⁻¹ * c⁻¹ ∈ W := by
      have h1 := (mem_normalizer_iff.mp (hTW y hyT) c).mp hcW
      exact mul_mem h1 (inv_mem hcW)
    have hk := hTW1 _ hkT hkW
    calc y * c = (y * c * y⁻¹ * c⁻¹) * (c * y) := by group
      _ = c * y := by rw [hk, one_mul]
  have hRW' : u ∈ W := hRW R hRΓ huR
  have ha1W : a1 ∈ W := hRW R1 hR1Γ ha1R
  have ha2W : a2 ∈ W := hRW R2 hR2Γ ha2R
  have hc1t : t * (u * a2) = (u * a2) * t := by
    have c02' : t * u * t * u = u * (t * u * t) := by
      rw [← ha2']
      exact c02.symm
    rw [ha2']
    calc t * (u * (t * u * t)) = (t * u * t * u) * t := by group
      _ = (u * (t * u * t)) * t := by rw [c02']
  have hyc1 := hC _ (mul_mem hRW' ha2W) hc1t
  set a3 := y⁻¹ * a2 * y with ha3
  have h13 : a1 * a3 = u * a2 := by
    calc a1 * a3 = y⁻¹ * (u * a2) * y := by rw [ha1, ha3]; group
      _ = y⁻¹ * ((u * a2) * y) := by group
      _ = y⁻¹ * (y * (u * a2)) := by rw [hyc1]
      _ = u * a2 := by group
  have hta1 : t * a1 * t⁻¹ = a3 := by
    rw [ha3, ha2, ha1, ht]
    calc y * y * (y⁻¹ * u * y) * (y * y)⁻¹ = y * u * y⁻¹ := by group
      _ = (y⁻¹ * y⁻¹ * y⁻¹) * u * (y * y * y) := by rw [hy3, hy3']
      _ = y⁻¹ * ((y * y)⁻¹ * u * (y * y)) * y := by group
  have htu : t * u * t⁻¹ = a2 := by rw [ha2', htinv]
  have ha3' : a3 = a1 * u * a2 := by
    calc a3 = (a1 * a1) * a3 := by rw [ha11, one_mul]
      _ = a1 * (a1 * a3) := by group
      _ = a1 * (u * a2) := by rw [h13]
      _ = a1 * u * a2 := by group
  have h23 : a2 * a3 = u * a1 := by
    rw [ha3']
    calc a2 * (a1 * u * a2) = (a2 * a1) * u * a2 := by group
      _ = (a1 * a2) * u * a2 := by rw [c12]
      _ = a1 * (a2 * u) * a2 := by group
      _ = a1 * (u * a2) * a2 := by rw [c02]
      _ = a1 * u * (a2 * a2) := by group
      _ = u * a1 := by rw [ha22, mul_one, c01]
  have hc2t : t * (u * a1) = (u * a1) * t := by
    have h : t * (u * a1) * t⁻¹ = u * a1 := by
      calc t * (u * a1) * t⁻¹ = (t * u * t⁻¹) * (t * a1 * t⁻¹) := by group
        _ = a2 * a3 := by rw [htu, hta1]
        _ = u * a1 := h23
    calc t * (u * a1) = (t * (u * a1) * t⁻¹) * t := by group
      _ = (u * a1) * t := by rw [h]
  have hyc2 := hC _ (mul_mem hRW' ha1W) hc2t
  have hya1 : y⁻¹ * a1 * y = a2 := by rw [ha1, ha2, ht]; group
  have h12 : a1 * a2 = a1 * u := by
    calc a1 * a2 = (y⁻¹ * u * y) * (y⁻¹ * a1 * y) := by rw [hya1, ha1]
      _ = y⁻¹ * (u * a1) * y := by rw [ha1]; group
      _ = y⁻¹ * ((u * a1) * y) := by group
      _ = y⁻¹ * (y * (u * a1)) := by rw [hyc2]
      _ = u * a1 := by group
      _ = a1 * u := c01
  have ha2u : a2 = u := mul_left_cancel h12
  have hmem : u ∈ R ⊓ R2 := ⟨huR, ha2u ▸ ha2R⟩
  rw [hF.inf_eq_bot R hRΔ R2 (hΓ hR2Γ) hR02, mem_bot] at hmem
  exact hu1 hmem

theorem commutes (hF : TIFamily S Δ) :
    ∀ R₁ ∈ Δ, ∀ R₂ ∈ Δ, R₁ ≠ R₂ → Commutes R₁ R₂ := by
  classical
  have hΔfin : Δ.Finite := Set.toFinite Δ
  let P : Finset (Subgroup G) → Prop := fun Γ =>
    (↑Γ : Set (Subgroup G)) ⊆ Δ ∧ ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → Commutes R₁ R₂
  have hne : ((hΔfin.toFinset.powerset).filter P).Nonempty :=
    ⟨∅, by simp [P]⟩
  obtain ⟨Γ, hΓmem, hΓmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at hΓmem
  obtain ⟨-, hΓΔ, hΓc⟩ := hΓmem
  set Γs : Set (Subgroup G) := (Γ : Set (Subgroup G)) with hΓs
  have hΓc' : ∀ R₁ ∈ Γs, ∀ R₂ ∈ Γs, R₁ ≠ R₂ → Commutes R₁ R₂ := hΓc
  have hself : ∀ T ∈ Δ, (∀ t ∈ T, ∀ R ∈ Γs, rightConjugate R t ∈ Γs) → T ∈ Γ := by
    intro T hT hperm
    by_contra hTΓ
    have hcT := hF.commutes_of_permutes hΓΔ hΓc' hT hTΓ hperm
    have hP : P (insert T Γ) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_insert]
        exact Set.insert_subset hT hΓΔ
      · intro R₁ h₁ R₂ h₂ h12
        rw [Finset.mem_insert] at h₁ h₂
        rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
        · exact absurd rfl h12
        · exact hcT R₂ h₂
        · exact (hcT R₁ h₁).symm
        · exact hΓc R₁ h₁ R₂ h₂ h12
    have hmem : insert T Γ ∈ (hΔfin.toFinset.powerset).filter P := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, hP⟩
      intro R hR
      rw [Set.Finite.mem_toFinset]
      exact hP.1 hR
    have := hΓmax _ hmem
    rw [Finset.card_insert_of_notMem hTΓ] at this
    omega
  set W : Subgroup G := ⨆ R : Γs, (R : Subgroup G) with hW
  have hRW : ∀ R ∈ Γs, R ≤ W := fun R hR => le_iSup (fun R : Γs => (R : Subgroup G)) ⟨R, hR⟩
  have hWN : ∀ R ∈ Γs, W ≤ normalizer (R : Set G) :=
    fun R hR => iSup_le_normalizer_of_commutes hΓc' hR
  have hWS : W ≤ S := iSup_le fun R => hF.le_S _ (hΓΔ R.2)
  have hm1 : ∀ T ∈ Δ, T ≤ W → T ∈ Γ := by
    intro T hT hTW
    refine hself T hT fun t ht R hR => ?_
    rw [(rightConjugate_eq_self_iff R t).mpr (hWN R hR (hTW ht))]
    exact hR
  have hm2 : ∀ s ∈ S, s ∈ normalizer (W : Set G) → ∀ R ∈ Γs, rightConjugate R s ∈ Γs := by
    intro s hsS hsN R hR
    refine hm1 _ (hF.conj_mem _ (hΓΔ hR) s hsS) ?_
    exact (rightConjugate_mono s (hRW R hR)).trans
      ((rightConjugate_eq_self_iff W s).mpr hsN).le
  have hm3 : ∀ T ∈ Δ, T ≤ S ⊓ normalizer (W : Set G) → T ∈ Γ := by
    intro T hT hTM
    exact hself T hT fun t ht R hR => hm2 t (hTM ht).1 (hTM ht).2 R hR
  set M := S ⊓ normalizer (W : Set G) with hM
  have hm4 : ∀ s ∈ S, s ∈ normalizer (M : Set G) → s ∈ M := by
    intro s hsS hsN
    refine ⟨hsS, mem_normalizer_iSup fun R hR => ?_⟩
    have hRM : R ≤ M := _root_.le_inf (hF.le_S _ (hΓΔ hR)) ((hRW R hR).trans le_normalizer)
    have hRs : rightConjugate R s ∈ Γs := by
      refine hm3 _ (hF.conj_mem _ (hΓΔ hR) s hsS) ?_
      exact (rightConjugate_mono s hRM).trans ((rightConjugate_eq_self_iff M s).mpr hsN).le
    exact hRW _ hRs
  have hm5 : M = S := by
    by_contra hMS
    have hlt : M < S := lt_of_le_of_ne inf_le_left hMS
    obtain ⟨s, hsS, hsM, hsN⟩ :=
      LiteratureLocal.TightCommuting.exists_mem_normalizer_not_mem hF.pGroup hlt
    exact hsM (hm4 s hsS hsN)
  have hm6 : ∀ T ∈ Δ, T ∈ Γ := fun T hT => hm3 T hT (hm5 ▸ hF.le_S T hT)
  intro R₁ h₁ R₂ h₂ h12
  exact hΓc R₁ (hm6 R₁ h₁) R₂ (hm6 R₂ h₂) h12

end TIFamily

theorem lemma25 [Finite G] {S : Subgroup G} {Δ : Set (Subgroup G)} (hS : IsPGroup 2 S)
    (hΔS : ∀ R ∈ Δ, R ≤ S) (hinv : ∀ R ∈ Δ, ∀ s ∈ S, rightConjugate R s ∈ Δ)
    (hcard : ∀ R ∈ Δ, ∀ T ∈ Δ, Nat.card R = Nat.card T) (hΦ : ∀ R ∈ Δ, frattini R ≠ ⊥)
    (hTI : ∀ R ∈ Δ, ∀ T ∈ Δ, R ≠ T → R ⊓ T = ⊥) :
    ∀ R ∈ Δ, ∀ T ∈ Δ, R ≠ T → ⁅R, T⁆ = ⊥ := by
  intro R hR T hT hne
  have h := TIFamily.commutes ⟨hS, hΔS, hinv, hcard, hΦ, hTI⟩ R hR T hT hne
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact (h a ha b hb).symm

end CFSG.ComponentClassification.Asc76X

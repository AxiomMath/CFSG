module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5CaseCard
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem sig_comm_eq_one {s : G} (hs : s ∈ (sec3DData e t).Sig)
    (hc : ∀ s' ∈ (sec3DData e t).Sig, s * s' = s' * s) : s = 1 := by
  have hse : s ∈ zpowers (sec3DData e t).e := by
    rw [← sig_inf_cent_e]
    exact ⟨hs, mem_centralizer_singleton_iff.mpr (hc _ d_e_mem_Sig)⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hse
  have hx := hc _ d_x₃_mem_Sig
  have h1 : (sec3DData e t).x₃ * (sec3DData e t).e ^ k * (sec3DData e t).x₃⁻¹ =
      (sec3DData e t).e ^ k := by
    rw [← hx, mul_inv_cancel_right]
  rw [← conj_zpow, x₃_conj_e, inv_zpow'] at h1
  have h2 : (sec3DData e t).e ^ (2 * k) = 1 := by
    rw [two_mul, zpow_add]
    nth_rewrite 1 [← h1]
    rw [zpow_neg, inv_mul_cancel]
  have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [orderOf_e] at h3
  have h4 : ((orderOf (sec3DData e t).e : ℕ) : ℤ) ∣ k := by
    rw [orderOf_e]
    push_cast at h3 ⊢
    omega
  exact orderOf_dvd_iff_zpow_eq_one.mp h4

section Dec

variable
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem exists_dec (hΘ : ThetaSpec t e Θ)
    (hdec : ∀ y ∈ autT, y ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) →
      ∃ s ∈ chSig.grp, ∃ a ∈ chA3.grp, ∃ i < 3, y = s * a * dP ^ i)
    {n : G} (hnA : n ∈ centralizer ((sec3DData e t).A₄ : Set G)) (hnH : n ∈ (sec3DData e t).H) :
    ∃ s ∈ (sec3DData e t).Sig, ∃ a ∈ (sec3DData e t).A₃, ∃ x : G, n = s * a * x ∧
      x ∈ centralizer ((sec3DData e t).Λ : Set G) ∧
      x ∈ centralizer ((sec3DData e t).Sig : Set G) ∧
      x ∈ Subgroup.normalizer ((sec3DData e t).A₃ : Set G) ∧ x ^ 3 ∈ zpowers t := by
  set n' : centralizer ({t} : Set G) := ⟨n, hnH⟩ with hn'
  have hC : Θ n' ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) :=
    (hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chA4) n').mp hnA
  obtain ⟨ŝ, hŝ, â, hâ, i, hi, hy⟩ := hdec _ (hΘ.mem_autT n') hC
  set s' : T46 := ⟨ŝ, grp_le_T46 gensOK_chSig hŝ⟩ with hs'
  set a' : T46 := ⟨â, grp_le_T46 gensOK_chA3 hâ⟩ with ha'
  set sC : centralizer ({t} : Set G) :=
    ⟨iotaG e s', hΘ.L_le_centralizer (iotaG_mem s')⟩ with hsC
  set aC : centralizer ({t} : Set G) :=
    ⟨iotaG e a', hΘ.L_le_centralizer (iotaG_mem a')⟩ with haC
  set x : centralizer ({t} : Set G) := (sC * aC)⁻¹ * n' with hx
  have hΘx : Θ x = dP ^ i := by
    rw [hx, map_mul, map_inv, map_mul, hsC, haC, hΘ.apply_iotaG, hΘ.apply_iotaG, hy]
    show (ŝ * â)⁻¹ * (ŝ * â * dP ^ i) = dP ^ i
    group
  refine ⟨iotaG e s', iotaG_mem_toG.mpr hŝ, iotaG e a', iotaG_mem_toG.mpr hâ, x, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hsC, haC]
    group
    rfl
  · rw [show (sec3DData e t).Λ = toG e chLam.grp from rfl,
      hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chLam), hΘx]
    exact pow_mem dP_centralizer_spec.2.2.2.2.2.1 i
  · rw [show (sec3DData e t).Sig = toG e chSig.grp from rfl,
      hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chSig), hΘx]
    exact pow_mem dP_centralizer_spec.2.2.2.2.1 i
  · rw [show (sec3DData e t).A₃ = toG e chA3.grp from rfl,
      hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA3), hΘx]
    exact pow_mem norm_chA3.1 i
  · have h3 : Θ (x ^ 3) = 1 := by
      rw [map_pow, hΘx, ← pow_mul, mul_comm, pow_mul, dP_pow_three, one_pow]
    have := (hΘ.eq_one_iff (x ^ 3)).mp h3
    rwa [Subgroup.coe_pow] at this

theorem Λ_comm_CA₄_of (hΘ : ThetaSpec t e Θ)
    (hdec : ∀ y ∈ autT, y ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) →
      ∃ s ∈ chSig.grp, ∃ a ∈ chA3.grp, ∃ i < 3, y = s * a * dP ^ i) :
    ∀ l ∈ (sec3DData e t).Λ, ∀ n ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
      ⁅l, n⁆ ∈ (sec3DData e t).withT (sec3DData e t).A₃ := by
  intro l hl n hn
  obtain ⟨s, hs, a, ha, x, rfl, hxΛ, -, -, -⟩ := exists_dec hΘ hdec hn.1 hn.2
  have hls : l * s = s * l := d_Λ_comm_Sig l hl s hs
  have hlx : l * x = x * l := mem_centralizer_iff.mp hxΛ l hl
  have hxl : x * l⁻¹ = l⁻¹ * x := by
    calc x * l⁻¹ = l⁻¹ * (l * x) * l⁻¹ := by group
      _ = l⁻¹ * (x * l) * l⁻¹ := by rw [hlx]
      _ = l⁻¹ * x := by group
  have hla : l * a * l⁻¹ ∈ (sec3DData e t).A₃ := (mem_normalizer_iff.mp (d_Λ_le_NA₃ hl) a).mp ha
  have key : ⁅l, s * a * x⁆ = s * (l * a * l⁻¹ * a⁻¹) * s⁻¹ := by
    rw [commutatorElement_def]
    calc l * (s * a * x) * l⁻¹ * (s * a * x)⁻¹ = (l * s) * a * (x * l⁻¹) * x⁻¹ * a⁻¹ * s⁻¹ := by
          group
      _ = (s * l) * a * (l⁻¹ * x) * x⁻¹ * a⁻¹ * s⁻¹ := by rw [hls, hxl]
      _ = s * (l * a * l⁻¹ * a⁻¹) * s⁻¹ := by group
  rw [key]
  exact mem_sup_left ((mem_normalizer_iff.mp (d_Sig_le_NA₃ hs) _).mp (mul_mem hla (inv_mem ha)))

theorem center_CA₄_of (hΘ : ThetaSpec t e Θ)
    (hdec : ∀ y ∈ autT, y ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) →
      ∃ s ∈ chSig.grp, ∃ a ∈ chA3.grp, ∃ i < 3, y = s * a * dP ^ i) :
    ∀ n ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
      (∀ m ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H,
        ⁅n, m⁆ ∈ (sec3DData e t).withT (sec3DData e t).A₃) →
      n ^ 3 ∈ (sec3DData e t).withT (sec3DData e t).A₃ := by
  intro n hn hcomm
  obtain ⟨s, hs, a, ha, x, rfl, -, hxS, hxN, hx3⟩ := exists_dec hΘ hdec hn.1 hn.2
  have hsc : ∀ s' ∈ (sec3DData e t).Sig, s * s' = s' * s := by
    intro s' hs'
    have hs'L : s' ∈ L := toG_le_L _ hs'
    have hm : s' ∈ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H :=
      Subgroup.mem_inf.mpr ⟨d_Sig_le_cent_A₄ hs', hΘ.L_le_centralizer hs'L⟩
    have h1 := hcomm s' hm
    have hxs : x * s' = s' * x := (mem_centralizer_iff.mp hxS s' hs').symm
    have hxs' : x * s' * x⁻¹ = s' := by rw [hxs, mul_inv_cancel_right]
    have key : ⁅s * a * x, s'⁆ = (s * (a * (s' * a⁻¹ * s'⁻¹)) * s⁻¹) * ⁅s, s'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s * a * x * s' * (s * a * x)⁻¹ * s'⁻¹ = s * a * (x * s' * x⁻¹) * a⁻¹ * s⁻¹ * s'⁻¹ := by
            group
        _ = s * a * s' * a⁻¹ * s⁻¹ * s'⁻¹ := by rw [hxs']
        _ = s * (a * (s' * a⁻¹ * s'⁻¹)) * s⁻¹ * (s * s' * s⁻¹ * s'⁻¹) := by group
    have hf : s * (a * (s' * a⁻¹ * s'⁻¹)) * s⁻¹ ∈ (sec3DData e t).A₃ := by
      refine (mem_normalizer_iff.mp (d_Sig_le_NA₃ hs) _).mp (mul_mem ha ?_)
      exact (mem_normalizer_iff.mp (d_Sig_le_NA₃ hs') _).mp (inv_mem ha)
    have h2 : ⁅s, s'⁆ ∈ toG e chA3.grp ⊔ zpowers t := by
      have h3 : ⁅s, s'⁆ = (s * (a * (s' * a⁻¹ * s'⁻¹)) * s⁻¹)⁻¹ * ⁅s * a * x, s'⁆ := by
        rw [key, inv_mul_cancel_left]
      rw [h3]
      exact mul_mem (inv_mem (mem_sup_left hf)) h1
    have h4 : ⁅s, s'⁆ ∈ (sec3DData e t).A₃ := by
      have hL : ⁅s, s'⁆ ∈ L := by
        rw [commutatorElement_def]
        have hsL : s ∈ L := toG_le_L _ hs
        exact mul_mem (mul_mem (mul_mem hsL hs'L) (inv_mem hsL)) (inv_mem hs'L)
      rw [show (sec3DData e t).A₃ = toG e chA3.grp from rfl,
        ← hΘ.toG_sup_inf_L (grp_le_T46 gensOK_chA3)]
      exact Subgroup.mem_inf.mpr ⟨h2, hL⟩
    have h5 : ⁅s, s'⁆ ∈ (sec3DData e t).Sig ⊓ (sec3DData e t).A₃ := by
      refine Subgroup.mem_inf.mpr ⟨?_, h4⟩
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hs hs') (inv_mem hs)) (inv_mem hs')
    rw [sig_inf_A₃, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
    exact h5
  have hs1 := sig_comm_eq_one hs hsc
  subst hs1
  have hxa : x * a * x⁻¹ ∈ (sec3DData e t).A₃ := (mem_normalizer_iff.mp hxN a).mp ha
  have hxxa : x * (x * a * x⁻¹) * x⁻¹ ∈ (sec3DData e t).A₃ := (mem_normalizer_iff.mp hxN _).mp hxa
  have e3 : (1 * a * x) ^ 3 = a * (x * a * x⁻¹) * (x * (x * a * x⁻¹) * x⁻¹) * x ^ 3 := by
    rw [one_mul, pow_three, pow_three]
    group
  rw [e3]
  exact mul_mem (mem_sup_left (mul_mem (mul_mem ha hxa) hxxa)) (mem_sup_right hx3)

end Dec

end CFSG.EvenSmallLie.UnitarySix.Child5

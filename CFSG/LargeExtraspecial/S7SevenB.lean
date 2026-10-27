module

public import CFSG.LargeExtraspecial.S7Seven
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S45QMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem apply_mem_commSpace_of_comm {t x : S.O} (hxt : x * t = t * x) {v : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
  rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, hxt]

variable (S g) in
@[expose] noncomputable def resC {t : S.O}
    (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    Cbar S t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (Cbar S t).subtype) (Vt S g t) fun c _ hu => by
    rw [← hV] at hu ⊢
    exact apply_mem_commSpace_of_comm (comm_of_mem_Cbar c.2) hu

theorem coe_resC_apply {t : S.O} (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    (c : Cbar S t) (v : Vt S g t) :
    ((resC S g hV c v : Vt S g t) : S.Qt) = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem commutator_RmodN {t : S.O} (hs : IsSimpleGroup (RmodN S g t))
    (hn : S5.NonabelianSylowTwo (RmodN S g t)) :
    ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := RmodN S g t with hX
  have : IsSimpleGroup X := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      have := (commutator_eq_bot_iff_center_eq_top (G := X)).mp h
      intro a b
      have ha : a ∈ center X := this ▸ mem_top a
      exact (mem_center_iff.mp ha b).symm
    obtain ⟨P₀⟩ : Nonempty (Sylow 2 X) := inferInstance
    set P := (P₀ : Subgroup X).map X.subtype with hP
    have hPi : P.relIndex X = (P₀ : Subgroup X).index := by
      rw [Subgroup.relIndex, hP, Subgroup.subgroupOf,
        comap_map_eq_self_of_injective X.subtype_injective]
    obtain ⟨x, hx, y, hy, hxy⟩ := hn P (map_subtype_le _) (P₀.isPGroup'.map _)
      (hPi ▸ P₀.not_dvd_index)
    obtain ⟨x', -, rfl⟩ := hx
    obtain ⟨y', -, rfl⟩ := hy
    exact hxy (congrArg Subtype.val (hcomm x' y'))
  · rw [← map_subtype_commutator, h, ← MonoidHom.range_eq_map, range_subtype]

theorem comm_of_fix_Vt (H : Hyp4 S g) {t : S.O} (hN : Nbar S g t = zpowers t)
    (hperf : ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t) {c : S.O} (hcM : c ∈ S.Mbar)
    (hct : c * t = t * c) (hcV : ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {r : S.O}
    (hr : r ∈ Rbar S g t) : r * c = c * r := by
  obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hcM
  set c := S.ρ κ with hc
  have hmem : ∀ r ∈ Rbar S g t, r * c * r⁻¹ * c⁻¹ ∈ zpowers t := by
    intro r hr
    rw [← hN]
    refine mem_Nbar.mpr ⟨?_, fun v hv => ?_⟩
    · rw [show r * c * r⁻¹ * c⁻¹ = r * (c * r⁻¹ * c⁻¹) by group]
      exact mul_mem hr (conj_mem_Rbar hct (inv_mem hr))
    · have h1 : ((c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
        conv_lhs => rw [← hcV v hv]
        exact inv_apply_apply_O _ v
      have h2 := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hr) hv
      simp only [coe_mul_apply, h1, hcV _ h2, apply_inv_apply_O]
  have hcommR : ∀ r ∈ Rbar S g t, ∀ y ∈ zpowers t, r * y = y * r := by
    intro r hr y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (commute_of_mem_Rbar H.conj_mem hr) k).eq
  have hcommZ : ∀ y ∈ zpowers t, ∀ y' ∈ zpowers t, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨k', rfl⟩ := mem_zpowers_iff.mp hy'
    exact (Commute.zpow_zpow_self t k k').eq
  obtain ⟨f, hf⟩ : ∃ f : Rbar S g t →* S.O,
      ∀ r : Rbar S g t, f r = r * c * (r : S.O)⁻¹ * c⁻¹ :=
    ⟨{ toFun := fun r => r * c * (r : S.O)⁻¹ * c⁻¹
       map_one' := by simp
       map_mul' := fun a b => by
        have h1 := hcommR a a.2 _ (hmem b b.2)
        have h2 := hcommZ _ (hmem a a.2) _ (hmem b b.2)
        change (a : S.O) * b * c * ((a : S.O) * b)⁻¹ * c⁻¹ =
          (a * c * (a : S.O)⁻¹ * c⁻¹) * (b * c * (b : S.O)⁻¹ * c⁻¹)
        calc (a : S.O) * b * c * ((a : S.O) * b)⁻¹ * c⁻¹ =
            a * (b * c * (b : S.O)⁻¹ * c⁻¹) * c * (a : S.O)⁻¹ * c⁻¹ := by group
          _ = (b * c * (b : S.O)⁻¹ * c⁻¹) * a * c * (a : S.O)⁻¹ * c⁻¹ := by rw [h1]
          _ = (b * c * (b : S.O)⁻¹ * c⁻¹) * (a * c * (a : S.O)⁻¹ * c⁻¹) := by group
          _ = _ := h2.symm }, fun r => rfl⟩
  have hfz : ∀ r : Rbar S g t, f r ∈ zpowers t := fun r => (hf r).symm ▸ hmem r r.2
  have hf_comm : commutator (Rbar S g t) ≤ f.ker := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcommZ _ (hfz a) _ (hfz b)
  have hmemR : resV H.conj_mem t ⟨r, hr⟩ ∈ ⁅RmodN S g t, RmodN S g t⁆ := by
    rw [hperf, ← range_resV H.conj_mem t]
    exact ⟨_, rfl⟩
  rw [← range_resV H.conj_mem t, ← map_commutator_eq] at hmemR
  obtain ⟨r', hr'c, hr'e⟩ := hmemR
  have hn : ((r'⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O) ∈ zpowers t := by
    rw [← hN, ← resV_eq_one_iff H.conj_mem, map_mul, map_inv, hr'e, inv_mul_cancel]
  have hfn : f (r'⁻¹ * ⟨r, hr⟩) = 1 := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    rw [hf, ← hk]
    have htk : t ^ k * c = c * t ^ k := (Commute.zpow_left (show Commute t c from hct.symm) k).eq
    rw [htk]
    group
  have h1 : f r' = 1 := MonoidHom.mem_ker.mp (hf_comm hr'c)
  have h3 : r * c * r⁻¹ * c⁻¹ = 1 := by
    have h2 : f (r'⁻¹ * ⟨r, hr⟩) = f r'⁻¹ * f ⟨r, hr⟩ := f.map_mul _ _
    rw [hfn, f.map_inv, h1, inv_one, one_mul, hf] at h2
    exact h2.symm
  calc r * c = (r * c * r⁻¹ * c⁻¹) * c * r := by group
    _ = c * r := by rw [h3, one_mul]

section Seven

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t))
include hCE H hNo C ht ht1 hVQ hΩ hN h8

theorem Cbar_inf_centralizer_eq_bot :
    Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D' := Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) with hD'
  have hD'M : D' ≤ S.Mbar := inf_le_left.trans Cbar_le_Mbar
  have hP : IsPGroup 2 D' := by
    rw [IsPGroup.iff_orderOf]
    intro d
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf d) with ⟨k, hk⟩ | ⟨p, hp, hpd, hpo⟩
    · exact ⟨k, hk⟩
    · exfalso
      rw [← Subgroup.orderOf_coe] at hpd
      set e := (d : S.O) ^ (orderOf (d : S.O) / p) with he
      have hd0 : orderOf (d : S.O) ≠ 0 := (orderOf_pos _).ne'
      have heo : orderOf e = p := orderOf_pow_orderOf_div hd0 hpd
      have hdR : ∀ r ∈ Rbar S g t, r * d = d * r := fun r hr =>
        mem_centralizer_iff.mp (d.2.2) r hr
      have heR : ∀ r ∈ Rbar S g t, r * e = e * r := fun r hr =>
        (Commute.pow_right (hdR r hr) _).eq
      have hK := S5.timmesfeld_5_3 H hNo C (K := zpowers e)
        (zpowers_le.mpr (pow_mem (hD'M d.2) _)) inferInstance
        (by rw [Nat.card_zpowers, heo]; exact hpo)
        (fun h0 => by
          have : e = 1 := by
            have : e ∈ zpowers e := mem_zpowers e
            rwa [h0, mem_bot] at this
          rw [this, orderOf_one] at heo
          exact hp.one_lt.ne' heo.symm)
        (fun s hs x hx => by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
          have := (Commute.zpow_right (heR s (Lbar_le_Rbar ht hs)) k).eq
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
          exact zpow_mem (mem_zpowers e) k)
      apply hK.2
      rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
      intro s hs
      exact heR s (Lbar_le_Rbar ht hs)
  have hnorm : S.Mbar ≤ normalizer (D' : Set S.O) := by
    intro x hx
    obtain ⟨σ, hσ, c', hc', rfl⟩ := exists_mul_Cbar hCE H hNo C ht ht1 hVQ hΩ hN h8 hx
    refine S4.mem_normalizer_of_conj_le fun p hp => ?_
    obtain ⟨hpC, hpR⟩ := hp
    set q := c' * p * c'⁻¹ with hq
    have hqC : q ∈ Cbar S t := mul_mem (mul_mem hc' hpC) (inv_mem hc')
    have hqR : q ∈ centralizer (Rbar S g t : Set S.O) := by
      rw [mem_centralizer_iff]
      intro r hr
      obtain ⟨κ', hκ'⟩ := MonoidHom.mem_range.mp (S.Mbar.inv_mem (Cbar_le_Mbar hc'))
      have hκt : S.ρ κ' * t = t * S.ρ κ' := by
        rw [hκ']
        have := comm_of_mem_Cbar hc'
        calc c'⁻¹ * t = c'⁻¹ * (t * c') * c'⁻¹ := by group
          _ = c'⁻¹ * (c' * t) * c'⁻¹ := by rw [this]
          _ = t * c'⁻¹ := by group
      have hr' : c'⁻¹ * r * c' ∈ Rbar S g t := by
        have := conj_mem_Rbar hκt hr
        rwa [hκ', inv_inv] at this
      have h1 := mem_centralizer_iff.mp hpR _ hr'
      calc r * q = c' * ((c'⁻¹ * r * c') * p) * c'⁻¹ := by rw [hq]; group
        _ = c' * (p * (c'⁻¹ * r * c')) * c'⁻¹ := by rw [h1]
        _ = q * r := by rw [hq]; group
    have hσq : σ * q = q * σ := (mem_centralizer_iff.mp hqC.2 σ hσ)
    have e : σ * c' * p * (σ * c')⁻¹ = q := by
      calc σ * c' * p * (σ * c')⁻¹ = σ * q * σ⁻¹ := by rw [hq]; group
        _ = q := by rw [hσq]; group
    rw [e]
    exact ⟨hqC, hqR⟩
  exact Setting.s12_noNormalTwo_Mbar S D' hD'M hP hnorm

theorem resC_injective (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    Function.Injective (resC S g hV) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcV : ∀ v ∈ Vt S g t, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    (restrictHom_eq_one_iff _ _ _ c).mp hc
  obtain ⟨hs, hn⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ (by omega)
  have hperf := commutator_RmodN hs hn
  have hmem : (c : S.O) ∈ Cbar S t ⊓ centralizer (Rbar S g t : Set S.O) :=
    ⟨c.2, mem_centralizer_iff.mpr fun r hr =>
      comm_of_fix_Vt H hN hperf (Cbar_le_Mbar c.2) (comm_of_mem_Cbar c.2) hcV hr⟩
  rw [Cbar_inf_centralizer_eq_bot hCE H hNo C ht ht1 hVQ hΩ hN h8, mem_bot] at hmem
  exact Subtype.ext hmem

end Seven

end CFSG.LargeExtraspecial.S7

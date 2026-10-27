module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFourGroupNormalizer
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCenterFour

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

section TwoCore

theorem twoCore_le_centralizer (x : G) :
    inSubgroup (pCore 2) (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G) :=
  map_subtype_le _

theorem isPGroup_twoCore (x : G) : IsPGroup 2 (inSubgroup (pCore 2) (centralizer ({x} : Set G))) :=
  (pCore_isPGroup (p := 2) (G := centralizer ({x} : Set G))).map _

theorem conj_mem_twoCore {x g y : G} (hg : g ∈ centralizer ({x} : Set G))
    (hy : y ∈ inSubgroup (pCore 2) (centralizer ({x} : Set G))) :
    g * y * g⁻¹ ∈ inSubgroup (pCore 2) (centralizer ({x} : Set G)) := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, (pCore_normal (p := 2)).conj_mem y' hy' _, rfl⟩

theorem le_twoCore {x : G} {W : Subgroup G} (hW : W ≤ centralizer ({x} : Set G))
    (hp : IsPGroup 2 W) (hn : ∀ g ∈ centralizer ({x} : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    W ≤ inSubgroup (pCore 2) (centralizer ({x} : Set G)) := by
  have hN : (W.subgroupOf (centralizer ({x} : Set G))).Normal :=
    ⟨fun n hn' g => by
      rw [mem_subgroupOf] at hn' ⊢
      exact hn g g.2 n hn'⟩
  have hle : W.subgroupOf (centralizer ({x} : Set G)) ≤ pCore 2 (centralizer ({x} : Set G)) :=
    le_sSup ⟨hN, hp.of_equiv (subgroupOfEquivOfLe hW).symm⟩
  intro w hw
  exact ⟨⟨w, hW hw⟩, hle (by rw [mem_subgroupOf]; exact hw), rfl⟩

theorem conj_mem_twoCore_conj {x h y : G}
    (hy : y ∈ inSubgroup (pCore 2) (centralizer ({x} : Set G))) :
    h⁻¹ * y * h ∈ inSubgroup (pCore 2) (centralizer ({h⁻¹ * x * h} : Set G)) := by
  set W := (inSubgroup (pCore 2) (centralizer ({x} : Set G))).map (MulAut.conj h⁻¹).toMonoidHom
  have hmemW : ∀ {v : G}, v ∈ inSubgroup (pCore 2) (centralizer ({x} : Set G)) →
      h⁻¹ * v * h ∈ W := fun {v} hv =>
    ⟨v, hv, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  refine le_twoCore (W := W) ?_ ((isPGroup_twoCore x).map _) ?_ (hmemW hy)
  · rintro _ ⟨v, hv, rfl⟩
    have hvx := mem_centralizer_singleton_iff.mp (twoCore_le_centralizer x hv)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc h⁻¹ * v * h * (h⁻¹ * x * h) = h⁻¹ * (v * x) * h := by group
      _ = h⁻¹ * (x * v) * h := by rw [hvx]
      _ = h⁻¹ * x * h * (h⁻¹ * v * h) := by group
  · rintro g hg _ ⟨v, hv, rfl⟩
    have hgx : h * g * h⁻¹ ∈ centralizer ({x} : Set G) := by
      have hg' := mem_centralizer_singleton_iff.mp hg
      rw [mem_centralizer_singleton_iff]
      calc h * g * h⁻¹ * x = h * (g * (h⁻¹ * x * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * x * h) * g) * h⁻¹ := by rw [hg']
        _ = x * (h * g * h⁻¹) := by group
    have h1 := hmemW (conj_mem_twoCore hgx hv)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    convert h1 using 1
    group

end TwoCore

theorem eq_or_eq_inv_of_mem_zpowers {c x : G} (hc : orderOf c = 4) (hx : x ∈ zpowers c)
    (hx2 : x ^ 2 = c ^ 2) : x = c ∨ x = c⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  have hc4 : c ^ 4 = 1 := hc ▸ pow_orderOf_eq_one c
  have hc2 : c ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hc] at this
    norm_num at this
  have hj : c ^ i = c ^ (i % 4).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num)), ← zpow_mod_orderOf,
      hc]
    rfl
  have hlt : (i % 4).toNat < 4 := by omega
  rw [hj] at hx2 ⊢
  interval_cases h : (i % 4).toNat
  · rw [pow_zero, one_pow] at hx2
    exact absurd hx2.symm hc2
  · left; exact pow_one c
  · rw [← pow_mul, show 2 * 2 = 4 from rfl, hc4] at hx2
    exact absurd hx2.symm hc2
  · right
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hc4

theorem mem_normalizer_of_conj_mem {g : G} {H : Subgroup G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem mutual_cyclic_four_roots_elementary_common_centralizer [Finite G] {z a : G}
    (hz : orderOf z = 2) (ha : orderOf a = 2) (hza : z ≠ a) (hcomm : z * a = a * z)
    {U N C Qz Qa P R K : Subgroup G} (hU : U = closure ({z, a} : Set G))
    (hN : N = normalizer (U : Set G)) (hC : C = centralizer (U : Set G))
    (hQz : Qz = inSubgroup (pCore 2) (centralizer ({z} : Set G)))
    (hQa : Qa = inSubgroup (pCore 2) (centralizer ({a} : Set G)))
    (hP : P = Qz ⊓ centralizer ({a} : Set G)) (hR : R = Qa ⊓ centralizer ({z} : Set G))
    (hK : K = Qz ⊓ Qa) {c s : G}
    (hcZ : (center Qz).map Qz.subtype = zpowers c) (hsZ : (center Qa).map Qa.subtype = zpowers s)
    (hc2 : c ^ 2 = z) (hs2 : s ^ 2 = a) (hca : a⁻¹ * c * a = c⁻¹) (hsz : z⁻¹ * s * z = s⁻¹)
    (hPe : CFSG.IsElementaryAbelian 2 P) (hRe : CFSG.IsElementaryAbelian 2 R) :
    a ∉ Qz ∧ z ∉ Qa ∧ K = P ⊓ R ∧
      (P = K ⊔ zpowers z ∧ K ⊓ zpowers z = ⊥) ∧ (R = K ⊔ zpowers a ∧ K ⊓ zpowers a = ⊥) ∧
      (((P : Set G) * (R : Set G) = ((P ⊔ R : Subgroup G) : Set G)) ∧ P ⊔ R = P ⊔ zpowers a ∧
        P ⊔ R = R ⊔ zpowers z ∧ P ⊔ R = K ⊔ U ∧ K ⊓ U = ⊥ ∧
        CFSG.IsElementaryAbelian 2 (P ⊔ R : Subgroup G)) ∧
      N ≤ normalizer (K : Set G) ∧ N ≤ normalizer ((P ⊔ R : Subgroup G) : Set G) ∧
      (Function.Surjective (U.normalizerMonoidHom) ∧
        Nonempty (MulAut U ≃* Equiv.Perm (Fin 3))) ∧
      (∀ k ∈ K, k * c = c * k ∧ k * s = s * k) ∧
      (c⁻¹ * z * c = z ∧ c⁻¹ * a * c = a * z ∧ c⁻¹ * (a * z) * c = a) ∧
      (s⁻¹ * a * s = a ∧ s⁻¹ * z * s = z * a ∧ s⁻¹ * (z * a) * s = z) ∧ z * a ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  obtain ⟨hc4, hs4, hcN, hsN, ⟨hcz, hcaz, hcaz2⟩, ⟨hsa, hszz, hsza⟩, ⟨hCn, ⟨hiso⟩, hS3⟩, hNz, -,
    hidx, -, -, -, -⟩ :=
    two_cyclic_four_roots_full_four_group_normalizer hz ha hza hcomm hU hN hC hc2 hs2 hca hsz
  have hQzC : Qz ≤ centralizer ({z} : Set G) := hQz ▸ twoCore_le_centralizer z
  have hQaC : Qa ≤ centralizer ({a} : Set G) := hQa ▸ twoCore_le_centralizer a
  have hcen : ∀ {Q : Subgroup G} {g : G}, (center Q).map Q.subtype = zpowers g →
      g ∈ Q ∧ ∀ y ∈ Q, y * g = g * y := by
    intro Q g hg
    obtain ⟨g', hg', rfl⟩ : g ∈ (center Q).map Q.subtype := hg ▸ mem_zpowers g
    exact ⟨g'.2, fun y hy => congrArg Subtype.val (mem_center_iff.mp hg' ⟨y, hy⟩)⟩
  obtain ⟨hcQ, hcQc⟩ := hcen hcZ
  obtain ⟨hsQ, hsQc⟩ := hcen hsZ
  have hzQ : z ∈ Qz := hc2 ▸ pow_mem hcQ 2
  have haQ : a ∈ Qa := hs2 ▸ pow_mem hsQ 2
  have haQz : a ∉ Qz := by
    intro h
    have hc' : c = c⁻¹ := by
      calc c = a⁻¹ * (a * c) := by group
        _ = a⁻¹ * (c * a) := by rw [hcQc a h]
        _ = c⁻¹ := by rw [← mul_assoc, hca]
    apply hz1
    rw [← hc2, pow_two]
    nth_rewrite 2 [hc']
    exact mul_inv_cancel c
  have hzQa : z ∉ Qa := by
    intro h
    have hs' : s = s⁻¹ := by
      calc s = z⁻¹ * (z * s) := by group
        _ = z⁻¹ * (s * z) := by rw [hsQc z h]
        _ = s⁻¹ := by rw [← mul_assoc, hsz]
    apply ha1
    rw [← hs2, pow_two]
    nth_rewrite 2 [hs']
    exact mul_inv_cancel s
  have hKPR : K = P ⊓ R := by
    rw [hK, hP, hR]
    apply le_antisymm
    · intro x hx
      obtain ⟨hxz, hxa⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxz, hQaC hxa⟩, mem_inf.mpr ⟨hxa, hQzC hxz⟩⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨(mem_inf.mp hx1).1, (mem_inf.mp hx2).1⟩
  have hKP : K ≤ P := hKPR ▸ inf_le_left
  have hKR : K ≤ R := hKPR ▸ inf_le_right
  have hKQz : K ≤ Qz := hK ▸ inf_le_left
  have hKQa : K ≤ Qa := hK ▸ inf_le_right
  have hzP : z ∈ P := hP ▸ mem_inf.mpr ⟨hzQ, mem_centralizer_singleton_iff.mpr hcomm⟩
  have haR : a ∈ R := hR ▸ mem_inf.mpr ⟨haQ, mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  have hazs : s * (a * z) * s⁻¹ = z := by
    rw [← hcomm]
    calc s * (z * a) * s⁻¹ = s * (s⁻¹ * z * s) * s⁻¹ := by rw [hszz]
      _ = z := by group
  have hzac : c * (z * a) * c⁻¹ = a := by
    rw [hcomm]
    calc c * (a * z) * c⁻¹ = c * (c⁻¹ * a * c) * c⁻¹ := by rw [hcaz]
      _ = a := by group
  have hCRc : ∀ r ∈ R, r * c = c * r → r ∈ K := by
    intro r hr hrc
    obtain ⟨hrQa, -⟩ := mem_inf.mp (hR ▸ hr)
    have h1 := conj_mem_twoCore_conj (h := c) (hQa ▸ hrQa)
    rw [show c⁻¹ * r * c = r by rw [mul_assoc, hrc, ← mul_assoc, inv_mul_cancel, one_mul],
      hcaz] at h1
    have h2 := conj_mem_twoCore_conj (h := s⁻¹) h1
    rw [show s⁻¹⁻¹ * r * s⁻¹ = r by rw [inv_inv, ← hsQc r hrQa, mul_inv_cancel_right],
      inv_inv, hazs] at h2
    exact hK ▸ mem_inf.mpr ⟨hQz ▸ h2, hrQa⟩
  have hCPs : ∀ p ∈ P, p * s = s * p → p ∈ K := by
    intro p hp hps
    obtain ⟨hpQz, -⟩ := mem_inf.mp (hP ▸ hp)
    have h1 := conj_mem_twoCore_conj (h := s) (hQz ▸ hpQz)
    rw [show s⁻¹ * p * s = p by rw [mul_assoc, hps, ← mul_assoc, inv_mul_cancel, one_mul],
      hszz] at h1
    have h2 := conj_mem_twoCore_conj (h := c⁻¹) h1
    rw [show c⁻¹⁻¹ * p * c⁻¹ = p by rw [inv_inv, ← hcQc p hpQz, mul_inv_cancel_right],
      inv_inv, hzac] at h2
    exact hK ▸ mem_inf.mpr ⟨hpQz, hQa ▸ h2⟩
  have hfix : ∀ {x g y : G} {Q : Subgroup G}, Q = inSubgroup (pCore 2) (centralizer {x}) →
      (center Q).map Q.subtype = zpowers g → orderOf g = 4 → g ^ 2 = x →
      y ∈ centralizer ({x} : Set G) → y⁻¹ * g * y = g ∨ y⁻¹ * g * y = g⁻¹ := by
    intro x g y Q hQ hgZ hg4 hg2 hy
    obtain ⟨hgQ, hgQc⟩ := hcen hgZ
    have hyQ : ∀ {v : G}, v ∈ Q → y * v * y⁻¹ ∈ Q := fun hv => hQ ▸ conj_mem_twoCore hy (hQ ▸ hv)
    have hyQ' : ∀ {v : G}, v ∈ Q → y⁻¹ * v * y ∈ Q := fun hv => by
      have := hQ ▸ conj_mem_twoCore (inv_mem hy) (hQ ▸ hv)
      rwa [inv_inv] at this
    have hmem : y⁻¹ * g * y ∈ (center Q).map Q.subtype := by
      refine ⟨⟨_, hyQ' hgQ⟩, mem_center_iff.mpr fun v => Subtype.ext ?_, rfl⟩
      have h1 := hgQc _ (hyQ v.2)
      change (v : G) * (y⁻¹ * g * y) = y⁻¹ * g * y * v
      calc (v : G) * (y⁻¹ * g * y) = y⁻¹ * ((y * v * y⁻¹) * g) * y := by group
        _ = y⁻¹ * (g * (y * v * y⁻¹)) * y := by rw [h1]
        _ = y⁻¹ * g * y * v := by group
    rw [hgZ] at hmem
    refine eq_or_eq_inv_of_mem_zpowers hg4 hmem ?_
    have hc' := conj_pow (i := 2) (a := y⁻¹) (b := g)
    rw [inv_inv] at hc'
    rw [hc', hg2, mul_assoc, ← mem_centralizer_singleton_iff.mp hy, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have hRc : ∀ r ∈ R, r⁻¹ * c * r = c ∨ r⁻¹ * c * r = c⁻¹ := fun r hr =>
    hfix hQz hcZ hc4 hc2 (mem_inf.mp (hR ▸ hr)).2
  have hPs : ∀ p ∈ P, p⁻¹ * s * p = s ∨ p⁻¹ * s * p = s⁻¹ := fun p hp =>
    hfix hQa hsZ hs4 hs2 (mem_inf.mp (hP ▸ hp)).2
  have hsplit : ∀ {X : Subgroup G} {g b : G}, (∀ r ∈ X, r * g = g * r → r ∈ K) →
      (∀ r ∈ X, r⁻¹ * g * r = g ∨ r⁻¹ * g * r = g⁻¹) → b ∈ X → b⁻¹ * g * b = g⁻¹ →
      K ≤ X → X = K ⊔ zpowers b := by
    intro X g b hCX hX hbX hbg hKX
    apply le_antisymm
    · intro r hr
      rcases hX r hr with h | h
      · refine mem_sup_left (hCX r hr ?_)
        calc r * g = r * (r⁻¹ * g * r) := by rw [h]
          _ = g * r := by group
      · have e : r⁻¹ * g⁻¹ * r = g := by
          rw [show r⁻¹ * g⁻¹ * r = (r⁻¹ * g * r)⁻¹ by group, h, inv_inv]
        have hk := hCX _ (mul_mem hbX hr) (by
          calc b * r * g = b * (r * (r⁻¹ * g⁻¹ * r)) := by rw [e, mul_assoc]
            _ = b * g⁻¹ * r := by group
            _ = b * (b⁻¹ * g * b) * r := by rw [hbg]
            _ = g * (b * r) := by group)
        rw [show r = b⁻¹ * (b * r) by group]
        exact mul_mem (mem_sup_right (inv_mem (mem_zpowers b))) (mem_sup_left hk)
    · exact sup_le hKX (zpowers_le.mpr hbX)
  have hRK : R = K ⊔ zpowers a := hsplit hCRc hRc haR hca hKR
  have hPK : P = K ⊔ zpowers z := hsplit hCPs hPs hzP hsz hKP
  have hKa : K ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxa⟩ := mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha hxa with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hKQz hxK) haQz
  have hKz : K ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxz⟩ := mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hxz with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hKQa hxK) hzQa
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPe.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPRc : P ≤ centralizer (R : Set G) := by
    rw [hPK]
    refine sup_le (fun k hk => mem_centralizer_iff.mpr fun y hy => hRcomm y hy k (hKR hk)) ?_
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hR ▸ hy)).2
  have hPRset : ((P ⊔ R : Subgroup G) : Set G) = (P : Set G) * R :=
    coe_mul_of_left_le_normalizer_right P R (hPRc.trans (centralizer_le_normalizer _))
  have hmemPR : ∀ {x : G}, x ∈ P ⊔ R → ∃ p ∈ P, ∃ r ∈ R, p * r = x := fun {x} hx => by
    have : x ∈ ((P ⊔ R : Subgroup G) : Set G) := hx
    rw [hPRset] at this
    exact Set.mem_mul.mp this
  have hsq : ∀ {X : Subgroup G}, CFSG.IsElementaryAbelian 2 X → ∀ x ∈ X, x ^ 2 = 1 :=
    fun {X} hX x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (A := X) x hx
  have hEe : CFSG.IsElementaryAbelian 2 (P ⊔ R : Subgroup G) := by
    have hcommE : ∀ x ∈ P ⊔ R, ∀ y ∈ P ⊔ R, x * y = y * x := by
      intro x hx y hy
      obtain ⟨p, hp, r, hr, rfl⟩ := hmemPR hx
      obtain ⟨p', hp', r', hr', rfl⟩ := hmemPR hy
      have h1 := mem_centralizer_iff.mp (hPRc hp) r' hr'
      have h2 := mem_centralizer_iff.mp (hPRc hp') r hr
      calc p * r * (p' * r') = p * (r * p') * r' := by group
        _ = p * (p' * r) * r' := by rw [← h2]
        _ = (p * p') * (r * r') := by group
        _ = (p' * p) * (r' * r) := by rw [hPcomm p hp p' hp', hRcomm r hr r' hr']
        _ = p' * (p * r') * r := by group
        _ = p' * (r' * p) * r := by rw [h1]
        _ = p' * r' * (p * r) := by group
    refine { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hcommE x x.2 y y.2)⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_ }
    obtain ⟨p, hp, r, hr, hx⟩ := hmemPR x.2
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← hx,
      Commute.mul_pow (mem_centralizer_iff.mp (hPRc hp) r hr).symm, hsq hPe p hp,
      hsq hRe r hr, one_mul]
  have hUza : U = zpowers z ⊔ zpowers a := by
    rw [hU, Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hEPa : P ⊔ R = P ⊔ zpowers a := by
    rw [hRK, ← sup_assoc, sup_eq_left.mpr hKP]
  have hERz : P ⊔ R = R ⊔ zpowers z := by
    rw [hPK, sup_comm K (zpowers z), sup_assoc, sup_eq_right.mpr hKR, sup_comm]
  have hEKU : P ⊔ R = K ⊔ U := by
    rw [hEPa, hPK, hUza, sup_assoc]
  have hKU : K ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxU⟩ := mem_inf.mp hx
    rw [hU, mem_four_iff hzz haa hcomm] at hxU
    rcases hxU with h | h | h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hKQa hxK) hzQa
    · exact absurd (h ▸ hKQz hxK) haQz
    · exfalso
      apply haQz
      have : z * a ∈ Qz := h ▸ hKQz hxK
      simpa using mul_mem (inv_mem hzQ) this
  have hCN : C ≤ N := by
    rw [hC, hN]; exact centralizer_le_normalizer _
  have hMN : C ⊔ zpowers c ⊔ zpowers s ≤ N :=
    sup_le (sup_le hCN (zpowers_le.mpr hcN)) (zpowers_le.mpr hsN)
  have hNgen : N ≤ C ⊔ zpowers c ⊔ zpowers s := by
    have hle1 : N ⊓ centralizer ({z} : Set G) ≤ C ⊔ zpowers c ⊔ zpowers s := hNz ▸ le_sup_left
    have h3 := relIndex_mul_relIndex _ _ _ hle1 hMN
    rw [hidx] at h3
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ h3) with h | h
    · exact relIndex_eq_one.mp h
    · exfalso
      rw [h] at h3
      have hle2 := relIndex_eq_one.mp (by omega :
        (N ⊓ centralizer ({z} : Set G)).relIndex (C ⊔ zpowers c ⊔ zpowers s) = 1)
      have hs' := (mem_inf.mp (hle2 (mem_sup_right (mem_zpowers s)))).2
      have : s⁻¹ * z * s = z := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hs', ← mul_assoc, inv_mul_cancel,
          one_mul]
      rw [hszz] at this
      exact ha1 (by simpa using congrArg (z⁻¹ * ·) this)
  have hcentK : ∀ k ∈ K, k * c = c * k ∧ k * s = s * k := fun k hk =>
    ⟨hcQc k (hKQz hk), hsQc k (hKQa hk)⟩
  have hNK : N ≤ normalizer (K : Set G) := by
    refine hNgen.trans (sup_le (sup_le ?_ ?_) ?_)
    · intro g hg
      have hgz : g ∈ centralizer ({z} : Set G) := by
        rw [hC] at hg
        exact centralizer_le (Set.singleton_subset_iff.mpr (hU ▸ subset_closure (by simp))) hg
      have hga : g ∈ centralizer ({a} : Set G) := by
        rw [hC] at hg
        exact centralizer_le (Set.singleton_subset_iff.mpr (hU ▸ subset_closure (by simp))) hg
      have hK1 : ∀ {g : G}, g ∈ centralizer ({z} : Set G) → g ∈ centralizer ({a} : Set G) →
          ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
        intro g hgz hga x hx
        rw [hK, hQz, hQa] at hx ⊢
        obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
        exact mem_inf.mpr ⟨conj_mem_twoCore hgz hx1, conj_mem_twoCore hga hx2⟩
      refine mem_normalizer_of_conj_mem (hK1 hgz hga) fun x hx => ?_
      have := hK1 (inv_mem hgz) (inv_mem hga) x hx
      rwa [inv_inv] at this
    · rw [zpowers_le]
      refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
      · rw [← (hcentK x hx).1, mul_inv_cancel_right]; exact hx
      · rw [mul_assoc, (hcentK x hx).1, ← mul_assoc, inv_mul_cancel, one_mul]; exact hx
    · rw [zpowers_le]
      refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
      · rw [← (hcentK x hx).2, mul_inv_cancel_right]; exact hx
      · rw [mul_assoc, (hcentK x hx).2, ← mul_assoc, inv_mul_cancel, one_mul]; exact hx
  have hNE : N ≤ normalizer ((P ⊔ R : Subgroup G) : Set G) := by
    intro n hn
    rw [hEKU]
    have hcon : ∀ {g : G}, g ∈ N → ∀ x ∈ K ⊔ U, g * x * g⁻¹ ∈ K ⊔ U := by
      intro g hg x hx
      have hmap : (K ⊔ U).map (MulAut.conj g).toMonoidHom ≤ K ⊔ U := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨k, hk, rfl⟩
          exact (mem_normalizer_iff.mp (hNK hg) k).mp hk
        · rintro _ ⟨u, hu, rfl⟩
          exact (mem_normalizer_iff.mp (hN ▸ hg) u).mp hu
      exact hmap ⟨x, hx, rfl⟩
    refine mem_normalizer_of_conj_mem (hcon hn) fun x hx => ?_
    have := hcon (inv_mem hn) x hx
    rwa [inv_inv] at this
  have hsurj : Function.Surjective (U.normalizerMonoidHom) := by
    subst hN hC
    rw [← MonoidHom.range_eq_top]
    apply eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      normalizerMonoidHom_ker, ← Nat.card_congr hiso.toEquiv]
  exact ⟨haQz, hzQa, hKPR, ⟨hPK, hKz⟩, ⟨hRK, hKa⟩,
    ⟨hPRset.symm, hEPa, hERz, hEKU, hKU, hEe⟩, hNK, hNE, ⟨hsurj, hS3⟩, hcentK,
    ⟨hcz, hcaz, hcaz2⟩, ⟨hsa, hszz, hsza⟩,
    fun h => ha1 (by simpa using congrArg (z⁻¹ * ·) h)⟩

end CFSG.LocalAnalysis.GorensteinLyons

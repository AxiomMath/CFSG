module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSeven
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint

section Generic

variable {X : Type*} [Group X]

theorem exists_conj_of_odd_orderOf {x y : X} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x⁻¹ * y))) : ∃ m : X, m * x * m⁻¹ = y := by
  set u := x⁻¹ * y with hu
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxu : x * u * x⁻¹ = u⁻¹ := by
    calc x * u * x⁻¹ = y * x⁻¹ := by rw [hu]; group
      _ = y⁻¹ * x := by rw [hxinv, hyinv]
      _ = u⁻¹ := by rw [hu, _root_.mul_inv_rev, inv_inv]
  obtain ⟨j, hj⟩ := hodd
  have h1 : x * u ^ j * x⁻¹ = (u ^ j)⁻¹ := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxu, inv_pow]
  have h2 : u ^ (2 * j) = u⁻¹ := by
    have h3 : u ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one u
    rw [pow_succ] at h3
    exact eq_inv_of_mul_eq_one_left h3
  refine ⟨u ^ j, ?_⟩
  calc u ^ j * x * (u ^ j)⁻¹ = u ^ j * (x * u ^ j * x⁻¹)⁻¹ * x := by group
    _ = u ^ j * u ^ j * x := by rw [h1, inv_inv]
    _ = u ^ (2 * j) * x := by rw [← pow_add, two_mul]
    _ = y := by rw [h2, hu, _root_.mul_inv_rev, inv_inv, mul_assoc, hx, mul_one, hyinv]

theorem exists_conj_of_inv_mul_mem [Finite X] {R : Subgroup X} (hR : Odd (Nat.card R)) {x y : X}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : x⁻¹ * y ∈ R) : ∃ m : X, m * x * m⁻¹ = y :=
  exists_conj_of_odd_orderOf hx hy (hR.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hxy))

theorem le_centralizer_of_conj_mul [Finite X] {R : Subgroup X} [hRn : R.Normal]
    (hR : Odd (Nat.card R)) {a z m : X} (ha : a * a = 1) (hz : z * z = 1)
    (haz : a * z = z * a) (ha1 : a ≠ 1) (hz1 : z ≠ 1) (hne : a ≠ z)
    (hC : R ⊓ centralizer ({a} : Set X) ≤ centralizer ({z} : Set X))
    (hm : m * a * m⁻¹ = a * z) : R ≤ centralizer ({z} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq, ha]) ha1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hz]) hz1
  set B : Subgroup X := zpowers a ⊔ zpowers z with hB
  have hcomm : ∀ v ∈ zpowers a, ∀ r ∈ zpowers z, v * r = r * v := by
    intro v hv r hr
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
    exact ((Commute.zpow_zpow (show Commute a z from haz) i k)).eq
  have hmemB : ∀ b ∈ B, b = 1 ∨ b = a ∨ b = z ∨ b = a * z := by
    intro b hb
    obtain ⟨v, hv, r, hr, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute hcomm hb
    obtain h1 | h1 := SteinbergBV.OneOrTwoLayer.eq_one_or_eq_of_mem_zpowers ha2 hv <;>
      obtain h2 | h2 := SteinbergBV.OneOrTwoLayer.eq_one_or_eq_of_mem_zpowers hz2 hr <;>
      rw [h1, h2]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inr (Or.inl (one_mul z)))
    · exact Or.inr (Or.inl (mul_one a))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hsq : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rcases hmemB b hb with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hz
    · calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [haz]
        _ = 1 := by rw [← mul_assoc, ha, one_mul, hz]
  have hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := by
    intro b hb c hc
    obtain ⟨v, hv, r, hr, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute hcomm hb
    obtain ⟨v', hv', r', hr', rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute hcomm hc
    have h1 : v * v' = v' * v := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv'
      exact (Commute.zpow_zpow_self a i k).eq
    have h2 : r * r' = r' * r := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hr
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr'
      exact (Commute.zpow_zpow_self z i k).eq
    have h3 := hcomm v hv r' hr'
    have h4 := hcomm v' hv' r hr
    calc v * r * (v' * r') = (v * v') * (r * r') := by rw [mul_assoc, ← mul_assoc r, ← h4]; group
      _ = (v' * v) * (r' * r) := by rw [h1, h2]
      _ = v' * r' * (v * r) := by rw [mul_assoc, ← mul_assoc v, h3]; group
  have hBel : IsElemAbelian 2 B :=
    ⟨⟨⟨fun b c => Subtype.ext (hBcomm _ b.2 _ c.2)⟩⟩, fun b hb => by rw [sq]; exact hsq b hb⟩
  have hB2 : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, sq]; exact hsq b b.2)⟩
  have hBcard : 2 ^ 2 ≤ Nat.card B := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB2
    rcases k with _ | _ | k
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact ha1 (by
        have : a ∈ B := mem_sup_left (mem_zpowers a)
        rwa [hk, mem_bot] at this)
    · exfalso
      have heq : zpowers a = B := eq_of_le_of_card_ge le_sup_left (by
        rw [hk, Nat.card_zpowers, ha2, pow_one])
      have hzB : z ∈ zpowers a := heq ▸ mem_sup_right (mem_zpowers z)
      rcases SteinbergBV.OneOrTwoLayer.eq_one_or_eq_of_mem_zpowers ha2 hzB with h | h
      · exact hz1 h
      · exact hne h.symm
    · rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBN : B ≤ normalizer (R : Set X) := by
    rw [normalizer_eq_top_iff.mpr hRn]
    exact le_top
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hBel
    hBcard hBN (Nat.coprime_two_left.mpr hR)
  have hCaz : R ⊓ centralizer ({a * z} : Set X) ≤ centralizer ({z} : Set X) := by
    have hle : R ⊓ centralizer ({a} : Set X) ≤ R ⊓ centralizer ({a * z} : Set X) := by
      intro x hx
      refine ⟨hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := mem_centralizer_singleton_iff.mp hx.2
      have h2 := mem_centralizer_singleton_iff.mp (hC hx)
      calc x * (a * z) = (x * a) * z := by group
        _ = a * (x * z) := by rw [h1, mul_assoc]
        _ = a * z * x := by rw [h2, mul_assoc]
    have hmap : R ⊓ centralizer ({a * z} : Set X) =
        (R ⊓ centralizer ({a} : Set X)).map (MulAut.conj m).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨hxR, hxC⟩
        refine ⟨m⁻¹ * x * m, ⟨by simpa using hRn.conj_mem x hxR m⁻¹,
          mem_centralizer_singleton_iff.mpr ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
        have h1 := mem_centralizer_singleton_iff.mp hxC
        rw [← hm] at h1
        calc m⁻¹ * x * m * a = m⁻¹ * (x * (m * a * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * a * m⁻¹) * x) * m := by rw [h1]
          _ = a * (m⁻¹ * x * m) := by group
      · rintro ⟨y, ⟨hyR, hyC⟩, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        refine ⟨hRn.conj_mem y hyR m, mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 := mem_centralizer_singleton_iff.mp hyC
        rw [← hm]
        calc m * y * m⁻¹ * (m * a * m⁻¹) = m * (y * a) * m⁻¹ := by group
          _ = m * (a * y) * m⁻¹ := by rw [h1]
          _ = m * a * m⁻¹ * (m * y * m⁻¹) := by group
    have hcard : Nat.card ↥(R ⊓ centralizer ({a * z} : Set X)) ≤
        Nat.card ↥(R ⊓ centralizer ({a} : Set X)) := by
      rw [hmap, card_map_of_injective (MulAut.conj m).injective]
    have heq := eq_of_le_of_card_ge hle hcard
    rw [← heq]
    exact hC
  rw [← hgen]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  rcases hmemB b hb with rfl | rfl | rfl | rfl
  · exact absurd rfl hb1
  · exact hC
  · exact inf_le_right
  · exact hCaz

theorem le_centralizer_of_isSimpleGroup {L R : Subgroup X} [IsSimpleGroup L]
    (hLR : L ≤ normalizer (R : Set X)) {z : X} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzR : R ≤ centralizer ({z} : Set X)) : L ≤ centralizer (R : Set X) := by
  set M : Subgroup L := (centralizer (R : Set X)).subgroupOf L with hM
  have hMn : M.Normal := ⟨fun c hc l => by
    rw [hM, mem_subgroupOf] at hc ⊢
    rw [mem_centralizer_iff] at hc ⊢
    intro r hr
    have hr' : (l : X)⁻¹ * r * l ∈ R := by
      have := (mem_normalizer_iff.mp (hLR (inv_mem l.2)) r).mp hr
      simpa using this
    have h1 := hc _ hr'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc r * ((l : X) * c * (l : X)⁻¹) = l * (((l : X)⁻¹ * r * l) * c) * (l : X)⁻¹ := by group
      _ = l * (c * ((l : X)⁻¹ * r * l)) * (l : X)⁻¹ := by rw [h1]
      _ = (l : X) * c * (l : X)⁻¹ * r := by group⟩
  have hzM : (⟨z, hzL⟩ : L) ∈ M := by
    rw [hM, mem_subgroupOf, mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hzR hr)
  have := hMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exfalso
    rw [h, mem_bot] at hzM
    exact hz1 (congrArg Subtype.val hzM)
  · intro l hl
    have : (⟨l, hl⟩ : L) ∈ M := h ▸ mem_top _
    exact this

theorem exists_conj_of_coordinateG [Finite X] {D : Subgroup X} [hDn : D.Normal]
    (hfaith : ∀ h : X, (∀ x ∈ D, h⁻¹ * x * h = x) → h = 1)
    {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (e : D ≃* ComponentClassification.CatalogueSchreierLinearTwo.coordinateG K) {t z : X}
    (ht : orderOf t = 2) (htz : orderOf (t * z) = 2) (hzD : z ∈ D) :
    ∃ g : X, g * t * g⁻¹ = t * z := by
  open ComponentClassification.CatalogueSchreierLinearTwo in
  obtain ⟨c, hc1, hc2, -⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.linear_two_automorphism_semilinear_isomorphism K
  let δ : X →* MulAut (coordinateG K) :=
    { toFun := fun n => e.symm.trans ((MulAut.conjNormal n).trans e)
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hδ : ∀ (n : X) (g : coordinateG K), ((δ n g : coordinateG K) : Equiv.Perm (Omega K)) =
      (e (MulAut.conjNormal n (e.symm g)) : Equiv.Perm (Omega K)) := fun n g => rfl
  let a : X →* coordinateE K := c.symm.toMonoidHom.comp δ
  have ha_inj : Function.Injective a := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : δ n = 1 := by
      have := congrArg c hn
      simpa [a] using this
    refine inv_eq_one.mp (hfaith n⁻¹ fun x hx => ?_)
    have h2 := congrArg (fun φ : MulAut (coordinateG K) => φ (e ⟨x, hx⟩)) h1
    simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (e.injective h2)
    simp only [MulAut.conjNormal_apply] at h3
    simpa using h3
  have ha_D : ∀ (d : X) (hd : d ∈ D), ((a d : coordinateE K) : Equiv.Perm (Omega K)) =
      (e ⟨d, hd⟩ : Equiv.Perm (Omega K)) := by
    intro d hd
    have hGE : ((e ⟨d, hd⟩ : coordinateG K) : Equiv.Perm (Omega K)) ∈ coordinateE K :=
      (coordinateG_le_D K).trans (coordinateD_le_E K) (e ⟨d, hd⟩).2
    have h1 : δ d = MulAut.conj (e ⟨d, hd⟩) := by
      ext g
      rw [hδ, MulAut.conj_apply]
      have h2 : MulAut.conjNormal d (e.symm g) = ⟨d, hd⟩ * e.symm g * (⟨d, hd⟩ : D)⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 : a d = ⟨_, hGE⟩ := by
      apply c.injective
      change c (c.symm (δ d)) = _
      rw [MulEquiv.apply_symm_apply, h1, hc2]
    rw [h3]
  have hnf := (LocalAnalysis.ComponentInitial.UnitaryHigher.even_linear_two_involution_normal_forms
    hm hK).2.2.2.2.2.2.2.2.2
  have hot : orderOf ((a t : coordinateE K) : Equiv.Perm (Omega K)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_injective a ha_inj, ht]
  have hotz : orderOf ((a (t * z) : coordinateE K) : Equiv.Perm (Omega K)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_injective a ha_inj, htz]
  have hz' : ((a z : coordinateE K) : Equiv.Perm (Omega K)) ∈ coordinateG K := by
    rw [ha_D z hzD]
    exact (e ⟨z, hzD⟩).2
  have hmul : ((a (t * z) : coordinateE K) : Equiv.Perm (Omega K)) =
      (a t : Equiv.Perm (Omega K)) * (a z : Equiv.Perm (Omega K)) := by
    rw [map_mul, Subgroup.coe_mul]
  have hiff : ((a t : coordinateE K) : Equiv.Perm (Omega K)) ∈ coordinateG K ↔
      ((a (t * z) : coordinateE K) : Equiv.Perm (Omega K)) ∈ coordinateG K := by
    rw [hmul]
    exact ⟨fun h => mul_mem h hz', fun h => by
      have := mul_mem h (inv_mem hz')
      rwa [mul_inv_cancel_right] at this⟩
  obtain ⟨g, hgG, hg⟩ : ∃ g ∈ coordinateG K, ((a (t * z) : coordinateE K) :
      Equiv.Perm (Omega K)) = g * (a t : Equiv.Perm (Omega K)) * g⁻¹ := by
    rcases hnf _ (a t).2 hot with ⟨h1, h, hh, hh'⟩ | ⟨h1, -, σ, hσ1, hσ2, -, hσu, -, ⟨h, hh, hh'⟩,
      -⟩
    · rcases hnf _ (a (t * z)).2 hotz with ⟨-, h', hh2, hh2'⟩ | ⟨h2, -⟩
      · refine ⟨h' * h⁻¹, mul_mem hh2 (inv_mem hh), ?_⟩
        rw [hh2', hh']
        group
      · exact absurd (hiff.mp h1) h2
    · rcases hnf _ (a (t * z)).2 hotz with ⟨h2, -⟩ | ⟨-, -, σ', hσ1', hσ2', -, -, -, ⟨h', hh2,
        hh2'⟩, -⟩
      · exact absurd (hiff.mpr h2) h1
      · obtain rfl := hσu σ' hσ1' hσ2'
        refine ⟨h' * h⁻¹, mul_mem hh2 (inv_mem hh), ?_⟩
        rw [hh2', hh']
        group
  refine ⟨(e.symm ⟨g, hgG⟩ : X), ha_inj (Subtype.ext ?_)⟩
  have hd := ha_D _ (e.symm ⟨g, hgG⟩).2
  rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hd,
    show (⟨((e.symm ⟨g, hgG⟩ : D) : X), (e.symm ⟨g, hgG⟩).2⟩ : D) = e.symm ⟨g, hgG⟩ from rfl,
    MulEquiv.apply_symm_apply, hg]

end Generic

namespace WData

open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LocalAnalysis.EvenBN.GMSK

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {q : ℕ}

theorem Lbar_inf_oddCore {K : Type} [Field K] (w : WData d Vi q) (D : LeviData A Vi K)
    [IsSimpleGroup (w.Lbar D.lev.range)]
    (hE : ∃ E : Subgroup w.Nbar, E ≤ w.Lbar D.lev.range ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 4) {x : w.Nbar} (hxL : x ∈ w.Lbar D.lev.range)
    (hxO : x ∈ standardComponentOddCore w.Nbar) : x = 1 := by
  set L := w.Lbar D.lev.range
  set R := standardComponentOddCore w.Nbar
  have hRn : (R.subgroupOf L).Normal := (inferInstance : R.Normal).subgroupOf L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf L) with h | h
  · have : (⟨x, hxL⟩ : L) ∈ R.subgroupOf L := hxO
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    obtain ⟨E, hEL, -, hE4⟩ := hE
    have hER : E ≤ R := fun y hy => by
      have : (⟨y, hEL hy⟩ : L) ∈ R.subgroupOf L := h ▸ mem_top _
      exact this
    have h4 := Subgroup.card_dvd_of_le hER
    rw [hE4] at h4
    exact (Nat.not_even_iff_odd.mpr (odd_card_standardComponentOddCore _))
      (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4))

theorem oddCore_inf_centralizer_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 3 ≤ Nat.card K) (w : WData d Vi q) (D : LeviData A Vi K)
    [IsSimpleGroup (w.Lbar D.lev.range)]
    (hE : ∃ E : Subgroup w.Nbar, E ≤ w.Lbar D.lev.range ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 4) :
    standardComponentOddCore w.Nbar ⊓ centralizer ({w.tbar} : Set w.Nbar) ≤
      centralizer (w.Lbar D.lev.range : Set w.Nbar) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro l hl
  obtain ⟨hxO, hxt⟩ := Subgroup.mem_inf.mp hx
  have hlt : l ∈ centralizer ({w.tbar} : Set w.Nbar) := w.Lbar_le_centralizer D hl
  have h1 : x * l * x⁻¹ ∈ w.Lbar D.lev.range := by
    have := (w.Lbar_normal hK D).conj_mem ⟨l, hlt⟩ (mem_subgroupOf.mpr hl) ⟨x, hxt⟩
    have h4 := mem_subgroupOf.mp this
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h4
  have h2 : l * x⁻¹ * l⁻¹ ∈ standardComponentOddCore w.Nbar :=
    (inferInstance : (standardComponentOddCore w.Nbar).Normal).conj_mem _ (inv_mem hxO) l
  have h3 : x * l * x⁻¹ * l⁻¹ = 1 := by
    refine w.Lbar_inf_oddCore D hE (mul_mem h1 (inv_mem hl)) ?_
    rw [show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
    exact mul_mem hxO h2
  calc l * x = (x * l * x⁻¹ * l⁻¹)⁻¹ * (x * l) := by group
    _ = x * l := by rw [h3, inv_one, one_mul]

abbrev Ebar (w : WData d Vi q) (L : Subgroup G) : Subgroup w.Nbar :=
  normalClosure (w.Lbar L : Set w.Nbar)

omit [Finite G] in
theorem CaseB.exists_conj {w : WData d Vi q} {L : Subgroup G} (hB : w.CaseB L) {z : w.Ntil}
    (hzL : z ∈ w.Ltil L) (hz : z * z = 1) : ∃ m : w.Ntil, m * w.ttil * m⁻¹ = w.ttil * z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hJ, ψ, hψ₁, hψ₂⟩ := hB.factors
  have hzE : z ∈ CFSG.layer w.Ntil := (Subgroup.mem_inf.mp (hJ ▸ hzL)).1
  have : (CFSG.layer w.Ntil).Characteristic := CFSG.LocalCores.layer_characteristic
  set m : CFSG.layer w.Ntil := ψ.symm (⟨z, hzL⟩, 1) with hm
  have hmt : w.ttil⁻¹ * (m : w.Ntil) * w.ttil ∈ CFSG.layer w.Ntil := by
    have := (inferInstance : (CFSG.layer w.Ntil).Normal).conj_mem _ m.2 w.ttil⁻¹
    simpa using this
  have h1 := hψ₂ (m : w.Ntil) m.2 hmt
  have h2 := hψ₁ z hzL hzE
  have hψm : ψ ⟨(m : w.Ntil), m.2⟩ = (⟨z, hzL⟩, 1) := by
    rw [Subtype.coe_eta, hm, MulEquiv.apply_symm_apply]
  have hzinv : (⟨z, hzL⟩ : w.Ltil L)⁻¹ = ⟨z, hzL⟩ :=
    Subtype.ext (inv_eq_of_mul_eq_one_right hz)
  have key : (⟨w.ttil⁻¹ * (m : w.Ntil) * w.ttil, hmt⟩ : CFSG.layer w.Ntil) * m⁻¹ = ⟨z, hzE⟩ := by
    apply ψ.injective
    rw [map_mul, map_inv, h1, h2, ← Subtype.coe_eta m m.2, hψm]
    ext <;> simp [hzinv]
  refine ⟨m, ?_⟩
  have key' := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key'
  calc (m : w.Ntil) * w.ttil * (m : w.Ntil)⁻¹ =
      w.ttil * (w.ttil⁻¹ * (m : w.Ntil) * w.ttil * (m : w.Ntil)⁻¹) := by group
    _ = w.ttil * z := by rw [key']

theorem CaseA.exists_conj {f : ℕ} (hf : 1 ≤ f) {w : WData d Vi (2 ^ f)} {L : Subgroup G}
    (hA : w.CaseA f L) {z : w.Ntil} (hzL : z ∈ w.Ltil L) (htz : orderOf (w.ttil * z) = 2) :
    ∃ m : w.Ntil, m * w.ttil * m⁻¹ = w.ttil * z := by
  obtain ⟨-, -, hJE, hDE, -, -, hfaith⟩ := hA.layer
  have : (CFSG.layer w.Ntil).Characteristic := CFSG.LocalCores.layer_characteristic
  have hmodel := hA.model
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.layer w.Ntil) .PSL 2 2 (2 * f) := by
    rcases hmodel with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  let e₀ : CFSG.layer w.Ntil ≃* ComponentClassification.CatalogueSchreierLinearTwo.coordinateG K' :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K').symm.trans
      (ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG K'))
  refine exists_conj_of_coordinateG (fun h hh => hfaith h (hDE ▸ hh)) (by omega) hK' e₀
    w.orderOf_ttil htz (hJE hzL)

end WData

namespace Hyp

open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LocalAnalysis.EvenBN.GMSK

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem commutator_oddCore_Ebar (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    (hGMS : GMSLinearStandardLayerListKRankOneStatement) (hL3 : LinearThreeExclusion27)
    (hG23 : G2ThreeExclusion27) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K]
    (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f) :
    ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ := by
  have hf := h.three_le
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hsimp, hnab, hE, -, -, -, -⟩ :=
    w.lbar_data h.three_le hR hW (h.normalizer_adj_le d hR hW) hKc D
  set R := standardComponentOddCore w.Nbar with hRdef
  set Lb := w.Lbar D.lev.range with hLb
  have hRodd : Odd (Nat.card R) := odd_card_standardComponentOddCore _
  have hRsq : ∀ x ∈ R, x * x = 1 → x = 1 := by
    intro x hx hx2
    have h1 : orderOf x ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hx
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx2])
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · rw [h3] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hRodd)
  obtain ⟨E, hEL, hEel, hE4⟩ := hE
  obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [this, Subgroup.card_bot] at hE4
    omega
  have hz2 : z * z = 1 := by rw [← sq]; exact hEel.2 z hzE
  have hzL : z ∈ Lb := hEL hzE
  have hzt : w.tbar * z = z * w.tbar :=
    (mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D hzL)).symm
  have ht2 : w.tbar * w.tbar = 1 := by
    have := pow_orderOf_eq_one w.tbar
    rwa [w.orderOf_tbar, sq] at this
  have ht1 : w.tbar ≠ 1 := by
    intro h1
    have := w.orderOf_tbar
    rw [h1, orderOf_one] at this
    omega
  have htz : w.tbar ≠ z := by
    intro heq
    have hcen : (⟨z, hzL⟩ : Lb) ∈ center Lb := mem_center_iff.mpr fun y => Subtype.ext (by
      have hy := mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D y.2)
      rw [heq] at hy
      exact hy)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Lb) with h1 | h1
    · rw [h1, mem_bot] at hcen
      exact hz1 (congrArg Subtype.val hcen)
    · obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (mem_center_iff.mp (h1 ▸ mem_top y) x)
  have htz2 : orderOf (w.ttil * w.projTil z) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => htz ?_
    · rw [← map_mul, ← map_pow, sq, show w.tbar * z * (w.tbar * z) = (w.tbar * w.tbar) * (z * z) by
        rw [mul_assoc, ← mul_assoc z, ← hzt]; group, ht2, hz2, one_mul, map_one]
    · rw [← map_mul] at h1
      have h2 : w.tbar * z ∈ R := (QuotientGroup.eq_one_iff _).mp h1
      have h3 := hRsq _ h2 (by rw [show w.tbar * z * (w.tbar * z) = (w.tbar * w.tbar) * (z * z) by
        rw [mul_assoc, ← mul_assoc z, ← hzt]; group, ht2, hz2, one_mul])
      calc w.tbar = w.tbar * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h3, one_mul]
  obtain ⟨mt, hmt⟩ : ∃ m : w.Ntil, m * w.ttil * m⁻¹ = w.ttil * w.projTil z := by
    rcases h.seitz27 hG hGMS hL3 hG23 hK d hR hW w D hKc with hA | hB
    · exact hA.exists_conj (by omega) ⟨z, hzL, rfl⟩ htz2
    · exact hB.exists_conj ⟨z, hzL, rfl⟩ (by rw [← map_mul, hz2, map_one])
  obtain ⟨mb, rfl⟩ := QuotientGroup.mk'_surjective _ mt
  have hxy : (w.tbar * z)⁻¹ * (mb * w.tbar * mb⁻¹) ∈ R := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change w.projTil ((w.tbar * z)⁻¹ * (mb * w.tbar * mb⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_inv]
    change (w.ttil * w.projTil z)⁻¹ * (w.projTil mb * w.ttil * (w.projTil mb)⁻¹) = 1
    rw [show w.projTil mb = (QuotientGroup.mk' (standardComponentOddCore w.Nbar)) mb from rfl, hmt,
      inv_mul_cancel]
  have hx2 : w.tbar * z * (w.tbar * z) = 1 := by
    rw [show w.tbar * z * (w.tbar * z) = (w.tbar * w.tbar) * (z * z) by
      rw [mul_assoc, ← mul_assoc z, ← hzt]; group, ht2, hz2, one_mul]
  have hy2 : mb * w.tbar * mb⁻¹ * (mb * w.tbar * mb⁻¹) = 1 := by
    rw [show mb * w.tbar * mb⁻¹ * (mb * w.tbar * mb⁻¹) = mb * (w.tbar * w.tbar) * mb⁻¹ by group,
      ht2, mul_one, mul_inv_cancel]
  obtain ⟨m', hm'⟩ := exists_conj_of_inv_mul_mem hRodd hx2 hy2 hxy
  have hm : (m'⁻¹ * mb) * w.tbar * (m'⁻¹ * mb)⁻¹ = w.tbar * z := by
    calc (m'⁻¹ * mb) * w.tbar * (m'⁻¹ * mb)⁻¹ = m'⁻¹ * (mb * w.tbar * mb⁻¹) * m' := by group
      _ = m'⁻¹ * (m' * (w.tbar * z) * m'⁻¹) * m' := by rw [hm']
      _ = w.tbar * z := by group
  have hC : R ⊓ centralizer ({w.tbar} : Set w.Nbar) ≤ centralizer ({z} : Set w.Nbar) := by
    intro x hx
    have := w.oddCore_inf_centralizer_le hK3 D ⟨E, hEL, hEel, hE4⟩ hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp this z hzL).symm
  have hRz := le_centralizer_of_conj_mul hRodd ht2 hz2 hzt ht1 hz1 htz hC hm
  have hLR : Lb ≤ centralizer (R : Set w.Nbar) :=
    le_centralizer_of_isSimpleGroup (by rw [normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      hzL hz1 hRz
  have hER : w.Ebar D.lev.range ≤ centralizer (R : Set w.Nbar) := normalClosure_le_normal hLR
  rw [commutator_eq_bot_iff_le_centralizer]
  exact le_centralizer_iff.mp hER

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree

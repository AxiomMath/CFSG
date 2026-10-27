module

public import CFSG.Foundations.Basic
import CFSG.Walter.Bender1970
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.PrimeSetCore
import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement
import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Local
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Subgroup

section TypeZero

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_mem_inf_inv_mul_mem_centralizer_of_isComponent (hO : pPrimeCore 2 Y = ⊥)
    (R : Sylow 2 Y) (hab : IsMulCommutative (R : Subgroup Y)) {K : Subgroup Y}
    (hK : IsComponent K) {u : Y} (hu : u ∈ (R : Subgroup Y)) :
    ∃ k ∈ K, k ∈ (R : Subgroup Y) ∧ k⁻¹ * u ∈ centralizer (K : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Walter.HasAbelianSylowTwo Y := Walter.hasAbelianSylowTwo_of_sylow R hab
  have hK' := (Walter.isComponent_iff_isComponentOf_top K).mp hK
  have : IsSimpleGroup K := Walter.isSimpleGroup_of_isComponentOf hO hY hK'
  have hnonab := Walter.nonabelian_of_isComponentOf hK'
  have hLC : ∀ x ∈ K, x ∈ centralizer (K : Set Y) → x = 1 := by
    intro x hxK hxC
    have hmem : (⟨x, hxK⟩ : K) ∈ center K := mem_center_iff.mpr fun y =>
      Subtype.ext ((mem_centralizer_iff.mp hxC) y y.2)
    rw [Walter.center_eq_bot_of_isSimpleGroup hnonab, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (Walter.isSubnormal_of_isComponentOf hK')
  have hPmem : ∀ x : K, x ∈ (P : Subgroup K) ↔ (x : Y) ∈ (R : Subgroup Y) := by
    intro x
    constructor
    · intro hx
      have hx' : (x : Y) ∈ (P : Subgroup K).map K.subtype := ⟨x, hx, rfl⟩
      rw [hP] at hx'
      exact hx'.1
    · intro hx
      have hx' : (x : Y) ∈ (R : Subgroup Y) ⊓ K := ⟨hx, x.2⟩
      rw [← hP] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [← Subtype.ext hyx]
  obtain ⟨k, hkK, hk⟩ := Walter.exists_inner_of_sylow_le_normalizer hY K hnonab R
    (Walter.sylow_le_normalizer_of_isComponentOf hO hY R hK') u hu
  have hcC : k⁻¹ * u ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro x hx
    calc x * (k⁻¹ * u) = k⁻¹ * (k * x * k⁻¹) * u := by group
      _ = k⁻¹ * (u * x * u⁻¹) * u := by rw [hk x hx]
      _ = k⁻¹ * u * x := by group
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp R.isPGroup') ⟨u, hu⟩
  have hupow : u ^ (2 ^ a) = 1 := by
    have h := pow_orderOf_eq_one (⟨u, hu⟩ : (R : Subgroup Y))
    rw [ha] at h
    exact congrArg Subtype.val h
  have hkpow : k ^ (2 ^ a) = 1 := by
    have hkc : Commute k (k⁻¹ * u) := mem_centralizer_iff.mp hcC k hkK
    have h1 := hkc.mul_pow (2 ^ a)
    rw [mul_inv_cancel_left, hupow] at h1
    apply hLC _ (K.pow_mem hkK _)
    rw [eq_inv_of_mul_eq_one_left h1.symm]
    exact inv_mem (pow_mem hcC _)
  have hkN : (⟨k, hkK⟩ : K) ∈ normalizer ((P : Subgroup K) : Set K) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hPmem, hPmem]
    have hy : ((⟨k, hkK⟩ * y * (⟨k, hkK⟩ : K)⁻¹ : K) : Y) = u * y * u⁻¹ := (hk y y.2).symm
    rw [hy]
    refine ⟨fun hyR => mul_mem (mul_mem hu hyR) (inv_mem hu), fun hyR => ?_⟩
    simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hu) hyR) hu
  have hkP := RankTwoShapes.mem_sylow_of_mem_normalizer_of_pow P hkN a (Subtype.ext hkpow)
  exact ⟨k, hkK, (hPmem _).mp hkP, hcC⟩

theorem sylow_le_of_isComponent_of_fpf (hO : pPrimeCore 2 Y = ⊥) (R : Sylow 2 Y)
    (hab : IsMulCommutative (R : Subgroup Y))
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), n * a * n⁻¹ = a → a = 1)
    {K : Subgroup Y} (hK : IsComponent K) : (R : Subgroup Y) ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Walter.HasAbelianSylowTwo Y := Walter.hasAbelianSylowTwo_of_sylow R hab
  have hK' := (Walter.isComponent_iff_isComponentOf_top K).mp hK
  have : IsSimpleGroup K := Walter.isSimpleGroup_of_isComponentOf hO hY hK'
  have hnonab := Walter.nonabelian_of_isComponentOf hK'
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (Walter.isSubnormal_of_isComponentOf hK')
  have hPmem : ∀ x : K, x ∈ (P : Subgroup K) ↔ (x : Y) ∈ (R : Subgroup Y) := by
    intro x
    constructor
    · intro hx
      have hx' : (x : Y) ∈ (P : Subgroup K).map K.subtype := ⟨x, hx, rfl⟩
      rw [hP] at hx'
      exact hx'.1
    · intro hx
      have hx' : (x : Y) ∈ (R : Subgroup Y) ⊓ K := ⟨hx, x.2⟩
      rw [← hP] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [← Subtype.ext hyx]
  have hPab : IsMulCommutative (P : Subgroup K) := ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val (hab.is_comm.comm
      (⟨((x : K) : Y), (hPmem _).mp x.2⟩ : (R : Subgroup Y)) ⟨((y : K) : Y), (hPmem _).mp y.2⟩)
    exact h⟩⟩
  have h2K : 2 ∣ Nat.card K := even_iff_two_dvd.mp (Walter.even_card_of_isSimpleGroup hnonab)
  have h2P : 2 ∣ Nat.card (P : Subgroup K) :=
    P.isPGroup'.card_eq_or_dvd.resolve_left fun h =>
      P.ne_bot_of_dvd_card h2K (Subgroup.card_eq_one.mp h)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup K)) 2 h2P
  have hzZ : z ∈ center (P : Subgroup K) := mem_center_iff.mpr fun g => hPab.is_comm.comm g z
  obtain ⟨g, hgP, hgz⟩ :=
    RankTwoShapes.simple_central_sylow_involution_movement hnonab P z hzZ hz
  obtain ⟨n, hn, hn'⟩ := P.conj_eq_normalizer_conj_of_mem (z : K) g z.2 hgP
  have hconj : ∀ e ∈ normalizer ((P : Subgroup K) : Set K), ∀ u ∈ (R : Subgroup Y),
      (e : Y) * u * (e : Y)⁻¹ ∈ (R : Subgroup Y) := by
    intro e he u hu
    obtain ⟨k, hkK, hkR, hc⟩ :=
      exists_mem_inf_inv_mul_mem_centralizer_of_isComponent hO R hab hK hu
    have hek : (e : Y) * k * (e : Y)⁻¹ ∈ (R : Subgroup Y) :=
      (hPmem (e * ⟨k, hkK⟩ * e⁻¹)).mp ((mem_normalizer_iff.mp he _).mp ((hPmem _).mpr hkR))
    have hc' : (e : Y) * (k⁻¹ * u) * (e : Y)⁻¹ = k⁻¹ * u := by
      rw [mem_centralizer_iff.mp hc (e : Y) e.2, mul_inv_cancel_right]
    have heq : (e : Y) * u * (e : Y)⁻¹ =
        ((e : Y) * k * (e : Y)⁻¹) * ((e : Y) * (k⁻¹ * u) * (e : Y)⁻¹) := by group
    rw [heq, hc']
    exact mul_mem hek (mul_mem (inv_mem hkR) hu)
  have hdN : ((n⁻¹ : K) : Y) ∈ normalizer ((R : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro u
    refine ⟨hconj _ (inv_mem hn) u, fun hu => ?_⟩
    have h := hconj _ hn _ hu
    simp only [coe_inv, inv_inv] at h
    simpa [mul_assoc] using h
  have hdC : ((n⁻¹ : K) : Y) ∉ centralizer ((R : Subgroup Y) : Set Y) := by
    intro h
    apply hgz
    rw [hn']
    have h1 := mem_centralizer_iff.mp h _ ((hPmem _).mp z.2)
    apply Subtype.ext
    simp only [coe_mul, coe_inv] at h1 ⊢
    rw [← h1, inv_mul_cancel_right]
  intro u hu
  obtain ⟨k, hkK, hkR, hc⟩ := exists_mem_inf_inv_mul_mem_centralizer_of_isComponent hO R hab hK hu
  have h1 : k⁻¹ * u = 1 := hfpf _ hdN hdC _ (mul_mem (inv_mem hkR) hu)
    (by rw [mem_centralizer_iff.mp hc _ (n⁻¹ : K).2, mul_inv_cancel_right])
  have hu' : u = k := by
    calc u = k * (k⁻¹ * u) := (mul_inv_cancel_left k u).symm
      _ = k := by rw [h1, mul_one]
  exact hu' ▸ hkK

theorem layer_eq_bot_of_fpf_of_not_conj
    (hO : pPrimeCore 2 Y = ⊥) (R : Sylow 2 Y)
    (hab : IsMulCommutative (R : Subgroup Y))
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), n * a * n⁻¹ = a → a = 1)
    {a b : Y} (ha : a ∈ (R : Subgroup Y)) (hb : b ∈ (R : Subgroup Y))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hnc : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ ≠ b) :
    layer Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Walter.HasAbelianSylowTwo Y := Walter.hasAbelianSylowTwo_of_sylow R hab
  rw [layer, sSup_eq_bot]
  intro K hK
  have hRK := sylow_le_of_isComponent_of_fpf hO R hab hfpf hK
  have hK' := (Walter.isComponent_iff_isComponentOf_top K).mp hK
  have : IsSimpleGroup K := Walter.isSimpleGroup_of_isComponentOf hO hY hK'
  have hKA : Walter.IsAStar K := Walter.isAStar_of_hasAbelianSylowTwo
    (Walter.simpleCaseHyp_of_benderHyp Walter.benderHyp) (hY.subgroup K)
  obtain ⟨h, -, hh⟩ := Walter.bender1970_2_2_subgroup hKA (hRK ha) (hRK hb) ha2 hb2
  obtain ⟨n, hn, hn'⟩ :=
    R.conj_eq_normalizer_conj_of_mem a h⁻¹ ha (by rw [inv_inv, hh]; exact hb)
  rw [inv_inv, hh] at hn'
  exact absurd (by rw [inv_inv]; exact hn'.symm) (hnc n⁻¹ (inv_mem hn))

end TypeZero

variable {Y : Type*} [Group Y] [Finite Y]

theorem sylow_normal_of_layer_eq_bot (hO : pPrimeCore 2 Y = ⊥) (R : Sylow 2 Y)
    (hab : IsMulCommutative (R : Subgroup Y)) (hlayer : layer Y = ⊥) :
    (R : Subgroup Y).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y 2 hO hlayer
  have hFR : pCore 2 Y ≤ (R : Subgroup Y) := pCore_isPGroup.le_sylow_of_normal R
  have hRC : (R : Subgroup Y) ≤ centralizer (pCore 2 Y : Set Y) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (hab.is_comm.comm ⟨x, hFR hx⟩ ⟨u, hu⟩)
  rw [le_antisymm (hRC.trans hchar) hFR]
  exact pCore_normal

def SmallCopy (Y : Type*) : Type := Fin (Nat.card Y)

theorem sylow_normal_of_fpf_of_not_conj
    (hO : pPrimeCore 2 Y = ⊥) (R : Sylow 2 Y)
    (hab : IsMulCommutative (R : Subgroup Y))
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), n * a * n⁻¹ = a → a = 1)
    {a b : Y} (ha : a ∈ (R : Subgroup Y)) (hb : b ∈ (R : Subgroup Y))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hnc : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ ≠ b) :
    (R : Subgroup Y).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : SmallCopy Y ≃ Y := (Finite.equivFin Y).symm
  let _ : Group (SmallCopy Y) := e.group
  let E : SmallCopy Y ≃* Y := e.mulEquiv
  have : Finite (SmallCopy Y) := Finite.of_equiv Y e.symm
  let R' : Sylow 2 (SmallCopy Y) := R.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hR : ∀ x, x ∈ (R' : Subgroup (SmallCopy Y)) ↔ E x ∈ (R : Subgroup Y) := fun x => by
    change x ∈ (R : Subgroup Y).map E.symm.toMonoidHom ↔ _
    rw [mem_map_equiv, MulEquiv.symm_symm]
  have hN : ∀ n, n ∈ normalizer ((R' : Subgroup (SmallCopy Y)) : Set (SmallCopy Y)) ↔
      E n ∈ normalizer ((R : Subgroup Y) : Set Y) := fun n => by
    simp only [mem_normalizer_iff, hR, map_mul, map_inv]
    exact ⟨fun h y => by simpa using h (E.symm y), fun h x => h (E x)⟩
  have hC : ∀ n, n ∈ centralizer ((R' : Subgroup (SmallCopy Y)) : Set (SmallCopy Y)) ↔
      E n ∈ centralizer ((R : Subgroup Y) : Set Y) := fun n => by
    simp only [mem_centralizer_iff, SetLike.mem_coe, hR]
    refine ⟨fun h y hy => ?_, fun h x hx => E.injective (by simpa using h (E x) hx)⟩
    simpa using congrArg E (h (E.symm y) (by simpa using hy))
  have hO' : pPrimeCore 2 (SmallCopy Y) = ⊥ := by
    rw [pPrimeCore_eq_piCore, ← LocalCores.piCore_map_mulEquiv _ E.symm, ← pPrimeCore_eq_piCore,
      hO, Subgroup.map_bot]
  have hab' : IsMulCommutative (R' : Subgroup (SmallCopy Y)) := by
    change IsMulCommutative ((R : Subgroup Y).map E.symm.toMonoidHom)
    exact Subgroup.map_isMulCommutative _ _
  have hfpf' : ∀ n ∈ normalizer ((R' : Subgroup (SmallCopy Y)) : Set (SmallCopy Y)),
      n ∉ centralizer ((R' : Subgroup (SmallCopy Y)) : Set (SmallCopy Y)) →
      ∀ x ∈ (R' : Subgroup (SmallCopy Y)), n * x * n⁻¹ = x → x = 1 := by
    intro n hn hnC x hx hnx
    apply E.injective
    rw [map_one]
    exact hfpf (E n) ((hN n).mp hn) (fun h => hnC ((hC n).mpr h)) (E x) ((hR x).mp hx)
      (by rw [← map_inv, ← map_mul, ← map_mul, hnx])
  have hnc' : ∀ n ∈ normalizer ((R' : Subgroup (SmallCopy Y)) : Set (SmallCopy Y)),
      n * E.symm a * n⁻¹ ≠ E.symm b := by
    intro n hn h
    apply hnc (E n) ((hN n).mp hn)
    simpa using congrArg E h
  have hR'n := sylow_normal_of_layer_eq_bot hO' R' hab'
    (layer_eq_bot_of_fpf_of_not_conj hO' R' hab' hfpf' ((hR _).mpr (by simpa using ha))
      ((hR _).mpr (by simpa using hb)) (by rwa [MulEquiv.orderOf_eq])
      (by rwa [MulEquiv.orderOf_eq]) hnc')
  refine ⟨fun x hx g => ?_⟩
  have h := hR'n.conj_mem (E.symm x) ((hR _).mpr (by simpa using hx)) (E.symm g)
  rw [hR] at h
  simpa using h

theorem sylow_normal_of_fpf_of_not_conj_of_oddCore
    (hO : oddCore Y = ⊥) (R : Sylow 2 Y)
    (hab : IsMulCommutative (R : Subgroup Y))
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), n * a * n⁻¹ = a → a = 1)
    {a b : Y} (ha : a ∈ (R : Subgroup Y)) (hb : b ∈ (R : Subgroup Y))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hnc : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ ≠ b) :
    (R : Subgroup Y).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact sylow_normal_of_fpf_of_not_conj
    ((pPrimeCore_eq_piCore Y 2).trans ((oddCore_eq_piCore Y).symm.trans hO)) R hab hfpf ha hb
    ha2 hb2 hnc

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

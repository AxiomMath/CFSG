module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools



section Generic

variable {G : Type*} [Group G]

theorem mem_sup_of_commute {V R : Subgroup G} (hc : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v) {x : G}
    (hx : x ∈ V ⊔ R) : ∃ v ∈ V, ∃ r ∈ R, x = v * r := by
  let S : Subgroup G :=
    { carrier := {x | ∃ v ∈ V, ∃ r ∈ R, x = v * r}
      mul_mem' := by
        rintro _ _ ⟨v, hv, r, hr, rfl⟩ ⟨w, hw, s, hs, rfl⟩
        exact ⟨v * w, mul_mem hv hw, r * s, mul_mem hr hs,
          Commute.mul_mul_mul_comm (hc w hw r hr).symm v s⟩
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨v, hv, r, hr, rfl⟩
        exact ⟨v⁻¹, inv_mem hv, r⁻¹, inv_mem hr,
          (mul_inv_rev v r).trans (Commute.inv_inv (hc v hv r hr)).eq.symm⟩ }
  have hle : V ⊔ R ≤ S := sup_le (fun v hv => ⟨v, hv, 1, one_mem _, (mul_one v).symm⟩)
    (fun r hr => ⟨1, one_mem _, r, hr, (one_mul r).symm⟩)
  exact hle hx

theorem mem_sup_zpowers_iff {V : Subgroup G} {t : G} (hc : ∀ v ∈ V, v * t = t * v)
    (ht : t * t = 1) {x : G} : x ∈ V ⊔ zpowers t ↔ x ∈ V ∨ x * t ∈ V := by
  have h2 : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := fun k => by
    rw [zpow_eq_zpow_emod k (show t ^ (2 : ℤ) = 1 by rw [zpow_two, ht])]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨v, hv, _, hr, rfl⟩ := mem_sup_of_commute (R := zpowers t)
      (fun v hv _ hr => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
        exact (Commute.zpow_right (hc v hv) k).eq) hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    rcases h2 k with h | h
    · simpa [h] using Or.inl hv
    · simpa [h, mul_assoc, ht] using Or.inr hv
  · rcases hx with hx | hx
    · exact mem_sup_left hx
    · simpa using mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right (mem_zpowers t)))

theorem card_eq_two_mul_card_inf {F V : Subgroup G} {t : G} (htF : t ∈ F) (htV : t ∉ V)
    (hF : ∀ x ∈ F, x ∈ V ∨ x * t ∈ V) :
    Nat.card F = 2 * Nat.card ↥(F ⊓ V) := by
  have hi : ((F ⊓ V).subgroupOf F).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨t, htF⟩, fun b => ?_⟩
    rw [xor_iff_iff_not]
    simp only [mem_subgroupOf, mem_inf, coe_mul]
    exact ⟨fun ⟨_, h1⟩ ⟨_, h2⟩ => htV (by simpa using mul_mem (inv_mem h2) h1),
      fun h => ⟨mul_mem b.2 htF, (hF _ b.2).resolve_left fun hv => h ⟨b.2, hv⟩⟩⟩
  have := card_mul_index ((F ⊓ V).subgroupOf F)
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at this
  omega

theorem isElemAbelian_sup_zpowers {E : Subgroup G} {t : G} (hE : IsElemAbelian 2 E)
    (hc : ∀ e ∈ E, e * t = t * e) (ht : t * t = 1) : IsElemAbelian 2 (E ⊔ zpowers t) := by
  have hz : ∀ e ∈ E, ∀ r ∈ zpowers t, e * r = r * e := fun e he r hr => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    exact (Commute.zpow_right (hc e he) k).eq
  have hsq : ∀ k : ℤ, (t ^ k) ^ 2 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht, one_zpow]
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, r, hr, hxe⟩ := mem_sup_of_commute hz x.2
    obtain ⟨e', he', r', hr', hye⟩ := mem_sup_of_commute hz y.2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hr'
    have hee : Commute e e' := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
    show (x : G) * y = y * x
    rw [hxe, hye]
    exact (Commute.mul_left (hee.mul_right (hz e he _ hr'))
      (Commute.mul_right (hz e' he' _ hr).symm (Commute.zpow_zpow_self t k k'))).eq
  · obtain ⟨e, he, _, hr, rfl⟩ := mem_sup_of_commute hz hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    rw [Commute.mul_pow (hz e he _ hr), hE.2 e he, hsq, one_mul]

end Generic




section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_normalizer_conj_of_mem_center {P : Subgroup G} {t z : G}
    (hP : IsSylowOf 2 P (centralizer ({t} : Set G)))
    (hz : z ∈ P ⊓ centralizer (P : Set G)) (hconj : IsConj t z) :
    ∃ n ∈ normalizer (P : Set G), n⁻¹ * t * n = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hzC⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have ht : t = c⁻¹ * z * c := by rw [← hc]; group
  let P₂ : Subgroup G := P.map (MulAut.conj c⁻¹).toMonoidHom
  have hmem : ∀ x : G, x ∈ P₂ ↔ c * x * c⁻¹ ∈ P := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have e : c * ((MulAut.conj c⁻¹).toMonoidHom y) * c⁻¹ = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hy
    · intro hx
      refine Subgroup.mem_map.mpr ⟨c * x * c⁻¹, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hle : P₂ ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have key : (c * x * c⁻¹) * z = z * (c * x * c⁻¹) :=
      mem_centralizer_iff.mp hzC _ ((hmem x).mp hx)
    rw [ht]
    calc x * (c⁻¹ * z * c) = c⁻¹ * ((c * x * c⁻¹) * z) * c := by group
      _ = c⁻¹ * (z * (c * x * c⁻¹)) * c := by rw [key]
      _ = c⁻¹ * z * c * x := by group
  have hcard : Nat.card P₂ = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have hP₂ : IsSylowOf 2 P₂ (centralizer ({t} : Set G)) :=
    isSylowOf_of_card hle (by rw [hcard]; exact hP.card_eq)
  obtain ⟨k, hk, hkconj⟩ := hP.exists_mem_conj hP₂
  refine ⟨k⁻¹ * c⁻¹, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    have e1 : c * (c⁻¹ * h * c) * c⁻¹ = h := by group
    have e2 : (k⁻¹ * c⁻¹) * h * (k⁻¹ * c⁻¹)⁻¹ = k⁻¹ * (c⁻¹ * h * c) * k := by group
    rw [e2, ← hkconj, hmem, e1]
  · have hkt : k * t * k⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp hk, mul_inv_cancel_right]
    calc (k⁻¹ * c⁻¹)⁻¹ * t * (k⁻¹ * c⁻¹) = c * (k * t * k⁻¹) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hkt]
      _ = z := hc

omit [Finite G] in
theorem odd_card_normalizer_class {P : Subgroup G} {t : G} (hPt : P ≤ centralizer ({t} : Set G))
    (hodd : ¬ 2 ∣ P.index) :
    Odd (Nat.card {x : G // ∃ n ∈ normalizer (P : Set G), x = n⁻¹ * t * n}) := by
  set N : Subgroup G := normalizer (P : Set G)
  have hcomm : ∀ x ∈ P, x * t = t * x := fun x hx => mem_centralizer_singleton_iff.mp (hPt hx)
  have htC : t ∈ centralizer (P : Set G) := mem_centralizer_iff.mpr fun x hx => hcomm x hx
  have htN : t ∈ N := centralizer_le_normalizer _ htC
  have hPN : P ≤ N := le_normalizer
  let t' : N := ⟨t, htN⟩
  have himg : (Subtype.val '' conjugatesOf t' : Set G) = {x : G | ∃ n ∈ N, x = n⁻¹ * t * n} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      refine ⟨(c : G)⁻¹, N.inv_mem c.2, ?_⟩
      rw [← hc]
      simp [t']
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n⁻¹ * t * n, N.mul_mem (N.mul_mem (N.inv_mem hn) htN) hn⟩, ?_, rfl⟩
      exact isConj_iff.mpr ⟨⟨n⁻¹, N.inv_mem hn⟩, Subtype.ext (by simp [t'])⟩
  have hcard : Nat.card {x : G // ∃ n ∈ N, x = n⁻¹ * t * n} =
      (centralizer ({t'} : Set N)).index := by
    rw [Subgroup.index_centralizer_eq_ncard, ← Set.ncard_image_of_injective _ Subtype.val_injective,
      himg]
    exact Nat.card_coe_set_eq _
  have hsub : P.subgroupOf N ≤ centralizer ({t'} : Set N) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hcomm x hx)
  have hdvd : (centralizer ({t'} : Set N)).index ∣ P.index :=
    (Subgroup.index_dvd_of_le hsub).trans (Subgroup.relIndex_dvd_index_of_le hPN)
  rw [hcard]
  have hndvd : ¬ 2 ∣ (centralizer ({t'} : Set N)).index := fun h => hodd (h.trans hdvd)
  exact Nat.not_even_iff_odd.mp fun he => hndvd (even_iff_two_dvd.mp he)

end Sylow




section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_orderOf_eq_two_of_isPGroup_ne_bot {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (hK : IsPGroup 2 ↥K) (hne : K ≠ ⊥) : ∃ w ∈ K, orderOf w = 2 := by
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq K (by simpa using hn))
  have hdvd : 2 ∣ Nat.card K := hn ▸ dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨(x : H), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem exists_involution_normal_center {T N : Subgroup G} (hT : IsPGroup 2 ↥T) (hNT : N ≤ T)
    (hN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ w ∈ N, orderOf w = 2 ∧ ∀ t ∈ T, t * w = w * t := by
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let N₀ : Subgroup ↥T := N.subgroupOf T
  have hN₀ : N₀.Normal := ⟨fun n hn g => by
    have := hN (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)⟩
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro n hn
    have hmem : (⟨n, hNT hn⟩ : ↥T) ∈ N₀ := Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at hmem
    have : n = 1 := congrArg Subtype.val hmem
    rw [this]; exact Subgroup.one_mem _
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀ne
  obtain ⟨w, hw, hwo⟩ := exists_orderOf_eq_two_of_isPGroup_ne_bot
    (hT.to_subgroup (N₀ ⊓ center ↥T)) hX
  refine ⟨(w : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hwo
  · have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem mem_of_mul_self_of_normalizes {A V : Subgroup G} (hV : IsSylowOf 2 V A) {a : G}
    (ha : a ∈ A) (ha2 : a * a = 1) (hn : ∀ v ∈ V, a * v * a⁻¹ ∈ V) : a ∈ V := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hsq : a ^ 2 = 1 := by rw [sq]; exact ha2
  have hZ : IsPGroup 2 ↥(zpowers a) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hsq
  have hnorm : zpowers a ≤ normalizer (V : Set G) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hn x, fun hx => ?_⟩
    have := hn _ hx
    rwa [hinv, show a * (a * x * a) * a = (a * a) * x * (a * a) by group, ha2, one_mul,
      mul_one] at this
  have hW : IsPGroup 2 ↥(zpowers a ⊔ V) := hZ.to_sup_of_normal_right' hV.isPGroup hnorm
  have hle : zpowers a ⊔ V ≤ A := sup_le (zpowers_le.2 ha) hV.le
  have hEq : zpowers a ⊔ V = V := hV.eq_of_le le_sup_right hle hW
  rw [← hEq]
  exact Subgroup.mem_sup_left (mem_zpowers a)

end Sylow


end CFSG.OddStandard.Seitz77

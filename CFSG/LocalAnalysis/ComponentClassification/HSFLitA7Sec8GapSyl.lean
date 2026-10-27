module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapWC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapE

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace GapSyl

theorem burnside {X : Type} [Group X] [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R = P) {a b g : X}
    (ha : ∀ p ∈ P, p * a = a * p) (hb : ∀ p ∈ P, p * b = b * p) (hg : g * a * g⁻¹ = b) :
    ∃ n ∈ normalizer (P : Set X), n * a * n⁻¹ = b := by
  have hPK : P ≤ centralizer ({b} : Set X) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (hb p hp)
  have hQK : P.map (MulAut.conj g).toMonoidHom ≤ centralizer ({b} : Set X) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * p * g⁻¹ * (g * a * g⁻¹) = g * (p * a) * g⁻¹ := by group
      _ = g * (a * p) * g⁻¹ := by rw [ha p hp]
      _ = g * a * g⁻¹ * (g * p * g⁻¹) := by group
  obtain ⟨k, hk, hkQ⟩ := exists_conj_of_max hPK hQK hP (hP.map _)
    (fun R hR hle _ => hmax R hR hle) (card_map_of_injective (MulAut.conj g).injective)
  refine ⟨k⁻¹ * g, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    have e : k⁻¹ * (g * x * g⁻¹) * k = k⁻¹ * g * x * (k⁻¹ * g)⁻¹ := by group
    constructor
    · intro hx
      have := (hkQ (g * x * g⁻¹)).mp ⟨x, hx, by simp⟩
      rwa [e] at this
    · intro hx
      rw [← e] at hx
      obtain ⟨y, hy, hyx⟩ := (hkQ _).mpr hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx)
      rwa [← this]
  · have hkb : k * b = b * k := mem_centralizer_singleton_iff.mp hk
    calc k⁻¹ * g * a * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * a * g⁻¹) * k := by group
      _ = b := by rw [hg, mul_assoc, ← hkb, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_C_iff {X : Type} [Group X] {g z : X} :
    g ∈ centralizer ({z} : Set X) ↔ g * z * g⁻¹ = z := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h; rw [h, mul_inv_cancel_right]
  · intro h
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h]

end GapSyl

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

theorem wcData_of {g : X} (hmem : ∀ v, A.conjΦ g v ∈ Y.P)
    (hA : ∀ a ∈ A.AA, g⁻¹ * a * g ∈ Y.P) (ht : g⁻¹ * S.t * g ∈ Y.P) : Y.WCData g := by
  have key : ∀ a : X, g⁻¹ * a * g ∈ Y.P → ∀ v, ∃ w, a * A.conjΦ g v * a⁻¹ = A.conjΦ g w := by
    intro a h v
    refine ⟨A.mat ⟨g⁻¹ * a * g, Y.mem_NA h⟩ *ᵥ v, ?_⟩
    rw [BData.conjΦ, BData.conjΦ, ← A.conj_Φ ⟨g⁻¹ * a * g, Y.mem_NA h⟩ v]
    group
  exact ⟨hmem, fun a ha v => key a (hA a ha) v, key S.t ht⟩

theorem mem_NA_of_normalizer (hnc : ¬ SubConj F.E₁ F.E₂) {g : X}
    (hg : g ∈ normalizer (Y.P : Set X)) : g ∈ A.NA := by
  have hgi : g⁻¹ ∈ normalizer (Y.P : Set X) := inv_mem hg
  have hc : ∀ x ∈ Y.P, g⁻¹ * x * g ∈ Y.P := fun x hx => by
    have := (mem_normalizer_iff.mp hgi x).mp hx
    rwa [inv_inv] at this
  refine (Y.wcData_of (fun v => (mem_normalizer_iff.mp hg _).mp (Y.AA_le (A.Φ_mem v)))
    (fun a ha => hc a (Y.AA_le ha)) (hc _ Y.t_mem)).mem_NA hnc

theorem max_X (hnc : ¬ SubConj F.E₁ F.E₂) {R : Subgroup X} (hR : IsPGroup 2 R)
    (hle : Y.P ≤ R) : R = Y.P := by
  by_contra hne
  have hlt : Y.P < R := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨g, hgR, hgP, hgN⟩ := exists_mem_normalizer_of_lt hR hlt
  have hgA := Y.mem_NA_of_normalizer hnc hgN
  have hS : IsPGroup 2 (Y.P ⊔ zpowers g : Subgroup X) :=
    hR.to_le (sup_le hle (zpowers_le.mpr hgR))
  have := Y.maximal _ hS le_sup_left (sup_le Y.le_NA (zpowers_le.mpr hgA))
  exact hgP (this ▸ mem_sup_right (mem_zpowers g))


theorem card_le_two_mul (hnc : ¬ SubConj F.E₁ F.E₂) :
    Nat.card Y.P ≤ 2 * Nat.card (Y.P ⊓ centralizer ({S.z} : Set X) : Subgroup X) := by
  set C := Y.P ⊓ centralizer ({S.z} : Set X) with hC
  by_cases hall : ∀ p ∈ Y.P, p * S.z * p⁻¹ = S.z
  · have : C = Y.P := le_antisymm inf_le_left fun p hp =>
      mem_inf.mpr ⟨hp, GapSyl.mem_C_iff.mpr (hall p hp)⟩
    rw [this]
    omega
  push Not at hall
  obtain ⟨p₀, hp₀, hz₀⟩ := hall
  have hz₀' : p₀ * S.z * p₀⁻¹ = S.z * F.kF := (Y.conj_z hnc hp₀).resolve_left hz₀
  have hk : ∀ p ∈ Y.P, p * F.kF * p⁻¹ = F.kF := fun p hp => A.kF_fixed hnc (Y.mem_NA hp)
  have hk2 : F.kF * F.kF = 1 := by rw [← pow_two]; exact F.kF_sq
  have hzk : S.z * F.kF ≠ S.z := fun h => (isK_kF F).ne_one (by
    calc F.kF = S.z⁻¹ * (S.z * F.kF) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have hidx : (C.subgroupOf Y.P).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨p₀, hp₀⟩, fun b => ?_⟩
    have hb := (b : Y.P).2
    have hconj : ((b * ⟨p₀, hp₀⟩ : Y.P) : X) * S.z * ((b * ⟨p₀, hp₀⟩ : Y.P) : X)⁻¹ =
        (b : X) * S.z * (b : X)⁻¹ * F.kF := by
      simp only [Subgroup.coe_mul]
      calc (b : X) * p₀ * S.z * ((b : X) * p₀)⁻¹ = (b : X) * (p₀ * S.z * p₀⁻¹) * (b : X)⁻¹ := by
            group
        _ = (b : X) * S.z * (b : X)⁻¹ * ((b : X) * F.kF * (b : X)⁻¹) := by rw [hz₀']; group
        _ = (b : X) * S.z * (b : X)⁻¹ * F.kF := by rw [hk _ hb]
    have hbp : ((b * ⟨p₀, hp₀⟩ : Y.P) : X) ∈ Y.P := (b * ⟨p₀, hp₀⟩).2
    change Xor (((b * ⟨p₀, hp₀⟩ : Y.P) : X) ∈ C) ((b : X) ∈ C)
    rw [hC, mem_inf, mem_inf, GapSyl.mem_C_iff, GapSyl.mem_C_iff, hconj]
    simp only [hbp, hb, true_and]
    rcases Y.conj_z hnc hb with h | h <;> rw [h]
    · exact Or.inr ⟨rfl, hzk⟩
    · exact Or.inl ⟨by rw [mul_assoc, hk2, mul_one], hzk⟩
  have := (C.subgroupOf Y.P).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : C ≤ Y.P)).toEquiv] at this
  change Nat.card C * 2 = Nat.card Y.P at this
  omega

end BData.Syl

namespace BData

variable (A : BData S F T₁)

include A in
theorem not_conjTo_z_k (hnc : ¬ SubConj F.E₁ F.E₂) : ¬ ConjTo S.z F.kF := by
  rintro ⟨x, hx⟩
  obtain ⟨Y⟩ := A.exists_syl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmaxX : ∀ R : Subgroup X, IsPGroup 2 R → Y.P ≤ R → R = Y.P := fun R hR hle =>
    Y.max_X hnc hR hle
  have hk : ∀ p ∈ Y.P, p * F.kF = F.kF * p := fun p hp => by
    have := A.kF_fixed hnc (Y.mem_NA hp)
    calc p * F.kF = (p * F.kF * p⁻¹) * p := by group
      _ = F.kF * p := by rw [this]
  set Kz := centralizer ({S.z} : Set X) with hKz
  set C := Y.P ⊓ Kz with hC
  have hCp : IsPGroup 2 C := Y.isPGroup.to_le inf_le_left
  obtain ⟨P', hP'⟩ := (hCp.comap_subtype (K := Kz)).exists_le_sylow
  set Tz : Subgroup X := (P' : Subgroup Kz).map Kz.subtype with hTz
  have hTzp : IsPGroup 2 Tz := P'.isPGroup'.map _
  have hCT : C ≤ Tz := fun c hc => ⟨⟨c, (mem_inf.mp hc).2⟩, hP' hc, rfl⟩
  have hTK : Tz ≤ Kz := map_subtype_le _
  have hmaxTz : ∀ R : Subgroup X, IsPGroup 2 R → Tz ≤ R → R ≤ Kz → R = Tz := by
    intro R hR hle hRK
    have hR' : IsPGroup 2 (R.subgroupOf Kz) := hR.comap_of_injective _ (subtype_injective _)
    have hle' : (P' : Subgroup Kz) ≤ R.subgroupOf Kz := fun y hy => hle ⟨y, hy, rfl⟩
    have heq := P'.is_maximal' hR' hle'
    apply le_antisymm _ hle
    intro y hy
    have : (⟨y, hRK hy⟩ : Kz) ∈ (P' : Subgroup Kz) := by rw [← heq]; exact hy
    exact ⟨_, this, rfl⟩
  have hcard1 : Nat.card Tz ≤ Nat.card Y.P := by
    obtain ⟨g, -, hg⟩ := GapNH.exists_conj_le_of_max (le_top : Y.P ≤ ⊤) le_top Y.isPGroup
      hTzp fun R hR hle _ => hmaxX R hR hle
    rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
    refine card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using hg y hy
  have hz : S.z = x⁻¹ * F.kF * x := by rw [← hx]; group
  have hPz : Y.P.map (MulAut.conj x⁻¹).toMonoidHom ≤ Kz := by
    rintro _ ⟨p, hp, rfl⟩
    rw [GapSyl.mem_C_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hz]
    calc x⁻¹ * p * x * (x⁻¹ * F.kF * x) * (x⁻¹ * p * x)⁻¹ = x⁻¹ * (p * F.kF * p⁻¹) * x := by
          group
      _ = x⁻¹ * F.kF * x := by rw [A.kF_fixed hnc (Y.mem_NA hp)]
  have hcard2 : Nat.card Y.P ≤ Nat.card Tz := by
    obtain ⟨c, -, hc⟩ := GapNH.exists_conj_le_of_max hTK hPz hTzp (Y.isPGroup.map _) hmaxTz
    rw [← card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom) (MulAut.conj x⁻¹).injective,
      ← card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).injective]
    refine card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using hc y hy
  have hidx : (C.subgroupOf Tz).index ≤ 2 := by
    have h1 := (C.subgroupOf Tz).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv] at h1
    have h2 := Y.card_le_two_mul hnc
    change Nat.card Y.P ≤ 2 * Nat.card C at h2
    have hpos : 0 < Nat.card C := Nat.card_pos
    by_contra h
    push Not at h
    have : Nat.card C * 3 ≤ Nat.card C * (C.subgroupOf Tz).index := Nat.mul_le_mul_left _ h
    omega
  have hnorm : (C.subgroupOf Tz).Normal := by
    rcases (show (C.subgroupOf Tz).index = 1 ∨ (C.subgroupOf Tz).index = 2 by
      have := (C.subgroupOf Tz).index_ne_zero_of_finite
      omega) with h | h
    · rw [index_eq_one] at h
      rw [h]
      infer_instance
    · exact normal_of_index_eq_two h
  have hconjC : ∀ y ∈ Tz, ∀ c ∈ C, y * c * y⁻¹ ∈ C := fun y hy c hc =>
    hnorm.conj_mem ⟨c, hCT hc⟩ hc ⟨y, hy⟩
  have hzA : S.z ∈ A.AA := A.Φ_z ▸ A.Φ_mem _
  have hAC : A.AA ≤ C := fun a ha =>
    mem_inf.mpr ⟨Y.AA_le ha, mem_centralizer_singleton_iff.mpr (A.AA_comm ha hzA)⟩
  have htC : S.t ∈ C :=
    mem_inf.mpr ⟨Y.t_mem, mem_centralizer_singleton_iff.mpr (commute_of_mem_B t_mem_B z_mem_B)⟩
  have hinv : ∀ y ∈ Tz, ∀ c ∈ C, y⁻¹ * c * y ∈ Y.P := fun y hy c hc => by
    have := hconjC _ (inv_mem hy) c hc
    rw [inv_inv] at this
    exact (mem_inf.mp this).1
  have hTA : Tz ≤ A.NA := fun y hy =>
    (Y.wcData_of (g := y) (fun v => (mem_inf.mp (hconjC y hy _ (hAC (A.Φ_mem v)))).1)
      (fun a ha => hinv y hy a (hAC ha)) (hinv y hy _ htC)).mem_NA hnc
  obtain ⟨n, hn, hnT⟩ := exists_conj_of_max (K := A.NA) (P := Y.P) (Q := Tz) Y.le_NA hTA
    Y.isPGroup hTzp Y.maximal (le_antisymm hcard1 hcard2)
  have hz' : ∀ p ∈ Y.P, p * (n⁻¹ * S.z * n) = (n⁻¹ * S.z * n) * p := by
    intro p hp
    have hy : n * p * n⁻¹ ∈ Tz := (hnT _).mpr (by rwa [show n⁻¹ * (n * p * n⁻¹) * n = p by group])
    have hc := mem_centralizer_singleton_iff.mp (hTK hy)
    calc p * (n⁻¹ * S.z * n) = n⁻¹ * ((n * p * n⁻¹) * S.z) * n := by group
      _ = n⁻¹ * (S.z * (n * p * n⁻¹)) * n := by rw [hc]
      _ = (n⁻¹ * S.z * n) * p := by group
  obtain ⟨m, hm, hmk⟩ := GapSyl.burnside Y.isPGroup hmaxX hz' hk (g := x * n)
    (by rw [← hx]; group)
  have h1 : n⁻¹ * S.z * n = F.kF := by
    have e := hmk.trans (A.kF_fixed hnc (Y.mem_NA_of_normalizer hnc hm)).symm
    exact mul_left_cancel (mul_right_cancel e)
  have h2 : S.z = F.kF := by
    calc S.z = n * (n⁻¹ * S.z * n) * n⁻¹ := by group
      _ = F.kF := by rw [h1, A.kF_fixed hnc hn]
  rw [← A.Φ_z, ← A.Φ_k] at h2
  have := A.Φ_injective h2
  revert this
  decide

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit

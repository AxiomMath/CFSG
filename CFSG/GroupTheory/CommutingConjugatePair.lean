module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.ABGLocalTools

theorem inf_eq_bot_of_isPGroup_two_of_odd {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hH : IsPGroup 2 H) (hK : Odd (Nat.card ↥K)) : H ⊓ K = ⊥ := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [← disjoint_iff]
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hn]
  exact hK.coprime_two_left.pow_left n



theorem eq_of_map_eq_map_of_isPGroup_of_odd_ker
    {U C : Type*} [Group U] [Finite U] [Group C]
    (π : U →* C) (hc : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {A B : Subgroup U} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (h : A.map π = B.map π) : A = B := by
  have key : ∀ {X Y : Subgroup U}, IsPGroup 2 X → IsPGroup 2 Y →
      X.map π = Y.map π → X ≤ Y := by
    intro X Y hX hY hXY
    intro a ha
    have hYZ : Y ⊓ π.ker = ⊥ :=
      inf_eq_bot_of_isPGroup_two_of_odd hY hodd
    have hXsup : X ≤ Y ⊔ π.ker := by
      intro x hx
      have hπx : π x ∈ Y.map π := by
        rw [← hXY]
        exact Subgroup.mem_map_of_mem π hx
      obtain ⟨y, hy, hxy⟩ := hπx
      have hz : x * y⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
      have haeq : x = (x * y⁻¹) * y := by group
      rw [haeq]
      exact (Y ⊔ π.ker).mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hy)
    have hmem : a ∈ Y ⊔ π.ker := hXsup ha
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨b, hb, z, hz, haeq⟩ := hmem
    have hzc : z ∈ Subgroup.center U := hc hz
    have hcomm : Commute b z := Subgroup.mem_center_iff.1 hzc b
    obtain ⟨n, hn⟩ := hX ⟨a, ha⟩
    have hapow : a ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 : (b * z) ^ 2 ^ n = 1 := by
      rw [haeq]
      exact hapow
    rw [hcomm.mul_pow] at h1
    have hbpow_mem : b ^ 2 ^ n ∈ Y ⊓ π.ker := by
      refine ⟨Y.pow_mem hb _, ?_⟩
      have h2 : b ^ 2 ^ n = (z ^ 2 ^ n)⁻¹ := by
        calc b ^ 2 ^ n = ((b ^ 2 ^ n)⁻¹)⁻¹ := (inv_inv _).symm
          _ = (z ^ 2 ^ n)⁻¹ := by rw [inv_eq_of_mul_eq_one_right h1]
      rw [h2]
      exact π.ker.inv_mem (π.ker.pow_mem hz _)
    have hbpow : b ^ 2 ^ n = 1 := by
      rw [hYZ] at hbpow_mem
      exact Subgroup.mem_bot.mp hbpow_mem
    have hzpow : z ^ 2 ^ n = 1 := by
      rw [hbpow, one_mul] at h1
      exact h1
    have hdvd : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hzpow
    have hoddz : Odd (orderOf z) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard π.ker hz)
    have hcop : Nat.Coprime (orderOf z) (2 ^ n) := hoddz.coprime_two_right.pow_right n
    have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)
    have haeqb : a = b := by rw [← haeq, hz1, mul_one]
    rwa [haeqb]
  exact le_antisymm (key hA hB h) (key hB hA h.symm)

theorem exists_conj_invariant_sylow {G : Type*} [Group G] [Finite G] {t : G} (ht : t ^ 2 = 1)
    {Y : Subgroup G} (hY : Y.map (MulAut.conj t) = Y) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q Y ∧ Q.map (MulAut.conj t) = Q := by
  classical
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr ht)
  let K : Subgroup G := Y ⊔ Subgroup.zpowers t
  have htK : t ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht_norm_Y : t ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hY
  have hK_le_normY : K ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact ht_norm_Y
  let tK : ↥K := ⟨t, htK⟩
  have hzpK : IsPGroup 2 (Subgroup.zpowers tK) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe tK]
      exact orderOf_dvd_iff_pow_eq_one.mpr ht)
  obtain ⟨R, hR⟩ := hzpK.exists_le_sylow
  let RK : Subgroup G := (R : Subgroup ↥K).map K.subtype
  have hRK_sylow : IsSylowOf 2 RK K := ⟨R, rfl⟩
  have hQ_sylow : IsSylowOf 2 (RK ⊓ Y) Y :=
    IsSylowOf.inf_of_le_normalizer hRK_sylow le_sup_left hK_le_normY
  have htRK : t ∈ RK := ⟨tK, hR (Subgroup.mem_zpowers tK), rfl⟩
  refine ⟨RK ⊓ Y, hQ_sylow, ?_⟩
  rw [Subgroup.map_inf (N := G) RK Y (MulAut.conj t) (MulAut.conj t).injective,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htRK), hY]

theorem exists_le_card_eq_commute_conj_of_odd_inf {G : Type*} [Group G] [Finite G] {t : G}
    (ht : t ^ 2 = 1) {P X₀ : Subgroup G} (hX₀P : X₀ ≤ P) (hX₀ : IsPGroup 2 X₀)
    (hodd : Odd (Nat.card ↥(P ⊓ P.map (MulAut.conj t).toMonoidHom)))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P.map (MulAut.conj t).toMonoidHom,
      x * y * x⁻¹ * y⁻¹ ∈ P ⊓ P.map (MulAut.conj t).toMonoidHom) :
    ∃ X : Subgroup G, X ≤ P ∧ Nat.card X = Nat.card X₀ ∧
      (∀ a ∈ X, ∀ c ∈ X, a * (t * c * t⁻¹) = (t * c * t⁻¹) * a) ∧
      ∀ a ∈ X, t * a * t⁻¹ ∈ X → a = 1 := by
  classical
  have htt : t * t = 1 := by rw [← pow_two]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let φ : G →* G := (MulAut.conj t).toMonoidHom
  have hφ_apply : ∀ x : G, φ x = t * x * t⁻¹ := fun x => rfl
  have hφ_invol : ∀ x : G, φ (φ x) = x := by
    intro x
    have hφφ : (MulAut.conj t) * (MulAut.conj t) = 1 := by
      rw [← map_mul, ← pow_two, ht, map_one]
    calc φ (φ x) = ((MulAut.conj t) * (MulAut.conj t)) x := rfl
      _ = x := by rw [hφφ]; rfl
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have h := congrArg φ hab
    rwa [hφ_invol, hφ_invol] at h
  let P' : Subgroup G := P.map φ
  let Z : Subgroup G := P ⊓ P'
  let X₀' : Subgroup G := X₀.map φ
  let W : Subgroup G := X₀ ⊔ Z
  let W' : Subgroup G := W.map φ
  let Y : Subgroup G := W ⊔ W'
  have hφZ : Z.map φ = Z := by
    show (P ⊓ P').map φ = P ⊓ P'
    rw [Subgroup.map_inf P P' φ hφ_inj]
    have hcomp : φ.comp φ = MonoidHom.id G := MonoidHom.ext hφ_invol
    have hP' : P'.map φ = P := by
      show (P.map φ).map φ = P
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [hP']
    show P' ⊓ P = P ⊓ P'
    exact inf_comm P' P
  have hφW' : W'.map φ = W := by
    show (W.map φ).map φ = W
    have hcomp : φ.comp φ = MonoidHom.id G := MonoidHom.ext hφ_invol
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hW'_eq : W' = X₀' ⊔ Z := by
    show (X₀ ⊔ Z).map φ = X₀.map φ ⊔ Z
    rw [Subgroup.map_sup, hφZ]
  have hX₀'_le_P' : X₀' ≤ P' := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem φ (hX₀P hy)
  have hX₀_le_W : X₀ ≤ W := le_sup_left
  have hZ_le_W : Z ≤ W := le_sup_right
  have hW_le_P : W ≤ P := sup_le hX₀P inf_le_left
  have hZ_le_W' : Z ≤ W' := by
    rw [hW'_eq]; exact le_sup_right
  have hW'_le_P' : W' ≤ P' := by
    rw [hW'_eq]; exact sup_le hX₀'_le_P' inf_le_right
  have hW_inf_W' : W ⊓ W' = Z := by
    refine le_antisymm ?_ (le_inf hZ_le_W hZ_le_W')
    calc W ⊓ W' ≤ P ⊓ P' := inf_le_inf hW_le_P hW'_le_P'
      _ = Z := rfl
  have hX₀_normZ : X₀ ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx z hz
    have h := hcomm x (hX₀P hx) z (Subgroup.mem_inf.mp hz).2
    rw [show x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z from by group]
    exact Z.mul_mem h hz
  have hX₀Z_bot : X₀ ⊓ Z = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hX₀ hodd
  have hcardW : Nat.card W = Nat.card X₀ * Nat.card Z := by
    have hdisj : Disjoint Z X₀ := by
      rw [disjoint_iff, inf_comm]
      exact hX₀Z_bot
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z X₀
      hX₀_normZ hdisj
    rw [show W = Z ⊔ X₀ from sup_comm X₀ Z, h]
    exact Nat.mul_comm _ _
  have hW'_norm_W : W' ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy w hw
    have h := hcomm w (hW_le_P hw) y (hW'_le_P' hy)
    rw [show y * w * y⁻¹ = (w * y * w⁻¹ * y⁻¹)⁻¹ * w from by group]
    exact W.mul_mem (hZ_le_W (Z.inv_mem h)) hw
  have hY_le_normW : Y ≤ Subgroup.normalizer (W : Set G) :=
    sup_le Subgroup.le_normalizer hW'_norm_W
  have hφY : Y.map φ = Y := by
    show (W ⊔ W').map φ = W ⊔ W'
    rw [Subgroup.map_sup, hφW']
    show W' ⊔ W = W ⊔ W'
    exact sup_comm W' W
  obtain ⟨Q, hQ_sylow, hφQ⟩ :=
    exists_conj_invariant_sylow ht (show Y.map (MulAut.conj t) = Y from hφY)
  have hφQ' : Q.map φ = Q := hφQ
  have hQ_ispgroup : IsPGroup 2 Q := hQ_sylow.isPGroup
  let X : Subgroup G := Q ⊓ W
  have hX_sylow : IsSylowOf 2 X W :=
    IsSylowOf.inf_of_le_normalizer hQ_sylow le_sup_left hY_le_normW
  have hX₀_sylow : IsSylowOf 2 X₀ W := by
    refine isSylowOf_iff.mpr ⟨hX₀_le_W, hX₀, ?_⟩
    have hrel : X₀.relIndex W = Nat.card Z := by
      have h1 : X₀.relIndex W * Nat.card X₀ = Nat.card W := by
        have h := Subgroup.relIndex_mul_card (H := X₀) (K := W)
        rwa [inf_eq_left.mpr hX₀_le_W] at h
      have hpos : 0 < Nat.card X₀ := by
        obtain ⟨n, hn⟩ := hX₀.exists_card_eq
        rw [hn]
        exact Nat.pow_pos (by norm_num)
      have h2 : X₀.relIndex W * Nat.card X₀ = Nat.card Z * Nat.card X₀ := by
        rw [h1, hcardW, Nat.mul_comm (Nat.card X₀) (Nat.card Z)]
      exact Nat.mul_right_cancel hpos h2
    intro hdvd
    have ho : Odd (X₀.relIndex W) := by rw [hrel]; exact hodd
    obtain ⟨k, hk⟩ := ho
    exact Nat.not_two_dvd_bit1 k (hk ▸ hdvd)
  have hcardX : Nat.card X = Nat.card X₀ := by
    rw [hX_sylow.card_eq, hX₀_sylow.card_eq]
  have hQZ_bot : Q ⊓ Z = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hQ_ispgroup hodd
  refine ⟨X, ?_, hcardX, ?_, ?_⟩
  · exact (inf_le_right : X ≤ W).trans hW_le_P
  · intro a ha c hc
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
    have haW : a ∈ W := (Subgroup.mem_inf.mp ha).2
    have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hc).1
    have hcW : c ∈ W := (Subgroup.mem_inf.mp hc).2
    have hbQ : t * c * t⁻¹ ∈ Q := by
      have hmem : φ c ∈ Q.map φ := Subgroup.mem_map_of_mem φ hcQ
      rw [hφQ'] at hmem
      rwa [hφ_apply c] at hmem
    have hbW' : t * c * t⁻¹ ∈ W' := by
      have hmem : φ c ∈ W.map φ := Subgroup.mem_map_of_mem φ hcW
      rwa [hφ_apply c] at hmem
    have hcommZ : a * (t * c * t⁻¹) * a⁻¹ * (t * c * t⁻¹)⁻¹ ∈ Z :=
      hcomm a (hW_le_P haW) (t * c * t⁻¹) (hW'_le_P' hbW')
    have hcommQ : a * (t * c * t⁻¹) * a⁻¹ * (t * c * t⁻¹)⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem (Q.mul_mem haQ hbQ) (Q.inv_mem haQ)) (Q.inv_mem hbQ)
    have hone : a * (t * c * t⁻¹) * a⁻¹ * (t * c * t⁻¹)⁻¹ = 1 := by
      have hmem : a * (t * c * t⁻¹) * a⁻¹ * (t * c * t⁻¹)⁻¹ ∈ Q ⊓ Z :=
        ⟨hcommQ, hcommZ⟩
      rw [hQZ_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc a * (t * c * t⁻¹)
        = (a * (t * c * t⁻¹) * a⁻¹ * (t * c * t⁻¹)⁻¹) * ((t * c * t⁻¹) * a) := by
          group
      _ = (t * c * t⁻¹) * a := by rw [hone, one_mul]
  · intro a ha hconj
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
    have haW : a ∈ W := (Subgroup.mem_inf.mp ha).2
    have hbW : t * a * t⁻¹ ∈ W := (Subgroup.mem_inf.mp hconj).2
    have haW' : a ∈ W' := by
      have heq : a = φ (t * a * t⁻¹) := by
        rw [hφ_apply]
        calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
          _ = t * (t * a * t⁻¹) * t⁻¹ := by rw [htinv]
      rw [heq]
      exact Subgroup.mem_map_of_mem φ hbW
    have haZ : a ∈ Z := by
      have hmem : a ∈ W ⊓ W' := ⟨haW, haW'⟩
      rwa [hW_inf_W'] at hmem
    have hmem : a ∈ Q ⊓ Z := ⟨haQ, haZ⟩
    rw [hQZ_bot] at hmem
    exact Subgroup.mem_bot.mp hmem

end CFSG.GroupTheory

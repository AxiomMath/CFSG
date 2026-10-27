module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL24VBase
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7Base
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport
public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCB
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.ComponentClassification.FooteLit.L24V

open CFSG Subgroup Equiv CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

theorem mem_of_centralizes_kleinFour_a7 {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
    (e : 𝕊 ≃* alternatingGroup (Fin 7)) {W : Subgroup 𝕊} (hW : IsKleinFour W) {s : 𝕊}
    {k : ℕ} (hs : s ^ 2 ^ k = 1) (hsW : ∀ w ∈ W, s * w = w * s) : s ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hsW'
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => by
    have := hW
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set H := W ⊔ zpowers s with hHdef
  have hcw : ∀ w ∈ W, H ≤ centralizer ({w} : Set 𝕊) := fun w hw => by
    apply sup_le
    · intro v hv
      rw [mem_centralizer_singleton_iff]
      exact hWc v hv w hw
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      exact hsW w hw
  have hcs : H ≤ centralizer ({s} : Set 𝕊) := by
    apply sup_le
    · intro v hv
      rw [mem_centralizer_singleton_iff]
      exact (hsW v hv).symm
    · rw [zpowers_le, mem_centralizer_singleton_iff]
  have hHC : H ≤ centralizer (H : Set 𝕊) := by
    apply sup_le
    · intro w hw
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (hcw w hw hh)
    · rw [zpowers_le, mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (hcs hh)
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; norm_num)
  have hs2 : IsPGroup 2 (zpowers s) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hWN : W ≤ normalizer ((zpowers s : Subgroup 𝕊) : Set 𝕊) := fun w hw => by
    have hc : ∀ j : ℤ, w * s ^ j * w⁻¹ = s ^ j := fun j => by
      rw [((Commute.zpow_right (show Commute w s from (hsW w hw).symm) j)).eq,
        mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨j, rfl⟩
      rw [hc j]
      exact zpow_mem_zpowers s j
    · rintro ⟨j, hj⟩
      have : h = s ^ j := by
        rw [show h = w⁻¹ * (w * h * w⁻¹) * w by group, ← hj]
        rw [show w⁻¹ * s ^ j * w = w⁻¹ * (s ^ j * w) by group, ← (Commute.zpow_right
          (show Commute w s from (hsW w hw).symm) j).eq, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact zpow_mem_zpowers s j
  have hH2 : IsPGroup 2 H := hW2.to_sup_of_normal_right' hs2 hWN
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH2
  have hWH : W ≤ H := le_sup_left
  have hsH : s ∈ H := le_sup_right (a := W) (mem_zpowers s)
  have h4 : 4 ∣ Nat.card H := hW.card_four ▸ card_dvd_of_le hWH
  have hne : Nat.card H ≠ 4 := fun h =>
    hsW' ((eq_of_le_of_card_ge hWH (by rw [h, hW.card_four])) ▸ hsH)
  obtain ⟨Q, hQ⟩ := (hH2.map e.toMonoidHom).exists_le_sylow
  have hle8 : Nat.card H ≤ 8 := by
    have h1 := card_le_of_le hQ
    rwa [card_map_of_injective e.injective, Sol78.card_sylow_two_alt7 Q] at h1
  have h8 : Nat.card H = 8 := by
    rw [hn] at h4 hne hle8 ⊢
    have hn3 : n ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all
  have hHQ : H.map e.toMonoidHom = Q := eq_of_le_of_card_ge hQ (by
    rw [Sol78.card_sylow_two_alt7 Q, card_map_of_injective e.injective, h8])
  have hQc : ∀ u v : (Q : Subgroup (alternatingGroup (Fin 7))), u * v = v * u := by
    intro u v
    obtain ⟨a, ha, hau⟩ : (u : alternatingGroup (Fin 7)) ∈ H.map e.toMonoidHom := hHQ.symm ▸ u.2
    obtain ⟨b, hb, hbv⟩ : (v : alternatingGroup (Fin 7)) ∈ H.map e.toMonoidHom := hHQ.symm ▸ v.2
    apply Subtype.ext
    rw [coe_mul, coe_mul, ← hau, ← hbv, ← map_mul, ← map_mul,
      mem_centralizer_iff.mp (hHC hb) a ha]
  obtain ⟨G, hG2, x, hx, y, hy, hxy⟩ := AutL2Facts.exists_noncomm_two_subgroup_a7
  obtain ⟨Q', hGQ'⟩ := hG2.exists_le_sylow
  set φ := Sylow.equiv Q' Q with hφ
  apply hxy
  have h1 := hQc (φ ⟨x, hGQ' hx⟩) (φ ⟨y, hGQ' hy⟩)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (φ.injective h1)

theorem isKleinFour_comap_conj {𝕊 : Type} [Group 𝕊]
    (hconj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊)) {V : Subgroup (MulAut 𝕊)}
    (hV : IsKleinFour V) (hVI : V ≤ innAut5 𝕊) :
    IsKleinFour (V.comap (MulAut.conj : 𝕊 →* MulAut 𝕊)) := by
  have hWV : (V.comap (MulAut.conj : 𝕊 →* MulAut 𝕊)).map MulAut.conj = V :=
    map_comap_eq_self hVI
  let e' : V.comap (MulAut.conj : 𝕊 →* MulAut 𝕊) ≃* V :=
    (equivMapOfInjective _ _ hconj).trans (MulEquiv.subgroupCongr hWV)
  exact { card_four := (Nat.card_congr e'.toEquiv).trans hV.card_four
          exponent_two := (Monoid.exponent_eq_of_mulEquiv e').trans hV.exponent_two }

theorem l24V_a7 {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (e : 𝕊 ≃* alternatingGroup (Fin 7))
    {V : Subgroup (MulAut 𝕊)} (hV : IsKleinFour V) (hVI : V ≤ innAut5 𝕊)
    {P : Subgroup (MulAut 𝕊)} (hP : IsSylowOf 2 P (centralizer (V : Set (MulAut 𝕊)))) :
    ∃ f ∈ P, P = zpowers f ⊔ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) :=
    Sol78.conj_injective_of_footeSimpleType (Or.inl ⟨e⟩)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hV
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨hPC, hP2⟩ := le_and_isPGroup_of_isSylowOf hP
  have : IsCyclic ℤˣ := isCyclic_of_prime_card (p := 2)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units_int])
  refine exists_eq_zpowers_sup (Perm.sign.comp
    ((MulAut.congr e).trans Aut5A7.autPerm).toMonoidHom) (le_of_isSylowOf_centralizer hVc hV2 hP)
    fun x hxP hx1 => ?_
  have hxI : x ∈ innAut5 𝕊 := by
    rw [← Aut5.congr_mem_innAut5_iff e, Aut5A7.mem_innAut5_iff]
    exact hx1
  obtain ⟨s, rfl⟩ := hxI
  have hW := isKleinFour_comap_conj hconj hV hVI
  have hsW : ∀ w ∈ V.comap (MulAut.conj : 𝕊 →* MulAut 𝕊), s * w = w * s := fun w hw => by
    apply hconj
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp (hPC hxP) _ hw).symm
  obtain ⟨k, hk⟩ := hP2 ⟨MulAut.conj s, hxP⟩
  have hs : s ^ 2 ^ k = 1 := hconj (by
    rw [map_pow, map_one]
    exact congrArg Subtype.val hk)
  exact mem_of_centralizes_kleinFour_a7 e hW hs hsW

end CFSG.ComponentClassification.FooteLit.L24V

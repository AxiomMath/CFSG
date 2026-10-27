module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapDefs
public import CFSG.GroupTheory.OddKernelImage
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

theorem orderOf_mk'_eq_two_of_l34SuzOdd (hS : L34SuzOddSetting A t) {x : ↥A} (hx : x * x = 1)
    (hx1 : x ≠ 1) : orderOf (QuotientGroup.mk' (center ↥A) x) = 2 := by
  have hxZ : x ∉ center ↥A := by
    intro hxZ
    have hdvd : orderOf x ∣ Nat.card (center ↥A) := Subgroup.orderOf_dvd_natCard _ hxZ
    have h2 : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx) hx1
    rw [h2] at hdvd
    exact Odd.not_two_dvd_nat hS.odd_card_center hdvd
  have hne : QuotientGroup.mk' (center ↥A) x ≠ 1 := fun h =>
    hxZ ((QuotientGroup.eq_one_iff x).mp h)
  refine orderOf_eq_prime ?_ hne
  rw [pow_two, ← map_mul, hx, map_one]

theorem map_subgroupOf_eq_commutator_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) :
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) =
      ⁅centralizer (((V.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) :
          Subgroup (↥A ⧸ center ↥A)) : Set (↥A ⧸ center ↥A)),
        centralizer (((V.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) :
          Subgroup (↥A ⧸ center ↥A)) : Set (↥A ⧸ center ↥A))⁆ := by
  let π : ↥A →* (↥A ⧸ center ↥A) := QuotientGroup.mk' (center ↥A)
  let X : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G)
  have hXA : X ≤ A := inf_le_left
  have hcard : Nat.card (V.subgroupOf A) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD.le_A).toEquiv, hD.card_V]
  have hV2 : IsPGroup 2 (V.subgroupOf A) :=
    IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hoddπ : Odd (Nat.card π.ker) := by
    rw [show π.ker = center ↥A from QuotientGroup.ker_mk' _]
    exact hS.odd_card_center
  have hCA : X.subgroupOf A = Subgroup.centralizer ((V.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hxV⟩ v hv
      apply Subtype.ext
      exact hxV (v : G) (Subgroup.mem_subgroupOf.mp hv)
    · intro hxV
      refine ⟨x.2, ?_⟩
      intro v hv
      have hv' : (⟨v, hD.le_A hv⟩ : ↥A) ∈ V.subgroupOf A := by
        rw [Subgroup.mem_subgroupOf]
        exact hv
      have h := hxV ⟨v, hD.le_A hv⟩ hv'
      exact congrArg Subtype.val h
  have hsub : (⁅X, X⁆).subgroupOf A = ⁅X.subgroupOf A, X.subgroupOf A⁆ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hXA hXA),
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXA]
  have hKX : K = ⁅X, X⁆ := hD.K_eq
  rw [hKX, hsub, Subgroup.map_commutator, hCA,
    CFSG.ComponentClassification.GrSLit.map_centralizer_eq_of_odd_ker π
      (QuotientGroup.mk'_surjective _) (Odd.not_two_dvd_nat hoddπ) hV2]

theorem isSuzTwoBFour_map_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) :
    IsSuzTwoBFour ((V.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) := by
  let π : ↥A →* (↥A ⧸ center ↥A) := QuotientGroup.mk' (center ↥A)
  have hcard : Nat.card (V.subgroupOf A) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD.le_A).toEquiv, hD.card_V]
  have hV2 : IsPGroup 2 (V.subgroupOf A) :=
    IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hoddπ : Odd (Nat.card π.ker) := by
    rw [show π.ker = center ↥A from QuotientGroup.ker_mk' _]
    exact hS.odd_card_center
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CFSG.GroupTheory.natCard_map_of_isPGroup_of_odd hoddπ hV2, hcard]
  · rintro w ⟨v, hv, rfl⟩
    rw [← map_mul, show v * v = 1 from by
      apply Subtype.ext
      exact hD.mul_self (v : G) (Subgroup.mem_subgroupOf.mp hv), map_one]
  · rintro w ⟨v, hv, rfl⟩ hw1
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have hv1 : (v : G) ≠ 1 := by
      intro h
      apply hw1
      rw [show v = 1 from Subtype.ext h, map_one]
    have hveq : QuotientGroup.mk' (center ↥A) v =
        ((⟨(v : G), hD.le_A hvV⟩ : ↥A) : ↥A ⧸ center ↥A) := rfl
    rw [hveq]
    exact hD.card_centralizer (v : G) hvV hv1
  · rw [← map_subgroupOf_eq_commutator_of_l34SuzOdd hS hD]
    exact hD.card_image


theorem exists_lift_of_l34SuzOdd (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {d : G} (hdA : d ∈ A) (hdK : d ∈ K) (hd : d * d = 1) {x : ↥A ⧸ center ↥A}
    (hxK : x ∈ (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))
    (hxd : x * QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩ =
      QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩ * x)
    (hx2 : IsPGroup 2 (zpowers x)) :
    ∃ r : ↥A, (r : G) ∈ K ∧ (r : G) * d = d * r ∧ IsPGroup 2 (zpowers (r : G)) ∧
      QuotientGroup.mk' (center ↥A) r = x := by
  let π : ↥A →* (↥A ⧸ center ↥A) := QuotientGroup.mk' (center ↥A)
  let πK : ↥(K.subgroupOf A) →* (↥A ⧸ center ↥A) := π.comp (K.subgroupOf A).subtype
  have hoddπK : Odd (Nat.card πK.ker) := by
    have hle : πK.ker.map (K.subgroupOf A).subtype ≤ center ↥A := by
      rintro _ ⟨u, hu, rfl⟩
      exact (QuotientGroup.eq_one_iff (u : ↥A)).mp hu
    have hdvd : Nat.card πK.ker ∣ Nat.card (center ↥A) := by
      rw [← Subgroup.card_map_of_injective (K.subgroupOf A).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hS.odd_card_center hdvd
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxK
  have hxrange : Subgroup.zpowers x ≤ πK.range := by
    rw [Subgroup.zpowers_le]
    exact ⟨⟨k, hkK⟩, hkx⟩
  obtain ⟨P, hP2, hPmap, hPinj⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd (Φ := πK) hoddπK hxrange hx2
  have hxmem : x ∈ P.map πK := by rw [hPmap]; exact Subgroup.mem_zpowers x
  obtain ⟨r, hrP, hrx⟩ := Subgroup.mem_map.mp hxmem
  have hKA : K ≤ A := by
    rw [hD.K_eq]
    exact Subgroup.commutator_le_of_le inf_le_left inf_le_left
  have hdKsub : (⟨d, hKA hdK⟩ : ↥A) ∈ K.subgroupOf A := Subgroup.mem_subgroupOf.mpr hdK
  let dK : ↥(K.subgroupOf A) := ⟨⟨d, hKA hdK⟩, hdKsub⟩
  have hdKeq : πK dK = QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩ := by
    change QuotientGroup.mk' (center ↥A) (⟨d, hKA hdK⟩ : ↥A) =
      QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩
    rw [show (⟨d, hKA hdK⟩ : ↥A) = ⟨d, hdA⟩ from Subtype.ext rfl]
  have hcen : πK.ker ≤ Subgroup.center ↥(K.subgroupOf A) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hzA : (z : ↥A) ∈ center ↥A := (QuotientGroup.eq_one_iff (z : ↥A)).mp hz
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzA (w : ↥A))
  have hπp_mem : ∀ p ∈ P, πK p ∈ Subgroup.zpowers x := by
    intro p hp
    rw [← hPmap]
    exact Subgroup.mem_map_of_mem πK hp
  have hcommπ : ∀ p ∈ P, πK dK * πK p = πK p * πK dK := by
    intro p hp
    have hzpcen : Subgroup.zpowers x ≤
        Subgroup.centralizer ({πK dK} : Set (↥A ⧸ center ↥A)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      rw [hdKeq]
      exact hxd
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hzpcen (hπp_mem p hp))
    exact h.symm
  have hQ2 : IsPGroup 2 (P.map (MulAut.conj dK).toMonoidHom) :=
    hP2.map (MulAut.conj dK).toMonoidHom
  have hconjeq : ∀ p ∈ P, πK ((MulEquiv.toMonoidHom (MulAut.conj dK)) p) = πK p := by
    intro p hp
    change πK (MulAut.conj dK p) = πK p
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hcommπ p hp, mul_assoc,
      mul_inv_cancel, mul_one]
  have hQle : (P.map (MulAut.conj dK).toMonoidHom).map πK ≤ P.map πK := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
    rw [hconjeq p hp]
    exact Subgroup.mem_map_of_mem πK hp
  have hPle : P.map πK ≤ (P.map (MulAut.conj dK).toMonoidHom).map πK := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hconjeq p hp]
    exact Subgroup.mem_map_of_mem πK (Subgroup.mem_map_of_mem (MulAut.conj dK).toMonoidHom hp)
  have hQleP : P.map (MulAut.conj dK).toMonoidHom ≤ P :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hcen hoddπK hQ2 hQle
  have hPleQ : P ≤ P.map (MulAut.conj dK).toMonoidHom :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hcen hoddπK hP2 hPle
  have hPeqQ : P = P.map (MulAut.conj dK).toMonoidHom := le_antisymm hPleQ hQleP
  have hfix : ∀ p ∈ P, MulAut.conj dK p = p := by
    intro p hp
    have hmem : MulAut.conj dK p ∈ P := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj dK).toMonoidHom hp
      rwa [← hPeqQ] at h
    exact congrArg Subtype.val (hPinj (a₁ := ⟨MulAut.conj dK p, hmem⟩) (a₂ := ⟨p, hp⟩)
      (by simpa using hconjeq p hp))
  have hdK2 : dK * dK = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hd
  have hdKinv : dK⁻¹ = dK := inv_eq_of_mul_eq_one_right hdK2
  have hfixr : dK * r * dK = r := by
    simpa only [hdKinv, MulAut.conj_apply] using hfix r hrP
  have hcommK : dK * r = r * dK := by
    calc dK * r = dK * r * (dK * dK) := by rw [hdK2, mul_one]
      _ = dK * r * dK * dK := by group
      _ = r * dK := by rw [hfixr]
  have hzpr : IsPGroup 2 (Subgroup.zpowers r) :=
    hP2.to_le (Subgroup.zpowers_le.mpr hrP)
  have hzprG : IsPGroup 2 (Subgroup.zpowers (((r : ↥A) : G))) := by
    have h := hzpr.map ((A.subtype).comp (K.subgroupOf A).subtype)
    rwa [MonoidHom.map_zpowers] at h
  refine ⟨(r : ↥A), ?_, ?_, hzprG, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp r.2
  · have h := congrArg (fun u : ↥(K.subgroupOf A) => (((u : ↥A) : G))) hcommK
    simpa using h.symm
  · exact hrx

end CFSG.ComponentClassification.GrSLit.L34Sec5S

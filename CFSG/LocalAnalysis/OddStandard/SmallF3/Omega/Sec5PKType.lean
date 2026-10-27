module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec5pk_oddCoreIn_cent {M K' O : Subgroup G} (hKM : K' ≤ M) (hOM : O ≤ M)
    (hO : Odd (Nat.card O)) (hOc : ∀ o ∈ O, ∀ m ∈ M, m * o * m⁻¹ = o)
    (hdec : ∀ m ∈ M, ∃ c ∈ K', c⁻¹ * m ∈ O) :
    oddCoreIn K' = K' ⊓ oddCoreIn M := by
  have hMn : M ≤ Subgroup.normalizer (oddCoreIn M : Subgroup G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_normal M).1).mp
      (oddCoreIn_normal M).2
  have hK'norm : K' ≤ Subgroup.normalizer (K' ⊓ oddCoreIn M : Subgroup G) :=
    (le_inf Subgroup.le_normalizer (hKM.trans hMn)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hN : ((K' ⊓ oddCoreIn M : Subgroup G).subgroupOf K').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hK'norm
  have hodd : Odd (Nat.card (K' ⊓ oddCoreIn M : Subgroup G)) :=
    (odd_card_oddCoreIn M).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hle : K' ⊓ oddCoreIn M ≤ oddCoreIn K' := le_oddCoreIn_of_normal inf_le_left hN hodd
  have hVM : oddCoreIn K' ≤ M := (oddCoreIn_normal K').1.trans hKM
  have hMnorm : M ≤ Subgroup.normalizer (oddCoreIn K' : Subgroup G) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm v hv
    obtain ⟨c, hc, hco⟩ := hdec m hm
    have hvm : v ∈ M := hKM ((oddCoreIn_normal K').1 hv)
    have hcomm : (c⁻¹ * m) * v * (c⁻¹ * m)⁻¹ = v := by
      have h := hOc (c⁻¹ * m) hco v hvm
      have h' : v * (c⁻¹ * m) = (c⁻¹ * m) * v := by
        calc v * (c⁻¹ * m) = (v * (c⁻¹ * m) * v⁻¹) * v := by group
          _ = (c⁻¹ * m) * v := by rw [h]
      rw [← h']
      group
    have hmdecomp : m = c * (c⁻¹ * m) := by group
    have hcv : m * v * m⁻¹ = c * v * c⁻¹ := by
      rw [hmdecomp]
      rw [show (c * (c⁻¹ * m)) * v * (c * (c⁻¹ * m))⁻¹
          = c * ((c⁻¹ * m) * v * (c⁻¹ * m)⁻¹) * c⁻¹ from by group]
      rw [hcomm]
    rw [hcv]
    exact conj_mem_oddCoreIn (Subgroup.le_normalizer hc) hv
  refine le_antisymm ?_ hle
  refine le_inf (oddCoreIn_normal K').1 ?_
  exact le_oddCoreIn_of_normal hVM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr hMnorm) (odd_card_oddCoreIn K')

theorem sec5pk_isSL23Mod_cent {M K' O : Subgroup G} (hKM : K' ≤ M) (hOM : O ≤ M)
    (hO : Odd (Nat.card O)) (hOc : ∀ o ∈ O, ∀ m ∈ M, m * o * m⁻¹ = o)
    (hdec : ∀ m ∈ M, ∃ c ∈ K', c⁻¹ * m ∈ O) (hM : IsSL23Mod M) : IsSL23Mod K' := by
  obtain ⟨e⟩ := hM
  have hOle : O ≤ oddCoreIn M :=
    le_oddCoreIn_of_normal hOM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mpr
        (Subgroup.le_normalizer_iff.mpr (fun m hm o ho => by rw [hOc o ho m hm]; exact ho))) hO
  have hmemM : ∀ y : ↥M, y ∈ CFSG.oddCore ↥M ↔ (y : G) ∈ oddCoreIn M := by
    intro y
    rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      rwa [hzy'] at hz
  have hmemK : ∀ y : ↥K', y ∈ CFSG.oddCore ↥K' ↔ (y : G) ∈ oddCoreIn K' := by
    intro y
    rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      rwa [hzy'] at hz
  have hcent : oddCoreIn K' = K' ⊓ oddCoreIn M := sec5pk_oddCoreIn_cent hKM hOM hO hOc hdec
  let q : ↥M →* (↥M ⧸ CFSG.oddCore ↥M) := QuotientGroup.mk' (CFSG.oddCore ↥M)
  let f : ↥K' →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp (q.comp (Subgroup.inclusion hKM))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥M) x
    obtain ⟨c, hc, hco⟩ := hdec (m : G) m.2
    refine ⟨⟨c, hc⟩, ?_⟩
    have hdecomp : m = Subgroup.inclusion hKM ⟨c, hc⟩ * ⟨c⁻¹ * (m : G), hOM hco⟩ := by
      ext
      show (m : G) = c * (c⁻¹ * (m : G))
      group
    have hker1 : q ⟨c⁻¹ * (m : G), hOM hco⟩ = 1 := by
      change ((⟨c⁻¹ * (m : G), hOM hco⟩ : ↥M) : ↥M ⧸ CFSG.oddCore ↥M) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (hmemM ⟨c⁻¹ * (m : G), hOM hco⟩).mpr (hOle hco)
    have heq : q (Subgroup.inclusion hKM ⟨c, hc⟩) = q m := by
      rw [hdecomp, map_mul, hker1, mul_one]
    show e (QuotientGroup.mk' (CFSG.oddCore ↥M) (Subgroup.inclusion hKM ⟨c, hc⟩)) =
      e (QuotientGroup.mk' (CFSG.oddCore ↥M) m)
    exact congrArg e heq
  have hker : f.ker = CFSG.oddCore ↥K' := by
    ext x
    rw [MonoidHom.mem_ker]
    have hx1 : f x = 1 ↔
        (Subgroup.inclusion hKM x : ↥M ⧸ CFSG.oddCore ↥M) = 1 := by
      constructor
      · intro h
        have h1 : e (Subgroup.inclusion hKM x : ↥M ⧸ CFSG.oddCore ↥M) = e 1 := by
          rw [map_one]
          exact h
        exact e.injective h1
      · intro h
        change e ((Subgroup.inclusion hKM x : ↥M ⧸ CFSG.oddCore ↥M)) = 1
        rw [h, map_one]
    rw [hx1, QuotientGroup.eq_one_iff, hmemM (Subgroup.inclusion hKM x), hmemK x,
      Subgroup.coe_inclusion, hcent]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem sec5pk_oddCoreIn_sup {K O : Subgroup G} (hO : Odd (Nat.card O))
    (hOc : ∀ o ∈ O, ∀ k ∈ K, k * o * k⁻¹ = o) (hOK : oddCoreIn K ≤ O) :
    oddCoreIn (K ⊔ O) = O := by
  have hKn : K ≤ Subgroup.normalizer (O : Subgroup G) :=
    Subgroup.le_normalizer_iff.mpr (fun k hk o ho => by rw [hOc o ho k hk]; exact ho)
  have hOn : O ≤ Subgroup.normalizer (O : Subgroup G) := Subgroup.le_normalizer
  have hle : O ≤ oddCoreIn (K ⊔ O) := by
    refine le_oddCoreIn_of_normal le_sup_right ?_ hO
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hKn hOn)
  refine le_antisymm ?_ hle
  intro y hy
  have hyV : y ∈ (↑(K ⊔ O) : Set G) := (oddCoreIn_normal (K ⊔ O)).1 hy
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right K O hKn
  rw [hset, Set.mem_mul] at hyV
  obtain ⟨k, hkK, o, hOo, hko⟩ := hyV
  have hkV : k ∈ oddCoreIn (K ⊔ O) := by
    have hk_eq : k = y * o⁻¹ := by rw [← hko]; group
    rw [hk_eq]
    exact (oddCoreIn (K ⊔ O)).mul_mem hy ((oddCoreIn (K ⊔ O)).inv_mem (hle hOo))
  have hVKn : ((oddCoreIn (K ⊔ O) ⊓ K).subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    have hVn : K ⊔ O ≤ Subgroup.normalizer (oddCoreIn (K ⊔ O) : Subgroup G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_normal (K ⊔ O)).1).mp
        (oddCoreIn_normal (K ⊔ O)).2
    exact (le_inf (le_sup_left.trans hVn) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hVKodd : Odd (Nat.card ↥(oddCoreIn (K ⊔ O) ⊓ K)) :=
    (odd_card_oddCoreIn (K ⊔ O)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hVK : oddCoreIn (K ⊔ O) ⊓ K ≤ oddCoreIn K :=
    le_oddCoreIn_of_normal inf_le_right hVKn hVKodd
  have hkO : k ∈ O := hOK (hVK ⟨hkV, hkK⟩)
  rw [← hko]
  exact O.mul_mem hkO hOo

theorem sec5pk_twoCoreIn_cent {K K' O : Subgroup G} (hO : Odd (Nat.card O))
    (hOc : ∀ o ∈ O, ∀ k ∈ K, k * o * k⁻¹ = o) (hK'M : K' ≤ K ⊔ O)
    (hdec : ∀ m ∈ K ⊔ O, ∃ c ∈ K', c⁻¹ * m ∈ O) (hK : IsSL23Mod K) (hK' : IsSL23Mod K')
    (hQ : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2)) (hQK' : twoCoreIn K ≤ K') :
    twoCoreIn K' = twoCoreIn K := by
  have hKnQ : K ≤ Subgroup.normalizer (twoCoreIn K : Subgroup G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le_self K)).mp
      (normal_subgroupOf_twoCoreIn K)
  have hOnQ : O ≤ Subgroup.normalizer (twoCoreIn K : Subgroup G) := by
    rw [Subgroup.le_normalizer_iff]
    intro o ho q hq
    have hcomm : q * o = o * q := by
      have h := hOc o ho q (twoCoreIn_le_self K hq)
      calc q * o = (q * o * q⁻¹) * q := by group
        _ = o * q := by rw [h]
    have hoq : o * q * o⁻¹ = q := by rw [← hcomm]; group
    rw [hoq]
    exact hq
  have hK'normQ : K' ≤ Subgroup.normalizer (twoCoreIn K : Subgroup G) :=
    hK'M.trans (sup_le hKnQ hOnQ)
  have hNQ : ((twoCoreIn K).subgroupOf K').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK').mpr hK'normQ
  have hQP : twoCoreIn K ≤ twoCoreIn K' :=
    le_twoCoreIn_of_normal hQK' (isPGroup_twoCoreIn K) hNQ
  have hPcard : Nat.card (twoCoreIn K') ≤ 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard24 : Nat.card (↥K' ⧸ CFSG.oddCore ↥K') = 24 := by
      obtain ⟨e'⟩ := hK'
      rw [Nat.card_congr e'.toEquiv, Matrix.card_SL_field 2]
      simp [ZMod.card, Fin.prod_univ_two]
    have hmemK' : ∀ y : ↥K', y ∈ CFSG.oddCore ↥K' ↔ (y : G) ∈ oddCoreIn K' := by
      intro y
      rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have hzy' : z = y := Subtype.ext hzy
        rwa [hzy'] at hz
    have hdisj : twoCoreIn K' ⊓ oddCoreIn K' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxP, hxO⟩ := hx
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_twoCoreIn K')
      have hdvd2 : orderOf x ∣ 2 ^ n := by
        rw [← hn]
        exact Subgroup.orderOf_dvd_natCard (twoCoreIn K') hxP
      have hdvdo : orderOf x ∣ Nat.card (oddCoreIn K') :=
        Subgroup.orderOf_dvd_natCard _ hxO
      have hcop2 : Nat.Coprime (2 ^ n) (Nat.card (oddCoreIn K')) :=
        (Nat.coprime_two_left.mpr (odd_card_oddCoreIn K')).pow_left n
      have hcop : Nat.Coprime (orderOf x) (Nat.card (oddCoreIn K')) :=
        Nat.Coprime.coprime_dvd_left hdvd2 hcop2
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvdo)
    let g : ↥(twoCoreIn K') →* (↥K' ⧸ CFSG.oddCore ↥K') :=
      (QuotientGroup.mk' (CFSG.oddCore ↥K')).comp
        (Subgroup.inclusion (twoCoreIn_le_self K'))
    have hginj : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      have hmem : ((Subgroup.inclusion (twoCoreIn_le_self K') (a * b⁻¹) : ↥K') :
          ↥K' ⧸ CFSG.oddCore ↥K') = 1 := by
        show g (a * b⁻¹) = 1
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      have hOab : ((a : G) * (b : G)⁻¹) ∈ oddCoreIn K' := by
        have h1 : (Subgroup.inclusion (twoCoreIn_le_self K') (a * b⁻¹) : ↥K') ∈
            CFSG.oddCore ↥K' := (QuotientGroup.eq_one_iff _).mp hmem
        have h2 := (hmemK' _).mp h1
        simpa [Subgroup.coe_inclusion] using h2
      have hPab : ((a : G) * (b : G)⁻¹) ∈ twoCoreIn K' := by
        have h2 := (a * b⁻¹).2
        simpa using h2
      have hbot : ((a : G) * (b : G)⁻¹) ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]
        exact ⟨hPab, hOab⟩
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
    have hdvd : Nat.card (twoCoreIn K') ∣ Nat.card (↥K' ⧸ CFSG.oddCore ↥K') := by
      have hcardrange : Nat.card g.range = Nat.card (twoCoreIn K') :=
        (Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv).symm
      have hdvd' := Subgroup.card_dvd_of_le (le_top : g.range ≤ ⊤)
      rwa [Subgroup.card_top, hcardrange] at hdvd'
    have hdvd24 : Nat.card (twoCoreIn K') ∣ 24 := by rw [← hcard24]; exact hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_twoCoreIn K')
    have h2k : 2 ^ k ∣ 24 := by rw [← hk]; exact hdvd24
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h16' := h16.trans h2k
      norm_num at h16'
    calc Nat.card (twoCoreIn K') = 2 ^ k := hk
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hQcard : Nat.card (twoCoreIn K) = 8 := by
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcard : Nat.card (twoCoreIn K') ≤ Nat.card (twoCoreIn K) := by
    rw [hQcard]
    exact hPcard
  exact (Subgroup.eq_of_le_of_card_ge hQP hcard).symm

end CFSG.OddStandard.SmallF3.Omega

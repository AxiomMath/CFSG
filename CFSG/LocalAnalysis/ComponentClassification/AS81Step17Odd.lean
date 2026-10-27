module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_inf_centralizer_le {B V W : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 B) (hBcard : 2 ^ 2 ≤ Nat.card B)
    (hpV : ¬ 2 ∣ Nat.card V) (hBV : B ≤ normalizer (V : Set G))
    (hle : ∀ b ∈ B, b ≠ 1 → V ⊓ centralizer ({b} : Set G) ≤ W) : V ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction B V := Subgroup.conjMulDistribMulActionOfLeNormalizer B V hBV
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := B) (H := V) hBcard hpV
  have hle' : (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have hfix : a • v = v := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a v).mp hv
    have hc : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val hfix
    have hcomm : (v : G) ∈ centralizer ({(a : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (v : G) * a = a * v * (a : G)⁻¹ * a := by rw [hc]
        _ = a * v := by group
    exact hle a a.2 (fun h => ha (Subtype.ext h)) ⟨v.2, hcomm⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) := by
    rw [hgen]
    exact mem_top _
  exact hle' hmem

theorem le_of_forall_inf_centralizer_hyperplane_le {E V W : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 2 E) (hEn : Nontrivial E) (hpV : ¬ 2 ∣ Nat.card V)
    (hEV : E ≤ normalizer (V : Set G))
    (hle : ∀ B : Subgroup G, B ≤ E → B.relIndex E = 2 →
      V ⊓ centralizer (B : Set G) ≤ W) : V ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction E V := Subgroup.conjMulDistribMulActionOfLeNormalizer E V hEV
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := V) hpV
  have hle' : (⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [mem_comap]
    have hcomm : ∀ b : B, ((b : E) : G) * (x : G) * ((b : E) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine hle (B.map E.subtype) (map_subtype_le B) ?_ (mem_inf.mpr ⟨x.2, ?_⟩)
    · rw [relIndex, ← comap_subtype, comap_map_eq_self_of_injective E.subtype_injective]
      exact hB
    · rw [mem_centralizer_iff]
      rintro _ ⟨y, hyB, rfl⟩
      have h1 := hcomm ⟨y, hyB⟩
      change ((y : E) : G) * (x : G) = (x : G) * ((y : E) : G)
      calc ((y : E) : G) * (x : G) = (((y : E) : G) * x * ((y : E) : G)⁻¹) * ((y : E) : G) := by
            group
        _ = (x : G) * ((y : E) : G) := by rw [h1]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := mem_top _
  rw [← hgen] at hx'
  exact hle' hx'

omit [Finite G] in
theorem le_oddCoreIn_of_odd_normal {K N : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreIn K := by
  have hnormal : (N.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hodd' : Odd (Nat.card (N.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv]
  have hle := le_assemblyOddCore hnormal hodd'
  intro x hx
  exact ⟨⟨x, hNK hx⟩, hle hx, rfl⟩

theorem mem_oddCoreIn_of_mem_sup_of_odd {K R : Subgroup G} (hRK : R ≤ K) (hR : IsPGroup 2 R)
    {x : G} (hx : x ∈ oddCoreIn K ⊔ R) (hxo : Odd (orderOf x)) : x ∈ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn K with hO
  have hxK : x ∈ K := sup_le (oddCoreIn_le K) hRK hx
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn K
  set H := O ⊔ zpowers x with hH
  have hxN : zpowers x ≤ normalizer (O : Set G) := zpowers_le.mpr (le_normalizer_oddCoreIn K hxK)
  have hcardH := card_sup_mul_card_inf hxN
  have hHodd : Odd (Nat.card H) := by
    have h1 : Nat.card H ∣ Nat.card O * Nat.card (zpowers x) := ⟨_, hcardH.symm⟩
    rw [Nat.card_zpowers] at h1
    exact (hOodd.mul hxo).of_dvd_nat h1
  have hRN : R ≤ normalizer (O : Set G) := hRK.trans (le_normalizer_oddCoreIn K)
  have hcardOR := card_sup_mul_card_inf hRN
  rw [oddCoreIn_inf_eq_bot hR, card_bot, mul_one] at hcardOR
  have hHle : H ≤ O ⊔ R := sup_le le_sup_left (zpowers_le.mpr hx)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨k, hk⟩ : Nat.card O ∣ Nat.card H := card_dvd_of_le le_sup_left
  have hkdvd : k ∣ 2 ^ m := by
    have h1 := card_dvd_of_le hHle
    rw [hcardOR, hk, hm] at h1
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp h1
  have hkodd : Odd k := by
    have h1 : Odd (Nat.card O * k) := by rw [← hk]; exact hHodd
    exact Nat.Odd.of_mul_right h1
  have hk1 : k = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd with ⟨i, -, rfl⟩
    rcases i with _ | i
    · rfl
    · rw [pow_succ] at hkodd
      exact absurd hkodd (by simp [parity_simps])
  rw [hk1, mul_one] at hk
  have hHO : H = O := (eq_of_le_of_card_ge le_sup_left hk.le).symm
  have : x ∈ H := mem_sup_right (mem_zpowers x)
  rwa [hHO] at this

theorem mem_oddCoreIn_of_twoElements {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (h2 : ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn K ⊔ R)
    {c : G} (hcK : c ∈ K) (hc : Odd (orderOf c))
    (hcR : ∀ ρ ∈ R, c * ρ * c⁻¹ * ρ⁻¹ ∈ oddCoreIn K) : c ∈ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn K with hO
  have hOK : O ≤ K := oddCoreIn_le K
  have hRK : R ≤ K := hR.le
  have hconjO : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hk) o).mp ho
  have hRN : R ≤ normalizer (O : Set G) := hRK.trans (le_normalizer_oddCoreIn K)
  have hOR : O ⊓ R = ⊥ := oddCoreIn_inf_eq_bot hR.isPGroup
  let C : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ ρ ∈ R, k * ρ * k⁻¹ * ρ⁻¹ ∈ O}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨K.mul_mem ha hb, fun ρ hρ => ?_⟩
        have e : a * b * ρ * (a * b)⁻¹ * ρ⁻¹ =
            a * (b * ρ * b⁻¹ * ρ⁻¹) * a⁻¹ * (a * ρ * a⁻¹ * ρ⁻¹) := by group
        rw [e]
        exact O.mul_mem (hconjO a ha _ (hb' ρ hρ)) (ha' ρ hρ)
      one_mem' := ⟨K.one_mem, fun ρ _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact O.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨K.inv_mem ha, fun ρ hρ => ?_⟩
        have e : a⁻¹ * ρ * a⁻¹⁻¹ * ρ⁻¹ = a⁻¹ * (a * ρ * a⁻¹ * ρ⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconjO a⁻¹ (K.inv_mem ha) _ (O.inv_mem (ha' ρ hρ)) }
  have hCK : C ≤ K := fun k hk => hk.1
  have hRC : R ≤ C := fun r hr => ⟨hRK hr, fun ρ hρ => by
    rw [hRc r hr ρ hρ, mul_inv_cancel_right, mul_inv_cancel]
    exact O.one_mem⟩
  have hcC : c ∈ C := ⟨hcK, hcR⟩
  have hCn : K ≤ normalizer (C : Set G) := by
    have hle : ∀ x ∈ K, ∀ k ∈ C, x * k * x⁻¹ ∈ C := by
      rintro x hx k ⟨hk, hk'⟩
      refine ⟨K.mul_mem (K.mul_mem hx hk) (K.inv_mem hx), fun ρ hρ => ?_⟩
      obtain ⟨m, hm⟩ := hR.isPGroup ⟨ρ, hρ⟩
      have hm' : ρ ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have hρ1K : x⁻¹ * ρ * x ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hx) (hRK hρ)) hx
        exact this
      have hρ1 : (x⁻¹ * ρ * x) ^ 2 ^ m = 1 := by
        have := conj_pow (a := x⁻¹) (b := ρ) (i := 2 ^ m)
        rw [inv_inv] at this
        rw [this, hm', mul_one, inv_mul_cancel]
      have hmem := h2 _ hρ1K m hρ1
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left O R hRN] at hmem
      obtain ⟨o, ho, ρ₂, hρ₂, hdec⟩ := hmem
      have e1 : x * k * x⁻¹ * ρ * (x * k * x⁻¹)⁻¹ * ρ⁻¹ =
          x * (k * (x⁻¹ * ρ * x) * k⁻¹ * (x⁻¹ * ρ * x)⁻¹) * x⁻¹ := by group
      rw [e1]
      apply hconjO x hx
      rw [← hdec]
      have e2 : k * (o * ρ₂) * k⁻¹ * (o * ρ₂)⁻¹ =
          (k * o * k⁻¹) * (k * ρ₂ * k⁻¹ * ρ₂⁻¹) * o⁻¹ := by group
      rw [e2]
      exact O.mul_mem (O.mul_mem (hconjO k hk o ho) (hk' ρ₂ hρ₂)) (O.inv_mem ho)
    intro x hx
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hle x hx k hk
  have hRCs : IsSylowOf 2 R C := hR.of_le hRC hCK
  obtain ⟨P, hP⟩ := hRCs.exists_sylow_eq_subgroupOf
  have hPc : normalizer ((P : Subgroup ↥C) : Set ↥C) ≤ centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro q hq
    rw [hP] at hq
    have hx' : x ∈ normalizer ((R.subgroupOf C : Subgroup ↥C) : Set ↥C) := hP ▸ hx
    have hq' : (q : G) ∈ R := mem_subgroupOf.mp hq
    have hxq : ((x * q * x⁻¹ : ↥C) : G) ∈ R :=
      mem_subgroupOf.mp ((mem_normalizer_iff.mp hx' q).mp hq)
    have h1 : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ ∈ O := x.2.2 q hq'
    have h2 : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ ∈ R :=
      R.mul_mem (by simpa using hxq) (R.inv_mem hq')
    have h3 : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ = 1 := by
      have hmem : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ ∈ O ⊓ R := ⟨h1, h2⟩
      rwa [hOR, mem_bot] at hmem
    apply Subtype.ext
    simp only [coe_mul]
    have h4 : (x : G) * q * (x : G)⁻¹ = q := by
      calc (x : G) * q * (x : G)⁻¹ = (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ * q := by group
        _ = q := by rw [h3, one_mul]
    calc (q : G) * x = (x : G) * q * (x : G)⁻¹ * x := by rw [h4]
      _ = x * q := by group
  obtain ⟨Q, hQn, hQ2, hQidx, -, hQchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hPc
  have hcQ : (⟨c, hcC⟩ : ↥C) ∈ Q := by
    have h1 : orderOf (QuotientGroup.mk' Q (⟨c, hcC⟩ : ↥C)) ∣ orderOf c := by
      have := orderOf_map_dvd (QuotientGroup.mk' Q) (⟨c, hcC⟩ : ↥C)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (QuotientGroup.mk' Q (⟨c, hcC⟩ : ↥C)) ∣ Nat.card (↥C ⧸ Q) :=
      orderOf_dvd_natCard _
    have h3 : Nat.card (↥C ⧸ Q) = Nat.card P := hQidx
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [h3, hm] at h2
    have hcop : Nat.Coprime (orderOf c) (2 ^ m) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc)
    have h4 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
    exact h4
  have hQO : Q.map C.subtype ≤ O := by
    refine le_oddCoreIn_of_odd_normal ((map_subtype_le Q).trans hCK) (fun x hx => ?_) ?_
    · exact mem_normalizer_of_map_conj_eq (map_conj_map_subtype_of_characteristic Q (hCn hx))
    · rw [card_map_of_injective C.subtype_injective]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hQ2)
  exact hQO ⟨_, hcQ, rfl⟩

end CFSG.ComponentClassification.AS81

module

public import CFSG.GH74.Uniqueness.SU.SU8Burn
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

namespace Prod

variable {Hb : Type} [Group Hb] (K : Subgroup Hb)

theorem comm_centralizer (k : ↥K) (c : ↥(centralizer (K : Set Hb))) :
    Commute (K.subtype k) ((centralizer (K : Set Hb)).subtype c) := by
  show (k : Hb) * (c : Hb) = (c : Hb) * (k : Hb)
  exact Subgroup.mem_centralizer_iff.mp c.2 k k.2

def mulHom : ↥K × ↥(centralizer (K : Set Hb)) →* Hb :=
  MonoidHom.noncommCoprod K.subtype (centralizer (K : Set Hb)).subtype (comm_centralizer K)

theorem mulHom_apply (k : ↥K) (c : ↥(centralizer (K : Set Hb))) :
    mulHom K (k, c) = (k : Hb) * (c : Hb) := by
  simp [mulHom, MonoidHom.noncommCoprod_apply]

noncomputable def prodEquiv (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb)) :
    ↥K × ↥(centralizer (K : Set Hb)) ≃* Hb :=
  MulEquiv.ofBijective (mulHom K)
    (by
      constructor
      · rw [injective_iff_map_eq_one]
        rintro ⟨k, c⟩ h
        have h1 : (k : Hb) * (c : Hb) = 1 := by rw [← mulHom_apply]; exact h
        have hk : (k : Hb) ∈ K ⊓ centralizer (K : Set Hb) := by
          refine ⟨k.2, ?_⟩
          have : (k : Hb) = (c : Hb)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]; exact Subgroup.inv_mem _ c.2
        rw [hK, Subgroup.mem_bot] at hk
        have hk1 : k = 1 := Subtype.ext hk
        have hc1 : (c : Hb) = 1 := by
          have : (k : Hb) = 1 := hk
          rw [this, one_mul] at h1; exact h1
        exact Prod.ext hk1 (Subtype.ext hc1)
      · intro h
        obtain ⟨k, hk, hc⟩ := hsup h
        exact ⟨(⟨k, hk⟩, ⟨k⁻¹ * h, hc⟩), by rw [mulHom_apply]; simp⟩)

theorem prodEquiv_apply (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb)) (k : ↥K)
    (c : ↥(centralizer (K : Set Hb))) :
    prodEquiv K hK hsup (k, c) = (k : Hb) * (c : Hb) := mulHom_apply K k c

theorem sylow_split (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb))
    {S : Subgroup Hb} (hS : IsPGroup 2 S) (PK : Sylow 2 ↥K)
    (hPK : ∀ p : ↥K, p ∈ (PK : Subgroup ↥K) → (p : Hb) ∈ S) :
    ∀ s ∈ S, ∃ p : ↥K, p ∈ (PK : Subgroup ↥K) ∧ ∃ c : ↥(centralizer (K : Set Hb)),
      (c : Hb) ∈ S ∧ s = (p : Hb) * (c : Hb) := by
  set θ := prodEquiv K hK hsup with hθ
  let ι : Hb →* ↥K := (MonoidHom.fst ↥K ↥(centralizer (K : Set Hb))).comp θ.symm.toMonoidHom
  have hι : ∀ p : ↥K, ι (p : Hb) = p := by
    intro p
    have : θ (p, 1) = (p : Hb) := by rw [hθ, prodEquiv_apply]; simp
    have h2 : θ.symm (p : Hb) = (p, 1) := by rw [← this]; simp
    simp [ι, h2]
  have hle : (PK : Subgroup ↥K) ≤ S.map ι := fun p hp => ⟨(p : Hb), hPK p hp, hι p⟩
  have hmax : S.map ι = (PK : Subgroup ↥K) := PK.is_maximal' (hS.map ι) hle
  intro s hs
  have hιs : ι s ∈ (PK : Subgroup ↥K) := by rw [← hmax]; exact ⟨s, hs, rfl⟩
  have hdec : s = ((ι s : ↥K) : Hb) * ((θ.symm s).2 : Hb) := by
    have h1 : θ (θ.symm s) = s := θ.apply_symm_apply s
    have h2 := prodEquiv_apply K hK hsup (θ.symm s).1 (θ.symm s).2
    rw [Prod.mk.eta] at h2
    show s = (((θ.symm s).1 : ↥K) : Hb) * ((θ.symm s).2 : Hb)
    rw [← h2]
    exact h1.symm
  refine ⟨ι s, hιs, (θ.symm s).2, ?_, hdec⟩
  have h1 : ((θ.symm s).2 : Hb) = ((ι s : ↥K) : Hb)⁻¹ * s := by
    rw [eq_inv_mul_iff_mul_eq]; exact hdec.symm
  rw [h1]
  exact S.mul_mem (S.inv_mem (hPK _ hιs)) hs

theorem card_sylow_split (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb))
    {S : Subgroup Hb} (hS : IsPGroup 2 S) (PK : Sylow 2 ↥K)
    (hPK : ∀ p : ↥K, p ∈ (PK : Subgroup ↥K) → (p : Hb) ∈ S) :
    Nat.card S = Nat.card (PK : Subgroup ↥K) * Nat.card ↥(S ⊓ centralizer (K : Set Hb)) := by
  have hsplit := sylow_split K hK hsup hS PK hPK
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun x : ↥(PK : Subgroup ↥K) × ↥(S ⊓ centralizer (K : Set Hb)) =>
      (⟨((x.1 : ↥K) : Hb) * (x.2 : Hb), S.mul_mem (hPK _ x.1.2) x.2.2.1⟩ : ↥S)) ⟨?_, ?_⟩
  · rintro ⟨⟨p, hp⟩, ⟨w, hw⟩⟩ ⟨⟨p', hp'⟩, ⟨w', hw'⟩⟩ h
    have h1 : (p : Hb) * w = p' * w' := congrArg Subtype.val h
    have h2 : (p' : Hb)⁻¹ * p = w' * w⁻¹ := by
      calc (p' : Hb)⁻¹ * p = (p' : Hb)⁻¹ * (p * w) * w⁻¹ := by group
        _ = (p' : Hb)⁻¹ * (p' * w') * w⁻¹ := by rw [h1]
        _ = w' * w⁻¹ := by group
    have hmem : ((p'⁻¹ * p : ↥K) : Hb) ∈ K ⊓ centralizer (K : Set Hb) := by
      refine ⟨(p'⁻¹ * p).2, ?_⟩
      have : ((p'⁻¹ * p : ↥K) : Hb) = w' * w⁻¹ := by rw [← h2]; simp
      rw [this]
      exact (centralizer (K : Set Hb)).mul_mem hw'.2 ((centralizer (K : Set Hb)).inv_mem hw.2)
    rw [hK, Subgroup.mem_bot] at hmem
    have hpp : p' = p := by
      have : p'⁻¹ * p = 1 := Subtype.ext hmem
      exact inv_mul_eq_one.mp this
    subst hpp
    have : w = w' := by
      have h3 : (p' : Hb) * w = p' * w' := h1
      exact mul_left_cancel h3
    subst this
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨p, hp, c, hcS, hsc⟩ := hsplit s hs
    refine ⟨(⟨p, hp⟩, ⟨(c : Hb), hcS, c.2⟩), ?_⟩
    apply Subtype.ext
    exact hsc.symm

theorem card_eq_mul (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb)) :
    Nat.card Hb = Nat.card K * Nat.card ↥(centralizer (K : Set Hb)) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (prodEquiv K hK hsup).toEquiv).symm

variable [Finite Hb]

theorem card_centralizer_eq_two [K.Normal] (hK : K ⊓ centralizer (K : Set Hb) = ⊥)
    (hsup : ∀ h : Hb, ∃ k ∈ K, k⁻¹ * h ∈ centralizer (K : Set Hb))
    (hO : pPrimeCore 2 Hb = ⊥) {S : Subgroup Hb} (hS : IsSylowIn ⊤ S) (PK : Sylow 2 ↥K)
    (hPK : ∀ p : ↥K, p ∈ (PK : Subgroup ↥K) → (p : Hb) ∈ S)
    (hW : Nat.card ↥(S ⊓ centralizer (K : Set Hb)) = 2) :
    Nat.card ↥(centralizer (K : Set Hb)) = 2 := by
  have hcardHb := card_eq_mul K hK hsup
  have hcardS := card_sylow_split K hK hsup hS.2.1 PK hPK
  rw [hW] at hcardS
  have hSidx : Odd S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hPKidx : Odd (PK : Subgroup ↥K).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp PK.not_dvd_index)
  have hSHb : Nat.card S * S.index = Nat.card Hb := Subgroup.card_mul_index S
  have hPKK : Nat.card (PK : Subgroup ↥K) * (PK : Subgroup ↥K).index = Nat.card K :=
    Subgroup.card_mul_index _
  have hWC : Nat.card ↥(S ⊓ centralizer (K : Set Hb)) *
      (S ⊓ centralizer (K : Set Hb)).relIndex (centralizer (K : Set Hb)) =
        Nat.card ↥(centralizer (K : Set Hb)) := by
    have h1 := Subgroup.card_mul_index
      ((S ⊓ centralizer (K : Set Hb)).subgroupOf (centralizer (K : Set Hb)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : S ⊓ centralizer (K : Set Hb) ≤ centralizer (K : Set Hb))).toEquiv] at h1
    exact h1
  rw [hW] at hWC
  have hapos : 0 < Nat.card (PK : Subgroup ↥K) := Nat.card_pos
  have hr : Odd ((S ⊓ centralizer (K : Set Hb)).relIndex (centralizer (K : Set Hb))) := by
    have hmul : (2 * Nat.card (PK : Subgroup ↥K)) *
        ((PK : Subgroup ↥K).index * (S ⊓ centralizer (K : Set Hb)).relIndex
          (centralizer (K : Set Hb))) = (2 * Nat.card (PK : Subgroup ↥K)) * S.index := by
      calc (2 * Nat.card (PK : Subgroup ↥K)) * ((PK : Subgroup ↥K).index *
            (S ⊓ centralizer (K : Set Hb)).relIndex (centralizer (K : Set Hb)))
          = (Nat.card (PK : Subgroup ↥K) * (PK : Subgroup ↥K).index) *
              (2 * (S ⊓ centralizer (K : Set Hb)).relIndex (centralizer (K : Set Hb))) := by ring
        _ = Nat.card K * Nat.card ↥(centralizer (K : Set Hb)) := by rw [hPKK, hWC]
        _ = Nat.card Hb := hcardHb.symm
        _ = Nat.card S * S.index := hSHb.symm
        _ = (2 * Nat.card (PK : Subgroup ↥K)) * S.index := by rw [hcardS]; ring
    have h1 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by norm_num) hapos) hmul
    have h2 : Odd ((PK : Subgroup ↥K).index * (S ⊓ centralizer (K : Set Hb)).relIndex
        (centralizer (K : Set Hb))) := by
      rw [h1]; exact hSidx
    exact (Nat.odd_mul.mp h2).2
  have hWsyl : IsSylowIn (centralizer (K : Set Hb)) (S ⊓ centralizer (K : Set Hb)) :=
    ⟨inf_le_right, hS.2.1.to_le inf_le_left, hr⟩
  have hPWcard : Nat.card (Burn.sylowOf hWsyl : Subgroup ↥(centralizer (K : Set Hb))) = 2 := by
    rw [Burn.coe_sylowOf hWsyl, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : S ⊓ centralizer (K : Set Hb) ≤ centralizer (K : Set Hb))).toEquiv]
    exact hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(Burn.sylowOf hWsyl : Subgroup ↥(centralizer (K : Set Hb))) :=
    isCyclic_of_prime_card hPWcard
  obtain ⟨hcardM, -⟩ := CFSG.cyclic_sylow_normal_odd_complement (Burn.sylowOf hWsyl) hcyc
  have hbot : pPrimeCore 2 ↥(centralizer (K : Set Hb)) = ⊥ := by
    let M : Subgroup Hb := (pPrimeCore 2 ↥(centralizer (K : Set Hb))).map
      (centralizer (K : Set Hb)).subtype
    have hMn : M.Normal := by
      refine ⟨fun m hm h => ?_⟩
      obtain ⟨c, hc, rfl⟩ := hm
      have h1 := CFSG.pPrimeCore_map_iso 2
        (MulAut.conjNormal (H := centralizer (K : Set Hb)) h)
      have h2 : (MulAut.conjNormal (H := centralizer (K : Set Hb)) h c) ∈
          pPrimeCore 2 ↥(centralizer (K : Set Hb)) := by
        rw [← h1]; exact ⟨c, hc, rfl⟩
      exact ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩
    have hMc : Nat.Coprime 2 (Nat.card M) := by
      have : Nat.card M = Nat.card (pPrimeCore 2 ↥(centralizer (K : Set Hb))) :=
        Subgroup.card_map_of_injective (centralizer (K : Set Hb)).subtype_injective
      rw [this]; exact CFSG.pPrimeCore_coprime_card
    have h3 := CFSG.pPrimeCore_eq_bot_iff.mp hO M hMn hMc
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (centralizer (K : Set Hb)).subtype_injective).mp h3
  rw [hbot, Subgroup.card_bot, hPWcard] at hcardM
  omega

end Prod

end CFSG.GH74.Uniqueness.SU.SU8

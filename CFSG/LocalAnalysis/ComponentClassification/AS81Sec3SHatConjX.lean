module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Open

namespace Sec3ConjX

variable {G : Type*} [Group G]

theorem card_sup_eq_mul {S P : Subgroup G} (hP : P ≤ normalizer (S : Set G)) (hSP : S ⊓ P = ⊥) :
    Nat.card ↥(S ⊔ P) = Nat.card S * Nat.card P := by
  let f : ↥S × ↥P → ↥(S ⊔ P) := fun sp =>
    ⟨(sp.1 : G) * sp.2, mul_mem (mem_sup_left sp.1.2) (mem_sup_right sp.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun k => ?_⟩
    · have h1 : (a.1 : G) * a.2 = b.1 * b.2 := congrArg Subtype.val hab
      have h2 : (b.1 : G)⁻¹ * a.1 = b.2 * (a.2 : G)⁻¹ := by
        calc (b.1 : G)⁻¹ * a.1 = (b.1 : G)⁻¹ * (a.1 * a.2) * (a.2 : G)⁻¹ := by group
          _ = (b.1 : G)⁻¹ * (b.1 * b.2) * (a.2 : G)⁻¹ := by rw [h1]
          _ = b.2 * (a.2 : G)⁻¹ := by group
      have h3 : (b.1 : G)⁻¹ * a.1 ∈ S ⊓ P :=
        mem_inf.mpr ⟨mul_mem (inv_mem b.1.2) a.1.2, h2 ▸ mul_mem b.2.2 (inv_mem a.2.2)⟩
      rw [hSP, mem_bot] at h3
      have e1 : (a.1 : G) = b.1 := by
        calc (a.1 : G) = b.1 * ((b.1 : G)⁻¹ * a.1) := by group
          _ = b.1 := by rw [h3, mul_one]
      have e2 : (a.2 : G) = b.2 := by
        rw [e1] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    · have hk : (k : G) ∈ ((S ⊔ P : Subgroup G) : Set G) := k.2
      rw [coe_mul_of_right_le_normalizer_left _ _ hP] at hk
      obtain ⟨s, hs, p, hp, hsp⟩ := hk
      exact ⟨(⟨s, hs⟩, ⟨p, hp⟩), Subtype.ext hsp⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end Sec3ConjX

open Sec3ConjX

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem exists_conj_x
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {n : G} (hnZ : n ∈ centralizer (Zs : Set G))
    (hk : ∀ s ∈ sec3SHat (Q₀ ⊔ Q) Zs,
      (n * x * n⁻¹ * x⁻¹) * s * (n * x * n⁻¹ * x⁻¹)⁻¹ * s⁻¹ ∈ Zs) :
    ∃ s ∈ sec3SHat (Q₀ ⊔ Q) Zs,
      ∃ w ∈ AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)),
        (s * n) * x * (s * n)⁻¹ = x * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hSdef
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  set W₁ := AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) with hW₁
  set k := n * x * n⁻¹ * x⁻¹ with hkdef
  have hSC : S ≤ sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hxZ : x ∈ centralizer (Zs : Set G) :=
    mem_centralizer_iff.mpr fun c hc => (H.x_comm_Zs hc).symm
  have hkZ : k ∈ centralizer (Zs : Set G) :=
    mul_mem (mul_mem (mul_mem hnZ hxZ) (inv_mem hnZ)) (inv_mem hxZ)
  have hZU : Zs ≤ U' := fun c hc => mem_inf.mpr ⟨H.Q_le (hZQ hc),
    mem_centralizer_iff.mpr fun d hd => H.comm_of_mem_Zs hd hc⟩
  have hUS : U' ≤ S := H.U_le_SHat hQF
  have hkU : k ∈ normalizer (U' : Set G) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨u, hu, rfl⟩
    show k * u * k⁻¹ ∈ U'
    have h1 := hZU (hk u (hUS hu))
    rw [show k * u * k⁻¹ = k * u * k⁻¹ * u⁻¹ * u by group]
    exact mul_mem h1 hu
  have hkN : k ∈ H.xsub.N := H.mem_N_of_mem_normalizer_U h17 hinner hCBz hZQ hkU
    (mem_centralizer_iff.mp hkZ z H.z_mem_Zs).symm
  obtain ⟨s₀, hs₀, w, hw, hksw⟩ := H.exists_mul_of_comm_SHat hΩ hQF hRc hZQ hkN hkZ hk
  have hwF := H.oddCoreIn_le_centralizer_sec3F hRc hw
  have hwx : w * x = x * w := mem_centralizer_singleton_iff.mp (H.oddCoreIn_le_centralizer_x h17 hw)
  have hws : ∀ t ∈ S, w * t = t * w := fun t ht => (mem_centralizer_iff.mp hwF t (hSC ht).1).symm
  have hnx : n * x * n⁻¹ = s₀ * x * w := by
    calc n * x * n⁻¹ = k * x := by rw [hkdef]; group
      _ = s₀ * w * x := by rw [hksw]
      _ = s₀ * x * w := by rw [mul_assoc, hwx, ← mul_assoc]
  have hxS : x ∈ normalizer (S : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (inf_normalizer_le_normalizer_inf ⟨H.N_le_normalizer_F H.x_mem_N, le_normalizer hxZ⟩)
  have hconj : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht => (mem_normalizer_iff.mp hxS t).mp ht
  have hcube : (s₀ * x) ^ 3 = 1 := by
    have h1 : (s₀ * x) ^ 3 ∈ S := by
      have e : (s₀ * x) ^ 3 = s₀ * (x * s₀ * x⁻¹) * (x * (x * s₀ * x⁻¹) * x⁻¹) * (x * x * x) := by
        rw [pow_three']
        group
      rw [e, ← pow_three', H.x_pow_three, mul_one]
      exact mul_mem (mul_mem hs₀ (hconj _ hs₀)) (hconj _ (hconj _ hs₀))
    have hcw : Commute (s₀ * x) w := by
      show s₀ * x * w = w * (s₀ * x)
      rw [mul_assoc, ← hwx, ← mul_assoc, ← hws s₀ hs₀, mul_assoc]
    have h2 : (s₀ * x) ^ 3 * w ^ 3 = 1 := by
      rw [← hcw.mul_pow, ← hnx, conj_pow, H.x_pow_three, mul_one, mul_inv_cancel]
    have h3 : (s₀ * x) ^ 3 ∈ W₁ := by
      rw [eq_inv_of_mul_eq_one_left h2]
      exact inv_mem (pow_mem hw 3)
    have h4 := AS76b.oddCoreIn_inf_eq_bot (K := centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) hS2
    have h5 : (s₀ * x) ^ 3 ∈ W₁ ⊓ S := mem_inf.mpr ⟨h3, h1⟩
    rw [h4, mem_bot] at h5
    exact h5
  have hx3 : orderOf x = 3 := H.q0.dData.suz.setting.order_x
  have hxS' : x ∉ S := by
    intro hx
    obtain ⟨m, hm⟩ := hS2 ⟨x, hx⟩
    have h1 : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hx3] at h2
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)) (by norm_num)
  have hsx1 : s₀ * x ≠ 1 := by
    intro h
    apply hxS'
    rw [show x = s₀⁻¹ * (s₀ * x) by group, h, mul_one]
    exact inv_mem hs₀
  have hsx3 : orderOf (s₀ * x) = 3 := orderOf_eq_prime hcube hsx1
  set K := S ⊔ zpowers x with hK
  have hPN : zpowers x ≤ normalizer (S : Set G) := zpowers_le.mpr hxS
  obtain ⟨a, ha⟩ := hS2.exists_card_eq
  have hcop : ∀ {P : Subgroup G}, Nat.card P = 3 → S ⊓ P = ⊥ := fun hP =>
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [ha, hP]; exact Nat.Coprime.pow_left a (by norm_num)))
  have hcx : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcsx : Nat.card (zpowers (s₀ * x)) = 3 := by rw [Nat.card_zpowers, hsx3]
  have hKc : Nat.card K = 2 ^ a * 3 := by
    rw [hK, card_sup_eq_mul hPN (hcop hcx), ha, hcx]
  have hsxK : s₀ * x ∈ K := mul_mem (mem_sup_left hs₀) (mem_sup_right (mem_zpowers x))
  have hsyl : ∀ {P : Subgroup G}, P ≤ K → Nat.card P = 3 →
      CFSG.ABGLocalTools.IsSylowOf 3 P K := by
    intro P hPK hP
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPK, IsPGroup.of_card (n := 1) (by rw [hP, pow_one]), fun h3 => ?_⟩
    have h1 := Subgroup.relIndex_mul_card P K
    rw [inf_eq_left.mpr hPK, hP, hKc] at h1
    have h2 : P.relIndex K = 2 ^ a := by omega
    rw [h2] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  obtain ⟨c, hcK, hc⟩ := (hsyl le_sup_right hcx).exists_mem_conj
    (hsyl (zpowers_le.mpr hsxK) hcsx)
  have hcK' : c ∈ ((S ⊔ zpowers x : Subgroup G) : Set G) := hcK
  rw [coe_mul_of_right_le_normalizer_left _ _ hPN] at hcK'
  obtain ⟨s₁, hs₁, p, hp, rfl⟩ := hcK'
  have hpx : p * x = x * p := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    exact (Commute.zpow_left (Commute.refl x) i).eq
  have hmem := (hc (s₀ * x)).mp (mem_zpowers _)
  set t := (s₁ * p)⁻¹ * (s₀ * x) * (s₁ * p) with ht
  have hts : s₁⁻¹ * (s₀ * x) * s₁ = p * t * p⁻¹ := by rw [ht]; group
  have htSx : t * x⁻¹ ∈ S := by
    have hpxi : p * x⁻¹ = x⁻¹ * p := by
      calc p * x⁻¹ = x⁻¹ * (x * p) * x⁻¹ := by group
        _ = x⁻¹ * (p * x) * x⁻¹ := by rw [hpx]
        _ = x⁻¹ * p := by group
    have h1 : t * x⁻¹ = p⁻¹ * (s₁⁻¹ * s₀ * (x * s₁ * x⁻¹)) * p := by
      calc t * x⁻¹ = p⁻¹ * s₁⁻¹ * s₀ * x * s₁ * (p * x⁻¹) := by rw [ht]; group
        _ = p⁻¹ * s₁⁻¹ * s₀ * x * s₁ * (x⁻¹ * p) := by rw [hpxi]
        _ = p⁻¹ * (s₁⁻¹ * s₀ * (x * s₁ * x⁻¹)) * p := by group
    rw [h1]
    have hpS : p⁻¹ * (s₁⁻¹ * s₀ * (x * s₁ * x⁻¹)) * p⁻¹⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (hPN (inv_mem hp)) _).mp
        (mul_mem (mul_mem (inv_mem hs₁) hs₀) (hconj _ hs₁))
    rwa [inv_inv] at hpS
  have htx : t = x := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
    have hi3 : x ^ i = x ^ (i % 3) := by
      rw [← zpow_mod_orderOf, hx3]; rfl
    have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rw [← hi, hi3] at htSx ⊢
    rcases hcases with h | h | h
    · exfalso
      rw [h, zpow_zero, one_mul] at htSx
      exact hxS' (by simpa using inv_mem htSx)
    · rw [h, zpow_one]
    · exfalso
      rw [h] at htSx
      have h2 : x ^ (2 : ℤ) * x⁻¹ = x := by
        rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one, mul_inv_cancel_right]
      rw [h2] at htSx
      exact hxS' htSx
  refine ⟨s₁⁻¹, inv_mem hs₁, w, hw, ?_⟩
  have h1 : s₁⁻¹ * (s₀ * x) * s₁ = x := by rw [hts, htx, hpx, mul_inv_cancel_right]
  have hws₁ : w * s₁ = s₁ * w := hws s₁ hs₁
  calc s₁⁻¹ * n * x * (s₁⁻¹ * n)⁻¹ = s₁⁻¹ * (n * x * n⁻¹) * s₁ := by group
    _ = s₁⁻¹ * (s₀ * x) * (w * s₁) := by rw [hnx]; group
    _ = s₁⁻¹ * (s₀ * x) * s₁ * w := by rw [hws₁]; group
    _ = x * w := by rw [h1]

theorem conj_mem_U
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    {n' w : G} (hn'Z : n' ∈ centralizer (Zs : Set G))
    (hw : w ∈ AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)))
    (hx : n' * x * n'⁻¹ = x * w) {b : G} (hb : b ∈ B₀) (hbZ : b ∈ centralizer (Zs : Set G))
    {u : G} (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    (n'⁻¹ * b * n') * u * (n'⁻¹ * b * n')⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
  have hbx : b * x = x * b := H.B₀_comm_x hb
  have hbw : b * w = w * b :=
    mem_centralizer_iff.mp (H.oddCoreIn_le_centralizer_sec3F hRc hw) b (H.B₀_le_F hb)
  have hbxw : b * (x * w) = x * w * b := by rw [← mul_assoc, hbx, mul_assoc, hbw, mul_assoc]
  have hcx : n'⁻¹ * b * n' * x = x * (n'⁻¹ * b * n') := by
    calc n'⁻¹ * b * n' * x = n'⁻¹ * (b * (n' * x * n'⁻¹)) * n' := by group
      _ = n'⁻¹ * ((n' * x * n'⁻¹) * b) * n' := by rw [hx, hbxw]
      _ = x * (n'⁻¹ * b * n') := by group
  have hbz : b * z = z * b := (mem_centralizer_iff.mp (H.B₀_le hb) z H.z_mem_Q₀).symm
  have hn'z : n' * z = z * n' := (mem_centralizer_iff.mp hn'Z z H.z_mem_Zs).symm
  have hcz : n'⁻¹ * b * n' * z = z * (n'⁻¹ * b * n') := by
    have hn'z' : n'⁻¹ * z = z * n'⁻¹ := ((show Commute n' z from hn'z).inv_left).eq
    calc n'⁻¹ * b * n' * z = n'⁻¹ * b * (n' * z) := by group
      _ = n'⁻¹ * (b * z) * n' := by rw [hn'z]; group
      _ = n'⁻¹ * z * b * n' := by rw [hbz]; group
      _ = z * (n'⁻¹ * b * n') := by rw [hn'z']; group
  have hcN := H.mem_normalizer_of_comm h17 hinner hCBz hcx hcz
  have hcZ : n'⁻¹ * b * n' ∈ centralizer (Zs : Set G) :=
    mul_mem (mul_mem (inv_mem hn'Z) hbZ) hn'Z
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcN u).mp hu.1,
    mul_mem (mul_mem hcZ hu.2) (inv_mem hcZ)⟩

end Sec38Hyp

end CFSG.ComponentClassification.AS81

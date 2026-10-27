module

public import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.GH74.Uniqueness.Bender.OddComplement
public import CFSG.GH74.Uniqueness.Theorem2

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

namespace Sec148

section General

variable {X : Type} [Group X]

theorem mem_normalizer_of_forall {H : Subgroup X} {g : X} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [e] at h3

theorem comm_of_mul_self_eq_one {V : Subgroup X} (h : ∀ x ∈ V, x * x = 1) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have h1 := h _ (V.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  calc a * b = (a * b)⁻¹ := h2.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem isPGroup_two_of_mul_self_eq_one {V : Subgroup X} (h : ∀ x ∈ V, x * x = 1) :
    IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h x x.2)⟩

theorem exists_mul_of_mem_sup {A B : Subgroup X} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {w : X}
    (hw : w ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, w = a * b := by
  have hB : B ≤ normalizer (A : Set X) := by
    intro b hb
    refine centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  have h1 : ((A ⊔ B : Subgroup X) : Set X) = (A : Set X) * (B : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  have hw' : w ∈ ((A ⊔ B : Subgroup X) : Set X) := hw
  rw [h1] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mul_self_eq_one_of_mem_sup {A B : Subgroup X} (hA : ∀ a ∈ A, a * a = 1)
    (hB : ∀ b ∈ B, b * b = 1) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ w ∈ A ⊔ B, w * w = 1 := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup h hw
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← h a ha b hb]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [hA a ha, hB b hb, one_mul]

variable [Finite X]

theorem mem_of_normal_sylow {U J : Subgroup X} (hU : ABGLocalTools.IsSylowOf 2 U J)
    (hnorm : ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U) {x : X} (hx : x ∈ J) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ U := by
  obtain ⟨-, -, hdvd⟩ := (ABGLocalTools.isSylowOf_iff (p := 2)).mp hU
  have : (U.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : X) g.2 (n : X) hn⟩
  have hodd : Odd (U.subgroupOf J).index := by
    have h2 : (U.subgroupOf J).index = U.relIndex J := rfl
    rw [h2, Nat.odd_iff]
    omega
  have := mem_of_odd_index (U.subgroupOf J) hodd (σ := (⟨x, hx⟩ : J)) (k := k)
    (Subtype.ext (by simpa using hxk))
  simpa [Subgroup.mem_subgroupOf] using this

theorem exists_conj_le_of_isSylowOf {C Q R : Subgroup X} (hQC : Q ≤ C) (hQ : IsPGroup 2 Q)
    (hR : ABGLocalTools.IsSylowOf 2 R C) : ∃ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ R := by
  obtain ⟨R', hR', hQR'⟩ := exists_isSylowOf_ge hQC hQ
  obtain ⟨w, hw, hwR⟩ := exists_conj_of_isSylowOf hR' hR
  refine ⟨w⁻¹, C.inv_mem hw, fun q hq => ?_⟩
  rw [← hwR, mem_conjugate_iff]
  have := hQR' hq
  simpa [mul_assoc] using this

theorem exists_conj_into_of_normal_two_sylow {Nn S D U B : Subgroup X}
    (hSN : S ≤ Nn) (hNS : Nn ≤ normalizer (S : Set X)) (hSp : IsPGroup 2 S)
    (hDN : D ≤ Nn) (hNSD : ∀ g ∈ Nn, ∃ s ∈ S, ∃ d ∈ D, g = s * d)
    (hUS : U ≤ S) (hUD : U ≤ D) (hDU : D ≤ normalizer (U : Set X)) (hUp : IsPGroup 2 U)
    (hodd : Odd (U.relIndex D)) (hBN : B ≤ Nn) (hB : Odd (Nat.card B)) :
    ∃ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ D := by
  classical
  have hUn : (U.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUD).mpr hDU
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup ↥D, (U.subgroupOf D).IsComplement' H' := by
    refine Subgroup.exists_right_complement'_of_coprime ?_
    obtain ⟨k, hk⟩ := (hUp.comap_subtype (K := D)).exists_card_eq
    have hk' : Nat.card (U.subgroupOf D) = 2 ^ k := hk
    have hidx : (U.subgroupOf D).index = U.relIndex D := rfl
    rw [hk', hidx]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  set H₀ : Subgroup X := H'.map D.subtype with hH₀
  have hH₀D : H₀ ≤ D := Subgroup.map_subtype_le H'
  have hH₀card : Nat.card H₀ = Nat.card H' :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hH₀odd : Odd (Nat.card H₀) := by
    rw [hH₀card, ← hH'.symm.index_eq_card]
    exact hodd
  have hH₀nd : ¬ 2 ∣ Nat.card H₀ := by
    have := Nat.odd_iff.mp hH₀odd
    omega
  have hUH : ∀ d ∈ D, ∃ u ∈ U, ∃ h ∈ H₀, d = u * h := by
    intro d hd
    obtain ⟨⟨⟨u', hu'⟩, ⟨h', hh'⟩⟩, hmul, -⟩ :=
      (Subgroup.isComplement_iff_existsUnique.mp (Subgroup.isComplement'_def.mp hH')) ⟨d, hd⟩
    refine ⟨u', hu', h', ⟨h', hh', rfl⟩, ?_⟩
    exact congrArg Subtype.val hmul.symm
  let N' : Subgroup ↥Nn := S.subgroupOf Nn
  let D' : Subgroup ↥Nn := H₀.subgroupOf Nn
  let A' : Subgroup ↥Nn := B.subgroupOf Nn
  have : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr hNS
  have hN'p : IsPGroup 2 N' := hSp.comap_subtype
  have hND : N' ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : X) ∈ S := hx.1
    have h2 : (x : X) ∈ H₀ := hx.2
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (eq_one_of_isPGroup_of_not_dvd Nat.prime_two hSp hH₀nd h1 h2))
  have hsup : N' ⊔ D' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs, d, hd, hx⟩ := hNSD (x : X) x.2
    obtain ⟨u, hu, h, hh, hdu⟩ := hUH d hd
    have hsu : s * u ∈ S := S.mul_mem hs (hUS hu)
    have e : x = ⟨s * u, hSN hsu⟩ * ⟨h, hDN (hH₀D hh)⟩ := by
      apply Subtype.ext
      simp [hx, hdu, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem_sup (show _ ∈ N' from hsu) (show _ ∈ D' from hh)
  have hA' : Odd (Nat.card A') := by
    have : Nat.card A' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    rwa [this]
  obtain ⟨n, hn, hconj⟩ := Bender.exists_conj_mem_of_odd_card (D₃ := D') hN'p hND hsup le_rfl
    (fun d hd _ => hd) hA'
  refine ⟨(n : X), hn, fun b hb => ?_⟩
  have h2 : ((n * ⟨b, hBN hb⟩ * n⁻¹ : ↥Nn) : X) ∈ H₀ := hconj ⟨b, hBN hb⟩ hb
  exact hH₀D (by simpa using h2)

end General

end Sec148

end CFSG.GH74.Uniqueness

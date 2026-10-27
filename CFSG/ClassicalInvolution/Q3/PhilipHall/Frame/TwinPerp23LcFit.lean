module

public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open CFSG CFSG.Open

private theorem fitlc_exists_aut {G : Type*} [Group G] [Finite G] {F : Subgroup G} {a : G}
    (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1) :
    ∃ η : MulAut ↥F, η ^ 3 = 1 ∧ ∀ x : ↥F, ((η x : ↥F) : G) = a * x * a⁻¹ := by
  have han : a ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => haF n hn
  refine ⟨F.normalizerMonoidHom ⟨a, han⟩, ?_, fun x => rfl⟩
  rw [← map_pow]
  convert map_one F.normalizerMonoidHom
  exact Subtype.ext ha3

private theorem fitlc_commute_of_thompson_AxB {G : Type*} [Group G] [Finite G] {Q B : Subgroup G}
    {c : G} (hQ : IsPGroup 2 Q) (hB : IsPGroup 2 B) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hc : Odd (orderOf c))
    (hcB : ∀ b ∈ B, c * b = b * c)
    (hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → c * q = q * c) :
    ∀ q ∈ Q, c * q = q * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers c with hAdef
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hcQ
  let α : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ)
  let β : B →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hBQ)
  have hα : ∀ (a : A) (q : Q), ((α a q : Q) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (q : Q), ((β b q : Q) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAdef, Nat.card_zpowers]
    exact Nat.odd_iff.mp hc |> fun h => by omega
  have hab : ∀ (a : A) (b : B), (a : G) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hcB b hb) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab a b]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hcr := hfix r r.2 hrB
    apply Subtype.ext
    rw [hα]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : Commute (c ^ k) (r : G) := Commute.zpow_left hcr k
    change c ^ k * r * (c ^ k)⁻¹ = r
    rw [this.eq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hQ hA2 hB α β hcomm hfix'
  intro q hq
  have hq' := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : G))
    (h ⟨c, Subgroup.mem_zpowers c⟩)
  rw [hα] at hq'
  change c * q * c⁻¹ = ((1 : MulAut Q) ⟨q, hq⟩ : G) at hq'
  rw [MulAut.one_apply] at hq'
  calc c * q = c * q * c⁻¹ * c := by group
    _ = q * c := by rw [hq']

theorem a_centralizes_fitting {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    (hOF : oddCore ↥F = ⊥) {a w : G} (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1)
    (hwF : w ∈ F) (hw2 : w * w = 1) (haw : a * w = w * a)
    (hfix : ∀ x ∈ F, x * w = w * x → a * x = x * a) :
    ∀ x ∈ ComponentClassification.Fitting.subgroup ↥F, a * (x : G) = (x : G) * a := by
  obtain ⟨η, -, hη⟩ := fitlc_exists_aut haF ha3
  have hchar := ComponentClassification.Fitting.characteristic ↥F
  have hnorm : (ComponentClassification.Fitting.subgroup ↥F).Normal := inferInstance
  set Q : Subgroup G := (ComponentClassification.Fitting.subgroup ↥F).map F.subtype
  have hQ2 : IsPGroup 2 Q := (isPGroup_two_genFittingFitting hOF).map F.subtype
  have hB2 : IsPGroup 2 (Subgroup.zpowers w) := by
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
    exact IsPGroup.of_card_dvd_pow (n := 1) (by rwa [Nat.card_zpowers, pow_one])
  have haQ : a ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map.mpr ⟨η y, Subgroup.characteristic_iff_le_comap.mp hchar η hy, hη y⟩
  have hwQ : w ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map.mpr ⟨⟨w, hwF⟩ * y * ⟨w, hwF⟩⁻¹, hnorm.conj_mem y hy ⟨w, hwF⟩, rfl⟩
  have hodd : Odd (orderOf a) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one ha3)
  have hcB : ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a w from haw) k).eq
  have hfixQ : ∀ q ∈ Q, (∀ b ∈ Subgroup.zpowers w, q * b = b * q) → a * q = q * a := by
    intro q hq hqB
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hq
    exact hfix _ y.2 (hqB w (Subgroup.mem_zpowers w))
  have key := fitlc_commute_of_thompson_AxB hQ2 hB2 haQ (Subgroup.zpowers_le.mpr hwQ) hodd hcB
    hfixQ
  exact fun x hx => key _ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem central_of_fitting_layer {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    (hOF : oddCore ↥F = ⊥) {a : G} (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1)
    (hfit : ∀ x ∈ ComponentClassification.Fitting.subgroup ↥F, a * (x : G) = (x : G) * a)
    (hlay : ∀ x ∈ ComponentClassification.Layer.subgroup ↥F, a * (x : G) = (x : G) * a) :
    ∀ x ∈ F, a * x = x * a := by
  obtain ⟨η, hη3, hη⟩ := fitlc_exists_aut haF ha3
  have hfixη : ∀ x : ↥F, a * (x : G) = (x : G) * a → η x = x := fun x hx =>
    Subtype.ext (by rw [hη]; exact mul_inv_eq_iff_eq_mul.mpr hx)
  have hle : ComponentClassification.Fitting.subgroup ↥F ⊔
      ComponentClassification.Layer.subgroup ↥F ≤ autFixSubgroup η :=
    sup_le (fun p hp => hfixη p (hfit p hp)) (fun p hp => hfixη p (hlay p hp))
  have hηFs : ∀ y ∈ genFittingFStar ↥F, η y = y := fun y hy => hle hy
  obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_fixes_fstar hOF η hηFs
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hη3) (orderOf_dvd_of_pow_eq_one hm)
  rw [(Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  intro x hx
  have h := hη ⟨x, hx⟩
  rw [hd, MulAut.one_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h.symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

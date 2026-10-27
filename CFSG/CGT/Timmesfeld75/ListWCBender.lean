module

public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.BenderSuzuki

section Sylow

variable {K : Type} [Group K]

theorem sylow_smul_eq_smul_iff {p : ℕ} {Q : Sylow p K} {g h : K} :
    g • Q = h • Q ↔ g⁻¹ * h ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
  have key : (g⁻¹ * h) • Q = Q ↔ g⁻¹ * h ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
    Sylow.smul_eq_iff_mem_normalizer
  rw [← key, mul_smul, inv_smul_eq_iff, eq_comm]

theorem mem_normalizer_of_eq_center' {Q T : Subgroup K}
    (hT : ∀ z, z ∈ T ↔ z ∈ Q ∧ ∀ y ∈ Q, Commute y z) {g : K}
    (hg : g ∈ Subgroup.normalizer (Q : Set K)) : g ∈ Subgroup.normalizer (T : Set K) := by
  have key : ∀ {g : K}, g ∈ Subgroup.normalizer (Q : Set K) → ∀ {z : K}, z ∈ T →
      g * z * g⁻¹ ∈ T := by
    intro g hg z hz
    obtain ⟨hzQ, hzc⟩ := (hT z).1 hz
    refine (hT _).2 ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hzQ, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      rwa [inv_inv] at h1
    have e1 : y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    have e2 : g * z * g⁻¹ * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
    show y * (g * z * g⁻¹) = g * z * g⁻¹ * y
    rw [e1, e2, (hzc _ hy').eq]
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key hg hh, fun hh => ?_⟩
  have h2 := key (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h2

variable [Finite K]

theorem sylow_inf_eq_bot (hK : IsBenderGroup K) {P Q : Sylow 2 K} (hPQ : P ≠ Q) :
    (P : Subgroup K) ⊓ Q = ⊥ := by
  by_contra hne
  have hp : IsPGroup 2 ((P : Subgroup K) ⊓ Q : Subgroup K) := P.isPGroup'.to_le inf_le_left
  rcases hp.card_eq_or_dvd with h1 | h2
  · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨⟨s, hs⟩, hsord⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [Subgroup.orderOf_mk] at hsord
  have hs2 : s * s = 1 := by rw [← pow_two, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    omega
  have hPN : (P : Subgroup K) ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := fun y hy =>
    centralizer_le_normalizer_of_isBenderGroup hK Q hs.2 hs2 hs1
      (Subgroup.mem_centralizer_singleton_iff.2
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK P hs.1 hs2 y
          hy).eq.symm)
  have hPQ' := le_of_isPGroup_of_le_normalizer P.isPGroup' Q hPN
  exact hPQ (Sylow.ext (P.is_maximal' Q.isPGroup' hPQ').symm)

theorem exists_smul_eq_of_card_sylow (hK : IsBenderGroup K) (Q : Sylow 2 K)
    (hcard : Nat.card (Sylow 2 K) = Nat.card (Q : Subgroup K) + 1) {P₁ P₂ : Sylow 2 K}
    (h₁ : P₁ ≠ Q) (h₂ : P₂ ≠ Q) : ∃ u ∈ (Q : Subgroup K), u • P₁ = P₂ := by
  have hQN : ∀ u ∈ (Q : Subgroup K), u • Q = Q := fun u hu =>
    Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hu)
  let F : Option (Q : Subgroup K) → Sylow 2 K := fun x => match x with
    | none => Q
    | some u => (u : K) • P₁
  have hF : Function.Injective F := by
    intro x y hxy
    rcases x with _ | u <;> rcases y with _ | v
    · rfl
    · exfalso
      have h : Q = (v : K) • P₁ := hxy
      apply h₁
      rw [← inv_smul_eq_iff.2 h]
      exact hQN _ (inv_mem v.2)
    · exfalso
      have h : Q = (u : K) • P₁ := hxy.symm
      apply h₁
      rw [← inv_smul_eq_iff.2 h]
      exact hQN _ (inv_mem u.2)
    · have h : (u : K) • P₁ = (v : K) • P₁ := hxy
      have hN : (u : K)⁻¹ * v ∈ Subgroup.normalizer ((P₁ : Subgroup K) : Set K) :=
        sylow_smul_eq_smul_iff.1 h
      have hQ : (u : K)⁻¹ * v ∈ (Q : Subgroup K) := mul_mem (inv_mem u.2) v.2
      have hP : (u : K)⁻¹ * v ∈ (P₁ : Subgroup K) :=
        le_of_isPGroup_of_le_normalizer (Q.isPGroup'.to_le
          (Subgroup.zpowers_le.2 hQ)) P₁ (Subgroup.zpowers_le.2 hN) (Subgroup.mem_zpowers _)
      have h1 : (u : K)⁻¹ * v = 1 := by
        have := sylow_inf_eq_bot hK h₁
        rw [eq_bot_iff] at this
        exact this ⟨hP, hQ⟩
      rw [inv_mul_eq_one] at h1
      exact congrArg some (Subtype.ext h1)
  have hbij : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨hF, by rw [Finite.card_option, hcard]⟩
  obtain ⟨x, hx⟩ := hbij.2 P₂
  rcases x with _ | u
  · exact absurd hx.symm h₂
  · exact ⟨u, u.2, hx⟩

theorem conjTwoTransitive_of_normalizer_eq (hK : IsBenderGroup K) (Q : Sylow 2 K)
    (hcard : Nat.card (Sylow 2 K) = Nat.card (Q : Subgroup K) + 1) {T : Subgroup K}
    (hN : Subgroup.normalizer (T : Set K) = Subgroup.normalizer ((Q : Subgroup K) : Set K)) :
    ConjTwoTransitive K T := by
  have key : ∀ g h : K, conjSubgroup g T = conjSubgroup h T ↔ g • Q = h • Q := fun g h => by
    rw [conjSubgroup_eq_conjSubgroup_iff, hN, sylow_smul_eq_smul_iff]
  intro a b c d hab hcd
  have h₁ : (a⁻¹ * b) • Q ≠ Q := by
    intro h
    apply hab
    rw [key, mul_smul, inv_smul_eq_iff] at *
    exact h.symm
  have h₂ : (c⁻¹ * d) • Q ≠ Q := by
    intro h
    apply hcd
    rw [key, mul_smul, inv_smul_eq_iff] at *
    exact h.symm
  obtain ⟨u, huQ, hu⟩ := exists_smul_eq_of_card_sylow hK Q hcard h₁ h₂
  have huQ' : u • Q = Q := Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer huQ)
  refine ⟨c * u * a⁻¹, (key _ _).2 ?_, (key _ _).2 ?_⟩
  · rw [inv_mul_cancel_right, mul_smul, huQ']
  · rw [show c * u * a⁻¹ * b = c * (u * (a⁻¹ * b)) by group, mul_smul, mul_smul, hu, ← mul_smul,
      mul_inv_cancel_left]

end Sylow

section Main

variable {K : Type} [Group K] [Finite K]

theorem bender_wc (hK : IsBenderGroup K) {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hsyl : Nat.card (Sylow 2 K) = q ^ k + 1)
    {T : Subgroup K} (hT : IsWC T) (hT1 : T ≠ ⊥) :
    (Nat.card T = q ∧
      (∃ S : Sylow 2 K, T = (Subgroup.center (S : Subgroup K)).map (S : Subgroup K).subtype) ∧
      BorelTwoTransitive K T) ∧
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set K), g * x * g⁻¹ = y := by
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  obtain ⟨⟨x, hxT⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hcomm : ∀ t ∈ T, ∀ y ∈ (Q : Subgroup K), Commute y t := fun t ht y hy =>
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q (hTQ ht)
      (elemAbelian_mul_self hT.1 ht) y hy).symm
  have hxc : x ∈ (Q : Subgroup K) ∧ ∀ y ∈ (Q : Subgroup K), Commute y x :=
    ⟨hTQ hxT, hcomm x hxT⟩
  have hiff : ∀ z, z ∈ T ↔ z ∈ (Q : Subgroup K) ∧ ∀ y ∈ (Q : Subgroup K), Commute y z := by
    intro z
    refine ⟨fun hz => ⟨hTQ hz, hcomm z hz⟩, fun hz => ?_⟩
    rcases eq_or_ne z 1 with rfl | hz1
    · exact T.one_mem
    obtain ⟨g, hgN, hg⟩ :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hK Q hxc hx1 hz hz1
    have hconj : conjSubgroup g T = T := by
      refine (hT.2 x hxT hx1).2 g fun w hw => ?_
      have hwQ : w ∈ (Q : Subgroup K) := by
        rw [mem_conjSubgroup] at hw
        have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 (hTQ hw)
        rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hxc.2 w hwQ).eq
    rw [← hconj, mem_conjSubgroup, ← hg]
    simpa [mul_assoc] using hxT
  have hTeq : T = (Subgroup.center (Q : Subgroup K)).map (Q : Subgroup K).subtype := by
    ext z
    rw [hiff z]
    constructor
    · rintro ⟨hzQ, hzc⟩
      exact ⟨⟨z, hzQ⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).eq, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun w hw => congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨w, hw⟩)⟩
  have hNle : Subgroup.normalizer ((Q : Subgroup K) : Set K) ≤ Subgroup.normalizer (T : Set K) :=
    fun g hg => mem_normalizer_of_eq_center' hiff hg
  have hNge : Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    intro g hg
    have hgx : g * x * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hg x).1 hxT
    have hgx1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h]
      group
    have hle : conjSubgroup g (Q : Subgroup K) ≤
        Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
      intro w hw
      apply centralizer_le_normalizer_of_isBenderGroup hK Q (hTQ hgx)
        (elemAbelian_mul_self hT.1 hgx) hgx1
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [mem_conjSubgroup] at hw
      have hu := hxc.2 _ hw
      calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [hu.eq]
        _ = g * x * g⁻¹ * w := by group
    have hQg : conjSubgroup g (Q : Subgroup K) ≤ (Q : Subgroup K) :=
      le_of_isPGroup_of_le_normalizer (Q.isPGroup'.map _) Q hle
    exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hQg)
  have hN : Subgroup.normalizer (T : Set K) = Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
    le_antisymm hNge hNle
  have hcard : Nat.card (Sylow 2 K) = Nat.card (Q : Subgroup K) + 1 := by
    rw [hsyl, (hB Q).2.2.2.2]
  refine ⟨⟨?_, ⟨Q, hTeq⟩, conjTwoTransitive_of_normalizer_eq hK Q hcard hN, Q, hN⟩, ?_⟩
  · rw [hTeq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), (hB Q).2.2.2.1]
  · intro y hy hy1 z hz hz1
    obtain ⟨g, hgN, hg⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hK Q
      ((hiff y).1 hy) hy1 ((hiff z).1 hz) hz1
    exact ⟨g, hNle hgN, hg⟩

end Main


end CFSG.CGT.Timmesfeld75

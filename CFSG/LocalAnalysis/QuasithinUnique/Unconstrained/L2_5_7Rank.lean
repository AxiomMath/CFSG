module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L257

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_sup_zpowers {p : ℕ} {P₀ : Subgroup G} (hP₀ : IsElemAbelian p P₀) {y : G}
    (hy : y ^ p = 1) (hcomm : ∀ a ∈ P₀, a * y = y * a) :
    IsElemAbelian p (P₀ ⊔ Subgroup.zpowers y) := by
  have hAB : ∀ a ∈ P₀, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (hcomm a ha) i).eq)
  have hbb : ∀ b ∈ Subgroup.zpowers y, ∀ b' ∈ Subgroup.zpowers y, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact (Commute.zpow_zpow_self y i j).eq
  have haa : ∀ a ∈ P₀, ∀ a' ∈ P₀, a * a' = a' * a := fun a ha a' ha' => by
    have := hP₀.1
    exact setLike_mul_comm ha ha'
  refine ⟨⟨⟨fun x x' => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := mem_sup_of_commute hAB x.2
    obtain ⟨a', ha', b', hb', hx'⟩ := mem_sup_of_commute hAB x'.2
    apply Subtype.ext
    show (x : G) * x' = x' * x
    rw [← hx, ← hx']
    have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
        _ = (a * a') * (b * b') := by group
    have e2 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [← hAB a ha b' hb']
        _ = (a' * a) * (b' * b) := by group
    rw [e1, e2, haa a ha a' ha', hbb b hb b' hb']
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a (y ^ i) := hAB a ha _ hb
    have hpow : (y ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
    rw [hc.mul_pow, hP₀.2 a ha, hpow, one_mul]

theorem card_sup_zpowers {p : ℕ} (hp : p.Prime) {P₀ : Subgroup G} (hcard : Nat.card P₀ = p ^ 2)
    {y : G} (hyo : orderOf y = p) (hcomm : ∀ a ∈ P₀, a * y = y * a) (hyP : y ∉ P₀) :
    Nat.card ↥(P₀ ⊔ Subgroup.zpowers y) = p ^ 3 := by
  have hAB : ∀ a ∈ P₀, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (hcomm a ha) i).eq)
  have h := B2F.card_sup_mul_card_inf_of_commute (A := P₀) (B := Subgroup.zpowers y) hAB
  have hz : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyo]
  have hinf : P₀ ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(P₀ ⊓ Subgroup.zpowers y) ∣ p := hz ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : P₀ ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hz])
      have hy' : y ∈ P₀ ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hyP hy'.1
  rw [hinf, Subgroup.card_bot, hz, hcard, mul_one] at h
  rw [h]
  ring

theorem cube_contradiction (he : CFSG.Assembly.evenRank G ≤ 2) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P₀ : Subgroup G}
    (hP₀ : IsElemAbelian p P₀) (hcard : Nat.card P₀ = p ^ 2) (hP₀H : P₀ ≤ H) {y : G} (hyH : y ∈ H)
    (hyo : orderOf y = p) (hcomm : ∀ a ∈ P₀, a * y = y * a) (hyP : y ∉ P₀) : False := by
  have hy : y ^ p = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  refine Unc25G2.false_of_isElemAbelian_card_cube he hH
    (sup_le hP₀H (Subgroup.zpowers_le.mpr hyH)) hp hp2
    (isElemAbelian_sup_zpowers hP₀ hy hcomm) (card_sup_zpowers hp hcard hyo hcomm hyP)

end L257

end CFSG.QuasithinUnique

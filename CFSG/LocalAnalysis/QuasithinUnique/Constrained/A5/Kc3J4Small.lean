module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.A5.Kc3J4

open CFSG.Open

variable {G : Type*} [Group G]

theorem pow_centralizer_of_orderOf_five [Finite G] {W : Subgroup G} (hW : IsPGroup 2 W)
    (hcard : Nat.card W ≤ 8) {x : G} (hx : orderOf x = 5)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) : x ∈ Subgroup.centralizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let c : ↥(Subgroup.zpowers x) →* MulAut ↥W :=
    (W.normalizerMonoidHom).comp (Subgroup.inclusion ((Subgroup.zpowers_le).2 hxW))
  let _ : MulAction ↥(Subgroup.zpowers x) ↥W := MulAction.compHom ↥W c
  have hP : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    norm_num
  have hmod : Nat.card ↥W ≡ Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥W) [MOD 5] :=
    hP.card_modEq_card_fixedPoints ↥W
  set F : Subgroup G := W ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hsmul : ∀ (s : ↥(Subgroup.zpowers x)) (w : ↥W),
      (((s • w : ↥W)) : G) = (s : G) * (w : G) * (s : G)⁻¹ := fun s w => by
    show ((c s) w : G) = _
    simp [c]
  have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥W) = Nat.card F := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun w => ⟨(w.1 : G), w.1.2, ?_⟩
        invFun := fun y => ⟨⟨(y : G), y.2.1⟩, ?_⟩
        left_inv := fun w => by rfl
        right_inv := fun y => by rfl }
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h := w.2 ⟨x, Subgroup.mem_zpowers x⟩
      have := congrArg (fun z : W => (z : G)) h
      rw [hsmul] at this
      simp only at this
      calc (w.1 : G) * x = ((x * w.1 * x⁻¹) * x) := by rw [this]
        _ = x * (w.1 : G) := by group
    · intro s
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 s.2
      show s • (⟨(y : G), y.2.1⟩ : W) = ⟨(y : G), y.2.1⟩
      apply Subtype.ext
      rw [hsmul, ← hk]
      have h1 : x * (y : G) = (y : G) * x :=
        (Subgroup.mem_centralizer_singleton_iff.1 y.2.2).symm
      have h2 : (y : G) * x ^ k = x ^ k * (y : G) := by
        have hc : Commute (y : G) x := h1.symm
        exact (hc.zpow_right k).eq
      calc x ^ k * (y : G) * (x ^ k)⁻¹ = ((y : G) * x ^ k) * (x ^ k)⁻¹ := by rw [h2]
        _ = (y : G) := by group
  rw [hfix] at hmod
  have hFW : F ≤ W := inf_le_left
  have hdvd : Nat.card F ∣ Nat.card W := Subgroup.card_dvd_of_le hFW
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hW)
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hk ▸ hdvd)
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjk' : j = k := by
    have h1 : 2 ^ k % 5 = 2 ^ j % 5 := by
      have := hmod
      rw [hk, hj] at this
      exact this
    have key : ∀ k : Fin 4, ∀ j : Fin 4, j.val ≤ k.val → 2 ^ k.val % 5 = 2 ^ j.val % 5 →
        j.val = k.val := by decide
    exact key ⟨k, by omega⟩ ⟨j, by omega⟩ hjle h1
  have hFeq : Nat.card F = Nat.card W := by rw [hj, hk, hjk']
  have hFtop : F = W := Subgroup.eq_of_le_of_card_ge hFW (by rw [hFeq])
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  have hwF : w ∈ F := by rw [hFtop]; exact hw
  exact Subgroup.mem_centralizer_singleton_iff.1 hwF.2

end CFSG.QuasithinUnique.A5.Kc3J4

module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Sec5NineGen
public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.T75I.AltRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem card_le_four_of_hatA {k : ℕ} (hk : k = 6 ∨ k = 7) {Y : Type} [Group Y]
    (hY : IsHatA k Y) {E : Subgroup Y} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  obtain ⟨-, Z, -, hZcard, hZn, ⟨φ⟩⟩ := hY
  let f : Y →* alternatingGroup (Fin k) := φ.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : f.ker = Z := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff φ φ.injective]
    exact QuotientGroup.eq_one_iff x
  have hEZ : E ⊓ f.ker = ⊥ := by
    rw [hker, eq_bot_iff]
    rintro x ⟨hxE, hxZ⟩
    have hx2 : x ^ 2 = 1 := hE.2 x hxE
    have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hd3 : orderOf x ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard Z hxZ).trans hZcard
    have hd1 : orderOf x ∣ 1 := by
      have := Nat.dvd_gcd hd2 hd3
      simpa using this
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd1))
  have hcard := card_map_eq_of_inf_ker_eq_bot f hEZ
  have hel : IsElemAbelian 2 (E.map f) := isElemAbelian_map_of_hom hE f
  have hk7 : k ≤ 7 := by omega
  rw [← hcard]
  exact card_le_four_of_alt hk7 (fun x hx => by simpa [pow_two] using hel.2 x hx)

theorem isElemAbelian_comap_subtype {G : Type*} [Group G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (H : Subgroup G) : IsElemAbelian 2 (A.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hA H

theorem ctx_of_hat (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    {G : Type} [Group G] {T T₁ : Subgroup G} (hy : StepHyp T T₁) (h16 : Nat.card T = 16)
    (hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal)
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    Sec6Ctx T T₁ 2 2 := by
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hS3 : Sec3 T T₁ := hP.sec3 hS
  obtain ⟨m, r, hm, hr, hq, hT⟩ := step511_card h214 hInv hIso hy
  have h4 : m * (r + 1) = 4 := by
    have h : (2 : ℕ) ^ (m * (r + 1)) = 2 ^ 4 := by
      rw [pow_mul, ← hT, h16]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h
  have hmr : (m = 1 ∧ r = 3) ∨ (m = 2 ∧ r = 1) := by
    have hm4 : m ∣ 4 := ⟨r + 1, h4.symm⟩
    have : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m <;> omega
  rcases hmr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    have hLdvd : Nat.card (normIn T T₁) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le (normIn_le T T₁)
    have hL8 : Nat.card (normIn T T₁) = 8 := by
      have h1 := Nat.div_mul_cancel hLdvd
      rw [hq, h16] at h1
      omega
    have hL₁8 : Nat.card (normIn T₁ T) = 8 := hS3.card_normIn_swap.trans hL8
    set H := hSub T (normIn T₁ T) with hH
    have hL₁H : normIn T₁ T ≤ H := le_hSub
    have hT₁ : IsElemAbelian 2 T₁ := hS3.cfg.wc₁.1
    have hL₁el : IsElemAbelian 2 (normIn T₁ T) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hT₁.2 x (normIn_le _ _ hx)⟩
      apply Subtype.ext
      exact elemAbelian_mul_comm hT₁ (normIn_le _ _ a.2) (normIn_le _ _ b.2)
    set A : Subgroup ↥H := (normIn T₁ T).subgroupOf H with hA
    have hAel : IsElemAbelian 2 A := isElemAbelian_comap_subtype hL₁el H
    have hAcard : Nat.card A = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁H).toEquiv, hL₁8]
    let ψ : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
    have hAker : A ⊓ ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxA, hxk⟩
      have hxT : (x : G) ∈ T := by
        have : x ∈ T.subgroupOf H := by simpa [ψ] using hxk
        exact Subgroup.mem_subgroupOf.1 this
      have hxL : (x : G) ∈ normIn T₁ T := Subgroup.mem_subgroupOf.1 hxA
      have hxT₁ : (x : G) ∈ T₁ := normIn_le _ _ hxL
      have hinf : (x : G) ∈ T ⊓ T₁ := ⟨hxT, hxT₁⟩
      rw [hS3.cfg.inf, Subgroup.mem_bot] at hinf
      exact Subgroup.mem_bot.2 (Subtype.ext hinf)
    have hEcard := card_map_eq_of_inf_ker_eq_bot ψ hAker
    have hEel : IsElemAbelian 2 (A.map ψ) := isElemAbelian_map_of_hom hAel ψ
    have hle : Nat.card (A.map ψ) ≤ 4 := by
      rcases hhat with h | h
      · exact card_le_four_of_hatA (Or.inl rfl) h hEel
      · exact card_le_four_of_hatA (Or.inr rfl) h hEel
    omega
  · exact ⟨hy, hS, hI, hq, hT, Or.inr (Or.inr ⟨h16, hnorm, hhat⟩)⟩

end CFSG.CGT.T75I

module

public import Mathlib.GroupTheory.SchurZassenhaus
import CFSG.StronglyEmbedded.SteinbergCDOddOrderStableActions
import CFSG.GroupTheory.SolvableMinimalNormalNode

public section

namespace CFSG.CGT.PushingUpLit.CGT6

structure SevenData (X : Type) [Group X] (Y : Subgroup X) : Prop where
  ycard : Nat.card ↥Y = 3
  gen : ∀ N : Subgroup X, N.Normal → Y ≤ N → N = ⊤
  pair : ∀ g : X, Nat.card ↥(Y ⊔ Y.map (MulAut.conj g).toMonoidHom) ∣ 315

theorem disjoint_of_card_three {X : Type} [Group X] [Finite X] {Y N : Subgroup X}
    (hY : Nat.card ↥Y = 3) (hYN : ¬ Y ≤ N) : Disjoint Y N := by
  rw [Subgroup.disjoint_def]
  intro x hxY hxN
  by_contra hx
  have h1 : Nat.card ↥(Y ⊓ N) ∣ 3 := hY ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(Y ⊓ N) ≠ 1 := by
    intro h
    have := Subgroup.card_eq_one.mp h
    exact hx (by simpa using (Subgroup.mem_bot.mp (this ▸ (Subgroup.mem_inf.mpr ⟨hxY, hxN⟩))))
  have h3 : Nat.card ↥(Y ⊓ N) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd h h2
    · exact h
  have : Y ⊓ N = Y := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [h3, hY]
  exact hYN (this ▸ inf_le_right)

namespace SevenData

variable {X : Type} [Group X] {Y : Subgroup X}

theorem quotient [Finite X] (h : SevenData X Y) (N : Subgroup X) [N.Normal] (hYN : Disjoint Y N) :
    SevenData (X ⧸ N) (Y.map (QuotientGroup.mk' N)) where
  ycard := by
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp Y.subtype) := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have hyN : (y : X) ∈ N := (QuotientGroup.eq_one_iff _).mp (by simpa using hy)
      exact Subtype.ext (Subgroup.disjoint_def.mp hYN y.2 hyN)
    have hrange : ((QuotientGroup.mk' N).comp Y.subtype).range = Y.map (QuotientGroup.mk' N) := by
      ext q
      simp [MonoidHom.mem_range, Subgroup.mem_map]
    rw [← h.ycard, ← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  gen := by
    intro M hM hYM
    have hcomap : M.comap (QuotientGroup.mk' N) = ⊤ := by
      apply h.gen
      · exact hM.comap _
      · intro y hy
        exact hYM ⟨y, hy, rfl⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have : x ∈ M.comap (QuotientGroup.mk' N) := by rw [hcomap]; exact Subgroup.mem_top x
    exact this
  pair := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hcomp : ((MulAut.conj (g : X ⧸ N)).toMonoidHom).comp (QuotientGroup.mk' N) =
        (QuotientGroup.mk' N).comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp
    have h1 : (Y.map (QuotientGroup.mk' N)) ⊔
        (Y.map (QuotientGroup.mk' N)).map (MulAut.conj (g : X ⧸ N)).toMonoidHom =
        (Y ⊔ Y.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) := by
      rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, hcomp]
    rw [h1]
    exact (Subgroup.card_map_dvd _ _).trans (h.pair g)

end SevenData

theorem commute_of_isPGroup_three_of_card_dvd {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (h3 : IsPGroup 3 ↥H) (hd : Nat.card ↥H ∣ 315) : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    have h27 : 3 ^ 3 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    rw [← hk] at h27
    have := h27.trans hd
    omega
  have hcomm : ∀ a b : H, a * b = b * a := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    interval_cases k
    · intro a b
      have : Nat.card H = 1 := by simpa using hk
      have h1 : Subsingleton H := (Nat.card_eq_one_iff_unique.mp this).1
      exact Subsingleton.elim _ _
    · have hp : Nat.card H = 3 := by simpa using hk
      have : IsCyclic H := isCyclic_of_prime_card hp
      exact fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b
    · have hp : Nat.card H = 3 ^ 2 := hk
      have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hp
      exact fun a b => this.is_comm.comm a b
  intro a ha b hb
  have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

open CFSG.GroupTheory in
theorem central_of_three {X : Type} [Group X] [Finite X] (hodd : Odd (Nat.card X)) {Y : Subgroup X}
    (h : SevenData X Y) {N : Subgroup X} [hN : N.Normal]
    (hNmin : ∀ M : Subgroup X, M.Normal → M ≠ ⊥ → M ≤ N → M = N) {d : ℕ} (hd : 1 ≤ d)
    (hNcard : Nat.card ↥N = 3 ^ d) : ∀ n ∈ N, ∀ x : X, x * n = n * x := by
  classical
  have hNp : IsPGroup 3 ↥N := IsPGroup.of_card hNcard
  have hYp : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by simpa using h.ycard)
  have ha : ∀ n ∈ N, ∀ y ∈ Y, y * (n * y * n⁻¹) = (n * y * n⁻¹) * y := by
    intro n hn y hy
    set H : Subgroup X := Y ⊔ Y.map (MulAut.conj n).toMonoidHom with hH
    have hHle : H ≤ Y ⊔ N := by
      refine sup_le le_sup_left ?_
      rintro _ ⟨y', hy', rfl⟩
      have h1 : n * (y' * n⁻¹ * y'⁻¹) ∈ N := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) y')
      have h2 : n * (y' * n⁻¹ * y'⁻¹) * y' ∈ N ⊔ Y := Subgroup.mul_mem_sup h1 hy'
      rw [sup_comm] at h2
      have h3 : n * (y' * n⁻¹ * y'⁻¹) * y' = (MulAut.conj n).toMonoidHom y' := by
        simp [MulAut.conj_apply]
        group
      rwa [h3] at h2
    have hH3 : IsPGroup 3 ↥H := (hYp.to_sup_of_normal_right hNp).to_le hHle
    have hcomm := commute_of_isPGroup_three_of_card_dvd hH3 (h.pair n)
    exact hcomm y (Subgroup.mem_sup_left hy) _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
  set ρ : X →* MulAut ↥N := MulAut.conjNormal with hρ
  have hρapply : ∀ (x : X) (u : ↥N), ((ρ x u : ↥N) : X) = x * u * x⁻¹ := fun x u =>
    MulAut.conjNormal_apply x u
  have hst : IsPStableAction 3 ρ :=
    CFSG.StronglyEmbedded.odd_order_stable_actions Nat.prime_three (by decide) hodd hNp ρ
  have hfix : ∀ y ∈ Y, ∀ u : ↥N, ρ y⁻¹ (u⁻¹ * ρ y⁻¹ u) = u⁻¹ * ρ y⁻¹ u := by
    intro y hy u
    apply Subtype.ext
    have hc : Commute y ((u : X)⁻¹ * y * (u : X)⁻¹⁻¹) := by
      have := ha ((u : X)⁻¹) (N.inv_mem u.2) y hy
      exact this
    have e1 : ((ρ y⁻¹ (u⁻¹ * ρ y⁻¹ u) : ↥N) : X) =
        y⁻¹ * ((u : X)⁻¹ * (y⁻¹ * (u : X) * y)) * y := by
      rw [hρapply, Subgroup.coe_mul, Subgroup.coe_inv, hρapply]
      simp [mul_assoc]
    have e2 : ((u⁻¹ * ρ y⁻¹ u : ↥N) : X) = (u : X)⁻¹ * (y⁻¹ * (u : X) * y) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hρapply]
      simp [mul_assoc]
    rw [e1, e2]
    have hc2 : Commute y ((u : X)⁻¹ * (y⁻¹ * (u : X) * y)) := by
      have h1 : Commute y (((u : X)⁻¹ * y * (u : X)⁻¹⁻¹)⁻¹ * y) :=
        (hc.inv_right).mul_right (Commute.refl y)
      have h2 : ((u : X)⁻¹ * y * (u : X)⁻¹⁻¹)⁻¹ * y = (u : X)⁻¹ * (y⁻¹ * (u : X) * y) := by
        group
      rwa [h2] at h1
    calc y⁻¹ * ((u : X)⁻¹ * (y⁻¹ * (u : X) * y)) * y
        = y⁻¹ * (y * ((u : X)⁻¹ * (y⁻¹ * (u : X) * y))) := by rw [hc2.eq]; group
      _ = (u : X)⁻¹ * (y⁻¹ * (u : X) * y) := by group
  have hQker : ∀ x ∈ actionPCore 3 ρ, ρ x = 1 := by
    intro x hx
    set Q : Subgroup X := actionPCore 3 ρ with hQ
    have hQn : Q.Normal := by
      have : (CFSG.pCore 3 (X ⧸ ρ.ker)).Normal := inferInstance
      exact this.comap _
    have hΓ : IsPGroup 3 ↥(Q.map ρ) := by
      rintro ⟨g, hg⟩
      obtain ⟨q, hq, rfl⟩ := hg
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := X ⧸ ρ.ker))
        ⟨QuotientGroup.mk' ρ.ker q, hq⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : q ^ 3 ^ k ∈ ρ.ker := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact congrArg Subtype.val hk
      have h2 : ρ (q ^ 3 ^ k) = 1 := h1
      simpa using h2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmod := hΓ.card_modEq_card_fixedPoints ↥N
    have hdvd : 3 ∣ Nat.card ↥N := by
      rw [hNcard]
      exact dvd_pow_self 3 (by omega)
    have hfixdvd : 3 ∣ Nat.card ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N) :=
      (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
    have hone : (1 : ↥N) ∈ MulAction.fixedPoints ↥(Q.map ρ) ↥N := fun g => by simp
    have hpos : 0 < Nat.card ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N) := by
      have : Nonempty ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N) := ⟨⟨1, hone⟩⟩
      exact Nat.card_pos
    have hge : 3 ≤ Nat.card ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N) :=
      Nat.le_of_dvd hpos hfixdvd
    have hnt : Nontrivial ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨b, hb⟩ := exists_ne (⟨1, hone⟩ : ↥(MulAction.fixedPoints ↥(Q.map ρ) ↥N))
    set n₀ : ↥N := b.1 with hn₀
    have hn₀1 : n₀ ≠ 1 := by
      intro h1
      exact hb (Subtype.ext h1)
    have hn₀fix : ∀ q ∈ Q, (q : X) * (n₀ : X) * (q : X)⁻¹ = (n₀ : X) := by
      intro q hq
      have h1 := b.2 ⟨ρ q, Subgroup.mem_map_of_mem ρ hq⟩
      have h2 : ρ q n₀ = n₀ := h1
      have h3 := congrArg (fun u : ↥N => (u : X)) h2
      simpa [hρapply] using h3
    set M : Subgroup X := N ⊓ Subgroup.centralizer (Q : Set X) with hM
    have hMn : M.Normal := by
      have : (Subgroup.centralizer (Q : Set X)).Normal := Subgroup.normal_centralizer
      exact Subgroup.normal_inf_normal N _
    have hMbot : M ≠ ⊥ := by
      intro hbot
      have hmem : (n₀ : X) ∈ M := by
        refine Subgroup.mem_inf.mpr ⟨n₀.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro q hq
        have := hn₀fix q hq
        calc (q : X) * (n₀ : X) = ((q : X) * (n₀ : X) * (q : X)⁻¹) * q := by group
          _ = (n₀ : X) * q := by rw [this]
      rw [hbot] at hmem
      exact hn₀1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    have hMN : M = N := hNmin M hMn hMbot inf_le_left
    have hcent : ∀ u : ↥N, (x : X) * (u : X) = (u : X) * x := by
      intro u
      have hu : (u : X) ∈ M := by rw [hMN]; exact u.2
      exact Subgroup.mem_centralizer_iff.mp hu.2 x hx
    ext u
    rw [hρapply, hcent u]
    simp
  have hYcent : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y := by
    intro y hy n hn
    have hy1 : y ∈ actionPCore 3 ρ :=
      hst y (fun u => (double_commutator_eq_one_iff ρ u y).mpr (hfix y hy u))
    have h1 := hQker y hy1
    have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : X)) h1
    simp only [hρapply, MulAut.one_apply] at h2
    calc y * n = (y * n * y⁻¹) * y := by group
      _ = n * y := by rw [h2]
  have hcen : (Subgroup.centralizer (N : Set X)) = ⊤ := by
    have : (Subgroup.centralizer (N : Set X)).Normal := Subgroup.normal_centralizer
    refine h.gen _ this (fun y hy => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hYcent y hy n hn).symm
  intro n hn x
  have hx : x ∈ Subgroup.centralizer (N : Set X) := by rw [hcen]; exact Subgroup.mem_top x
  exact (Subgroup.mem_centralizer_iff.mp hx n hn).symm

theorem mem_normalizer_of_conj_mem_aux {X : Type*} [Group X] {A : Subgroup X} {g : X}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (h' : ∀ x ∈ A, g⁻¹ * x * g ∈ A) :
    g ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

theorem prime_dvd_315 {r : ℕ} (hr : r.Prime) (hd : r ∣ 315) : r = 3 ∨ r = 5 ∨ r = 7 := by
  have h : r ∣ 3 * 3 * 5 * 7 := by simpa using hd
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h1))

theorem central_of_other_prime {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (h : SevenData X Y) {N : Subgroup X} [hN : N.Normal] {r d : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hr7 : r ≠ 7) (hNcard : Nat.card ↥N = r ^ d) : ∀ n ∈ N, ∀ x : X, x * n = n * x := by
  classical
  have hy3 : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ^ Nat.card ↥Y = 1 := pow_card_eq_one'
    rw [h.ycard] at this
    simpa using congrArg Subtype.val this
  have hmain : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y := by
    intro y hy n hn
    set H : Subgroup X := Y ⊔ Y.map (MulAut.conj n).toMonoidHom with hH
    have hHcard : Nat.card ↥H ∣ 315 := h.pair n
    have hyH : y ∈ H := Subgroup.mem_sup_left hy
    have hzdef : (MulAut.conj n).toMonoidHom y = n * y * n⁻¹ := by simp [MulAut.conj_apply]
    have hzH : n * y * n⁻¹ ∈ H := by
      rw [← hzdef]
      exact Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    set c : X := n * y * n⁻¹ * y⁻¹ with hc
    have hcN : c ∈ N := by
      have : c = n * (y * n⁻¹ * y⁻¹) := by rw [hc]; group
      rw [this]
      exact N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) y)
    have hcH : c ∈ H := H.mul_mem hzH (H.inv_mem hyH)
    have hc1 : c = 1 := by
      have hord1 : orderOf c ∣ Nat.card ↥H := Subgroup.orderOf_dvd_natCard H hcH
      have hord2 : orderOf c ∣ r ^ d := hNcard ▸ Subgroup.orderOf_dvd_natCard N hcN
      by_cases hr5 : r = 5
      · subst hr5
        set A : Subgroup X := H ⊓ N with hA
        have hAc : c ∈ A := Subgroup.mem_inf.mpr ⟨hcH, hcN⟩
        have hAcard1 : Nat.card ↥A ∣ 315 := (Subgroup.card_dvd_of_le inf_le_left).trans hHcard
        have hAcard2 : Nat.card ↥A ∣ 5 ^ d := hNcard ▸ Subgroup.card_dvd_of_le inf_le_right
        obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hAcard2
        have ha1 : a ≤ 1 := by
          by_contra hlt
          have h25 : 5 ^ 2 ∣ 5 ^ a := Nat.pow_dvd_pow 5 (by omega)
          rw [← ha] at h25
          have := h25.trans hAcard1
          omega
        by_cases ha0 : a = 0
        ·
          have hA1 : Nat.card ↥A = 1 := by rw [ha, ha0]; simp
          have := Subgroup.card_eq_one.mp hA1
          have hcA : c ∈ (⊥ : Subgroup X) := this ▸ hAc
          exact Subgroup.mem_bot.mp hcA
        ·
          have ha1' : a = 1 := by omega
          have hA5 : Nat.card ↥A = 5 := by rw [ha, ha1']; simp
          have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
          have hcyc : IsCyclic ↥A := isCyclic_of_prime_card hA5
          have hynorm : y ∈ Subgroup.normalizer (A : Set X) := by
            refine mem_normalizer_of_conj_mem_aux (fun x hx => ?_) (fun x hx => ?_)
            · exact Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hyH (Subgroup.mem_inf.mp hx).1)
                (H.inv_mem hyH), hN.conj_mem x (Subgroup.mem_inf.mp hx).2 y⟩
            · exact Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hyH)
                (Subgroup.mem_inf.mp hx).1) hyH, by
                  have := hN.conj_mem x (Subgroup.mem_inf.mp hx).2 y⁻¹
                  simpa using this⟩
          set α : MulAut ↥A := A.normalizerMonoidHom ⟨y, hynorm⟩ with hα
          have hα3 : α ^ 3 = 1 := by
            rw [hα, ← map_pow]
            have : (⟨y, hynorm⟩ : Subgroup.normalizer (A : Set X)) ^ 3 = 1 :=
              Subtype.ext (by simpa using hy3 y hy)
            rw [this, map_one]
          have hαcard : Nat.card (MulAut ↥A) = 4 := by
            rw [IsCyclic.card_mulAut, hA5]
            decide
          have hαord : orderOf α ∣ Nat.gcd 3 4 :=
            Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hα3) (hαcard ▸ orderOf_dvd_natCard α)
          have hα1 : α = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hαord))
          have hcomm : y * c * y⁻¹ = c := by
            have := congrArg (fun φ : MulAut ↥A => ((φ ⟨c, hAc⟩ : ↥A) : X)) hα1
            simpa [hα] using this
          have hyc : Commute y c := by
            have : y * c = c * y := by
              calc y * c = (y * c * y⁻¹) * y := by group
                _ = c * y := by rw [hcomm]
            exact this
          have hz3 : (n * y * n⁻¹) ^ 3 = 1 := by
            have : (n * y * n⁻¹) ^ 3 = n * y ^ 3 * n⁻¹ := conj_pow
            rw [this, hy3 y hy]
            group
          have hcy : n * y * n⁻¹ = c * y := by rw [hc]; group
          have hc3 : c ^ 3 = 1 := by
            have h1 : (c * y) ^ 3 = c ^ 3 * y ^ 3 := (hyc.symm).mul_pow 3
            rw [← hcy, hz3, hy3 y hy, mul_one] at h1
            exact h1.symm
          have hord5 : orderOf c ∣ 5 := hA5 ▸ Subgroup.orderOf_dvd_natCard A hAc
          have hord3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
          have : orderOf c ∣ Nat.gcd 5 3 := Nat.dvd_gcd hord5 hord3
          exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using this))
      ·
        have hrnd : ¬ r ∣ 315 := by
          intro hd
          rcases prime_dvd_315 hr hd with h3 | h5 | h7
          · exact hr3 h3
          · exact hr5 h5
          · exact hr7 h7
        have hcop : Nat.Coprime (Nat.card ↥H) (r ^ d) := by
          apply Nat.Coprime.pow_right
          exact (Nat.Prime.coprime_iff_not_dvd hr).mpr (fun hd => hrnd (hd.trans hHcard)) |>.symm
        have : orderOf c ∣ Nat.gcd (Nat.card ↥H) (r ^ d) := Nat.dvd_gcd hord1 hord2
        rw [hcop] at this
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
    have hz : n * y * n⁻¹ = y := by
      have : n * y * n⁻¹ * y⁻¹ = 1 := hc1
      calc n * y * n⁻¹ = (n * y * n⁻¹ * y⁻¹) * y := by group
        _ = y := by rw [this, one_mul]
    calc y * n = (n * y * n⁻¹) * n := by rw [hz]
      _ = n * y := by group
  have hcen : (Subgroup.centralizer (N : Set X)) = ⊤ := by
    have : (Subgroup.centralizer (N : Set X)).Normal := Subgroup.normal_centralizer
    refine h.gen _ this (fun y hy => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hmain y hy n hn).symm
  intro n hn x
  have hx : x ∈ Subgroup.centralizer (N : Set X) := by rw [hcen]; exact Subgroup.mem_top x
  exact (Subgroup.mem_centralizer_iff.mp hx n hn).symm

theorem comap_quotient_facts {X : Type} [Group X] [Finite X] {Y N : Subgroup X} [hN : N.Normal]
    {Rb : Subgroup (X ⧸ N)} (hYR : Y.map (QuotientGroup.mk' N) ⊔ Rb = ⊤) :
    N ≤ Rb.comap (QuotientGroup.mk' N) ∧ Y ⊔ Rb.comap (QuotientGroup.mk' N) = ⊤ ∧
      Nat.card ↥(Rb.comap (QuotientGroup.mk' N)) = Nat.card ↥N * Nat.card ↥Rb := by
  classical
  set f := QuotientGroup.mk' N with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
  set K : Subgroup X := Rb.comap f with hK
  have hNK : N ≤ K := by
    intro n hn
    show f n ∈ Rb
    rw [hf, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact Rb.one_mem
  refine ⟨hNK, ?_, ?_⟩
  · have h1 : (Y ⊔ K).map f = ⊤ := by
      rw [Subgroup.map_sup, hK, Subgroup.map_comap_eq_self_of_surjective hfsurj, hYR]
    have h2 : f.ker ≤ Y ⊔ K := by
      rw [hf, QuotientGroup.ker_mk']
      exact hNK.trans le_sup_right
    have := Subgroup.comap_map_eq_self h2
    rw [h1, Subgroup.comap_top] at this
    exact this.symm
  · have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index Rb
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h4 : K.index = Rb.index := Subgroup.index_comap_of_surjective Rb hfsurj
    have hi : Rb.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [h4] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    calc Nat.card ↥K * Rb.index = Nat.card X := h1
      _ = Nat.card (X ⧸ N) * Nat.card ↥N := h3
      _ = Nat.card ↥N * Nat.card ↥Rb * Rb.index := by rw [← h2]; ring

theorem exists_normal_sevenGroup_of_central {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (h : SevenData X Y) {N : Subgroup X} [hN : N.Normal] {r d : ℕ} (hr : r.Prime) (hr7 : r ≠ 7)
    (hNcard : Nat.card ↥N = r ^ d) (hcent : ∀ n ∈ N, ∀ x : X, x * n = n * x)
    {Rb : Subgroup (X ⧸ N)} (hRbn : Rb.Normal) (hRb7 : IsPGroup 7 ↥Rb)
    (hYR : Y.map (QuotientGroup.mk' N) ⊔ Rb = ⊤) :
    ∃ R : Subgroup X, R.Normal ∧ IsPGroup 7 ↥R ∧ Y ⊔ R = ⊤ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hNK, hYK, hKcard⟩ := comap_quotient_facts (Y := Y) (N := N) hYR
  set K : Subgroup X := Rb.comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := hRbn.comap _
  set N' : Subgroup ↥K := N.subgroupOf K with hN'
  have : N'.Normal := hN.subgroupOf K
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  obtain ⟨m, hm⟩ := hRb7.exists_card_eq
  have hN'idx : N'.index = 7 ^ m := by
    have h1 := Subgroup.card_mul_index N'
    rw [hN'card, hKcard, hm] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcop : Nat.Coprime (Nat.card ↥N') N'.index := by
    rw [hN'card, hNcard, hN'idx]
    exact Nat.Coprime.pow d m ((Nat.coprime_primes hr (by norm_num)).mpr hr7)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hH'card : Nat.card ↥H' = 7 ^ m := by
    rw [← hN'idx]
    exact (hH'.symm.index_eq_card).symm
  set H : Subgroup X := H'.map K.subtype with hH
  have hHcard : Nat.card ↥H = 7 ^ m := by
    rw [hH, Subgroup.card_map_of_injective K.subtype_injective]
    exact hH'card
  have hH7 : IsPGroup 7 ↥H := IsPGroup.of_card hHcard
  have hHK : H ≤ K := Subgroup.map_subtype_le H'
  have hKNH : K = N ⊔ H := by
    have h1 := hH'.sup_eq_top
    have h2 : (N' ⊔ H').map K.subtype = K := by
      rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [Subgroup.map_sup, hN', Subgroup.map_subgroupOf_eq_of_le hNK] at h2
    exact h2.symm
  have hpowH : ∀ g ∈ H, g ^ 7 ^ m = 1 := by
    intro g hg
    have := (pow_card_eq_one' : (⟨g, hg⟩ : ↥H) ^ Nat.card ↥H = 1)
    rw [hHcard] at this
    simpa using congrArg Subtype.val this
  have hHn : H.Normal := by
    refine ⟨fun h₁ hh₁ g => ?_⟩
    have hgK : g * h₁ * g⁻¹ ∈ K := hKn.conj_mem h₁ (hHK hh₁) g
    have hmem : g * h₁ * g⁻¹ ∈ ((H ⊔ N : Subgroup X) : Set X) := by
      rw [sup_comm, ← hKNH]
      exact hgK
    rw [Subgroup.mul_normal H N] at hmem
    obtain ⟨h₂, hh₂, n, hn, hprod0⟩ := hmem
    have hprod : h₂ * n = g * h₁ * g⁻¹ := hprod0
    have hpow1 : (g * h₁ * g⁻¹) ^ 7 ^ m = 1 := by
      have : (g * h₁ * g⁻¹) ^ 7 ^ m = g * h₁ ^ 7 ^ m * g⁻¹ := conj_pow
      rw [this, hpowH h₁ hh₁]
      group
    have hcomm : Commute h₂ n := hcent n hn h₂
    have hn1 : n ^ 7 ^ m = 1 := by
      have := hpow1
      rw [← hprod, hcomm.mul_pow, hpowH h₂ hh₂, one_mul] at this
      exact this
    have hnN : n ^ r ^ d = 1 := by
      have := (pow_card_eq_one' : (⟨n, hn⟩ : ↥N) ^ Nat.card ↥N = 1)
      rw [hNcard] at this
      simpa using congrArg Subtype.val this
    have hn' : n = 1 := by
      have hg : Nat.gcd (7 ^ m) (r ^ d) = 1 :=
        Nat.Coprime.pow m d ((Nat.coprime_primes (by norm_num) hr).mpr hr7.symm)
      have := pow_gcd_eq_one.mpr ⟨hn1, hnN⟩
      rwa [hg, pow_one] at this
    rw [← hprod, hn', mul_one]
    exact hh₂
  set M : Subgroup X := Y ⊔ H with hM
  have hMn : M.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hYK]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    rw [hKNH]
    refine sup_le ?_ (le_sup_right.trans Subgroup.le_normalizer)
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have : n * g * n⁻¹ = g := by rw [(hcent n hn g).symm, mul_inv_cancel_right]
    rw [this]
  have hMtop : M = ⊤ := h.gen M hMn le_sup_left
  exact ⟨H, hHn, hH7, hMtop⟩

theorem exists_normal_sevenGroup_sup_eq_top_aux (n : ℕ) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → Odd n → ∀ (Y : Subgroup X),
      SevenData X Y → ∃ R : Subgroup X, R.Normal ∧ IsPGroup 7 ↥R ∧ Y ⊔ R = ⊤ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hodd Y hY
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hYtop : Y = ⊤
  · exact ⟨⊥, inferInstance, IsPGroup.of_card (n := 0) (by simp), by simp [hYtop]⟩
  have hodd' : Odd (Nat.card X) := hn ▸ hodd
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hnt : Nontrivial X := by
    by_contra h1
    rw [not_nontrivial_iff_subsingleton] at h1
    apply hYtop
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 1]
    exact Y.one_mem
  obtain ⟨N, hNnorm, hNbot, hNmin0⟩ := CFSG.exists_minimal_normal hsolv hnt
  have hNmin : ∀ M : Subgroup X, M.Normal → M ≠ ⊥ → M ≤ N → M = N :=
    fun M hM hMbot hMN => hNmin0 M hM hMN hMbot
  have hN : N.Normal := hNnorm
  obtain ⟨r, d, hr, hd, hNelem, hNcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian hsolv N hNbot hNmin
  have hYN : ¬ Y ≤ N := by
    intro hle
    have hNtop : N = ⊤ := hY.gen N hN hle
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ N := hNtop ▸ Subgroup.mem_top a
      have hb : b ∈ N := hNtop ▸ Subgroup.mem_top b
      have := hNelem.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥N) ⟨b, hb⟩
      simpa using congrArg Subtype.val this
    apply hYtop
    refine hY.gen Y ⟨fun m hm g => ?_⟩ le_rfl
    rw [hcomm g m, mul_inv_cancel_right]
    exact hm
  have hdisj : Disjoint Y N := disjoint_of_card_three hY.ycard hYN
  have hlt : Nat.card (X ⧸ N) < n := hn ▸ CFSG.card_quotient_lt_of_ne_bot N hNbot
  have hoddq : Odd (Nat.card (X ⧸ N)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1] at hodd'
    exact (Nat.odd_mul.mp hodd').1
  obtain ⟨Rb, hRbn, hRb7, hYR⟩ := ih _ hlt (X ⧸ N) rfl hoddq _ (hY.quotient N hdisj)
  by_cases h7 : r = 7
  ·
    subst h7
    obtain ⟨hNK, hYK, hKcard⟩ := comap_quotient_facts (Y := Y) (N := N) hYR
    refine ⟨Rb.comap (QuotientGroup.mk' N), hRbn.comap _, ?_, hYK⟩
    obtain ⟨m, hm⟩ := hRb7.exists_card_eq
    exact IsPGroup.of_card (n := d + m) (by rw [hKcard, hNcard, hm, pow_add])
  · have hcent : ∀ n ∈ N, ∀ x : X, x * n = n * x := by
      by_cases h3 : r = 3
      · subst h3
        exact central_of_three hodd' hY hNmin hd hNcard
      · exact central_of_other_prime hY hr h3 h7 hNcard
    exact exists_normal_sevenGroup_of_central hY hr h7 hNcard hcent hRbn hRb7 hYR

theorem exists_normal_sevenGroup_sup_eq_top {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card X)) {Y : Subgroup X} (h : SevenData X Y) :
    ∃ R : Subgroup X, R.Normal ∧ IsPGroup 7 ↥R ∧ Y ⊔ R = ⊤ :=
  exists_normal_sevenGroup_sup_eq_top_aux (Nat.card X) X rfl hodd Y h

end CFSG.CGT.PushingUpLit.CGT6

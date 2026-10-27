module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7FStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Gold

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Elem

variable {Y : Type} [Group Y]

theorem exists_q8_pair {Q : Subgroup Y} (hQ : IsQuatSub Q) (h8 : Nat.card Q = 8) {t : Y}
    (ht : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = t) :
    (∀ x ∈ Q, x * x = 1 ∨ x * x = t) ∧ (∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = t) ∧
      ∃ i ∈ Q, ∃ j ∈ Q, i * i = t ∧ j * j = t ∧ i * j * (i * j) = t ∧ i * j ≠ j * i := by
  obtain ⟨k, -, ⟨e⟩⟩ := hQ
  have hk1 : k = 1 := by
    have h := Nat.card_congr e.toEquiv
    rw [h8, Nat.card_eq_fintype_card, QuaternionGroup.card] at h
    have h2 : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hk1
  let f : QuaternionGroup (2 ^ 1) → Y := fun q => (e.symm q : Y)
  have hfm : ∀ q r, f q * f r = f (q * r) := fun q r => by simp [f, map_mul]
  have hfQ : ∀ q, f q ∈ Q := fun q => (e.symm q).2
  have hfinj : ∀ q r, f q = f r → q = r := fun q r h => e.symm.injective (Subtype.ext h)
  have hf1 : f 1 = 1 := by simp [f]
  have hsurj : ∀ x ∈ Q, ∃ q, f q = x := fun x hx => ⟨e ⟨x, hx⟩, by simp [f]⟩
  have hct : f (QuaternionGroup.a 2) = t := by
    rcases ht (f (QuaternionGroup.a 2)) (hfQ _)
      (by rw [hfm, ← hf1]; exact congrArg f (by decide)) with h | h
    · exact absurd (hfinj _ _ (h.trans hf1.symm)) (by decide)
    · exact h
  refine ⟨?_, ?_, f (QuaternionGroup.a 1), hfQ _, f (QuaternionGroup.xa 0), hfQ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, rfl⟩ := hsurj x hx
    rw [hfm, ← hct, ← hf1]
    have : ∀ q : QuaternionGroup (2 ^ 1), q * q = 1 ∨ q * q = QuaternionGroup.a 2 := by decide
    rcases this q with h | h <;> rw [h] <;> simp
  · intro x hx hcen
    obtain ⟨q, rfl⟩ := hsurj x hx
    have hq : ∀ r, q * r = r * q := fun r =>
      hfinj _ _ (by rw [← hfm, ← hfm]; exact hcen _ (hfQ r))
    have : ∀ q : QuaternionGroup (2 ^ 1), (∀ r, q * r = r * q) →
        q = 1 ∨ q = QuaternionGroup.a 2 := by
      decide
    rcases this q hq with h | h
    · left; rw [h, hf1]
    · right; rw [h, hct]
  · rw [hfm, ← hct]; exact congrArg f (by decide)
  · rw [hfm, ← hct]; exact congrArg f (by decide)
  · simp only [hfm]; rw [← hct]; exact congrArg f (by decide)
  · intro h
    rw [hfm, hfm] at h
    exact absurd (hfinj _ _ h) (by decide)

theorem data_of_core {N : Subgroup Y} {t p q p' : Y} (ht2 : t * t = 1) (hp : p * p = t)
    (hq : q * q = t) (hp' : p' * p' = t) (hpq : p * q ≠ q * p) (h1 : p * p' = p' * p)
    (h2 : q * p' = p' * q) (ha : p * p' ∈ N) (hb : q * p' ∈ N) :
    ∃ a b : Y, a ∈ N ∧ b ∈ N ∧ a * t = t * a ∧ b * t = t * b ∧ orderOf a = 2 ∧
      orderOf b = 2 ∧ a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct : ∀ {x : Y}, x * x = t → Commute x t := fun {x} hx => by
    rw [← hx]; exact (Commute.refl x).mul_right (Commute.refl x)
  have hsq : ∀ {x : Y}, x * x = t → x * p' = p' * x → (x * p') * (x * p') = 1 := by
    intro x hx hxc
    calc (x * p') * (x * p') = x * (p' * x) * p' := by group
      _ = x * (x * p') * p' := by rw [← hxc]
      _ = (x * x) * (p' * p') := by group
      _ = 1 := by rw [hx, hp', ht2]
  have hne : ∀ {x y : Y}, x * y ≠ y * x → y * p' = p' * y → x * p' ≠ 1 := by
    intro x y hxy hyc h
    have hp'x : p' = x⁻¹ := eq_inv_of_mul_eq_one_right h
    apply hxy
    rw [hp'x] at hyc
    calc x * y = x * (y * x⁻¹) * x := by group
      _ = x * (x⁻¹ * y) * x := by rw [hyc]
      _ = y * x := by group
  refine ⟨p * p', q * p', ha, hb, ((hct hp).mul_left (hct hp')).eq,
    ((hct hq).mul_left (hct hp')).eq, orderOf_eq_prime (by rw [pow_two]; exact hsq hp h1)
      (hne hpq h2), orderOf_eq_prime (by rw [pow_two]; exact hsq hq h2)
      (hne (fun h => hpq h.symm) h1), ?_⟩
  intro h
  apply hpq
  have e1 : (p * p') * (q * p') = p * q * (p' * p') := by
    calc (p * p') * (q * p') = p * (p' * q) * p' := by group
      _ = p * (q * p') * p' := by rw [← h2]
      _ = p * q * (p' * p') := by group
  have e2 : (q * p') * (p * p') = q * p * (p' * p') := by
    calc (q * p') * (p * p') = q * (p' * p) * p' := by group
      _ = q * (p * p') * p' := by rw [← h1]
      _ = q * p * (p' * p') := by group
  rw [e1, e2] at h
  exact mul_right_cancel h

theorem exists_data_of_index_two {R₁ R₂ N : Subgroup Y} (hc : Commutes R₁ R₂) {t : Y}
    (ht2 : t * t = 1) {i₁ j₁ i₂ j₂ : Y} (hi₁ : i₁ ∈ R₁) (hj₁ : j₁ ∈ R₁) (hi₂ : i₂ ∈ R₂)
    (hj₂ : j₂ ∈ R₂) (hii₁ : i₁ * i₁ = t) (hjj₁ : j₁ * j₁ = t) (hkk₁ : i₁ * j₁ * (i₁ * j₁) = t)
    (hij₁ : i₁ * j₁ ≠ j₁ * i₁) (hii₂ : i₂ * i₂ = t) (hjj₂ : j₂ * j₂ = t)
    (hkk₂ : i₂ * j₂ * (i₂ * j₂) = t) (hij₂ : i₂ * j₂ ≠ j₂ * i₂)
    (hN : ∀ x ∈ R₁ ⊔ R₂, ∀ y ∈ R₁ ⊔ R₂, x ∉ N → y ∉ N → x * y ∈ N) :
    ∃ a b : Y, a ∈ N ∧ b ∈ N ∧ a * t = t * a ∧ b * t = t * b ∧ orderOf a = 2 ∧
      orderOf b = 2 ∧ a * b ≠ b * a := by
  have pickN : ∀ {R : Subgroup Y}, R ≤ R₁ ⊔ R₂ → ∀ {i j : Y}, i ∈ R → j ∈ R → i * i = t →
      j * j = t → i * j * (i * j) = t → ∃ r ∈ R, r * r = t ∧ r ∈ N := by
    intro R hR i j hi hj hii hjj hkk
    by_cases hiN : i ∈ N
    · exact ⟨i, hi, hii, hiN⟩
    by_cases hjN : j ∈ N
    · exact ⟨j, hj, hjj, hjN⟩
    exact ⟨i * j, R.mul_mem hi hj, hkk, hN _ (hR hi) _ (hR hj) hiN hjN⟩
  have pickOut : ∀ {R : Subgroup Y}, ∀ {i j : Y}, i ∈ R → j ∈ R → i * i = t → j * j = t →
      i * j * (i * j) = t → i * j ≠ j * i → ¬ (i ∈ N ∧ j ∈ N) →
      ∃ p ∈ R, ∃ q ∈ R, p * p = t ∧ q * q = t ∧ p * q ≠ q * p ∧ p ∉ N ∧ q ∉ N := by
    intro R i j hi hj hii hjj hkk hij hnot
    by_cases hiN : i ∈ N
    · have hjN : j ∉ N := fun h => hnot ⟨hiN, h⟩
      refine ⟨j, hj, i * j, R.mul_mem hi hj, hjj, hkk, fun h => hij ?_, hjN, fun h => hjN ?_⟩
      · have h' : (j * i) * j = (i * j) * j := by rw [mul_assoc]; exact h
        exact (mul_right_cancel h').symm
      · simpa using N.mul_mem (N.inv_mem hiN) h
    · by_cases hjN : j ∈ N
      · refine ⟨i, hi, i * j, R.mul_mem hi hj, hii, hkk, fun h => hij ?_, hiN, fun h => hiN ?_⟩
        · have h' : i * (i * j) = i * (j * i) := by rw [h, mul_assoc]
          exact mul_left_cancel h'
        · simpa using N.mul_mem h (N.inv_mem hjN)
      · exact ⟨i, hi, j, hj, hii, hjj, hij, hiN, hjN⟩
  by_cases h2N : i₂ ∈ N ∧ j₂ ∈ N
  · obtain ⟨r, hr, hrr, hrN⟩ := pickN le_sup_left hi₁ hj₁ hii₁ hjj₁ hkk₁
    exact data_of_core ht2 hii₂ hjj₂ hrr hij₂ (hc r hr i₂ hi₂).symm (hc r hr j₂ hj₂).symm
      (N.mul_mem h2N.1 hrN) (N.mul_mem h2N.2 hrN)
  obtain ⟨p', hp', hpp', hp'N⟩ : ∃ p' ∈ R₂, p' * p' = t ∧ p' ∉ N := by
    by_cases h : i₂ ∈ N
    · exact ⟨j₂, hj₂, hjj₂, fun h' => h2N ⟨h, h'⟩⟩
    · exact ⟨i₂, hi₂, hii₂, h⟩
  by_cases h1N : i₁ ∈ N ∧ j₁ ∈ N
  · obtain ⟨r, hr, hrr, hrN⟩ := pickN le_sup_right hi₂ hj₂ hii₂ hjj₂ hkk₂
    exact data_of_core ht2 hii₁ hjj₁ hrr hij₁ (hc i₁ hi₁ r hr) (hc j₁ hj₁ r hr)
      (N.mul_mem h1N.1 hrN) (N.mul_mem h1N.2 hrN)
  obtain ⟨p, hp, q, hq, hpp, hqq, hpq, hpN, hqN⟩ :=
    pickOut hi₁ hj₁ hii₁ hjj₁ hkk₁ hij₁ h1N
  exact data_of_core ht2 hpp hqq hpp' hpq (hc p hp p' hp') (hc q hq p' hp')
    (hN _ (Subgroup.mem_sup_left hp) _ (Subgroup.mem_sup_right hp') hpN hp'N)
    (hN _ (Subgroup.mem_sup_left hq) _ (Subgroup.mem_sup_right hp') hqN hp'N)

theorem card_le_two_mul_inf [Finite Y] {Q N : Subgroup Y}
    (hN : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ N → y ∉ N → x * y ∈ N) :
    Nat.card Q ≤ 2 * Nat.card ↥(Q ⊓ N) := by
  by_cases hQN : Q ≤ N
  · rw [inf_eq_left.mpr hQN]; omega
  obtain ⟨x₀, hx₀Q, hx₀N⟩ := Set.not_subset.mp hQN
  have hx₀' : x₀⁻¹ ∉ N := fun h => hx₀N (by simpa using N.inv_mem h)
  classical
  let f : Q → Bool × ↥(Q ⊓ N) := fun y =>
    if hy : (y : Y) ∈ N then (false, ⟨y, y.2, hy⟩)
    else (true, ⟨x₀⁻¹ * y, Q.mul_mem (Q.inv_mem hx₀Q) y.2,
      hN _ (Q.inv_mem hx₀Q) _ y.2 hx₀' hy⟩)
  have hf : Function.Injective f := by
    intro y y' h
    by_cases hy : (y : Y) ∈ N <;> by_cases hy' : (y' : Y) ∈ N <;> simp [f, hy, hy'] at h
    · have h' := congrArg (fun z : ↥(Q ⊓ N) => (z : Y)) h
      exact Subtype.ext h'
    · have h' := congrArg (fun z : ↥(Q ⊓ N) => (z : Y)) h
      exact Subtype.ext (mul_left_cancel h')
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

theorem sup_of_commutes [Finite Y] {R₁ R₂ : Subgroup Y} (hc : Commutes R₁ R₂) :
    (∀ x ∈ R₁ ⊔ R₂, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, x = r₁ * r₂) ∧
      Nat.card ↥(R₁ ⊔ R₂) * Nat.card ↥(R₁ ⊓ R₂) = Nat.card R₁ * Nat.card R₂ := by
  let μ : R₁ × R₂ →* Y := MonoidHom.noncommCoprod R₁.subtype R₂.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : R₁ × R₂, μ x = (x.1 : Y) * x.2 := fun _ => rfl
  have hrange : μ.range = R₁ ⊔ R₂ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y.1, y.1.2, y.2, y.2.2, hμ y⟩
  have hker : Nat.card μ.ker = Nat.card ↥(R₁ ⊓ R₂) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : Y), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : Y)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R₂.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem mul_mem_of_isCyclic_map [Finite Y] {Q N : Subgroup Y} [N.Normal]
    (hcyc : IsCyclic ↥(Q.map (QuotientGroup.mk' N))) (hsq : ∀ x ∈ Q, x * x ∈ N) :
    ∀ x ∈ Q, ∀ y ∈ Q, x ∉ N → y ∉ N → x * y ∈ N := by
  intro x hx y hy hxN hyN
  set H := Q.map (QuotientGroup.mk' N)
  have hexp : ∀ h : H, h ^ 2 = 1 := by
    rintro ⟨_, z, hz, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, ← map_mul, Subgroup.coe_one]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq z hz)
  have hcard : Nat.card H ≤ 2 := by
    have := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    rw [IsCyclic.exponent_eq_card] at this
    exact Nat.le_of_dvd (by norm_num) this
  let x' : H := ⟨QuotientGroup.mk' N x, x, hx, rfl⟩
  let y' : H := ⟨QuotientGroup.mk' N y, y, hy, rfl⟩
  have hx1 : x' ≠ 1 := fun h => hxN ((QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val h))
  have hy1 : y' ≠ 1 := fun h => hyN ((QuotientGroup.eq_one_iff y).mp (congrArg Subtype.val h))
  have h2 : Nat.card H = 2 := by
    haveI : Nontrivial H := ⟨⟨x', 1, hx1⟩⟩
    have := Finite.one_lt_card (α := H)
    omega
  have heq : x' = y' := ((Nat.card_eq_two_iff' (1 : H)).mp h2).unique hx1 hy1
  have hxy : (QuotientGroup.mk' N x : Y ⧸ N) = QuotientGroup.mk' N y := congrArg Subtype.val heq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have := N.mul_mem (hsq x hx) hxy
  simpa [mul_assoc] using this

end Elem

section Gold

@[expose] def GoldOutCyc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
    goldschmidtSimpleType ↥(genFittingFStar X) → ∀ Q : Subgroup X, IsPGroup 2 Q →
      letI : (genFittingFStar X).Normal := genFittingFStar_normal X
      IsCyclic ↥(Q.map (QuotientGroup.mk' (genFittingFStar X)))

theorem goldschmidtSimpleType_fstar {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup (genFittingFStar Y)] (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    (T : Sylow 2 Y) {A : Subgroup Y} (hAT : A ≤ (T : Subgroup Y)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : Y, g⁻¹ * a * g ∈ (T : Subgroup Y) → g⁻¹ * a * g ∈ A) {x : Y}
    (hxA : x ∈ A) (hxL : x ∈ genFittingFStar Y) (hx1 : x ≠ 1) :
    goldschmidtSimpleType ↥(genFittingFStar Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := genFittingFStar Y
  haveI : L.Normal := genFittingFStar_normal Y
  obtain ⟨TL, hTL⟩ := Glauberman.sylow_inf_normal T (N := L)
  have hAabL : IsMulCommutative ((A ⊓ L).subgroupOf L) := ⟨⟨fun x y => by
    have := congrArg Subtype.val (hAab.is_comm.comm ⟨x.1.1, (Subgroup.mem_inf.1 x.2).1⟩
      ⟨y.1.1, (Subgroup.mem_inf.1 y.2).1⟩)
    exact Subtype.ext (Subtype.ext (by simpa using this))⟩⟩
  refine Hat2A7.goldschmidtSimpleType_of_milestone
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian hnab TL
    (A := (A ⊓ L).subgroupOf L) ?_ ?_ hAabL ?_
  · intro h
    have hx : (⟨x, hxL⟩ : L) ∈ (A ⊓ L).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨hxA, hxL⟩
    rw [h, Subgroup.mem_bot] at hx
    exact hx1 (congrArg Subtype.val hx)
  · intro y hy
    rw [hTL, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hy
    exact ⟨hAT (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
  · intro y hy g hg
    rw [hTL, Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    refine ⟨?_, (g⁻¹ * y * g).2⟩
    simpa using hcl _ (Subgroup.mem_inf.1 hy).1 g (by simpa using (Subgroup.mem_inf.1 hg).1)

variable {n : ℕ}

theorem p23_178_of_out (hO : GoldOutCyc) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g)
    (T : Sylow 2 Y) {A : Subgroup Y} (hAT : A ≤ (T : Subgroup Y)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ x : Y, x⁻¹ * a * x ∈ (T : Subgroup Y) → x⁻¹ * a * x ∈ A)
    (hue : u * e ∈ A) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hc.std.perp.core.simple
  set L := genFittingFStar Y with hL
  haveI hLn : L.Normal := genFittingFStar_normal Y
  have htL : t ∈ L := p23_t_mem_fstar hc
  have hueL : u * e ∈ L := by
    rw [← hc.data.hgt]
    exact hLn.conj_mem t htL g
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hue1 : u * e ≠ 1 := fun h => hz.ne_one (by
    have h' : g * t * g⁻¹ = 1 := by rw [hc.data.hgt, h]
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have hG := goldschmidtSimpleType_fstar hc.std.perp.core.nonab T hAT hAab hcl hue hueL hue1
  obtain ⟨R₁, R₂, -, -, hR₁, hR₂, -, -, hcomm, -, -, -, -, -, -⟩ := e_decomp hc
  have hst := CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC
  have h8₁ : Nat.card R₁ = 8 := hst.card8 _ hK R₁ hR₁
  have h8₂ : Nat.card R₂ = 8 := hst.card8 _ hc.std.hK'.1 R₂ hR₂
  have hq₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  have hq₂ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hc.std.hK'.1 hR₂)
  obtain ⟨hsq₁, hcen₁, i₁, hi₁, j₁, hj₁, hii₁, hjj₁, hkk₁, hij₁⟩ :=
    exists_q8_pair hq₁ h8₁ (fun x hx hxx => hz.unique x (hR₁.1 hx) hxx)
  obtain ⟨hsq₂, -, i₂, hi₂, j₂, hj₂, hii₂, hjj₂, hkk₂, hij₂⟩ :=
    exists_q8_pair hq₂ h8₂ (fun x hx hxx => hz'.unique x (hR₂.1 hx) hxx)
  have ht2 : t * t = 1 := hz.sq
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) hz.ne_one
  obtain ⟨hprodQ, hcardQ⟩ := sup_of_commutes hcomm
  set Q := R₁ ⊔ R₂ with hQ
  have hinf : R₁ ⊓ R₂ ≤ Subgroup.zpowers t := by
    intro x hx
    rcases hcen₁ x hx.1 (fun y hy => (hcomm y hy x hx.2).symm) with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have hinf2 : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 := by
    have := Subgroup.card_le_of_le hinf
    rwa [Nat.card_zpowers, hot] at this
  rw [h8₁, h8₂] at hcardQ
  have hQ32 : 32 ≤ Nat.card Q := by nlinarith
  have hQ2 : IsPGroup 2 Q := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card Q ∣ 2 ^ 6 from Dvd.intro _ (hcardQ.trans (by norm_num)))
    exact IsPGroup.of_card hm
  have hsqQ : ∀ x ∈ Q, x * x ∈ L := by
    intro x hx
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hprodQ x hx
    have hmem : ∀ {s : Y}, (s * s = 1 ∨ s * s = t) → s * s ∈ L := by
      rintro s (h | h) <;> rw [h]
      exacts [L.one_mem, htL]
    have e1 : r₁ * r₂ * (r₁ * r₂) = (r₁ * r₁) * (r₂ * r₂) := by
      calc r₁ * r₂ * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
        _ = r₁ * (r₁ * r₂) * r₂ := by rw [← hcomm r₁ hr₁ r₂ hr₂]
        _ = (r₁ * r₁) * (r₂ * r₂) := by group
    rw [e1]
    exact L.mul_mem (hmem (hsq₁ r₁ hr₁)) (hmem (hsq₂ r₂ hr₂))
  have hN := mul_mem_of_isCyclic_map (hO Y inferInstance hG Q hQ2) hsqQ
  obtain ⟨a, b, haL, hbL, hat, hbt, ha2, hb2, hab⟩ := exists_data_of_index_two hcomm ht2 hi₁ hj₁
    hi₂ hj₂ hii₁ hjj₁ hkk₁ hij₁ hii₂ hjj₂ hkk₂ hij₂ hN
  have hP16 : 16 ≤ Nat.card ↥(Q ⊓ L) := by
    have : Nat.card Q ≤ 2 * Nat.card ↥(Q ⊓ L) := card_le_two_mul_inf hN
    omega
  have h := FStar178.inf_fstar_eq_bot_of_stronglyClosed hc.std.perp.core.nonab (z := t) htL haL
    hbL hot (Subgroup.mem_centralizer_singleton_iff.mpr hat)
    (Subgroup.mem_centralizer_singleton_iff.mpr hbt) ha2 hb2 hab (P := Q ⊓ L) inf_le_right
    (hQ2.to_le inf_le_left) hP16 T hAT hAab hcl
  have := (Subgroup.mem_inf.2 ⟨hue, hueL⟩ : u * e ∈ A ⊓ L)
  rw [h, Subgroup.mem_bot] at this
  exact hue1 this

end Gold

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

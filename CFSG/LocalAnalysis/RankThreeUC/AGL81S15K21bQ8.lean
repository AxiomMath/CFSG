module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bQ8Proof

theorem quaternion_pow_four (g : QuaternionGroup 2) : g ^ 4 = 1 := by
  revert g
  decide

theorem quaternion_not_comm : ¬ ∀ g h : QuaternionGroup 2, g * h = h * g := by
  decide

theorem exists_noncomm_of_equiv {H : Type} [Group H] {Q : Subgroup H}
    (e : ↥Q ≃* QuaternionGroup 2) : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply quaternion_not_comm
  intro g h
  have hgh := hcon (e.symm g) (e.symm g).2 (e.symm h) (e.symm h).2
  apply e.symm.injective
  apply Subtype.ext
  simpa [map_mul] using hgh

theorem pow_four_of_equiv {H : Type} [Group H] {Q : Subgroup H}
    (e : ↥Q ≃* QuaternionGroup 2) {a : H} (ha : a ∈ Q) : a ^ 4 = 1 := by
  have h1 : (⟨a, ha⟩ : ↥Q) ^ 4 = 1 :=
    e.injective (by rw [map_pow, quaternion_pow_four, map_one])
  have h2 := congrArg (fun x : ↥Q => (x : H)) h1
  simpa using h2

theorem mulAut_comm_of_card_three {C : Type} [Group C] (hC : Nat.card C = 3) (σ τ : MulAut C) :
    σ * τ = τ * σ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic C := isCyclic_of_prime_card hC
  apply (IsCyclic.mulAutMulEquiv C).injective
  rw [map_mul, map_mul, mul_comm]

@[expose] def restrictAut {V : Type} [Group V] (F : Subgroup V) (a : MulAut V)
    (h1 : ∀ x ∈ F, a x ∈ F) (h2 : ∀ x ∈ F, a⁻¹ x ∈ F) : MulAut ↥F where
  toFun x := ⟨a x.1, h1 x.1 x.2⟩
  invFun x := ⟨a⁻¹ x.1, h2 x.1 x.2⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self _ a x.1)
  right_inv x := Subtype.ext (MulAut.apply_inv_self _ a x.1)
  map_mul' x y := Subtype.ext (map_mul a x.1 y.1)

theorem restrictAut_apply {V : Type} [Group V] (F : Subgroup V) (a : MulAut V)
    (h1 : ∀ x ∈ F, a x ∈ F) (h2 : ∀ x ∈ F, a⁻¹ x ∈ F) (x : ↥F) :
    ((restrictAut F a h1 h2 x : ↥F) : V) = a x.1 :=
  rfl

theorem comm_on_subgroup {V : Type} [Group V] (F : Subgroup V) (hF : Nat.card F = 3)
    (a b : MulAut V) (ha1 : ∀ x ∈ F, a x ∈ F) (ha2 : ∀ x ∈ F, a⁻¹ x ∈ F)
    (hb1 : ∀ x ∈ F, b x ∈ F) (hb2 : ∀ x ∈ F, b⁻¹ x ∈ F) {x : V} (hx : x ∈ F) :
    a (b x) = b (a x) := by
  have h := congrArg (fun σ : MulAut ↥F => ((σ ⟨x, hx⟩ : ↥F) : V))
    (mulAut_comm_of_card_three hF (restrictAut F a ha1 ha2) (restrictAut F b hb1 hb2))
  simpa [MulAut.mul_apply, restrictAut_apply] using h

theorem map_eq_of_invariant {V : Type} [Group V] (F : Subgroup V) (a : MulAut V)
    (h1 : ∀ x ∈ F, a x ∈ F) (h2 : ∀ x ∈ F, a⁻¹ x ∈ F) : F.map (a : V →* V) = F := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro hy
    exact ⟨a⁻¹ y, h2 y hy, MulAut.apply_inv_self _ a y⟩

theorem comm_mod_subgroup {V : Type} [Group V] (F : Subgroup V) [F.Normal]
    (hF : Nat.card (V ⧸ F) = 3) (a b : MulAut V) (ha : F.map (a : V →* V) = F)
    (hb : F.map (b : V →* V) = F) (x : V) : (a (b x))⁻¹ * b (a x) ∈ F := by
  have h := congrArg (fun σ : MulAut (V ⧸ F) => σ (QuotientGroup.mk x))
    (mulAut_comm_of_card_three hF (QuotientGroup.congr F F a ha) (QuotientGroup.congr F F b hb))
  simp only [MulAut.mul_apply, QuotientGroup.congr_mk] at h
  exact QuotientGroup.eq.mp h

theorem mul_mul_eq_one {V : Type} [Group V] (hp : ∀ x : V, x ^ 3 = 1) (F : Subgroup V)
    (k : MulAut V) (h1 : ∀ x ∈ F, k x = x) (h2 : ∀ x : V, x⁻¹ * k x ∈ F) :
    k * (k * k) = 1 := by
  ext x
  obtain ⟨δ, hδF, hkx⟩ : ∃ δ ∈ F, k x = x * δ := ⟨x⁻¹ * k x, h2 x, by simp⟩
  have hδ3 : δ * δ * δ = 1 :=
    calc δ * δ * δ = δ ^ 3 := (pow_three' δ).symm
      _ = 1 := hp δ
  have e2 : k (x * δ) = x * δ * δ := by rw [map_mul, ← hkx, h1 δ hδF]
  have e3 : k (x * δ * δ) = x * δ * δ * δ := by rw [map_mul, e2, h1 δ hδF]
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hkx, e2, e3]
  calc x * δ * δ * δ = x * (δ * δ * δ) := by simp only [mul_assoc]
    _ = x := by rw [hδ3, mul_one]

end K21bQ8Proof

theorem hasQ8_exists_noncomm {H : Type} [Group H] {A : Subgroup H} (hA : KFactsSmall.HasQ8 A) :
    ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  obtain ⟨Q, hQA, ⟨e⟩⟩ := hA
  obtain ⟨a, ha, b, hb, hab⟩ := K21bQ8Proof.exists_noncomm_of_equiv e
  exact ⟨a, hQA ha, b, hQA hb, hab⟩

theorem eq_bot_or_eq_top_of_hasQ8 {V : Type} [Group V] [Finite V] (hV : ∀ x y : V, x * y = y * x)
    (hp : ∀ x : V, x ^ 3 = 1) (hc : Nat.card V = 9) {A : Subgroup (MulAut V)}
    (hA : KFactsSmall.HasQ8 A) (F : Subgroup V) (hF : ∀ a ∈ A, ∀ x ∈ F, a x ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hbot, htop⟩ := hne
  obtain ⟨Q, hQA, ⟨e⟩⟩ := hA
  have hdvd : Nat.card F ∣ 3 ^ 2 := by
    have h := F.card_subgroup_dvd_card
    rwa [hc, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  obtain ⟨m, hm, hFm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hF3 : Nat.card F = 3 := by
    interval_cases m
    · exact absurd (Subgroup.eq_bot_of_card_eq F (by simpa using hFm)) hbot
    · simpa using hFm
    · exact absurd ((Subgroup.card_eq_iff_eq_top F).mp (by rw [hFm, hc]; norm_num)) htop
  haveI hFn : F.Normal := ⟨fun n hn g => by rw [hV g n, mul_inv_cancel_right]; exact hn⟩
  have hQcard : Nat.card (V ⧸ F) = 3 := by
    have h := F.index_mul_card
    rw [F.index_eq_card, hF3, hc] at h
    omega
  have hinv : ∀ a ∈ A, ∀ x ∈ F, a⁻¹ x ∈ F := fun a ha => hF a⁻¹ (A.inv_mem ha)
  have hcommF : ∀ a ∈ A, ∀ b ∈ A, ∀ x ∈ F, a (b x) = b (a x) := fun a ha b hb x hx =>
    K21bQ8Proof.comm_on_subgroup F hF3 a b (hF a ha) (hinv a ha) (hF b hb) (hinv b hb) hx
  have hcommQ : ∀ a ∈ A, ∀ b ∈ A, ∀ x : V, (a (b x))⁻¹ * b (a x) ∈ F := fun a ha b hb x =>
    K21bQ8Proof.comm_mod_subgroup F hQcard a b
      (K21bQ8Proof.map_eq_of_invariant F a (hF a ha) (hinv a ha))
      (K21bQ8Proof.map_eq_of_invariant F b (hF b hb) (hinv b hb)) x
  have hk3 : ∀ a ∈ A, ∀ b ∈ A, (a * b * (b * a)⁻¹) * ((a * b * (b * a)⁻¹) * (a * b * (b * a)⁻¹))
      = 1 := by
    intro a ha b hb
    have hba : b * a ∈ A := A.mul_mem hb ha
    have hy : ∀ x ∈ F, (b * a)⁻¹ x ∈ F := fun x hx => hF _ (A.inv_mem hba) x hx
    have h1 : ∀ x : V, b (a ((b * a)⁻¹ x)) = x := fun x => by
      have h := MulAut.apply_inv_self _ (b * a) x
      rwa [MulAut.mul_apply] at h
    have e1 : ∀ x : V, (a * b * (b * a)⁻¹) x = a (b ((b * a)⁻¹ x)) := fun x => by
      simp only [MulAut.mul_apply]
    apply K21bQ8Proof.mul_mul_eq_one hp F
    · intro x hx
      rw [e1, hcommF a ha b hb _ (hy x hx), h1]
    · intro x
      have h := hcommQ a ha b hb ((b * a)⁻¹ x)
      rw [h1] at h
      have h' := F.inv_mem h
      rw [mul_inv_rev, inv_inv] at h'
      rwa [e1]
  obtain ⟨a, ha, b, hb, hab⟩ := K21bQ8Proof.exists_noncomm_of_equiv e
  apply hab
  have hk4 : (a * b * (b * a)⁻¹) ^ 4 = 1 :=
    K21bQ8Proof.pow_four_of_equiv e (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem (Q.mul_mem hb ha)))
  have hk := hk3 a (hQA ha) b (hQA hb)
  have hk1 : a * b * (b * a)⁻¹ = 1 := by
    calc a * b * (b * a)⁻¹ = (a * b * (b * a)⁻¹) ^ 4 := by
          generalize a * b * (b * a)⁻¹ = k at hk ⊢
          calc k = k * 1 := (mul_one k).symm
            _ = k * (k * (k * k)) := by rw [hk]
            _ = k ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := hk4
  exact mul_inv_eq_one.mp hk1

end CFSG.LocalAnalysis.RankThreeUC.S15

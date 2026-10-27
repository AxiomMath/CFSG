module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.BorelDataP

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

section RK

variable (hB : BorelDataP p P M x f W) {O : Subgroup G}

open scoped Pointwise in
theorem mem_QK_sup_iff (hQO : hB.QK ≤ normalizer (O : Set G)) {r : G} :
    r ∈ hB.QK ⊔ O ↔ ∃ (t : GaloisField p n) (o : G), o ∈ O ∧ r = f t * o := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right hB.QK O hQO
  constructor
  · intro hr
    have hr' : r ∈ ((hB.QK : Set G) * (O : Set G)) := by rw [← h]; exact hr
    obtain ⟨q, hq, o, ho, rfl⟩ := hr'
    obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
    exact ⟨t, o, ho, rfl⟩
  · rintro ⟨t, o, ho, rfl⟩
    exact Subgroup.mul_mem_sup (hB.f_mem_QK t) ho

theorem eq_of_f_mul_mem (hO : ¬ p ∣ Nat.card O) {s t : GaloisField p n} {o o' : G}
    (ho : o ∈ O) (ho' : o' ∈ O) (hQO : hB.QK ≤ normalizer (O : Set G))
    (h : f s * o = f t * o') : s = t := by
  have h1 : f (s - t) ∈ O := by
    have hst : f (s - t) = f s * (f t)⁻¹ := by
      rw [sub_eq_add_neg, hB.f_add, hB.f_neg]
    rw [hst]
    have h2 : f s = f t * o' * o⁻¹ := by
      have := congrArg (· * o⁻¹) h
      simpa using this
    rw [h2]
    have : f t * o' * o⁻¹ * (f t)⁻¹ = (f t * (o' * o⁻¹) * (f t)⁻¹) := by group
    rw [this]
    exact (mem_normalizer_iff.mp (hQO (hB.f_mem_QK t)) (o' * o⁻¹)).mp
      (O.mul_mem ho' (O.inv_mem ho))
  have h3 : f (s - t) ^ p = 1 := hB.f_pow_p _
  by_contra hne
  have hne' : s - t ≠ 0 := sub_ne_zero.mpr hne
  have hf1 : f (s - t) ≠ 1 := fun h1' => hne' (hB.f_inj (h1'.trans hB.f_zero.symm))
  have hord : orderOf (f (s - t)) = p := orderOf_eq_prime h3 hf1
  have hd : orderOf (f (s - t)) ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨f (s - t), h1⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rw [hord] at hd
  exact hO hd

theorem QK_inf_eq_bot (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) :
    hB.QK ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgQ, hgO⟩
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hgQ
  have h : t = 0 := hB.eq_of_f_mul_mem hO (s := t) (t := 0) (o := 1) (o' := f t)
    O.one_mem hgO hQO (by rw [hB.f_zero]; simp)
  rw [h, hB.f_zero]
  exact Subgroup.one_mem _

theorem pow_p_mem_QK_sup (hQO : hB.QK ≤ normalizer (O : Set G)) {r : G}
    (hr : r ∈ hB.QK ⊔ O) : r ^ p ∈ O := by
  obtain ⟨t, o, ho, rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr
  have hinv : (f t)⁻¹ ∈ normalizer (O : Set G) := hQO (hB.QK.inv_mem (hB.f_mem_QK t))
  have hconj : ∀ g ∈ O, (f t)⁻¹ * g * f t ∈ O := fun g hg => by
    have := (mem_normalizer_iff.mp hinv g).mp hg
    simpa using this
  have key : ∀ k : ℕ, ∃ o' ∈ O, (f t * o) ^ k = f t ^ k * o' := by
    intro k
    induction k with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨o', ho', h⟩ := ih
      refine ⟨(f t)⁻¹ * o' * f t * o, O.mul_mem (hconj o' ho') ho, ?_⟩
      rw [pow_succ (f t * o) k, h, pow_succ (f t) k]
      group
  obtain ⟨o', ho', h⟩ := key p
  rw [h, hB.f_pow_p t, one_mul]
  exact ho'

theorem comm_mem_QK_sup (hQO : hB.QK ≤ normalizer (O : Set G)) {r r' : G}
    (hr : r ∈ hB.QK ⊔ O) (hr' : r' ∈ hB.QK ⊔ O) : r * r' * r⁻¹ * r'⁻¹ ∈ O := by
  obtain ⟨s, o, ho, rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr
  obtain ⟨t, o', ho', rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr'
  have hab : f s * f t = f t * f s := hB.QK_comm (hB.f_mem_QK s) (hB.f_mem_QK t)
  have hbo : (f t)⁻¹ * o * f t ∈ O := by
    have := (mem_normalizer_iff.mp (hQO (hB.f_mem_QK t |> hB.QK.inv_mem)) o).mp ho
    simpa using this
  have hao : (f s)⁻¹ * o' * f s ∈ O := by
    have := (mem_normalizer_iff.mp (hQO (hB.f_mem_QK s |> hB.QK.inv_mem)) o').mp ho'
    simpa using this
  set o₁ : G := ((f t)⁻¹ * o * f t) * o' with ho₁
  set o₂ : G := ((f s)⁻¹ * o' * f s) * o with ho₂
  have h1 : (f s * o) * (f t * o') = (f s * f t) * o₁ := by simp only [ho₁]; group
  have h2 : (f t * o') * (f s * o) = (f s * f t) * o₂ := by rw [hab]; simp only [ho₂]; group
  have h3 : f s * o * (f t * o') * (f s * o)⁻¹ * (f t * o')⁻¹ =
      ((f s * o) * (f t * o')) * ((f t * o') * (f s * o))⁻¹ := by group
  rw [h3, h1, h2]
  have hc : f s * f t ∈ hB.QK := hB.QK.mul_mem (hB.f_mem_QK s) (hB.f_mem_QK t)
  have : (f s * f t) * o₁ * ((f s * f t) * o₂)⁻¹ =
      (f s * f t) * (o₁ * o₂⁻¹) * (f s * f t)⁻¹ := by group
  rw [this]
  exact (mem_normalizer_iff.mp (hQO hc) _).mp (O.mul_mem (O.mul_mem hbo ho') (O.inv_mem
    (O.mul_mem hao ho)))

theorem card_QK_sup (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) :
    Nat.card (hB.QK ⊔ O : Subgroup G) = Nat.card hB.QK * Nat.card O := by
  have hbot := hB.QK_inf_eq_bot hO hQO
  let φ : hB.QK × O → (hB.QK ⊔ O : Subgroup G) := fun z =>
    ⟨(z.1 : G) * z.2, Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨o, ho⟩⟩ ⟨⟨a', ha'⟩, ⟨o', ho'⟩⟩ h
    have h1 : a * o = a' * o' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = o' * o⁻¹ := by
      have := congrArg (fun z => a'⁻¹ * z * o⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : a'⁻¹ * a ∈ hB.QK ⊓ O := ⟨hB.QK.mul_mem (hB.QK.inv_mem ha') ha, by
      rw [h2]; exact O.mul_mem ho' (O.inv_mem ho)⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
    subst h3
    have : o = o' := by simpa using h1
    subst this
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨r, hr⟩
    obtain ⟨t, o, ho, rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr
    exact ⟨⟨⟨f t, hB.f_mem_QK t⟩, ⟨o, ho⟩⟩, rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

theorem QK_isPGroup : IsPGroup p hB.QK :=
  fun g => ⟨1, Subtype.ext (by simpa using hB.QK_pow_p g.2)⟩

theorem isSylowOf_QK (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf p hB.QK (hB.QK ⊔ O) := by
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left ?_
  obtain ⟨k, hk⟩ := hB.QK_isPGroup.exists_card_eq
  rw [hB.card_QK_sup hO hQO, hk]
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hO0,
    Nat.Prime.factorization_pow hp.out, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hO]
  simp

theorem card_QK : Nat.card hB.QK = p ^ n := by
  have hfinj : Function.Injective hB.fHom := fun a b hab =>
    Multiplicative.toAdd.injective (hB.f_inj hab)
  have h1 : Nat.card (Multiplicative (GaloisField p n)) = Nat.card hB.QK :=
    Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
  rw [← h1, Nat.card_congr (Multiplicative.toAdd : Multiplicative (GaloisField p n) ≃ _)]
  exact GaloisField.card p n (by have := hB.three_le; omega)

@[expose] def Acts (O : Subgroup G) (m : G) (ψ : GaloisField p n → GaloisField p n) : Prop :=
  ∀ t, ∃ o ∈ O, m * f t * m⁻¹ = f (ψ t) * o

theorem exists_acts (hRM : M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G))
    (hQO : hB.QK ≤ normalizer (O : Set G)) {m : G} (hm : m ∈ M) :
    ∃ ψ : GaloisField p n → GaloisField p n, Acts (f := f) O m ψ := by
  have : ∀ t, ∃ s, ∃ o ∈ O, m * f t * m⁻¹ = f s * o := by
    intro t
    have h := (mem_normalizer_iff.mp (hRM hm) (f t)).mp (Subgroup.mem_sup_left (hB.f_mem_QK t))
    obtain ⟨s, o, ho, h'⟩ := (hB.mem_QK_sup_iff hQO).mp h
    exact ⟨s, o, ho, h'⟩
  choose ψ hψ using this
  exact ⟨ψ, hψ⟩

theorem Acts.map_add (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G)) {m : G}
    {ψ : GaloisField p n → GaloisField p n} (h : Acts (f := f) O m ψ) (s t : GaloisField p n) :
    ψ (s + t) = ψ s + ψ t := by
  obtain ⟨o₁, ho₁, h1⟩ := h s
  obtain ⟨o₂, ho₂, h2⟩ := h t
  obtain ⟨o₃, ho₃, h3⟩ := h (s + t)
  have hc : m * f (s + t) * m⁻¹ = (m * f s * m⁻¹) * (m * f t * m⁻¹) := by
    rw [hB.f_add]; group
  have ho : (f (ψ t))⁻¹ * o₁ * f (ψ t) ∈ O := by
    have := (mem_normalizer_iff.mp (hQO (hB.QK.inv_mem (hB.f_mem_QK (ψ t)))) o₁).mp ho₁
    simpa using this
  have h4 : f (ψ s + ψ t) * (((f (ψ t))⁻¹ * o₁ * f (ψ t)) * o₂) = f (ψ (s + t)) * o₃ := by
    rw [← h3, hc, h1, h2, hB.f_add]
    group
  exact (hB.eq_of_f_mul_mem hO (O.mul_mem ho ho₂) ho₃ hQO h4).symm

theorem Acts.injective (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G))
    {m : G} (hmO : m ∈ normalizer (O : Set G)) {ψ : GaloisField p n → GaloisField p n}
    (h : Acts (f := f) O m ψ) : Function.Injective ψ := by
  intro s t hst
  obtain ⟨o₁, ho₁, h1⟩ := h s
  obtain ⟨o₂, ho₂, h2⟩ := h t
  rw [hst] at h1
  have h3 : m * (f s * (f t)⁻¹) * m⁻¹ = f (ψ t) * o₁ * o₂⁻¹ * (f (ψ t))⁻¹ := by
    have e1 : m * (f s * (f t)⁻¹) * m⁻¹ = (m * f s * m⁻¹) * (m * f t * m⁻¹)⁻¹ := by group
    rw [e1, h1, h2]
    group
  have h4 : f (ψ t) * (o₁ * o₂⁻¹) * (f (ψ t))⁻¹ ∈ O :=
    (mem_normalizer_iff.mp (hQO (hB.f_mem_QK _)) _).mp (O.mul_mem ho₁ (O.inv_mem ho₂))
  have h5 : f s * (f t)⁻¹ ∈ O := by
    have h6 : m * (f s * (f t)⁻¹) * m⁻¹ ∈ O := by
      rw [h3]
      simpa [mul_assoc] using h4
    have := (mem_normalizer_iff.mp hmO (f s * (f t)⁻¹)).mpr h6
    exact this
  have h7 : f (s - t) ∈ hB.QK ⊓ O := by
    refine ⟨hB.f_mem_QK _, ?_⟩
    rw [sub_eq_add_neg, hB.f_add, hB.f_neg]
    exact h5
  rw [hB.QK_inf_eq_bot hO hQO, Subgroup.mem_bot] at h7
  exact sub_eq_zero.mp (hB.f_inj (h7.trans hB.f_zero.symm))

theorem Acts.involutive (hO : ¬ p ∣ Nat.card O) (hQO : hB.QK ≤ normalizer (O : Set G))
    {m : G} (hmO : m ∈ normalizer (O : Set G)) (hm2 : m * m = 1)
    {ψ : GaloisField p n → GaloisField p n} (h : Acts (f := f) O m ψ) (t : GaloisField p n) :
    ψ (ψ t) = t := by
  obtain ⟨o₁, ho₁, h1⟩ := h t
  obtain ⟨o₂, ho₂, h2⟩ := h (ψ t)
  have h3 : f t = f (ψ (ψ t)) * (o₂ * (m * o₁ * m⁻¹)) := by
    have e : f t = m * (m * f t * m⁻¹) * m⁻¹ := by
      have : m * (m * f t * m⁻¹) * m⁻¹ = (m * m) * f t * (m * m)⁻¹ := by group
      rw [this, hm2]; simp
    rw [e, h1]
    have : m * (f (ψ t) * o₁) * m⁻¹ = (m * f (ψ t) * m⁻¹) * (m * o₁ * m⁻¹) := by group
    rw [this, h2]
    group
  have ho : o₂ * (m * o₁ * m⁻¹) ∈ O :=
    O.mul_mem ho₂ ((mem_normalizer_iff.mp hmO o₁).mp ho₁)
  exact hB.eq_of_f_mul_mem hO (O := O) (o := o₂ * (m * o₁ * m⁻¹)) (o' := 1) ho O.one_mem hQO
    (by rw [← h3]; simp)

end RK

end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

private theorem cnt_exists_mul_subgroup {G : Type} [Group G] (A B : Subgroup G)
    (h : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) :
    ∃ C : Subgroup G, ∀ x, x ∈ C ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b :=
  ⟨{ carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
     one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
     mul_mem' := by
       rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
       refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha (h b hb a' ha'), b * b', B.mul_mem hb hb', ?_⟩
       group
     inv_mem' := by
       rintro _ ⟨a, ha, b, hb, rfl⟩
       refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, h b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha), b⁻¹, B.inv_mem hb, ?_⟩
       group }, fun _ => Iff.rfl⟩

private theorem cnt_odd_le_of_cover {G : Type} [Group G] [Finite G] (Hh K R : Subgroup G) (y : G)
    (hy : y ∈ Hh) (hcov : ∀ c ∈ Hh, c ∈ K ∨ ∃ z ∈ K, c = y * z) (hRH : R ≤ Hh)
    (hRodd : Odd (Nat.card R)) : R ≤ K := by
  obtain ⟨k, hk⟩ := hRodd
  intro r hr
  have hpow : r ^ (2 * k + 1) = 1 := by
    have h1 : (⟨r, hr⟩ : R) ^ Nat.card R = 1 := pow_card_eq_one'
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have key : r ^ 2 ∈ K → r ∈ K := by
    intro h2
    have hr' : (r ^ 2) ^ (k + 1) = r := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hpow, one_mul]
    rw [← hr']
    exact K.pow_mem h2 _
  rcases hcov r (hRH hr) with h | ⟨z, hz, hrz⟩
  · exact h
  · have hzH : z ∈ Hh := by
      have : z = y⁻¹ * r := by rw [hrz]; group
      rw [this]
      exact Hh.mul_mem (Hh.inv_mem hy) (hRH hr)
    rcases hcov (y * z * y) (Hh.mul_mem (Hh.mul_mem hy hzH) hy) with h | ⟨z', hz', hzz'⟩
    · apply key
      have : r ^ 2 = (y * z * y) * z := by rw [sq, hrz]; group
      rw [this]
      exact K.mul_mem h hz
    · have hyK : y ∈ K := by
        have h3 : z * y = z' := mul_left_cancel (by rw [← mul_assoc]; exact hzz')
        have : y = z⁻¹ * z' := by rw [← h3]; group
        rw [this]
        exact K.mul_mem (K.inv_mem hz) hz'
      rw [hrz]
      exact K.mul_mem hyK hz

private theorem cnt_card_le_mul_card_inf {G : Type} [Group G] [Finite G] (R T : Subgroup G) {X : Type}
    [Finite X] (φ : R → X) (h : ∀ r s : R, φ r = φ s → (r : G)⁻¹ * s ∈ T) :
    Nat.card R ≤ Nat.card X * Nat.card ↥(R ⊓ T) := by
  classical
  let ρ : X → R := Function.invFun φ
  have hρ : ∀ r : R, φ (ρ (φ r)) = φ r := fun r => Function.invFun_eq ⟨r, rfl⟩
  let Θ : R → X × ↥(R ⊓ T) := fun r =>
    (φ r, ⟨((ρ (φ r) : R) : G)⁻¹ * r, R.mul_mem (R.inv_mem (ρ (φ r)).2) r.2, h _ _ (hρ r)⟩)
  have hΘ : Function.Injective Θ := by
    intro r s hrs
    have h1 : φ r = φ s := congrArg Prod.fst hrs
    have h2 := congrArg (fun p : X × ↥(R ⊓ T) => (p.2 : G)) hrs
    simp only [Θ] at h2
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  calc Nat.card R ≤ Nat.card (X × ↥(R ⊓ T)) := Nat.card_le_card_of_injective Θ hΘ
    _ = Nat.card X * Nat.card ↥(R ⊓ T) := Nat.card_prod _ _

private theorem cnt_exists_prod_split {G : Type} [Group G] [Finite G] (M I R₁ : Subgroup G)
    (hMI : ∀ m ∈ M, ∀ i ∈ I, m * i = i * m) (hMIinf : M ⊓ I = ⊥)
    (hR₁ : ∀ x ∈ R₁, ∃ m ∈ M, ∃ i ∈ I, x = m * i) :
    ∃ P Z : Subgroup G, P ≤ I ∧ Z ≤ M ∧ Z ≤ R₁ ∧ (∀ p ∈ P, ∃ m ∈ M, m * p ∈ R₁) ∧
      Nat.card R₁ = Nat.card P * Nat.card Z := by
  have huniq : ∀ m ∈ M, ∀ m' ∈ M, ∀ i ∈ I, ∀ i' ∈ I, m * i = m' * i' → i = i' := by
    intro m hm m' hm' i hi i' hi' h
    have h1 : m'⁻¹ * m ∈ M ⊓ I := by
      refine ⟨M.mul_mem (M.inv_mem hm') hm, ?_⟩
      have : m'⁻¹ * m = i' * i⁻¹ :=
        calc m'⁻¹ * m = m'⁻¹ * (m * i) * i⁻¹ := by group
          _ = m'⁻¹ * (m' * i') * i⁻¹ := by rw [h]
          _ = i' * i⁻¹ := by group
      rw [this]
      exact I.mul_mem hi' (I.inv_mem hi)
    rw [hMIinf, Subgroup.mem_bot] at h1
    have h3 : m' = m := inv_mul_eq_one.mp h1
    subst h3
    exact mul_left_cancel h
  have hex : ∀ x : R₁, ∃ i, i ∈ I ∧ ∃ m ∈ M, (x : G) = m * i := by
    intro x
    obtain ⟨m, hm, i, hi, hx⟩ := hR₁ x x.2
    exact ⟨i, hi, m, hm, hx⟩
  choose ι hιI hι using hex
  have hmul : ∀ x y : R₁, ι (x * y) = ι x * ι y := by
    intro x y
    obtain ⟨m, hm, hx⟩ := hι x
    obtain ⟨m', hm', hy⟩ := hι y
    obtain ⟨m'', hm'', hxy⟩ := hι (x * y)
    have h1 : ((x * y : R₁) : G) = (m * m') * (ι x * ι y) :=
      calc ((x * y : R₁) : G) = (x : G) * y := rfl
        _ = (m * ι x) * (m' * ι y) := by rw [← hx, ← hy]
        _ = m * (ι x * m') * ι y := by group
        _ = m * (m' * ι x) * ι y := by rw [← hMI m' hm' (ι x) (hιI x)]
        _ = (m * m') * (ι x * ι y) := by group
    exact huniq m'' hm'' (m * m') (M.mul_mem hm hm') _ (hιI _) _ (I.mul_mem (hιI x) (hιI y))
      (hxy.symm.trans h1)
  let ψ : R₁ →* G := MonoidHom.mk' ι hmul
  refine ⟨ψ.range, ψ.ker.map R₁.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hιI x
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm, hxm⟩ := hι x
    have h1 : ι x = 1 := hx
    rw [Subgroup.coe_subtype, hxm, h1, mul_one]
    exact hm
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · rintro _ ⟨x, rfl⟩
    obtain ⟨m, hm, hxm⟩ := hι x
    exact ⟨m, hm, hxm ▸ x.2⟩
  · rw [Subgroup.card_map_of_injective R₁.subtype_injective, mul_comm]
    exact (Subgroup.card_ker_mul_card_range ψ).symm

theorem odd_subgroup_bound {G : Type} [Group G] [Finite G]
    (Hh M I F₀ A : Subgroup G) (y u : G) (e : ℕ) (he : 0 < e)
    (hM : M ≤ Hh) (hI : I ≤ Hh) (hF₀ : F₀ ≤ Hh) (hy : y ∈ Hh) (hA : A ≤ M)
    (hMn : ∀ c ∈ Hh, ∀ m ∈ M, c * m * c⁻¹ ∈ M) (hIn : ∀ c ∈ Hh, ∀ i ∈ I, c * i * c⁻¹ ∈ I)
    (hMI : ∀ m ∈ M, ∀ i ∈ I, m * i = i * m) (hMIinf : M ⊓ I = ⊥)
    (hgen : ∀ c ∈ Hh, ∃ m ∈ M, ∃ i ∈ I, ∃ f ∈ F₀, ∃ ε : ℕ, c = m * i * y ^ ε * f)
    (hy2 : y * y = 1) (hF₀odd : Odd (Nat.card ↥F₀))
    (hModd : ∀ P : Subgroup G, P ≤ M → Odd (Nat.card ↥P) → P ≤ A)
    (huI : u ∈ I)
    (hCI : ∀ P : Subgroup G, P ≤ I → (∀ p ∈ P, p * u = u * p) → Odd (Nat.card ↥P) →
      Nat.card ↥P ∣ e)
    (R : Subgroup G) (hRH : R ≤ Hh) (hRu : ∀ r ∈ R, r * u = u * r) (hRodd : Odd (Nat.card ↥R)) :
    Nat.card ↥R ≤ Nat.card ↥A * e * Nat.card ↥F₀ := by
  have _ := And.intro hM (And.intro hI (And.intro hA hF₀odd))
  obtain ⟨N, hN⟩ := cnt_exists_mul_subgroup M I (fun i hi m hm => by
    have h : i * m * i⁻¹ = m := by rw [← hMI m hm i hi, mul_inv_cancel_right]
    rw [h]
    exact hm)
  have hNH : ∀ c ∈ Hh, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    obtain ⟨m, hm, i, hi, rfl⟩ := (hN n).1 hn
    refine (hN _).2 ⟨c * m * c⁻¹, hMn c hc m hm, c * i * c⁻¹, hIn c hc i hi, ?_⟩
    group
  obtain ⟨K, hK⟩ := cnt_exists_mul_subgroup N F₀ (fun f hf n hn => hNH f (hF₀ hf) n hn)
  have hcov : ∀ c ∈ Hh, c ∈ K ∨ ∃ z ∈ K, c = y * z := by
    intro c hc
    obtain ⟨m, hm, i, hi, f, hf, ε, rfl⟩ := hgen c hc
    have hmiN : m * i ∈ N := (hN _).2 ⟨m, hm, i, hi, rfl⟩
    rcases Nat.even_or_odd ε with hev | hod
    · left
      have hyε : y ^ ε = 1 := by
        obtain ⟨k, rfl⟩ := hev
        rw [← two_mul, pow_mul, sq, hy2, one_pow]
      refine (hK _).2 ⟨m * i, hmiN, f, hf, ?_⟩
      rw [hyε, mul_one]
    · right
      have hyε : y ^ ε = y := by
        obtain ⟨k, rfl⟩ := hod
        rw [pow_succ, pow_mul, sq, hy2, one_pow, one_mul]
      refine ⟨y⁻¹ * (m * i) * y * f, (hK _).2 ⟨y⁻¹ * (m * i) * y, ?_, f, hf, rfl⟩, ?_⟩
      · have := hNH y⁻¹ (Hh.inv_mem hy) _ hmiN
        rwa [inv_inv] at this
      · rw [hyε]
        group
  have hRK : R ≤ K := cnt_odd_le_of_cover Hh K R y hy hcov hRH hRodd
  have hdec : ∀ r : R, ∃ f : F₀, ∃ n ∈ N, (r : G) = n * f := by
    intro r
    obtain ⟨n, hn, f, hf, h⟩ := (hK _).1 (hRK r.2)
    exact ⟨⟨f, hf⟩, n, hn, h⟩
  choose φ hφ using hdec
  have hfiber : ∀ r s : R, φ r = φ s → (r : G)⁻¹ * s ∈ N := by
    intro r s hrs
    obtain ⟨n, hn, hr⟩ := hφ r
    obtain ⟨n', hn', hs⟩ := hφ s
    rw [hrs] at hr
    have hfH : ((φ s : F₀) : G) ∈ Hh := hF₀ (φ s).2
    have h1 := hNH ((φ s : F₀) : G)⁻¹ (Hh.inv_mem hfH) (n⁻¹ * n') (N.mul_mem (N.inv_mem hn) hn')
    rw [inv_inv] at h1
    have h2 : (r : G)⁻¹ * s = ((φ s : F₀) : G)⁻¹ * (n⁻¹ * n') * ((φ s : F₀) : G) := by
      rw [hr, hs]
      group
    rw [h2]
    exact h1
  have hB2 : Nat.card R ≤ Nat.card F₀ * Nat.card ↥(R ⊓ N) := cnt_card_le_mul_card_inf R N φ hfiber
  have hR₁ : ∀ x ∈ R ⊓ N, ∃ m ∈ M, ∃ i ∈ I, x = m * i := fun x hx => (hN x).1 hx.2
  obtain ⟨P, Z, hPI, hZM, _, hP, hcard⟩ := cnt_exists_prod_split M I (R ⊓ N) hMI hMIinf hR₁
  have hR₁odd : Odd (Nat.card ↥(R ⊓ N)) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hPZodd : Odd (Nat.card P) ∧ Odd (Nat.card Z) := by
    rw [hcard] at hR₁odd
    exact Nat.odd_mul.1 hR₁odd
  have hZle : Nat.card Z ≤ Nat.card A := Subgroup.card_le_of_le (hModd Z hZM hPZodd.2)
  have hPcomm : ∀ p ∈ P, p * u = u * p := by
    intro p hp
    obtain ⟨m, hm, hmp⟩ := hP p hp
    have h1 : m * p * u = u * (m * p) := hRu _ hmp.1
    have h2 : m * u = u * m := hMI m hm u huI
    apply mul_left_cancel (a := m)
    calc m * (p * u) = m * p * u := (mul_assoc _ _ _).symm
      _ = u * (m * p) := h1
      _ = u * m * p := (mul_assoc _ _ _).symm
      _ = m * u * p := by rw [h2]
      _ = m * (u * p) := mul_assoc _ _ _
  have hPle : Nat.card P ≤ e := Nat.le_of_dvd he (hCI P hPI hPcomm hPZodd.1)
  calc Nat.card R ≤ Nat.card F₀ * Nat.card ↥(R ⊓ N) := hB2
    _ = Nat.card F₀ * (Nat.card P * Nat.card Z) := by rw [hcard]
    _ ≤ Nat.card F₀ * (e * Nat.card A) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hPle hZle)
    _ = Nat.card A * e * Nat.card F₀ := by ring

end CFSG.GH74.GLS.SP.Local

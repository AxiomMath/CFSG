module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutBfs

public section

namespace CFSG.KS.Asc82Syl

variable {Γ : Type*} [Group Γ]

def subOfMul [Finite Γ] (s : Set Γ) (h1 : (1 : Γ) ∈ s) (hm : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) :
    Subgroup Γ where
  carrier := s
  one_mem' := h1
  mul_mem' := fun hx hy => hm _ hx _ hy
  inv_mem' := by
    intro x hx
    let M : Submonoid Γ := { carrier := s, mul_mem' := fun hx hy => hm _ hx _ hy, one_mem' := h1 }
    have hp : x ^ (orderOf x - 1) ∈ M := M.pow_mem hx _
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [e]
    exact hp

theorem core_bound {n q : ℕ} (e : Fin n → Γ) (mul : Fin n → Fin n → Fin n) (one : Fin n)
    (isE : Fin n → Prop) (he : Function.Injective e) (hes : Function.Surjective e)
    (hone : e one = 1) (hmul : ∀ i j, e (mul i j) = e i * e j)
    (hE1 : isE one) (hEm : ∀ i j, isE i → isE j → isE (mul i j))
    (hEc : ∀ i j, isE i → isE j → e i * e j = e j * e i)
    (hEn : ∀ i j, isE i → ∃ c, isE c ∧ e i * e j = e j * e c)
    (π : Fin n → Fin q) (rep : Fin q → Fin n)
    (hsplit : ∀ i, ∃ c, isE c ∧ e i = e c * e (rep (π i)))
    (hrep : ∀ u v c, isE c → e (rep v) = e c * e (rep u) → u = v)
    (qmQ : Fin q → Fin q → Fin q) (hqm : ∀ u v, π (mul (rep u) (rep v)) = qmQ u v)
    {l : ℕ} (hq : q = 2 ^ l) (𝓛 : Set (Finset (Fin q))) (h0 : {π one} ∈ 𝓛)
    (h2 : ∀ X ∈ 𝓛, ∀ x : Fin q, x ∉ X → qmQ x x ∈ X → (∀ h ∈ X, qmQ x h = qmQ h x) →
      X ∪ X.image (qmQ x) ∈ 𝓛)
    (flag : Bool) (bound : ℕ)
    (hbound : ∀ X ∈ 𝓛, ∃ gens : Finset (Fin q), gens ⊆ X ∧ ∃ C : Finset (Fin n),
      (∀ c, isE c → (∀ g ∈ gens, e c * e (rep g) = e (rep g) * e c) →
        (flag = true → e c * e c = 1) → c ∈ C) ∧ C.card * X.card ≤ bound)
    (H : Finset (Fin n)) (h1H : one ∈ H) (hmH : ∀ a ∈ H, ∀ b ∈ H, mul a b ∈ H)
    (hcH : ∀ a ∈ H, ∀ b ∈ H, mul a b = mul b a) (hfH : flag = true → ∀ a ∈ H, mul a a = one) :
    H.card ≤ bound := by
  classical
  have : Finite Γ := Finite.of_surjective e hes
  let E : Subgroup Γ := subOfMul {x | ∃ c, isE c ∧ e c = x} ⟨one, hE1, hone⟩ (by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact ⟨mul i j, hEm i j hi hj, hmul i j⟩)
  have hmemE : ∀ x, x ∈ E ↔ ∃ c, isE c ∧ e c = x := fun x => Iff.rfl
  have hEN : E.Normal := ⟨by
    intro x hx g
    obtain ⟨i, hi, rfl⟩ := (hmemE x).1 hx
    obtain ⟨j, hj⟩ := hes g⁻¹
    obtain ⟨c, hc, hce⟩ := hEn i j hi
    refine (hmemE _).2 ⟨c, hc, ?_⟩
    rw [← inv_inv g, ← hj, inv_inv, mul_assoc, hce, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  let eQ : Fin q → Γ ⧸ E := fun u => ((e (rep u) : Γ) : Γ ⧸ E)
  have hmk : ∀ i, ((e i : Γ) : Γ ⧸ E) = eQ (π i) := by
    intro i
    obtain ⟨c, hc, hce⟩ := hsplit i
    change ((e i : Γ) : Γ ⧸ E) = ((e (rep (π i)) : Γ) : Γ ⧸ E)
    rw [QuotientGroup.eq, hce]
    have h := hEN.conj_mem _ (E.inv_mem ((hmemE _).2 ⟨c, hc, rfl⟩)) (e (rep (π i)))⁻¹
    simpa [mul_assoc] using h
  have hinj : Function.Injective eQ := by
    intro u v h
    have h' := QuotientGroup.eq.1 h
    obtain ⟨c, hc, hce⟩ := (hmemE _).1 h'
    obtain ⟨c', hc', hce'⟩ := (hmemE _).1 (hEN.conj_mem _ ((hmemE _).2 ⟨c, hc, rfl⟩) (e (rep u)))
    refine hrep u v c' hc' ?_
    rw [hce', hce]
    group
  have hsurj : Function.Surjective eQ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨i, rfl⟩ := hes g
    exact ⟨π i, (hmk i).symm⟩
  have hcard : Nat.card (Γ ⧸ E) = 2 ^ l := by
    rw [← Nat.card_eq_of_bijective eQ ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card, Fintype.card_fin, hq]
  have hQp : IsPGroup 2 (Γ ⧸ E) := IsPGroup.of_card hcard
  have hQone : eQ (π one) = 1 := by
    rw [← hmk, hone]
    rfl
  have hQmul : ∀ u v, eQ (qmQ u v) = eQ u * eQ v := by
    intro u v
    rw [← hqm, ← hmk, hmul]
    rfl
  let A : Subgroup Γ := subOfMul {x | ∃ h ∈ H, e h = x} ⟨one, h1H, hone⟩ (by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact ⟨mul i j, hmH i hi j hj, hmul i j⟩)
  have hmemA : ∀ x, x ∈ A ↔ ∃ h ∈ H, e h = x := fun x => Iff.rfl
  let K : Subgroup (Γ ⧸ E) := A.map (QuotientGroup.mk' E)
  have hK : ∀ y ∈ K, ∃ u, eQ u = y := fun y _ => hsurj y
  have hKc : ∀ y ∈ K, ∀ z ∈ K, y * z = z * y := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (hmemA a).1 ha
    obtain ⟨j, hj, rfl⟩ := (hmemA b).1 hb
    change ((e i * e j : Γ) : Γ ⧸ E) = ((e j * e i : Γ) : Γ ⧸ E)
    rw [← hmul, ← hmul, hcH i hi j hj]
  obtain ⟨X, hX, hXmem⟩ := CFSG.OddStandard.SmallF3.Omega.ffRA_bfs_abelian_mem eQ hinj (π one)
    hQone qmQ hQmul 𝓛 h0 h2 hK (hQp.to_subgroup K) hKc
  have hXH : X = H.image π := by
    ext u
    rw [hXmem, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hau⟩
      obtain ⟨i, hi, rfl⟩ := (hmemA a).1 ha
      refine ⟨i, hi, hinj ?_⟩
      rw [← hmk]
      exact hau
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, (hmemA _).2 ⟨i, hi, rfl⟩, hmk i⟩
  obtain ⟨gens, hgX, C, hC, hCb⟩ := hbound X hX
  have hfib : ∀ u ∈ H.image π, (H.filter fun a => π a = u).card ≤ C.card := by
    intro u hu
    obtain ⟨h0, h0H, rfl⟩ := Finset.mem_image.1 hu
    let f : Fin n → Fin n := fun h => (hes ((e h0)⁻¹ * e h)).choose
    have hf : ∀ h, e (f h) = (e h0)⁻¹ * e h := fun h => (hes ((e h0)⁻¹ * e h)).choose_spec
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro h hh
      obtain ⟨hH, hπ⟩ := Finset.mem_filter.1 hh
      have hE : e (f h) ∈ E := by
        rw [hf]
        refine QuotientGroup.eq.1 ?_
        rw [hmk, hmk, hπ]
      obtain ⟨c, hc, hce⟩ := (hmemE _).1 hE
      have hcf : c = f h := he hce
      have hA : e (f h) ∈ A := by
        rw [hf]
        exact A.mul_mem (A.inv_mem ((hmemA _).2 ⟨h0, h0H, rfl⟩)) ((hmemA _).2 ⟨h, hH, rfl⟩)
      obtain ⟨c2, hc2, hce2⟩ := (hmemA _).1 hA
      have hc2f : c2 = f h := he hce2
      have hcE : isE (f h) := hcf ▸ hc
      have hcmem : f h ∈ H := hc2f ▸ hc2
      refine hC (f h) hcE (fun g hg => ?_) (fun hfl => ?_)
      · have hgX' : g ∈ X := hgX hg
        rw [hXH, Finset.mem_image] at hgX'
        obtain ⟨h1, h1H, rfl⟩ := hgX'
        obtain ⟨c1, hc1, hce1⟩ := hsplit h1
        have hr : e (rep (π h1)) = (e c1)⁻¹ * e h1 := by
          rw [hce1, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [hr]
        have k1 : Commute (e (f h)) (e c1) := hEc (f h) c1 hcE hc1
        have k2 : Commute (e (f h)) (e h1) := by
          change e (f h) * e h1 = e h1 * e (f h)
          rw [← hmul, ← hmul, hcH (f h) hcmem h1 h1H]
        exact (k1.inv_right.mul_right k2).eq
      · rw [← hmul, hfH hfl (f h) hcmem, hone]
    · intro h hh h' hh' hff
      have := congrArg e hff
      rw [hf, hf] at this
      exact he (mul_left_cancel this)
  calc H.card ≤ C.card * (H.image π).card := Finset.card_le_mul_card_image H C.card hfib
    _ = C.card * X.card := by rw [hXH]
    _ ≤ bound := hCb

section Table

variable {n : ℕ} (mul : Fin n → Fin n → Fin n) (one : Fin n)
  (assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)) (one_mul' : ∀ a, mul one a = a)
  (mul_one' : ∀ a, mul a one = a) (lcancel : ∀ a b b', mul a b = mul a b' → b = b')

noncomputable def lmul (a : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (mul a) (Finite.injective_iff_bijective.1 (fun b b' h => lcancel a b b' h))

include assoc in
theorem lmul_mul (a b : Fin n) :
    lmul mul lcancel (mul a b) = lmul mul lcancel a * lmul mul lcancel b := by
  ext c
  simp only [lmul, Equiv.Perm.mul_apply, Equiv.ofBijective_apply]
  rw [assoc]

noncomputable def lmulGrp : Subgroup (Equiv.Perm (Fin n)) :=
  subOfMul (Set.range (lmul mul lcancel)) ⟨one, by
    ext c
    simp only [lmul, Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq]
    rw [one_mul']⟩ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨mul a b, lmul_mul mul assoc lcancel a b⟩)

include assoc one_mul' mul_one' lcancel in
theorem core_table {q : ℕ} (isE : Fin n → Prop) (hE1 : isE one)
    (hEm : ∀ i j, isE i → isE j → isE (mul i j))
    (hEc : ∀ i j, isE i → isE j → mul i j = mul j i)
    (hEn : ∀ i j, isE i → ∃ c, isE c ∧ mul i j = mul j c)
    (π : Fin n → Fin q) (rep : Fin q → Fin n)
    (hsplit : ∀ i, ∃ c, isE c ∧ i = mul c (rep (π i)))
    (hrep : ∀ u v c, isE c → rep v = mul c (rep u) → u = v)
    (qmQ : Fin q → Fin q → Fin q) (hqm : ∀ u v, π (mul (rep u) (rep v)) = qmQ u v)
    {l : ℕ} (hq : q = 2 ^ l) (𝓛 : Set (Finset (Fin q))) (h0 : {π one} ∈ 𝓛)
    (h2 : ∀ X ∈ 𝓛, ∀ x : Fin q, x ∉ X → qmQ x x ∈ X → (∀ h ∈ X, qmQ x h = qmQ h x) →
      X ∪ X.image (qmQ x) ∈ 𝓛)
    (flag : Bool) (bound : ℕ)
    (hbound : ∀ X ∈ 𝓛, ∃ gens : Finset (Fin q), gens ⊆ X ∧ ∃ C : Finset (Fin n),
      (∀ c, isE c → (∀ g ∈ gens, mul c (rep g) = mul (rep g) c) →
        (flag = true → mul c c = one) → c ∈ C) ∧ C.card * X.card ≤ bound)
    (H : Finset (Fin n)) (h1H : one ∈ H) (hmH : ∀ a ∈ H, ∀ b ∈ H, mul a b ∈ H)
    (hcH : ∀ a ∈ H, ∀ b ∈ H, mul a b = mul b a) (hfH : flag = true → ∀ a ∈ H, mul a a = one) :
    H.card ≤ bound := by
  let G := lmulGrp mul one assoc one_mul' lcancel
  let e : Fin n → G := fun a => ⟨lmul mul lcancel a, a, rfl⟩
  have hmul : ∀ i j, e (mul i j) = e i * e j := fun i j =>
    Subtype.ext (lmul_mul mul assoc lcancel i j)
  have he : Function.Injective e := by
    intro a b h
    have h1 := congrArg (fun g : G => (g : Equiv.Perm (Fin n)) one) h
    simp only [e, lmul, Equiv.ofBijective_apply] at h1
    rw [mul_one', mul_one'] at h1
    exact h1
  have hes : Function.Surjective e := by
    rintro ⟨g, a, rfl⟩
    exact ⟨a, rfl⟩
  have hone : e one = 1 := by
    apply Subtype.ext
    ext c
    simp only [e, lmul, Equiv.ofBijective_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    rw [one_mul']
  have hcomm : ∀ i j, mul i j = mul j i → e i * e j = e j * e i := by
    intro i j h
    rw [← hmul, ← hmul, h]
  refine core_bound e mul one isE he hes hone hmul hE1 hEm (fun i j hi hj => hcomm i j
    (hEc i j hi hj)) (fun i j hi => ?_) π rep (fun i => ?_) (fun u v c hc h => ?_) qmQ hqm hq 𝓛
    h0 h2 flag bound (fun X hX => ?_) H h1H hmH hcH hfH
  · obtain ⟨c, hc, h⟩ := hEn i j hi
    exact ⟨c, hc, by rw [← hmul, ← hmul, h]⟩
  · obtain ⟨c, hc, h⟩ := hsplit i
    exact ⟨c, hc, by rw [← hmul, ← h]⟩
  · rw [← hmul] at h
    exact hrep u v c hc (he h)
  · obtain ⟨gens, hg, C, hC, hb⟩ := hbound X hX
    refine ⟨gens, hg, C, fun c hc hcg hcf => hC c hc (fun g hgg => he ?_) (fun hf => he ?_), hb⟩
    · rw [hmul, hmul]
      exact hcg g hgg
    · rw [hmul, hone]
      exact hcf hf

end Table

end CFSG.KS.Asc82Syl

end

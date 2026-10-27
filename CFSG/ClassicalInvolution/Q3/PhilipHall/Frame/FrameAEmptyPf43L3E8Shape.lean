module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf12L3E8
public import CFSG.ClassicalInvolution.Generic.Frame
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped Matrix

structure FaithfulL3E8 (X : Type) [Group X] (E : Subgroup X) : Prop where
  normal : E.Normal
  elemAbelian : IsElemAbelian 2 E
  card : Nat.card E = 8
  centralizer : Subgroup.centralizer (E : Set X) = E
  quotient : Nonempty ((X ⧸ E) ≃* L3Two)

@[expose] def IsFaithfulL3E8 (X : Type) [Group X] : Prop := ∃ E : Subgroup X, FaithfulL3E8 X E

section Shape

variable {X : Type} [Group X]

theorem l3Two_no_q8 : ∀ i j : L3Two, i * i = j * j → i * i ≠ 1 → j * i * j⁻¹ = i⁻¹ → False := by
  decide +kernel

private def l3Inv : L3Two := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

private theorem l3Two_involutions_conj_inv :
    ∀ a : L3Two, a * a = 1 → a ≠ 1 → ∃ g : L3Two, g * a * g⁻¹ = l3Inv := by
  decide +kernel

theorem l3Two_involutions_conj : ∀ a b : L3Two, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
    ∃ g : L3Two, g * a * g⁻¹ = b := by
  intro a b ha ha1 hb hb1
  obtain ⟨g, hg⟩ := l3Two_involutions_conj_inv a ha ha1
  obtain ⟨h, hh⟩ := l3Two_involutions_conj_inv b hb hb1
  refine ⟨h⁻¹ * g, ?_⟩
  calc h⁻¹ * g * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
    _ = h⁻¹ * l3Inv * h := by rw [hg]
    _ = b := by rw [← hh]; group

private theorem l3Two_card : Nat.card L3Two = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem l3_transitive : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ M : L3Two, (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = w := by
  decide +kernel

private theorem l3_invol : ∀ M : L3Two, M * M = 1 → M ≠ 1 →
    (Finset.univ.filter (fun w : Fin 3 → ZMod 2 =>
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w)).card ≤ 4 := by
  decide +kernel

private theorem l3_three : ∀ M : L3Two, M * M * M = 1 →
    (Finset.univ.filter (fun w : Fin 3 → ZMod 2 =>
      ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
        (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) + 1) *ᵥ w = 0)).card ≤ 4 := by
  decide +kernel

private def gA : L3Two := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

private def gB : L3Two := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

private theorem gA_sq : gA * gA = 1 := by decide

private theorem gA_ne : gA ≠ 1 := by decide

private theorem gB_cube : gB * gB * gB = 1 := by decide

private theorem gB_ne : gB ≠ 1 := by decide

private theorem gAB_pow : (gA * gB) ^ 7 = 1 := by decide +kernel

private theorem gAB_ne : gA * gB ≠ 1 := by decide

private theorem gen_closure : Subgroup.closure ({gA, gB} : Set L3Two) = ⊤ := by
  set H := Subgroup.closure ({gA, gB} : Set L3Two) with hH
  haveI : IsSimpleGroup L3Two := isSimpleGroup_l3Two
  have hA : gA ∈ H := Subgroup.subset_closure (by simp)
  have hB : gB ∈ H := Subgroup.subset_closure (by simp)
  have hAB : gA * gB ∈ H := H.mul_mem hA hB
  have o2 : orderOf gA = 2 := orderOf_eq_prime (by rw [sq]; exact gA_sq) gA_ne
  have o3 : orderOf gB = 3 := orderOf_eq_prime (by rw [pow_succ, sq]; exact gB_cube) gB_ne
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have o7 : orderOf (gA * gB) = 7 := orderOf_eq_prime gAB_pow gAB_ne
  have d2 : 2 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hA
    rwa [o2] at this
  have d3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hB
    rwa [o3] at this
  have d7 : 7 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hAB
    rwa [o7] at this
  have h42 : 42 ∣ Nat.card H := by omega
  have hge : 42 ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos h42
  have hcard : Nat.card H * H.index = 168 := by rw [Subgroup.card_mul_index, l3Two_card]
  by_contra hne
  have hidx4 : H.index ≤ 4 := by
    by_contra h5
    have h5' : 5 ≤ H.index := by omega
    have : 42 * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul hge h5'
    omega
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hbot | htop
  · have h1 := H.index_normalCore_dvd_factorial_index
    rw [hbot, Subgroup.index_bot, l3Two_card] at h1
    have h2 : 168 ≤ Nat.factorial H.index := Nat.le_of_dvd (Nat.factorial_pos _) h1
    have h3 : Nat.factorial H.index ≤ Nat.factorial 4 := Nat.factorial_le hidx4
    have h4 : Nat.factorial 4 = 24 := by decide
    omega
  · apply hne
    rw [eq_top_iff]
    calc (⊤ : Subgroup L3Two) = H.normalCore := htop.symm
      _ ≤ H := H.normalCore_le

private theorem elem_comm {E : Subgroup X} (hE : IsElemAbelian 2 E) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have := hE.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

private theorem elem_sq {E : Subgroup X} (hE : IsElemAbelian 2 E) {a : X} (ha : a ∈ E) :
    a * a = 1 := by
  simpa [sq] using hE.2 a ha

private theorem elem_inv {E : Subgroup X} (hE : IsElemAbelian 2 E) {a : X} (ha : a ∈ E) :
    a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (elem_sq hE ha)

private def toL3 {E : Subgroup X} [E.Normal] (e : (X ⧸ E) ≃* L3Two) : X →* L3Two :=
  e.toMonoidHom.comp (QuotientGroup.mk' E)

private theorem toL3_eq_one_iff {E : Subgroup X} [E.Normal] (e : (X ⧸ E) ≃* L3Two) (x : X) :
    toL3 e x = 1 ↔ x ∈ E := by
  show e (QuotientGroup.mk' E x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

private theorem toL3_surjective {E : Subgroup X} [E.Normal] (e : (X ⧸ E) ≃* L3Two) :
    Function.Surjective (toL3 e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective E)

private theorem q8_exists_unique {P : Subgroup X} (hP : Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∃ z, IsUniqueInvolution P z := by
  obtain ⟨φ⟩ := hP
  obtain ⟨w, hw⟩ : ∃ w : P, φ w = QuaternionGroup.a 2 := ⟨φ.symm _, φ.apply_symm_apply _⟩
  refine ⟨(w : X), w.2, ?_, ?_, ?_⟩
  · intro h
    have h1 : w = 1 := Subtype.ext h
    have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by rw [← hw, h1, map_one]
    exact absurd h2 (by decide)
  · have h1 : w * w = 1 := by
      apply φ.injective
      rw [map_mul, map_one, hw]
      decide
    exact congrArg Subtype.val h1
  · intro y hy hy2
    have h1 : (⟨y, hy⟩ : P) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    have h2 : φ ⟨y, hy⟩ * φ ⟨y, hy⟩ = 1 := by rw [← map_mul, h1, map_one]
    have h4 : ∀ g : QuaternionGroup 2, g * g = 1 → g = 1 ∨ g = QuaternionGroup.a 2 := by decide
    rcases h4 _ h2 with h3 | h3
    · left
      have : (⟨y, hy⟩ : P) = 1 := φ.injective (by rw [h3, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨y, hy⟩ : P) = w := φ.injective (by rw [h3, hw])
      exact congrArg Subtype.val this

private theorem q8_data {P : Subgroup X} {z : X} (hP : Nonempty (↥P ≃* QuaternionGroup 2))
    (hz : IsUniqueInvolution P z) :
    ∃ a b : X, a ∈ P ∧ b ∈ P ∧ a * a = z ∧ b * b = z ∧ a * b * (a * b) = z ∧
      b * a * b⁻¹ = a⁻¹ ∧ b * a = a * b⁻¹ ∧ a * b * a = a * (a * b)⁻¹ := by
  obtain ⟨φ⟩ := hP
  obtain ⟨zP, hzP⟩ : ∃ w : P, φ w = QuaternionGroup.a 2 := ⟨φ.symm _, φ.apply_symm_apply _⟩
  obtain ⟨a, ha⟩ : ∃ w : P, φ w = QuaternionGroup.a 1 := ⟨φ.symm _, φ.apply_symm_apply _⟩
  obtain ⟨b, hb⟩ : ∃ w : P, φ w = QuaternionGroup.xa 0 := ⟨φ.symm _, φ.apply_symm_apply _⟩
  have hzz : (zP : X) = z := by
    have h1 : zP * zP = 1 := by
      apply φ.injective
      rw [map_mul, map_one, hzP]
      decide
    have h2 : (zP : X) ≠ 1 := by
      intro h
      have h1' : zP = 1 := Subtype.ext h
      have h2' : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by rw [← hzP, h1', map_one]
      exact absurd h2' (by decide)
    rcases hz.unique _ zP.2 (congrArg Subtype.val h1) with h | h
    · exact absurd h h2
    · exact h
  have e1 : a * a = zP := by
    apply φ.injective; rw [map_mul, ha, hzP]; decide
  have e2 : b * b = zP := by
    apply φ.injective; rw [map_mul, hb, hzP]; decide
  have e3 : a * b * (a * b) = zP := by
    apply φ.injective; simp only [map_mul, ha, hb, hzP]; decide
  have e4 : b * a * b⁻¹ = a⁻¹ := by
    apply φ.injective; simp only [map_mul, map_inv, ha, hb]; decide
  have e5 : b * a = a * b⁻¹ := by
    apply φ.injective; simp only [map_mul, map_inv, ha, hb]; decide
  have e6 : a * b * a = a * (a * b)⁻¹ := by
    apply φ.injective; simp only [map_mul, map_inv, ha, hb]; decide
  refine ⟨a, b, a.2, b.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val e1; rw [hzz] at this; exact this
  · have := congrArg Subtype.val e2; rw [hzz] at this; exact this
  · have := congrArg Subtype.val e3; rw [hzz] at this; exact this
  · exact congrArg Subtype.val e4
  · exact congrArg Subtype.val e5
  · exact congrArg Subtype.val e6

private theorem q8_mem_E {E : Subgroup X} [E.Normal] (e : (X ⧸ E) ≃* L3Two) {P : Subgroup X}
    {z : X} (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution P z) : z ∈ E := by
  obtain ⟨a, b, -, -, haa, hbb, -, hbab, -, -⟩ := q8_data hP hz
  by_contra hzE
  refine l3Two_no_q8 (toL3 e a) (toL3 e b) ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, haa, hbb]
  · rw [← map_mul, haa]
    exact fun h => hzE ((toL3_eq_one_iff e z).1 h)
  · have := congrArg (toL3 e) hbab
    simpa only [map_mul, map_inv] using this

private theorem three_elems {H : Type*} [Finite H] (hH : Nat.card H ≤ 2) (a b c : H) :
    a = b ∨ a = c ∨ b = c := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  have hinj : Function.Injective (![a, b, c] : Fin 3 → H) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

private theorem orderOf_eq_four {k z : X} (hk : k * k = z) (hz1 : z ≠ 1) (hzz : z * z = 1) :
    orderOf k = 4 := by
  have h2 : k ^ 2 = z := by rw [sq, hk]
  have h4 : k ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq]
    exact hzz
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := k) (by simpa [h2] using hz1)
    (by simpa using h4)
  simpa using this

private theorem commute_of_F {a n z ε : X} (hnn : n * n = z) (hzz : z * z = 1)
    (hna : n * a = a * n⁻¹) (hεε : ε * ε = 1) (hF : n⁻¹ * ε * n * ε = z) :
    a * ε * n = n * (a * ε) := by
  have hnz : n * z = n⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc n * z * n = (n * n) * (n * n) := by rw [← hnn]; group
      _ = 1 := by rw [hnn, hzz]
  have h1 : n⁻¹ * ε * n = z * ε := by
    calc n⁻¹ * ε * n = n⁻¹ * ε * n * (ε * ε) := by rw [hεε, mul_one]
      _ = (n⁻¹ * ε * n * ε) * ε := by group
      _ = z * ε := by rw [hF]
  have h2 : ε * n = n⁻¹ * ε := by
    calc ε * n = n * (n⁻¹ * ε * n) := by group
      _ = n * (z * ε) := by rw [h1]
      _ = (n * z) * ε := by group
      _ = n⁻¹ * ε := by rw [hnz]
  calc a * ε * n = a * (ε * n) := by group
    _ = a * (n⁻¹ * ε) := by rw [h2]
    _ = (a * n⁻¹) * ε := by group
    _ = (n * a) * ε := by rw [hna]
    _ = n * (a * ε) := by group

private theorem F_mul {a b z ε : X} (hzb : z * b = b * z) (hFa : a⁻¹ * ε * a * ε = z)
    (hεε : ε * ε = 1) :
    (a * b)⁻¹ * ε * (a * b) * ε = z * (b⁻¹ * ε * b * ε) := by
  have e1 : a⁻¹ * ε * a = z * ε := by
    calc a⁻¹ * ε * a = a⁻¹ * ε * a * (ε * ε) := by rw [hεε, mul_one]
      _ = (a⁻¹ * ε * a * ε) * ε := by group
      _ = z * ε := by rw [hFa]
  have hzb' : b⁻¹ * z = z * b⁻¹ := by
    calc b⁻¹ * z = b⁻¹ * (z * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * z) * b⁻¹ := by rw [hzb]
      _ = z * b⁻¹ := by group
  calc (a * b)⁻¹ * ε * (a * b) * ε = b⁻¹ * (a⁻¹ * ε * a) * b * ε := by group
    _ = b⁻¹ * (z * ε) * b * ε := by rw [e1]
    _ = (b⁻¹ * z) * ε * b * ε := by group
    _ = (z * b⁻¹) * ε * b * ε := by rw [hzb']
    _ = z * (b⁻¹ * ε * b * ε) := by group

private theorem comm_set_le_two {E : Subgroup X} [E.Normal] (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 8) {b : X} (hb : b * b ∈ E) {ε₀ : X} (hε₀ : ε₀ ∈ E)
    (hne : b⁻¹ * ε₀ * b * ε₀ ≠ 1) :
    ∀ ε ∈ E, b⁻¹ * ε * b * ε = 1 ∨ b⁻¹ * ε * b * ε = b⁻¹ * ε₀ * b * ε₀ := by
  intro ε hε
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hconj : ∀ x ∈ E, b⁻¹ * x * b ∈ E := fun x hx => by
    simpa using ‹E.Normal›.conj_mem x hx b⁻¹
  have hmem : ∀ x ∈ E, b⁻¹ * x * b * x ∈ E := fun x hx => E.mul_mem (hconj x hx) hx
  let F : E →* E := MonoidHom.mk' (fun x => ⟨b⁻¹ * x * b * x, hmem x x.2⟩) (by
    intro x y
    apply Subtype.ext
    show b⁻¹ * ((x : X) * y) * b * ((x : X) * y) = (b⁻¹ * x * b * x) * (b⁻¹ * y * b * y)
    have hc : (x : X) * (b⁻¹ * y * b) = (b⁻¹ * y * b) * x :=
      elem_comm hE x.2 (hconj y y.2)
    calc b⁻¹ * ((x : X) * y) * b * ((x : X) * y)
        = (b⁻¹ * x * b) * (b⁻¹ * y * b) * x * y := by group
      _ = (b⁻¹ * x * b) * ((b⁻¹ * y * b) * x) * y := by group
      _ = (b⁻¹ * x * b) * (x * (b⁻¹ * y * b)) * y := by rw [hc]
      _ = (b⁻¹ * x * b * x) * (b⁻¹ * y * b * y) := by group)
  have hFF : ∀ x : E, F (F x) = 1 := by
    intro x
    apply Subtype.ext
    show b⁻¹ * (b⁻¹ * (x : X) * b * x) * b * (b⁻¹ * (x : X) * b * x) = 1
    have hpE : b⁻¹ * (x : X) * b ∈ E := hconj x x.2
    have h1 : b⁻¹ * (b⁻¹ * (x : X) * b) * b = x := by
      have hc := elem_comm hE hb x.2
      calc b⁻¹ * (b⁻¹ * (x : X) * b) * b = (b * b)⁻¹ * (x * (b * b)) := by group
        _ = (b * b)⁻¹ * ((b * b) * x) := by rw [hc]
        _ = x := by group
    calc b⁻¹ * (b⁻¹ * (x : X) * b * x) * b * (b⁻¹ * (x : X) * b * x)
        = (b⁻¹ * (b⁻¹ * (x : X) * b) * b) * (b⁻¹ * (x : X) * b) * ((b⁻¹ * (x : X) * b) * x) := by
          group
      _ = x * (b⁻¹ * (x : X) * b) * ((b⁻¹ * (x : X) * b) * x) := by rw [h1]
      _ = x * ((b⁻¹ * (x : X) * b) * (b⁻¹ * (x : X) * b)) * x := by group
      _ = x * x := by rw [elem_sq hE hpE]; group
      _ = 1 := elem_sq hE x.2
  have hle : F.range ≤ F.ker := by
    rintro _ ⟨x, rfl⟩
    exact hFF x
  have hcard1 := Subgroup.card_ker_mul_card_range F
  have hle1 : Nat.card F.range ≤ Nat.card F.ker := Subgroup.card_le_of_le hle
  have hle2 : Nat.card F.range ≤ 2 := by
    rw [hcard] at hcard1
    by_contra hr
    push Not at hr
    have h3 : 3 ≤ Nat.card F.ker := le_trans hr hle1
    nlinarith
  have hs : F ⟨ε, hε⟩ ∈ F.range := ⟨⟨ε, hε⟩, rfl⟩
  have hs₀ : F ⟨ε₀, hε₀⟩ ∈ F.range := ⟨⟨ε₀, hε₀⟩, rfl⟩
  rcases three_elems hle2 (1 : F.range) ⟨F ⟨ε₀, hε₀⟩, hs₀⟩ ⟨F ⟨ε, hε⟩, hs⟩ with h | h | h
  · exfalso
    exact hne (congrArg (fun t : F.range => (((t : F.range) : E) : X)) h).symm
  · left
    exact (congrArg (fun t : F.range => (((t : F.range) : E) : X)) h).symm
  · right
    exact (congrArg (fun t : F.range => (((t : F.range) : E) : X)) h).symm

private theorem faithful_card_X {E : Subgroup X} (h : FaithfulL3E8 X E) : Nat.card X = 1344 := by
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup E, Nat.card_congr e.toEquiv, l3Two_card,
    h.card]

private theorem faithful_finite {E : Subgroup X} (h : FaithfulL3E8 X E) : Finite X :=
  Nat.finite_of_card_ne_zero (by rw [faithful_card_X h]; norm_num)

private noncomputable def slEquivGL : L3Two ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : L3Two →* GL (Fin 3) (ZMod 2))
    (Matrix.SpecialLinearGroup.toGL_injective.bijective_of_nat_card_le (by
      rw [l3Two_card, CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 3]
      simp [Fin.prod_univ_succ]))

private theorem faithful_model {E : Subgroup X} [E.Normal] (h : FaithfulL3E8 X E) :
    ∃ (ε : E ≃* Multiplicative (Fin 3 → ZMod 2)) (Θ : X →* L3Two),
      (∀ x : X, Θ x = 1 ↔ x ∈ E) ∧ Function.Surjective Θ ∧
      ∀ (x : X) (w : E), (Θ x : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (ε w) =
        Multiplicative.toAdd (ε (MulAut.conjNormal x w)) := by
  haveI := faithful_finite h
  have hcomm : ∀ a b : E, a * b = b * a := fun a b =>
    Subtype.ext (elem_comm h.elemAbelian a.2 b.2)
  have hpow : ∀ a : E, a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [sq] using elem_sq h.elemAbelian a.2)
  obtain ⟨ε⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow
    (n := 3) (by rw [h.card]; norm_num)
  let Θ : X →* L3Two := slEquivGL.symm.toMonoidHom.comp
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL ε).toMonoidHom.comp MulAut.conjNormal)
  have hΘ : ∀ x : X, slEquivGL (Θ x) =
      CFSG.SectionRank.Ccomm.elemAutEquivGL ε (MulAut.conjNormal x) :=
    fun x => slEquivGL.apply_symm_apply _
  have hΘ1 : ∀ x : X, Θ x = 1 ↔ MulAut.conjNormal x = (1 : MulAut E) := by
    intro x
    constructor
    · intro hx
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL ε).injective
      rw [← hΘ, hx, map_one, map_one]
    · intro hx
      apply slEquivGL.injective
      rw [hΘ, hx, map_one, map_one]
  have hkerΘ : ∀ x : X, Θ x = 1 ↔ x ∈ E := by
    intro x
    rw [hΘ1]
    constructor
    · intro hx
      have h2 : x ∈ Subgroup.centralizer (E : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h3 : ((MulAut.conjNormal x ⟨y, hy⟩ : E) : X) = y := by rw [hx]; rfl
        rw [MulAut.conjNormal_apply] at h3
        change x * y * x⁻¹ = y at h3
        calc y * x = (x * y * x⁻¹) * x := by rw [h3]
          _ = x * y := by group
      rwa [h.centralizer] at h2
    · intro hx
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      change x * (w : X) * x⁻¹ = (w : X)
      calc x * (w : X) * x⁻¹ = w * x * x⁻¹ := by rw [elem_comm h.elemAbelian hx w.2]
        _ = w := by group
  have hsurj : Function.Surjective Θ := by
    have hkerE : Θ.ker = E := by
      ext x
      rw [MonoidHom.mem_ker]
      exact hkerΘ x
    have h1 := Subgroup.card_ker_mul_card_range Θ
    rw [hkerE, h.card, faithful_card_X h] at h1
    have h2 : Θ.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [l3Two_card]
      omega
    exact MonoidHom.range_eq_top.1 h2
  refine ⟨ε, Θ, hkerΘ, hsurj, fun x w => ?_⟩
  have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec ε (MulAut.conjNormal x) w
  have h2 : ((Θ x : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL ε (MulAut.conjNormal x) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← hΘ x]
    rfl
  rw [h2]
  exact h1

private theorem faithful_char [Finite X] {E : Subgroup X} (h : FaithfulL3E8 X E) :
    ∀ φ : MulAut X, ∀ x ∈ E, φ x ∈ E := by
  intro φ x hx
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  have hNn : (E.map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹E.Normal› φ.toMonoidHom φ.surjective
  have hNcard : Nat.card (E.map φ.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective φ.injective, h.card]
  haveI : IsSimpleGroup L3Two := isSimpleGroup_l3Two
  haveI hNm : ((E.map φ.toMonoidHom).map (toL3 e)).Normal := hNn.map _ (toL3_surjective e)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((E.map φ.toMonoidHom).map (toL3 e)) with h0 | h0
  · have h1 : toL3 e (φ x) ∈ (E.map φ.toMonoidHom).map (toL3 e) := ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    rw [h0, Subgroup.mem_bot] at h1
    exact (toL3_eq_one_iff e _).1 h1
  · exfalso
    have hsurj : Function.Surjective (fun n : E.map φ.toMonoidHom => toL3 e n) := by
      intro g
      have : g ∈ (E.map φ.toMonoidHom).map (toL3 e) := by rw [h0]; exact Subgroup.mem_top _
      obtain ⟨n, hn, rfl⟩ := this
      exact ⟨⟨n, hn⟩, rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hNcard, l3Two_card] at this
    omega

private def resE {E : Subgroup X} (hchar : ∀ φ : MulAut X, ∀ x ∈ E, φ x ∈ E) :
    MulAut X →* MulAut E where
  toFun φ :=
    { toFun := fun x => ⟨φ x, hchar φ x x.2⟩
      invFun := fun x => ⟨φ.symm x, hchar φ.symm x x.2⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (φ.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul φ (x : X) (y : X)) }
  map_one' := MulEquiv.ext (fun x => Subtype.ext rfl)
  map_mul' φ ψ := MulEquiv.ext (fun x => Subtype.ext rfl)

private theorem card_ker_resE_le [Finite X] {E : Subgroup X} (h : FaithfulL3E8 X E)
    (hchar : ∀ φ : MulAut X, ∀ x ∈ E, φ x ∈ E) : Nat.card (resE hchar).ker ≤ 16 := by
  classical
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  obtain ⟨ε, Θ, hΘker, -, hΘact⟩ := faithful_model h
  have hkerE : ∀ κ : MulAut X, κ ∈ (resE hchar).ker → ∀ x ∈ E, κ x = x := by
    intro κ hκ x hx
    have := congrArg (fun α : MulAut E => ((α ⟨x, hx⟩ : E) : X)) (MonoidHom.mem_ker.mp hκ)
    exact this
  have hδ : ∀ κ : MulAut X, (∀ x ∈ E, κ x = x) → ∀ x : X, x⁻¹ * κ x ∈ E := by
    intro κ hκ x
    have hC : x⁻¹ * κ x ∈ Subgroup.centralizer (E : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : x * y * x⁻¹ ∈ E := ‹E.Normal›.conj_mem y hy x
      have h1 : κ (x * y * x⁻¹) = x * y * x⁻¹ := hκ _ hy1
      rw [map_mul, map_mul, map_inv, hκ y hy] at h1
      calc y * (x⁻¹ * κ x) = x⁻¹ * (x * y * x⁻¹) * κ x := by group
        _ = x⁻¹ * (κ x * y * (κ x)⁻¹) * κ x := by rw [h1]
        _ = (x⁻¹ * κ x) * y := by group
    rwa [h.centralizer] at hC
  obtain ⟨u, hu⟩ := toL3_surjective e gA
  obtain ⟨v, hv⟩ := toL3_surjective e gB
  have huu : u * u ∈ E := (toL3_eq_one_iff e _).1 (by rw [map_mul, hu]; exact gA_sq)
  have huE : u ∉ E := fun hE' => gA_ne (by rw [← hu]; exact (toL3_eq_one_iff e u).2 hE')
  have hvvv : v * v * v ∈ E :=
    (toL3_eq_one_iff e _).1 (by rw [map_mul, map_mul, hv]; exact gB_cube)
  have hgen : ∀ x : X, ∃ w ∈ Subgroup.closure ({u, v} : Set X), w⁻¹ * x ∈ E := by
    intro x
    have h1 : toL3 e x ∈ (Subgroup.closure ({u, v} : Set X)).map (toL3 e) := by
      rw [MonoidHom.map_closure, Set.image_pair, hu, hv, gen_closure]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwx⟩ := h1
    refine ⟨w, hw, (toL3_eq_one_iff e _).1 ?_⟩
    rw [map_mul, map_inv, hwx, inv_mul_cancel]
  have hBu_sq : Θ u⁻¹ * Θ u⁻¹ = 1 := by
    rw [← map_mul]
    refine (hΘker _).2 ?_
    have : u⁻¹ * u⁻¹ = (u * u)⁻¹ := by group
    rw [this]
    exact E.inv_mem huu
  have hBu_ne : Θ u⁻¹ ≠ 1 := fun h' => huE (by
    have := (hΘker _).1 h'
    simpa using E.inv_mem this)
  have hBv_cube : Θ v⁻¹ * Θ v⁻¹ * Θ v⁻¹ = 1 := by
    rw [← map_mul, ← map_mul]
    refine (hΘker _).2 ?_
    have : v⁻¹ * v⁻¹ * v⁻¹ = (v * v * v)⁻¹ := by group
    rw [this]
    exact E.inv_mem hvvv
  have hu_rel : ∀ κ : MulAut X, (∀ x ∈ E, κ x = x) → u⁻¹ * (u⁻¹ * κ u) * u = u⁻¹ * κ u := by
    intro κ hκ
    have hδE := hδ κ hκ u
    have e1 : κ u * κ u = u * u := by rw [← map_mul]; exact hκ _ huu
    have e2 : (u⁻¹ * κ u) * u * (u⁻¹ * κ u) = u := by
      have : u * ((u⁻¹ * κ u) * u * (u⁻¹ * κ u)) = u * u := by
        calc u * ((u⁻¹ * κ u) * u * (u⁻¹ * κ u)) = (κ u) * (κ u) := by group
          _ = u * u := e1
      exact mul_left_cancel this
    calc u⁻¹ * (u⁻¹ * κ u) * u
        = u⁻¹ * ((u⁻¹ * κ u) * u * (u⁻¹ * κ u)) * (u⁻¹ * κ u)⁻¹ := by group
      _ = u⁻¹ * u * (u⁻¹ * κ u)⁻¹ := by rw [e2]
      _ = (u⁻¹ * κ u)⁻¹ := by group
      _ = u⁻¹ * κ u := elem_inv h.elemAbelian hδE
  have hv_rel : ∀ κ : MulAut X, (∀ x ∈ E, κ x = x) →
      (v⁻¹ * v⁻¹ * (v⁻¹ * κ v) * v * v) * (v⁻¹ * (v⁻¹ * κ v) * v) * (v⁻¹ * κ v) = 1 := by
    intro κ hκ
    have e1 : κ v * κ v * κ v = v * v * v := by rw [← map_mul, ← map_mul]; exact hκ _ hvvv
    have : v * v * v * ((v⁻¹ * v⁻¹ * (v⁻¹ * κ v) * v * v) * (v⁻¹ * (v⁻¹ * κ v) * v) *
        (v⁻¹ * κ v)) = v * v * v * 1 := by
      calc _ = κ v * κ v * κ v := by group
        _ = v * v * v := e1
        _ = v * v * v * 1 := (mul_one _).symm
    exact mul_left_cancel this
  let S₁ : Finset (Fin 3 → ZMod 2) := Finset.univ.filter (fun w : Fin 3 → ZMod 2 =>
    ((Θ u⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w)
  let S₂ : Finset (Fin 3 → ZMod 2) := Finset.univ.filter (fun w : Fin 3 → ZMod 2 =>
    (((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + 1) *ᵥ w = 0)
  have hS₁ : S₁.card ≤ 4 := l3_invol (Θ u⁻¹) hBu_sq hBu_ne
  have hS₂ : S₂.card ≤ 4 := l3_three (Θ v⁻¹) hBv_cube
  have hmem1 : ∀ (κ : MulAut X) (hκ : ∀ x ∈ E, κ x = x),
      ((Θ u⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (ε ⟨u⁻¹ * κ u, hδ κ hκ u⟩) =
        Multiplicative.toAdd (ε ⟨u⁻¹ * κ u, hδ κ hκ u⟩) := by
    intro κ hκ
    have h2 : MulAut.conjNormal u⁻¹ (⟨u⁻¹ * κ u, hδ κ hκ u⟩ : E) =
        ⟨u⁻¹ * κ u, hδ κ hκ u⟩ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change u⁻¹ * (u⁻¹ * κ u) * u⁻¹⁻¹ = u⁻¹ * κ u
      rw [inv_inv]
      exact hu_rel _ hκ
    rw [hΘact, h2]
  have hmem2 : ∀ (κ : MulAut X) (hκ : ∀ x ∈ E, κ x = x),
      (((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
        ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + 1) *ᵥ
        Multiplicative.toAdd (ε ⟨v⁻¹ * κ v, hδ κ hκ v⟩) = 0 := by
    intro κ hκ
    have hrel : MulAut.conjNormal (v⁻¹ * v⁻¹) (⟨v⁻¹ * κ v, hδ κ hκ v⟩ : E) *
        MulAut.conjNormal v⁻¹ (⟨v⁻¹ * κ v, hδ κ hκ v⟩ : E) * ⟨v⁻¹ * κ v, hδ κ hκ v⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
      change v⁻¹ * v⁻¹ * (v⁻¹ * κ v) * (v⁻¹ * v⁻¹)⁻¹ *
        (v⁻¹ * (v⁻¹ * κ v) * v⁻¹⁻¹) * (v⁻¹ * κ v) = 1
      calc v⁻¹ * v⁻¹ * (v⁻¹ * κ v) * (v⁻¹ * v⁻¹)⁻¹ * (v⁻¹ * (v⁻¹ * κ v) * v⁻¹⁻¹) * (v⁻¹ * κ v)
          = (v⁻¹ * v⁻¹ * (v⁻¹ * κ v) * v * v) * (v⁻¹ * (v⁻¹ * κ v) * v) * (v⁻¹ * κ v) := by
            group
        _ = 1 := hv_rel _ hκ
    have h3 := congrArg (fun t : E => Multiplicative.toAdd (ε t)) hrel
    rw [map_mul ε, map_mul ε, toAdd_mul, toAdd_mul, map_one ε, toAdd_one] at h3
    rw [← hΘact, ← hΘact] at h3
    have h4 : ((Θ (v⁻¹ * v⁻¹) : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((Θ v⁻¹ : L3Two) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [h4] at h3
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    exact h3
  let D : (resE hchar).ker → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) := fun κ =>
    (Multiplicative.toAdd (ε ⟨u⁻¹ * (κ : MulAut X) u, hδ _ (hkerE _ κ.2) u⟩),
     Multiplicative.toAdd (ε ⟨v⁻¹ * (κ : MulAut X) v, hδ _ (hkerE _ κ.2) v⟩))
  have hD_mem : ∀ κ : (resE hchar).ker, D κ ∈ S₁ ×ˢ S₂ := fun κ =>
    Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem1 _ (hkerE _ κ.2)⟩,
       Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem2 _ (hkerE _ κ.2)⟩⟩
  have hD_inj : Function.Injective D := by
    intro κ₁ κ₂ hD
    have hD1 := congrArg Prod.fst hD
    have hD2 := congrArg Prod.snd hD
    simp only [D] at hD1 hD2
    have h1 : (κ₁ : MulAut X) u = (κ₂ : MulAut X) u := by
      have := ε.injective (Multiplicative.toAdd.injective hD1)
      have := mul_left_cancel (congrArg Subtype.val this)
      exact this
    have h2 : (κ₁ : MulAut X) v = (κ₂ : MulAut X) v := by
      have := ε.injective (Multiplicative.toAdd.injective hD2)
      have := mul_left_cancel (congrArg Subtype.val this)
      exact this
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨w, hw, hwx⟩ := hgen x
    have hxw : x = w * (w⁻¹ * x) := by group
    have hκ1 := hkerE _ κ₁.2
    have hκ2 := hkerE _ κ₂.2
    have hww : (κ₁ : MulAut X) w = (κ₂ : MulAut X) w := by
      refine MonoidHom.eqOn_closure (f := (κ₁ : MulAut X).toMonoidHom)
        (g := (κ₂ : MulAut X).toMonoidHom) (s := {u, v}) ?_ hw
      intro t ht
      rcases ht with rfl | rfl
      · exact h1
      · exact h2
    calc (κ₁ : MulAut X) x = (κ₁ : MulAut X) (w * (w⁻¹ * x)) := congrArg (κ₁ : MulAut X) hxw
      _ = (κ₁ : MulAut X) w * (κ₁ : MulAut X) (w⁻¹ * x) := map_mul _ _ _
      _ = (κ₂ : MulAut X) w * (w⁻¹ * x) := by rw [hww, hκ1 _ hwx]
      _ = (κ₂ : MulAut X) w * (κ₂ : MulAut X) (w⁻¹ * x) := by rw [hκ2 _ hwx]
      _ = (κ₂ : MulAut X) (w * (w⁻¹ * x)) := (map_mul _ _ _).symm
      _ = (κ₂ : MulAut X) x := congrArg (κ₂ : MulAut X) hxw.symm
  haveI : Fintype (resE hchar).ker := Fintype.ofFinite _
  have hcard : Nat.card (resE hchar).ker ≤ (S₁ ×ˢ S₂).card := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.card_le_card_of_injOn D (fun κ _ => hD_mem κ) (fun a _ b _ hab => hD_inj hab)
  calc Nat.card (resE hchar).ker ≤ (S₁ ×ˢ S₂).card := hcard
    _ = S₁.card * S₂.card := Finset.card_product _ _
    _ ≤ 4 * 4 := Nat.mul_le_mul hS₁ hS₂

theorem l3e8_centralizer_dichotomy {E : Subgroup X} [E.Normal] (hE : IsElemAbelian 2 E)
    (e : (X ⧸ E) ≃* L3Two) :
    Subgroup.centralizer (E : Set X) = E ∨ E ≤ Subgroup.center X := by
  set K : Subgroup X := Subgroup.centralizer (E : Set X) with hK
  have hEK : E ≤ K := fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => elem_comm hE hz hy
  have hKnormal : K.Normal := ⟨fun k hk g y hy => by
    have hk' := Subgroup.mem_centralizer_iff.mp hk
    have hy' : g⁻¹ * y * g ∈ E := by
      simpa using ‹E.Normal›.conj_mem y hy g⁻¹
    have := hk' _ hy'
    calc y * (g * k * g⁻¹) = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = (g * k * g⁻¹) * y := by group⟩
  haveI : IsSimpleGroup L3Two := isSimpleGroup_l3Two
  have hfs : Function.Surjective (toL3 e) := toL3_surjective e
  have hKm : (K.map (toL3 e)).Normal := hKnormal.map _ hfs
  haveI := hKm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (toL3 e)) with h | h
  · left
    refine le_antisymm (fun n hn => ?_) hEK
    have : toL3 e n ∈ K.map (toL3 e) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (toL3_eq_one_iff e n).mp this
  · right
    have hKtop : K = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : toL3 e x ∈ K.map (toL3 e) := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := this
      have : x * k⁻¹ ∈ E :=
        (toL3_eq_one_iff e _).mp (by rw [map_mul, map_inv, hkx, mul_inv_cancel])
      have := K.mul_mem (hEK this) hk
      simpa using this
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro x
    have := Subgroup.mem_centralizer_iff.mp (hKtop ▸ Subgroup.mem_top x) c hc
    exact this.symm

theorem l3e8_central_q8_involution_eq {E : Subgroup X} [E.Normal] (hE : IsElemAbelian 2 E)
    (hc : E ≤ Subgroup.center X) (e : (X ⧸ E) ≃* L3Two) {P P' : Subgroup X} {z z' : X}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution P z)
    (hP' : Nonempty (↥P' ≃* QuaternionGroup 2)) (hz' : IsUniqueInvolution P' z') : z = z' := by
  have hzE : z ∈ E := q8_mem_E e hP hz
  have hzE' : z' ∈ E := q8_mem_E e hP' hz'
  obtain ⟨a, -, haP, -, haa, -, -, -, -, -⟩ := q8_data hP hz
  obtain ⟨a', -, haP', -, haa', -, -, -, -, -⟩ := q8_data hP' hz'
  have hf1 : toL3 e a * toL3 e a = 1 := by
    rw [← map_mul, haa]; exact (toL3_eq_one_iff e z).2 hzE
  have hf1' : toL3 e a' * toL3 e a' = 1 := by
    rw [← map_mul, haa']; exact (toL3_eq_one_iff e z').2 hzE'
  have hf2 : toL3 e a ≠ 1 := fun h =>
    hz.ne_one (by rw [← haa]; exact elem_sq hE ((toL3_eq_one_iff e a).1 h))
  have hf2' : toL3 e a' ≠ 1 := fun h =>
    hz'.ne_one (by rw [← haa']; exact elem_sq hE ((toL3_eq_one_iff e a').1 h))
  obtain ⟨g, hg⟩ := l3Two_involutions_conj _ _ hf1 hf2 hf1' hf2'
  obtain ⟨x, hx⟩ := toL3_surjective e g
  have h3 : toL3 e (x * a * x⁻¹) = toL3 e a' := by
    rw [map_mul, map_mul, map_inv, hx]; exact hg
  have h4 : (x * a * x⁻¹)⁻¹ * a' ∈ E := by
    rw [← toL3_eq_one_iff e, map_mul, map_inv, h3, inv_mul_cancel]
  set ε := (x * a * x⁻¹)⁻¹ * a' with hε
  have hεc : ∀ y : X, y * ε = ε * y := fun y => Subgroup.mem_center_iff.mp (hc h4) y
  have ha' : a' = x * a * x⁻¹ * ε := by rw [hε]; group
  have hεε : ε * ε = 1 := elem_sq hE h4
  have hzc : ∀ y : X, y * z = z * y := fun y => Subgroup.mem_center_iff.mp (hc hzE) y
  calc z = x * z * x⁻¹ := by rw [hzc x]; group
    _ = (x * a * x⁻¹) * (x * a * x⁻¹) := by rw [← haa]; group
    _ = (x * a * x⁻¹) * (x * a * x⁻¹) * (ε * ε) := by rw [hεε, mul_one]
    _ = (x * a * x⁻¹) * ((x * a * x⁻¹) * ε) * ε := by group
    _ = (x * a * x⁻¹) * (ε * (x * a * x⁻¹)) * ε := by rw [hεc (x * a * x⁻¹)]
    _ = (x * a * x⁻¹ * ε) * (x * a * x⁻¹ * ε) := by group
    _ = a' * a' := by rw [← ha']
    _ = z' := haa'

namespace FaithfulL3E8

variable {E : Subgroup X}

theorem mem_E_of_q8 (h : FaithfulL3E8 X E) {P : Subgroup X} {z : X}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution P z) : z ∈ E := by
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  exact q8_mem_E e hP hz

theorem exists_conj (h : FaithfulL3E8 X E) {e f : X} (he : e ∈ E) (hf : f ∈ E) (he1 : e ≠ 1)
    (hf1 : f ≠ 1) : ∃ x : X, x * e * x⁻¹ = f := by
  haveI := h.normal
  obtain ⟨ε, Θ, -, hsurj, hact⟩ := faithful_model h
  have hv : Multiplicative.toAdd (ε ⟨e, he⟩) ≠ 0 := by
    intro h0
    have h1 : ε ⟨e, he⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 : (⟨e, he⟩ : E) = 1 := ε.injective (h1.trans (map_one ε).symm)
    exact he1 (congrArg Subtype.val h2)
  have hw : Multiplicative.toAdd (ε ⟨f, hf⟩) ≠ 0 := by
    intro h0
    have h1 : ε ⟨f, hf⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 : (⟨f, hf⟩ : E) = 1 := ε.injective (h1.trans (map_one ε).symm)
    exact hf1 (congrArg Subtype.val h2)
  obtain ⟨M, hM⟩ := l3_transitive _ _ hv hw
  obtain ⟨x, hx⟩ := hsurj M
  refine ⟨x, ?_⟩
  have h1 := hact x ⟨e, he⟩
  rw [hx, hM] at h1
  have h2 : MulAut.conjNormal x ⟨e, he⟩ = (⟨f, hf⟩ : E) :=
    ε.injective (Multiplicative.toAdd.injective h1.symm)
  have h3 := congrArg Subtype.val h2
  rw [MulAut.conjNormal_apply] at h3
  exact h3

theorem center_eq_bot (h : FaithfulL3E8 X E) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzE : z ∈ E := by
    have : z ∈ Subgroup.centralizer (E : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp hz y
    rwa [h.centralizer] at this
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  have hex : ∃ f : E, f ≠ 1 ∧ (f : X) ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (![1, ⟨z, hzE⟩] : Fin 2 → E) := by
      intro f
      by_cases hf : f = 1
      · exact ⟨0, by simp [hf]⟩
      · exact ⟨1, by simpa using (Subtype.ext (hcon f hf)).symm⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [h.card] at this
    simp at this
  obtain ⟨f, hf1, hfz⟩ := hex
  obtain ⟨x, hx⟩ := exists_conj h hzE f.2 hz1 (fun h' => hf1 (Subtype.ext h'))
  have : x * z * x⁻¹ = z := by rw [Subgroup.mem_center_iff.mp hz x]; group
  exact hfz (hx.symm.trans this)

theorem out_le_two [Finite X] (h : FaithfulL3E8 X E) :
    (MulAut.conj : X →* MulAut X).range.index ≤ 2 := by
  classical
  haveI := h.normal
  haveI : Finite (MulAut X) := MulEquiv.finite_left
  have hchar := faithful_char h
  have hK := card_ker_resE_le h hchar
  obtain ⟨ε, -⟩ := faithful_model h
  haveI : Finite E := inferInstance
  haveI : Finite (MulAut E) := MulEquiv.finite_left
  have hAutE : Nat.card (MulAut E) = 168 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL ε,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 3]
    simp [Fin.prod_univ_succ]
  have hR : Nat.card (resE hchar).range ≤ 168 := by
    rw [← hAutE]
    exact Subgroup.card_le_card_group _
  have h1 := Subgroup.card_ker_mul_card_range (resE hchar)
  have hAut : Nat.card (MulAut X) ≤ 2688 := by
    rw [← h1]
    calc Nat.card (resE hchar).ker * Nat.card (resE hchar).range ≤ 16 * 168 :=
          Nat.mul_le_mul hK hR
      _ = 2688 := by norm_num
  have hcent : (MulAut.conj : X →* MulAut X).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut X => φ g) (MonoidHom.mem_ker.mp hx)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * x = (x * g * x⁻¹) * x := by rw [h2]
        _ = x * g := by group
    rw [center_eq_bot h] at this
    exact Subgroup.mem_bot.mp this
  have h2 := Subgroup.card_ker_mul_card_range (MulAut.conj : X →* MulAut X)
  rw [hcent, Subgroup.card_bot, one_mul] at h2
  have h3 := Subgroup.index_mul_card (MulAut.conj : X →* MulAut X).range
  rw [h2, faithful_card_X h] at h3
  omega

theorem exists_inner [Finite X] (h : FaithfulL3E8 X E) (A : Subgroup (MulAut X))
    (hA : Nat.card A = 4) : ∃ φ ∈ A, φ ≠ 1 ∧ φ ∈ (MulAut.conj : X →* MulAut X).range := by
  classical
  haveI : Finite (MulAut X) := MulEquiv.finite_left
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun φ : A =>
      (QuotientGroup.mk (φ : MulAut X) :
        MulAut X ⧸ (MulAut.conj : X →* MulAut X).range)) := by
    intro φ ψ hφψ
    have h1 := QuotientGroup.eq.1 hφψ
    have h2 : (φ : MulAut X)⁻¹ * ψ ∈ A := A.mul_mem (A.inv_mem φ.2) ψ.2
    by_contra hne
    have h3 : (φ : MulAut X)⁻¹ * ψ ≠ 1 := fun h4 => hne (Subtype.ext (inv_mul_eq_one.1 h4))
    exact hcon _ h2 h3 h1
  have h5 := Nat.card_le_card_of_injective _ hinj
  rw [hA] at h5
  have h6 := out_le_two h
  have h7 : Nat.card (MulAut X ⧸ (MulAut.conj : X →* MulAut X).range) ≤ 2 := h6
  omega

theorem involution_cent_order_four (h : FaithfulL3E8 X E) {P : Subgroup X}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) {y : X} (hy : y * y = 1) :
    ∃ x : X, ∃ k ∈ P, orderOf k = 4 ∧ y * (x * k * x⁻¹) = (x * k * x⁻¹) * y := by
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  obtain ⟨z, hz⟩ := q8_exists_unique hP
  obtain ⟨a, b, haP, hbP, haa, hbb, hab, hbab, hba, hca⟩ := q8_data hP hz
  have hzE : z ∈ E := q8_mem_E e hP hz
  have hzz : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hzb : z * b = b * z := by rw [← hbb]; group
  have hord_b : orderOf b = 4 := orderOf_eq_four hbb hz1 hzz
  have hord_c : orderOf (a * b) = 4 := orderOf_eq_four hab hz1 hzz
  have hcP : a * b ∈ P := P.mul_mem haP hbP
  by_cases hyE : y ∈ E
  · by_cases hy1 : y = 1
    · exact ⟨1, b, hbP, hord_b, by subst hy1; simp⟩
    · obtain ⟨x, hx⟩ := exists_conj h hzE hyE hz1 hy1
      refine ⟨x, b, hbP, hord_b, ?_⟩
      rw [← hx]
      calc x * z * x⁻¹ * (x * b * x⁻¹) = x * (z * b) * x⁻¹ := by group
        _ = x * (b * z) * x⁻¹ := by rw [hzb]
        _ = x * b * x⁻¹ * (x * z * x⁻¹) := by group
  ·
    have hfa1 : toL3 e a * toL3 e a = 1 := by
      rw [← map_mul, haa]; exact (toL3_eq_one_iff e z).2 hzE
    have hfa2 : toL3 e a ≠ 1 := fun h' =>
      hz1 (by rw [← haa]; exact elem_sq h.elemAbelian ((toL3_eq_one_iff e a).1 h'))
    have hfb1 : toL3 e b * toL3 e b = 1 := by
      rw [← map_mul, hbb]; exact (toL3_eq_one_iff e z).2 hzE
    have hfb2 : toL3 e b ≠ 1 := fun h' =>
      hz1 (by rw [← hbb]; exact elem_sq h.elemAbelian ((toL3_eq_one_iff e b).1 h'))
    have hfy1 : toL3 e y * toL3 e y = 1 := by rw [← map_mul, hy, map_one]
    have hfy2 : toL3 e y ≠ 1 := fun h' => hyE ((toL3_eq_one_iff e y).1 h')
    obtain ⟨g₁, hg₁⟩ := l3Two_involutions_conj _ _ hfy1 hfy2 hfa1 hfa2
    obtain ⟨x₁, hx₁⟩ := toL3_surjective e g₁
    have hfy₀ : toL3 e (x₁ * y * x₁⁻¹) = toL3 e a := by
      rw [map_mul, map_mul, map_inv, hx₁]; exact hg₁
    have hy₀y₀ : (x₁ * y * x₁⁻¹) * (x₁ * y * x₁⁻¹) = 1 := by
      calc (x₁ * y * x₁⁻¹) * (x₁ * y * x₁⁻¹) = x₁ * (y * y) * x₁⁻¹ := by group
        _ = 1 := by rw [hy]; group
    have hεE : a⁻¹ * (x₁ * y * x₁⁻¹) ∈ E :=
      (toL3_eq_one_iff e _).1 (by rw [map_mul, map_inv, hfy₀, inv_mul_cancel])
    set ε := a⁻¹ * (x₁ * y * x₁⁻¹) with hε
    have hy₀ε : x₁ * y * x₁⁻¹ = a * ε := by rw [hε]; group
    have hεε : ε * ε = 1 := elem_sq h.elemAbelian hεE
    have hFa : a⁻¹ * ε * a * ε = z := by
      have h1 : a * ε * (a * ε) = 1 := by rw [← hy₀ε]; exact hy₀y₀
      have h2 : ε * a * ε = a⁻¹ := by
        have : a * (ε * a * ε) = 1 := by
          calc a * (ε * a * ε) = a * ε * (a * ε) := by group
            _ = 1 := h1
        exact eq_inv_of_mul_eq_one_right this
      calc a⁻¹ * ε * a * ε = a⁻¹ * (ε * a * ε) := by group
        _ = a⁻¹ * a⁻¹ := by rw [h2]
        _ = (a * a)⁻¹ := by group
        _ = z⁻¹ := by rw [haa]
        _ = z := inv_eq_of_mul_eq_one_right hzz
    have hfy₀1 : toL3 e (x₁ * y * x₁⁻¹) * toL3 e (x₁ * y * x₁⁻¹) = 1 := by rw [hfy₀]; exact hfa1
    have hfy₀2 : toL3 e (x₁ * y * x₁⁻¹) ≠ 1 := by rw [hfy₀]; exact hfa2
    obtain ⟨g₂, hg₂⟩ := l3Two_involutions_conj _ _ hfy₀1 hfy₀2 hfb1 hfb2
    obtain ⟨x₂, hx₂⟩ := toL3_surjective e g₂
    have hfyb : toL3 e (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) = toL3 e b := by
      rw [map_mul, map_mul, map_inv, hx₂]; exact hg₂
    have hyb : (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) * (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) = 1 := by
      calc (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) * (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹)
          = x₂ * ((x₁ * y * x₁⁻¹) * (x₁ * y * x₁⁻¹)) * x₂⁻¹ := by group
        _ = 1 := by rw [hy₀y₀]; group
    have hεbE : b⁻¹ * (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) ∈ E :=
      (toL3_eq_one_iff e _).1 (by rw [map_mul, map_inv, hfyb, inv_mul_cancel])
    set εb := b⁻¹ * (x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹) with hεb
    have hyεb : x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹ = b * εb := by rw [hεb]; group
    have hFb : b⁻¹ * εb * b * εb = z := by
      have h1 : b * εb * (b * εb) = 1 := by rw [← hyεb]; exact hyb
      have h2 : εb * b * εb = b⁻¹ := by
        have : b * (εb * b * εb) = 1 := by
          calc b * (εb * b * εb) = b * εb * (b * εb) := by group
            _ = 1 := h1
        exact eq_inv_of_mul_eq_one_right this
      calc b⁻¹ * εb * b * εb = b⁻¹ * (εb * b * εb) := by group
        _ = b⁻¹ * b⁻¹ := by rw [h2]
        _ = (b * b)⁻¹ := by group
        _ = z⁻¹ := by rw [hbb]
        _ = z := inv_eq_of_mul_eq_one_right hzz
    have hFbε := comm_set_le_two h.elemAbelian h.card (by rw [hbb]; exact hzE) hεbE
      (by rw [hFb]; exact hz1) ε hεE
    rw [hFb] at hFbε
    have key : ∀ k : X, x₁ * y * x₁⁻¹ * k = k * (x₁ * y * x₁⁻¹) →
        y * (x₁⁻¹ * k * x₁⁻¹⁻¹) = (x₁⁻¹ * k * x₁⁻¹⁻¹) * y := by
      intro k hk
      calc y * (x₁⁻¹ * k * x₁⁻¹⁻¹) = x₁⁻¹ * ((x₁ * y * x₁⁻¹) * k) * x₁ := by group
        _ = x₁⁻¹ * (k * (x₁ * y * x₁⁻¹)) * x₁ := by rw [hk]
        _ = (x₁⁻¹ * k * x₁⁻¹⁻¹) * y := by group
    rcases hFbε with hF1 | hFz
    · have hFc : (a * b)⁻¹ * ε * (a * b) * ε = z := by
        rw [F_mul hzb hFa hεε, hF1, mul_one]
      have hcom : a * ε * (a * b) = (a * b) * (a * ε) := commute_of_F hab hzz hca hεε hFc
      refine ⟨x₁⁻¹, a * b, hcP, hord_c, key _ ?_⟩
      rw [hy₀ε]; exact hcom
    · have hcom : a * ε * b = b * (a * ε) := commute_of_F hbb hzz hba hεε hFz
      refine ⟨x₁⁻¹, b, hbP, hord_b, key _ ?_⟩
      rw [hy₀ε]; exact hcom

end FaithfulL3E8

end Shape

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

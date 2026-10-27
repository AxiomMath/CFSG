module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.AGLEmbedding

section ClassTwo

variable {Γ : Type} [Group Γ]

theorem classTwo_pow_mul (a b d : Γ) (hba : b * a = a * b * d) (hdb : d * b = b * d)
    (n : ℕ) : b ^ n * a = a * b ^ n * d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdbn : d * b ^ n = b ^ n * d := (Commute.pow_right (show Commute d b from hdb) n).eq
    rw [pow_succ', mul_assoc, ih, pow_succ']
    calc b * (a * b ^ n * d ^ n) = (b * a) * b ^ n * d ^ n := by group
      _ = (a * b * d) * b ^ n * d ^ n := by rw [hba]
      _ = a * b * (d * b ^ n) * d ^ n := by group
      _ = a * b * (b ^ n * d) * d ^ n := by rw [hdbn]
      _ = a * (b * b ^ n) * (d * d ^ n) := by group

theorem classTwo_mul_pow (a b d : Γ) (hba : b * a = a * b * d) (hda : d * a = a * d)
    (hdb : d * b = b * d) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n * d ^ (n.choose 2) := by
  have hdk : ∀ k : ℕ, ∀ g : Γ, d * g = g * d → d ^ k * g = g * d ^ k := fun k g hg =>
    (Commute.pow_left (show Commute d g from hg) k).eq
  have hdab : d * (a * b) = (a * b) * d := by rw [← mul_assoc, hda, mul_assoc, hdb, mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    have h1 : b ^ n * a = a * b ^ n * d ^ n := classTwo_pow_mul a b d hba hdb n
    calc a ^ n * b ^ n * d ^ (n.choose 2) * (a * b)
        = a ^ n * b ^ n * (d ^ (n.choose 2) * (a * b)) := by group
      _ = a ^ n * b ^ n * ((a * b) * d ^ (n.choose 2)) := by rw [hdk _ _ hdab]
      _ = a ^ n * (b ^ n * a) * b * d ^ (n.choose 2) := by group
      _ = a ^ n * (a * b ^ n * d ^ n) * b * d ^ (n.choose 2) := by rw [h1]
      _ = a ^ n * a * b ^ n * (d ^ n * b) * d ^ (n.choose 2) := by group
      _ = a ^ n * a * b ^ n * (b * d ^ n) * d ^ (n.choose 2) := by rw [hdk _ _ hdb]
      _ = a ^ (n + 1) * b ^ (n + 1) * d ^ (n + n.choose 2) := by
        rw [pow_succ a, pow_succ b, pow_add]; group

theorem commutator_pow_eq_one_of_central {p : ℕ} {B Z₀ : Subgroup Γ}
    (hZc : Z₀ ≤ Subgroup.centralizer (B : Set Γ)) (hpow : ∀ b ∈ B, b ^ p ∈ Z₀)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ Z₀) {x y : Γ} (hx : x ∈ B) (hy : y ∈ B) :
    (x * y * x⁻¹ * y⁻¹) ^ p = 1 := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcB : ∀ g ∈ B, c * g = g * c := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (hZc (hcomm x hx y hy)) g hg).symm
  have hyp : x * y ^ p * x⁻¹ = y ^ p := by
    rw [(Subgroup.mem_centralizer_iff.mp (hZc (hpow y hy)) x hx)]; group
  have h1 : (x * y * x⁻¹) ^ p = x * y ^ p * x⁻¹ := by
    rw [conj_pow]
  have h2 : x * y * x⁻¹ = c * y := by rw [hc]; group
  have h3 : (c * y) ^ p = c ^ p * y ^ p := (Commute.mul_pow (hcB y hy) p)
  rw [h2, h3, hyp] at h1
  exact mul_right_cancel (h1.trans (one_mul _).symm)

theorem mul_pow_prime_of_classTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B Z₀ : Subgroup Γ}
    (hZc : Z₀ ≤ Subgroup.centralizer (B : Set Γ)) (hpow : ∀ b ∈ B, b ^ p ∈ Z₀)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ Z₀) {a b : Γ} (ha : a ∈ B) (hb : b ∈ B) :
    (a * b) ^ p = a ^ p * b ^ p := by
  set d := b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ with hd
  have hba : b * a = a * b * d := by rw [hd]; group
  have hdZ : d ∈ Z₀ := hcomm b⁻¹ (B.inv_mem hb) a⁻¹ (B.inv_mem ha)
  have hda : d * a = a * d := (Subgroup.mem_centralizer_iff.mp (hZc hdZ) a ha).symm
  have hdb : d * b = b * d := (Subgroup.mem_centralizer_iff.mp (hZc hdZ) b hb).symm
  have hdp : d ^ p = 1 :=
    commutator_pow_eq_one_of_central hZc hpow hcomm (B.inv_mem hb) (B.inv_mem ha)
  have hchoose : p ∣ p.choose 2 :=
    hp.dvd_choose_self (by norm_num) (by have := hp.two_le; omega)
  obtain ⟨m, hm⟩ := hchoose
  rw [classTwo_mul_pow a b d hba hda hdb p, hm, pow_mul, hdp, one_pow, mul_one]

@[expose] def cyclicOmegaOne (p : ℕ) (Z₀ : Subgroup Γ) (hZ₀ : IsCyclic Z₀) : Subgroup Γ where
  carrier := {z | z ∈ Z₀ ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
    refine ⟨Z₀.mul_mem ha hb, ?_⟩
    have hab : a * b = b * a := by
      have := hZ₀.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    rw [(Commute.mul_pow hab p), hap, hbp, one_mul]
  one_mem' := ⟨Z₀.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨ha, hap⟩
    exact ⟨Z₀.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩

end ClassTwo

section Finite

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem relIndex_inf_centralizer_le_card {B₀ D₁ : Subgroup Γ}
    (hD₁c : D₁ ≤ Subgroup.centralizer (B₀ : Set Γ)) (hD₁B : D₁ ≤ B₀)
    (hcomm : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b * a⁻¹ * b⁻¹ ∈ D₁) {b : Γ} (hb : b ∈ B₀) :
    (B₀ ⊓ Subgroup.centralizer ({b} : Set Γ)).relIndex B₀ ≤ Nat.card D₁ := by
  have hcen : ∀ d ∈ D₁, ∀ g ∈ B₀, d * g = g * d := fun d hd g hg =>
    (Subgroup.mem_centralizer_iff.mp (hD₁c hd) g hg).symm
  let f : B₀ →* D₁ :=
    { toFun := fun x => ⟨x * b * x⁻¹ * b⁻¹, hcomm x x.2 b hb⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        set u := (x : Γ) * b * (x : Γ)⁻¹ * b⁻¹ with hu
        set v := (y : Γ) * b * (y : Γ)⁻¹ * b⁻¹ with hv
        have hvD : v ∈ D₁ := hcomm y y.2 b hb
        have hc := hcen _ hvD x x.2
        calc (x : Γ) * y * b * ((x : Γ) * y)⁻¹ * b⁻¹ = (x : Γ) * v * (x : Γ)⁻¹ * u := by
              rw [hu, hv]; group
          _ = v * u := by rw [← hc]; group
          _ = u * v := hcen _ hvD _ (hD₁B (hcomm x x.2 b hb)) }
  have hker : f.ker = (B₀ ⊓ Subgroup.centralizer ({b} : Set Γ)).subgroupOf B₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 : (x : Γ) * b * (x : Γ)⁻¹ * b⁻¹ = 1 := congrArg Subtype.val hx
      refine ⟨x.2, ?_⟩
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    · rintro ⟨-, hx⟩
      ext
      change (x : Γ) * b * (x : Γ)⁻¹ * b⁻¹ = 1
      rw [hx]; group
  have h1 := Subgroup.index_ker f
  rw [hker] at h1
  change (B₀ ⊓ Subgroup.centralizer ({b} : Set Γ)).relIndex B₀ ≤ Nat.card D₁
  rw [Subgroup.relIndex, h1]
  exact Subgroup.card_le_card_group _

theorem exists_abelian_relIndex_sq {p : ℕ} [hp : Fact p.Prime] (D₁ : Subgroup Γ)
    (hD₁ : Nat.card D₁ ≤ p) :
    ∀ (n : ℕ) (B₀ Z' : Subgroup Γ), Z'.relIndex B₀ = n → IsPGroup p B₀ → Z' ≤ B₀ →
      Z' ≤ Subgroup.centralizer (B₀ : Set Γ) → D₁ ≤ Z' → (∀ b ∈ B₀, b ^ p ∈ Z') →
      (∀ a ∈ B₀, ∀ b ∈ B₀, a * b * a⁻¹ * b⁻¹ ∈ D₁) →
      ∃ A : Subgroup Γ, Z' ≤ A ∧ A ≤ B₀ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
        Z'.relIndex B₀ ≤ (Z'.relIndex A) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₀ Z' hn hB₀ hZB hZc hDZ hpow hcomm
  by_cases hBZ : B₀ ≤ Z'
  · refine ⟨Z', le_rfl, hZB, fun a ha b hb => ?_, ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp (hZc ha) b (hZB hb)).symm
    · rw [le_antisymm hBZ hZB, Subgroup.relIndex_self]; simp
  obtain ⟨b, hbB, hbZ⟩ := Set.not_subset.mp hBZ
  set C := B₀ ⊓ Subgroup.centralizer ({b} : Set Γ) with hC
  set Z'' := Z' ⊔ Subgroup.zpowers b with hZ''
  have hcenZ : ∀ z ∈ Z', ∀ g ∈ B₀, z * g = g * z := fun z hz g hg =>
    (Subgroup.mem_centralizer_iff.mp (hZc hz) g hg).symm
  have hZC : Z' ≤ C := fun z hz =>
    ⟨hZB hz, Subgroup.mem_centralizer_singleton_iff.mpr (hcenZ z hz b hbB)⟩
  have hbC : b ∈ C := ⟨hbB, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hZ''C : Z'' ≤ C := sup_le hZC ((Subgroup.zpowers_le).mpr hbC)
  have hCB : C ≤ B₀ := inf_le_left
  have hZ''c : Z'' ≤ Subgroup.centralizer (C : Set Γ) := by
    refine sup_le (hZc.trans (Subgroup.centralizer_le hCB)) ((Subgroup.zpowers_le).mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hZZ'' : Z' ≤ Z'' := le_sup_left
  have hx : p ≤ Z'.relIndex Z'' := by
    have hZ''p : IsPGroup p Z'' := hB₀.to_le (hZ''C.trans hCB)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ''p
    have hdvd : Z'.relIndex Z'' ∣ p ^ k := hk ▸ Subgroup.relIndex_dvd_card Z' Z''
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hne : Z'.relIndex Z'' ≠ 1 := by
      intro h1
      apply hbZ
      have : Z'' ≤ Z' := (Subgroup.relIndex_eq_one).mp h1
      exact this (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    rw [hjeq] at hne ⊢
    rcases j with _ | j
    · simp at hne
    · exact le_self_pow₀ hp.out.one_lt.le (by omega)
  have hz : C.relIndex B₀ ≤ p :=
    (relIndex_inf_centralizer_le_card (hDZ.trans hZc) (hDZ.trans hZB) hcomm hbB).trans hD₁
  have htow1 := Subgroup.relIndex_mul_relIndex Z' Z'' B₀ hZZ'' (hZ''C.trans hCB)
  have htow2 := Subgroup.relIndex_mul_relIndex Z'' C B₀ hZ''C hCB
  have hlt : Z''.relIndex C < n := by
    rw [← hn, ← htow1, ← htow2]
    have h1 : 0 < C.relIndex B₀ := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have h3 : 0 < Z''.relIndex C := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have h2 : 2 ≤ Z'.relIndex Z'' := le_trans hp.out.two_le hx
    have h4 : Z''.relIndex C ≤ Z''.relIndex C * C.relIndex B₀ := Nat.le_mul_of_pos_right _ h1
    nlinarith
  obtain ⟨A, hZA, hAC, hAab, hA⟩ := ih _ hlt C Z'' rfl (hB₀.to_le hCB) hZ''C hZ''c
    (hDZ.trans hZZ'') (fun c hc => Subgroup.mem_sup_left (hpow c (hCB hc)))
    (fun a ha b' hb' => hcomm a (hCB ha) b' (hCB hb'))
  refine ⟨A, hZZ''.trans hZA, hAC.trans hCB, hAab, ?_⟩
  have htow3 := Subgroup.relIndex_mul_relIndex Z' Z'' A hZZ'' hZA
  rw [← htow3, ← htow1, ← htow2]
  set x := Z'.relIndex Z''
  set a := Z''.relIndex A
  set y := Z''.relIndex C
  set z := C.relIndex B₀
  calc x * (y * z) ≤ x * (a ^ 2 * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hA hz)
    _ ≤ x * (a ^ 2 * x) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hx)
    _ = (x * a) ^ 2 := by ring

theorem card_cyclicOmegaOne_le {p : ℕ} (hp : 0 < p) (Z₀ : Subgroup Γ) (hZ₀ : IsCyclic Z₀) :
    Nat.card (cyclicOmegaOne p Z₀ hZ₀) ≤ p := by
  classical
  let _ : Fintype Z₀ := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := Z₀) hp
  let f : cyclicOmegaOne p Z₀ hZ₀ → ({a : Z₀ | a ^ p = 1} : Finset Z₀) := fun z =>
    ⟨⟨z, z.2.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; ext; simp [z.2.2]⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (f x : Z₀) = (f y : Z₀) := congrArg Subtype.val hxy
    have h2 : ((f x : Z₀) : Γ) = ((f y : Z₀) : Γ) := congrArg Subtype.val h1
    exact Subtype.ext h2
  calc Nat.card (cyclicOmegaOne p Z₀ hZ₀) ≤ Nat.card ({a : Z₀ | a ^ p = 1} : Finset Z₀) :=
        Nat.card_le_card_of_injective f hf
    _ = Finset.card ({a : Z₀ | a ^ p = 1} : Finset Z₀) := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe _
    _ ≤ p := h

theorem exists_relIndex_eq_pow_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {H K : Subgroup Γ}
    (hK : IsPGroup p K) : ∃ i : ℕ, H.relIndex K = p ^ i := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK
  have hdvd : H.relIndex K ∣ p ^ m := hm ▸ Subgroup.relIndex_dvd_card H K
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  exact ⟨i, hi⟩

end Finite

end CFSG.AGLEmbedding

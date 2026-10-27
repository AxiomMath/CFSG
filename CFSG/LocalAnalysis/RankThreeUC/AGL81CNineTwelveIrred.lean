module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixSeven

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

variable {V : Type} [Group V] [Finite V]

theorem card_modEq_card_fixed_mulAut {q : ℕ} (hq : q.Prime) {β : MulAut V} (hβ : orderOf β = q)
    {B : Subgroup V} (hB : ∀ b ∈ B, β b ∈ B) :
    Nat.card B ≡ Nat.card ↥({x : V | x ∈ B ∧ β x = x} : Set V) [MOD q] := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite ↥B := Finite.of_injective (fun b : ↥B => (b : V)) (fun _ _ h => Subtype.ext h)
  haveI : Fintype ↥B := Fintype.ofFinite ↥B
  let f : Function.End ↥B := fun b => ⟨β b, hB b b.2⟩
  have hpow : ∀ n : ℕ, ∀ b : ↥B, ((f ^ n) b : V) = (β ^ n) (b : V) := by
    intro n
    induction n with
    | zero => intro b; rfl
    | succ n ih =>
        intro b
        change (((f ^ n) * f) b : V) = (β ^ n * β) (b : V)
        change ((f ^ n) (f b) : V) = (β ^ n * β) (b : V)
        rw [ih (f b)]
        rw [show ((f b : ↥B) : V) = β (b : V) from rfl]
        rfl
  have hfq : f ^ q = 1 := by
    funext b
    apply Subtype.ext
    rw [hpow q b, ← hβ, pow_orderOf_eq_one]
    rfl
  have hfpow : f ^ q ^ 1 = 1 := by rw [pow_one]; exact hfq
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := q) (n := 1) hfpow
  have hmod' : Nat.card ↥B ≡ Nat.card ↥(f.fixedPoints) [MOD q] := by
    rw [Nat.card_eq_fintype_card (α := ↥B), Nat.card_eq_fintype_card (α := ↥(f.fixedPoints))]
    exact hmod
  have heq : ↥(f.fixedPoints) ≃ ↥({x : V | x ∈ B ∧ β x = x} : Set V) :=
    { toFun := fun b => (⟨(b.1 : V), b.1.2, congrArg Subtype.val b.2⟩ :
        ↥({x : V | x ∈ B ∧ β x = x} : Set V))
      invFun := fun x => (⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩ : ↥(f.fixedPoints))
      left_inv := fun b => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  rw [show Nat.card ↥({x : V | x ∈ B ∧ β x = x} : Set V) = Nat.card ↥(f.fixedPoints)
      from (Nat.card_congr heq).symm]
  exact hmod'

private def fixedPointsSubgroup (β : MulAut V) : Subgroup V where
  carrier := {x : V | β x = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change β a = a at ha
    change β b = b at hb
    change β (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change β a = a at ha
    change β a⁻¹ = a⁻¹
    rw [map_inv, ha]

private theorem eq_bot_or_eq_top_of_card_eq_prime_pow {p n q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcard : Nat.card V = p ^ n) {β : MulAut V} (hβ : orderOf β = q)
    (hmod : p ^ n ≡ 1 [MOD q])
    (hno : ∀ k, 0 < k → k < n → ¬ (p ^ k ≡ 1 [MOD q]))
    {B : Subgroup V} (hB : ∀ b ∈ B, β b ∈ B) : B = ⊥ ∨ B = ⊤ := by
  classical
  have hCcard : Nat.card (fixedPointsSubgroup β) = 1 := by
    have htop := card_modEq_card_fixed_mulAut (V := V) hq hβ (B := ⊤)
      (fun b _ => Subgroup.mem_top b)
    rw [Subgroup.card_top, hcard] at htop
    have hset : ({x : V | x ∈ (⊤ : Subgroup V) ∧ β x = x} : Set V)
        = (fixedPointsSubgroup β : Set V) := by
      ext x; simp [fixedPointsSubgroup]
    rw [hset] at htop
    have htop' : p ^ n ≡ Nat.card (fixedPointsSubgroup β) [MOD q] := htop
    have hdvd : Nat.card (fixedPointsSubgroup β) ∣ p ^ n := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hmodk : p ^ k ≡ 1 [MOD q] := by
      rw [← hk_eq]
      exact htop'.symm.trans hmod
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk_eq; exact hk_eq
    · rcases lt_or_eq_of_le hk_le with hklt | hkeq
      · exact absurd hmodk (hno k hkpos hklt)
      · exfalso
        have hCtop : fixedPointsSubgroup β = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [hk_eq, hkeq, hcard]
        have hβ1 : β = 1 := by
          ext x
          have hx : x ∈ fixedPointsSubgroup β := by rw [hCtop]; exact Subgroup.mem_top x
          exact hx
        rw [hβ1, orderOf_one] at hβ
        exact hq.ne_one hβ.symm
  have hSB : Nat.card ↥({x : V | x ∈ B ∧ β x = x} : Set V) = 1 := by
    have hle : ({x : V | x ∈ B ∧ β x = x} : Set V) ⊆ (fixedPointsSubgroup β : Set V) :=
      fun x hx => hx.2
    have hsub : Nat.card ↥({x : V | x ∈ B ∧ β x = x} : Set V)
        ≤ Nat.card (fixedPointsSubgroup β) :=
      Nat.card_le_card_of_injective
        (fun x : ↥({x : V | x ∈ B ∧ β x = x} : Set V) =>
          (⟨x.1, hle x.2⟩ : ↥(fixedPointsSubgroup β)))
        (fun a b hab => Subtype.ext
          (congrArg (fun y : ↥(fixedPointsSubgroup β) => (y : V)) hab))
    haveI : Nonempty ↥({x : V | x ∈ B ∧ β x = x} : Set V) := ⟨⟨1, B.one_mem, map_one β⟩⟩
    have hpos : 1 ≤ Nat.card ↥({x : V | x ∈ B ∧ β x = x} : Set V) :=
      Nat.succ_le_of_lt Nat.card_pos
    exact le_antisymm (hCcard ▸ hsub) hpos
  have hmodB : Nat.card B ≡ 1 [MOD q] := by
    have h := card_modEq_card_fixed_mulAut (V := V) hq hβ hB
    rwa [hSB] at h
  have hdvdB : Nat.card B ∣ p ^ n := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card B
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvdB
  have hmodk : p ^ k ≡ 1 [MOD q] := by
    rw [← hk_eq]
    exact hmodB
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · left
    apply Subgroup.eq_bot_of_card_eq
    rw [hk0, pow_zero] at hk_eq
    exact hk_eq
  · rcases lt_or_eq_of_le hk_le with hklt | hkeq
    · exact absurd hmodk (hno k hkpos hklt)
    · right
      apply Subgroup.eq_top_of_card_eq
      rw [hk_eq, hkeq, hcard]

theorem eq_bot_or_eq_top_of_orderOf_eq_thirteen (hV : Nat.card V = 27) {β : MulAut V}
    (hβ : orderOf β = 13) {B : Subgroup V} (hB : ∀ b ∈ B, β b ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hcard : Nat.card V = 3 ^ 3 := by rw [hV]; norm_num
  refine eq_bot_or_eq_top_of_card_eq_prime_pow (V := V) (p := 3) (n := 3) (q := 13)
    (by norm_num) (by norm_num) hcard hβ ?_ ?_ hB
  · norm_num [Nat.ModEq]
  · intro k hk0 hk3
    interval_cases k <;> norm_num [Nat.ModEq]

private theorem commutatorElement_mul_left_of_mem_center {v : V}
    (hcent : ∀ u : V, ⁅u, v⁆ ∈ center V) (u w : V) :
    ⁅u * w, v⁆ = ⁅u, v⁆ * ⁅w, v⁆ := by
  have hc : w * v * w⁻¹ = ⁅w, v⁆ * v := by
    rw [commutatorElement_def]; group
  have hcc : u * ⁅w, v⁆ * u⁻¹ = ⁅w, v⁆ := by
    calc u * ⁅w, v⁆ * u⁻¹ = ⁅w, v⁆ * u * u⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp (hcent w)) u]
      _ = ⁅w, v⁆ := by group
  calc ⁅u * w, v⁆ = u * w * v * w⁻¹ * u⁻¹ * v⁻¹ := by rw [commutatorElement_def]; group
    _ = u * (w * v * w⁻¹) * u⁻¹ * v⁻¹ := by group
    _ = u * (⁅w, v⁆ * v) * u⁻¹ * v⁻¹ := by rw [hc]
    _ = (u * ⁅w, v⁆ * u⁻¹) * (u * v * u⁻¹ * v⁻¹) := by group
    _ = ⁅w, v⁆ * ⁅u, v⁆ := by rw [hcc]; simp only [commutatorElement_def]
    _ = ⁅u, v⁆ * ⁅w, v⁆ := by
      exact ((Subgroup.mem_center_iff.mp (hcent w)) ⁅u, v⁆).symm

theorem orderOf_ne_thirteen_of_extraspecial (hV : CFSG.IsExtraspecialPGroup 3 V)
    (hcard : Nat.card V = 3 ^ 5) (β : MulAut V) : orderOf β ≠ 13 := by
  classical
  intro hβ
  have h13 : Nat.Prime 13 := by norm_num
  have hZcard : Nat.card (center V) = 3 := hV.2.2.2
  let C : Subgroup V := fixedPointsSubgroup β
  have hCcard : Nat.card C = 9 := by
    have htop := card_modEq_card_fixed_mulAut (V := V) (q := 13) h13 hβ (B := ⊤)
      (fun b _ => Subgroup.mem_top b)
    rw [Subgroup.card_top, hcard] at htop
    have hset : ({x : V | x ∈ (⊤ : Subgroup V) ∧ β x = x} : Set V) = (C : Set V) := by
      ext x; simp [C, fixedPointsSubgroup]
    rw [hset] at htop
    have hdvd : Nat.card C ∣ 3 ^ 5 := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card C
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
    have hmodk : 3 ^ k ≡ 9 [MOD 13] := by
      rw [← hk_eq]
      exact htop.symm.trans (by norm_num [Nat.ModEq] : (3 : ℕ) ^ 5 ≡ 9 [MOD 13])
    have hk : k = 2 ∨ k = 5 := by
      interval_cases k
      · norm_num [Nat.ModEq] at hmodk
      · norm_num [Nat.ModEq] at hmodk
      · exact Or.inl rfl
      · norm_num [Nat.ModEq] at hmodk
      · norm_num [Nat.ModEq] at hmodk
      · exact Or.inr rfl
    rcases hk with hk2 | hk5
    · rw [hk_eq, hk2]; norm_num
    · exfalso
      have hCtop : C = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hk_eq, hk5, hcard]
      have hβ1 : β = 1 := by
        ext x
        have hx : x ∈ C := by rw [hCtop]; exact Subgroup.mem_top x
        exact hx
      rw [hβ1, orderOf_one] at hβ
      norm_num at hβ
  have hZC : center V ≤ C := by
    have hZinv : ∀ z ∈ center V, β z ∈ center V := by
      intro z hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      calc g * β z = β (β.symm g) * β z := by rw [MulEquiv.apply_symm_apply]
        _ = β (β.symm g * z) := by rw [map_mul]
        _ = β (z * β.symm g) := by rw [hz (β.symm g)]
        _ = β z * β (β.symm g) := by rw [map_mul]
        _ = β z * g := by rw [MulEquiv.apply_symm_apply]
    have htopZ := card_modEq_card_fixed_mulAut (V := V) (q := 13) h13 hβ hZinv
    rw [hZcard] at htopZ
    have hsetZ : ({x : V | x ∈ center V ∧ β x = x} : Set V)
        = ((center V ⊓ C : Subgroup V) : Set V) := by
      ext x; simp [C, fixedPointsSubgroup]
    rw [hsetZ] at htopZ
    have hdvd : Nat.card (center V ⊓ C : Subgroup V) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (show center V ⊓ C ≤ center V from inf_le_left)
      rwa [hZcard] at h
    have hcard3 : Nat.card (center V ⊓ C : Subgroup V) = 3 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3)
          (Nat.card (center V ⊓ C : Subgroup V)) hdvd) with h1 | h3
      · exfalso
        have htopZ' : (3 : ℕ) ≡ 1 [MOD 13] := by
          rw [← h1]
          exact htopZ
        norm_num [Nat.ModEq] at htopZ'
      · exact h3
    have hZinf : center V ⊓ C = center V :=
      Subgroup.eq_of_le_of_card_ge (show center V ⊓ C ≤ center V from inf_le_left)
        (by rw [hcard3, hZcard])
    intro z hz
    have hz' : z ∈ center V ⊓ C := by rw [hZinf]; exact hz
    exact hz'.2
  have hCnotle : ¬ C ≤ center V := by
    intro hle
    have h := Subgroup.card_le_of_le hle
    rw [hCcard, hZcard] at h
    norm_num at h
  obtain ⟨v, hvC, hvnotZ⟩ := IsConcreteLE.not_le_iff_exists.mp hCnotle
  have hcent : ∀ u : V, ⁅u, v⁆ ∈ center V := by
    intro u
    rw [← hV.2.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
  let A : Subgroup V := Subgroup.centralizer ({v} : Set V)
  have hCvcard : Nat.card A = 81 := by
    let φ : V →* V :=
      { toFun := fun u => ⁅u, v⁆
        map_one' := by simp
        map_mul' := fun u w => commutatorElement_mul_left_of_mem_center hcent u w }
    have hker : φ.ker = A := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
      change ⁅u, v⁆ = 1 ↔ ∀ h ∈ ({v} : Set V), h * u = u * h
      rw [commutatorElement_eq_one_iff_mul_comm]
      constructor
      · intro h h' hh'
        rw [Set.mem_singleton_iff] at hh'
        rw [hh']
        exact h.symm
      · intro h
        exact (h v (Set.mem_singleton v)).symm
    have hrange_le : φ.range ≤ center V := by
      rintro _ ⟨u, rfl⟩
      exact hcent u
    have hrange_ne : φ.range ≠ ⊥ := by
      intro hbot
      apply hvnotZ
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : φ u ∈ φ.range := ⟨u, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hu
      rw [show φ u = ⁅u, v⁆ from rfl, commutatorElement_eq_one_iff_mul_comm] at hu
      exact hu
    have hrange_card : Nat.card φ.range = 3 := by
      have hdvd : Nat.card φ.range ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hrange_le
        rwa [hZcard] at h
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3)
          (Nat.card φ.range) hdvd) with h1 | h3
      · exfalso
        exact hrange_ne (Subgroup.eq_bot_of_card_eq φ.range h1)
      · exact h3
    have hindex : φ.ker.index = 3 := by
      rw [Subgroup.index_ker φ, hrange_card]
    have hmul := Subgroup.card_mul_index (H := φ.ker)
    rw [hindex, hker, hcard] at hmul
    norm_num at hmul
    omega
  have hAinv : ∀ a ∈ A, β a ∈ A := by
    intro a ha
    change a ∈ Subgroup.centralizer ({v} : Set V) at ha
    change β a ∈ Subgroup.centralizer ({v} : Set V)
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    have hvβ : β v = v := hvC
    calc v * β a = β v * β a := by rw [hvβ]
      _ = β (v * a) := by rw [map_mul]
      _ = β (a * v) := by rw [ha v (Set.mem_singleton v)]
      _ = β a * β v := by rw [map_mul]
      _ = β a * v := by rw [hvβ]
  have hSmod : Nat.card ↥({x : V | x ∈ A ∧ β x = x} : Set V) ≡ 3 [MOD 13] := by
    have h := card_modEq_card_fixed_mulAut (V := V) (q := 13) h13 hβ hAinv
    rw [hCvcard] at h
    exact h.symm.trans (by norm_num [Nat.ModEq] : (81 : ℕ) ≡ 3 [MOD 13])
  have hSdvd : Nat.card ↥({x : V | x ∈ A ∧ β x = x} : Set V) ∣ 9 := by
    have h := Subgroup.card_dvd_of_le (show A ⊓ C ≤ C from inf_le_right)
    rw [hCcard] at h
    exact h
  have hScard : Nat.card ↥({x : V | x ∈ A ∧ β x = x} : Set V) = 3 := by
    have hdvd : Nat.card ↥({x : V | x ∈ A ∧ β x = x} : Set V) ∣ 3 ^ 2 := by
      simpa using hSdvd
    obtain ⟨k, hk_le, hk_eq⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 2) (by norm_num)).mp hdvd
    have hmodk : 3 ^ k ≡ 3 [MOD 13] := by
      rw [← hk_eq]
      exact hSmod
    have hk1 : k = 1 := by
      interval_cases k
      · norm_num [Nat.ModEq] at hmodk
      · rfl
      · norm_num [Nat.ModEq] at hmodk
    rw [hk_eq, hk1]; norm_num
  have hZle : center V ≤ A ⊓ C := by
    intro z hz
    constructor
    · change z ∈ Subgroup.centralizer ({v} : Set V)
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact (Subgroup.mem_center_iff.mp hz) v
    · exact hZC hz
  have hAZ : A ⊓ C = center V := by
    have hle := Subgroup.eq_of_le_of_card_ge (show center V ≤ A ⊓ C from hZle)
      (by rw [hZcard]; exact le_of_eq hScard)
    exact hle.symm
  have hvA : v ∈ A := by
    change v ∈ Subgroup.centralizer ({v} : Set V)
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
  have hvZ : v ∈ center V := by
    rw [← hAZ]
    exact ⟨hvA, hvC⟩
  exact hvnotZ hvZ

theorem isIrreducibleAut_of_orderOf_eq_thirteen {D : Type} [Group D] [Finite D]
    (hD : Nat.card D = 27) {W : Subgroup (MulAut D)} {x : MulAut D} (hxW : x ∈ W)
    (hx : orderOf x = 13) : IsIrreducibleAut W := by
  intro B hB
  exact eq_bot_or_eq_top_of_orderOf_eq_thirteen (V := D) hD hx (fun b hb => hB x hxW b hb)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

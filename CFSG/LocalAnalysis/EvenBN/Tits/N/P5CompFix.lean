module

public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Comp

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N.P5

section Fixed

variable {Q : Type*} [Group Q]

@[expose] def restrictEnd (φ : MulAut Q) (B : Subgroup Q) (hB : ∀ b ∈ B, φ b ∈ B) :
    Function.End B := fun b => ⟨φ b, hB b b.2⟩

theorem coe_restrictEnd_pow (φ : MulAut Q) (B : Subgroup Q) (hB : ∀ b ∈ B, φ b ∈ B) (n : ℕ)
    (b : B) : (((restrictEnd φ B hB ^ n) b : B) : Q) = (φ ^ n) b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply]
    exact (ih (restrictEnd φ B hB b)).trans (by rfl)

theorem mem_fixedPoints_restrictEnd (φ : MulAut Q) (B : Subgroup Q) (hB : ∀ b ∈ B, φ b ∈ B)
    (b : B) : b ∈ Function.fixedPoints (restrictEnd φ B hB) ↔ φ b = b := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem card_modEq_card_fixedPoints {p : ℕ} [Fact p.Prime] {φ : MulAut Q} (hφ : φ ^ p = 1)
    {B : Subgroup Q} [Finite B] (hB : ∀ b ∈ B, φ b ∈ B) :
    Nat.card B ≡ Nat.card (Function.fixedPoints (restrictEnd φ B hB)) [MOD p] := by
  classical
  haveI := Fintype.ofFinite B
  have hfp : restrictEnd φ B hB ^ p ^ 1 = 1 := by
    funext b
    apply Subtype.ext
    rw [pow_one, coe_restrictEnd_pow, hφ]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := restrictEnd φ B hB) (p := p) (n := 1) hfp
  simpa only [← Nat.card_eq_fintype_card] using h

theorem card_modEq_one_of_fpf {p : ℕ} [Fact p.Prime] {φ : MulAut Q} (hφ : φ ^ p = 1)
    {B : Subgroup Q} [Finite B] (hB : ∀ b ∈ B, φ b ∈ B) (hfpf : ∀ b ∈ B, φ b = b → b = 1) :
    Nat.card B ≡ 1 [MOD p] := by
  have h := card_modEq_card_fixedPoints hφ hB
  have h1 : Nat.card (Function.fixedPoints (restrictEnd φ B hB)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩,
      ⟨⟨1, (mem_fixedPoints_restrictEnd φ B hB 1).2 (map_one φ)⟩⟩⟩
    have ha1 := hfpf a a.2 ((mem_fixedPoints_restrictEnd φ B hB a).1 ha)
    have hb1 := hfpf b b.2 ((mem_fixedPoints_restrictEnd φ B hB b).1 hb)
    exact Subtype.ext (Subtype.ext (ha1.trans hb1.symm))
  rwa [h1] at h

theorem exists_fixed_ne_one {p : ℕ} [Fact p.Prime] {ψ : MulAut Q} (hψ : ψ ^ p = 1)
    {B : Subgroup Q} [Finite B] (hB : ∀ b ∈ B, ψ b ∈ B) (hp : p ∣ Nat.card B) :
    ∃ b ∈ B, b ≠ 1 ∧ ψ b = b := by
  have h := card_modEq_card_fixedPoints hψ hB
  have hdvd : p ∣ Nat.card (Function.fixedPoints (restrictEnd ψ B hB)) :=
    Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hp))
  haveI : Finite (Function.fixedPoints (restrictEnd ψ B hB)) := inferInstance
  have hpos : 0 < Nat.card (Function.fixedPoints (restrictEnd ψ B hB)) :=
    Nat.card_pos_iff.2 ⟨⟨⟨1, (mem_fixedPoints_restrictEnd ψ B hB 1).2 (map_one ψ)⟩⟩, inferInstance⟩
  have h1 : 1 < Nat.card (Function.fixedPoints (restrictEnd ψ B hB)) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvd)
  haveI := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne
    (⟨1, (mem_fixedPoints_restrictEnd ψ B hB 1).2 (map_one ψ)⟩ :
      Function.fixedPoints (restrictEnd ψ B hB))
  refine ⟨b, b.2, fun hb1' => hb1 ?_, (mem_fixedPoints_restrictEnd ψ B hB b).1 hb⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hb1'

end Fixed

section Invariant

variable {Q : Type*} [Group Q] [Finite Q]

theorem card_eq_two_pow_of_le {Ab B : Subgroup Q} (hcard : Nat.card Ab = 256) (hBA : B ≤ Ab) :
    ∃ k, k ≤ 8 ∧ Nat.card B = 2 ^ k := by
  have h : Nat.card B ∣ 2 ^ 8 := by
    have := Subgroup.card_dvd_of_le hBA
    rwa [hcard] at this
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem le_of_invariant {Ab U B : Subgroup Q} {φ ψ : MulAut Q}
    (hcard : Nat.card Ab = 256) (hφ : φ ^ 5 = 1) (hψ : ψ ^ 2 = 1) (hcomm : φ * ψ = ψ * φ)
    (hφA : ∀ a ∈ Ab, φ a ∈ Ab) (hψA : ∀ a ∈ Ab, ψ a ∈ Ab)
    (hfpf : ∀ a ∈ Ab, φ a = a → a = 1)
    (hUA : U ≤ Ab) (hU : ∀ a ∈ Ab, ψ a = a ↔ a ∈ U) (hU16 : Nat.card U = 16)
    (hBA : B ≤ Ab) (hφB : ∀ b ∈ B, φ b ∈ B) (hψB : ∀ b ∈ B, ψ b ∈ B) (hB : B ≠ ⊥) :
    U ≤ B := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := card_eq_two_pow_of_le hcard hBA
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hB (Subgroup.card_eq_one.1 (by simpa using hk))
  have h2 : 2 ∣ Nat.card B := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨b, hbB, hb1, hψb⟩ := exists_fixed_ne_one hψ hψB h2
  have hbU : b ∈ U := (hU b (hBA hbB)).1 hψb
  have hinv : ∀ c ∈ B ⊓ U, φ c ∈ B ⊓ U := by
    intro c hc
    rw [Subgroup.mem_inf] at hc ⊢
    refine ⟨hφB c hc.1, ?_⟩
    have hcA : c ∈ Ab := hBA hc.1
    rw [← hU _ (hφA c hcA)]
    have hc' : ψ c = c := (hU c hcA).2 hc.2
    calc ψ (φ c) = (ψ * φ) c := rfl
      _ = (φ * ψ) c := by rw [hcomm]
      _ = φ c := by rw [MulAut.mul_apply, hc']
  have hmod : Nat.card ↥(B ⊓ U) ≡ 1 [MOD 5] :=
    card_modEq_one_of_fpf hφ hinv fun c hc h => hfpf c (hBA (Subgroup.mem_inf.1 hc).1) h
  have hdvd : Nat.card ↥(B ⊓ U) ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : B ⊓ U ≤ U)
    rwa [hU16] at this
  obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne : Nat.card ↥(B ⊓ U) ≠ 1 := by
    intro h1
    have := Subgroup.card_eq_one.1 h1
    have hb' : b ∈ B ⊓ U := Subgroup.mem_inf.2 ⟨hbB, hbU⟩
    rw [this, Subgroup.mem_bot] at hb'
    exact hb1 hb'
  have h16 : Nat.card ↥(B ⊓ U) = 16 := by
    rw [hmc] at hmod hne ⊢
    interval_cases m <;> simp_all [Nat.ModEq]
  have heq : B ⊓ U = U :=
    Subgroup.eq_of_le_of_card_ge (inf_le_right : B ⊓ U ≤ U) (by rw [h16, hU16])
  rw [← heq]
  exact inf_le_left

theorem card_eq_of_invariant {Ab B : Subgroup Q} {φ : MulAut Q}
    (hcard : Nat.card Ab = 256) (hφ : φ ^ 5 = 1) (hφA : ∀ a ∈ Ab, φ a ∈ Ab)
    (hfpf : ∀ a ∈ Ab, φ a = a → a = 1) (hBA : B ≤ Ab) (hφB : ∀ b ∈ B, φ b ∈ B) :
    Nat.card B = 1 ∨ Nat.card B = 16 ∨ Nat.card B = 256 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk8, hk⟩ := card_eq_two_pow_of_le hcard hBA
  have hmod : Nat.card B ≡ 1 [MOD 5] :=
    card_modEq_one_of_fpf hφ hφB fun c hc h => hfpf c (hBA hc) h
  rw [hk] at hmod ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

end Invariant

section Components

variable {Q : Type} [Group Q] [Finite Q]

theorem isComponentOf_map_mulAut (e : MulAut Q) {K : Subgroup Q} (hK : IsComponentOf K ⊤) :
    IsComponentOf (K.map e.toMonoidHom) ⊤ := by
  have h := G310.isComponentOf_map_mulEquiv e hK
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h

theorem comm_of_components {K L : Subgroup Q} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hne : K ≠ L) : ∀ y ∈ L, ∀ k ∈ K, y * k = k * y := by
  intro y hy k hk
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b Q K L hK hL hne)
  exact (Subgroup.mem_centralizer_iff.1 (h hk) y hy)

@[expose] def partialNorm (φ : MulAut Q) (b : Q) : ℕ → Q
  | 0 => 1
  | j + 1 => partialNorm φ b j * (φ ^ j) b

theorem partialNorm_succ (φ : MulAut Q) (b : Q) (j : ℕ) :
    partialNorm φ b (j + 1) = partialNorm φ b j * (φ ^ j) b := rfl

theorem partialNorm_succ' (φ : MulAut Q) (b : Q) (j : ℕ) :
    partialNorm φ b (j + 1) = b * φ (partialNorm φ b j) := by
  induction j with
  | zero => simp [partialNorm_succ, partialNorm]
  | succ j ih =>
    have h1 : partialNorm φ b (j + 1 + 1) = (b * φ (partialNorm φ b j)) * (φ ^ (j + 1)) b := by
      rw [partialNorm_succ φ b (j + 1), ih]
    have h2 : b * φ (partialNorm φ b (j + 1)) =
        b * (φ (partialNorm φ b j) * (φ ^ (j + 1)) b) := by
      rw [partialNorm_succ φ b j, map_mul, pow_succ' φ j, MulAut.mul_apply]
    rw [h1, h2, mul_assoc]

theorem map_eq_of_fpf {p : ℕ} [Fact p.Prime] {φ : MulAut Q} (hφ : φ ^ p = 1)
    {Ab : Subgroup Q} (hab : ∀ a ∈ Ab, ∀ b ∈ Ab, a * b = b * a) (hφA : ∀ a ∈ Ab, φ a ∈ Ab)
    (hfpf : ∀ a ∈ Ab, φ a = a → a = 1) {K : Subgroup Q} (hK : IsComponentOf K ⊤)
    {b : Q} (hbA : b ∈ Ab) (hbK : b ∈ K) (hbc : ∃ k ∈ K, b * k ≠ k * b) :
    K.map φ.toMonoidHom = K := by
  by_contra hne
  have hpow : ∀ (n : ℕ) (a : Q), a ∈ Ab → (φ ^ n) a ∈ Ab := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hφA a ha)
  have hmapmul : ∀ (e f : MulAut Q) (L : Subgroup Q),
      L.map (e * f).toMonoidHom = (L.map f.toMonoidHom).map e.toMonoidHom := by
    intro e f L
    rw [Subgroup.map_map]
    rfl
  have hdist : ∀ i, 1 ≤ i → i < p → K.map (φ ^ i).toMonoidHom ≠ K := by
    intro i hi1 hip heq
    apply hne
    obtain ⟨j, hj⟩ : ∃ j, i * j % p = 1 := by
      have hcop : Nat.Coprime i p := by
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2
          (Nat.not_dvd_of_pos_of_lt (by omega) hip)
      obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : p.Prime).one_lt
      exact ⟨j, hj⟩
    have hpw : (φ ^ i) ^ j = φ := by
      rw [← pow_mul]
      have h1 : i * j = p * (i * j / p) + 1 := by
        have := Nat.div_add_mod (i * j) p
        omega
      rw [h1, pow_add, pow_mul, hφ, one_pow, one_mul, pow_one]
    have hit : ∀ n : ℕ, K.map ((φ ^ i) ^ n).toMonoidHom = K := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero]
        exact (Subgroup.map_id K : K.map (MonoidHom.id Q) = K)
      | succ n ih => rw [pow_succ, hmapmul, heq, ih]
    rw [← hpw]
    exact hit j
  have hcomm : ∀ i, 1 ≤ i → i < p → ∀ y ∈ K, ∀ k ∈ K, (φ ^ i) y * k = k * (φ ^ i) y := by
    intro i hi1 hip y hy k hk
    exact comm_of_components hK (isComponentOf_map_mulAut (φ ^ i) hK) (hdist i hi1 hip).symm
      _ ⟨y, hy, rfl⟩ k hk
  have hmem : ∀ j, partialNorm φ b j ∈ Ab := by
    intro j
    induction j with
    | zero => exact Ab.one_mem
    | succ j ih => exact Ab.mul_mem ih (hpow j b hbA)
  have hcent : ∀ j, j + 1 ≤ p → φ (partialNorm φ b j) ∈ centralizer (K : Set Q) := by
    intro j
    induction j with
    | zero => intro _; simp [partialNorm]
    | succ j ih =>
      intro hj
      have h1 : φ (partialNorm φ b (j + 1)) = φ (partialNorm φ b j) * (φ ^ (j + 1)) b := by
        rw [partialNorm, map_mul, pow_succ' φ j, MulAut.mul_apply]
      rw [h1]
      refine Subgroup.mul_mem _ (ih (by omega)) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm (j + 1) (by omega) (by omega) b hbK k hk).symm
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  have hc : φ (partialNorm φ b m) ∈ centralizer (K : Set Q) := hcent m (by omega)
  have hcA : φ (partialNorm φ b m) ∈ Ab := hφA _ (hmem m)
  have hn : partialNorm φ b p = b * φ (partialNorm φ b m) := by
    rw [hm, partialNorm_succ']
  have hφn : φ (partialNorm φ b p) = partialNorm φ b p := by
    have h1 : partialNorm φ b p = partialNorm φ b m * (φ ^ m) b := by rw [hm, partialNorm]
    have h2 : φ (partialNorm φ b p) = φ (partialNorm φ b m) * b := by
      rw [h1, map_mul, ← MulAut.mul_apply, ← pow_succ' φ m, ← hm, hφ]
      rfl
    rw [h2, hn]
    exact hab _ hcA b hbA
  have hnA : partialNorm φ b p ∈ Ab := hmem p
  have hn1 : partialNorm φ b p = 1 := hfpf _ hnA hφn
  obtain ⟨k, hk, hbk⟩ := hbc
  apply hbk
  have hb : b = (φ (partialNorm φ b m))⁻¹ := by
    rw [hn] at hn1
    exact eq_inv_of_mul_eq_one_left hn1
  have hck := Subgroup.mem_centralizer_iff.1 hc k hk
  rw [hb]
  have : (φ (partialNorm φ b m))⁻¹ * k = k * (φ (partialNorm φ b m))⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hck, mul_assoc, mul_inv_cancel, mul_one]
  exact this

theorem map_eq_of_involution {ψ : MulAut Q} (hψ : ψ ^ 2 = 1) {K : Subgroup Q}
    (hK : IsComponentOf K ⊤) (hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z = 1)
    (hsolv : Group.IsSolvable ↥(fixSub ψ)) : K.map ψ.toMonoidHom = K := by
  by_contra hne
  have hψψ : ∀ x, ψ (ψ x) = x := fun x => by
    have := congrArg (fun e : MulAut Q => e x) hψ
    simpa [pow_two] using this
  have hcomm : ∀ y ∈ K.map ψ.toMonoidHom, ∀ k ∈ K, y * k = k * y :=
    comm_of_components hK (isComponentOf_map_mulAut ψ hK) (Ne.symm hne)
  let f : K →* Q := MonoidHom.mk' (fun k => (k : Q) * ψ k) (by
    intro k₁ k₂
    have h := hcomm (ψ k₁) ⟨k₁, k₁.2, rfl⟩ k₂ k₂.2
    simp only [Subgroup.coe_mul, map_mul]
    calc (k₁ : Q) * k₂ * (ψ k₁ * ψ k₂) = k₁ * (k₂ * ψ k₁) * ψ k₂ := by group
      _ = k₁ * (ψ k₁ * k₂) * ψ k₂ := by rw [h]
      _ = k₁ * ψ k₁ * (k₂ * ψ k₂) := by group)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (k : Q) * ψ k = 1 := hk
    have h1 : ψ k = (k : Q)⁻¹ := eq_inv_of_mul_eq_one_right hk'
    have hkK' : (k : Q) ∈ K.map ψ.toMonoidHom := by
      have h2 : (k : Q)⁻¹ ∈ K.map ψ.toMonoidHom := ⟨k, k.2, h1⟩
      simpa using Subgroup.inv_mem _ h2
    exact Subtype.ext (hZ k k.2 fun k' hk' => hcomm _ hkK' k' hk')
  have hfix : ∀ k : K, f k ∈ fixSub ψ := by
    intro k
    show ψ ((k : Q) * ψ k) = (k : Q) * ψ k
    rw [map_mul, hψψ]
    exact hcomm (ψ k) ⟨k, k.2, rfl⟩ k k.2
  let g : K →* ↥(fixSub ψ) := f.codRestrict (fixSub ψ) hfix
  haveI : Group.IsSolvable K :=
    solvable_of_solvable_injective (f := g) (fun a b h => hfinj (congrArg Subtype.val h))
  haveI : Nontrivial K := CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2
  haveI : Group.IsPerfect K := ⟨hK.2.2.1⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

end Components

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Comp

module

public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
public import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.OrderThreePairCommutator

open scoped commutatorElement
open CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

private lemma eq_one_of_pow_three_eq_one {P : Type*} [Group P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp : p ≠ 3) {y : P} (hy : y ^ 3 = 1) : y = 1 := by
  have hcop : p.Coprime 3 :=
    (Nat.coprime_primes (Fact.out : Nat.Prime p) Nat.prime_three).mpr hp
  exact orderOf_eq_one_iff.mp
    ((hP.orderOf_coprime hcop y).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hy))

private lemma map_eq_self_of_forall_mem {P : Type*} [Group P] [Finite P] (N : Subgroup P)
    (α : MulAut P) (h : ∀ n ∈ N, α n ∈ N) : N.map (α : P →* P) = N := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨n, hn, rfl⟩
    exact h n hn
  · rw [Subgroup.card_map_of_injective α.injective]

private lemma map_apply_map_of_commute {P : Type*} [Group P] {α β : MulAut P}
    (h : Commute α β) (x : P) : α (β x) = β (α x) := by
  have h' := congrArg (fun e : MulAut P => e x) h.eq
  simpa [MulAut.mul_apply] using h'

private lemma map_mem_center {P : Type*} [Group P] (α : MulAut P) {z : P}
    (hz : z ∈ Subgroup.center P) : α z ∈ Subgroup.center P := by
  have hmap : Subgroup.map (α : P →* P) (Subgroup.center P) = Subgroup.center P :=
    (Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic) α
  rw [← hmap]
  exact Subgroup.mem_map_of_mem (α : P →* P) hz

private lemma apply_apply_apply_of_pow_three {P : Type*} [Group P] {α : MulAut P}
    (hα : α ^ 3 = 1) (x : P) : α (α (α x)) = x := by
  have h := congrArg (fun e : MulAut P => e x) hα
  simpa [pow_succ, MulAut.mul_apply] using h

private lemma center_norm_fixed {P : Type*} [Group P]
    (α : MulAut (Subgroup.center P)) (hα : α ^ 3 = 1) (z : Subgroup.center P) :
    α (z * α z * α (α z)) = z * α z * α (α z) := by
  have hα3 := apply_apply_apply_of_pow_three hα z
  simp only [map_mul]
  rw [hα3]
  ac_rfl

private lemma center_induced_data {P : Type*} [Group P] {φ ψ : MulAut P}
    (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ) :
    ∃ (φZ ψZ : MulAut (Subgroup.center P)),
      φZ ^ 3 = 1 ∧ ψZ ^ 3 = 1 ∧ Commute φZ ψZ ∧
      (∀ z : Subgroup.center P, ψZ (φZ z) = φZ (ψZ z)) ∧
      (∀ z : Subgroup.center P, ((φZ z : Subgroup.center P) : P) = φ (z : P)) ∧
      (∀ z : Subgroup.center P, ((ψZ z : Subgroup.center P) : P) = ψ (z : P)) := by
  let Z := Subgroup.center P
  let φZ : MulAut Z := MulAut.characteristic Z φ
  let ψZ : MulAut Z := MulAut.characteristic Z ψ
  have hφZ : φZ ^ 3 = 1 := by
    change (MulAut.characteristic Z φ) ^ 3 = 1
    rw [← map_pow, hφ, map_one]
  have hψZ : ψZ ^ 3 = 1 := by
    change (MulAut.characteristic Z ψ) ^ 3 = 1
    rw [← map_pow, hψ, map_one]
  have hφψZ : Commute φZ ψZ := by
    show (MulAut.characteristic Z) φ * (MulAut.characteristic Z) ψ =
      (MulAut.characteristic Z) ψ * (MulAut.characteristic Z) φ
    rw [← map_mul, ← map_mul, hφψ.eq]
  have hψφZ : ∀ z : Z, ψZ (φZ z) = φZ (ψZ z) := fun z =>
    (map_apply_map_of_commute hφψZ z).symm
  have hφZcoe : ∀ z : Z, ((φZ z : Z) : P) = φ (z : P) := fun z =>
    MulAut.characteristic_apply_apply_coe Z φ z
  have hψZcoe : ∀ z : Z, ((ψZ z : Z) : P) = ψ (z : P) := fun z =>
    MulAut.characteristic_apply_apply_coe Z ψ z
  exact ⟨φZ, ψZ, hφZ, hψZ, hφψZ, hψφZ, hφZcoe, hψZcoe⟩

private lemma center_pow_three_eq_one_of_no_fixed {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hp : p ≠ 3)
    {φ ψ : MulAut P} (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ)
    (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
    (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x)
    (hφfix : ∀ z : P, z ∈ Subgroup.center P → φ z = z → z = 1)
    (hψfix : ∀ z : P, z ∈ Subgroup.center P → ψ z = z → z = 1) :
    ∀ z : Subgroup.center P, z ^ 3 = 1 := by
  obtain ⟨φZ, ψZ, hφZ, hψZ, hφψZ, hψφZ, hφZcoe, hψZcoe⟩ :=
    center_induced_data hφ hψ hφψ
  intro z
  let a₁ : Subgroup.center P := z * φZ z * φZ (φZ z)
  let a₂ : Subgroup.center P := z * ψZ z * ψZ (ψZ z)
  let β : MulAut (Subgroup.center P) := φZ * ψZ
  let γ : MulAut (Subgroup.center P) := φZ * ψZ ^ 2
  let a₃ : Subgroup.center P := z * φZ (ψZ z) * φZ (φZ (ψZ (ψZ z)))
  let a₄ : Subgroup.center P := z * φZ (ψZ (ψZ z)) * φZ (φZ (ψZ z))
  have hβ3 : β ^ 3 = 1 := by
    dsimp [β]
    rw [hφψZ.mul_pow, hφZ, hψZ, one_mul]
  have hψ2pow : (ψZ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul]
    rw [show 2 * 3 = 3 * 2 by norm_num, pow_mul, hψZ]
    simp
  have hγ3 : γ ^ 3 = 1 := by
    dsimp [γ]
    rw [(hφψZ.pow_right 2).mul_pow, hφZ, hψ2pow, mul_one]
  have hψZ3 : ∀ y : Subgroup.center P, ψZ (ψZ (ψZ y)) = y := fun y =>
    apply_apply_apply_of_pow_three hψZ y
  have ha₁ : a₁ = 1 := by
    have hfixZ : φZ a₁ = a₁ := by
      simpa [a₁] using center_norm_fixed φZ hφZ z
    have hfixP : φ (a₁ : P) = (a₁ : P) := by
      rw [← hφZcoe]
      exact congrArg Subtype.val hfixZ
    exact Subtype.ext (hφfix (a₁ : P) a₁.2 hfixP)
  have ha₂ : a₂ = 1 := by
    have hfixZ : ψZ a₂ = a₂ := by
      simpa [a₂] using center_norm_fixed ψZ hψZ z
    have hfixP : ψ (a₂ : P) = (a₂ : P) := by
      rw [← hψZcoe]
      exact congrArg Subtype.val hfixZ
    exact Subtype.ext (hψfix (a₂ : P) a₂.2 hfixP)
  have ha₃β : a₃ = z * β z * β (β z) := by
    dsimp [a₃, β]
    simp only [MulAut.mul_apply, hψφZ]
  have ha₃ : a₃ = 1 := by
    have hβfix : β a₃ = a₃ := by
      rw [ha₃β]
      exact center_norm_fixed β hβ3 z
    have hβfixP : φ (ψ (a₃ : P)) = (a₃ : P) := by
      calc φ (ψ (a₃ : P)) = φ ((ψZ a₃ : Subgroup.center P) : P) := by rw [hψZcoe]
        _ = ((φZ (ψZ a₃) : Subgroup.center P) : P) := by rw [hφZcoe]
        _ = (((φZ * ψZ) a₃ : Subgroup.center P) : P) := by rw [MulAut.mul_apply]
        _ = ((a₃ : Subgroup.center P) : P) := congrArg Subtype.val hβfix
    exact Subtype.ext (hφfix (a₃ : P) a₃.2 (h₁ (a₃ : P) hβfixP))
  have hψ2coe : ∀ y : Subgroup.center P,
      (((ψZ ^ 2) y : Subgroup.center P) : P) = ψ (ψ (y : P)) := by
    intro y
    rw [pow_two, MulAut.mul_apply, hψZcoe, hψZcoe]
  have ha₄γ : a₄ = z * γ z * γ (γ z) := by
    dsimp [a₄, γ]
    simp only [MulAut.mul_apply, pow_two, hψφZ, hψZ3]
  have ha₄ : a₄ = 1 := by
    have hγfix : γ a₄ = a₄ := by
      rw [ha₄γ]
      exact center_norm_fixed γ hγ3 z
    have hγfixP : φ (ψ (ψ (a₄ : P))) = (a₄ : P) := by
      calc φ (ψ (ψ (a₄ : P))) = φ (((ψZ ^ 2) a₄ : Subgroup.center P) : P) := by
            rw [hψ2coe]
        _ = ((φZ ((ψZ ^ 2) a₄) : Subgroup.center P) : P) := by rw [hφZcoe]
        _ = (((φZ * ψZ ^ 2) a₄ : Subgroup.center P) : P) := by rw [MulAut.mul_apply]
        _ = ((a₄ : Subgroup.center P) : P) := congrArg Subtype.val hγfix
    exact Subtype.ext (hφfix (a₄ : P) a₄.2 (h₂ (a₄ : P) hγfixP))
  have hprod : a₁ * a₂ * a₃ * a₄ = z ^ 3 * (a₁ * ψZ a₁ * ψZ (ψZ a₁)) := by
    dsimp [a₁, a₂, a₃, a₄]
    simp only [map_mul, hψφZ, pow_three]
    ac_rfl
  have hz3 : z ^ 3 = 1 := by
    have h := hprod
    rw [ha₁, ha₂, ha₃, ha₄] at h
    simpa using h.symm
  exact hz3

private lemma exists_nontrivial_center_fixed {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hp : p ≠ 3) (hPnt : Nontrivial P)
    {φ ψ : MulAut P} (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ)
    (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
    (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x) :
    (∃ z : P, z ∈ Subgroup.center P ∧ z ≠ 1 ∧ φ z = z) ∨
      (∃ z : P, z ∈ Subgroup.center P ∧ z ≠ 1 ∧ ψ z = z) := by
  haveI : Nontrivial P := hPnt
  by_contra hcon
  have hφcon : ¬ ∃ z : P, z ∈ Subgroup.center P ∧ z ≠ 1 ∧ φ z = z :=
    fun h => hcon (Or.inl h)
  have hψcon : ¬ ∃ z : P, z ∈ Subgroup.center P ∧ z ≠ 1 ∧ ψ z = z :=
    fun h => hcon (Or.inr h)
  have hφfix : ∀ z : P, z ∈ Subgroup.center P → φ z = z → z = 1 := by
    intro z hz hzfix
    by_contra hz1
    exact hφcon ⟨z, hz, hz1, hzfix⟩
  have hψfix : ∀ z : P, z ∈ Subgroup.center P → ψ z = z → z = 1 := by
    intro z hz hzfix
    by_contra hz1
    exact hψcon ⟨z, hz, hz1, hzfix⟩
  have hcube := center_pow_three_eq_one_of_no_fixed hP hp hφ hψ hφψ h₁ h₂ hφfix hψfix
  have hZbot : Subgroup.center P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have h := congrArg Subtype.val (hcube ⟨z, hz⟩)
      simpa using h
    exact eq_one_of_pow_three_eq_one hP hp hz3
  have hZnt : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt hZbot

private lemma exists_central_fixed_subgroup_of_fixed {P : Type*} [Group P]
    {α β : MulAut P} (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (hαβ : Commute α β)
    {z : P} (hzZ : z ∈ Subgroup.center P) (hz1 : z ≠ 1) (hzfix : α z = z) :
    ∃ N : Subgroup P, N ≠ ⊥ ∧ N ≤ Subgroup.center P ∧
      (∀ n ∈ N, α n = n) ∧ (∀ n ∈ N, α n ∈ N) ∧ (∀ n ∈ N, β n ∈ N) := by
  let S : Set P := {z, β z, β (β z)}
  let N : Subgroup P := Subgroup.closure S
  have hzN : z ∈ N := Subgroup.subset_closure (by simp [S])
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hz : z = 1 := by simpa [hbot] using hzN
    exact hz1 hz
  have hNcenter : N ≤ Subgroup.center P := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]
      exact hzZ
    · rw [h]
      exact map_mem_center β hzZ
    · rw [h]
      exact map_mem_center β (map_mem_center β hzZ)
  have hαβz : α (β z) = β z := by
    calc α (β z) = β (α z) := map_apply_map_of_commute hαβ z
      _ = β z := by rw [hzfix]
  have hαfix : ∀ n ∈ N, α n = n := by
    have hle : N ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id P) := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h
      · rw [h]
        change α z = z
        exact hzfix
      · rw [h]
        change α (β z) = β z
        exact hαβz
      · rw [h]
        change α (β (β z)) = β (β z)
        calc α (β (β z)) = β (α (β z)) := map_apply_map_of_commute hαβ (β z)
          _ = β (β z) := by rw [hαβz]
    intro n hn
    have h := hle hn
    change α n = n at h
    exact h
  have hαN : ∀ n ∈ N, α n ∈ N := by
    intro n hn
    rw [hαfix n hn]
    exact hn
  have hβN : ∀ n ∈ N, β n ∈ N := by
    have hle : N ≤ Subgroup.comap β.toMonoidHom N := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h
      · rw [h]
        change β z ∈ N
        exact Subgroup.subset_closure (by simp [S])
      · rw [h]
        change β (β z) ∈ N
        exact Subgroup.subset_closure (by simp [S])
      · rw [h]
        change β (β (β z)) ∈ N
        rw [apply_apply_apply_of_pow_three hβ z]
        exact hzN
    intro n hn
    exact Subgroup.mem_comap.mp (hle hn)
  exact ⟨N, hNne, hNcenter, hαfix, hαN, hβN⟩

private lemma exists_central_fixed_subgroup {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hp : p ≠ 3) (hPnt : Nontrivial P)
    {φ ψ : MulAut P} (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ)
    (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
    (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x) :
    ∃ N : Subgroup P, N ≠ ⊥ ∧ N ≤ Subgroup.center P ∧
      ((∀ n ∈ N, φ n = n) ∨ (∀ n ∈ N, ψ n = n)) ∧
      (∀ n ∈ N, φ n ∈ N) ∧ (∀ n ∈ N, ψ n ∈ N) := by
  rcases exists_nontrivial_center_fixed hP hp hPnt hφ hψ hφψ h₁ h₂ with
    ⟨z, hzZ, hz1, hzfix⟩ | ⟨z, hzZ, hz1, hzfix⟩
  · obtain ⟨N, hne, hcen, hfix, hφN, hψN⟩ :=
      exists_central_fixed_subgroup_of_fixed hφ hψ hφψ hzZ hz1 hzfix
    exact ⟨N, hne, hcen, Or.inl hfix, hφN, hψN⟩
  · obtain ⟨N, hne, hcen, hfix, hψN, hφN⟩ :=
      exists_central_fixed_subgroup_of_fixed hψ hφ hφψ.symm hzZ hz1 hzfix
    exact ⟨N, hne, hcen, Or.inr hfix, hφN, hψN⟩

private noncomputable def quotientAut {P : Type*} [Group P] [Finite P]
    (N : Subgroup P) [N.Normal] (α : MulAut P) (hαN : ∀ n ∈ N, α n ∈ N) :
    MulAut (P ⧸ N) :=
  QuotientGroup.congr N N α (map_eq_self_of_forall_mem N α hαN)

private lemma quotientAut_mk {P : Type*} [Group P] [Finite P] (N : Subgroup P) [N.Normal]
    (α : MulAut P) (hαN : ∀ n ∈ N, α n ∈ N) (x : P) :
    quotientAut N α hαN (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk N N α _ x

private lemma quotientAut_pow_three {P : Type*} [Group P] [Finite P] (N : Subgroup P)
    [N.Normal] {α : MulAut P} (hα : α ^ 3 = 1) (hαN : ∀ n ∈ N, α n ∈ N) :
    quotientAut N α hαN ^ 3 = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    calc (quotientAut N α hαN ^ 3) (QuotientGroup.mk x)
        = quotientAut N α hαN
            (quotientAut N α hαN (quotientAut N α hαN (QuotientGroup.mk x))) := by
          simp [pow_succ, MulAut.mul_apply]
      _ = QuotientGroup.mk (α (α (α x))) := by
          rw [quotientAut_mk, quotientAut_mk, quotientAut_mk]
      _ = QuotientGroup.mk x := by rw [apply_apply_apply_of_pow_three hα]
      _ = (1 : MulAut (P ⧸ N)) (QuotientGroup.mk x) := by simp

private lemma quotientAut_commute {P : Type*} [Group P] [Finite P] (N : Subgroup P)
    [N.Normal] {α β : MulAut P} (hαN : ∀ n ∈ N, α n ∈ N)
    (hβN : ∀ n ∈ N, β n ∈ N) (hαβ : Commute α β) :
    Commute (quotientAut N α hαN) (quotientAut N β hβN) := by
  show quotientAut N α hαN * quotientAut N β hβN =
    quotientAut N β hβN * quotientAut N α hαN
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply]
    rw [quotientAut_mk, quotientAut_mk, quotientAut_mk, quotientAut_mk]
    exact congrArg QuotientGroup.mk (map_apply_map_of_commute hαβ x)

private lemma quotientAut_fixed {P : Type*} [Group P] [Finite P]
    {N : Subgroup P} [N.Normal] {φ ψ : MulAut P}
    (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ)
    (hφN : ∀ n ∈ N, φ n ∈ N) (hψN : ∀ n ∈ N, ψ n ∈ N)
    (hnot3 : ¬ 3 ∣ Nat.card N)
    (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
    (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x) :
    (∀ q, quotientAut N φ hφN (quotientAut N ψ hψN q) = q →
      quotientAut N φ hφN q = q) ∧
    (∀ q, quotientAut N φ hφN (quotientAut N ψ hψN (quotientAut N ψ hψN q)) = q →
      quotientAut N φ hφN q = q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφψ3 : (φ * ψ) ^ 3 = 1 := by
    rw [hφψ.mul_pow, hφ, hψ, one_mul]
  have hφψN : ∀ n ∈ N, (φ * ψ) n ∈ N := fun n hn => hφN (ψ n) (hψN n hn)
  have hψ2pow : (ψ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul]
    rw [show 2 * 3 = 3 * 2 by norm_num, pow_mul, hψ]
    simp
  have hφψ2 : (φ * ψ ^ 2) ^ 3 = 1 := by
    rw [(hφψ.pow_right 2).mul_pow, hφ, hψ2pow, mul_one]
  have hφψ2N : ∀ n ∈ N, (φ * ψ ^ 2) n ∈ N := by
    intro n hn
    simpa [MulAut.mul_apply, pow_two] using hφN (ψ (ψ n)) (hψN (ψ n) (hψN n hn))
  constructor
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      intro hq
      have hq' : quotientMap (φ * ψ) N hφψN (QuotientGroup.mk x) = QuotientGroup.mk x := by
        rw [quotientMap_mk]
        rw [quotientAut_mk, quotientAut_mk] at hq
        simpa [MulAut.mul_apply] using hq
      obtain ⟨y, hy, hφψy⟩ :=
        (fixed_quotient_iff (φ * ψ) hφψ3 N hφψN hnot3 (QuotientGroup.mk x)).mp hq'
      have hφy : φ y = y := h₁ y hφψy
      have hqφ : quotientMap φ N hφN (QuotientGroup.mk x) = QuotientGroup.mk x :=
        (fixed_quotient_iff φ hφ N hφN hnot3 (QuotientGroup.mk x)).mpr ⟨y, hy, hφy⟩
      calc quotientAut N φ hφN (QuotientGroup.mk x)
          = quotientMap φ N hφN (QuotientGroup.mk x) := by
            rw [quotientAut_mk, quotientMap_mk]
        _ = QuotientGroup.mk x := hqφ
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      intro hq
      have hq' : quotientMap (φ * ψ ^ 2) N hφψ2N (QuotientGroup.mk x) = QuotientGroup.mk x := by
        rw [quotientMap_mk]
        rw [quotientAut_mk, quotientAut_mk, quotientAut_mk] at hq
        simpa [MulAut.mul_apply, pow_two] using hq
      obtain ⟨y, hy, hφψ2y⟩ :=
        (fixed_quotient_iff (φ * ψ ^ 2) hφψ2 N hφψ2N hnot3 (QuotientGroup.mk x)).mp hq'
      have hφy : φ y = y := h₂ y hφψ2y
      have hqφ : quotientMap φ N hφN (QuotientGroup.mk x) = QuotientGroup.mk x :=
        (fixed_quotient_iff φ hφ N hφN hnot3 (QuotientGroup.mk x)).mpr ⟨y, hy, hφy⟩
      calc quotientAut N φ hφN (QuotientGroup.mk x)
          = quotientMap φ N hφN (QuotientGroup.mk x) := by
            rw [quotientAut_mk, quotientMap_mk]
        _ = QuotientGroup.mk x := hqφ

private lemma pow_three_eq_one_of_psi_fixes {P : Type*} [Group P] {p : ℕ} [Fact p.Prime]
    (_hP : IsPGroup p P) (_hp : p ≠ 3) {ψ : MulAut P} (hψ : ψ ^ 3 = 1) {w e : P}
    (hψe : ψ e = e) (hψw : ψ w = w * e) : e ^ 3 = 1 := by
  have he2 : ψ (ψ w) = w * e ^ 2 := by
    rw [hψw, map_mul, hψe, hψw, pow_two]
    group
  have hψe2 : ψ (e ^ 2) = e ^ 2 := by rw [map_pow, hψe]
  have he4 : ψ (ψ (ψ w)) = w * e ^ 3 := by
    rw [he2, map_mul, hψe2, hψw]
    rw [show e ^ 3 = e ^ 2 * e by rw [pow_succ]]
    group
  have h3 : ψ (ψ (ψ w)) = w := apply_apply_apply_of_pow_three hψ w
  have h : w * e ^ 3 = w := he4.symm.trans h3
  have h' : w * e ^ 3 = w * 1 := by
    rw [mul_one]
    exact h
  exact mul_left_cancel h'

private lemma pow_three_eq_one_of_phi_fixes {P : Type*} [Group P] {φ ψ : MulAut P}
    (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ) {x e : P}
    (heZ : e ∈ Subgroup.center P) (hφe : φ e = e)
    (hψw : ψ (x⁻¹ * φ x) = (x⁻¹ * φ x) * e) : e ^ 3 = 1 := by
  let wfun : P → P := fun y => y⁻¹ * φ y
  have hψwx : ψ (wfun x) = wfun x * e := by simpa [wfun] using hψw
  have hwφ : ∀ y : P, wfun (φ y) = φ (wfun y) := by
    intro y
    simp [wfun, map_mul]
  have hcomm : ∀ y : P, ψ (φ y) = φ (ψ y) := fun y =>
    (map_apply_map_of_commute hφψ y).symm
  have hψwφ : ψ (wfun (φ x)) = wfun (φ x) * e := by
    calc ψ (wfun (φ x)) = ψ (φ (wfun x)) := by rw [hwφ]
      _ = φ (ψ (wfun x)) := hcomm (wfun x)
      _ = φ (wfun x * e) := by rw [hψwx]
      _ = φ (wfun x) * φ e := by rw [map_mul]
      _ = wfun (φ x) * e := by rw [← hwφ, hφe]
  have hψwφ2 : ψ (wfun (φ (φ x))) = wfun (φ (φ x)) * e := by
    calc ψ (wfun (φ (φ x))) = ψ (φ (wfun (φ x))) := by rw [hwφ]
      _ = φ (ψ (wfun (φ x))) := hcomm (wfun (φ x))
      _ = φ (wfun (φ x) * e) := by rw [hψwφ]
      _ = φ (wfun (φ x)) * φ e := by rw [map_mul]
      _ = wfun (φ (φ x)) * e := by rw [← hwφ, hφe]
  have htelescope : wfun x * wfun (φ x) * wfun (φ (φ x)) = 1 := by
    dsimp [wfun]
    rw [apply_apply_apply_of_pow_three hφ x]
    group
  have he_central : ∀ y : P, y * e = e * y := fun y =>
    (Subgroup.mem_center_iff.mp heZ) y
  have hmul_central : ∀ a b c : P,
      (a * e) * (b * e) * (c * e) = (a * b * c) * e ^ 3 := by
    intro a b c
    calc (a * e) * (b * e) * (c * e)
        = a * (e * b) * e * (c * e) := by group
      _ = a * (b * e) * e * (c * e) := by rw [← he_central b]
      _ = a * b * (e * e) * (c * e) := by group
      _ = a * b * ((e * e) * c) * e := by group
      _ = a * b * (c * (e * e)) * e := by
            rw [show (e * e) * c = c * (e * e) from by
              calc (e * e) * c = e * (e * c) := by group
                _ = e * (c * e) := by rw [← he_central c]
                _ = (e * c) * e := by group
                _ = (c * e) * e := by rw [← he_central c]
                _ = c * (e * e) := by group]
      _ = a * b * c * (e * e * e) := by group
      _ = (a * b * c) * e ^ 3 := by rw [pow_three]; group
  have hmain : ψ (wfun x * wfun (φ x) * wfun (φ (φ x))) =
      (wfun x * wfun (φ x) * wfun (φ (φ x))) * e ^ 3 := by
    rw [map_mul, map_mul, hψwx, hψwφ, hψwφ2]
    exact hmul_central _ _ _
  have hprodψ : ψ (wfun x * wfun (φ x) * wfun (φ (φ x))) = 1 := by
    rw [htelescope, map_one]
  have h : (wfun x * wfun (φ x) * wfun (φ (φ x))) * e ^ 3 = 1 :=
    hmain.symm.trans hprodψ
  rwa [htelescope, one_mul] at h

private theorem apply_inv_mul_apply_aux (n : ℕ) :
    ∀ (P : Type*) [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
      (hP : IsPGroup p P) (hp : p ≠ 3) {φ ψ : MulAut P}
      (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hφψ : Commute φ ψ)
      (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
      (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x)
      (_ : Nat.card P = n) (x : P),
      ψ (x⁻¹ * φ x) = x⁻¹ * φ x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P _ _ p _ hP hp φ ψ hφ hψ hφψ h₁ h₂ hcard x
    classical
    by_cases hPnt : Nontrivial P
    · haveI : Nontrivial P := hPnt
      obtain ⟨N, hNne, hNleZ, hNfix, hφN, hψN⟩ :=
        exists_central_fixed_subgroup hP hp hPnt hφ hψ hφψ h₁ h₂
      haveI hNnormal : N.Normal := Subgroup.normal_of_le_center hNleZ
      have hnot3 : ¬ 3 ∣ Nat.card N := by
        intro h3
        obtain ⟨k, hk⟩ := (hP.to_subgroup N).exists_card_eq
        rw [hk] at h3
        have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h3
        have hp3 : p = 3 :=
          (Nat.Prime.dvd_iff_eq (Fact.out : Nat.Prime p) (by norm_num : 3 ≠ 1)).mp h3p
        exact hp hp3
      have hNφmap : Subgroup.map (φ : P →* P) N = N :=
        map_eq_self_of_forall_mem N φ hφN
      have hNψmap : Subgroup.map (ψ : P →* P) N = N :=
        map_eq_self_of_forall_mem N ψ hψN
      let Q := P ⧸ N
      let φbar : MulAut Q := quotientAut N φ hφN
      let ψbar : MulAut Q := quotientAut N ψ hψN
      have hφbar3 : φbar ^ 3 = 1 := quotientAut_pow_three N hφ hφN
      have hψbar3 : ψbar ^ 3 = 1 := quotientAut_pow_three N hψ hψN
      have hφψbar : Commute φbar ψbar := quotientAut_commute N hφN hψN hφψ
      have hfixed := quotientAut_fixed hφ hψ hφψ hφN hψN hnot3 h₁ h₂
      have hcardQ : Nat.card Q < n := by
        rw [← hcard]
        exact CFSG.card_quotient_lt_of_ne_bot N hNne
      have hIH := ih (Nat.card Q) hcardQ Q (p := p) (φ := φbar) (ψ := ψbar)
        (hP.to_quotient N) hp hφbar3 hψbar3 hφψbar hfixed.1 hfixed.2 rfl
      have hφbar_apply : ∀ y : P,
          φbar (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y =>
        quotientAut_mk N φ hφN y
      have hψbar_apply : ∀ y : P,
          ψbar (QuotientGroup.mk y) = QuotientGroup.mk (ψ y) := fun y =>
        quotientAut_mk N ψ hψN y
      have hquot : ∀ y : P, (ψ (y⁻¹ * φ y) : Q) = (y⁻¹ * φ y : Q) := by
        intro y
        have h := hIH (QuotientGroup.mk y)
        have harg : (QuotientGroup.mk y)⁻¹ * φbar (QuotientGroup.mk y) =
            QuotientGroup.mk (y⁻¹ * φ y) := by
          rw [hφbar_apply]
          simp
        rw [harg, hψbar_apply (y⁻¹ * φ y)] at h
        exact h
      let w : P := x⁻¹ * φ x
      let e : P := w⁻¹ * ψ w
      have he_mem : e ∈ N := by
        have h := hquot x
        exact (QuotientGroup.eq (s := N) (a := w) (b := ψ w)).mp h.symm
      have hψw : ψ w = w * e := by
        dsimp [e]
        group
      have he3 : e ^ 3 = 1 := by
        rcases hNfix with hφfixN | hψfixN
        · exact pow_three_eq_one_of_phi_fixes hφ hψ hφψ (hNleZ he_mem)
            (hφfixN e he_mem) (by simpa [w] using hψw)
        · exact pow_three_eq_one_of_psi_fixes hP hp hψ (hψfixN e he_mem) hψw
      have he1 : e = 1 := eq_one_of_pow_three_eq_one hP hp he3
      have hψw' : ψ w = w := by
        rw [hψw, he1, mul_one]
      simpa [w] using hψw'
    · haveI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hPnt
      exact Subsingleton.elim _ _

theorem apply_inv_mul_apply {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp : p ≠ 3) {φ ψ : MulAut P} (hφ : φ ^ 3 = 1) (hψ : ψ ^ 3 = 1)
    (hφψ : Commute φ ψ) (h₁ : ∀ x, φ (ψ x) = x → φ x = x)
    (h₂ : ∀ x, φ (ψ (ψ x)) = x → φ x = x) (x : P) :
    ψ (x⁻¹ * φ x) = x⁻¹ * φ x :=
  apply_inv_mul_apply_aux (Nat.card P) P hP hp hφ hψ hφψ h₁ h₂ rfl x

private lemma conj_eq_self_of_mem_centralizer {G : Type*} [Group G] {P : Subgroup G}
    {a c : G} (h : P ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer {c})
    {y : P} (hy : a * (y : G) * a⁻¹ = (y : G)) :
    c * (y : G) * c⁻¹ = (y : G) := by
  have hycent : (y : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : G) * a = (a * (y : G) * a⁻¹) * a := by rw [hy]
      _ = a * (y : G) := by group
  have hmem : (y : G) ∈ P ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_inf.mpr ⟨y.2, hycent⟩
  have hc_comm : (y : G) * c = c * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (h hmem)
  calc c * (y : G) * c⁻¹ = (y : G) * c * c⁻¹ := by rw [← hc_comm]
    _ = (y : G) := by group

private lemma commute_d_commutator_c {G : Type*} [Group G] {P : Subgroup G} {c d : G}
    {φ ψ : MulAut P}
    (hφcoe : ∀ y : P, ((φ y : P) : G) = c * (y : G) * c⁻¹)
    (hψcoe : ∀ y : P, ((ψ y : P) : G) = d * (y : G) * d⁻¹)
    (happly : ∀ y : P, ψ (y⁻¹ * φ y) = y⁻¹ * φ y) :
    ∀ y ∈ P, Commute d ⁅y, c⁆ := by
  intro y hy
  let y' : P := ⟨y⁻¹, P.inv_mem hy⟩
  have hfix := happly y'
  have hd_fix : d * (((y'⁻¹ * φ y' : P) : G)) * d⁻¹ =
      (((y'⁻¹ * φ y' : P) : G)) := by
    have h := congrArg Subtype.val hfix
    rw [hψcoe] at h
    exact h
  have hcomm : Commute d (((y'⁻¹ * φ y' : P) : G)) := by
    show d * (((y'⁻¹ * φ y' : P) : G)) = (((y'⁻¹ * φ y' : P) : G)) * d
    calc d * (((y'⁻¹ * φ y' : P) : G))
        = (d * (((y'⁻¹ * φ y' : P) : G)) * d⁻¹) * d := by group
      _ = (((y'⁻¹ * φ y' : P) : G)) * d := by rw [hd_fix]
  have hval : (((y'⁻¹ * φ y' : P) : G)) = ⁅y, c⁆ := by
    dsimp [y']
    rw [hφcoe]
    rw [commutatorElement_def]
    group
  rwa [hval] at hcomm

private lemma commute_d_commutator_c_sq {G : Type*} [Group G] {P : Subgroup G} {c d : G}
    (hcd : Commute c d) (hcomm_c : ∀ y ∈ P, Commute d ⁅y, c⁆) :
    ∀ y ∈ P, Commute d ⁅y, c ^ 2⁆ := by
  intro y hy
  have hu : Commute d ⁅y, c⁆ := hcomm_c y hy
  have hdc : Commute d c := hcd.symm
  have hcu : Commute d (c * ⁅y, c⁆ * c⁻¹) :=
    (hdc.mul_right hu).mul_right hdc.inv_right
  have hdecomp : ⁅y, c ^ 2⁆ = ⁅y, c⁆ * (c * ⁅y, c⁆ * c⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def, pow_two]
    group
  rw [hdecomp]
  exact hu.mul_right hcu

private lemma commute_d_commutator_zpowers {G : Type*} [Group G] {P : Subgroup G} {c d : G}
    (hc : c ^ 3 = 1) (hcomm_c : ∀ y ∈ P, Commute d ⁅y, c⁆)
    (hcomm_c2 : ∀ y ∈ P, Commute d ⁅y, c ^ 2⁆) :
    ∀ y ∈ P, ∀ z ∈ Subgroup.zpowers c, Commute d ⁅y, z⁆ := by
  intro y hy z hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk3 := zpow_eq_zpow_emod' (x := c) k (n := 3) (by simpa using hc)
  have hk0 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
  have hklt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hkz : c ^ (k % 3) = z := hk3.symm.trans hk
  rcases hcases with h | h | h
  · have hz1 : z = 1 := by
      rw [h] at hkz
      simpa using hkz.symm
    rw [hz1]
    simpa using Commute.one_right d
  · have hzc : z = c := by
      rw [h] at hkz
      simpa using hkz.symm
    rw [hzc]
    exact hcomm_c y hy
  · have hzc2 : z = c ^ 2 := by
      rw [h] at hkz
      simpa using hkz.symm
    rw [hzc2]
    exact hcomm_c2 y hy

theorem commutator_zpowers_le_centralizer {G : Type*} [Group G] {P : Subgroup G} [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hp : p ≠ 3) {c d : G} (hc : c ^ 3 = 1)
    (hd : d ^ 3 = 1) (hcd : Commute c d) (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hdP : d ∈ Subgroup.normalizer (P : Set G))
    (h₁ : P ⊓ Subgroup.centralizer {c * d} ≤ Subgroup.centralizer {c})
    (h₂ : P ⊓ Subgroup.centralizer {c * d ^ 2} ≤ Subgroup.centralizer {c}) :
    ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer {d} := by
  classical
  let φ : MulAut P := CFSG.GroupTheory.WielandtProduct.normalizerConj P ⟨c, hcP⟩
  let ψ : MulAut P := CFSG.GroupTheory.WielandtProduct.normalizerConj P ⟨d, hdP⟩
  have hc' : (⟨c, hcP⟩ : Subgroup.normalizer (P : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hc
  have hd' : (⟨d, hdP⟩ : Subgroup.normalizer (P : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hd
  have hφ : φ ^ 3 = 1 := by
    dsimp [φ]
    rw [← map_pow, hc', map_one]
  have hψ : ψ ^ 3 = 1 := by
    dsimp [ψ]
    rw [← map_pow, hd', map_one]
  have hφψ : Commute φ ψ := by
    show φ * ψ = ψ * φ
    dsimp [φ, ψ]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcd.eq
  have hφcoe : ∀ y : P, ((φ y : P) : G) = c * (y : G) * c⁻¹ := by
    intro y
    simpa [φ] using CFSG.GroupTheory.WielandtProduct.coe_normalizerConj_apply P ⟨c, hcP⟩ y
  have hψcoe : ∀ y : P, ((ψ y : P) : G) = d * (y : G) * d⁻¹ := by
    intro y
    simpa [ψ] using CFSG.GroupTheory.WielandtProduct.coe_normalizerConj_apply P ⟨d, hdP⟩ y
  have h₁' : ∀ y : P, φ (ψ y) = y → φ y = y := by
    intro y hy
    have hconj : (c * d) * (y : G) * (c * d)⁻¹ = (y : G) := by
      have h := congrArg Subtype.val hy
      rw [hφcoe, hψcoe] at h
      calc (c * d) * (y : G) * (c * d)⁻¹
          = c * (d * (y : G) * d⁻¹) * c⁻¹ := by group
        _ = (y : G) := h
    have hcy : c * (y : G) * c⁻¹ = (y : G) :=
      conj_eq_self_of_mem_centralizer h₁ hconj
    apply Subtype.ext
    rw [hφcoe]
    exact hcy
  have h₂' : ∀ y : P, φ (ψ (ψ y)) = y → φ y = y := by
    intro y hy
    have hψ2 : ((ψ (ψ y) : P) : G) = d ^ 2 * (y : G) * (d ^ 2)⁻¹ := by
      rw [hψcoe, hψcoe]
      rw [show d * (d * (y : G) * d⁻¹) * d⁻¹ = d ^ 2 * (y : G) * (d ^ 2)⁻¹ by
        rw [pow_two]; group]
    have hconj : (c * d ^ 2) * (y : G) * (c * d ^ 2)⁻¹ = (y : G) := by
      have h := congrArg Subtype.val hy
      rw [hφcoe, hψ2] at h
      calc (c * d ^ 2) * (y : G) * (c * d ^ 2)⁻¹
          = c * (d ^ 2 * (y : G) * (d ^ 2)⁻¹) * c⁻¹ := by group
        _ = (y : G) := h
    have hcy : c * (y : G) * c⁻¹ = (y : G) :=
      conj_eq_self_of_mem_centralizer h₂ hconj
    apply Subtype.ext
    rw [hφcoe]
    exact hcy
  have happly : ∀ y : P, ψ (y⁻¹ * φ y) = y⁻¹ * φ y :=
    fun y => apply_inv_mul_apply hP hp hφ hψ hφψ h₁' h₂' y
  have hcomm_c := commute_d_commutator_c hφcoe hψcoe happly
  have hcomm_c2 := commute_d_commutator_c_sq hcd hcomm_c
  have hcommutator := commute_d_commutator_zpowers hc hcomm_c hcomm_c2
  refine Subgroup.commutator_le.mpr ?_
  intro y hy z hz
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommutator y hy z hz).symm.eq

end CFSG.GroupTheory.CoprimeActionSupport.OrderThreePairCommutator

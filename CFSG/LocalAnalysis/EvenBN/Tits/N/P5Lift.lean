module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Lift

open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.EvenBN.Tits.N CFSG.LocalAnalysis.EvenBN.Tits.N.P5

theorem exists_mul_normalizer_of_normalizer_map {M Q : Type*} [Group M] [Finite M] [Group Q]
    (π : M →* Q) (hker : Odd (Nat.card π.ker)) {A : Subgroup M} (hA : IsPGroup 2 A) {m : M}
    (hm : π m ∈ normalizer ((A.map π : Subgroup Q) : Set Q)) :
    ∃ k ∈ A, ∃ n ∈ normalizer (A : Set M), π m = π k * π n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup M := (A.map π).comap π with hH
  have hAH : A ≤ H := fun a ha => ⟨a, ha, rfl⟩
  have hHeq : H = π.ker ⊔ A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, hax⟩ := hx
      have hk : x * a⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel]
      have h2 : x = (x * a⁻¹) * a := by group
      rw [h2]
      exact Subgroup.mul_mem_sup hk ha
    · refine sup_le (fun k hk => ⟨1, A.one_mem, ?_⟩) hAH
      rw [map_one, MonoidHom.mem_ker.1 hk]
  have hrel : A.relIndex H = A.relIndex π.ker := by
    rw [hHeq]
    exact relIndex_sup_eq_relIndex_of_normal π.ker A
  have hodd : Odd (A.relIndex H) := by
    rw [hrel]
    exact hker.of_dvd_nat (Dvd.intro _ (Subgroup.relIndex_mul_card A π.ker))
  have hSylA : IsSylowOf 2 A H := by
    rw [isSylowOf_iff]
    refine ⟨hAH, hA, fun h => ?_⟩
    obtain ⟨c, hc⟩ := h
    obtain ⟨d, hd⟩ := hodd
    omega
  set A₁ : Subgroup M := A.map (MulAut.conj m).toMonoidHom with hA₁
  have hA₁mem : ∀ x, x ∈ A₁ ↔ m⁻¹ * x * m ∈ A := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hx
      refine ⟨m⁻¹ * x * m, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hA₁H : A₁ ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : π a ∈ A.map π := ⟨a, ha, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 hm (π a)).1 h1
    show π ((MulAut.conj m).toMonoidHom a) ∈ A.map π
    simpa [MulAut.conj_apply] using h2
  have hSyl₁ : IsSylowOf 2 A₁ H := by
    refine isSylowOf_of_card hA₁H ?_
    rw [← hSylA.card_eq, hA₁, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  obtain ⟨k, hkH, hk⟩ := IsSylowOf.exists_mem_conj hSylA hSyl₁
  have hnorm : k⁻¹ * m ∈ normalizer (A : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : x ∈ A ↔ m * x * m⁻¹ ∈ A₁ := by
      rw [hA₁mem]
      have : m⁻¹ * (m * x * m⁻¹) * m = x := by group
      rw [this]
    rw [h1, hk]
    have : k⁻¹ * (m * x * m⁻¹) * k = (k⁻¹ * m) * x * (k⁻¹ * m)⁻¹ := by group
    rw [this]
  obtain ⟨a, ha, hak⟩ := hkH
  refine ⟨a, ha, k⁻¹ * m, hnorm, ?_⟩
  rw [hak, ← map_mul]
  congr 1
  group

theorem exists_fixed_of_involutive {α : Type*} [Finite α] {f : α → α} (hf : ∀ a, f (f a) = a)
    (hα : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  haveI := Fintype.ofFinite α
  have hinv : Function.Involutive f := hf
  have hσ : (hinv.toPerm f) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun x => hinv x
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    intro h
    obtain ⟨c, hc⟩ := h
    obtain ⟨d, hd⟩ := hα
    omega
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
  exact ⟨a, by simpa using ha⟩

theorem isSolvable_fixSub_of_odd_kernel {M Q : Type*} [Group M] [Finite M] [Group Q]
    (π : M →* Q) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker))
    {τ : MulAut M} {ψ : MulAut Q} (hτ : τ ^ 2 = 1) (hcompat : ∀ m, π (τ m) = ψ (π m))
    (hs : Group.IsSolvable ↥(fixSub τ)) : Group.IsSolvable ↥(fixSub ψ) := by
  have hττ : ∀ m, τ (τ m) = m := fun m => by
    have := congrArg (fun e : MulAut M => e m) hτ
    simpa [pow_two] using this
  have hfix : ∀ x : fixSub τ, π (x : M) ∈ fixSub ψ := by
    intro x
    show ψ (π x) = π x
    rw [← hcompat, mem_fixSub.1 x.2]
  let g : fixSub τ →* fixSub ψ := (π.comp (fixSub τ).subtype).codRestrict (fixSub ψ) hfix
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨m₀, rfl⟩ := hπ q
    have hq' : ψ (π m₀) = π m₀ := hq
    let f : π.ker → π.ker := fun k => ⟨m₀⁻¹ * τ (m₀ * k), by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcompat, map_mul, MonoidHom.mem_ker.1 k.2, mul_one,
        hq', inv_mul_cancel]⟩
    have hf : ∀ k, f (f k) = k := by
      intro k
      apply Subtype.ext
      show m₀⁻¹ * τ (m₀ * (m₀⁻¹ * τ (m₀ * (k : M)))) = k
      rw [mul_inv_cancel_left, hττ, inv_mul_cancel_left]
    obtain ⟨k, hk⟩ := exists_fixed_of_involutive hf hker
    have hk' : m₀⁻¹ * τ (m₀ * (k : M)) = k := congrArg Subtype.val hk
    have hτm : τ (m₀ * (k : M)) = m₀ * k := by
      have := congrArg (fun y => m₀ * y) hk'
      simpa [mul_inv_cancel_left] using this
    refine ⟨⟨m₀ * k, mem_fixSub.2 hτm⟩, Subtype.ext ?_⟩
    show π (m₀ * (k : M)) = π m₀
    rw [map_mul, MonoidHom.mem_ker.1 k.2, mul_one]
  haveI := hs
  exact solvable_of_surjective hg

theorem card_sub_one_dvd_card_imgIn {Γ : Type*} [Group Γ] [Finite Γ] (A : Subgroup Γ) (hA : A ≠ ⊥)
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer (A : Set Γ), n⁻¹ * a * n = b) :
    (Nat.card A - 1) ∣ Nat.card (imgIn A (normalizer (A : Set Γ))) := by
  classical
  set I := imgIn A (normalizer (A : Set Γ)) with hI
  obtain ⟨a₀, ha₀⟩ : ∃ a : ↥A, a ≠ 1 := by
    by_contra h
    push Not at h
    apply hA
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (h ⟨x, hx⟩))
  haveI : Fintype ↥I := Fintype.ofFinite _
  haveI : Fintype ↥A := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbit ↥I a₀) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥I a₀) := Fintype.ofFinite _
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥I a₀
  have horb : MulAction.orbit ↥I a₀ = {a | a ≠ 1} := by
    ext b
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨σ, rfl⟩ h1
      have : (σ : MulAut ↥A) a₀ = 1 := h1
      exact ha₀ (by simpa using this)
    · intro hb
      have hb' : (b : Γ) ≠ 1 := fun h => hb (Subtype.ext h)
      have ha₀' : (a₀ : Γ) ≠ 1 := fun h => ha₀ (Subtype.ext h)
      obtain ⟨n, hn, hnab⟩ := htrans a₀ a₀.2 b b.2 ha₀' hb'
      have hn' : n⁻¹ ∈ normalizer (A : Set Γ) := Subgroup.inv_mem _ hn
      refine ⟨⟨actFun A n⁻¹, actFun_mem_imgIn hn' hn'⟩, ?_⟩
      show actFun A n⁻¹ a₀ = b
      apply Subtype.ext
      rw [actFun_apply_coe A hn', inv_inv]
      exact hnab
  have hcard : Nat.card (MulAction.orbit ↥I a₀) = Nat.card A - 1 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun a : ↥A => a ≠ 1)
      (fun x => by rw [horb]; rfl)), Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card] at key
  rw [hcard] at key
  exact Dvd.intro _ key

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Lift

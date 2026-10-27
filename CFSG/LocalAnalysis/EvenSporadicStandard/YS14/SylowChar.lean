module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.SylowTrick
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.LargeInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second

public section

namespace CFSG.EvenSporadicStandard.YS14

open scoped Pointwise

theorem mulAut_apply_apply_of_mul_eq_one {K : Type*} [Group K] {α : MulAut K}
    (hαα : α * α = 1) (a : K) : α (α a) = a := by
  have h := congrArg (fun f : MulAut K => f a) hαα
  simpa using h

theorem mulEquiv_isLargeInv_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    IsLargeInv a ↔ IsLargeInv (e a) := by
  have hsq : a * a = 1 ↔ e a * e a = 1 := by
    rw [← map_mul, e.map_eq_one_iff]
  have hne : a ≠ 1 ↔ e a ≠ 1 := by
    rw [Ne, Ne, e.map_eq_one_iff]
  have hc : Nat.card ↥(Subgroup.centralizer ({a} : Set A)) =
      Nat.card ↥(Subgroup.centralizer ({e a} : Set B)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun x => ?_)
    show x ∈ Subgroup.centralizer ({a} : Set A) ↔ e x ∈ Subgroup.centralizer ({e a} : Set B)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg e h
      rwa [map_mul, map_mul] at h'
    · intro h
      apply e.injective
      rw [map_mul, map_mul]
      exact h
  unfold IsLargeInv
  rw [hsq, hne, hc]

@[expose] def invAutRestrict {K : Type*} [Group K] {α : MulAut K} (hαα : α * α = 1)
    (S : Subgroup K) (hS : ∀ x ∈ S, α x ∈ S) : S ≃* S where
  toFun s := ⟨α (s : K), hS (s : K) s.2⟩
  invFun s := ⟨α (s : K), hS (s : K) s.2⟩
  left_inv s := Subtype.ext (mulAut_apply_apply_of_mul_eq_one hαα (s : K))
  right_inv s := Subtype.ext (mulAut_apply_apply_of_mul_eq_one hαα (s : K))
  map_mul' s t := Subtype.ext (map_mul α (s : K) (t : K))

@[expose] def largeInvSet {K : Type*} [Group K] (S : Subgroup K) : Set K :=
  {x | ∃ s : S, IsLargeInv s ∧ (s : K) = x}

theorem mem_largeInvSet {K : Type*} [Group K] {S : Subgroup K} {x : K} :
    x ∈ largeInvSet S ↔ ∃ s : S, IsLargeInv s ∧ (s : K) = x := Iff.rfl

theorem closure_exp_two_comm {K : Type*} [Group K] (G : Set K) (hG2 : ∀ x ∈ G, x * x = 1)
    (hGc : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) :
    (∀ a ∈ Subgroup.closure G, a * a = 1) ∧
      (∀ a ∈ Subgroup.closure G, ∀ b ∈ Subgroup.closure G, a * b = b * a) := by
  have hcent : Subgroup.closure G ≤ Subgroup.centralizer G :=
    (Subgroup.closure_le _).2 fun g hg => Subgroup.mem_centralizer_iff.2 fun h hh => hGc h hh g hg
  have hcomm : ∀ a ∈ Subgroup.closure G, ∀ b ∈ Subgroup.closure G, a * b = b * a := by
    intro a ha b hb
    have hb' : Subgroup.closure G ≤ Subgroup.centralizer ({b} : Set K) :=
      (Subgroup.closure_le _).2 fun g hg =>
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hcent hb) g hg)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hb' ha)
  refine ⟨?_, hcomm⟩
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hG2 x hx
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy]
      _ = x * x * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx =>
    rw [inv_eq_of_mul_eq_one_right ihx]
    exact ihx

theorem exists_sylow_two_fixed {K : Type*} [Group K] [Finite K] (α : MulAut K)
    (hαα : α * α = 1) : ∃ S : Sylow 2 K, α • S = S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_subgroup_of_finite K
  haveI : Finite (Sylow 2 K) :=
    Finite.of_injective (fun S : Sylow 2 K => (S : Subgroup K)) (fun _ _ h => Sylow.ext h)
  have hmod : Nat.card (Sylow 2 K) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 K
  have hodd : Odd (Nat.card (Sylow 2 K)) := by
    rw [Nat.odd_iff]
    simpa [Nat.ModEq] using hmod
  have hα4 : α ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hαα, one_mul]
  have hσ : (MulAction.toPerm α : Equiv.Perm (Sylow 2 K)) ^ 4 = 1 := by
    have h : (MulAction.toPerm α : Equiv.Perm (Sylow 2 K)) =
        MulAction.toPermHom (MulAut K) (Sylow 2 K) α := rfl
    rw [h, ← map_pow, hα4, map_one]
  obtain ⟨S, hS⟩ := exists_fixed_of_pow_four_eq_one (MulAction.toPerm α) hσ hodd
  exact ⟨S, hS⟩

theorem involutionFixesElem_of_sylow_large_invs {K : Type*} [Group K] [Finite K] {T : Type*}
    [Group T]
    (hiso : ∀ S : Sylow 2 K, Nonempty (↥(S : Subgroup K) ≃* T))
    (hcomm : ∀ x y : T, IsLargeInv x → IsLargeInv y → x * y = y * x)
    (V : Finset T) (hV : 128 ≤ V.card)
    (hVX : ∀ v ∈ V, v ∈ Subgroup.closure {x : T | IsLargeInv x}) :
    CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem K 16 := by
  classical
  intro α _ hαα
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSα⟩ := exists_sylow_two_fixed α hαα
  obtain ⟨φ⟩ := hiso S
  have hSsub : α • (S : Subgroup K) = (S : Subgroup K) := by
    rw [← Sylow.pointwise_smul_def, hSα]
  have hαS : ∀ x ∈ (S : Subgroup K), α x ∈ (S : Subgroup K) := by
    intro x hx
    have h := Subgroup.smul_mem_pointwise_smul x α (S : Subgroup K) hx
    rw [hSsub, MulAut.smul_def] at h
    exact h
  have hG2 : ∀ x ∈ largeInvSet (S : Subgroup K), x * x = 1 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_largeInvSet.1 hx
    exact congrArg Subtype.val hs.1
  have hGc : ∀ x ∈ largeInvSet (S : Subgroup K), ∀ y ∈ largeInvSet (S : Subgroup K),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := mem_largeInvSet.1 hx
    obtain ⟨t, ht, rfl⟩ := mem_largeInvSet.1 hy
    have h1 := hcomm (φ s) (φ t) ((mulEquiv_isLargeInv_iff φ s).1 hs)
      ((mulEquiv_isLargeInv_iff φ t).1 ht)
    have h2 : s * t = t * s := by
      apply φ.injective
      rw [map_mul, map_mul]
      exact h1
    exact congrArg Subtype.val h2
  obtain ⟨hE2, hEc⟩ := closure_exp_two_comm (largeInvSet (S : Subgroup K)) hG2 hGc
  have hGα : ∀ x ∈ largeInvSet (S : Subgroup K), α x ∈ largeInvSet (S : Subgroup K) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_largeInvSet.1 hx
    exact mem_largeInvSet.2 ⟨invAutRestrict hαα (S : Subgroup K) hαS s,
      (mulEquiv_isLargeInv_iff (invAutRestrict hαα (S : Subgroup K) hαS) s).1 hs, rfl⟩
  have hEα : ∀ a ∈ Subgroup.closure (largeInvSet (S : Subgroup K)),
      α a ∈ Subgroup.closure (largeInvSet (S : Subgroup K)) := by
    intro a ha
    have hle : Subgroup.closure (largeInvSet (S : Subgroup K)) ≤
        (Subgroup.closure (largeInvSet (S : Subgroup K))).comap α.toMonoidHom := by
      apply (Subgroup.closure_le _).2
      intro g hg
      exact Subgroup.subset_closure (hGα g hg)
    exact hle ha
  have hαE : α • Subgroup.closure (largeInvSet (S : Subgroup K)) =
      Subgroup.closure (largeInvSet (S : Subgroup K)) := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulAut.smul_def]
      exact hEα y hy
    · intro hx
      exact ⟨α x, hEα x hx, by rw [MulAut.smul_def, mulAut_apply_apply_of_mul_eq_one hαα]⟩
  have hψ : ∀ v ∈ Subgroup.closure {x : T | IsLargeInv x},
      ((φ.symm v : ↥(S : Subgroup K)) : K) ∈ Subgroup.closure (largeInvSet (S : Subgroup K)) := by
    intro v hv
    have hle : (Subgroup.closure {x : T | IsLargeInv x}).map
        ((S : Subgroup K).subtype.comp φ.symm.toMonoidHom) ≤
        Subgroup.closure (largeInvSet (S : Subgroup K)) := by
      rw [MonoidHom.map_closure]
      apply (Subgroup.closure_le _).2
      rintro _ ⟨u, hu, rfl⟩
      have hmem : ((φ.symm u : ↥(S : Subgroup K)) : K) ∈ largeInvSet (S : Subgroup K) :=
        mem_largeInvSet.2 ⟨φ.symm u, (mulEquiv_isLargeInv_iff φ.symm u).1 hu, rfl⟩
      exact Subgroup.subset_closure hmem
    exact hle (Subgroup.mem_map_of_mem _ hv)
  have hcardV : V.card ≤ Nat.card ↥(Subgroup.closure (largeInvSet (S : Subgroup K))) := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_le_card_of_injective (fun v : V =>
      (⟨((φ.symm (v : T) : ↥(S : Subgroup K)) : K), hψ (v : T) (hVX _ v.2)⟩ :
        ↥(Subgroup.closure (largeInvSet (S : Subgroup K)))))
    intro v w h
    apply Subtype.ext
    apply φ.symm.injective
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  obtain ⟨C, hCα, hC2, hCc, hle⟩ :=
    card_fixedSubgroup_ge α hαα (Subgroup.closure (largeInvSet (S : Subgroup K))) hE2 hEc hαE
  have hCp : IsPGroup 2 ↥C := by
    rw [IsPGroup.iff_orderOf]
    intro g
    by_cases hg : g = 1
    · exact ⟨0, by simp [hg]⟩
    · refine ⟨1, ?_⟩
      have h2 : g ^ 2 = 1 := by
        rw [pow_two]
        exact Subtype.ext (hC2 g.1 g.2)
      rw [orderOf_eq_prime h2 hg]
      norm_num
  obtain ⟨n, hn⟩ := hCp.exists_card_eq
  rw [hn] at hle
  have h128 : 128 ≤ 2 ^ n * 2 ^ n := le_trans (le_trans hV hcardV) hle
  refine ⟨C, hCα, hC2, hCc, ?_⟩
  rw [hn]
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n <;> norm_num at h128
  · calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4

end CFSG.EvenSporadicStandard.YS14

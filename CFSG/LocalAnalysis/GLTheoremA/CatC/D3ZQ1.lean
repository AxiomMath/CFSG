module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL1
public import CFSG.LieType.Chevalley.A2Commutator

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three


section Node

variable {K : Type} [Field K] [Finite K]

theorem commute_adjX_outer {i j : Fin Tag.D4.rank} (hi : i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hj : j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hij : i ≠ j) (c d : K) :
    adjX Tag.D4 K i c * adjX Tag.D4 K j d = adjX Tag.D4 K j d * adjX Tag.D4 K i c := by
  refine Subtype.ext ?_
  have h := (commute_rho_outer hi hj hij (uSL c) (uSL d)).eq
  rw [simpleRootSL2_uSL, simpleRootSL2_uSL] at h
  exact h

theorem not_commute_adjX_two {m : Fin Tag.D4.rank} (hm : m ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    adjX Tag.D4 K 2 1 * adjX Tag.D4 K m 1 ≠ adjX Tag.D4 K m 1 * adjX Tag.D4 K 2 1 := by
  intro h
  have h' : Commute (xUnit Tag.D4 K 2 1) (xUnit Tag.D4 K m 1) := congrArg Subtype.val h
  have hij : Tag.D4.cartan 2 m = -1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  have hji : Tag.D4.cartan m 2 = -1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  have hc := (a2_simple_root_commutatorElement (τ := Tag.D4) K hij hji 1 1).1
  rw [commutatorElement_eq_one_iff_commute.2 h', eq_comm, conj_eq_one_iff] at hc
  have h0 : xUnit Tag.D4 K m (1 * 1) = xUnit Tag.D4 K m 0 := by rw [hc, xUnit_zero]
  have h1 : (1 : K) * 1 = 0 := xUnit_inj_d4 m h0
  have h2 : (1 : K) = 0 := by simpa using h1
  exact one_ne_zero h2

theorem simplePerm_two (β : unipotentPairAut Tag.D4 K) : simplePermHom Tag.D4 K β 2 = 2 := by
  by_contra hne
  have hspec : ∀ i, (simplePosSubgroup Tag.D4 K i).map
      (β : MulAut (adjointGroup Tag.D4 K)).toMonoidHom =
      simplePosSubgroup Tag.D4 K (simplePermHom Tag.D4 K β i) := fun i => (simplePerm_spec β i).1
  have contra : ∀ i j : Fin Tag.D4.rank, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) →
      j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) → i ≠ j → simplePermHom Tag.D4 K β i = 2 → False := by
    intro i j hi hj hij hπi
    have hπj : simplePermHom Tag.D4 K β j ≠ 2 := fun h =>
      hij ((simplePermHom Tag.D4 K β).injective (hπi.trans h.symm))
    have hmO : simplePermHom Tag.D4 K β j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
      have h4 : ∀ k : Fin Tag.D4.rank, k ≠ 2 → k = 0 ∨ k = 1 ∨ k = 3 := by decide
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h4 _ hπj
    have h2mem : adjX Tag.D4 K 2 1 ∈ simplePosSubgroup Tag.D4 K (simplePermHom Tag.D4 K β i) := by
      rw [hπi]; exact ⟨1, rfl⟩
    have hmmem : adjX Tag.D4 K (simplePermHom Tag.D4 K β j) 1 ∈
        simplePosSubgroup Tag.D4 K (simplePermHom Tag.D4 K β j) := ⟨1, rfl⟩
    rw [← hspec i] at h2mem
    rw [← hspec j] at hmmem
    obtain ⟨x, hx, hxβ⟩ := Subgroup.mem_map.1 h2mem
    obtain ⟨y, hy, hyβ⟩ := Subgroup.mem_map.1 hmmem
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    have hxe : x = adjX Tag.D4 K i c := Subtype.ext hc
    have hye : y = adjX Tag.D4 K j d := Subtype.ext hd
    have hcomm : x * y = y * x := by rw [hxe, hye]; exact commute_adjX_outer hi hj hij c d
    have h3 : (β : MulAut (adjointGroup Tag.D4 K)) x * (β : MulAut (adjointGroup Tag.D4 K)) y =
        (β : MulAut (adjointGroup Tag.D4 K)) y * (β : MulAut (adjointGroup Tag.D4 K)) x := by
      rw [← map_mul, ← map_mul, hcomm]
    exact not_commute_adjX_two hmO (by
      have e1 : (β : MulAut (adjointGroup Tag.D4 K)) x = adjX Tag.D4 K 2 1 := hxβ
      have e2 : (β : MulAut (adjointGroup Tag.D4 K)) y =
          adjX Tag.D4 K (simplePermHom Tag.D4 K β j) 1 := hyβ
      rwa [e1, e2] at h3)
  obtain ⟨i, hi⟩ := (simplePermHom Tag.D4 K β).surjective 2
  have hi2 : i ≠ 2 := fun h => hne (h ▸ hi)
  fin_cases i
  · exact contra 0 1 (by simp) (by simp) (by decide) hi
  · exact contra 1 0 (by simp) (by simp) (by decide) hi
  · exact hi2 rfl
  · exact contra 3 0 (by simp) (by simp) (by decide) hi

end Node

section PermRel

variable {K : Type} [Field K] [Finite K]

theorem perm_relation {g c c' : adjointGroup Tag.D4 K} {βt β β' : MulAut (adjointGroup Tag.D4 K)}
    (hβt : βt ∈ unipotentPairAut Tag.D4 K) (hβ : β ∈ unipotentPairAut Tag.D4 K)
    (hβ' : β' ∈ unipotentPairAut Tag.D4 K)
    (h : (MulAut.conj g * βt) * (MulAut.conj c * β) =
      (MulAut.conj c' * β') * (MulAut.conj g * βt)) :
    simplePermHom Tag.D4 K ⟨β', hβ'⟩ * simplePermHom Tag.D4 K ⟨βt, hβt⟩ =
      simplePermHom Tag.D4 K ⟨βt, hβt⟩ * simplePermHom Tag.D4 K ⟨β, hβ⟩ := by
  have e1 : (MulAut.conj g * βt) * (MulAut.conj c * β) = MulAut.conj (g * βt c) * (βt * β) := by
    calc (MulAut.conj g * βt) * (MulAut.conj c * β)
        = MulAut.conj g * (βt * MulAut.conj c) * β := by group
      _ = MulAut.conj g * (MulAut.conj (βt c) * βt) * β := by rw [mul_conj_eq]
      _ = MulAut.conj (g * βt c) * (βt * β) := by rw [map_mul]; group
  have e2 : (MulAut.conj c' * β') * (MulAut.conj g * βt) =
      MulAut.conj (c' * β' g) * (β' * βt) := by
    calc (MulAut.conj c' * β') * (MulAut.conj g * βt)
        = MulAut.conj c' * (β' * MulAut.conj g) * βt := by group
      _ = MulAut.conj c' * (MulAut.conj (β' g) * β') * βt := by rw [mul_conj_eq]
      _ = MulAut.conj (c' * β' g) * (β' * βt) := by rw [map_mul]; group
  obtain ⟨y, hy⟩ : ∃ y : adjointGroup Tag.D4 K, y = (g * βt c)⁻¹ * (c' * β' g) := ⟨_, rfl⟩
  have hyy : βt * β = MulAut.conj y * (β' * βt) := by
    have h' := h
    rw [e1, e2] at h'
    rw [hy, map_mul, map_inv]
    calc βt * β = (MulAut.conj (g * βt c))⁻¹ * (MulAut.conj (g * βt c) * (βt * β)) := by group
      _ = (MulAut.conj (g * βt c))⁻¹ * (MulAut.conj (c' * β' g) * (β' * βt)) := by rw [h']
      _ = _ := (mul_assoc _ _ _).symm
  have hyA : MulAut.conj y ∈ unipotentPairAut Tag.D4 K := by
    have : MulAut.conj y = (βt * β) * (β' * βt)⁻¹ := by rw [hyy]; group
    rw [this]
    exact mul_mem (mul_mem hβt hβ) (inv_mem (mul_mem hβ' hβt))
  have h1 : (⟨βt, hβt⟩ * ⟨β, hβ⟩ : unipotentPairAut Tag.D4 K) =
      ⟨MulAut.conj y, hyA⟩ * (⟨β', hβ'⟩ * ⟨βt, hβt⟩) := Subtype.ext hyy
  have h2 := congrArg (simplePermHom Tag.D4 K) h1
  have h4 := perm_conj_eq_one y hyA
  rw [map_mul, map_mul, map_mul, h4, one_mul] at h2
  exact h2.symm

theorem perm_sq_of_sq {c : adjointGroup Tag.D4 K} {β : MulAut (adjointGroup Tag.D4 K)}
    (hβ : β ∈ unipotentPairAut Tag.D4 K) (h2 : (MulAut.conj c * β) * (MulAut.conj c * β) = 1) :
    simplePermHom Tag.D4 K ⟨β, hβ⟩ * simplePermHom Tag.D4 K ⟨β, hβ⟩ = 1 := by
  have e3 : MulAut.conj c * β * (MulAut.conj c * β) = MulAut.conj (c * β c) * (β * β) := by
    calc MulAut.conj c * β * (MulAut.conj c * β) = MulAut.conj c * (β * MulAut.conj c) * β := by group
      _ = MulAut.conj c * (MulAut.conj (β c) * β) * β := by rw [mul_conj_eq]
      _ = MulAut.conj (c * β c) * (β * β) := by rw [map_mul]; group
  rw [e3] at h2
  have hsq : β * β = MulAut.conj (c * β c)⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h2
  have hyA : MulAut.conj (c * β c)⁻¹ ∈ unipotentPairAut Tag.D4 K := by
    rw [← hsq]; exact mul_mem hβ hβ
  have h1 : (⟨β, hβ⟩ * ⟨β, hβ⟩ : unipotentPairAut Tag.D4 K) = ⟨MulAut.conj (c * β c)⁻¹, hyA⟩ :=
    Subtype.ext hsq
  have h2' := congrArg (simplePermHom Tag.D4 K) h1
  rw [map_mul] at h2'
  exact h2'.trans (perm_conj_eq_one (c * β c)⁻¹ hyA)

end PermRel

section Finite

theorem perm_a4_trivial (ε : ℕ) (hε : ε = 1 ∨ ε = 2) (π₁ : Equiv.Perm (Fin Tag.D4.rank))
    (h2 : π₁ 2 = 2) (hsq : π₁ * π₁ = 1)
    (h3 : π₁ * ((d4Rho ^ ε) * π₁ * (d4Rho ^ ε)⁻¹) =
      (d4Rho ^ ε) * ((d4Rho ^ ε) * π₁ * (d4Rho ^ ε)⁻¹) * (d4Rho ^ ε)⁻¹) : π₁ = 1 := by
  rcases hε with rfl | rfl
  · revert π₁
    unfold d4Rho TwistTag.perm
    decide +kernel
  · revert π₁
    unfold d4Rho TwistTag.perm
    decide +kernel

end Finite

section A4Perm

variable {K : Type} [Field K] [Finite K]

theorem a4_perm_trivial {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {g c₁ c₂ : adjointGroup Tag.D4 K}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {β₁ β₂ : MulAut (adjointGroup Tag.D4 K)}
    (hβ₁ : β₁ ∈ unipotentPairAut Tag.D4 K) (hβ₂ : β₂ ∈ unipotentPairAut Tag.D4 K)
    (h₁ : (MulAut.conj c₁ * β₁) * (MulAut.conj c₁ * β₁) = 1)
    (hb₁ : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) *
        (MulAut.conj c₁ * β₁) =
      (MulAut.conj c₂ * β₂) * (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)))
    (hb₂ : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) *
        (MulAut.conj c₂ * β₂) =
      ((MulAut.conj c₁ * β₁) * (MulAut.conj c₂ * β₂)) *
        (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) :
    simplePermHom Tag.D4 K ⟨β₁, hβ₁⟩ = 1 ∧ simplePermHom Tag.D4 K ⟨β₂, hβ₂⟩ = 1 := by
  set βt : MulAut (adjointGroup Tag.D4 K) := exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε with hβt
  have hβtA : βt ∈ unipotentPairAut Tag.D4 K := mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hpt : simplePermHom Tag.D4 K ⟨βt, hβtA⟩ = d4Rho ^ ε := perm_normal_graph a σ ε
  have hr1 := perm_relation hβtA hβ₁ hβ₂ hb₁
  have e3 : (MulAut.conj c₁ * β₁) * (MulAut.conj c₂ * β₂) =
      MulAut.conj (c₁ * β₁ c₂) * (β₁ * β₂) := by
    calc (MulAut.conj c₁ * β₁) * (MulAut.conj c₂ * β₂)
        = MulAut.conj c₁ * (β₁ * MulAut.conj c₂) * β₂ := by group
      _ = MulAut.conj c₁ * (MulAut.conj (β₁ c₂) * β₁) * β₂ := by rw [mul_conj_eq]
      _ = MulAut.conj (c₁ * β₁ c₂) * (β₁ * β₂) := by rw [map_mul]; group
  have hβ₁₂ : β₁ * β₂ ∈ unipotentPairAut Tag.D4 K := mul_mem hβ₁ hβ₂
  have hr2 := perm_relation hβtA hβ₂ hβ₁₂ (by rw [← e3]; exact hb₂)
  have hsq := perm_sq_of_sq hβ₁ h₁
  have hmul : simplePermHom Tag.D4 K ⟨β₁ * β₂, hβ₁₂⟩ =
      simplePermHom Tag.D4 K ⟨β₁, hβ₁⟩ * simplePermHom Tag.D4 K ⟨β₂, hβ₂⟩ :=
    map_mul (simplePermHom Tag.D4 K) ⟨β₁, hβ₁⟩ ⟨β₂, hβ₂⟩
  rw [hmul, hpt] at hr2
  rw [hpt] at hr1
  have h2 : simplePermHom Tag.D4 K ⟨β₁, hβ₁⟩ 2 = 2 := simplePerm_two ⟨β₁, hβ₁⟩
  have hπ₂ : simplePermHom Tag.D4 K ⟨β₂, hβ₂⟩ =
      (d4Rho ^ ε) * simplePermHom Tag.D4 K ⟨β₁, hβ₁⟩ * (d4Rho ^ ε)⁻¹ := eq_mul_inv_of_mul_eq hr1
  have hπ₁ : simplePermHom Tag.D4 K ⟨β₁, hβ₁⟩ = 1 := by
    refine perm_a4_trivial ε hε _ h2 hsq ?_
    rw [← hπ₂]
    exact eq_mul_inv_of_mul_eq hr2
  refine ⟨hπ₁, ?_⟩
  rw [hπ₂, hπ₁]; group

end A4Perm

end CFSG.LocalAnalysis.GLTheoremA

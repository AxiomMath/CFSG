module

public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

variable {H : Type*} [Group H] {Δ : Type*} {M : Type*} [CommGroup M]

def supported (rad : Δ → Subgroup M) (Γ : Set Δ) : Subgroup M :=
  ⨅ D ∈ Γᶜ, rad D

theorem mem_supported {rad : Δ → Subgroup M} {Γ : Set Δ} {x : M} :
    x ∈ supported rad Γ ↔ ∀ D, D ∉ Γ → x ∈ rad D := by
  simp [supported]

theorem eq_one_of_prod_eq_one_of_disjoint_supports (rad : Δ → Subgroup M)
    (hbot : ∀ x : M, (∀ D, x ∈ rad D) → x = 1) {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : ι → Set Δ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Γ i) (Γ j)) (x : ι → M) (hx : ∀ i, x i ∈ supported rad (Γ i))
    (hprod : ∏ i, x i = 1) (i : ι) : x i = 1 := by
  refine hbot _ fun D => ?_
  by_cases hD : D ∈ Γ i
  · have hterm : ∀ j, j ≠ i → x j ∈ rad D := fun j hj =>
      (mem_supported.mp (hx j)) D fun hmem => Set.disjoint_left.mp (hdisj j i hj) hmem hD
    have hsplit := Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)
    have hinv : x i = (∏ j ∈ Finset.univ.erase i, x j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [hsplit]
      exact hprod
    rw [hinv]
    exact (rad D).inv_mem (prod_mem fun j hj => hterm j (Finset.ne_of_mem_erase hj))
  · exact (mem_supported.mp (hx i)) D hD

section Equivariant

variable (φ : H →* Equiv.Perm Δ) (ψ : H →* Monoid.End M) (rad : Δ → Subgroup M)

theorem map_mem_supported (hmap : ∀ (h : H) (D : Δ) (x : M), x ∈ rad D → ψ h x ∈ rad (φ h D))
    {Γ : Set Δ} {x : M} (hx : x ∈ supported rad Γ) (h : H) : ψ h x ∈ supported rad (φ h '' Γ) := by
  rw [mem_supported] at hx ⊢
  intro D hD
  have h1 : (φ h).symm D ∉ Γ := fun hmem => hD ⟨(φ h).symm D, hmem, (φ h).apply_symm_apply D⟩
  simpa using hmap h _ x (hx _ h1)

theorem pairwise_disjoint_translates (B : Subgroup H) {Γ : Set Δ}
    (hdisj : ∀ b ∈ B, b ≠ 1 → Disjoint (φ b '' Γ) Γ) (b b' : B) (hbb : b ≠ b') :
    Disjoint (φ b '' Γ) (φ b' '' Γ) := by
  rw [Set.disjoint_left]
  rintro z ⟨γ₁, hγ₁, rfl⟩ ⟨γ₂, hγ₂, h⟩
  have h1 : (b'⁻¹ * b : B) ≠ 1 := fun h' => hbb (by simpa [inv_mul_eq_one, eq_comm] using h')
  have h2 : φ ((b'⁻¹ * b : B) : H) γ₁ = γ₂ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Equiv.Perm.mul_apply, ← h, ← Equiv.Perm.mul_apply,
      ← map_mul]
    simp
  exact Set.disjoint_left.mp (hdisj _ (b'⁻¹ * b).2 fun h' => h1 (Subtype.ext h')) ⟨γ₁, hγ₁, h2⟩ hγ₂

theorem prod_ne_one_of_disjoint_translates
    (hmap : ∀ (h : H) (D : Δ) (x : M), x ∈ rad D → ψ h x ∈ rad (φ h D))
    (hbot : ∀ x : M, (∀ D, x ∈ rad D) → x = 1) (B : Subgroup H) [Fintype B] {Γ : Set Δ}
    (hdisj : ∀ b ∈ B, b ≠ 1 → Disjoint (φ b '' Γ) Γ) {x : M} (hx : x ∈ supported rad Γ) (hx1 : x ≠ 1) :
    ∏ b : B, ψ (b : H) x ≠ 1 := by
  classical
  intro hprod
  have h1 := eq_one_of_prod_eq_one_of_disjoint_supports rad hbot (fun b : B => φ (b : H) '' Γ)
    (pairwise_disjoint_translates φ B hdisj) (fun b : B => ψ (b : H) x)
    (fun b => map_mem_supported φ ψ rad hmap hx (b : H)) hprod 1
  apply hx1
  have h2 : ψ ((1 : B) : H) x = x := by simp
  rw [← h2]
  exact h1

theorem prod_translates_fixed (B : Subgroup H) [Fintype B] (x : M) (b' : B) :
    ψ (b' : H) (∏ b : B, ψ (b : H) x) = ∏ b : B, ψ (b : H) x := by
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft b') _ _ fun b => ?_
  show ψ (b' : H) (ψ (b : H) x) = ψ ((b' * b : B) : H) x
  rw [Subgroup.coe_mul, map_mul]
  rfl

end Equivariant

theorem card_subtype_ne_one (B : Type*) [Group B] [Finite B] :
    Nat.card {b : B // b ≠ 1} = Nat.card B - 1 := by
  classical
  haveI := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert Fintype.card_subtype_compl (fun b : B => b = 1) using 2
  simp

section Counting

variable (φ : H →* Equiv.Perm Δ) (S B : Subgroup H) (D₀ : Δ)

structure RegularConfig : Prop where
  normalizes : ∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ ∈ S
  fixes : ∀ b ∈ B, φ b D₀ = D₀
  transitive : ∀ D, ∃ s ∈ S, φ s D₀ = D
  stabilizer_trivial : ∀ s ∈ S, φ s D₀ = D₀ → φ s = 1
  semiregular : ∀ b ∈ B, b ≠ 1 → ∀ D, φ b D = D → D = D₀

variable {φ S B D₀}

theorem RegularConfig.mono (hc : RegularConfig φ S B D₀) {B' : Subgroup H} (h : B' ≤ B) :
    RegularConfig φ S B' D₀ :=
  ⟨fun b hb s hs => hc.normalizes b (h hb) s hs, fun b hb => hc.fixes b (h hb), hc.transitive,
    hc.stabilizer_trivial, fun b hb => hc.semiregular b (h hb)⟩

theorem RegularConfig.action_eq (hc : RegularConfig φ S B D₀) {x y : H} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : φ x D₀ = φ y D₀) : φ x = φ y := by
  have h1 : φ (y⁻¹ * x) D₀ = D₀ := by
    rw [map_mul, Equiv.Perm.mul_apply, hxy, ← Equiv.Perm.mul_apply, ← map_mul]
    simp
  have h2 := hc.stabilizer_trivial _ (S.mul_mem (S.inv_mem hy) hx) h1
  rw [map_mul, map_inv] at h2
  exact (inv_mul_eq_one.mp h2).symm

theorem RegularConfig.sol_unique (hc : RegularConfig φ S B D₀) {b : H} (hb : b ∈ B) (hb1 : b ≠ 1)
    (γ γ' : Δ) {s₁ s₂ : H} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (h₁ : φ b (φ s₁ γ) = φ s₁ γ')
    (h₂ : φ b (φ s₂ γ) = φ s₂ γ') : φ s₁ D₀ = φ s₂ D₀ := by
  obtain ⟨u, hu, rfl⟩ := hc.transitive γ
  obtain ⟨u', hu', rfl⟩ := hc.transitive γ'
  have key : ∀ s ∈ S, φ b (φ s (φ u D₀)) = φ s (φ u' D₀) →
      φ (b * s * b⁻¹) = φ s * φ u' * (φ (b * u * b⁻¹))⁻¹ := by
    intro s hs h
    have hx : b * s * u * b⁻¹ ∈ S := by
      have := S.mul_mem (hc.normalizes b hb s hs) (hc.normalizes b hb u hu)
      convert this using 1
      group
    have hy : s * u' ∈ S := S.mul_mem hs hu'
    have hD : φ (b * s * u * b⁻¹) D₀ = φ (s * u') D₀ := by
      have e1 : φ (b * s * u * b⁻¹) D₀ = φ b (φ s (φ u D₀)) := by
        have : φ (b * s * u * b⁻¹) (φ b D₀) = φ b (φ s (φ u D₀)) := by
          rw [← Equiv.Perm.mul_apply, ← map_mul]
          have : b * s * u * b⁻¹ * b = b * (s * u) := by group
          rw [this, map_mul, map_mul]
          rfl
        rwa [hc.fixes b hb] at this
      rw [e1, h, map_mul]
      rfl
    have hφ := hc.action_eq hx hy hD
    have e2 : φ (b * s * u * b⁻¹) = φ (b * s * b⁻¹) * φ (b * u * b⁻¹) := by
      rw [← map_mul]
      congr 1
      group
    rw [e2, map_mul φ s u'] at hφ
    exact eq_mul_inv_of_mul_eq hφ
  have e₁ := key s₁ hs₁ h₁
  have e₂ := key s₂ hs₂ h₂
  have hy : s₁ * s₂⁻¹ ∈ S := S.mul_mem hs₁ (S.inv_mem hs₂)
  have hconj : φ (b * (s₁ * s₂⁻¹) * b⁻¹) = φ (s₁ * s₂⁻¹) := by
    have h3 : b * (s₁ * s₂⁻¹) * b⁻¹ = (b * s₁ * b⁻¹) * (b * s₂ * b⁻¹)⁻¹ := by group
    rw [h3, map_mul φ (b * s₁ * b⁻¹), map_inv φ (b * s₂ * b⁻¹), e₁, e₂, map_mul φ s₁, map_inv φ s₂]
    group
  have hfix : φ b (φ (s₁ * s₂⁻¹) D₀) = φ (s₁ * s₂⁻¹) D₀ := by
    have : φ (b * (s₁ * s₂⁻¹) * b⁻¹) (φ b D₀) = φ b (φ (s₁ * s₂⁻¹) D₀) := by
      rw [← Equiv.Perm.mul_apply, ← map_mul]
      have : b * (s₁ * s₂⁻¹) * b⁻¹ * b = b * (s₁ * s₂⁻¹) := by group
      rw [this, map_mul]
      rfl
    rw [← this, hc.fixes b hb, hconj]
  have h0 := hc.semiregular b hb hb1 _ hfix
  have h1 := hc.stabilizer_trivial _ hy h0
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [h1]

theorem exists_good_translate [Finite Δ] [Finite B] (hc : RegularConfig φ S B D₀) (Γ : Set Δ)
    (hΓ : (Nat.card B - 1) * Γ.ncard ^ 2 < Nat.card Δ) :
    ∃ s ∈ S, ∀ b ∈ B, b ≠ 1 → Disjoint (φ b '' (φ s '' Γ)) (φ s '' Γ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∀ D : Δ, ∃ τ : {b : B // b ≠ 1} × Γ × Γ, ∃ s ∈ S, φ s D₀ = D ∧
      φ ((τ.1.1 : B) : H) (φ s (τ.2.1 : Δ)) = φ s (τ.2.2 : Δ) := by
    intro D
    obtain ⟨s, hs, hsD⟩ := hc.transitive D
    obtain ⟨b, hb, hb1, hnd⟩ := hcon s hs
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨z, ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩, ⟨γ', hγ', hz⟩⟩ := hnd
    exact ⟨(⟨⟨b, hb⟩, fun h => hb1 (congrArg Subtype.val h)⟩, ⟨γ, hγ⟩, ⟨γ', hγ'⟩), s, hs, hsD, hz.symm⟩
  choose f s hs hsD hf using hex
  have hinj : Function.Injective f := by
    intro D₁ D₂ h12
    have e1 := hf D₁
    have e2 := hf D₂
    rw [h12] at e1
    have := hc.sol_unique (f D₂).1.1.2 (fun h => (f D₂).1.2 (Subtype.ext h)) _ _ (hs D₁) (hs D₂) e1 e2
    rwa [hsD D₁, hsD D₂] at this
  have hle := Nat.card_le_card_of_injective f hinj
  have hcard : Nat.card ({b : B // b ≠ 1} × Γ × Γ) = (Nat.card B - 1) * Γ.ncard ^ 2 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, card_subtype_ne_one, pow_two]
  omega

end Counting

section Assembly

variable {φ : H →* Equiv.Perm Δ} {S B : Subgroup H} {D₀ : Δ}

theorem eq_one_of_card_lt [Finite Δ] [Finite B] (ψ : H →* Monoid.End M) (rad : Δ → Subgroup M)
    (hmap : ∀ (h : H) (D : Δ) (x : M), x ∈ rad D → ψ h x ∈ rad (φ h D))
    (hbot : ∀ x : M, (∀ D, x ∈ rad D) → x = 1) (hc : RegularConfig φ S B D₀) (hBnt : ∃ b ∈ B, b ≠ 1)
    (hM : ∀ b ∈ B, b ≠ 1 → ∀ x : M, ψ b x = x → x = 1) {Γ : Set Δ}
    (hΓ : (Nat.card B - 1) * Γ.ncard ^ 2 < Nat.card Δ) {x : M} (hx : x ∈ supported rad Γ) : x = 1 := by
  classical
  by_contra hx1
  obtain ⟨s, hs, hgood⟩ := exists_good_translate hc Γ hΓ
  haveI : Fintype B := Fintype.ofFinite B
  have hx' : ψ s x ∈ supported rad (φ s '' Γ) := map_mem_supported φ ψ rad hmap hx s
  have hx'1 : ψ s x ≠ 1 := by
    intro h
    have h1 : ψ s⁻¹ (ψ s x) = x := by
      have : ψ (s⁻¹ * s) x = x := by simp
      rw [map_mul] at this
      exact this
    rw [h, map_one] at h1
    exact hx1 h1.symm
  have hprod := prod_ne_one_of_disjoint_translates φ ψ rad hmap hbot B hgood hx' hx'1
  obtain ⟨b, hb, hb1⟩ := hBnt
  exact hprod (hM b hb hb1 _ (prod_translates_fixed ψ B (ψ s x) ⟨b, hb⟩))

end Assembly

end CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

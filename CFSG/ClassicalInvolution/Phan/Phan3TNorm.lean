module

public import CFSG.ClassicalInvolution.Phan.Coherent
public import CFSG.ClassicalInvolution.Phan.Phan3TAutA
public import CFSG.ClassicalInvolution.Phan.Phan3TAutB
public import CFSG.ClassicalInvolution.Phan.Parabolic.TorusHom

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]
  {n : ℕ}

structure BlockTriple (F : PhanFamily K p f X n) (θ : Su K p f 4 →* X) (i₀ i₁ i₂ : Fin n) :
    Prop where
  h₁ : (i₁ : ℕ) = i₀ + 1
  h₂ : (i₂ : ℕ) = i₁ + 1
  ker : θ.ker ≤ Subgroup.center (Su K p f 4)
  e₀ : (blockEmb2 K p f 3 0).range.map θ = (F.ι i₀).range
  e₁ : (blockEmb2 K p f 3 1).range.map θ = (F.ι i₁).range
  e₂ : (blockEmb2 K p f 3 2).range.map θ = (F.ι i₂).range
  hι : ∀ i, Function.Injective (F.ι i)
  hθ : ∀ i : Fin n, (i : ℕ) + 1 < n → (F.θ i).ker ≤ Subgroup.center (Su K p f 3)

variable {F : PhanFamily K p f X n} {θ : Su K p f 4 →* X} {i₀ i₁ i₂ : Fin n}

theorem BlockTriple.inj (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    (k : Fin 3) : Function.Injective (θ.comp (blockEmb2 K p f 3 k)) :=
  comp_blockEmb_injective (m := 4) (k := 2) (i := k.val) hK T.ker (by omega) (by omega)
    (by omega)

theorem BlockTriple.middle_torus (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β : Su K p f 2 ≃* Su K p f 2} (hβ : ∀ g, F.ι i₁ (β g) = θ (blockEmb2 K p f 3 1 g)) :
    (diagTorus2 K p f).map β.symm.toMonoidHom = diagTorus2 K p f := by
  have hi₀ : (i₀ : ℕ) + 1 < n := by have := i₁.isLt; have := T.h₁; omega
  have hlt3 : (1 : ℕ) + 1 < 3 := by omega
  let θ₂ : Su K p f 3 →* X := θ.comp (blockEmb3 K p f 3 ⟨1, by omega⟩ hlt3)
  have hθ₂inj : Function.Injective θ₂ :=
    comp_blockEmb_injective (m := 4) (k := 3) (i := 1) hK T.ker (by omega) (by omega) (by omega)
  have hθ₂ker : θ₂.ker ≤ Subgroup.center (Su K p f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hθ₂inj]
    exact bot_le
  have hfin : (⟨i₀ + 1, hi₀⟩ : Fin n) = i₁ := Fin.ext T.h₁.symm
  have hR : (F.θ i₀).comp (embSUid (unitaryInvolution K p f) 0) = F.ι i₁ := by
    have := F.right i₀ hi₀
    rwa [hfin] at this
  have hL : (F.θ i₀).comp (embSUid (unitaryInvolution K p f) 2) = F.ι i₀ := F.left i₀ hi₀
  have h2 : θ₂.comp (embSUid (unitaryInvolution K p f) 2) = θ.comp (blockEmb2 K p f 3 1) := by
    rw [MonoidHom.comp_assoc]
    exact congrArg θ.comp (blockEmb3_comp_embSUid_two 3 ⟨1, by omega⟩ hlt3)
  have h0 : θ₂.comp (embSUid (unitaryInvolution K p f) 0) = θ.comp (blockEmb2 K p f 3 2) := by
    rw [MonoidHom.comp_assoc]
    exact congrArg θ.comp (blockEmb3_comp_embSUid_zero 3 ⟨1, by omega⟩ hlt3)
  have hM : (B23 K p f).map (F.θ i₀) = (B12 K p f).map θ₂ := by
    change (embSUid (unitaryInvolution K p f) 0).range.map (F.θ i₀) =
      (embSUid (unitaryInvolution K p f) 2).range.map θ₂
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp, hR, h2, MonoidHom.range_comp]
    exact T.e₁.symm
  have hcomm : ∀ x ∈ (B12 K p f).map (F.θ i₀), ∀ y ∈ (B23 K p f).map θ₂, x * y = y * x := by
    intro x hx y hy
    change x ∈ (embSUid (unitaryInvolution K p f) 2).range.map (F.θ i₀) at hx
    change y ∈ (embSUid (unitaryInvolution K p f) 0).range.map θ₂ at hy
    rw [← MonoidHom.range_comp, hL] at hx
    rw [← MonoidHom.range_comp, h0, MonoidHom.range_comp, T.e₂] at hy
    obtain ⟨A, rfl⟩ := hx
    obtain ⟨B, rfl⟩ := hy
    exact F.comm i₀ i₂ (by have := T.h₁; have := T.h₂; omega) A B
  have hagree := torus_agree hK (T.hθ i₀ hi₀) hθ₂ker hM hcomm
  rw [map_D23, map_D12, hR, h2] at hagree
  have hι : F.ι i₁ = (θ.comp (blockEmb2 K p f 3 1)).comp β.symm.toMonoidHom := by
    ext h
    have := hβ (β.symm h)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  rw [hι, ← Subgroup.map_map] at hagree
  exact Subgroup.map_injective (T.inj hK 1) hagree

theorem blockEmb2_torusTwo_comm_four (j k : Fin 3) (u v : normOne (unitaryInvolution K p f)) :
    blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) u) *
        blockEmb2 K p f 3 k (torusTwo (unitaryInvolution K p f) v) =
      blockEmb2 K p f 3 k (torusTwo (unitaryInvolution K p f) v) *
        blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) u) :=
  torus_mul_comm (blockEmb2_torusTwo_mem_torus j u) (blockEmb2_torusTwo_mem_torus k v)

theorem BlockTriple.first_torus (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₀ β₁ : Su K p f 2 ≃* Su K p f 2}
    (hβ₀ : ∀ g, F.ι i₀ (β₀ g) = θ (blockEmb2 K p f 3 0 g))
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    (hD₁ : (diagTorus2 K p f).map β₁.toMonoidHom = diagTorus2 K p f) :
    (diagTorus2 K p f).map β₀.toMonoidHom ≤ diagTorus2 K p f := by
  have hi₀ : (i₀ : ℕ) + 1 < n := by have := i₁.isLt; have := T.h₁; omega
  have hfin : (⟨i₀ + 1, hi₀⟩ : Fin n) = i₁ := Fin.ext T.h₁.symm
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_normOne_ne_one hK
  have hmem : torusTwo (unitaryInvolution K p f) s ∈
      (diagTorus2 K p f).map β₁.toMonoidHom := by
    rw [hD₁]
    exact ⟨s, rfl⟩
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hmem
  have hc := congrArg θ (blockEmb2_torusTwo_comm_four (K := K) (p := p) (f := f) 0 1 u v)
  rw [map_mul, map_mul, ← hβ₀, ← hβ₁] at hc
  have hv' : β₁ (torusTwo (unitaryInvolution K p f) v) =
      torusTwo (unitaryInvolution K p f) s := hv
  rw [hv'] at hc
  refine mem_diagTorus2_of_map_commute_zero hK (T.hθ i₀ hi₀) hs ?_
  rw [F.θ_embSUid_two i₀ hi₀, F.θ_embSUid_zero i₀ hi₀, hfin]
  exact hc

theorem BlockTriple.last_torus (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₁ β₂ : Su K p f 2 ≃* Su K p f 2}
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    (hβ₂ : ∀ g, F.ι i₂ (β₂ g) = θ (blockEmb2 K p f 3 2 g))
    (hD₁ : (diagTorus2 K p f).map β₁.toMonoidHom = diagTorus2 K p f) :
    (diagTorus2 K p f).map β₂.toMonoidHom ≤ diagTorus2 K p f := by
  have hi₁ : (i₁ : ℕ) + 1 < n := by have := i₂.isLt; have := T.h₂; omega
  have hfin : (⟨i₁ + 1, hi₁⟩ : Fin n) = i₂ := Fin.ext T.h₂.symm
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_normOne_ne_one hK
  have hmem : torusTwo (unitaryInvolution K p f) s ∈
      (diagTorus2 K p f).map β₁.toMonoidHom := by
    rw [hD₁]
    exact ⟨s, rfl⟩
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hmem
  have hc := congrArg θ (blockEmb2_torusTwo_comm_four (K := K) (p := p) (f := f) 2 1 u v)
  rw [map_mul, map_mul, ← hβ₂, ← hβ₁] at hc
  have hv' : β₁ (torusTwo (unitaryInvolution K p f) v) =
      torusTwo (unitaryInvolution K p f) s := hv
  rw [hv'] at hc
  refine mem_diagTorus2_of_map_commute_two hK (T.hθ i₁ hi₁) hs ?_
  rw [F.θ_embSUid_two i₁ hi₁, F.θ_embSUid_zero i₁ hi₁, hfin]
  exact hc

theorem BlockTriple.conj_left (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₀ β₁ : Su K p f 2 ≃* Su K p f 2}
    (hβ₀ : ∀ g, F.ι i₀ (β₀ g) = θ (blockEmb2 K p f 3 0 g))
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    {c u : normOne (unitaryInvolution K p f)}
    (hcu : β₀ (torusTwo (unitaryInvolution K p f) c) = torusTwo (unitaryInvolution K p f) u)
    (B : Su K p f 2) :
    conjDiag hK ![u⁻¹, 1] (β₁ B) = β₁ (conjDiag hK ![c⁻¹, 1] B) := by
  have hmain := blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK (n := 3) (0 : Fin 3) (1 : Fin 3) c B
  change blockEmb2 K p f 3 0 (torusTwo (unitaryInvolution K p f) c) * blockEmb2 K p f 3 1 B *
      (blockEmb2 K p f 3 0 (torusTwo (unitaryInvolution K p f) c))⁻¹ =
    blockEmb2 K p f 3 1 (conjDiag hK (blockTuple (n := 3) 0 1 c) B) at hmain
  rw [blockTuple_succ (by rfl)] at hmain
  have h2 := congrArg θ hmain
  simp only [map_mul, map_inv] at h2
  rw [← hβ₀, ← hβ₁, ← hβ₁, hcu] at h2
  have h3 := F.conj_torusFactor hK i₀ i₁ u (β₁ B)
  rw [blockTuple_succ T.h₁, PhanFamily.torusFactor_apply] at h3
  exact T.hι i₁ (h3.symm.trans h2)

theorem BlockTriple.conj_right (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₁ β₂ : Su K p f 2 ≃* Su K p f 2}
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    (hβ₂ : ∀ g, F.ι i₂ (β₂ g) = θ (blockEmb2 K p f 3 2 g))
    {c u : normOne (unitaryInvolution K p f)}
    (hcu : β₂ (torusTwo (unitaryInvolution K p f) c) = torusTwo (unitaryInvolution K p f) u)
    (B : Su K p f 2) :
    conjDiag hK ![1, u] (β₁ B) = β₁ (conjDiag hK ![1, c] B) := by
  have hmain := blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK (n := 3) (2 : Fin 3) (1 : Fin 3) c B
  change blockEmb2 K p f 3 2 (torusTwo (unitaryInvolution K p f) c) * blockEmb2 K p f 3 1 B *
      (blockEmb2 K p f 3 2 (torusTwo (unitaryInvolution K p f) c))⁻¹ =
    blockEmb2 K p f 3 1 (conjDiag hK (blockTuple (n := 3) 2 1 c) B) at hmain
  rw [blockTuple_pred (by rfl)] at hmain
  have h2 := congrArg θ hmain
  simp only [map_mul, map_inv] at h2
  rw [← hβ₂, ← hβ₁, ← hβ₁, hcu] at h2
  have h3 := F.conj_torusFactor hK i₂ i₁ u (β₁ B)
  rw [blockTuple_pred T.h₂, PhanFamily.torusFactor_apply] at h3
  exact T.hι i₁ (h3.symm.trans h2)

theorem normOneMap_inv (φ : K ≃+* K) (u : normOne (unitaryInvolution K p f)) :
    normOneMap φ u⁻¹ = (normOneMap φ u)⁻¹ :=
  Subtype.ext (map_inv (Units.map (φ : K →* K)) (u : Kˣ))

theorem autForm_torusTwo (hK : Nat.card K = (p ^ f) ^ 2)
    (t : Fin 2 → normOne (unitaryInvolution K p f)) (φ : K ≃+* K)
    (u : normOne (unitaryInvolution K p f)) :
    (diagConj p f hK t * fieldAutSU p f φ 2) (torusTwo (unitaryInvolution K p f) u) =
      torusTwo (unitaryInvolution K p f) (normOneMap φ u) := by
  rw [MulAut.mul_apply, fieldAutSU_torusTwo, diagConj_torusTwo]

theorem BlockTriple.field_eq_left (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₀ β₁ : Su K p f 2 ≃* Su K p f 2}
    (hβ₀ : ∀ g, F.ι i₀ (β₀ g) = θ (blockEmb2 K p f 3 0 g))
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    {a₀ b₀ a₁ b₁ : normOne (unitaryInvolution K p f)} {φ₀ φ₁ : K ≃+* K}
    (hα₀ : β₀.symm = diagConj p f hK ![a₀, b₀] * fieldAutSU p f φ₀ 2)
    (hα₁ : β₁.symm = diagConj p f hK ![a₁, b₁] * fieldAutSU p f φ₁ 2) : φ₀ = φ₁ := by
  refine ringEquiv_eq_of_eq_on_normOne hK φ₀ φ₁ fun u => ?_
  have hcu : β₀ (torusTwo (unitaryInvolution K p f) (normOneMap φ₀ u)) =
      torusTwo (unitaryInvolution K p f) u := by
    have h := autForm_torusTwo hK ![a₀, b₀] φ₀ u
    rw [← hα₀] at h
    rw [← h]
    exact β₀.apply_symm_apply _
  have key : ∀ B : Su K p f 2,
      conjDiag hK ![normOneMap φ₁ u⁻¹, 1] B = conjDiag hK ![(normOneMap φ₀ u)⁻¹, 1] B := by
    intro B
    have h1 := congrArg β₁.symm (T.conj_left hK hβ₀ hβ₁ hcu B)
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 := aut_conjDiag_left hK a₁ b₁ φ₁ u⁻¹ (β₁ B)
    rw [← hα₁, MulEquiv.symm_apply_apply] at h2
    exact h2.symm.trans h1
  have := conjDiag_eq_left hK key
  rw [normOneMap_inv, inv_inj] at this
  exact (congrArg (fun v : normOne (unitaryInvolution K p f) => ((v : Kˣ) : K)) this).symm

theorem BlockTriple.field_eq_right (hK : Nat.card K = (p ^ f) ^ 2) (T : BlockTriple F θ i₀ i₁ i₂)
    {β₁ β₂ : Su K p f 2 ≃* Su K p f 2}
    (hβ₁ : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g))
    (hβ₂ : ∀ g, F.ι i₂ (β₂ g) = θ (blockEmb2 K p f 3 2 g))
    {a₁ b₁ a₂ b₂ : normOne (unitaryInvolution K p f)} {φ₁ φ₂ : K ≃+* K}
    (hα₁ : β₁.symm = diagConj p f hK ![a₁, b₁] * fieldAutSU p f φ₁ 2)
    (hα₂ : β₂.symm = diagConj p f hK ![a₂, b₂] * fieldAutSU p f φ₂ 2) : φ₂ = φ₁ := by
  refine ringEquiv_eq_of_eq_on_normOne hK φ₂ φ₁ fun u => ?_
  have hcu : β₂ (torusTwo (unitaryInvolution K p f) (normOneMap φ₂ u)) =
      torusTwo (unitaryInvolution K p f) u := by
    have h := autForm_torusTwo hK ![a₂, b₂] φ₂ u
    rw [← hα₂] at h
    rw [← h]
    exact β₂.apply_symm_apply _
  have key : ∀ B : Su K p f 2,
      conjDiag hK ![1, normOneMap φ₁ u] B = conjDiag hK ![1, normOneMap φ₂ u] B := by
    intro B
    have h1 := congrArg β₁.symm (T.conj_right hK hβ₁ hβ₂ hcu B)
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 := aut_conjDiag_right hK a₁ b₁ φ₁ u (β₁ B)
    rw [← hα₁, MulEquiv.symm_apply_apply] at h2
    exact h2.symm.trans h1
  have := conjDiag_eq_right hK key
  exact (congrArg (fun v : normOne (unitaryInvolution K p f) => ((v : Kˣ) : K)) this).symm

theorem BlockTriple.exists_extension (hK : Nat.card K = (p ^ f) ^ 2)
    (T : BlockTriple F θ i₀ i₁ i₂) :
    ∃ Θ : Su K p f 4 →* X, Θ.comp (blockEmb2 K p f 3 0) = F.ι i₀ ∧
      Θ.comp (blockEmb2 K p f 3 1) = F.ι i₁ ∧ Θ.comp (blockEmb2 K p f 3 2) = F.ι i₂ := by
  obtain ⟨β₀, hβ₀⟩ := exists_mulEquiv_comp_eq (T.inj hK 0) (T.hι i₀)
    (by rw [MonoidHom.range_comp]; exact T.e₀)
  obtain ⟨β₁, hβ₁⟩ := exists_mulEquiv_comp_eq (T.inj hK 1) (T.hι i₁)
    (by rw [MonoidHom.range_comp]; exact T.e₁)
  obtain ⟨β₂, hβ₂⟩ := exists_mulEquiv_comp_eq (T.inj hK 2) (T.hι i₂)
    (by rw [MonoidHom.range_comp]; exact T.e₂)
  have hβ₀' : ∀ g, F.ι i₀ (β₀ g) = θ (blockEmb2 K p f 3 0 g) := hβ₀
  have hβ₁' : ∀ g, F.ι i₁ (β₁ g) = θ (blockEmb2 K p f 3 1 g) := hβ₁
  have hβ₂' : ∀ g, F.ι i₂ (β₂ g) = θ (blockEmb2 K p f 3 2 g) := hβ₂
  have hD₁ : (diagTorus2 K p f).map β₁.symm.toMonoidHom = diagTorus2 K p f :=
    T.middle_torus hK hβ₁'
  have hD₁' : (diagTorus2 K p f).map β₁.toMonoidHom = diagTorus2 K p f :=
    (Subgroup.map_symm_eq_iff_map_eq (diagTorus2 K p f)).1 hD₁
  have hD₀ : (diagTorus2 K p f).map β₀.toMonoidHom = diagTorus2 K p f :=
    map_eq_of_le_of_finite β₀ (T.first_torus hK hβ₀' hβ₁' hD₁')
  have hD₂ : (diagTorus2 K p f).map β₂.toMonoidHom = diagTorus2 K p f :=
    map_eq_of_le_of_finite β₂ (T.last_torus hK hβ₁' hβ₂' hD₁')
  have hD₀' : (diagTorus2 K p f).map β₀.symm.toMonoidHom = diagTorus2 K p f :=
    (Subgroup.map_symm_eq_iff_map_eq (diagTorus2 K p f)).2 hD₀
  have hD₂' : (diagTorus2 K p f).map β₂.symm.toMonoidHom = diagTorus2 K p f :=
    (Subgroup.map_symm_eq_iff_map_eq (diagTorus2 K p f)).2 hD₂
  obtain ⟨a₀, b₀, φ₀, h₀⟩ := exists_diagConj_fieldAut hK β₀.symm hD₀'.le
  obtain ⟨a₁, b₁, φ₁, h₁⟩ := exists_diagConj_fieldAut hK β₁.symm hD₁.le
  obtain ⟨a₂, b₂, φ₂, h₂⟩ := exists_diagConj_fieldAut hK β₂.symm hD₂'.le
  have e₀ : φ₀ = φ₁ := T.field_eq_left hK hβ₀' hβ₁' h₀ h₁
  have e₂ : φ₂ = φ₁ := T.field_eq_right hK hβ₁' hβ₂' h₁ h₂
  rw [e₀] at h₀
  rw [e₂] at h₂
  obtain ⟨x, hx⟩ := exists_diag_of_ratios
    (![a₀ * b₀⁻¹, a₁ * b₁⁻¹, a₂ * b₂⁻¹] : Fin 3 → normOne (unitaryInvolution K p f))
  have hβ4 : ∀ (k : Fin 3) (A : Su K p f 2) (a b : normOne (unitaryInvolution K p f))
      (γ : Su K p f 2 ≃* Su K p f 2), γ = diagConj p f hK ![a, b] * fieldAutSU p f φ₁ 2 →
      x k.castSucc * (x k.succ)⁻¹ = a * b⁻¹ →
      (diagConj p f hK x * fieldAutSU p f φ₁ 4) (blockEmb2 K p f 3 k A) =
        blockEmb2 K p f 3 k (γ A) := by
    intro k A a b γ hγ hr
    rw [blockAut4_blockEmb2, diagConj_two hK _ _ a b hr, ← hγ]
  refine ⟨θ.comp (diagConj p f hK x * fieldAutSU p f φ₁ 4).toMonoidHom, ?_, ?_, ?_⟩
  · ext A
    have := hβ4 0 A a₀ b₀ β₀.symm h₀ (hx 0)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, ← hβ₀' (β₀.symm A), MulEquiv.apply_symm_apply]
  · ext A
    have := hβ4 1 A a₁ b₁ β₁.symm h₁ (hx 1)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, ← hβ₁' (β₁.symm A), MulEquiv.apply_symm_apply]
  · ext A
    have := hβ4 2 A a₂ b₂ β₂.symm h₂ (hx 2)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, ← hβ₂' (β₂.symm A), MulEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Phan.Q3G

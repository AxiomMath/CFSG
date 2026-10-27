module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Props

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X5

section Conj

variable {k : Type*} [Field k] {V' : Type*} [AddCommGroup V'] [Module k V']
  {H : Type*} [Group H]

theorem fixSub_closure_le {σ : H →* (V' ≃ₗ[k] V')} (S : Set H) {v : V'}
    (hv : ∀ x ∈ S, σ x v = v) : v ∈ fixSub σ (Subgroup.closure S) := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hv x hx
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, LinearEquiv.mul_apply, hy, hx]
  | inv x _ hx =>
    have : σ x⁻¹ v = v := by
      have := congrArg (σ x⁻¹) hx
      rw [ρ_inv_apply] at this
      exact this.symm
    exact this

theorem map_fix_conj [Finite V'] {σ : H →* (V' ≃ₗ[k] V')} (M : Submodule k V')
    (hM : ∀ n, ∀ m ∈ M, σ n m ∈ M) (A : Subgroup H) (l : H) :
    (M ⊓ fixSub σ A).map (σ l : V' →ₗ[k] V') =
      M ⊓ fixSub σ (A.map (MulAut.conj l).toMonoidHom) := by
  ext v
  constructor
  · rintro ⟨u, ⟨hu, hfix⟩, rfl⟩
    refine ⟨hM l u hu, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    show σ (l * a * l⁻¹) (σ l u) = σ l u
    have : σ (l * a * l⁻¹) (σ l u) = σ l (σ a u) := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      rw [← LinearEquiv.mul_apply, ← map_mul]
      congr 2
      group
    rw [this, hfix a ha]
  · rintro ⟨hvM, hvfix⟩
    refine ⟨σ l⁻¹ v, ⟨hM _ v hvM, fun a ha => ?_⟩, ρ_apply_inv σ l v⟩
    have h1 := hvfix (l * a * l⁻¹) ⟨a, ha, rfl⟩
    calc σ a (σ l⁻¹ v) = σ l⁻¹ (σ (l * a * l⁻¹) v) := by
          rw [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
          congr 2
          group
      _ = σ l⁻¹ v := by rw [h1]

theorem card_fix_conj [Finite V'] {σ : H →* (V' ≃ₗ[k] V')} (M : Submodule k V')
    (hM : ∀ n, ∀ m ∈ M, σ n m ∈ M) (A : Subgroup H) (l : H) :
    Nat.card ↥(M ⊓ fixSub σ (A.map (MulAut.conj l).toMonoidHom)) = Nat.card ↥(M ⊓ fixSub σ A) := by
  rw [← map_fix_conj M hM A l]
  exact Nat.card_congr (Submodule.equivMapOfInjective (σ l : V' →ₗ[k] V')
    (σ l).injective (M ⊓ fixSub σ A)).toEquiv.symm

end Conj

section Dim

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem card_M_le (hD : A6ShortGeneration) (ρ : H →* (W ≃ₗ[ZMod 2] W)) (L A : Subgroup H)
    [L.Normal] (hL : CFSG.IsQuasisimple ↥L)
    (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hcent : Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hne : A ≠ ⊥)
    (hel : CFSG.IsElementaryAbelian 2 ↥A) (sec : D4Section ρ L A) :
    Nat.card ↥sec.M ≤ 64 := by
  classical
  have hperf : Group.IsPerfect ↥L := hL.1
  have hker : ∀ h : H, outAct L eQ h = 1 → h ∈ (Subgroup.center ↥L).map L.subtype := fun h hh => by
    have := mem_centralizer_of_outAct_eq_one L eQ hh
    rwa [hcent] at this
  have hinjA : ∀ a ∈ A, outAct L eQ a = 1 → a = 1 := fun a ha hh =>
    eq_one_of_mem_center_of_sq hcent hodd hel ha (mem_centralizer_of_outAct_eq_one L eQ hh)
  have hinj : Function.Injective ((outAct L eQ).comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinjA a.1 a.2 ha)
  have hAbar_card : Nat.card ↥(A.map (outAct L eQ)) = Nat.card ↥A := by
    have h1 : ((outAct L eQ).comp A.subtype).range = A.map (outAct L eQ) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hAbar_el : CFSG.IsElementaryAbelian 2 ↥(A.map (outAct L eQ)) := by
    have := hel
    exact CFSG.IsElementaryAbelian.map (outAct L eQ)
  have hAbar_ne : A.map (outAct L eQ) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have h1 : outAct L eQ a ∈ A.map (outAct L eQ) := ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (hinjA a ha h1)
  obtain ⟨r, m, hr, hr1, hr3, hmr, s, hgen⟩ := hD.2.2.2 _ hAbar_ne hAbar_el
  obtain ⟨l, hl⟩ := L_le_closure_of_inner_generation L eQ hker A s hgen
  set M := sec.M with hMdef
  set σ := cvAct ρ L with hσ
  let U : Fin m → Submodule (ZMod 2) (W ⧸ fixSub ρ L) := fun i =>
    M ⊓ fixSub σ (A.map (MulAut.conj (l i : H)).toMonoidHom)
  have hUM : ∀ i ∈ (Finset.univ : Finset (Fin m)), U i ≤ M := fun i _ => inf_le_left
  have hq : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Nat.card ↥M ≤ Nat.card ↥A * Nat.card ↥(U i) := by
    intro i _
    show Nat.card ↥M ≤ Nat.card ↥A *
      Nat.card ↥(M ⊓ fixSub σ (A.map (MulAut.conj (l i : H)).toMonoidHom))
    rw [card_fix_conj M sec.Minv A (l i : H)]
    exact sec.offender
  have hbot : M ⊓ (Finset.univ : Finset (Fin m)).inf U = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvM, hvU⟩ := Submodule.mem_inf.1 hv
    have hvfix : ∀ i, v ∈ fixSub σ (A.map (MulAut.conj (l i : H)).toMonoidHom) := fun i => by
      have : v ∈ U i := (Finset.inf_le (Finset.mem_univ i) : (Finset.univ : Finset (Fin m)).inf U ≤ U i) hvU
      exact (Submodule.mem_inf.1 this).2
    have hvJ : v ∈ fixSub σ (Subgroup.closure (⋃ i,
        ((A.map (MulAut.conj (l i : H)).toMonoidHom : Subgroup H) : Set H))) := by
      refine fixSub_closure_le _ (fun x hx => ?_)
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      exact hvfix i x hxi
    have hvL : v ∈ fixSub σ L := fun x hx => hvJ x (hl hx)
    have : v ∈ M ⊓ fixSub σ L := ⟨hvM, hvL⟩
    rw [sec.fix_bot] at this
    exact this
  have hmain := card_le_pow_mul_card_iInf U (Finset.univ : Finset (Fin m)) hUM hq
  rw [hbot, Finset.card_univ, Fintype.card_fin] at hmain
  have hbotcard : Nat.card ↥(⊥ : Submodule (ZMod 2) (W ⧸ fixSub ρ L)) = 1 := by
    simp
  rw [hbotcard, mul_one, ← hAbar_card, hr, ← pow_mul] at hmain
  calc Nat.card ↥M ≤ 2 ^ (r * m) := hmain
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hmr)
    _ = 64 := by norm_num

end Dim

end CFSG.QuasithinUnique.Setup.X3

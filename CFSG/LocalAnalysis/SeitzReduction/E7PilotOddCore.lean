module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem map_mem_closure_odd_centralizer {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {t : G}
    (ht : t ∈ closure {c : G | c ∈ centralizer ({t} : Set G) ∧ Odd (orderOf c)}) :
    φ t ∈ closure {c : H | c ∈ φ.range ⊓ centralizer ({φ t} : Set H) ∧ Odd (orderOf c)} := by
  have h := mem_map_of_mem φ ht
  rw [MonoidHom.map_closure] at h
  refine Subgroup.closure_mono ?_ h
  rintro _ ⟨c, ⟨hc, hodd⟩, rfl⟩
  refine ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_range.2 ⟨c, rfl⟩, ?_⟩,
    by rwa [orderOf_injective φ hφ c]⟩
  rw [mem_centralizer_singleton_iff] at hc ⊢
  rw [← map_mul, ← map_mul, hc]

theorem conj_mem_closure_odd_centralizer {G : Type*} [Group G] (n : G) {t : G}
    (ht : t ∈ closure {c : G | c ∈ centralizer ({t} : Set G) ∧ Odd (orderOf c)}) :
    n * t * n⁻¹ ∈
      closure {c : G | c ∈ centralizer ({n * t * n⁻¹} : Set G) ∧ Odd (orderOf c)} := by
  have h :=
    map_mem_closure_odd_centralizer (MulAut.conj n).toMonoidHom (MulAut.conj n).injective ht
  refine Subgroup.closure_mono ?_ h
  intro c hc
  exact ⟨(Subgroup.mem_inf.1 hc.1).2, hc.2⟩

theorem setOf_mem_centralizer_odd_eq {G : Type*} [Group G] (t : G) :
    {c : G | c ∈ centralizer ({t} : Set G) ∧ Odd (orderOf c)} =
      {c : G | c * t = t * c ∧ Odd (orderOf c)} := by
  ext c
  exact and_congr_left fun _ => mem_centralizer_singleton_iff

@[expose] def oddDerivE7XFrame : List (Fin Tag.E7.rank → ℤ) :=
  [highRoot .E7]

@[expose] def oddDerivE7XDeriv :
    List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) := [
  (![1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 0], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 1, 0], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 0, 0], ![1, 1, 1, 2, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 1], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 0], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 1, 0], ![1, 1, 1, 2, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1, 1], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 1], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1, 0], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 2, 1], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 2, 1, 1], ![1, 1, 1, 2, 2, 1, 1], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 2, 1], ![0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 2, 1], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 1, 1], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 3, 2, 1], ![0, -1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 3, 2, 2, 1], ![1, 1, 2, 3, 2, 2, 1], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 1], ![0, 1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![0, 0, -1, 0, 0, 0, 0]),
  (![1, 2, 3, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![0, 0, 1, 0, 0, 0, 0]),
  (![2, 2, 3, 4, 3, 2, 1], ![1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1])]

@[expose] def oddDerivE7XPerp : List (Fin Tag.E7.rank → ℤ) :=
  [![0, -1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0]]

theorem oddDerivE7X_check :
    oddDerivCheck .E7 10 oddDerivE7XFrame (oddDerivE7XDeriv.map Prod.fst) oddDerivE7XPerp
      oddDerivE7XDeriv = true := by
  decide +kernel

theorem e7ASFrame_sub_oddDeriv :
    (∀ σ ∈ e7ASFrame 0, σ ∈ oddDerivE7XDeriv.map Prod.fst) ∧
      (∀ σ ∈ e7ASFrame 1, σ ∈ oddDerivE7YDeriv.map Prod.fst) ∧
      ∀ σ ∈ e7ASFrame 2, σ ∈ oddDerivE7ZDeriv.map Prod.fst := by
  decide +kernel

variable {K : Type} [Field K]

theorem rootSpan_le_closure_odd_E7_x [Finite K] [CharP K 2] {t : adjointGroup .E7 K}
    (ht : (t : ModGL .E7 K) = (oddDerivE7XFrame.map fun σ => pinnedX .E7 K σ 1).prod) :
    ∀ x : adjointGroup .E7 K,
      (x : ModGL .E7 K) ∈ rootSpan .E7 K {γ | γ ∈ oddDerivE7XDeriv.map Prod.fst} →
        x ∈ closure {c : adjointGroup .E7 K | c * t = t * c ∧ Odd (orderOf c)} := by
  have h := oddDerivE7X_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  exact rootSpan_le_closure_odd_of_oddDerivFrame _ _ ht h.1.1.1 (oddDeriv_cov_map_fst _) h.1.2

theorem heightSeries_le_closure_odd_E7_x [Finite K] [CharP K 2] {t : adjointGroup .E7 K}
    (ht : (t : ModGL .E7 K) = (oddDerivE7XFrame.map fun σ => pinnedX .E7 K σ 1).prod) :
    ∀ x : adjointGroup .E7 K, (x : ModGL .E7 K) ∈ heightSeries .E7 K 10 →
      x ∈ closure {c : adjointGroup .E7 K | c * t = t * c ∧ Odd (orderOf c)} :=
  heightSeries_le_closure_odd_of_oddDerivCheck _ _ ht oddDerivE7X_check

theorem coe_e7ASRep_mem_rootSpan {S : Set (Fin Tag.E7.rank → ℤ)} {k : Fin 5}
    (hS : ∀ β ∈ e7ASFrame k, β ∈ S) : (e7ASRep K k : ModGL .E7 K) ∈ rootSpan .E7 K S :=
  list_prod_mem fun x hx => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan (hS σ hσ) 1

theorem e7ASRep_mem_closure_odd [Finite K] [CharP K 2] (k : Fin 5) (hk : k.val ≤ 2) :
    e7ASRep K k ∈ closure {c : adjointGroup .E7 K |
      c ∈ centralizer ({e7ASRep K k} : Set (adjointGroup .E7 K)) ∧ Odd (orderOf c)} := by
  rw [setOf_mem_centralizer_odd_eq]
  obtain ⟨h0, h1, h2⟩ := e7ASFrame_sub_oddDeriv
  match k, hk with
  | 0, _ => exact rootSpan_le_closure_odd_E7_x (coe_e7ASRep 0) _ (coe_e7ASRep_mem_rootSpan h0)
  | 1, _ => exact rootSpan_le_closure_odd_E7_y (coe_e7ASRep 1) _ (coe_e7ASRep_mem_rootSpan h1)
  | 2, _ => exact rootSpan_le_closure_odd_E7_z (coe_e7ASRep 2) _ (coe_e7ASRep_mem_rootSpan h2)

theorem e7Rep_mem_closure_odd [Finite K] [CharP K 2] (k : Fin 5) (hk : k.val ≤ 2) :
    e7Rep K k ∈ closure {c : adjointGroup .E7 K |
      c ∈ centralizer ({e7Rep K k} : Set (adjointGroup .E7 K)) ∧ Odd (orderOf c)} := by
  rw [← e7RepConj_mul_e7ASRep_mul_inv k]
  exact conj_mem_closure_odd_centralizer _ (e7ASRep_mem_closure_odd k hk)

theorem exists_conj_eq_e7Rep_of_map_not_mem_closure_odd [Finite K] [CharP K 2] {G : Type*}
    [Group G] (φ : adjointGroup .E7 K →* G) (hφ : Function.Injective φ)
    {y : adjointGroup .E7 K} (hy2 : orderOf y = 2)
    (hy : φ y ∉ closure {x : G | x ∈ φ.range ⊓ centralizer ({φ y} : Set G) ∧ Odd (orderOf x)}) :
    ∃ (k : Fin 5) (c : adjointGroup .E7 K), 3 ≤ k.val ∧ c * y * c⁻¹ = e7Rep K k := by
  obtain ⟨k, c, hc⟩ := exists_conj_eq_e7Rep hy2
  refine ⟨k, c, ?_, hc⟩
  by_contra hk
  apply hy
  set ψ : adjointGroup .E7 K →* G := φ.comp (MulAut.conj c⁻¹).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := hφ.comp (MulAut.conj c⁻¹).injective
  have hconj : MulAut.conj c⁻¹ (e7Rep K k) = y := by
    rw [← hc, MulAut.conj_apply, inv_inv]
    group
  have hψk : ψ (e7Rep K k) = φ y := by
    change φ (MulAut.conj c⁻¹ (e7Rep K k)) = φ y
    rw [hconj]
  have h := map_mem_closure_odd_centralizer ψ hψinj (e7Rep_mem_closure_odd k (by omega))
  rw [hψk] at h
  refine Subgroup.closure_mono ?_ h
  intro x hx
  refine ⟨Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hx.1).2⟩, hx.2⟩
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 (Subgroup.mem_inf.1 hx.1).1
  exact ⟨MulAut.conj c⁻¹ a, rfl⟩

end CFSG.SeitzReduction.E7Pilot

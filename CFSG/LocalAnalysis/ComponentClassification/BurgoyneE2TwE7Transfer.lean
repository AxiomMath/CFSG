module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Torus
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {T G : Type} [Group T] [Group G]

theorem conj_mem_comap_iff {Ψ : T →* G} {X : Subgroup G} {c : T}
    (h1 : ∀ w ∈ X, Ψ c * w * (Ψ c)⁻¹ ∈ X) (h2 : ∀ w ∈ X, Ψ c⁻¹ * w * (Ψ c⁻¹)⁻¹ ∈ X) (s : T) :
    c * s * c⁻¹ ∈ X.comap Ψ ↔ s ∈ X.comap Ψ := by
  rw [mem_comap, mem_comap]
  constructor
  · intro hs
    have h := h2 _ hs
    have e : Ψ c⁻¹ * Ψ (c * s * c⁻¹) * (Ψ c⁻¹)⁻¹ = Ψ s := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rwa [e] at h
  · intro hs
    rw [map_mul, map_mul, map_inv]
    exact h1 _ hs

theorem orderOf_neg_one_SL {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    orderOf (-1 : SL(2, K)) = 2 := by
  have h1 : (-1 : SL(2, K)) ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 this
  exact orderOf_eq_prime (by rw [neg_one_sq]) h1

theorem burgTorusFor_of_frame (hZ : center T = ⊥) {α : MulAut T} (hα : orderOf α = 2)
    {Ψ : T →* G} (hΨ : Function.Injective Ψ) {C' S' : Subgroup G} (hC'Ψ : C' ≤ Ψ.range)
    (hS'Ψ : S' ≤ Ψ.range) (hqC' : IsQuasisimple C') {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hqK : IsQuasisimple (SL(2, K))) (e : SL(2, K) ≃* S')
    (hC'fix : ∀ c, Ψ c ∈ C' → α c = c)
    (hC'norm : ∀ c, α c = c → ∀ w ∈ C', Ψ c * w * (Ψ c)⁻¹ ∈ C')
    (hS'norm : ∀ c, Ψ c * (e (-1) : G) = (e (-1) : G) * Ψ c → ∀ w ∈ S', Ψ c * w * (Ψ c)⁻¹ ∈ S')
    {x' : G} (hx' : ∀ s, Ψ (α s) = x' * Ψ s * x'⁻¹) (hx'S : ∀ w ∈ S', x' * w * x'⁻¹ ∈ S')
    (hx'ne : ∃ w ∈ S', x' * w * x'⁻¹ ≠ w)
    (hinner : ∀ β : MulAut T, Odd (orderOf β) → (∀ q, Ψ q ∈ C' → β q = q) →
      β ∈ (MulAut.conj : T →* MulAut T).range)
    (hcent : ∀ c, α c = c → (∀ q, Ψ q ∈ C' → c * q = q * c) →
      (∀ w ∈ S', Ψ c * w * (Ψ c)⁻¹ ∈ S') ∧ ((∀ w ∈ S', Ψ c * w = w * Ψ c) → c = 1)) :
    BurgTorusFor α := by
  classical
  set Q := C'.comap Ψ with hQ
  set S := S'.comap Ψ with hS
  let eQ : Q ≃* C' := (Q.equivMapOfInjective Ψ hΨ).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hC'Ψ))
  let eS : S ≃* S' := (S.equivMapOfInjective Ψ hΨ).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hS'Ψ))
  have heS : ∀ s : S, ((eS s : S') : G) = Ψ s := fun s => rfl
  let eK : S ≃* SL(2, K) := eS.trans e.symm
  set uS : S := eS.symm (e (-1)) with huS
  have hΨu : Ψ (uS : T) = (e (-1) : G) := by
    rw [← heS, huS, MulEquiv.apply_symm_apply]
  have heKu : eK uS = -1 := by
    change e.symm (eS (eS.symm (e (-1)))) = -1
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hcenter : (center S).map S.subtype = zpowers (uS : T) := by
    have he' : ((eK uS : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
      rw [heKu]
      simp
    rw [Proj.center_eq_zpowers_of_sl eK he', MonoidHom.map_zpowers]
    rfl
  have hα2 : ∀ s, α (α s) = s := by
    intro s
    have h2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have := congrArg (fun φ : MulAut T => φ s) h2
    simpa [sq] using this
  have hαS : ∀ s, s ∈ S → α s ∈ S := fun s hs => by
    change Ψ (α s) ∈ S'
    rw [hx']
    exact hx'S _ hs
  obtain ⟨p', n', hp', hp'2, hn', ⟨eGF⟩⟩ := PSL.exists_sl_galoisField (K := K) hK2
  refine ⟨Q, LocalCores.isQuasisimple_of_mulEquiv eQ.symm hqC', fun c hc => hC'fix c hc,
    fun c hc => ?_, uS, S, ?_, LocalCores.isQuasisimple_of_mulEquiv eK.symm hqK, ?_, ?_,
    ⟨p', n', hp', hp'2, hn', ⟨eK.trans eGF⟩⟩, hcenter, fun s => ⟨fun h => ?_, hαS s⟩, ?_, ?_⟩
  ·
    have hc' : α c = c := hc
    rw [mem_normalizer_iff]
    intro q
    exact (conj_mem_comap_iff (hC'norm c hc') (hC'norm c⁻¹ (by rw [map_inv, hc'])) q).symm
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq eK, heKu]
    exact orderOf_neg_one_SL hK2
  · intro s hs
    rw [mem_centralizer_singleton_iff]
    have hz : (uS : T) ∈ (center S).map S.subtype := by
      rw [hcenter]
      exact mem_zpowers _
    obtain ⟨z, hz, hzeq⟩ := hz
    have := (mem_center_iff.1 hz) ⟨s, hs⟩
    rw [← hzeq]
    exact congrArg Subtype.val this
  · intro c hc
    have hcu : c * uS = uS * c := mem_centralizer_singleton_iff.1 hc
    have hcu' : c⁻¹ * uS = uS * c⁻¹ := mem_centralizer_singleton_iff.1 (inv_mem hc)
    have h1 := hS'norm c (by rw [← hΨu, ← map_mul, hcu, map_mul])
    have h2 := hS'norm c⁻¹ (by rw [← hΨu, ← map_mul, hcu', map_mul])
    rw [mem_normalizer_iff]
    intro s
    exact (conj_mem_comap_iff h1 h2 s).symm
  · have := hαS _ h
    rwa [hα2] at this
  · obtain ⟨w, hw, hne⟩ := hx'ne
    obtain ⟨s, rfl⟩ := hS'Ψ hw
    refine ⟨s, hw, fun h => hne ?_⟩
    rw [← hx', h]
  · intro β hβ hcomm hfixQ
    obtain ⟨c, rfl⟩ := hinner β hβ fun q hq => hfixQ q hq
    have hcα : α c = c := apply_eq_of_commute_conj hZ hcomm
    have hcQ : ∀ q, Ψ q ∈ C' → c * q = q * c := fun q hq => by
      have h := hfixQ q hq
      rw [MulAut.conj_apply] at h
      calc c * q = c * q * c⁻¹ * c := by group
        _ = q * c := by rw [h]
    have hcQ' : ∀ q, Ψ q ∈ C' → c⁻¹ * q = q * c⁻¹ := fun q hq => by
      calc c⁻¹ * q = c⁻¹ * (q * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * q) * c⁻¹ := by rw [hcQ q hq]
        _ = q * c⁻¹ := by group
    obtain ⟨h1, h1'⟩ := hcent c hcα hcQ
    obtain ⟨h2, -⟩ := hcent c⁻¹ (by rw [map_inv, hcα]) hcQ'
    refine ⟨fun s => ?_, fun hfixS => ?_⟩
    · rw [MulAut.conj_apply]
      exact conj_mem_comap_iff h1 h2 s
    · have hc1 : c = 1 := h1' fun w hw => by
        obtain ⟨s, rfl⟩ := hS'Ψ hw
        have h := hfixS s hw
        rw [MulAut.conj_apply] at h
        rw [← map_mul, ← map_mul]
        congr 1
        calc c * s = c * s * c⁻¹ * c := by group
          _ = s * c := by rw [h]
      rw [hc1, map_one]

end CFSG.ComponentClassification.Burgoyne.E2.TwE7

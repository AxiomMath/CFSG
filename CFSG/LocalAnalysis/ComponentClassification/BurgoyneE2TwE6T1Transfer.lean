module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Transfer

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Burgoyne.E2.TwE7 (conj_mem_comap_iff orderOf_neg_one_SL)
open scoped MatrixGroups

variable {T G : Type} [Group T] [Group G]

theorem burgTorusFor_of_frame_induced {α : MulAut T} {Ψ : T →* G} (hΨ : Function.Injective Ψ)
    {C' S' : Subgroup G} (hC'Ψ : C' ≤ Ψ.range) (hS'Ψ : S' ≤ Ψ.range) (hqC' : IsQuasisimple C')
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (hqK : IsQuasisimple (SL(2, K)))
    (e : SL(2, K) ≃* S') (hC'fix : ∀ c, Ψ c ∈ C' → α c = c)
    (hC'norm : ∀ c, α c = c → ∀ w ∈ C', Ψ c * w * (Ψ c)⁻¹ ∈ C')
    (hS'norm : ∀ c, Ψ c * (e (-1) : G) = (e (-1) : G) * Ψ c → ∀ w ∈ S', Ψ c * w * (Ψ c)⁻¹ ∈ S')
    {x' : G} (hx' : ∀ s, Ψ (α s) = x' * Ψ s * x'⁻¹) (hx'S : ∀ w ∈ S', x' * w * x'⁻¹ ∈ S')
    (hx'S' : ∀ w ∈ S', x'⁻¹ * w * x' ∈ S') (hx'ne : ∃ w ∈ S', x' * w * x'⁻¹ ≠ w)
    (hind : ∀ β : MulAut T, Odd (orderOf β) → α * β = β * α → (∀ q, Ψ q ∈ C' → β q = q) →
      ∃ z : G, (∀ s, Ψ (β s) = z * Ψ s * z⁻¹) ∧ (∀ w ∈ S', z * w * z⁻¹ ∈ S') ∧
        (∀ w ∈ S', z⁻¹ * w * z ∈ S') ∧ ((∀ w ∈ S', z * w = w * z) → ∀ s, β s = s)) :
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
  obtain ⟨p', n', hp', hp'2, hn', ⟨eGF⟩⟩ := PSL.exists_sl_galoisField (K := K) hK2
  refine ⟨Q, LocalCores.isQuasisimple_of_mulEquiv eQ.symm hqC', fun c hc => hC'fix c hc,
    fun c hc => ?_, uS, S, ?_, LocalCores.isQuasisimple_of_mulEquiv eK.symm hqK, ?_, ?_,
    ⟨p', n', hp', hp'2, hn', ⟨eK.trans eGF⟩⟩, hcenter, fun s => ⟨fun h => ?_, fun h => ?_⟩, ?_,
    ?_⟩
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
  ·
    change Ψ s ∈ S'
    have h1 := hx'S' _ h
    rwa [hx', show x'⁻¹ * (x' * Ψ s * x'⁻¹) * x' = Ψ s by group] at h1
  · change Ψ (α s) ∈ S'
    rw [hx']
    exact hx'S _ h
  · obtain ⟨w, hw, hne⟩ := hx'ne
    obtain ⟨s, rfl⟩ := hS'Ψ hw
    refine ⟨s, hw, fun h => hne ?_⟩
    rw [← hx', h]
  · intro β hβ hcomm hfixQ
    obtain ⟨z, hz, hzS, hzS', hz1⟩ := hind β hβ hcomm fun q hq => hfixQ q hq
    refine ⟨fun s => ⟨fun h => ?_, fun h => ?_⟩, fun hfixS => ?_⟩
    · change Ψ s ∈ S'
      have h1 := hzS' _ (show Ψ (β s) ∈ S' from h)
      rwa [hz, show z⁻¹ * (z * Ψ s * z⁻¹) * z = Ψ s by group] at h1
    · change Ψ (β s) ∈ S'
      rw [hz]
      exact hzS _ h
    · have hβ1 : ∀ s, β s = s := hz1 fun w hw => by
        obtain ⟨s, rfl⟩ := hS'Ψ hw
        have h := congrArg Ψ (hfixS s hw)
        rw [hz] at h
        calc z * Ψ s = z * Ψ s * z⁻¹ * z := by group
          _ = Ψ s * z := by rw [h]
      exact MulEquiv.ext hβ1

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

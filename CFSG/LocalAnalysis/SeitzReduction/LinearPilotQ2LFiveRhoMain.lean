module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoSection
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveQuaMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Fischer
open scoped Pointwise

@[expose] noncomputable def rhoInvT :
    SpecialLinearGroup (Fin 4) F4 →* SpecialLinearGroup (Fin 4) F4 where
  toFun A := SpecialLinearGroup.transpose A⁻¹
  map_one' := by
    ext i j
    simp [SpecialLinearGroup.coe_transpose, Matrix.one_apply, eq_comm]
  map_mul' A B := Subtype.ext (by
    change ((↑((A * B)⁻¹) : Matrix (Fin 4) (Fin 4) F4))ᵀ =
      (↑(A⁻¹) : Matrix (Fin 4) (Fin 4) F4)ᵀ * (↑(B⁻¹) : Matrix (Fin 4) (Fin 4) F4)ᵀ
    rw [_root_.mul_inv_rev]
    change ((↑(B⁻¹) : Matrix (Fin 4) (Fin 4) F4) * (↑(A⁻¹) : Matrix (Fin 4) (Fin 4) F4))ᵀ = _
    rw [transpose_mul])

theorem coe_rhoInvT (A : SpecialLinearGroup (Fin 4) F4) :
    ((rhoInvT A : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      ((A⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)ᵀ :=
  SpecialLinearGroup.coe_transpose _

theorem rhoInvT_rhoInvT (A : SpecialLinearGroup (Fin 4) F4) : rhoInvT (rhoInvT A) = A := by
  ext i j
  rw [coe_rhoInvT, ← map_inv, coe_rhoInvT, inv_inv, transpose_transpose]

theorem rhoInvT_veeFrob (A : SpecialLinearGroup (Fin 4) F4) :
    rhoInvT (veeFrob A) = veeFrob (rhoInvT A) := by
  ext i j
  rw [coe_rhoInvT, ← map_inv, coe_veeFrob_eq_map, coe_veeFrob_eq_map, coe_rhoInvT,
    transpose_map]

section Coordinates

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {t y : G} (ht2 : t * t = 1) (hy : y ∈ zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hsq : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  have hk : t ^ k = t ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [_root_.zpow_add, _root_.zpow_mul, hsq, _root_.one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, _root_.zpow_zero]
  · right
    rw [hk, h, _root_.zpow_one]

@[expose] noncomputable def rhoExtOfCoordinates {N W : Subgroup G} {t : G}
    (ψ : N →* SpecialLinearGroup (Fin 4) F4) (β : W → Fin 4 → F4)
    (hψs : Function.Surjective ψ) (hψk : ∀ n, ψ n = 1 ↔ (n : G) ∈ W)
    (hψt : ∀ n m : N, (m : G) = t * n * t⁻¹ → ψ m = veeFrob (ψ n))
    (hβb : Function.Bijective β) (hβadd : ∀ v w : W, β (v * w) = β v + β w)
    (hnat : ∀ (n : N) (w v : W), (v : G) = n * w * n⁻¹ →
      β v = (ψ n : Matrix (Fin 4) (Fin 4) F4) *ᵥ β w)
    (hWN : W ≤ N) (ht2 : t * t = 1) (htN : t ∈ normalizer (N : Set G)) : RhoExt N where
  π := ψ
  surj := hψs
  β := fun k => β ⟨((k : N) : G), (hψk k).1 k.2⟩
  bij := by
    refine ⟨fun k k' h => ?_, fun v => ?_⟩
    · have h1 := congrArg Subtype.val (hβb.1 h)
      exact Subtype.ext (Subtype.ext h1)
    · obtain ⟨w, hw⟩ := hβb.2 v
      exact ⟨⟨⟨(w : G), hWN w.2⟩, (hψk _).2 w.2⟩, hw⟩
  β_mul := fun v w => hβadd ⟨((v : N) : G), (hψk v).1 v.2⟩ ⟨((w : N) : G), (hψk w).1 w.2⟩
  conj := fun e w v h => hnat e ⟨((w : N) : G), (hψk w).1 w.2⟩ ⟨((v : N) : G), (hψk v).1 v.2⟩
    (by
      have h1 := congrArg Subtype.val h
      simpa using h1)
  τ :=
    { toFun := fun n => ⟨t * n * t⁻¹, (mem_normalizer_iff.1 htN n).1 n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  τ_τ := fun e => Subtype.ext (by
    change t * (t * (e : G) * t⁻¹) * t⁻¹ = e
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    calc t * (t * (e : G) * t⁻¹) * t⁻¹ = (t * t) * e * (t⁻¹ * t⁻¹) := by group
      _ = e := by rw [ht2, hti, ht2, one_mul, mul_one])
  π_τ := fun e => hψt e _ rfl

theorem exists_complement_of_coordinates {N W : Subgroup G} {t : G}
    (ψ : N →* SpecialLinearGroup (Fin 4) F4) (β : W → Fin 4 → F4)
    (hψs : Function.Surjective ψ) (hψk : ∀ n, ψ n = 1 ↔ (n : G) ∈ W)
    (hψt : ∀ n m : N, (m : G) = t * n * t⁻¹ → ψ m = veeFrob (ψ n))
    (hβb : Function.Bijective β) (hβadd : ∀ v w : W, β (v * w) = β v + β w)
    (hnat : ∀ (n : N) (w v : W), (v : G) = n * w * n⁻¹ →
      β v = (ψ n : Matrix (Fin 4) (Fin 4) F4) *ᵥ β w)
    (hWN : W ≤ N) (ht2 : t * t = 1) (htN : t ∈ normalizer (N : Set G)) (htn : t ∉ N) :
    ∃ D : Subgroup G, W ⊓ D = ⊥ ∧ W ⊔ D = N ⊔ zpowers t := by
  set X := rhoExtOfCoordinates ψ β hψs hψk hψt hβb hβadd hnat hWN ht2 htN with hX
  obtain ⟨C, hCk, hCs, hCτ⟩ := X.exists_complement
  have hCk' : C ⊓ ψ.ker = ⊥ := hCk
  have hCs' : C ⊔ ψ.ker = ⊤ := hCs
  have hτ : ∀ c ∈ C, (⟨t * c * t⁻¹, (mem_normalizer_iff.1 htN c).1 c.2⟩ : N) ∈ C := hCτ
  set C' := C.map N.subtype with hC'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hfwd : ∀ x ∈ C', t * x * t⁻¹ ∈ C' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, hτ c hc, rfl⟩
  have htC : t ∈ normalizer (C' : Set G) := by
    refine mem_normalizer_iff.2 fun x => ⟨hfwd x, fun hx => ?_⟩
    have h1 := hfwd _ hx
    have h2 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
        _ = x := by rw [ht2, hti, ht2, one_mul, mul_one]
    rwa [h2] at h1
  have hC'N : C' ≤ N := Subgroup.map_subtype_le C
  have hWC : W ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hxW, ⟨c, hc, rfl⟩⟩
    have hck : c ∈ C ⊓ ψ.ker := ⟨hc, (hψk c).2 hxW⟩
    rw [hCk', Subgroup.mem_bot] at hck
    rw [hck, map_one]
    exact one_mem _
  have hWsC : W ⊔ C' = N := by
    refine le_antisymm (sup_le hWN hC'N) fun n hn => ?_
    have h1 : (⟨n, hn⟩ : N) ∈ C ⊔ ψ.ker := by
      rw [hCs']
      exact mem_top _
    have h2 : n ∈ (C ⊔ ψ.ker).map N.subtype := ⟨_, h1, rfl⟩
    rw [Subgroup.map_sup] at h2
    refine (sup_le le_sup_right ?_ : C' ⊔ ψ.ker.map N.subtype ≤ W ⊔ C') h2
    rintro _ ⟨k, hk, rfl⟩
    exact mem_sup_left ((hψk k).1 hk)
  refine ⟨C' ⊔ zpowers t, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxW, hxD⟩
    have hDset : ((C' ⊔ zpowers t : Subgroup G) : Set G) = (C' : Set G) * (zpowers t : Set G) :=
      coe_mul_of_right_le_normalizer_left C' (zpowers t) (zpowers_le.2 htC)
    have hxD' : x ∈ ((C' ⊔ zpowers t : Subgroup G) : Set G) := hxD
    rw [hDset] at hxD'
    obtain ⟨c, hc, y, hy, rfl⟩ := hxD'
    rcases eq_one_or_eq_of_mem_zpowers ht2 hy with rfl | rfl
    · simp only [mul_one] at hxW ⊢
      have : c ∈ W ⊓ C' := ⟨hxW, hc⟩
      rwa [hWC] at this
    · exfalso
      apply htn
      have h1 : c * y ∈ N := hWN hxW
      have h2 : y = c⁻¹ * (c * y) := by group
      rw [h2]
      exact mul_mem (inv_mem (hC'N hc)) h1
  · rw [← sup_assoc, hWsC]

end Coordinates

theorem lFiveFieldTildeSplitInput_holds :
    LFiveFieldTildeSplitInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield
  obtain ⟨ψ, β, hψs, hψk, hψt, hβb, hβadd, hnat, -⟩ :=
    exists_wOne_coordinates hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  obtain ⟨hWN, htn, htNt, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  rcases hnat with hnat | hdual
  · exact exists_complement_of_coordinates ψ β hψs hψk hψt hβb hβadd hnat hWN ht2 htNt htn
  · refine exists_complement_of_coordinates (rhoInvT.comp ψ) β ?_ ?_ ?_ hβb hβadd ?_ hWN ht2
      htNt htn
    · intro g
      obtain ⟨n, hn⟩ := hψs (rhoInvT g)
      exact ⟨n, by rw [MonoidHom.comp_apply, hn, rhoInvT_rhoInvT]⟩
    · intro n
      rw [MonoidHom.comp_apply, ← hψk n]
      constructor
      · intro h
        rw [← rhoInvT_rhoInvT (ψ n), h, map_one]
      · intro h
        rw [h, map_one]
    · intro n m h
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hψt n m h, rhoInvT_veeFrob]
    · intro n w v h
      rw [hdual n w v h, MonoidHom.comp_apply, coe_rhoInvT]

end CFSG.SeitzReduction.LinearPilot

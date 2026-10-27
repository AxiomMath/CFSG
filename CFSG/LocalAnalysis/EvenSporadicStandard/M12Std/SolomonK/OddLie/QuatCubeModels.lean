module

public import CFSG.GH74.Filter.ClassicalOdd.Unitary
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.Open CFSG.GH74.Filter.ClassicalOdd CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem ofSq_rho_eq_scalar {K : Type*} [Field K] (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) (g : QuaternionGroup 2) (c : K)
    (hg : (QuatRep.ofSq hK h).ρ g = scalar (Fin 2) c) :
    (g = 1 ∧ c = 1) ∨ (g = .a 2 ∧ c = -1) := by
  have key : ∀ g : QuaternionGroup 2, q8Frattini g = 1 → g = 1 ∨ g = .a 2 := by decide
  rcases key g ((QuatRep.ofSq hK h).scalar_eq g c hg).1 with rfl | rfl
  · refine Or.inl ⟨rfl, ?_⟩
    rw [map_one] at hg
    have := congrFun (congrFun hg 0) 0
    simpa [scalar_apply] using this.symm
  · refine Or.inr ⟨rfl, ?_⟩
    have hg' : ((quatHom h (.a 2) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) c := hg
    rw [quatHom_a_two] at hg'
    have := congrFun (congrFun hg' 0) 0
    simpa [scalar_apply] using this.symm

theorem quatCube_eq_of_scalar {K : Type*} [Field K] (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) {x y z : QuaternionGroup 2} {c : K}
    (hx : (QuatRep.ofSq hK h).ρ x = scalar (Fin 2) c)
    (hy : (QuatRep.ofSq hK h).ρ y = scalar (Fin 2) c)
    (hz : (QuatRep.ofSq hK h).ρ z = scalar (Fin 2) c) :
    (x, y, z) = 1 ∨ (x, y, z) = (.a 2, .a 2, .a 2) := by
  have hne : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hK
  rcases ofSq_rho_eq_scalar hK h x c hx with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;>
  rcases ofSq_rho_eq_scalar hK h y c hy with ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ <;>
  rcases ofSq_rho_eq_scalar hK h z c hz with ⟨rfl, hc''⟩ | ⟨rfl, hc''⟩
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; apply hne
       first
        | exact hc'.symm.trans hc
        | exact hc.symm.trans hc'
        | exact hc''.symm.trans hc
        | exact hc.symm.trans hc''
        | exact hc''.symm.trans hc'
        | exact hc'.symm.trans hc'')

theorem exists_quatCube_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)}
    (α : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* GL ι K) (hα : ∀ k, α k ∈ H)
    (hscal : ∀ (k : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2) (c : K),
      (α k : Matrix ι ι K) = scalar ι c → k = 1 ∨ k = (.a 2, .a 2, .a 2)) :
    ∃ φ : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* StatedProj H,
      ∀ k, φ k = 1 → k = 1 ∨ k = (.a 2, .a 2, .a 2) := by
  refine ⟨(QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp (α.codRestrict H hα),
    fun k hk => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hk
  obtain ⟨c, hc⟩ := hk
  refine hscal k (c : K) ?_
  rw [← GeneralLinearGroup.coe_scalar, hc]
  rfl

@[expose] def cubeToPi (n : ℕ) :
    QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* (Fin n → QuaternionGroup 2) where
  toFun k i := if i.val = 0 then k.1 else if i.val = 1 then k.2.1 else if i.val = 2 then k.2.2
    else 1
  map_one' := by
    funext i
    simp only [Prod.fst_one, Prod.snd_one, Pi.one_apply]
    split_ifs <;> rfl
  map_mul' k l := by
    funext i
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
    split_ifs <;> simp

theorem quatCube_PSL {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2) (hn : 6 ≤ n)
    (hm : StatedClassicalModel G .PSL n p f) :
    ∃ φ : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* G,
      ∀ k, φ k = 1 → k = 1 ∨ k = (.a 2, .a 2, .a 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + (2 + (2 + m)) := ⟨n - 6, by omega⟩
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hK2).1
  obtain ⟨φ, hφ⟩ := exists_quatCube_statedProj (H := StatedSL (2 + (2 + (2 + m))) K)
    (alpha6 (QuatRep.ofSq hK2 hab).ρ m).toHomUnits
    (fun k => Subgroup.subset_closure (det_alpha6 (QuatRep.ofSq hK2 hab).det_eq m k))
    (fun k c h => by
      have h' : alpha6 (QuatRep.ofSq hK2 hab).ρ m k = scalar _ c := h
      rw [alpha6_apply] at h'
      obtain ⟨h1, h23⟩ := eq_scalar_of_diagBlock_eq h'
      obtain ⟨h2, h3m⟩ := eq_scalar_of_diagBlock_eq h23
      obtain ⟨h3, -⟩ := eq_scalar_of_diagBlock_eq h3m
      exact quatCube_eq_of_scalar hK2 hab h1 h2 h3)
  exact ⟨e.symm.toMonoidHom.comp φ, fun k hk => hφ k (e.symm.map_eq_one_iff.1 hk)⟩

theorem quatCube_PSU {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2) (hn : 6 ≤ n)
    (hm : StatedClassicalModel G .PSU n p f) :
    ∃ φ : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* G,
      ∀ k, φ k = 1 → k = 1 ∨ k = (.a 2, .a 2, .a 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + (2 + (2 + m)) := ⟨n - 6, by omega⟩
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hK
  have hσ : ∀ x, iterateFrobenius K p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius K p f) ((QuatRep.ofSq hK2 hab).ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  have hfun : (fun x : K => x ^ (p ^ f)) = iterateFrobenius K p f :=
    funext fun x => (hσ x).symm
  obtain ⟨φ, hφ⟩ := exists_quatCube_statedProj (H := StatedSU (2 + (2 + (2 + m))) (p ^ f) K)
    (alpha6 (QuatRep.ofSq hK2 hab).ρ m).toHomUnits
    (fun k => by
      refine Subgroup.subset_closure ⟨det_alpha6 (QuatRep.ofSq hK2 hab).det_eq m k, ?_⟩
      change ((alpha6 (QuatRep.ofSq hK2 hab).ρ m k).map (fun x => x ^ (p ^ f)))ᵀ *
        alpha6 (QuatRep.ofSq hK2 hab).ρ m k = 1
      rw [hfun]
      exact isUni_alpha6 hQ m k)
    (fun k c h => by
      have h' : alpha6 (QuatRep.ofSq hK2 hab).ρ m k = scalar _ c := h
      rw [alpha6_apply] at h'
      obtain ⟨h1, h23⟩ := eq_scalar_of_diagBlock_eq h'
      obtain ⟨h2, h3m⟩ := eq_scalar_of_diagBlock_eq h23
      obtain ⟨h3, -⟩ := eq_scalar_of_diagBlock_eq h3m
      exact quatCube_eq_of_scalar hK2 hab h1 h2 h3)
  exact ⟨e.symm.toMonoidHom.comp φ, fun k hk => hφ k (e.symm.map_eq_one_iff.1 hk)⟩

theorem quatCube_PSp {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hm : StatedClassicalModel G .PSp n p f) :
    ∃ φ : QuaternionGroup 2 × QuaternionGroup 2 × QuaternionGroup 2 →* G,
      ∀ k, φ k = 1 → k = 1 ∨ k = (.a 2, .a 2, .a 2) := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hK2).1
  obtain ⟨φ, hφ⟩ := exists_quatCube_statedProj (H := StatedSp n K)
    ((alphaSp (QuatRep.ofSq hK2 hab).ρ (Fin n)).comp (cubeToPi n)).toHomUnits
    (fun k => Subgroup.subset_closure (planeDiag_symplectic _ fun i =>
      (QuatRep.ofSq hK2 hab).det_eq _))
    (fun k c h => by
      have h0 := planeDiag_eq_scalar (fun i => (QuatRep.ofSq hK2 hab).ρ (cubeToPi n k i)) c h
        ⟨0, by omega⟩
      have h1 := planeDiag_eq_scalar (fun i => (QuatRep.ofSq hK2 hab).ρ (cubeToPi n k i)) c h
        ⟨1, by omega⟩
      have h2 := planeDiag_eq_scalar (fun i => (QuatRep.ofSq hK2 hab).ρ (cubeToPi n k i)) c h
        ⟨2, by omega⟩
      simp only [cubeToPi, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1 h2
      simp at h0 h1 h2
      exact quatCube_eq_of_scalar hK2 hab h0 h1 h2)
  exact ⟨e.symm.toMonoidHom.comp φ, fun k hk => hφ k (e.symm.map_eq_one_iff.1 hk)⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphNormalUnitary

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Conj

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem map_conj_modelToG (e : L ≃* StatedSp n K) (π : Equiv.Perm (Fin n))
    (H : Subgroup (StatedSp n K)) :
    (modelToG e H).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      modelToG e (H.map (MulAut.conj (permSp K π)).toMonoidHom) := by
  rw [UnitaryPilot.modelToG, UnitaryPilot.modelToG, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem map_centralizer_mulAut_three (c : MulAut G) (Y : Subgroup G) :
    (centralizer (Y : Set G)).map c.toMonoidHom =
      centralizer ((Y.map c.toMonoidHom : Subgroup G) : Set G) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    change c y * c a = c a * c y
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 ha y hy]
  · intro hb
    refine ⟨c.symm b, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    apply c.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_centralizer_iff.1 hb (c y) ⟨y, hy, rfl⟩

variable [Finite G]

theorem map_centralizerPerfectCore_mulAut_three (c : MulAut G) (Y : Subgroup G) :
    (centralizerPerfectCore Y).map c.toMonoidHom =
      centralizerPerfectCore (Y.map c.toMonoidHom) := by
  rw [centralizerPerfectCore, centralizerPerfectCore, CFSG.Quasithin.map_perfectCore,
    map_centralizer_mulAut_three]

theorem map_conj_edgeCoreSp (e : L ≃* StatedSp n K) (π : Equiv.Perm (Fin n)) (k l : Fin n) :
    (edgeCoreSp e k l).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      edgeCoreSp e (π k) (π l) := by
  rw [edgeCoreSp, edgeCoreSp, map_centralizerPerfectCore_mulAut_three, Subgroup.map_sup,
    map_conj_modelToG, map_conj_modelToG, map_conj_permSp_rootTorusSp, map_conj_permSp_rootTorusSp]

theorem natCard_edgeCoreSp_perm (e : L ≃* StatedSp n K) (π : Equiv.Perm (Fin n)) (k l : Fin n) :
    Nat.card (edgeCoreSp e (π k) (π l)) = Nat.card (edgeCoreSp e k l) := by
  rw [← map_conj_edgeCoreSp e π k l]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem exists_perm_fin_three_zero_one {k l : Fin 3} (hkl : k ≠ l) :
    ∃ π : Equiv.Perm (Fin 3), π 0 = k ∧ π 1 = l := by
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1, by decide, by decide⟩
  · exact absurd rfl hkl
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2 * Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2, by decide, by decide⟩
  · exact absurd rfl hkl

theorem natCard_edgeCoreSp_eq_zero_one (e : L ≃* StatedSp 3 K) {k l : Fin 3} (hkl : k ≠ l) :
    Nat.card (edgeCoreSp e k l) = Nat.card (edgeCoreSp e 0 1) := by
  obtain ⟨π, rfl, rfl⟩ := exists_perm_fin_three_zero_one hkl
  exact natCard_edgeCoreSp_perm e π 0 1

end Conj

section Unitary

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def SpThreeUnitaryNormalized (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3)
    (b : Bool) : Prop :=
  ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
    (C₀ : GL (Fin (2 * 2)) K') (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G),
    Φ.range = neighbourCore e k ∧
    Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) ∧
    (∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (cond b (tauSp x) x))) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G)) ∧
    ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x)

theorem spThreeUnitaryNormalized_false_or_true
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryEven) :
    SpThreeUnitaryNormalized e t f k false ∨ SpThreeUnitaryNormalized e t f k true := by
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι, κ, Φ, hκ, hrange, hker, hN1, hN3⟩ :=
    exists_unitaryNeighbourParam_three hset hKc hf e htC ht k hk
  rcases hκ with rfl | rfl
  · exact Or.inl ⟨K', inferInstance, h, inferInstance, C₀, hC, hC₀, ι, Φ, hrange, hker,
      fun x => hN1 x, hN3⟩
  · exact Or.inr ⟨K', inferInstance, h, inferInstance, C₀, hC, hC₀, ι, Φ, hrange, hker,
      fun x => hN1 x, hN3⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_uTorus_eq_of_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {f : ℕ} {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (β : StatedSp 2 K →* StatedSp 2 K)
    (βk : StatedSp 2 h.fixedField →* StatedSp 2 h.fixedField)
    (hβ : ∀ κ : Kˣ, statedSpMap (ι : K →+* h.fixedField) 2 (β (rootTorusHom K 2 0 κ)) =
      βk (rootTorusHom h.fixedField 2 0 (Units.map (ι : K →+* h.fixedField) κ)))
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G)) :
    (((rootTorusSp h.fixedField 0).map βk).map (uModelSU h hC₀)).map (Φ.codRestrict _ hΦE) =
      (modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) := by
  have hval : ∀ κ : Kˣ, Φ (uModelSU h hC₀ (βk (rootTorusHom h.fixedField 2 0
      (Units.map (ι : K →+* h.fixedField) κ)))) =
        ((e.symm (rootTorusHom K 3 (k.succAbove 0) κ) : L) : G) := by
    intro κ
    rw [← hβ, hN1, coe_complSpEquiv_rootTorusHom]
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨μ, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rw [mem_subgroupOf]
    set κ : Kˣ := Units.map (ι.symm : h.fixedField →+* K) μ with hκ
    have hμ : Units.map (ι : K →+* h.fixedField) κ = μ := by
      ext
      simp [hκ]
    change Φ (uModelSU h hC₀ (βk (rootTorusHom h.fixedField 2 0 μ))) ∈ _
    rw [← hμ, hval]
    exact symm_mem_modelToG e (rootTorusHom_mem_rootTorusSp _ κ)
  · intro hy
    rw [mem_subgroupOf] at hy
    obtain ⟨x, hx, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    refine ⟨_, ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp 0 (Units.map (ι : K →+* h.fixedField) κ),
      rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ _ = (y : G)
    rw [hval, hxy]

end Unitary

section Edge

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem not_sq_dvd_natCard_edgeCoreSp_of_unitary_std {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3}
    (hn : SpThreeUnitaryNormalized e t f k false) :
    ¬ (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨K', _, h, _, C₀, -, hC₀, ι, Φ, hrange, hker, hN1, -⟩ := hn
  have : Finite K' := h.finite
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hkK : Nat.card h.fixedField = Nat.card K := (Nat.card_congr ι.toEquiv).symm
  have hk4 : 4 ≤ Nat.card h.fixedField := hkK ▸ hK4
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hTY := map_uTorus_eq_of_N1 e k h hC₀ ι (MonoidHom.id _) (MonoidHom.id _)
    (fun κ => statedSpMap_rootTorusHom (ι : K →+* h.fixedField) 0 κ) Φ hΦE (fun x => hN1 x)
  rw [Subgroup.map_id, ← hΦ'] at hTY
  have hQ := le_map_perfectCore_centralizer Φ' hΦ's hker' (uStdTorus h hC₀)
    (Q := perfectCore (centralizer (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf
      (neighbourCore e k) : Subgroup (neighbourCore e k)) : Set (neighbourCore e k))))
    (perfectCore_perfect _) (by rw [uStdTorus, hTY]; exact perfectCore_le _)
  have h1 := (Subgroup.card_dvd_of_le hQ).trans ((Subgroup.card_map_dvd _ _).trans
    (natCard_perfectCore_centralizer_uStdTorus_dvd h hC₀ hk4))
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hkK] at h1
  intro h2
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  exact not_sq_dvd_mul_sq_sub_one_mul hq2 (by omega) odd_one (by rw [mul_one]; exact h2.trans h1)

omit [Finite K] in
theorem sq_dvd_natCard_edgeCoreSp_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3}
    (hn : SpThreeUnitaryNormalized e t f k true) :
    (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨K', _, h, _, C₀, -, hC₀, ι, Φ, hrange, hker, hN1, -⟩ := hn
  have : Finite K' := h.finite
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hkK : Nat.card h.fixedField = Nat.card K := (Nat.card_congr ι.toEquiv).symm
  have hk4 : 4 ≤ Nat.card h.fixedField := hkK ▸ hK4
  have hK'4 : 4 ≤ Nat.card K' := hk4.trans (natCard_fixedField_le h)
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hker' : Φ'.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hTY := map_uTorus_eq_of_N1 e k h hC₀ ι tauSp tauSp
    (fun κ => statedSpMap_tauSp_rootTorusHom (ι : K →+* h.fixedField) 0 κ) Φ hΦE
    (fun x => hN1 x)
  rw [← hΦ'] at hTY
  have h1 : ((lambdaU h hC₀).range.map Φ') ≤ perfectCore (centralizer
      (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) :
        Subgroup (neighbourCore e k)) : Set (neighbourCore e k))) := by
    refine (Subgroup.map_mono
      (range_lambdaU_le_perfectCore_centralizer_uTwTorus h hC₀ hK'4)).trans ?_
    have h2 := map_perfectCore_centralizer_le Φ' (uTwTorus h hC₀)
    rw [uTwTorus, hTY] at h2
    exact h2
  have h3 := Subgroup.card_dvd_of_le h1
  rw [natCard_map_range_lambdaU h hC₀ Φ' hker',
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h3
  have hK' : Nat.card K' = (Nat.card K) ^ 2 := by
    rw [h.card, hKc, ← pow_mul, mul_comm]
  rw [hK'] at h3
  exact (dvd_mul_right _ _).trans h3

end Edge

end CFSG.SeitzReduction.SymplecticPilot

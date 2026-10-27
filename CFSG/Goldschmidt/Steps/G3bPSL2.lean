module

public import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalKleinFourIndexThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.Walter.Defs

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

section KleinFour

variable {G : Type*} [Group G] [Finite G]

theorem isKleinFour_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsKleinFour A) : IsKleinFour B :=
  ⟨(Nat.card_congr e.toEquiv).symm.trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans hA.exponent_two⟩

theorem exists_ne_one_ne_of_three_le_card' {H : Type*} [Group H] [Finite H]
    (h3 : 3 ≤ Nat.card H) : ∃ a b : H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have := Fintype.ofFinite H
  have : Nontrivial H := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  refine ⟨a, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset H) ⊆ {1, a} := by
    intro y _
    by_cases hy : y = 1
    · rw [Finset.mem_insert]
      exact Or.inl hy
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hcon y ha hy).symm
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_le_two (a := (1 : H)) (b := a)
  omega

omit [Finite G] in
theorem orderOf_eq_two_of_kleinFour {H : Subgroup G} (hH : IsKleinFour H) {x : G}
    (hx : x ∈ H) (hx1 : x ≠ 1) : orderOf x = 2 := by
  have : IsKleinFour H := hH
  have h := IsKleinFour.mul_self (⟨x, hx⟩ : H)
  exact orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val h) hx1

theorem exists_normalizer_moves {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    [IsMulCommutative (S : Subgroup G)] {x y : G} (hx : x ∈ (S : Subgroup G))
    (hy : y ∈ (S : Subgroup G)) (hxy : x ≠ y) (hconj : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ ≠ x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hy' : c⁻¹⁻¹ * x * c⁻¹ ∈ (S : Subgroup G) := by rwa [inv_inv, hc]
  obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x c⁻¹ hx hy'
  refine ⟨n⁻¹, Subgroup.inv_mem _ hn, fun h => hxy ?_⟩
  rw [inv_inv, hc] at hn'
  rw [inv_inv] at h
  rw [hn', h]

theorem index_normalizer_kleinFour (S : Sylow 2 G) (hS : IsKleinFour (S : Subgroup G))
    (hC : Subgroup.centralizer ((S : Subgroup G) : Set G) = S)
    (hmove : ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∃ x ∈ (S : Subgroup G),
      n * x * n⁻¹ ≠ x) :
    ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3 := by
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set φ := Sg.normalizerMonoidHom with hφ
  have hker : φ.ker = Sg.subgroupOf N := by rw [hφ, Subgroup.normalizerMonoidHom_ker, hC]
  have hidx : (Sg.subgroupOf N).index = Nat.card φ.range := by
    rw [← hker, Subgroup.index_ker]
  have h6 : Nat.card φ.range ∣ 6 := by
    have : IsKleinFour Sg := hS
    rw [← kleinFourAut_card Sg]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ (Sg.subgroupOf N).index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    obtain ⟨n, hn, x, hx, hnx⟩ := hmove
    have hmem : φ ⟨n, hn⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hmem
    exact hnx (congrArg (fun a : MulAut Sg => ((a ⟨x, hx⟩ : Sg) : G)) hmem)
  rw [hidx] at hodd ⊢
  have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases h : Nat.card φ.range <;> simp_all

theorem normalizer_mulEquiv_alternatingGroup_four (S : Sylow 2 G)
    (hS : IsKleinFour (S : Subgroup G))
    (hC : Subgroup.centralizer ((S : Subgroup G) : Set G) = S)
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    Nonempty (Subgroup.normalizer ((S : Subgroup G) : Set G) ≃* alternatingGroup (Fin 4)) := by
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  have hSN : Sg ≤ N := Subgroup.le_normalizer
  have : IsKleinFour Sg := hS
  have : IsMulCommutative Sg := IsKleinFour.isMulCommutative
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_ne_one_ne_of_three_le_card' (H := Sg) (by rw [hS.card_four]; norm_num)
  have hord : ∀ c : Sg, c ≠ 1 → orderOf (c : G) = 2 := fun c hc => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact IsKleinFour.mul_self c) hc
  have hmove := exists_normalizer_moves S a.2 b.2 (fun h => hab (Subtype.ext h))
    (hconj _ _ (hord a ha) (hord b hb))
  obtain ⟨n, hn, hna⟩ := hmove
  have hidx := index_normalizer_kleinFour S hS hC ⟨n, hn, a, a.2, hna⟩
  refine mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three (Sg.subgroupOf N)
    Subgroup.normal_in_normalizer
    (isKleinFour_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hSN).symm hS) ?_ hidx
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hxC : (x : G) ∈ Subgroup.centralizer (Sg : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (h ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.mpr hs))
    rwa [hC] at hxC
  · intro h s hs
    have hxC : (x : G) ∈ Subgroup.centralizer (Sg : Set G) := by rw [hC]; exact h
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC s (Subgroup.mem_subgroupOf.mp hs))

end KleinFour

theorem psl2_centralizer_kleinFour
    (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (V : Subgroup PSL(2, K)) (hV : IsKleinFour V) :
    Subgroup.centralizer (V : Set PSL(2, K)) = V := by
  apply le_antisymm
  · intro x hx
    let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
    have hinj : Function.Injective toPGL := fun _ _ h =>
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
    have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective V hV toPGL hinj
    have hxC : toPGL x ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 K)) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx v hv]
    rw [pgl2_kleinFour_centralizer_eq_self K hK _ hVP] at hxC
    obtain ⟨v, hv, hvx⟩ := hxC
    rwa [← hinj hvx]
  · have : IsMulCommutative V := IsKleinFour.isMulCommutative
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : V) ⟨x, hx⟩)

section FieldAut

variable {p f : ℕ} [Fact p.Prime]

theorem psl2FieldAut_mul_conj {K : Type*} [Field K] (σ : K ≃+* K) (g : PSL(2, K))
    (hg : psl2FieldAut K σ g = g) :
    psl2FieldAut K σ * MulAut.conj g = MulAut.conj g * psl2FieldAut K σ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hg]

theorem psl2_mulAut_fix_normalForm
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 PSL(2, GaloisField p f)) :
    ∃ (V0 : Subgroup PSL(2, GaloisField p f)) (k : PSL(2, GaloisField p f)),
      IsKleinFour V0 ∧
      (∀ x, x ∈ (S : Subgroup PSL(2, GaloisField p f)) ↔ k * x * k⁻¹ ∈ V0) ∧
      (∀ τ : GaloisField p f ≃+* GaloisField p f, ∀ v ∈ V0,
        psl2FieldAut (GaloisField p f) τ v = v) ∧
      (∃ y ∈ Subgroup.normalizer (V0 : Set PSL(2, GaloisField p f)), ∃ v ∈ V0,
        y * v * y⁻¹ ≠ v ∧
          ∀ τ : GaloisField p f ≃+* GaloisField p f, psl2FieldAut (GaloisField p f) τ y = y) ∧
      ∀ α : MulAut PSL(2, GaloisField p f),
        (∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x) →
        ∃ g0 ∈ V0, ∃ σ : GaloisField p f ≃+* GaloisField p f,
          MulAut.conj k * α * (MulAut.conj k)⁻¹ =
            MulAut.conj g0 * psl2FieldAut (GaloisField p f) σ := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK hp hf
  have hcard : 3 < Nat.card K := by omega
  have hp8 : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by
    rw [pow_one, ← pow_mod_eight_of_odd hp (odd_of_pow_mod_eight hp h8)]
    exact h8
  have hZ : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨P0⟩ : Nonempty (Sylow 2 PSL(2, ZMod p)) := inferInstance
  have hP0 := psl2_sylow_two_isKleinFour (ZMod p) hZ hp one_pos hp8 P0
  set ψ := psl2Map (algebraMap (ZMod p) K) with hψ
  set V0 := (P0 : Subgroup PSL(2, ZMod p)).map ψ with hV0def
  have hV0 : IsKleinFour V0 := isKleinFour_map_of_injective _ hP0 _ (psl2Map_injective _)
  have hV0fix : ∀ τ : K ≃+* K, ∀ v ∈ V0, psl2FieldAut K τ v = v := by
    rintro τ _ ⟨x, -, rfl⟩
    exact psl2FieldAut_psl2Map_zmod τ x
  have hScard : Nat.card (S : Subgroup PSL(2, K)) = 4 :=
    psl2_sylow_two_card_eq_four K hK hp hf h8 S
  let V0S : Sylow 2 PSL(2, K) :=
    Sylow.ofCard V0 (by rw [hV0.card_four, ← hScard, S.card_eq_multiplicity])
  have hV0S : (V0S : Subgroup PSL(2, K)) = V0 := Sylow.coe_ofCard _ _
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, K) S V0S
  have hmemS : ∀ x, x ∈ (S : Subgroup PSL(2, K)) ↔ k * x * k⁻¹ ∈ V0 := by
    intro x
    rw [← hV0S, ← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, MulAut.smul_def, MulAut.conj_apply]
    simp [mul_assoc]
  refine ⟨V0, k, hV0, hmemS, hV0fix, ?_, ?_⟩
  ·
    have : IsKleinFour (P0 : Subgroup PSL(2, ZMod p)) := hP0
    have : IsMulCommutative (P0 : Subgroup PSL(2, ZMod p)) := IsKleinFour.isMulCommutative
    obtain ⟨a, b, ha, hb, hab⟩ := exists_ne_one_ne_of_three_le_card'
      (H := (P0 : Subgroup PSL(2, ZMod p))) (by rw [hP0.card_four]; norm_num)
    have hord : ∀ c : (P0 : Subgroup PSL(2, ZMod p)), c ≠ 1 →
        orderOf (c : PSL(2, ZMod p)) = 2 := fun c hc => by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact IsKleinFour.mul_self c) hc
    obtain ⟨n, hn, hna⟩ := exists_normalizer_moves P0 a.2 b.2 (fun h => hab (Subtype.ext h))
      (psl2_isConj_of_orderOf_eq_two (ZMod p) hZ hp one_pos (hord a ha) (hord b hb))
    refine ⟨ψ n, Subgroup.le_normalizer_map ψ ⟨n, hn, rfl⟩, ψ a, ⟨a, a.2, rfl⟩, ?_,
      fun τ => psl2FieldAut_psl2Map_zmod τ n⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact fun h => hna (psl2Map_injective _ h)
  ·
    intro α hαS
    set α' := MulAut.conj k * α * (MulAut.conj k)⁻¹ with hα'
    have hα'V : ∀ v ∈ V0, α' v = v := by
      intro v hv
      have hv' : k⁻¹ * v * k ∈ (S : Subgroup PSL(2, K)) := by
        rw [hmemS]
        simpa [mul_assoc] using hv
      have h := hαS _ hv'
      change k * α ((MulAut.conj k)⁻¹ v) * k⁻¹ = v
      rw [← map_inv, MulAut.conj_apply, inv_inv, h]
      group
    obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hK hK' hcard α'
    set g := x.left
    set σ := x.right
    have hα'gσ : α' = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
      rw [← hx, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul, pGammaL2ToMulAutPSL2_inl,
        pGammaL2ToMulAutPSL2_inr]
    let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
    have htoPGL : Function.Injective toPGL := fun _ _ h =>
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
    have hVP : IsKleinFour (V0.map toPGL) := isKleinFour_map_of_injective V0 hV0 toPGL htoPGL
    have hgC : g ∈ Subgroup.centralizer ((V0.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
        have h := hα'V v hv
        rw [hα'gσ, MulAut.mul_apply, hV0fix σ v hv] at h
        exact h
      have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
      rw [h1] at h2
      calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
        _ = g * toPGL v := by group
    rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
    obtain ⟨g0, hg0V, hg0⟩ := hgC
    refine ⟨g0, hg0V, σ, ?_⟩
    rw [hα'gσ, ← hg0]
    exact congrArg (· * psl2FieldAut K σ) (pgl2InnerAutPSL2_toPGL K hK' hcard g0)

theorem psl2_mulAut_fix_props
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 PSL(2, GaloisField p f)) :
    (∀ α β : MulAut PSL(2, GaloisField p f),
      (∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x) →
      (∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), β x = x) → α * β = β * α) ∧
    (∃ Γ : Subgroup (MulAut PSL(2, GaloisField p f)), IsCyclic Γ ∧
      ∀ α : MulAut PSL(2, GaloisField p f), Odd (orderOf α) →
        (∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x) → α ∈ Γ) ∧
    (∃ y ∈ Subgroup.normalizer ((S : Subgroup PSL(2, GaloisField p f)) : Set _),
      ∃ v ∈ (S : Subgroup PSL(2, GaloisField p f)), y * v * y⁻¹ ≠ v ∧
        ∀ α : MulAut PSL(2, GaloisField p f), Odd (orderOf α) →
          (∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x) → α y = y) := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK hp hf
  have hcard : 3 < Nat.card K := by omega
  obtain ⟨V0, k, hV0, hmemS, hV0fix, ⟨y, hyN, v, hv, hyv, hyfix⟩, hnf⟩ :=
    psl2_mulAut_fix_normalForm hp hf h5 h8 S
  have : IsMulCommutative V0 := @IsKleinFour.isMulCommutative _ _ hV0
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hσcomm : ∀ σ τ : K ≃+* K, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.commGroup (α := K ≃+* K)).mul_comm σ τ
  have hodd : ∀ α : MulAut PSL(2, K), Odd (orderOf α) →
      (∀ x ∈ (S : Subgroup PSL(2, K)), α x = x) →
      ∃ σ : K ≃+* K, MulAut.conj k * α * (MulAut.conj k)⁻¹ = psl2FieldAut K σ := by
    intro α hαo hαS
    obtain ⟨g0, hg0V, σ, hα⟩ := hnf α hαS
    have hcomm : Commute (MulAut.conj g0) (psl2FieldAut K σ) :=
      (psl2FieldAut_mul_conj σ g0 (hV0fix σ g0 hg0V)).symm
    have hg02 : g0 ^ 2 = 1 := by
      have h := @IsKleinFour.mul_self _ _ hV0 ⟨g0, hg0V⟩
      rw [pow_two]
      exact congrArg Subtype.val h
    set n := orderOf α with hn
    have hg0n : g0 ^ n = g0 := by
      obtain ⟨j, hj⟩ := hαo
      rw [hj, pow_succ, pow_mul, hg02, one_pow, one_mul]
    have hpow : (MulAut.conj k * α * (MulAut.conj k)⁻¹) ^ n = 1 := by
      have : MulAut.conj k * α * (MulAut.conj k)⁻¹ = MulAut.conj (MulAut.conj k) α := rfl
      rw [this, ← map_pow, hn, pow_orderOf_eq_one, map_one]
    rw [hα, hcomm.mul_pow, ← map_pow, hg0n, ← map_pow] at hpow
    let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
    have htoPGL : Function.Injective toPGL := fun _ _ h =>
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
    have hinl : pGammaL2ToMulAutPSL2 K hK' hcard
        (SemidirectProduct.inl (toPGL g0) * SemidirectProduct.inr (σ ^ n)) =
        pGammaL2ToMulAutPSL2 K hK' hcard 1 := by
      rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
        pgl2InnerAutPSL2_toPGL, map_one]
      exact hpow
    have h1 := pGammaL2ToMulAutPSL2_injective K hK' hcard hinl
    have hleft := congrArg SemidirectProduct.left h1
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.one_left, map_one, mul_one] at hleft
    have hg01 : g0 = 1 := htoPGL (by rw [hleft, map_one])
    refine ⟨σ, ?_⟩
    rw [hα, hg01, map_one, one_mul]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro α β hαS hβS
    obtain ⟨g1, hg1V, σ1, hα⟩ := hnf α hαS
    obtain ⟨g2, hg2V, σ2, hβ⟩ := hnf β hβS
    have hg12 : g1 * g2 = g2 * g1 :=
      congrArg Subtype.val (mul_comm' (⟨g1, hg1V⟩ : V0) ⟨g2, hg2V⟩)
    have key : (MulAut.conj g1 * psl2FieldAut K σ1) * (MulAut.conj g2 * psl2FieldAut K σ2) =
        (MulAut.conj g2 * psl2FieldAut K σ2) * (MulAut.conj g1 * psl2FieldAut K σ1) := by
      calc (MulAut.conj g1 * psl2FieldAut K σ1) * (MulAut.conj g2 * psl2FieldAut K σ2)
          = MulAut.conj g1 * (psl2FieldAut K σ1 * MulAut.conj g2) * psl2FieldAut K σ2 := by
            simp only [mul_assoc]
        _ = MulAut.conj g1 * (MulAut.conj g2 * psl2FieldAut K σ1) * psl2FieldAut K σ2 := by
            rw [psl2FieldAut_mul_conj σ1 g2 (hV0fix σ1 g2 hg2V)]
        _ = MulAut.conj (g1 * g2) * psl2FieldAut K (σ1 * σ2) := by
            simp only [map_mul, mul_assoc]
        _ = MulAut.conj (g2 * g1) * psl2FieldAut K (σ2 * σ1) := by rw [hg12, hσcomm]
        _ = MulAut.conj g2 * (MulAut.conj g1 * psl2FieldAut K σ2) * psl2FieldAut K σ1 := by
            simp only [map_mul, mul_assoc]
        _ = MulAut.conj g2 * (psl2FieldAut K σ2 * MulAut.conj g1) * psl2FieldAut K σ1 := by
            rw [psl2FieldAut_mul_conj σ2 g1 (hV0fix σ2 g1 hg1V)]
        _ = (MulAut.conj g2 * psl2FieldAut K σ2) * (MulAut.conj g1 * psl2FieldAut K σ1) := by
            simp only [mul_assoc]
    rw [← hα, ← hβ] at key
    have h := congrArg (fun z => (MulAut.conj k)⁻¹ * z * MulAut.conj k) key
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
      mul_one, one_mul] using h
  ·
    refine ⟨(psl2FieldAut K).range.map (MulAut.conj (MulAut.conj k)⁻¹).toMonoidHom, ?_, ?_⟩
    · have : IsCyclic (psl2FieldAut K).range :=
        isCyclic_of_surjective (psl2FieldAut K).rangeRestrict
          (psl2FieldAut K).rangeRestrict_surjective
      exact (((MulAut.conj (MulAut.conj k)⁻¹).subgroupMap
        (psl2FieldAut K).range).isCyclic).mp this
    · intro α hαo hαS
      obtain ⟨σ, hσ⟩ := hodd α hαo hαS
      refine ⟨psl2FieldAut K σ, ⟨σ, rfl⟩, ?_⟩
      rw [← hσ]
      change (MulAut.conj k)⁻¹ * (MulAut.conj k * α * (MulAut.conj k)⁻¹) *
        (MulAut.conj k)⁻¹⁻¹ = α
      group
  ·
    have hmemS' : ∀ x, x ∈ (S : Subgroup PSL(2, K)) ↔ k * x * k⁻¹ ∈ V0 := hmemS
    refine ⟨k⁻¹ * y * k, ?_, k⁻¹ * v * k, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmemS' x, hmemS' (k⁻¹ * y * k * x * (k⁻¹ * y * k)⁻¹),
        Subgroup.mem_normalizer_iff.mp hyN]
      have : k * (k⁻¹ * y * k * x * (k⁻¹ * y * k)⁻¹) * k⁻¹ = y * (k * x * k⁻¹) * y⁻¹ := by
        group
      rw [this]
    · rw [hmemS']
      simpa [mul_assoc] using hv
    · intro h
      apply hyv
      have h' := congrArg (fun z => k * z * k⁻¹) h
      calc y * v * y⁻¹ = k * (k⁻¹ * y * k * (k⁻¹ * v * k) * (k⁻¹ * y * k)⁻¹) * k⁻¹ := by
            group
        _ = k * (k⁻¹ * v * k) * k⁻¹ := h'
        _ = v := by group
    · intro α hαo hαS
      obtain ⟨σ, hσ⟩ := hodd α hαo hαS
      have hα : α = (MulAut.conj k)⁻¹ * psl2FieldAut K σ * MulAut.conj k := by
        rw [← hσ]
        group
      rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
      have : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
      rw [this, hyfix σ, ← map_inv, MulAut.conj_apply, inv_inv]

theorem mulAut_fix_props_of_mulEquiv
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 H) :
    (∀ α β : MulAut H, (∀ x ∈ (S : Subgroup H), α x = x) →
      (∀ x ∈ (S : Subgroup H), β x = x) → α * β = β * α) ∧
    (∃ Γ : Subgroup (MulAut H), IsCyclic Γ ∧
      ∀ α : MulAut H, Odd (orderOf α) → (∀ x ∈ (S : Subgroup H), α x = x) → α ∈ Γ) ∧
    (∃ y ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∃ v ∈ (S : Subgroup H),
      y * v * y⁻¹ ≠ v ∧ ∀ α : MulAut H, Odd (orderOf α) →
        (∀ x ∈ (S : Subgroup H), α x = x) → α y = y) := by
  classical
  set c := MulAut.congr e with hc
  have happ : ∀ (α : MulAut H) (x : H), c α (e x) = e (α x) := by
    intro α x
    show e (α (e.symm (e x))) = e (α x)
    rw [MulEquiv.symm_apply_apply]
  let S' : Sylow 2 PSL(2, GaloisField p f) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup PSL(2, GaloisField p f)) = (S : Subgroup H).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hfix : ∀ α : MulAut H, (∀ x ∈ (S : Subgroup H), α x = x) →
      ∀ x ∈ (S' : Subgroup PSL(2, GaloisField p f)), c α x = x := by
    intro α hα x hx
    rw [hS'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, happ, hα y hy]
  have hord : ∀ α : MulAut H, orderOf (c α) = orderOf α := fun α => MulEquiv.orderOf_eq c α
  obtain ⟨hcomm, ⟨Γ, hΓ, hΓmem⟩, ⟨y, hyN, v, hv, hyv, hyfix⟩⟩ :=
    psl2_mulAut_fix_props hp hf h5 h8 S'
  refine ⟨?_, ?_, ?_⟩
  · intro α β hα hβ
    apply c.injective
    rw [map_mul, map_mul]
    exact hcomm _ _ (hfix α hα) (hfix β hβ)
  · refine ⟨Γ.map c.symm.toMonoidHom, (c.symm.subgroupMap Γ).isCyclic.mp hΓ, ?_⟩
    intro α hαo hαS
    refine ⟨c α, hΓmem (c α) (by rwa [hord]) (hfix α hαS), ?_⟩
    simp
  · have hyH : e.symm y ∈ Subgroup.normalizer ((S : Subgroup H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp hyN (e x)
      rw [hS'] at h1
      have h2 : y * e x * y⁻¹ = e (e.symm y * x * (e.symm y)⁻¹) := by simp
      rw [h2, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
      simpa using h1
    have hvH : e.symm v ∈ (S : Subgroup H) := by
      rw [hS'] at hv
      rwa [← Subgroup.mem_map_equiv]
    refine ⟨e.symm y, hyH, e.symm v, hvH, ?_, ?_⟩
    · intro h
      apply hyv
      have h' := congrArg e h
      simpa using h'
    · intro α hαo hαS
      have h := hyfix (c α) (by rwa [hord]) (hfix α hαS)
      have h' : c α (e (e.symm y)) = e (e.symm y) := by simpa using h
      rw [happ] at h'
      exact e.injective h'

end FieldAut

end CFSG.Goldschmidt.G3b

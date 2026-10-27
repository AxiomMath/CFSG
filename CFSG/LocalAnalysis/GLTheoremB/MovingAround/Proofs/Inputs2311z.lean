module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Plane9
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Transvection
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeS
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSixW
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311z

section Abstract

variable {G : Type} [Group G]

theorem pow_conj_eq_zpow_mul_inputs2311z {x y c : G} (hcx : c * x * c⁻¹ = x) {s : ℤ}
    (hcy : c * y * c⁻¹ = x ^ s * y) (n : ℕ) :
    c ^ n * y * (c ^ n)⁻¹ = x ^ (s * n) * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcxs : c * x ^ (s * n) * c⁻¹ = x ^ (s * n) := by
      have h := map_zpow (MulAut.conj c) x (s * n)
      simp only [MulAut.conj_apply] at h
      rw [h, hcx]
    calc c ^ (n + 1) * y * (c ^ (n + 1))⁻¹ = c * (c ^ n * y * (c ^ n)⁻¹) * c⁻¹ := by
          rw [pow_succ']; group
      _ = c * (x ^ (s * n) * y) * c⁻¹ := by rw [ih]
      _ = (c * x ^ (s * n) * c⁻¹) * (c * y * c⁻¹) := by group
      _ = x ^ (s * n) * (x ^ s * y) := by rw [hcxs, hcy]
      _ = x ^ (s * ((n + 1 : ℕ) : ℤ)) * y := by
          rw [← mul_assoc, ← zpow_add]; push_cast; ring_nf

theorem exists_mem_derived_conj_inputs2311z [Finite G] {x y c : G} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : y * x = x * y) (hcx : c * x * c⁻¹ = x)
    (hcy : c * y * c⁻¹ = x * y ∨ c * y * c⁻¹ = x⁻¹ * y)
    (h9 : ¬ 9 ∣ (⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆).relIndex
      (Subgroup.centralizer ({x} : Set G)))
    (hyR : y ∉ ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆) :
    ∃ r ∈ ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆,
      r * y * r⁻¹ = x * y ∨ r * y * r⁻¹ = x⁻¹ * y := by
  classical
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set R := ⁅C, C⁆ with hR
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.2 (by
    calc c * x = (c * x * c⁻¹) * c := by group
      _ = x * c := by rw [hcx])
  have hmemR : ∀ u : C, (u : G) ∈ R ↔ u ∈ commutator C := fun u => by
    rw [hR, ← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_iff_mem C.subtype_injective
  have hsub : R.subgroupOf C = commutator C := by
    ext u
    rw [Subgroup.mem_subgroupOf]
    exact hmemR u
  set A := Abelianization C with hA
  have hcard : Nat.card A = R.relIndex C := by
    rw [Subgroup.relIndex, hsub]
    rfl
  set π : C →* A := Abelianization.of with hπ
  have hπ1 : ∀ u : C, π u = 1 ↔ (u : G) ∈ R := fun u => by
    rw [hmemR, ← Abelianization.ker_of, MonoidHom.mem_ker]
  set yb := π ⟨y, hyC⟩ with hyb
  set cb := π ⟨c, hcC⟩ with hcb
  have hyb1 : yb ≠ 1 := fun h => hyR ((hπ1 _).1 h)
  have hyb3 : yb ^ 3 = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyC⟩ : C) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)
    rw [this, map_one]
  set n := Nat.card A with hn
  have hn9 : ¬ 9 ∣ n := by rw [hcard]; exact h9
  have hcn : cb ^ n = 1 := pow_card_eq_one'
  obtain ⟨b, hb3, hcb3⟩ : ∃ b : ℕ, b % 3 = 1 ∧ cb ^ (3 * b) = 1 := by
    by_cases h3 : 3 ∣ n
    · obtain ⟨m, hm⟩ := h3
      have hm3 : ¬ 3 ∣ m := fun ⟨k, hk⟩ => hn9 ⟨k, by rw [hm, hk]; ring⟩
      refine ⟨m * m, ?_, ?_⟩
      · have : m % 3 = 1 ∨ m % 3 = 2 := by omega
        rcases this with h | h <;> simp [Nat.mul_mod, h]
      · rw [show 3 * (m * m) = (3 * m) * m by ring, ← hm, pow_mul, hcn, one_pow]
    · refine ⟨n * n, ?_, ?_⟩
      · have : n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases this with h | h <;> simp [Nat.mul_mod, h]
      · rw [show 3 * (n * n) = n * (3 * n) by ring, pow_mul, hcn, one_pow]
  set wb := cb ^ b with hwb
  have hwb3 : wb ^ 3 = 1 := by rw [hwb, ← pow_mul, mul_comm, hcb3]
  have hwy : wb ∈ Subgroup.zpowers yb := by
    by_contra hnot
    have h9' :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.card_closure_pair
        hyb3 hyb1 hwb3 (mul_comm yb wb) hnot
    apply hn9
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← h9']
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := hwy
  have hrC : c ^ b * y ^ (-k) ∈ C := mul_mem (pow_mem hcC b) (zpow_mem hyC (-k))
  have hrR : c ^ b * y ^ (-k) ∈ R := by
    have h := (hπ1 ⟨c ^ b * y ^ (-k), hrC⟩).1 (by
      have e : (⟨c ^ b * y ^ (-k), hrC⟩ : C) = (⟨c, hcC⟩ : C) ^ b * (⟨y, hyC⟩ : C) ^ (-k) :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_pow, map_zpow, ← hcb, ← hyb, ← hwb, ← hk, zpow_neg, mul_inv_cancel])
    exact h
  have hyk : y ^ (-k) * y * (y ^ (-k))⁻¹ = y := by group
  have hconj : (c ^ b * y ^ (-k)) * y * (c ^ b * y ^ (-k))⁻¹ = c ^ b * y * (c ^ b)⁻¹ := by
    calc (c ^ b * y ^ (-k)) * y * (c ^ b * y ^ (-k))⁻¹ =
        c ^ b * (y ^ (-k) * y * (y ^ (-k))⁻¹) * (c ^ b)⁻¹ := by group
      _ = c ^ b * y * (c ^ b)⁻¹ := by rw [hyk]
  have hxb : ∀ s : ℤ, x ^ (s * (b : ℤ)) = x ^ s := fun s => by
    have hb : (b : ℤ) = 3 * ((b / 3 : ℕ) : ℤ) + 1 := by omega
    have hx3' : x ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hx3
    rw [hb, mul_add, mul_one, zpow_add, show s * (3 * ((b / 3 : ℕ) : ℤ)) =
      3 * (s * ((b / 3 : ℕ) : ℤ)) by ring, zpow_mul, hx3', one_zpow, one_mul]
  refine ⟨c ^ b * y ^ (-k), hrR, ?_⟩
  rw [hconj]
  rcases hcy with h | h
  · left
    have h' : c * y * c⁻¹ = x ^ (1 : ℤ) * y := by rw [zpow_one]; exact h
    rw [pow_conj_eq_zpow_mul_inputs2311z hcx h' b, hxb, zpow_one]
  · right
    have h' : c * y * c⁻¹ = x ^ (-1 : ℤ) * y := by rw [zpow_neg_one]; exact h
    rw [pow_conj_eq_zpow_mul_inputs2311z hcx h' b, hxb, zpow_neg_one]

end Abstract

section Frame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
open scoped Matrix


variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_steinberg_frame_inputs2311z {q : ℕ} (hq1 : 1 ≤ q) (Φ : D4PhiFrame K σ q (-1)) :
    ∃ g : ModGL TwistTag.D4.tag (AlgebraicClosure K),
      g ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      trialityFrob (AlgebraicClosure K) Φ.Fr g = g * threeSixN (AlgebraicClosure K) (-1) ∧
      ∀ e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        frameConj Φ e ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) →
          g⁻¹ * triEmb K σ (AlgebraicClosure K) e * g = frameConj Φ e := by
  classical
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  set nε := threeSixN (AlgebraicClosure K) (-1) with hnε
  have hnεM : nε ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) :=
    threeSixN_mem_monomialSubgroup hε
  have hnεw := threeSixN_weylImage (L := AlgebraicClosure K) hε
  have hWeq : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨Φ.n, Φ.hn⟩ =
      weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨nε, hnεM⟩ := by
    rw [Φ.hnw]
    exact ext_single fun i => (Φ.hw _).trans (hnεw _).symm
  set t := Φ.n * nε⁻¹ with ht
  have htM : t ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) :=
    mul_mem Φ.hn (inv_mem hnεM)
  have htT : t ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) := by
    refine mem_torusGroup_of_mapsRootLines_one htM ?_
    have h1 : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨t, htM⟩ = 1 := by
      have e : (⟨t, htM⟩ : monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)) =
          ⟨Φ.n, Φ.hn⟩ * (⟨nε, hnεM⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, hWeq, mul_inv_cancel]
    have := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := AlgebraicClosure K) ⟨t, htM⟩
    rwa [h1] at this
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust Φ.Fr Φ.hFr hnεM (d4T36M (-1)) hnεw
    (d4T36M_sub_det_ne_zero hε hq1) htT
  have hsG : s ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) :=
    torusGroup_le_adjointGroup' hsT
  refine ⟨Φ.g0 * s⁻¹, mul_mem Φ.hg0C (inv_mem hsG), ?_, fun e he => ?_⟩
  · have hFs : twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr s = nε⁻¹ * (s * t) * nε := by
      rw [← hs]; group
    change twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr (Φ.g0 * s⁻¹) = Φ.g0 * s⁻¹ * nε
    rw [map_mul, map_inv, Φ.hg0, hFs, ht]
    group
  · rw [frameConj_apply] at he ⊢
    have hc := torusGroup_comm hsT he
    calc (Φ.g0 * s⁻¹)⁻¹ * triEmb K σ (AlgebraicClosure K) e * (Φ.g0 * s⁻¹) =
        s * (Φ.g0⁻¹ * triEmb K σ (AlgebraicClosure K) e * Φ.g0) * s⁻¹ := by group
      _ = (Φ.g0⁻¹ * triEmb K σ (AlgebraicClosure K) e * Φ.g0) * s * s⁻¹ := by rw [hc]
      _ = Φ.g0⁻¹ * triEmb K σ (AlgebraicClosure K) e * Φ.g0 := by group

end Frame

section Crux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

theorem phiExp_root_check_inputs2311z : ∀ i j : ZMod 3, ∃ k : Fin 24,
    (∑ t : Fin TwistTag.D4.tag.rank, ((d4RootVec k t : ℤ) : ZMod 3) * phiExp i j t) = 0 := by
  decide +kernel

@[expose] def orthVecs_inputs2311z : List (Fin Tag.D4.rank → ℤ) :=
  [![1, 0, 0, -1], ![0, 1, 0, 1], ![1, -1, 0, 0], ![1, 1, 0, 0]]

theorem phiExp_orth_check_inputs2311z : ∀ i j i' j' : ZMod 3, (i, j) ≠ (0, 0) →
    (i', j') ≠ (0, 0) → (i', j') ≠ (i, j) → (i', j') ≠ (2 * i, 2 * j) →
    ∃ μ ∈ orthVecs_inputs2311z, (∀ k : Fin 24,
      (∑ t : Fin TwistTag.D4.tag.rank, ((d4RootVec k t : ℤ) : ZMod 3) * phiExp i j t) = 0 →
        iform (τ := Tag.D4) (d4RootVec k) μ = 0) ∧
      (∑ t : Fin TwistTag.D4.tag.rank, ((μ t : ℤ) : ZMod 3) * phiExp i' j' t) ≠ 0 := by
  decide +kernel


theorem rootChar_eq_one_of_mem_d4A2Tv_inputs2311z {L : Type} [Field L] {v : WeylGroup Tag.D4}
    {b : Fin Tag.D4.rank → Lˣ} (hb : rootDiagUnit Tag.D4 b ∈ d4A2Tv L v)
    {μ : Fin Tag.D4.rank → ℤ}
    (hμ : ∀ α ∈ (fun β => v • β) '' d4A2Sigma, iform (τ := Tag.D4) α μ = 0) :
    rootChar b μ = 1 := by
  obtain ⟨h, hh, hhb⟩ := Subgroup.mem_map.1 hb
  obtain ⟨t, u, rfl⟩ := mem_subsystemTorus_d4A2.1 hh
  set c₀ : Fin Tag.D4.rank → Lˣ := fun j => t ^ Tag.D4.cartan 0 j with hc₀
  set c₂ : Fin Tag.D4.rank → Lˣ := fun j => u ^ Tag.D4.cartan 2 j with hc₂
  have hdc : d4A2TorusElt t u = rootDiagUnit Tag.D4 (c₀ * c₂) := by
    rw [d4A2TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
    exact (map_mul (rootDiagUnitHom Tag.D4 L) c₀ c₂).symm
  have hb' : weylTuple v (c₀ * c₂) = b := by
    apply rootDiagUnit_injective
    rw [← canonicalRep_conj_rootDiagUnit, ← hdc]
    exact hhb
  have hpair : ∀ i : Fin Tag.D4.rank, Pi.single i 1 ∈ d4A2Sigma →
      ∑ j, Tag.D4.cartan i j * (v⁻¹ • μ) j = 0 := by
    intro i hi
    have h1 := iform_single_left (τ := Tag.D4) i (v⁻¹ • μ)
    have hs : Tag.D4.symmetrizer i i = 1 := by fin_cases i <;> rfl
    rw [hs, one_mul, ← iform_smul v, smul_inv_smul] at h1
    rw [← h1]
    exact hμ _ ⟨_, hi, rfl⟩
  have h0 := hpair 0 (by simp [d4A2Sigma])
  have h2 := hpair 2 (by simp [d4A2Sigma])
  rw [← hb', rootChar_weylTuple]
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, hc₀, hc₂, ← zpow_mul,
    Finset.prod_zpow_eq_zpow_sum, h0, h2, zpow_zero, mul_one]

end Crux

section Main

theorem not_nine_dvd_index_inputs2311z {Q : ℕ} (hQ : Q % 3 = 2) :
    ¬ 9 ∣ Q ^ 9 * (Q ^ 3 - 1) * (Q ^ 8 + Q ^ 4 + 1) := by
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub h3]
  have hQ9 : Q % 9 = 2 ∨ Q % 9 = 5 ∨ Q % 9 = 8 := by omega
  rw [← ZMod.natCast_mod Q 9]
  rcases hQ9 with h | h | h <;> rw [h] <;> decide

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
open scoped Matrix


theorem exists_frame_core_transvection_inputs2311z {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Φ : D4PhiFrame K σ (ℓ ^ f) (-1)) {x y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hxT : frameConj Φ x ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr))
    (hyT : frameConj Φ y ∈
      twistedTorusOf Φ.n (twistHom TwistTag.D4 (AlgebraicClosure K) Φ.Fr))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ r ∈ Subgroup.closure {k | k * x = x * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1},
      r * x * r⁻¹ = x ∧ (r * y * r⁻¹ = x * y ∨ r * y * r⁻¹ = x⁻¹ * y) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have h3L : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three (AlgebraicClosure K) h3L
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hφ := frameConj_injective Φ
  obtain ⟨i, j, hxd⟩ := exists_phiExp_of_frameTorus hq Φ hζ hx3 hxT
  obtain ⟨i', j', hyd⟩ := exists_phiExp_of_frameTorus hq Φ hζ hy3 hyT
  have hphi0 : phiExp 0 0 = 0 := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · rfl
    · show (0 : ZMod 3) - 0 = 0
      exact sub_self 0
  have hd0 : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp 0 0)) = 1 := by
    rw [hphi0]
    have : tup ζ (0 : Exp3) = 1 := by
      funext k
      simp [tup]
    rw [this]
    exact map_one (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K))
  have hij : (i, j) ≠ (0, 0) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hx1 (hφ (by rw [hxd, hd0, map_one]))
  have hij' : (i', j') ≠ (0, 0) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hyx (by
      rw [show y = 1 from hφ (by rw [hyd, hd0, map_one])]
      exact one_mem _)
  have hij1 : (i', j') ≠ (i, j) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hyx (by
      rw [show y = x from hφ (by rw [hyd, hxd])]
      exact Subgroup.mem_zpowers x)
  have hij2 : (i', j') ≠ (2 * i, 2 * j) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    apply hyx
    have : y = x ^ 2 := by
      apply hφ
      rw [hyd, map_pow, hxd, phiExp_two_mul, tup_two_mul hζ3]
      exact map_pow (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K)) _ 2
    rw [this]
    exact Subgroup.npow_mem_zpowers x 2
  obtain ⟨c, hcx, hcy⟩ := exists_frame_transvection hℓ hℓ3 hf hq hK Φ hxT hyT hx3 hx1 hy3 hyx
  have hxy : y * x = x * y := by
    apply hφ
    rw [map_mul, map_mul]
    exact torusGroup_comm (mem_twistedTorusOf.1 hyT).1 (mem_twistedTorusOf.1 hxT).1
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨g, hgG, hFg, hgφ⟩ := exists_steinberg_frame_inputs2311z hq1 Φ
  have hconj : ∀ {e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
      {a : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ},
      frameConj Φ e = rootDiagUnit TwistTag.D4.tag a →
        threeSixEmb K (AlgebraicClosure K) σ e = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
    intro e a he
    have h := hgφ e (he ▸ rootDiagUnit_mem_torusGroup a)
    rw [he] at h
    calc threeSixEmb K (AlgebraicClosure K) σ e =
        g * (g⁻¹ * triEmb K σ (AlgebraicClosure K) e * g) * g⁻¹ := by
          change triEmb K σ (AlgebraicClosure K) e = _
          group
      _ = _ := by rw [h]
  have hxa := hconj hxd
  have hyb := hconj hyd
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Φ.Fr.comp (algebraMap K (AlgebraicClosure K)) :=
    RingHom.ext fun c => by simp [hσ, Φ.hFr, map_pow]
  have haT : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) ∈
      threeSixTorus (AlgebraicClosure K) Φ.Fr (-1) := by
    refine Subgroup.mem_inf.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    have hfix : trialityFrob (AlgebraicClosure K) Φ.Fr (triEmb K σ (AlgebraicClosure K) x) =
        triEmb K σ (AlgebraicClosure K) x := triEmb_fixed Φ.Fr hcomm x
    have e : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) =
        g⁻¹ * triEmb K σ (AlgebraicClosure K) x * g := by
      rw [hgφ x (mem_twistedTorusOf.1 hxT).1, hxd]
    change threeSixN (AlgebraicClosure K) (-1) * trialityFrob (AlgebraicClosure K) Φ.Fr
      (rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j))) *
        (threeSixN (AlgebraicClosure K) (-1))⁻¹ = rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j))
    set nε := threeSixN (AlgebraicClosure K) (-1) with hnε
    rw [e, map_mul, map_mul, map_inv, hFg, hfix]
    clear_value nε
    group
  have ha1 : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j)) ≠ 1 :=
    fun h => hx1 (hφ (by rw [hxd, h, map_one]))
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i j))) = 3 :=
    orderOf_eq_prime (by rw [← hxd, ← map_pow, hx3, map_one]) ha1
  have hane : tup ζ (phiExp i j) ≠ 1 := fun h => ha1 (by
    rw [h]; exact map_one (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K)))
  obtain ⟨k₀, hk₀⟩ := phiExp_root_check_inputs2311z i j
  have hne : (survivingRoots (tup ζ (phiExp i j))).Nonempty :=
    ⟨d4RootVec k₀, isRoot_d4RootVec k₀, (rootChar_tup hζ3 (phiExp i j) (d4RootVec k₀)).trans
      (by rw [hk₀, ZMod.val_zero, pow_zero])⟩
  obtain ⟨i₀, hi₀⟩ := survivingRoots_eq_sigma_of_nonempty hε
    ((rootDiagUnit_mem_threeSixTorus_iff Φ.Fr Φ.hFr hε _).1 haT) hane hne
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
      (fun α => v • α) '' d4A2Sigma = survivingRoots (tup ζ (phiExp i j)) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i₀
    exact ⟨w, by rw [hi₀, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  have hdle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * (ℓ ^ f : ℕ) + 1 :=
    ⟨(ℓ ^ f) ^ 2 - ℓ ^ f + 1, by push_cast [Nat.cast_sub hdle]; ring⟩
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    have : ℓ ≠ 4 := by rintro rfl; exact absurd hℓ (by norm_num)
    omega
  have hq2 : 2 < ℓ ^ f :=
    lt_of_lt_of_le (by omega) (le_trans hℓ5 (Nat.le_self_pow (by omega) ℓ))
  obtain ⟨-, -, hR, -, hunit, hQS, hZ, -, -, -, -⟩ :=
    triality_three_six_singular_fixed_centralizers_gen hℓ hf K hK σ hσ (AlgebraicClosure K) Φ.Fr
      Φ.hFr hε hd g hgG hFg Nat.prime_three (by norm_num) hℓ3 hq2 _ haT hord v hv x hxa
  set C := Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    with hC
  set R := threeSixSingularR (AlgebraicClosure K) K σ Φ.Fr (-1) v g with hRdef
  have hRC : R ≤ C := hR ▸ Subgroup.commutator_le_self C
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  have : Finite (ModGL TwistTag.D4.tag K) := inferInstance
  obtain ⟨U, hU, eU, -⟩ := hunit rfl
  have hRcard : Nat.card R = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    rw [Nat.card_congr eU.toEquiv, ← mnSyl_card_unitarySet_three (Ω := AlgebraicClosure K) hf,
      ← hU]
    rfl
  have h9 : ¬ 9 ∣ R.relIndex C := by
    have hΓ := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hidx : R.relIndex C * Nat.card R = Nat.card C := by
      have h := Subgroup.relIndex_mul_card (H := R) (K := C)
      rwa [inf_eq_left.2 hRC] at h
    have hCdvd : Nat.card C ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.card_subgroup_dvd_card C
    have hΓR : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        Nat.card R * ((ℓ ^ f) ^ 9 * ((ℓ ^ f) ^ 3 - 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1)) := by
      rw [hΓ, hRcard]
      have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h3 : 1 ≤ (ℓ ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h6 : 1 ≤ (ℓ ^ f) ^ 6 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h3, h6]
      ring
    have hdvd : R.relIndex C ∣
        (ℓ ^ f) ^ 9 * ((ℓ ^ f) ^ 3 - 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) := by
      have h1 : Nat.card R * R.relIndex C ∣ Nat.card R *
          ((ℓ ^ f) ^ 9 * ((ℓ ^ f) ^ 3 - 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1)) := by
        rw [mul_comm, hidx, ← hΓR]
        exact hCdvd
      exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
    exact fun h => not_nine_dvd_index_inputs2311z hq (h.trans hdvd)
  have hyR : y ∉ R := by
    intro hy
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hy)
    have hub : u = rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i' j')) := by
      have h1 : g * u * g⁻¹ = g * rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i' j')) * g⁻¹ := by
        rw [← hyb]
        exact hug
      simpa using h1
    have hbQ : rootDiagUnit TwistTag.D4.tag (tup ζ (phiExp i' j')) ∈
        d4A2Qv (AlgebraicClosure K) v := by
      rw [← hub]
      exact (Subgroup.mem_inf.1 hu).1
    have hbT : rootDiagUnit Tag.D4 (tup ζ (phiExp i' j')) ∈ d4A2Tv (AlgebraicClosure K) v := by
      rw [← d4A2Qv_inf_torusGroup]
      exact Subgroup.mem_inf.2 ⟨hbQ, rootDiagUnit_mem_torusGroup _⟩
    obtain ⟨μ, -, hμx, hμy⟩ := phiExp_orth_check_inputs2311z i j i' j' hij hij' hij1 hij2
    have h1 := rootChar_eq_one_of_mem_d4A2Tv_inputs2311z hbT (μ := μ) (fun α hα => by
      rw [hv] at hα
      obtain ⟨hαr, hα1⟩ := hα
      obtain ⟨k, rfl⟩ := exists_d4RootVec_eq hαr
      have h2 := (rootChar_tup hζ3 (phiExp i j) (d4RootVec k)).symm.trans hα1
      exact hμx k (pow_val_inj hζ (by rw [ZMod.val_zero, pow_zero]; exact h2)))
    have h2 := (rootChar_tup hζ3 (phiExp i' j') μ).symm.trans h1
    exact hμy (pow_val_inj hζ (by rw [ZMod.val_zero, pow_zero]; exact h2))
  have hN3 : R ≤ Subgroup.closure {k | k * x = x * k ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} := by
    have hℓR : ℓ ∣ Nat.card R := by
      rw [hRcard]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self ℓ (by omega))
        (by norm_num)) _) _
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' ℓ hℓR
    set N : Subgroup R := Subgroup.normalClosure {u : R | u ^ ℓ = 1} with hN
    have hwN : w ∈ N := Subgroup.subset_normalClosure (by
      show w ^ ℓ = 1
      rw [← hw]
      exact pow_orderOf_eq_one w)
    have hNc : ¬ N ≤ Subgroup.center R := by
      intro hc
      have hdvd : ℓ ∣ Nat.card (Subgroup.center R) := by
        rw [← hw]
        exact Subgroup.orderOf_dvd_natCard _ (hc hwN)
      rw [hZ] at hdvd
      have h3 : ℓ ∣ 3 := by
        have h' : (Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - (-1)) : ℤ) ∣ 3 := Int.gcd_dvd_left ..
        exact hdvd.trans (by exact_mod_cast h')
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3)
    have htop : N = ⊤ := by
      rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.normal_le_center_or_eq_top hQS.1 hQS.2.1 N with
        hc | htop
      · exact absurd hc hNc
      · exact htop
    intro r hr
    have hrN : (⟨r, hr⟩ : R) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    have hle : N ≤ Subgroup.closure {u : R | u ^ ℓ = 1} := by
      rw [hN, Subgroup.normalClosure]
      refine Subgroup.closure_mono ?_
      intro u hu
      obtain ⟨b, hb, hbu⟩ := Group.mem_conjugatesOfSet_iff.1 hu
      obtain ⟨c', rfl⟩ := isConj_iff.1 hbu
      show (c' * b * c'⁻¹) ^ ℓ = 1
      rw [conj_pow, show b ^ ℓ = 1 from hb]
      group
    have h1 := Subgroup.mem_map_of_mem R.subtype (hle hrN)
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.1 (hRC u.2), 1, ?_⟩
    rw [pow_one, ← map_pow, show u ^ ℓ = 1 from hu, map_one]
  obtain ⟨r, hrR, hry⟩ := exists_mem_derived_conj_inputs2311z hx3 hy3 hxy hcx hcy
    (by rw [hR]; exact h9) (by rw [hR]; exact hyR)
  rw [hR] at hrR
  refine ⟨r, hN3 hrR, ?_, hry⟩
  rw [Subgroup.mem_centralizer_singleton_iff.1 (hRC hrR), mul_inv_cancel_right]

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311z

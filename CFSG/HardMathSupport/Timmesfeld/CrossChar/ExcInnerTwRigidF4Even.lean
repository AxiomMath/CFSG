module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusTransport
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.Ree CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups

theorem not_dvd_card_reeF4_two_pow (m : ℕ) :
    ¬ (2 ^ (2 * m + 1) + 1) ^ 4 ∣ (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) ^ 2 *
      (2 ^ (2 * m + 1) + 1) ^ 2 * ((2 ^ (2 * m + 1)) ^ 2 + 1) ^ 2 *
      ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) *
      ((2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1) := by
  intro h
  set q := 2 ^ (2 * m + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  set X := q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) with hX
  have hfor : q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) = (q + 1) ^ 2 * X := by rw [hX]; ring
  rw [hfor, show (q + 1) ^ 4 = (q + 1) ^ 2 * (q + 1) ^ 2 by ring] at h
  have hX2 : (q + 1) ^ 2 ∣ X := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have h3 : 3 ∣ q + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, hqdef]
    push_cast
    rw [show (2 : ZMod 3) = -1 by decide, pow_succ, pow_mul,
      show ((-1 : ZMod 3)) ^ 2 = 1 by decide, one_pow, one_mul]
    decide
  have h9 : 9 ∣ X := (show 9 = 3 ^ 2 by norm_num) ▸ (pow_dvd_pow_of_dvd h3 2).trans hX2
  have h0 := (ZMod.natCast_eq_zero_iff X 9).2 h9
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [hX] at h0
  push_cast [Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_sub hq4] at h0
  have hqr : (q : ZMod 9) = 2 ∨ (q : ZMod 9) = 5 ∨ (q : ZMod 9) = 8 := by
    have h1 : (q : ZMod 9) = 2 * 4 ^ m := by
      rw [hqdef, Nat.cast_pow, pow_succ, pow_mul, mul_comm]
      norm_num
    obtain ⟨t, r, hr, hm⟩ : ∃ t r, r < 3 ∧ m = 3 * t + r :=
      ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
    have h64 : (4 : ZMod 9) ^ 3 = 1 := by decide
    rw [h1, hm, pow_add, pow_mul, h64, one_pow, one_mul]
    interval_cases r <;> decide
  rcases hqr with hq | hq | hq <;> rw [hq] at h0 <;> revert h0 <;> decide

section Even

theorem coe_finiteExceptionalAut_pow_two_mul {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (j : ℕ) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ j)
    (h : adjointGroup ReeTag.F4.tag K) :
    ((ReeTag.F4.finiteExceptionalAut K ^ (2 * j)) h : ModGL ReeTag.F4.tag K) =
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL ReeTag.F4.tag K) := by
  rw [finiteExceptionalAut_pow_two_mul, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.F4 hσ]
  rw [coe_exactNormalAut, rootDiagUnit_one, exactQ_zero, mul_one, one_mul, inv_one, mul_one,
    mul_one]

theorem eq_one_of_fix_twistedSL2_F4_even (K : Type) [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hev : Even (Nat.card K)) (hK4 : 4 ≤ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (P : Fin Tag.F4.rank → GL (Fin 2) L)
    (hPΓ : ∀ (i : Fin Tag.F4.rank) (A : SL2 K), rootSL2 Tag.F4 L (Pi.single i 1)
      (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈ langModel Tag.F4 K L g0)
    (hPH : ∀ (i : Fin Tag.F4.rank) (ζ : Lˣ), ζ ^ (Nat.card K + 1) = 1 →
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL (P i)))
    (δ : MulAut (langModel Tag.F4 K L g0))
    (hδ : ∀ (i : Fin Tag.F4.rank) (A : SL2 K), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩) : δ = 1 := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  have hp₀2 : p₀ = 2 := by
    by_contra hne
    have hodd : Odd (p₀ ^ f) := (hp₀.odd_of_ne_two hne).pow
    rw [← hK] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hev
  subst hp₀2
  have : CharP K 2 := finite_field_prime_power_characteristic hp₀ hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB⟩ := exists_mul_cartan_F4
  set e := langModelMulEquiv Tag.F4 K L g0 with he_def
  have he : ∀ h, (e h : ModGL Tag.F4 L) = g0⁻¹ * baseChangeGL (algebraMap K L) h * g0 :=
    fun h => by rw [coe_langModelMulEquiv, inv_inv]
  have hfield : ∀ j < f, (∀ i : Fin Tag.F4.rank, ∃ b : Label Tag.F4, ∀ k : Fin Tag.F4.rank,
      ((Nat.card K + 1 : ℕ) : ℤ) ∣
        (∑ l, Tag.F4.cartan k l * b.latticeWeight l) - (2 ^ j : ℕ) * Tag.F4.cartan k i) →
      j = 0 := by
    intro j hj h
    obtain ⟨b, hb⟩ := h ⟨0, by decide⟩
    rw [hK] at hb
    exact field_exponent_eq_zero hp₀ hj (d := 1) (m := 2 ^ f + 1) (B := B)
      (by rw [hB, Nat.cast_one, one_smul]) (dvd_refl _) (by omega) (by omega)
      (fun x hx => by rwa [Nat.cast_one, one_mul] at hx) ⟨0, by decide⟩
      (fun β hβ hβl => root_mod_simple_of_artifact f4_root_bound f4_root_simple f4_root_small
        (by have := Nat.one_lt_pow (n := f) (by omega) hp₀.one_lt; omega) _ β hβ hβl) b hb
  have hcard : entryDegreeBound Tag.F4 < Nat.card K := by simp [entryDegreeBound]; omega
  set φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K with hφ
  obtain ⟨-, hNF, -, hINV, -, -, hODD⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hNF' : ∀ α : MulAut (adjointGroup Tag.F4 K),
      ∃! gk : adjointGroup Tag.F4 K × Fin (2 * f), α = MulAut.conj gk.1 * φ ^ (gk.2 : ℕ) := hNF
  have hINV' : ∀ (α : MulAut (adjointGroup Tag.F4 K)) (g : adjointGroup Tag.F4 K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * φ ^ k → α ^ 2 = 1 → k = 0 ∨ k = f := hINV
  have hOUT : ∀ α : MulAut (adjointGroup Tag.F4 K), α ^ 2 = 1 →
      α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range →
        ∃ ψ : MulAut (adjointGroup Tag.F4 K), ψ * α * ψ⁻¹ = φ ^ f := fun α h1 h2 => by
    obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical hf K hK α h1 h2
    exact ⟨ψ, hψ⟩
  have hFIX : ∀ m' : ℕ, f = 2 * m' + 1 → ∀ g : adjointGroup Tag.F4 K,
      g ∈ ReeTag.F4.finiteReeFixedGroup K m' ↔ (φ ^ f) g = g := fun m' hm' => (hODD m' hm').2.2
  have hpow2 : ∀ (j : ℕ) {σ : K ≃+* K}, (∀ c, σ c = c ^ 2 ^ j) → ∀ h : adjointGroup Tag.F4 K,
      ((φ ^ (2 * j)) h : ModGL Tag.F4 K) = Units.map (entrywiseHom σ.toRingHom) h :=
    fun j _ hσ h => coe_finiteExceptionalAut_pow_two_mul j hσ h
  have hfieldtype : ∀ δ : MulAut (langModel Tag.F4 K L g0),
      (∀ (i : Fin Tag.F4.rank) (A : SL2 K), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩) →
      ∀ (g : adjointGroup Tag.F4 K) (j : ℕ),
        (e.trans δ).trans e.symm = MulAut.conj g * φ ^ (2 * j) → δ = 1 := by
    intro δ hδ g j hα
    obtain ⟨σ, hσ⟩ := CFSG.RankThree.Chevalley.exists_frobenius_pow (L := K) (ℓ := 2) j
    refine eq_one_of_model_aut_twisted hp₀ hf hK hg0C e he P hPΓ hPH hfield hcard δ hδ
      (y := (g : ModGL Tag.F4 K)) (σ := σ)
      (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2) fun h => ?_
    rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hpow2 j hσ h]
  set α := (e.trans δ).trans e.symm with hαdef
  obtain ⟨⟨g, k⟩, hgk, huniq⟩ := hNF' α
  simp only at hgk
  rcases Nat.even_or_odd (k : ℕ) with ⟨m, hm⟩ | hodd
  · exact hfieldtype δ hδ g m (hgk.trans (by rw [hm, ← two_mul]))
  exfalso
  have hconj : ∀ (ψ : MulAut (adjointGroup Tag.F4 K)) (x : adjointGroup Tag.F4 K),
      ψ * MulAut.conj x = MulAut.conj (ψ x) * ψ := fun ψ x => by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  set k₀ : ℕ := (k : ℕ) with hk₀
  have hα2form : α ^ 2 = MulAut.conj (g * (φ ^ k₀) g) * φ ^ (2 * k₀) := by
    rw [hgk, pow_two, mul_assoc, ← mul_assoc (φ ^ k₀), hconj, mul_assoc, ← pow_add,
      ← mul_assoc, ← map_mul, ← two_mul]
  have hsq : (e.trans (δ ^ 2)).trans e.symm = α ^ 2 := by
    ext h
    simp only [hαdef, pow_two, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hδ2 : δ ^ 2 = 1 := hfieldtype (δ ^ 2)
    (fun i A => by rw [pow_two, MulAut.mul_apply, hδ i A, hδ i A])
    (g * (φ ^ k₀) g) k₀ (by rw [hsq, hα2form])
  have hα2 : α ^ 2 = 1 := by
    rw [← hsq, hδ2]
    ext h
    simp
  have hkf : k₀ = f := (hINV' α g k₀ k.2 hgk hα2).resolve_left (by obtain ⟨r, hr⟩ := hodd; omega)
  obtain ⟨m', hm'⟩ : ∃ m', f = 2 * m' + 1 := by
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r, by omega⟩
  have hαo : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := by
    rintro ⟨x, hx⟩
    have h0 := huniq ⟨x, ⟨0, by omega⟩⟩ (by
      change α = MulAut.conj x * φ ^ (0 : ℕ)
      rw [pow_zero, mul_one, hx])
    have h1 := congrArg (fun z : adjointGroup Tag.F4 K × Fin (2 * f) => (z.2 : ℕ)) h0
    simp only at h1
    omega
  obtain ⟨ψ, hψ⟩ := hOUT α hα2 hαo
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K (L := L)
    (dvd_refl (Nat.card K + 1))
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    (rootDiagUnit_mem_torusGroup_of_unimodular hB) f4Neg_smul hFr hζq
  rw [hζord] at hH₀card
  set Fδ : Subgroup (langModel Tag.F4 K L g0) :=
    δ.toMonoidHom.eqLocus (MonoidHom.id (langModel Tag.F4 K L g0)) with hFδ
  have hTfix : ∀ (i : Fin Tag.F4.rank) (t : Lˣ), t ^ (Nat.card K + 1) = 1 →
      torusElt Tag.F4 L i t ∈ Fδ.map (langModel Tag.F4 K L g0).subtype := by
    intro i t ht
    obtain ⟨_, ⟨A, rfl⟩, hA⟩ := hPH i t ht
    have hval : rootSL2 Tag.F4 L (Pi.single i 1)
        (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) =
          torusElt Tag.F4 L i t := by
      rw [hA, rootSL2_single, simpleRootSL2_HSL]
    refine ⟨⟨_, hPΓ i A⟩, ?_, hval⟩
    change δ _ = _
    exact hδ i A
  have hH₀F : H₀ ≤ Fδ.map (langModel Tag.F4 K L g0).subtype := by
    intro x hx
    obtain ⟨a, rfl, ha⟩ := (mem_twistedTorus_of_neg (rootDiagUnit_mem_torusGroup_of_unimodular hB)
      f4Neg_smul hFr).1 (hH₀T hx)
    rw [rootDiagUnit_eq_list_prod_torusElt hB a]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    refine hTfix i _ ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha j, one_zpow]
  set S : Subgroup (langModel Tag.F4 K L g0) :=
    (Fδ.map (langModel Tag.F4 K L g0).subtype ⊓ H₀).subgroupOf (langModel Tag.F4 K L g0) with hS
  set H₁ : Subgroup (adjointGroup Tag.F4 K) :=
    (S.map e.symm.toMonoidHom).map ψ.toMonoidHom with hH₁
  have hH₁R : H₁ ≤ ReeTag.F4.finiteReeFixedGroup K m' := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine (hFIX m' hm' _).2 ?_
    have hyF : δ y = y := by
      obtain ⟨⟨z, hz, hzy⟩, -⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)
      have hzy' : z = y := Subtype.ext hzy
      rw [← hzy']
      exact hz
    have hαy : α (e.symm y) = e.symm y := by
      simp only [hαdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hyF]
    rw [← hψ]
    change ψ (α (ψ⁻¹ (ψ (e.symm y)))) = ψ (e.symm y)
    rw [MulAut.inv_apply_self, hαy]
  have hcardH₁ : Nat.card H₁ = (Nat.card K + 1) ^ 4 := by
    rw [hH₁, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
      Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans
        (Subgroup.map_subtype_le Fδ))).toEquiv, inf_of_le_right hH₀F, hH₀card]
    rfl
  have hdvd := Subgroup.card_dvd_of_le hH₁R
  have hK' : Nat.card K = 2 ^ (2 * m' + 1) := by rw [hK, hm']
  have hR : Nat.card (ReeTag.F4.finiteReeFixedGroup K m') = Nat.card (ReeTag.F4.reeGamma K m') :=
    (Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective).symm
  have hdvd' : (Nat.card K + 1) ^ 4 ∣ Nat.card (ReeTag.F4.reeGamma K m') := by
    rw [← hcardH₁]
    exact hdvd.trans (dvd_of_eq hR)
  rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    m' K hK').1, hK'] at hdvd'
  exact not_dvd_card_reeF4_two_pow m' hdvd'

end Even

end CFSG.HardMathSupport.Timmesfeld.CrossChar

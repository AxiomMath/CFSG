module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Steinberg.TwistedD4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4

theorem isRoot_d4_longFixedA : IsRoot d4 ![0, 0, 1, 0] :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨2, by decide, by
    funext i
    fin_cases i <;> decide⟩

theorem isRoot_d4_longFixedB : IsRoot d4 ![1, 1, 1, 1] :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨19, by decide, by
    funext i
    fin_cases i <;> decide⟩

theorem coe_xPar_d4_eq_pinnedX {K : Type} [Field K] {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β)
    (c : K) :
    ((xPar (rootOperatorFamily d4) β c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K β ((((rootOperatorFamily d4).pinnedFamilySign β : ℤ) : K) * c) := by
  have h2 : pinnedX d4 K β ((((rootOperatorFamily d4).pinnedFamilySign β : ℤ) : K) * c) =
      (rootOperatorFamily d4).eltUnit K ⟨β, hβ⟩ c := by
    rw [(rootOperatorFamily d4).pinnedX_eq_eltUnit K hβ, ← mul_assoc,
      (rootOperatorFamily d4).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot hβ]
  exact h2.symm

theorem rootDiagUnit_conj_xPar_d4 {K : Type} [Field K] (a : Fin d4.rank → Kˣ)
    {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (c : K) :
    rootDiagUnit d4 a * ((xPar (rootOperatorFamily d4) β c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 a)⁻¹ =
      ((xPar (rootOperatorFamily d4) β (((rootChar a β : Kˣ) : K) * c) : adjointGroup d4 K) :
        ModGL d4 K) := by
  rw [coe_xPar_d4_eq_pinnedX hβ, coe_xPar_d4_eq_pinnedX hβ, rootDiagUnit_conj_pinnedX a hβ]
  congr 1
  ring

theorem rootChar_eq_one_of_commute_xPar_d4 {K : Type} [Field K] (a : Fin d4.rank → Kˣ)
    {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β)
    (h : rootDiagUnit d4 a * ((xPar (rootOperatorFamily d4) β 1 : adjointGroup d4 K) : ModGL d4 K) =
      ((xPar (rootOperatorFamily d4) β 1 : adjointGroup d4 K) : ModGL d4 K) *
        rootDiagUnit d4 a) :
    rootChar a β = 1 := by
  have h1 := rootDiagUnit_conj_xPar_d4 a hβ (1 : K)
  rw [h, mul_inv_cancel_right] at h1
  have h2 : (1 : K) = ((rootChar a β : Kˣ) : K) * 1 :=
    xPar_injective hβ (Subtype.ext h1)
  exact Units.ext (by simpa using h2.symm)

theorem graphFixedRootMonomial_eq_canonicalRep_mul_torus (t : TwistTag) {K : Type} [Field K]
    (σ : K →+* K) (n : graphFixedRootMonomial t K σ) :
    ∃ s ∈ torusGroup t.tag K, (n : ModGL t.tag K) =
      canonicalRep (coxeterSystem t.tag) K (graphFixedRootWeylHom t K σ n) * s := by
  set w := graphFixedRootWeylHom t K σ n
  have hwmem : w ∈ relWeylTwist t := by
    rw [← graphFixedRootWeylHom_range t K σ]
    exact ⟨n, rfl⟩
  set m : graphFixedRootMonomial t K σ :=
    ⟨canonicalRep (coxeterSystem t.tag) K w, canonicalRep_mem_graphFixedRootMonomial t K σ hwmem⟩
  have hmw : graphFixedRootWeylHom t K σ m = w := graphFixedRootWeylHom_canonicalRep t K σ hwmem
  have hker : m⁻¹ * n ∈ (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmw, inv_mul_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  have ht : ((m⁻¹ * n : graphFixedRootMonomial t K σ) : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hker).1).1
  exact ⟨_, ht, congrArg Subtype.val (mul_inv_cancel_left m n).symm⟩

theorem units_pow_three_eq_one_cases {K : Type} [Field K] {ω x : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hx : x ^ 3 = 1) : x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have hW3 : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hW1 : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have hX3 : (x : K) ^ 3 = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have hsum : 1 + (ω : K) + (ω : K) ^ 2 = 0 := by
    have h : ((ω : K) - 1) * (1 + (ω : K) + (ω : K) ^ 2) = 0 := by linear_combination hW3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hW1
    · exact h
  have hprod : ((x : K) - 1) * ((x : K) - ω) * ((x : K) - (ω : K) ^ 2) = 0 := by
    linear_combination hX3 + ((x : K) - (x : K) ^ 2) * hsum + ((x : K) - 1) * hW3
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.1 h))
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.1 h)))

theorem d4_torus_cent_fixed {p f : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (_hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] (_hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (_hσ : ∀ c, σ c = c ^ (p ^ f))
    (ω : Kˣ) (_hωσ : Units.map σ.toRingHom.toMonoidHom ω = ω) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hz : (z : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω])
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hW3 : (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hct : (c : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hc0 : (c : ModGL TwistTag.D4.tag K) *
        ((xPar (rootOperatorFamily d4) ![0, 0, 1, 0] 1 : adjointGroup d4 K) :
          ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) ![0, 0, 1, 0] 1 : adjointGroup d4 K) :
          ModGL TwistTag.D4.tag K) * (c : ModGL TwistTag.D4.tag K))
    (hc2 : (c : ModGL TwistTag.D4.tag K) *
        ((xPar (rootOperatorFamily d4) ![1, 1, 1, 1] 1 : adjointGroup d4 K) :
          ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) ![1, 1, 1, 1] 1 : adjointGroup d4 K) :
          ModGL TwistTag.D4.tag K) * (c : ModGL TwistTag.D4.tag K))
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) c = c) :
    c ∈ Subgroup.zpowers z := by
  classical
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hct).1
  have hΓ : (c : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ c.2
  have hcompat : ∀ i, a (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (a i) := by
    apply compat_of_twistHom_rootDiagUnit
    rw [← ha]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).2
  set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom
  have ha2 : a (2 : Fin 4) = 1 := by
    have h := (rootChar_d4_apply a ![0, 0, 1, 0]).symm.trans
      (rootChar_eq_one_of_commute_xPar_d4 a isRoot_d4_longFixedA (by rw [← ha]; exact hc0))
    simpa using h
  have ha013 : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1 := by
    have h := (rootChar_d4_apply a ![1, 1, 1, 1]).symm.trans
      (rootChar_eq_one_of_commute_xPar_d4 a isRoot_d4_longFixedB (by rw [← ha]; exact hc2))
    simpa [ha2] using h
  set a' : Fin TwistTag.D4.tag.rank → Kˣ := fun i => Units.map δ.toRingHom.toMonoidHom (a i)
    with ha'
  have hfa : ((fieldActor (t := TwistTag.D4) σ δ c :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag a' := by
    rw [coe_fieldActor, ha, units_map_entrywiseHom_rootDiagUnit]
  have hfix' : (n : ModGL TwistTag.D4.tag K) * rootDiagUnit TwistTag.D4.tag a' *
      (n : ModGL TwistTag.D4.tag K)⁻¹ = rootDiagUnit TwistTag.D4.tag a := by
    rw [MulAut.mul_apply, MulAut.conj_apply] at hfix
    have h := congrArg Subtype.val hfix
    rw [← ha, ← hfa]
    exact h
  set g : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩
  obtain ⟨s, hs, hn⟩ := graphFixedRootMonomial_eq_canonicalRep_mul_torus TwistTag.D4 σ.toRingHom g
  set w := graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g
  have hwmem : w ∈ relWeylTwist TwistTag.D4 := by
    rw [← graphFixedRootWeylHom_range TwistTag.D4 K σ.toRingHom]
    exact ⟨g, rfl⟩
  have hn' : (n : ModGL TwistTag.D4.tag K) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * s := hn
  have hcomm : rootDiagUnit TwistTag.D4.tag a' * s = s * rootDiagUnit TwistTag.D4.tag a' :=
    mul_inv_eq_iff_eq_mul.1 (conj_rootDiagUnit_of_mem_torusGroup a' hs)
  have hconj : rootDiagUnit TwistTag.D4.tag a =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootDiagUnit TwistTag.D4.tag a' *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ := by
    rw [← hfix', hn']
    calc canonicalRep (coxeterSystem TwistTag.D4.tag) K w * s * rootDiagUnit TwistTag.D4.tag a' *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * s)⁻¹
        = canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            (s * rootDiagUnit TwistTag.D4.tag a' * s⁻¹) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ := by group
      _ = _ := by rw [← hcomm, mul_inv_cancel_right]
  have hchar : ∀ v : Fin TwistTag.D4.tag.rank → ℤ, rootChar a (w • v) = rootChar a' v :=
    (rootDiagUnit_eq_conj_canonicalRep_iff a a' w).1 hconj
  have hker : ∀ v : Fin TwistTag.D4.tag.rank → ℤ, v (0 : Fin 4) = v (1 : Fin 4) →
      v (1 : Fin 4) = v (3 : Fin 4) → rootChar a v = 1 := by
    intro v h01 h13
    rw [rootChar_d4_apply, ha2, one_zpow, mul_one, ← h13, h01, ← mul_zpow, ← mul_zpow, ha013,
      one_zpow]
  have h0 := hchar (d4LatVec 1 0 0 0)
  obtain ⟨hm1, hm2⟩ := d4_weyl_order_three_mod_fixed w hwmem hW3 (d4LatVec 1 0 0 0)
  have hdec : w • d4LatVec 1 0 0 0 =
      d4LatVec 1 0 0 0 + (w • d4LatVec 1 0 0 0 - d4LatVec 1 0 0 0) := by abel
  rw [hdec, rootChar_add, hker _ hm1 hm2, mul_one, rootChar_d4_apply, rootChar_d4_apply] at h0
  simp [d4LatVec, ha'] at h0
  have hδ0 : Units.map δ.toRingHom.toMonoidHom (a (0 : Fin 4)) = a (0 : Fin 4) := h0.symm
  have hσ0 : σU (a (0 : Fin 4)) = a (0 : Fin 4) := by
    rcases hδ with hδ | hδ
    · rw [hδ] at hδ0
      exact hδ0
    · rw [hδ] at hδ0
      refine Units.ext ?_
      have h1 : (σ⁻¹ : K ≃+* K) (a (0 : Fin 4) : K) = (a (0 : Fin 4) : K) :=
        congrArg Units.val hδ0
      change σ (a (0 : Fin 4) : K) = (a (0 : Fin 4) : K)
      rw [RingAut.inv_apply, RingEquiv.symm_apply_eq] at h1
      exact h1.symm
  have h10 : a (1 : Fin 4) = a (0 : Fin 4) := (hcompat (0 : Fin 4)).trans hσ0
  have h30 : a (3 : Fin 4) = a (0 : Fin 4) :=
    (hcompat (1 : Fin 4)).trans ((congrArg σU h10).trans hσ0)
  have hcube : a (0 : Fin 4) ^ 3 = 1 := by
    rw [h10, h30] at ha013
    rw [pow_three']
    exact ha013
  set b0 : Fin TwistTag.D4.tag.rank → Kˣ := ![ω, ω, 1, ω]
  have hpow : ∀ j : ℕ, a (0 : Fin 4) = ω ^ j → c = z ^ j := by
    intro j hj
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, hz, rootDiagUnit_pow, ha]
    congr 1
    funext i
    fin_cases i
    · exact hj
    · exact h10.trans hj
    · exact ha2.trans (one_pow j).symm
    · exact h30.trans hj
  have hmem : ∀ j : ℕ, a (0 : Fin 4) = ω ^ j → c ∈ Subgroup.zpowers z := fun j hj => by
    rw [hpow j hj]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) j
  rcases units_pow_three_eq_one_cases hω3 hω1 hcube with h | h | h
  · exact hmem 0 (by rw [h, pow_zero])
  · exact hmem 1 (by rw [h, pow_one])
  · exact hmem 2 h

end CFSG.GH74.GLS.Stage2.Bender.Thm1

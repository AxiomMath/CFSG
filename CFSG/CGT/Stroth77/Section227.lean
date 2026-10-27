module

public import CFSG.CGT.Stroth77.Section227Sylow
import CFSG.CGT.Stroth77.Section223Family

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace Arch76

theorem two_torsion_eq_w_add_two_nsmul : ∀ u : Co, 2 • u = 0 →
    ∃ (i : Bool) (u₀ : Co), u = (if i then (1, 0, 0) else 0) + 2 • u₀ := by
  decide +kernel

theorem two_nsmul_022 : (2 : ℕ) • ((0, 2, 2) : Co) = 0 := by decide

theorem coord_w_ne_zero : ((1, 0, 0) : Co) ≠ 0 := by decide

end Arch76

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem isConj_w_xy_sq_of_forall (h : F.IsD D dD)
    (hall : ∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
      ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) :
    IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := F.dA.toConfig with hK
  have hev022 : K.ev (0, 2, 2) = (K.x * K.y) ^ 2 := by
    rw [K.xy_sq]
    simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
  have hw1 : K.w ≠ 1 := by rw [← K.ev_w, Ne, K.ev_eq_one_iff]; exact Arch76.coord_w_ne_zero
  have hz2 : ((K.x * K.y) ^ 2) ^ 2 = 1 := by
    rw [← hev022, ← K.ev_nsmul, K.ev_eq_one_iff]; exact Arch76.two_nsmul_022
  have hwV : K.w ∈ omegaIn 1 D := by
    rw [h.omegaIn_one_eq]
    exact mem_omegaIn_one_of_mul_self K.w_mem (by rw [← pow_two, K.hw])
  have hzV : (K.x * K.y) ^ 2 ∈ omegaIn 1 D := by
    rw [h.omegaIn_one_eq, ← hev022]
    exact mem_omegaIn_one_of_mul_self (K.ev_mem _) (by rw [← pow_two, hev022, hz2])
  obtain ⟨g, hg⟩ := hall _ hwV (orderOf_eq_prime K.hw hw1) _ hzV
    (orderOf_eq_prime hz2 (F.xy_sq_ne_one))
  exact isConj_iff.mpr ⟨g, hg.symm⟩

theorem mem_of_t2m1 (h : F.IsD D dD) (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hC : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer (F.A : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
        (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
          x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5))
    {y : G} (hyN : y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))
    (hyw : y * (F.dA.c : G) = (F.dA.c : G) * y)
    (hyc : ∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
      Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) :
    y ∈ D := by
  classical
  set K := F.dA.toConfig with hK
  set W := Subgroup.closure {(F.dA.c : G), (K.x * K.y) ^ 2} with hW
  have hAc : IsMulCommutative F.A := F.dA.isMulCommutative
  have hcommD := h.comm
  have hmn : τ.m < τ.n := by rcases hτ with rfl | rfl <;> decide
  have hev022 : K.ev (0, 2, 2) = (K.x * K.y) ^ 2 := by
    rw [K.xy_sq]
    simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
  have hWV : W ≤ omegaIn 1 F.A := by
    rw [hW, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_omegaIn_one_of_mul_self K.w_mem (by rw [← pow_two]; exact K.hw)
    · rw [← hev022]
      exact mem_omegaIn_one_of_mul_self (K.ev_mem _)
        (by rw [← pow_two, ← K.ev_nsmul, Arch76.two_nsmul_022, K.ev_zero])
  have hsq : ∀ d ∈ D, y * d ^ 2 = d ^ 2 * y := by
    intro d hd
    set k := d⁻¹ * y⁻¹ * d * y with hk
    have hkV := (mem_omegaIn_one_iff hAc).mp (hWV (hyc d hd))
    have hkD : k ∈ D := h.A_le hkV.1
    have h1 : y⁻¹ * d * y = d * k := by rw [hk]; group
    have h2 : y⁻¹ * d ^ 2 * y = d ^ 2 := by
      rw [Arch76.Config.conj_pow_eq, h1, pow_two, pow_two,
        show d * k * (d * k) = d * d * (k * k) by
          rw [mul_assoc d k (d * k), ← mul_assoc k d k, hcommD k hkD d hd]; group,
        hkV.2, mul_one]
    calc y * d ^ 2 = y * (y⁻¹ * d ^ 2 * y) := by rw [h2]
      _ = d ^ 2 * y := by group
  have hyA : y ∈ Subgroup.centralizer (F.A : Set G) := by
    have hAeq := h.A_eq_mho_sup_omegaIn_one hmn
    have hn : τ.n - 2 = 1 := by rcases hτ with rfl | rfl <;> decide
    rw [hn, pow_one] at hAeq
    have hle : F.A ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hAeq]
      refine sup_le (GroupTheory.HuppertProduct.mho_le_of_forall fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hsq d hd).symm) ?_
      intro v hv
      rw [h.omegaIn_one_eq] at hv
      have hv' := (mem_omegaIn_one_iff hAc).mp hv
      obtain ⟨u, rfl⟩ := K.exists_ev hv'.1
      have hu2 : 2 • u = 0 := by rw [← K.ev_eq_one_iff, K.ev_nsmul, pow_two, hv'.2]
      obtain ⟨i, u₀, hu⟩ := Arch76.two_torsion_eq_w_add_two_nsmul u hu2
      rw [hu, K.ev_add, K.ev_nsmul]
      refine mul_mem ?_ (Subgroup.mem_centralizer_singleton_iff.mpr
        (hsq _ (h.A_le (K.ev_mem u₀))).symm)
      cases i
      · simp only [Bool.false_eq_true, ↓reduceIte, K.ev_zero]; exact one_mem _
      · simp only [↓reduceIte]
        rw [K.ev_w]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hyw.symm
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  rcases hC y ⟨hyN, hyA⟩ with htriv | ⟨-, ha, -⟩
  · refine h.mem_of_mem_centralizer hyN.1 (Subgroup.mem_centralizer_iff.mpr fun d hd => ?_)
    calc d * y = y * (y⁻¹ * d * y) := by group
      _ = y * d := by rw [htriv d hd]
  · exfalso
    have hcomm : (dD.a : G)⁻¹ * y⁻¹ * (dD.a : G) * y = (dD.a : G) ^ 4 := by
      rw [mul_assoc ((dD.a : G)⁻¹ * y⁻¹), show (dD.a : G)⁻¹ * y⁻¹ * ((dD.a : G) * y) =
        (dD.a : G)⁻¹ * (y⁻¹ * (dD.a : G) * y) by group, ha]
      group
    have ha4 : (dD.a : G) ^ 4 ∈ W := hcomm ▸ hyc _ dD.a.2
    have hWu : W ≤ Subgroup.centralizer ({F.dA.u} : Set G) := by
      rw [hW, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        calc K.w * F.dA.u = F.dA.u * (F.dA.u⁻¹ * K.w * F.dA.u) := by group
          _ = F.dA.u * K.w := by rw [show F.dA.u⁻¹ * K.w * F.dA.u = K.w from K.hu_w]
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_xy_sq F.u_mem_S).symm
    have hu4 := Subgroup.mem_centralizer_singleton_iff.mp (hWu ha4)
    have hua : dD.u⁻¹ * (dD.a : G) * dD.u = dD.b := by
      have h2 := dD.conj_apply dD.u_mem dD.u_conj Torus.a
      rw [show Additive.toMul (dD.e.symm Torus.a) = dD.a from rfl] at h2
      have h3 : conjBy dD.u_mem dD.a = dD.b := by
        apply Additive.ofMul.injective
        apply dD.e.injective
        rw [h2]
        simp only [StrothWeakTypeData.b, ofMul_toMul, AddEquiv.apply_symm_apply]
        rcases hτ with rfl | rfl <;> decide
      exact congrArg Subtype.val h3
    rw [h.u_eq] at hua
    have hb4 : F.dA.u⁻¹ * (dD.a : G) ^ 4 * F.dA.u = (dD.b : G) ^ 4 := by
      rw [Arch76.Config.conj_pow_eq, hua]
    have hne : ((dD.a : G)) ^ 4 ≠ ((dD.b : G)) ^ 4 := by
      intro heq
      have h1 : (dD.a ^ 4 : D) = dD.b ^ 4 := Subtype.ext (by simpa using heq)
      have h2 := congrArg (fun x : D => dD.e (Additive.ofMul x)) h1
      simp only [ofMul_pow, map_nsmul, StrothWeakTypeData.a, StrothWeakTypeData.b, ofMul_toMul,
        AddEquiv.apply_symm_apply] at h2
      rcases hτ with rfl | rfl <;> exact absurd h2 (by decide)
    apply hne
    rw [← hb4]
    calc (dD.a : G) ^ 4 = F.dA.u⁻¹ * (F.dA.u * (dD.a : G) ^ 4) := by group
      _ = F.dA.u⁻¹ * ((dD.a : G) ^ 4 * F.dA.u) := by rw [← hu4]
      _ = F.dA.u⁻¹ * (dD.a : G) ^ 4 * F.dA.u := by group

end StrothFrame.IsD

theorem h227plus_of_h226ac_of_ni_of_t2m1
    (h226ac : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D' → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D' → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n)
    (hNI : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      τ.m ≠ τ.n → τ ≠ .t200 1 → τ ≠ .t201 1 →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D)
    (hNI₅ : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      (τ = .t200 1 ∨ τ = .t201 1) →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n := by
  intro G _ _ F D τ dD h hns hall
  by_contra hmn
  have hmn' : τ.m < τ.n := lt_of_le_of_ne (StrothTypeIndex.k_zero_le_k_one τ) hmn
  have hw := h.isConj_w_xy_sq_of_forall hall
  rcases h.good_or_bad hmn' hns hw with ⟨B, hB, hBn, hBD, hBc⟩ | ⟨y, hyN, hy2, hyD, hyw, hyc⟩
  · exact hmn (h226ac F D τ dD B h hns hall hB hBn hBD hBc)
  · by_cases ht : τ = .t200 1 ∨ τ = .t201 1
    · exact hyD (hNI₅ F D τ dD h ht hns y hyN hy2 hyw hyc)
    · push Not at ht
      exact hyD (hNI F D τ dD h hns hmn ht.1 ht.2 y hyN hy2 hyw hyc)

theorem h227plus_of_h226ac_of_ni
    (h226ac : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D' → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D' → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n)
    (hNI : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) → τ.m ≠ τ.n →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n :=
  h227plus_of_h226ac_of_ni_of_t2m1 h226ac
    (fun F D τ dD h hns hmn _ _ => hNI F D τ dD h hns hmn)
    (fun F D τ dD h hτ hns => hNI F D τ dD h hns (by rcases hτ with rfl | rfl <;> decide))

theorem h227plus_of_h226_of_ni
    (h226 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n)
    (hNI : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) → τ.m ≠ τ.n →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n :=
  h227plus_of_h226ac_of_ni (fun F D' τ' dD' B h hns _ => h226 F D' τ' dD' B h hns) hNI

end CFSG.CGT.Stroth77

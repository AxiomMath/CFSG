module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviTori
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotFieldNormalizeNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section TorusDecomp

variable {k : Type} [Field k]

theorem f4Cartan_values :
    Tag.F4.cartan 0 0 = 2 ∧ Tag.F4.cartan 0 1 = -1 ∧ Tag.F4.cartan 0 2 = 0 ∧
    Tag.F4.cartan 0 3 = 0 ∧ Tag.F4.cartan 1 0 = -1 ∧ Tag.F4.cartan 1 1 = 2 ∧
    Tag.F4.cartan 1 2 = -1 ∧ Tag.F4.cartan 1 3 = 0 ∧ Tag.F4.cartan 2 0 = 0 ∧
    Tag.F4.cartan 2 1 = -2 ∧ Tag.F4.cartan 2 2 = 2 ∧ Tag.F4.cartan 2 3 = -1 ∧
    Tag.F4.cartan 3 0 = 0 ∧ Tag.F4.cartan 3 1 = 0 ∧ Tag.F4.cartan 3 2 = -1 ∧
    Tag.F4.cartan 3 3 = 2 := by
  decide

theorem fin_F4_cases (i : Fin (Tag.rank .F4)) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> decide

theorem tuple_eq_X {b : Fin (Tag.rank .F4) → kˣ} {c₁ c₂ c₃ : kˣ} (h₁ : c₁ ^ 2 = b 1)
    (h₂ : c₂ ^ 2 = b 2) (h₃ : c₃ ^ 2 = b 3) :
    b = Pi.mulSingle 0 (b 0 * (c₁ ^ 3 * c₂ ^ 4 * c₃ ^ 2)) *
      (fun i => (c₁ ^ 3 * c₂ ^ 4 * c₃ ^ 2) ^ Tag.F4.cartan 1 i) *
      (fun i => (c₁ ^ 2 * c₂ ^ 4 * c₃ ^ 2) ^ Tag.F4.cartan 2 i) *
      (fun i => (c₁ * c₂ ^ 2 * c₃ ^ 2) ^ Tag.F4.cartan 3 i) := by
  obtain ⟨-, -, -, -, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩ :=
    f4Cartan_values
  funext i
  rcases fin_F4_cases i with rfl | rfl | rfl | rfl
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_same, a10, a20, a30]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (1 : Fin (Tag.rank .F4)) ≠ 0 by decide),
      a11, a21, a31, ← h₁]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (2 : Fin (Tag.rank .F4)) ≠ 0 by decide),
      a12, a22, a32, ← h₂]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (3 : Fin (Tag.rank .F4)) ≠ 0 by decide),
      a13, a23, a33, ← h₃]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp

theorem tuple_eq_Y {b : Fin (Tag.rank .F4) → kˣ} {c₀ c₁ c₂ : kˣ} (h₀ : c₀ ^ 2 = b 0)
    (h₁ : c₁ ^ 2 = b 1) (h₂ : c₂ ^ 2 = b 2) :
    b = Pi.mulSingle 3 (b 3 * (c₀ * c₁ ^ 2 * c₂ ^ 3)) *
      (fun i => (c₀ ^ 2 * c₁ ^ 2 * c₂ ^ 2) ^ Tag.F4.cartan 0 i) *
      (fun i => (c₀ ^ 2 * c₁ ^ 4 * c₂ ^ 4) ^ Tag.F4.cartan 1 i) *
      (fun i => (c₀ * c₁ ^ 2 * c₂ ^ 3) ^ Tag.F4.cartan 2 i) := by
  obtain ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, -, -, -, -⟩ :=
    f4Cartan_values
  funext i
  rcases fin_F4_cases i with rfl | rfl | rfl | rfl
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (0 : Fin (Tag.rank .F4)) ≠ 3 by decide),
      a00, a10, a20, ← h₀]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (1 : Fin (Tag.rank .F4)) ≠ 3 by decide),
      a01, a11, a21, ← h₁]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne (show (2 : Fin (Tag.rank .F4)) ≠ 3 by decide),
      a02, a12, a22, ← h₂]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
  · simp only [Pi.mul_apply, Pi.mulSingle_eq_same, a03, a13, a23]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
    field_simp


theorem weylElt_one_mul_rootDiagUnit_mul_inv {τ : Tag} (a : Fin τ.rank → kˣ) (i : Fin τ.rank) :
    weylElt τ k i 1 * rootDiagUnit τ a * (weylElt τ k i 1)⁻¹ =
      rootDiagUnit τ (fun j => a j * a i ^ (-τ.cartan i j)) := by
  have h := rootDiagUnit_conj_weylElt_one (K := k) a i
  have h2 : weylElt τ k i 1 * rootDiagUnit τ a * (weylElt τ k i 1)⁻¹ =
      (torusElt τ k i (a i))⁻¹ * rootDiagUnit τ a := by
    rw [eq_inv_mul_iff_mul_eq]
    calc torusElt τ k i (a i) * (weylElt τ k i 1 * rootDiagUnit τ a * (weylElt τ k i 1)⁻¹) =
        (rootDiagUnit τ a * weylElt τ k i 1 * (rootDiagUnit τ a)⁻¹) *
          rootDiagUnit τ a * (weylElt τ k i 1)⁻¹ := by rw [h]; group
      _ = rootDiagUnit τ a := by group
  rw [h2, torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  rw [mul_comm]

theorem exists_weylElt_one_inv_mul_rootDiagUnit_mul {τ : Tag} (b : Fin τ.rank → kˣ)
    (i : Fin τ.rank) :
    ∃ b' : Fin τ.rank → kˣ, (weylElt τ k i 1)⁻¹ * rootDiagUnit τ b * weylElt τ k i 1 =
      rootDiagUnit τ b' := by
  refine ⟨fun j => b j * b i ^ (-τ.cartan i j), ?_⟩
  have h := weylElt_one_mul_rootDiagUnit_mul_inv (fun j => b j * b i ^ (-τ.cartan i j)) i
  have hb : (fun j => (fun j => b j * b i ^ (-τ.cartan i j)) j *
      (fun j => b j * b i ^ (-τ.cartan i j)) i ^ (-τ.cartan i j)) = b := by
    funext j
    simp only [Tag.cartan_self]
    group
  rw [hb] at h
  rw [← h]
  group

theorem coe_n1242_eq_mul : (n1242 k : ModGL .F4 k) = weylElt .F4 k 1 1 * weylElt .F4 k 0 1 := by
  rw [coe_n1242]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem exists_n1242_inv_mul_rootDiagUnit_mul (b : Fin (Tag.rank .F4) → kˣ) :
    ∃ b' : Fin (Tag.rank .F4) → kˣ, (n1242 k : ModGL .F4 k)⁻¹ * rootDiagUnit .F4 b *
      (n1242 k : ModGL .F4 k) = rootDiagUnit .F4 b' := by
  obtain ⟨b₁, hb₁⟩ := exists_weylElt_one_inv_mul_rootDiagUnit_mul b 1
  obtain ⟨b₂, hb₂⟩ := exists_weylElt_one_inv_mul_rootDiagUnit_mul b₁ 0
  refine ⟨b₂, ?_⟩
  rw [coe_n1242_eq_mul, ← hb₂, ← hb₁]
  group

theorem torusElt_mem_neighbourLevi
    {N : AmalgamNeighbour} {j : Fin (Tag.rank .F4)} (hj : j ∈ N.nodes) (μ : kˣ) :
    torusElt .F4 k j μ ∈ (N.levi k).map (adjointGroup .F4 k).subtype := by
  have h1 : rootSubgroup .F4 k (Pi.single j 1) ⊔ rootSubgroup .F4 k (-Pi.single j 1) ≤
      rootSpan .F4 k (amalgamRoots {j}) := by
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ amalgamRoots {j}) => rootSubgroup .F4 k β)
        (Pi.single j 1) ⟨j, Finset.mem_singleton_self j, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ amalgamRoots {j}) => rootSubgroup .F4 k β)
        (-Pi.single j 1) ⟨j, Finset.mem_singleton_self j, Or.inr rfl⟩ le_rfl
  rw [← map_subtype_levi_f4Datum] at h1
  exact map_mono (levi_le_neighbourLevi (Finset.singleton_subset_iff.2 hj))
    (h1 (torusElt_mem_rootPair j μ))

end TorusDecomp

section Neighbour


variable {k K : Type} [Field k] [Field K]

theorem map_subtype_levi (N : AmalgamNeighbour) :
    (N.levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K (orthRoots N.root) := by
  rw [AmalgamNeighbour.levi_eq, subgroupOf_map_subtype,
    inf_of_le_left (rootSpan_le_adjointGroup_F4 _)]

theorem mem_levi_of_coe_mem {N : AmalgamNeighbour} {g : adjointGroup .F4 K}
    (h : (g : ModGL .F4 K) ∈ (N.levi K).map (adjointGroup .F4 K).subtype) : g ∈ N.levi K := by
  obtain ⟨y, hy, hyg⟩ := h
  rwa [show y = g from Subtype.ext hyg] at hy

section Centralize


theorem levi_le_centralizer_torus (N : AmalgamNeighbour) :
    (N.levi K).map (adjointGroup .F4 K).subtype ≤
      centralizer (N.torus K : Set (ModGL .F4 K)) := by
  have hX : (C3Levi K).map (adjointGroup .F4 K).subtype ≤
      centralizer (torusLineR K : Set (ModGL .F4 K)) := by
    rw [map_subtype_C3Levi, torusLineR_eq_leviTorus]
    refine rootSpan_le_centralizer_leviTorus fun γ hγ => ⟨(mem_c3LeviRoots.1 hγ).1, fun i hi => ?_⟩
    rcases fin_F4_cases i with rfl | rfl | rfl | rfl
    · exact (mem_c3LeviRoots.1 hγ).2
    all_goals exact absurd (by decide) hi
  cases N
  · exact hX
  · change (B3Levi K).map (adjointGroup .F4 K).subtype ≤
      centralizer (torusLineS K : Set (ModGL .F4 K))
    rw [B3Levi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_F4 _), torusLineS]
    refine rootSpan_le_centralizer_leviTorus fun γ hγ => ⟨(mem_b3LeviRoots.1 hγ).1, fun i hi => ?_⟩
    rcases fin_F4_cases i with rfl | rfl | rfl | rfl
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact (mem_b3LeviRoots.1 hγ).2
  · change (C3Levi1242 K).map (adjointGroup .F4 K).subtype ≤
      centralizer (torusLine1242 K : Set (ModGL .F4 K))
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_conj_n1242_C3Levi] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have hc := mem_centralizer_iff.1 (hX ⟨y, hy, rfl⟩) t ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype, coe_mul, coe_inv]
    calc (n1242 K : ModGL .F4 K) * t * (n1242 K : ModGL .F4 K)⁻¹ *
          ((n1242 K : ModGL .F4 K) * y * (n1242 K : ModGL .F4 K)⁻¹) =
        (n1242 K : ModGL .F4 K) * (t * y) * (n1242 K : ModGL .F4 K)⁻¹ := by group
      _ = (n1242 K : ModGL .F4 K) * (y * t) * (n1242 K : ModGL .F4 K)⁻¹ := by
          rw [show t * (y : ModGL .F4 K) = y * t from hc]
      _ = _ := by group

end Centralize


theorem baseChangeGL_weylElt_one_eq (ι : k →+* K) (i : Fin (Tag.rank .F4)) :
    baseChangeGL ι (weylElt .F4 k i 1) = weylElt .F4 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit,
    CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem baseChangeGL_n1242 (ι : k →+* K) :
    baseChangeGL ι (n1242 k : ModGL .F4 k) = (n1242 K : ModGL .F4 K) := by
  rw [coe_n1242_eq_mul, coe_n1242_eq_mul, map_mul, baseChangeGL_weylElt_one_eq,
    baseChangeGL_weylElt_one_eq]

theorem baseChangeGL_mem_leviTorus (ι : k →+* K) {J : Finset (Fin (Tag.rank .F4))}
    {d : ModGL .F4 k} (hd : d ∈ leviTorus k J) : baseChangeGL ι d ∈ leviTorus K J := by
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hd
  rw [baseChangeGL_rootDiagUnit_eq_map]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [hb j hj, map_one]

theorem baseChangeGL_mem_torus (ι : k →+* K) (N : AmalgamNeighbour) {d : ModGL .F4 k}
    (hd : d ∈ N.torus k) : baseChangeGL ι d ∈ N.torus K := by
  cases N
  · change d ∈ torusLineR k at hd
    change baseChangeGL ι d ∈ torusLineR K
    rw [torusLineR_eq_leviTorus] at hd ⊢
    exact baseChangeGL_mem_leviTorus ι hd
  · exact baseChangeGL_mem_leviTorus ι hd
  · obtain ⟨t, ht, rfl⟩ := hd
    refine ⟨baseChangeGL ι t, ?_, ?_⟩
    · rw [torusLineR_eq_leviTorus] at ht ⊢
      exact baseChangeGL_mem_leviTorus ι ht
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
        baseChangeGL_n1242]

theorem baseChangeGL_mem_map_levi (ι : k →+* K) (N : AmalgamNeighbour) {g : ModGL .F4 k}
    (hg : g ∈ (N.levi k).map (adjointGroup .F4 k).subtype) :
    baseChangeGL ι g ∈ (N.levi K).map (adjointGroup .F4 K).subtype := by
  rw [map_subtype_levi] at hg ⊢
  exact map_rootSpan_baseChangeGL_le ι _ ⟨g, hg, rfl⟩

section Decomp


variable (k) in
theorem exists_eq_mul_of_rootDiagUnit_X [Finite k] [CharP k 2] (b : Fin (Tag.rank .F4) → kˣ) :
    ∃ d₁ ∈ AmalgamNeighbour.X.torus k, ∃ d₂ ∈ (AmalgamNeighbour.X.levi k).map
      (adjointGroup .F4 k).subtype, rootDiagUnit .F4 b = d₁ * d₂ := by
  have hk : ringChar k = 2 := ringChar.eq k 2
  obtain ⟨c₁, h₁⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 1)
  obtain ⟨c₂, h₂⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 2)
  obtain ⟨c₃, h₃⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 3)
  refine ⟨rootDiagUnit .F4 (Pi.mulSingle 0 (b 0 * (c₁ ^ 3 * c₂ ^ 4 * c₃ ^ 2))), ?_,
    torusElt .F4 k 1 (c₁ ^ 3 * c₂ ^ 4 * c₃ ^ 2) * torusElt .F4 k 2 (c₁ ^ 2 * c₂ ^ 4 * c₃ ^ 2) *
      torusElt .F4 k 3 (c₁ * c₂ ^ 2 * c₃ ^ 2), ?_, ?_⟩
  · change _ ∈ torusLineR k
    rw [torusLineR_eq_leviTorus]
    refine rootDiagUnit_mem_leviTorus fun j hj => Pi.mulSingle_eq_of_ne ?_ _
    rintro rfl
    exact absurd hj (by decide)
  · exact mul_mem (mul_mem (torusElt_mem_neighbourLevi (by decide) _)
      (torusElt_mem_neighbourLevi (by decide) _))
      (torusElt_mem_neighbourLevi (by decide) _)
  · conv_lhs => rw [tuple_eq_X h₁ h₂ h₃]
    simp only [torusElt_eq_rootDiagUnit, rootDiagUnit_mul, mul_assoc]

variable (k) in
theorem exists_eq_mul_of_rootDiagUnit_Y [Finite k] [CharP k 2] (b : Fin (Tag.rank .F4) → kˣ) :
    ∃ d₁ ∈ AmalgamNeighbour.Y.torus k, ∃ d₂ ∈ (AmalgamNeighbour.Y.levi k).map
      (adjointGroup .F4 k).subtype, rootDiagUnit .F4 b = d₁ * d₂ := by
  have hk : ringChar k = 2 := ringChar.eq k 2
  obtain ⟨c₀, h₀⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 0)
  obtain ⟨c₁, h₁⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 1)
  obtain ⟨c₂, h₂⟩ := exists_sq_eq_of_ringChar_eq_two hk (b 2)
  refine ⟨rootDiagUnit .F4 (Pi.mulSingle 3 (b 3 * (c₀ * c₁ ^ 2 * c₂ ^ 3))), ?_,
    torusElt .F4 k 0 (c₀ ^ 2 * c₁ ^ 2 * c₂ ^ 2) * torusElt .F4 k 1 (c₀ ^ 2 * c₁ ^ 4 * c₂ ^ 4) *
      torusElt .F4 k 2 (c₀ * c₁ ^ 2 * c₂ ^ 3), ?_, ?_⟩
  · change _ ∈ leviTorus k {0, 1, 2}
    refine rootDiagUnit_mem_leviTorus fun j hj => Pi.mulSingle_eq_of_ne ?_ _
    rintro rfl
    exact absurd hj (by decide)
  · exact mul_mem (mul_mem (torusElt_mem_neighbourLevi (by decide) _)
      (torusElt_mem_neighbourLevi (by decide) _))
      (torusElt_mem_neighbourLevi (by decide) _)
  · conv_lhs => rw [tuple_eq_Y h₀ h₁ h₂]
    simp only [torusElt_eq_rootDiagUnit, rootDiagUnit_mul, mul_assoc]

theorem exists_eq_mul_of_rootDiagUnit [Finite k] [CharP k 2] (N : AmalgamNeighbour)
    (b : Fin (Tag.rank .F4) → kˣ) :
    ∃ d₁ ∈ N.torus k, ∃ d₂ ∈ (N.levi k).map (adjointGroup .F4 k).subtype,
      rootDiagUnit .F4 b = d₁ * d₂ := by
  cases N
  · exact exists_eq_mul_of_rootDiagUnit_X k b
  · exact exists_eq_mul_of_rootDiagUnit_Y k b
  · obtain ⟨b', hb'⟩ := exists_n1242_inv_mul_rootDiagUnit_mul (k := k) b
    obtain ⟨d₁, hd₁, _, ⟨x, hx, rfl⟩, he⟩ := exists_eq_mul_of_rootDiagUnit_X k b'
    refine ⟨(n1242 k : ModGL .F4 k) * d₁ * (n1242 k : ModGL .F4 k)⁻¹, ⟨d₁, hd₁, rfl⟩,
      (((n1242 k * x * (n1242 k)⁻¹ : adjointGroup .F4 k)) : ModGL .F4 k), ?_, ?_⟩
    · refine ⟨n1242 k * x * (n1242 k)⁻¹, ?_, rfl⟩
      change _ ∈ C3Levi1242 k
      rw [← map_conj_n1242_C3Levi]
      exact ⟨x, hx, rfl⟩
    · have h1 : rootDiagUnit .F4 b = (n1242 k : ModGL .F4 k) *
          ((n1242 k : ModGL .F4 k)⁻¹ * rootDiagUnit .F4 b * (n1242 k : ModGL .F4 k)) *
            (n1242 k : ModGL .F4 k)⁻¹ := by group
      rw [h1, hb', he]
      simp only [coe_subtype, coe_mul, coe_inv]
      group

end Decomp

end Neighbour

section Inclusion


variable {k K : Type} [Field k] [Field K]

@[expose] noncomputable def leviBaseChange (ι : k →+* K) (N : AmalgamNeighbour) :
    N.levi k →* N.levi K :=
  (((baseChangeGL ι).comp ((adjointGroup .F4 k).subtype.comp (N.levi k).subtype)).codRestrict
      (adjointGroup .F4 K) fun g =>
        map_subtype_le _ (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)).codRestrict
    (N.levi K) fun g => mem_levi_of_coe_mem (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)

theorem coe_leviBaseChange (ι : k →+* K) (N : AmalgamNeighbour) (x : N.levi k) :
    (((leviBaseChange ι N x : N.levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL ι ((x : adjointGroup .F4 k) : ModGL .F4 k) :=
  rfl

theorem leviBaseChange_injective (ι : k →+* K) (N : AmalgamNeighbour) :
    Function.Injective (leviBaseChange ι N) := fun _ _ h => Subtype.ext (Subtype.ext
  (baseChangeGL_injective ι (congrArg (fun x : N.levi K => ((x : adjointGroup .F4 K) :
    ModGL .F4 K)) h)))

variable (σ : K ≃+* K)

@[expose] noncomputable def leviInclusion (N : AmalgamNeighbour) :
    N.levi (fixSubfield σ) →* N.levi K :=
  leviBaseChange (fixSubfield σ).subtype N

theorem coe_leviInclusion (N : AmalgamNeighbour) (x : N.levi (fixSubfield σ)) :
    (((leviInclusion σ N x : N.levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype ((x : adjointGroup .F4 (fixSubfield σ)) :
        ModGL .F4 (fixSubfield σ)) :=
  rfl

variable {G : Type} [Group G] {L : Subgroup G} (e : L ≃* adjointGroup .F4 (fixSubfield σ))

structure FieldNeighbourIso (N : AmalgamNeighbour) where
  Φ : N.levi K ≃* neighbourCore e N
  fix : ∀ x : N.levi (fixSubfield σ), ((Φ (leviInclusion σ N x) : neighbourCore e N) : G) =
    ((e.symm (x : adjointGroup .F4 (fixSubfield σ)) : L) : G)

end Inclusion

section Equivariance


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem FieldNeighbourIso.map_conj [Finite K] [CharP K 2] {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .F4 (fixSubfield σ)}
    (hd : (d : ModGL .F4 (fixSubfield σ)) ∈ leviTorus (fixSubfield σ) ∅) {x y : N.levi K}
    (hy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ)) *
        ((x : adjointGroup .F4 K) : ModGL .F4 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ)))⁻¹) :
    ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ := by
  obtain ⟨b, -, hb⟩ := mem_leviTorus.1 hd
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_rootDiagUnit N b
  rw [hb] at he
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hι₁ := baseChangeGL_mem_torus (fixSubfield σ).subtype N hd₁
  have hc₁ : ∀ z : N.levi K, Commute (baseChangeGL (fixSubfield σ).subtype d₁)
      ((z : adjointGroup .F4 K) : ModGL .F4 K) := by
    intro z
    have hz : ((z : adjointGroup .F4 K) : ModGL .F4 K) ∈
        (N.levi K).map (adjointGroup .F4 K).subtype := ⟨z, z.2, rfl⟩
    exact mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hι₁
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = leviInclusion σ N ⟨x₂, hx₂⟩ := ⟨_, rfl⟩
  have hξc : ((ξ : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .F4 (fixSubfield σ)) := by
    rw [hξ]
    rfl
  have hy' : y = ξ * x * ξ⁻¹ := by
    refine Subtype.ext (Subtype.ext ?_)
    show ((y : adjointGroup .F4 K) : ModGL .F4 K) = ((ξ : adjointGroup .F4 K) : ModGL .F4 K) *
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * (((ξ : adjointGroup .F4 K) : ModGL .F4 K))⁻¹
    have hcomm := ((hc₁ ξ).mul_right (hc₁ x)).mul_right (hc₁ ξ).inv_right
    rw [hy, he, map_mul, ← hξc]
    calc baseChangeGL (fixSubfield σ).subtype d₁ * ((ξ : adjointGroup .F4 K) : ModGL .F4 K) *
          ((x : adjointGroup .F4 K) : ModGL .F4 K) *
            (baseChangeGL (fixSubfield σ).subtype d₁ *
              ((ξ : adjointGroup .F4 K) : ModGL .F4 K))⁻¹ =
        baseChangeGL (fixSubfield σ).subtype d₁ * (((ξ : adjointGroup .F4 K) : ModGL .F4 K) *
          ((x : adjointGroup .F4 K) : ModGL .F4 K) * (((ξ : adjointGroup .F4 K) :
            ModGL .F4 K))⁻¹) * (baseChangeGL (fixSubfield σ).subtype d₁)⁻¹ := by group
      _ = _ := by rw [hcomm.eq, mul_inv_cancel_right]
  have hd₁G := symm_mem_modelToG e (x := ⟨d₁, N.torus_le_adjointGroup hd₁⟩) hd₁
  have hc₂ : ∀ z : neighbourCore e N, Commute
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) (z : G) := by
    intro z
    exact mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ z.2) _ hd₁G
  have hfix : ((h.Φ ξ : neighbourCore e N) : G) = ((e.symm x₂ : L) : G) := by
    rw [hξ]
    exact h.fix ⟨x₂, hx₂⟩
  have hΦy : ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm x₂ : L) : G) * (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹ := by
    rw [hy', map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, hfix]
  have hcomm := ((hc₂ (h.Φ ξ)).mul_right (hc₂ (h.Φ x))).mul_right (hc₂ (h.Φ ξ)).inv_right
  rw [hfix] at hcomm
  rw [hΦy, hdd, map_mul, L.coe_mul]
  calc ((e.symm x₂ : L) : G) * (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹ =
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) * (((e.symm x₂ : L) : G) *
        (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹) *
          ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G)⁻¹ := by
        rw [hcomm.eq, mul_inv_cancel_right]
    _ = _ := by group

theorem FieldNeighbourIso.map_conj_rootDiagUnit [Finite K] [CharP K 2] {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (b : Fin (Tag.rank .F4) → (fixSubfield σ)ˣ) {x y : N.levi K}
    (hy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      rootDiagUnit .F4 (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (b i)) *
        ((x : adjointGroup .F4 K) : ModGL .F4 K) *
          (rootDiagUnit .F4 (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (b i)))⁻¹) :
    ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm ⟨rootDiagUnit .F4 b, f4RootDiagUnit_mem_adjointGroup b⟩ : L) : G) * (h.Φ x : G) *
        ((e.symm ⟨rootDiagUnit .F4 b, f4RootDiagUnit_mem_adjointGroup b⟩ : L) : G)⁻¹ := by
  refine h.map_conj (rootDiagUnit_mem_leviTorus fun j hj => absurd hj (Finset.notMem_empty j)) ?_
  rw [hy]
  change _ = baseChangeGL (fixSubfield σ).subtype (rootDiagUnit .F4 b) * _ *
    (baseChangeGL (fixSubfield σ).subtype (rootDiagUnit .F4 b))⁻¹
  rw [baseChangeGL_rootDiagUnit_eq_map]


theorem baseChangeGL_conj_mem_map_levi {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (N : AmalgamNeighbour) {d : ModGL .F4 k} (hd : d ∈ leviTorus k ∅)
    {g : ModGL .F4 K} (hg : g ∈ (N.levi K).map (adjointGroup .F4 K).subtype) :
    baseChangeGL ι d * g * (baseChangeGL ι d)⁻¹ ∈ (N.levi K).map (adjointGroup .F4 K).subtype := by
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hd
  obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := exists_eq_mul_of_rootDiagUnit N b
  have hι₁ := baseChangeGL_mem_torus ι N hd₁
  have hι₂ := baseChangeGL_mem_map_levi ι N hd₂
  have hc : Commute (baseChangeGL ι d₁) (baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹) :=
    mem_centralizer_iff.1 (levi_le_centralizer_torus N
      (mul_mem (mul_mem hι₂ hg) (inv_mem hι₂))) _ hι₁
  have h1 : baseChangeGL ι (rootDiagUnit .F4 b) * g * (baseChangeGL ι (rootDiagUnit .F4 b))⁻¹ =
      baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹ := by
    rw [he, map_mul]
    calc baseChangeGL ι d₁ * baseChangeGL ι d₂ * g * (baseChangeGL ι d₁ * baseChangeGL ι d₂)⁻¹ =
        baseChangeGL ι d₁ * (baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹) *
          (baseChangeGL ι d₁)⁻¹ := by group
      _ = _ := by rw [hc.eq, mul_inv_cancel_right]
  rw [h1]
  exact mul_mem (mul_mem hι₂ hg) (inv_mem hι₂)

theorem FieldNeighbourIso.commute_iff [Finite K] [CharP K 2] {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .F4 (fixSubfield σ)}
    (hd : (d : ModGL .F4 (fixSubfield σ)) ∈ leviTorus (fixSubfield σ) ∅) (x : N.levi K) :
    Commute ((h.Φ x : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .F4 K) : ModGL .F4 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ))) := by
  have hmem := baseChangeGL_conj_mem_map_levi (fixSubfield σ).subtype N hd
    (g := ((x : adjointGroup .F4 K) : ModGL .F4 K)) ⟨x, x.2, rfl⟩
  obtain ⟨y₀, hy₀, hy₀e⟩ := hmem
  set y : N.levi K := ⟨y₀, hy₀⟩ with hydef
  have hy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ)) *
        ((x : adjointGroup .F4 K) : ModGL .F4 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ)))⁻¹ := hy₀e
  have hΦ := h.map_conj hd hy
  constructor
  · intro hc
    have h1 : ((h.Φ y : neighbourCore e N) : G) = (h.Φ x : G) := by
      rw [hΦ, ← hc.eq, mul_inv_cancel_right]
    have h2 : y = x := h.Φ.injective (Subtype.ext h1)
    have h3 : ((y : adjointGroup .F4 K) : ModGL .F4 K) = ((x : adjointGroup .F4 K) : ModGL .F4 K) :=
      by rw [h2]
    rw [hy, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · intro hc
    have h1 : y = x := by
      refine Subtype.ext (Subtype.ext ?_)
      show ((y : adjointGroup .F4 K) : ModGL .F4 K) = ((x : adjointGroup .F4 K) : ModGL .F4 K)
      rw [hy, ← hc.eq, mul_inv_cancel_right]
    rw [h1] at hΦ
    have h2 : ((e.symm d : L) : G) * (h.Φ x : G) = (h.Φ x : G) * ((e.symm d : L) : G) := by
      calc ((e.symm d : L) : G) * (h.Φ x : G) =
          ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ *
            ((e.symm d : L) : G) := by group
        _ = _ := by rw [← hΦ]
    exact h2.symm

end Equivariance

end CFSG.SeitzReduction.F4Pilot

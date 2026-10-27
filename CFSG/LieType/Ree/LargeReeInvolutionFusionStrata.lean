module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords
public import CFSG.LieType.Ree.ReeGenericPerfect

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)

section Classes

variable {G : Type*} [Group G]

theorem ncard_uClass_mul_card (P : Subgroup G) [Finite P] (g : G) :
    {y | ∃ x ∈ P, x * g * x⁻¹ = y}.ncard * Nat.card (P ⊓ Subgroup.centralizer {g} : Subgroup G) =
      Nat.card P := by
  let _ : MulAction P G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp P.subtype)
  have hsmul : ∀ (x : P) (y : G), x • y = (x : G) * y * (x : G)⁻¹ := fun x y =>
    ConjAct.toConjAct_smul (x : G) y
  have horb : MulAction.orbit P g = {y | ∃ x ∈ P, x * g * x⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x g).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ g⟩
  have hstab : MulAction.stabilizer P g = (Subgroup.centralizer {g}).subgroupOf P := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer P g).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

end Classes

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (m K) in
abbrev uClass
    (g : ModGL F4.tag K) : Set (ModGL F4.tag K) :=
  {y | ∃ u ∈ F4.reeFixedPosUnipotent K m, u * g * u⁻¹ = y}

theorem ncard_uClass
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K} {k : ℕ}
    (hk : k ≤ 12)
    (hC : Nat.card (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {g} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ k) :
    (uClass m K g).ncard = (2 ^ (2 * m + 1)) ^ (12 - k) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have h := ncard_uClass_mul_card (F4.reeFixedPosUnipotent K m) g
  rw [hC, card_reeFixedPosUnipotent hK] at h
  have e : (2 ^ (2 * m + 1)) ^ 12 = (2 ^ (2 * m + 1)) ^ (12 - k) * (2 ^ (2 * m + 1)) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem uClass_subset
    (g : ModGL F4.tag K) (hg : g ∈ F4.reeFixedPosUnipotent K m) :
    uClass m K g ⊆ (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) := by
  rintro _ ⟨u, hu, rfl⟩
  exact mul_mem (mul_mem hu hg) (inv_mem hu)

theorem conj_sq_eq_one {G : Type*} [Group G] {u g : G} (hg : g ^ 2 = 1) :
    (u * g * u⁻¹) ^ 2 = 1 := by
  rw [sq] at hg ⊢
  calc u * g * u⁻¹ * (u * g * u⁻¹) = u * (g * g) * u⁻¹ := by group
    _ = 1 := by rw [hg, mul_one, mul_inv_cancel]

@[expose] def stratumOneVec (m : ℕ) (y : Fin 6 → K) : Fin 12 → K :=
  ![1, 0, 0, y 0, y 1, y 2,
    (y 2 + y 0 * largeReeSigma m (y 0)) * largeReeSigma m (y 2 + y 0 * largeReeSigma m (y 0)) +
      y 2 * y 4 + y 1 * (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)) +
      y 0 * y 5 + y 0 * y 2 * (y 2 + y 0 * largeReeSigma m (y 0)) +
      y 2 * (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)) +
      y 2 * largeReeSigma m (y 2) +
      y 0 * largeReeSigma m (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)),
    y 2 + y 0 * largeReeSigma m (y 0), y 3,
    y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2), y 4, y 5]

theorem stratumOne_eq_range
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    {x : Fin 12 → K | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1} = Set.range (stratumOneVec (K := K) m) := by
  ext x
  constructor
  · rintro ⟨h0, hsq⟩
    have hsq' : sylowV m K 1 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
        (x 11) ^ 2 = 1 := by
      rw [← h0]
      exact hsq
    obtain ⟨h1, h2, h7, h9, h6⟩ := (sylowV_one_sq_eq_one_iff hK _ _ _ _ _ _ _ _ _ _ _).1 hsq'
    refine ⟨![x 3, x 4, x 5, x 8, x 10, x 11], funext fun i => ?_⟩
    fin_cases i <;> simp [stratumOneVec, h0, h1, h2, h6, h7, h9]
  · rintro ⟨y, rfl⟩
    refine ⟨by simp [stratumOneVec], ?_⟩
    have e : sylowVec m K (stratumOneVec m y) = sylowV m K 1 0 0 (y 0) (y 1) (y 2)
        ((y 2 + y 0 * largeReeSigma m (y 0)) * largeReeSigma m (y 2 + y 0 * largeReeSigma m (y 0)) +
          y 2 * y 4 + y 1 * (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)) +
          y 0 * y 5 + y 0 * y 2 * (y 2 + y 0 * largeReeSigma m (y 0)) +
          y 2 * (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)) +
          y 2 * largeReeSigma m (y 2) +
          y 0 * largeReeSigma m (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)))
        (y 2 + y 0 * largeReeSigma m (y 0)) (y 3)
        (y 0 * (y 2 + y 0 * largeReeSigma m (y 0)) + largeReeSigma m (y 2)) (y 4) (y 5) := by
      simp [sylowVec, stratumOneVec]
    rw [e, sylowV_one_sq_eq_one_iff hK]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Finite K] [CharP K F4.prime] in
theorem stratumOneVec_injective : Function.Injective (stratumOneVec (K := K) m) := by
  intro y y' h
  funext i
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h8 := congrFun h 8
  have h10 := congrFun h 10
  have h11 := congrFun h 11
  simp only [stratumOneVec] at h3 h4 h5 h8 h10 h11
  simp at h3 h4 h5 h8 h10 h11
  fin_cases i <;> assumption

theorem ncard_stratumOne
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (sylowVec m K '' {x | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1}).ncard = (2 ^ (2 * m + 1)) ^ 6 := by
  rw [((bijOn_sylowVec hK).2.1.mono (Set.subset_univ _)).ncard_image,
    stratumOne_eq_range hK, Set.ncard_range_of_injective stratumOneVec_injective, Nat.card_fun,
    Nat.card_fin, hK]

theorem sylowA_one_sq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) : sylowA m K 1 ^ 2 = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sq, sylowA_mul hK, CharTwo.add_self_eq_zero, sylowA_zero]

theorem uClass_sylowA_one_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    uClass m K (sylowA m K 1) = sylowVec m K '' {x | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1} := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have hA : sylowA m K 1 = sylowVec m K ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [← sylowV_eq_sylowA]
    simp [sylowVec]
  have hsub : uClass m K (sylowA m K 1) ⊆
      sylowVec m K '' {x | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have hmem : u * sylowA m K 1 * u⁻¹ ∈ F4.reeFixedPosUnipotent K m :=
      uClass_subset _ (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1)) ⟨u, hu, rfl⟩
    obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 hmem
    have h0 := coord_zero_conj hK hu (hA ▸ hy.symm)
    refine ⟨y, ⟨by rw [h0]; simp, ?_⟩, hy⟩
    rw [hy]
    exact conj_sq_eq_one (sylowA_one_sq hK)
  have hC := card_centralizer_of_eq hK (centralizer_sylowA_one hK) {1, 2, 5, 6, 7, 9}
    (by ext x; simp)
  rw [show 12 - ({1, 2, 5, 6, 7, 9} : Finset (Fin 12)).card = 6 by decide] at hC
  have hcard := ncard_uClass hK (by decide) hC
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hcard, ncard_stratumOne hK]

@[expose] def stratumZeroOneVec (m : ℕ) (y : Fin 5 → K) : Fin 12 → K :=
  ![0, 0, 1, 0, y 0 * largeReeSigma m (y 0), y 0, y 1, largeReeSigma m (y 0), y 2, y 3,
    largeReeSigma m (y 0) * y 3, y 4]

theorem stratumZeroOne_eq_range
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    {x : Fin 12 → K | x 0 = 0 ∧ x 2 = 1 ∧ sylowVec m K x ^ 2 = 1} =
      Set.range (stratumZeroOneVec (K := K) m) := by
  ext x
  constructor
  · rintro ⟨h0, h2, hsq⟩
    have hsq' : sylowV m K 0 (x 1) 1 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
        (x 11) ^ 2 = 1 := by
      rw [← h0, ← h2]
      exact hsq
    obtain ⟨h1, h3, h7, h4, h10⟩ :=
      (sylowV_zero_one_sq_eq_one_iff hK _ _ _ _ _ _ _ _ _ _).1 hsq'
    refine ⟨![x 5, x 6, x 8, x 9, x 11], funext fun i => ?_⟩
    fin_cases i <;> simp [stratumZeroOneVec, h0, h1, h2, h3, h4, h7, h10]
  · rintro ⟨y, rfl⟩
    refine ⟨by simp [stratumZeroOneVec], by simp [stratumZeroOneVec], ?_⟩
    have e : sylowVec m K (stratumZeroOneVec m y) = sylowV m K 0 0 1 0
        (y 0 * largeReeSigma m (y 0)) (y 0) (y 1) (largeReeSigma m (y 0)) (y 2) (y 3)
        (largeReeSigma m (y 0) * y 3) (y 4) := by
      simp [sylowVec, stratumZeroOneVec]
    rw [e, sylowV_zero_one_sq_eq_one_iff hK]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Finite K] [CharP K F4.prime] in
theorem stratumZeroOneVec_injective : Function.Injective (stratumZeroOneVec (K := K) m) := by
  intro y y' h
  funext i
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h8 := congrFun h 8
  have h9 := congrFun h 9
  have h11 := congrFun h 11
  simp only [stratumZeroOneVec] at h5 h6 h8 h9 h11
  simp at h5 h6 h8 h9 h11
  fin_cases i <;> assumption

theorem ncard_stratumZeroOne
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (sylowVec m K '' {x | x 0 = 0 ∧ x 2 = 1 ∧ sylowVec m K x ^ 2 = 1}).ncard =
      (2 ^ (2 * m + 1)) ^ 5 := by
  rw [((bijOn_sylowVec hK).2.1.mono (Set.subset_univ _)).ncard_image,
    stratumZeroOne_eq_range hK, Set.ncard_range_of_injective stratumZeroOneVec_injective,
    Nat.card_fun, Nat.card_fin, hK]

omit [Finite K] [CharP K F4.prime] in
theorem sylowB_mul_sylowH_eq (c i : K) :
    sylowB m K 0 c * sylowH m K 0 i = sylowVec m K ![0, 0, c, 0, 0, 0, 0, 0, i, 0, 0, 0] := by
  simp [sylowVec, sylowV, sylowA_zero, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowB_mul_sylowH_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (c i : K) :
    sylowB m K 0 c * sylowH m K 0 i ∈ F4.reeFixedPosUnipotent K m := by
  rw [sylowB_mul_sylowH_eq]
  exact (bijOn_sylowVec hK).1 (Set.mem_univ _)

theorem commute_sylowH
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K m) (i : K) :
    u * sylowH m K 0 i = sylowH m K 0 i * u := by
  rw [sylowH_zero_eq_centralZ]
  exact commute_centralZ hm hK hu i

theorem card_centralizer_sylowB_mul_sylowH
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (i : K) :
    Nat.card (F4.reeFixedPosUnipotent K m ⊓
      Subgroup.centralizer {sylowB m K 0 1 * sylowH m K 0 i} : Subgroup (ModGL F4.tag K)) =
        (2 ^ (2 * m + 1)) ^ 8 := by
  have e : F4.reeFixedPosUnipotent K m ⊓
      Subgroup.centralizer {sylowB m K 0 1 * sylowH m K 0 i} =
        F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowB m K 0 1} := by
    ext u
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun ⟨hu, h⟩ => ⟨hu, ?_⟩, fun ⟨hu, h⟩ => ⟨hu, ?_⟩⟩
    · have hz := commute_sylowH hm hK hu i
      have h' : u * sylowB m K 0 1 * sylowH m K 0 i = sylowB m K 0 1 * u * sylowH m K 0 i := by
        calc u * sylowB m K 0 1 * sylowH m K 0 i = u * (sylowB m K 0 1 * sylowH m K 0 i) := by
              group
          _ = sylowB m K 0 1 * sylowH m K 0 i * u := h
          _ = sylowB m K 0 1 * (u * sylowH m K 0 i) := by rw [mul_assoc, ← hz]
          _ = sylowB m K 0 1 * u * sylowH m K 0 i := by group
      exact mul_right_cancel h'
    · calc u * (sylowB m K 0 1 * sylowH m K 0 i) = u * sylowB m K 0 1 * sylowH m K 0 i := by
            group
        _ = sylowB m K 0 1 * u * sylowH m K 0 i := by rw [h]
        _ = sylowB m K 0 1 * (u * sylowH m K 0 i) := by group
        _ = sylowB m K 0 1 * sylowH m K 0 i * u := by rw [commute_sylowH hm hK hu i]; group
  rw [e, card_centralizer_of_eq hK (centralizer_sylowB_zero_one hK) {0, 3, 4, 10}
    (by ext x; simp), show 12 - ({0, 3, 4, 10} : Finset (Fin 12)).card = 8 by decide]

theorem sylowH_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (i j : K) :
    sylowH m K 0 i * sylowH m K 0 j = sylowH m K 0 (i + j) := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma hK
  have hc := sylowX_commute_of_commFactors (K := K) (i := 44) (j := 47) (by norm_num)
    (by norm_num) (by norm_num) (by decide) j (largeReeSigma m i)
  rw [sylowH_zero_left, sylowH_zero_left, sylowH_zero_left, ← hσ, ← hσ, ← hσ, map_add]
  rw [← hσ] at hc
  simp only [sylowX, pinnedX_add] at hc ⊢
  calc pinnedX F4.tag K (orbitCertRoot F4.tag 44) i *
        pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ i) *
          (pinnedX F4.tag K (orbitCertRoot F4.tag 44) j *
            pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ j)) =
      pinnedX F4.tag K (orbitCertRoot F4.tag 44) i *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ i) *
          pinnedX F4.tag K (orbitCertRoot F4.tag 44) j) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ j) := by group
    _ = pinnedX F4.tag K (orbitCertRoot F4.tag 44) i *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 44) j *
          pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ i)) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 47) (σ j) := by rw [hc.eq]
    _ = _ := by group

omit [Finite K] [CharP K F4.prime] in
theorem sylowH_injective
    {i j : K} (h : sylowH m K 0 i = sylowH m K 0 j) : i = j := by
  rw [sylowH_zero_eq_centralZ, sylowH_zero_eq_centralZ] at h
  exact centralZ_injective h

theorem uClass_disjoint
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {i j : K}
    (hij : i ≠ j) :
    Disjoint (uClass m K (sylowB m K 0 1 * sylowH m K 0 i))
      (uClass m K (sylowB m K 0 1 * sylowH m K 0 j)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', h⟩
  apply hij
  have hwU : u'⁻¹ * u ∈ F4.reeFixedPosUnipotent K m := mul_mem (inv_mem hu') hu
  have hwz : u'⁻¹ * u * sylowH m K 0 i * (u'⁻¹ * u)⁻¹ = sylowH m K 0 i := by
    rw [commute_sylowH hm hK hwU i, mul_inv_cancel_right]
  have h1 : u'⁻¹ * u * (sylowB m K 0 1 * sylowH m K 0 i) * (u'⁻¹ * u)⁻¹ =
      sylowB m K 0 1 * sylowH m K 0 j := by
    calc u'⁻¹ * u * (sylowB m K 0 1 * sylowH m K 0 i) * (u'⁻¹ * u)⁻¹ =
        u'⁻¹ * (u * (sylowB m K 0 1 * sylowH m K 0 i) * u⁻¹) * u' := by group
      _ = u'⁻¹ * (u' * (sylowB m K 0 1 * sylowH m K 0 j) * u'⁻¹) * u' := by rw [h]
      _ = sylowB m K 0 1 * sylowH m K 0 j := by group
  rw [weyl_conj_mul, hwz] at h1
  have hzi : (sylowH m K 0 i)⁻¹ = sylowH m K 0 i := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [sylowH_mul hK, CharTwo.add_self_eq_zero, sylowH_zero_left, sylowX, sylowX,
      largeReeSigma_zero, pinnedX_zero, pinnedX_zero, mul_one]
  have hconj : u'⁻¹ * u * sylowB m K 0 1 * (u'⁻¹ * u)⁻¹ =
      sylowB m K 0 1 * sylowH m K 0 (j + i) := by
    rw [eq_mul_inv_of_mul_eq h1, hzi, mul_assoc, sylowH_mul hK]
  obtain ⟨x, -, hx⟩ := (bijOn_sylowVec hK).2.2 hwU
  rw [← hx] at hconj
  have hfix : sylowVec m K x * sylowB m K 0 1 * (sylowVec m K x)⁻¹ = sylowB m K 0 1 :=
    sylowV_conj_eq_of_mem_mul (m := m) _ _ _ _ _ _ _ _ _ _ _ _ (j + i) hconj
  rw [hfix] at hconj
  have hz1 : sylowH m K 0 (j + i) = sylowH m K 0 0 := by
    have := congrArg ((sylowB m K 0 1)⁻¹ * ·) hconj
    simp only [inv_mul_cancel_left, inv_mul_cancel] at this
    rw [← this, sylowH_zero_left, sylowX, sylowX, largeReeSigma_zero, pinnedX_zero, pinnedX_zero,
      mul_one]
  have hji := sylowH_injective hz1
  have : j = i := by
    have := congrArg (· + i) hji
    simpa [CharTwo.add_self_eq_zero, add_assoc] using this
  exact this.symm

theorem sylowB_mul_sylowH_sq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (i : K) :
    (sylowB m K 0 1 * sylowH m K 0 i) ^ 2 = 1 := by
  rw [sylowB_mul_sylowH_eq]
  have e : sylowVec m K ![0, 0, 1, 0, 0, 0, 0, 0, i, 0, 0, 0] =
      sylowV m K 0 0 1 0 0 0 0 0 i 0 0 0 := by simp [sylowVec]
  rw [e, sylowV_zero_one_sq_eq_one_iff hK]
  simp [largeReeSigma_zero]

theorem stratumZeroOne_eq
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    sylowVec m K '' {x | x 0 = 0 ∧ x 2 = 1 ∧ sylowVec m K x ^ 2 = 1} =
      ⋃ i : K, uClass m K (sylowB m K 0 1 * sylowH m K 0 i) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have hsub : (⋃ i : K, uClass m K (sylowB m K 0 1 * sylowH m K 0 i)) ⊆
      sylowVec m K '' {x | x 0 = 0 ∧ x 2 = 1 ∧ sylowVec m K x ^ 2 = 1} := by
    refine Set.iUnion_subset fun i => ?_
    rintro _ ⟨u, hu, rfl⟩
    have hmem : u * (sylowB m K 0 1 * sylowH m K 0 i) * u⁻¹ ∈ F4.reeFixedPosUnipotent K m :=
      uClass_subset _ (sylowB_mul_sylowH_mem hK 1 i) ⟨u, hu, rfl⟩
    obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 hmem
    have hy' := hy
    rw [sylowB_mul_sylowH_eq] at hy'
    have h0 := coord_zero_conj hK hu hy'.symm
    have h12 := coord_one_two_conj hK hu (by simp) hy'.symm
    refine ⟨y, ⟨by rw [h0]; simp, by rw [h12.2]; simp, ?_⟩, hy⟩
    rw [hy]
    exact conj_sq_eq_one (sylowB_mul_sylowH_sq hK i)
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  have hcl : ∀ i : K, (uClass m K (sylowB m K 0 1 * sylowH m K 0 i)).ncard =
      (2 ^ (2 * m + 1)) ^ 4 := fun i =>
    ncard_uClass hK (by decide) (card_centralizer_sylowB_mul_sylowH hm hK i)
  have := Fintype.ofFinite K
  rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _)
      (fun i j hij => uClass_disjoint hm hK hij), ncard_stratumZeroOne hK]
  simp only [hcl]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hK]
  ring_nf
  exact le_rfl

theorem torusTwo_conj_coords
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) {x x' : Fin 12 → K}
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (h : pairedTorusHom m (f4i 1) (f4i 2) u * sylowVec m K x *
      (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ = sylowVec m K x') :
    x' 0 = 0 ∧ x' 1 = 0 ∧ x' 2 = (u : K) * x 2 := by
  have hT := torusTwo_mem (m := m) hK u
  have hnorm : ∀ j : Fin F4.fixedOrbitCount, ∀ w ∈ F4.reeFixedOrbitComplementUnipotent K m j,
      pairedTorusHom m (f4i 1) (f4i 2) u * w * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ ∈
        F4.reeFixedOrbitComplementUnipotent K m j := fun j w hw =>
    (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_complement j hT) w).1 hw
  have h0 : x' 0 = 0 := by
    have hw := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
      (x 9) (x 10) (x 11)
    have e : sylowVec m K x' = sylowA m K 0 * (pairedTorusHom m (f4i 1) (f4i 2) u *
        sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) *
          (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹) := by
      rw [← h, sylowA_zero, one_mul, sylowVec_eq_sylowA_mul, hx0, sylowA_zero, one_mul]
    exact coord_zero_eq hK (hnorm _ _ hw) e
  obtain ⟨n, hn, hxn⟩ := exists_sylowVec_eq_sylowB_mul hK x
  rw [hx1] at hxn
  have e : sylowVec m K x' = sylowB m K 0 ((u : K) * x 2) *
      (pairedTorusHom m (f4i 1) (f4i 2) u * n * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹) := by
    rw [← h, hxn, ← torusTwo_conj_sylowB]
    group
  obtain ⟨h1, h2⟩ := coord_one_two_eq hK (hnorm _ _ hn) e
  exact ⟨h0, h1, h2⟩

theorem torus_conj_mem
    {h : ModGL F4.tag K}
    (hh : h ∈ F4.reeFixedTorus K m) {v : ModGL F4.tag K} (hv : v ∈ F4.reeFixedPosUnipotent K m) :
    h * v * h⁻¹ ∈ F4.reeFixedPosUnipotent K m :=
  (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_reeFixedPosUnipotent hh) v).1 hv

theorem torusTwo_conj_mem_stratum
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) {c : K}
    {y : ModGL F4.tag K}
    (hy : y ∈ sylowVec m K '' {x | x 0 = 0 ∧ x 2 = c ∧ sylowVec m K x ^ 2 = 1}) :
    pairedTorusHom m (f4i 1) (f4i 2) u * y * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ ∈
      sylowVec m K '' {x | x 0 = 0 ∧ x 2 = (u : K) * c ∧ sylowVec m K x ^ 2 = 1} := by
  obtain ⟨x, ⟨hx0, hx2, hsq⟩, rfl⟩ := hy
  have hx1 : x 1 = 0 := sq_eq_one_b (m := m) (hsq.trans rfl)
  obtain ⟨x', -, hx'⟩ := (bijOn_sylowVec hK).2.2 (torus_conj_mem (torusTwo_mem hK u)
    ((bijOn_sylowVec hK).1 (Set.mem_univ x)))
  obtain ⟨h0, -, h2⟩ := torusTwo_conj_coords hK u hx0 hx1 hx'.symm
  refine ⟨x', ⟨h0, by rw [h2, hx2], ?_⟩, hx'⟩
  rw [hx']
  exact conj_sq_eq_one hsq

theorem image_torus_uClass
    {h : ModGL F4.tag K}
    (hh : h ∈ F4.reeFixedTorus K m) (g : ModGL F4.tag K) :
    (fun y => h * y * h⁻¹) '' uClass m K g = uClass m K (h * g * h⁻¹) := by
  ext y
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨h * u * h⁻¹, torus_conj_mem hh hu, by group⟩
  · rintro ⟨u, hu, rfl⟩
    have hu' : h⁻¹ * u * h ∈ F4.reeFixedPosUnipotent K m := by
      have := torus_conj_mem (inv_mem hh) hu
      rwa [inv_inv] at this
    exact ⟨h⁻¹ * u * h * g * (h⁻¹ * u * h)⁻¹, ⟨_, hu', rfl⟩, by group⟩

theorem image_torusTwo_stratumZero
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (c : Kˣ) :
    (fun y => pairedTorusHom m (f4i 1) (f4i 2) c * y * (pairedTorusHom m (f4i 1) (f4i 2) c)⁻¹) ''
        (sylowVec m K '' {x | x 0 = 0 ∧ x 2 = 1 ∧ sylowVec m K x ^ 2 = 1}) =
      sylowVec m K '' {x | x 0 = 0 ∧ x 2 = (c : K) ∧ sylowVec m K x ^ 2 = 1} := by
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨y, hy, rfl⟩
    have := torusTwo_conj_mem_stratum hK c hy
    rwa [mul_one] at this
  · have hy' := torusTwo_conj_mem_stratum hK c⁻¹ hy
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero] at hy'
    refine ⟨_, hy', ?_⟩
    simp only [map_inv]
    group

theorem stratumZero_eq
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {c : K} (hc : c ≠ 0) :
    sylowVec m K '' {x | x 0 = 0 ∧ x 2 = c ∧ sylowVec m K x ^ 2 = 1} =
      ⋃ i : K, uClass m K (sylowB m K 0 c * sylowH m K 0 i) ∧
    (∀ i j : K, i ≠ j → Disjoint (uClass m K (sylowB m K 0 c * sylowH m K 0 i))
      (uClass m K (sylowB m K 0 c * sylowH m K 0 j))) ∧
    ∀ i : K, (uClass m K (sylowB m K 0 c * sylowH m K 0 i)).ncard = (2 ^ (2 * m + 1)) ^ 4 := by
  set T := pairedTorusHom m (f4i 1) (f4i 2) (Units.mk0 c hc) with hT
  have hTmem : T ∈ F4.reeFixedTorus K m := torusTwo_mem hK _
  have hφ : Function.Injective fun y : ModGL F4.tag K => T * y * T⁻¹ := fun y y' h => by
    simpa using h
  have hconj : ∀ i : K, T * (sylowB m K 0 1 * sylowH m K 0 i) * T⁻¹ =
      sylowB m K 0 c * sylowH m K 0 i := fun i => by
    rw [weyl_conj_mul, hT, torusTwo_conj_sylowB, torusTwo_conj_sylowH hK, Units.val_mk0, mul_one]
  have himg : ∀ i : K, (fun y => T * y * T⁻¹) '' uClass m K (sylowB m K 0 1 * sylowH m K 0 i) =
      uClass m K (sylowB m K 0 c * sylowH m K 0 i) := fun i => by
    rw [image_torus_uClass hTmem, hconj]
  refine ⟨?_, fun i j hij => ?_, fun i => ?_⟩
  · have h := image_torusTwo_stratumZero (m := m) hK (Units.mk0 c hc)
    rw [Units.val_mk0, stratumZeroOne_eq hm hK, Set.image_iUnion] at h
    rw [← h]
    exact Set.iUnion_congr himg
  · rw [← himg i, ← himg j]
    exact (Set.disjoint_image_iff hφ).2 (uClass_disjoint hm hK hij)
  · rw [← himg i, Set.ncard_image_of_injective _ hφ]
    exact ncard_uClass hK (by decide) (card_centralizer_sylowB_mul_sylowH hm hK i)

end CFSG.LieType.Ree.LargeReeInvolution

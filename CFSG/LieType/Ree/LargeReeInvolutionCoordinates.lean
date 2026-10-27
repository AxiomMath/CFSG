module

public import CFSG.LieType.Ree.LargeReeInvolutionCollect
public import CFSG.LieType.Ree.LargeReeEightCollection

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover

section Words

variable (m : ℕ) (K : Type) [Field K]

@[expose] def sylowX
    (r : ℕ) (c : K) : ModGL F4.tag K :=
  pinnedX F4.tag K (orbitCertRoot F4.tag r) c

@[expose] def sylowA
    (a : K) : ModGL F4.tag K :=
  sylowX K 24 a * sylowX K 33 (largeReeSigma m a)

@[expose] def sylowB
    (b c : K) : ModGL F4.tag K :=
  sylowX K 25 b * sylowX K 27 (largeReeSigma m b) * sylowX K 28 c *
    sylowX K 30 (largeReeSigma m c + b ^ 2 * largeReeSigma m b)

@[expose] def sylowD
    (d e : K) : ModGL F4.tag K :=
  sylowX K 26 d * sylowX K 34 (largeReeSigma m d) * sylowX K 36 e *
    sylowX K 39 (largeReeSigma m e + d ^ 2 * largeReeSigma m d)

@[expose] def sylowF
    (f g : K) : ModGL F4.tag K :=
  sylowX K 29 f * sylowX K 37 (largeReeSigma m f) * sylowX K 43 g *
    sylowX K 46 (largeReeSigma m g + f ^ 2 * largeReeSigma m f)

@[expose] def sylowH
    (h i : K) : ModGL F4.tag K :=
  sylowX K 35 h * sylowX K 32 (largeReeSigma m h) * sylowX K 44 i *
    sylowX K 47 (largeReeSigma m i + h ^ 2 * largeReeSigma m h)

@[expose] def sylowJ
    (j : K) : ModGL F4.tag K :=
  sylowX K 31 j * sylowX K 40 (largeReeSigma m j)

@[expose] def sylowK
    (k : K) : ModGL F4.tag K :=
  sylowX K 38 k * sylowX K 42 (largeReeSigma m k)

@[expose] def sylowL
    (l : K) : ModGL F4.tag K :=
  sylowX K 41 l * sylowX K 45 (largeReeSigma m l)

@[expose] def sylowV
    (a b c d e f g h i j k l : K) : ModGL F4.tag K :=
  sylowA m K a * sylowB m K b c * sylowD m K d e * sylowF m K f g * sylowH m K h i *
    sylowJ m K j * sylowK m K k * sylowL m K l

@[expose] def sylowVec
    (x : Fin 12 → K) : ModGL F4.tag K :=
  sylowV m K (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)

end Words

section Blocks

variable {m : ℕ} {K : Type} [Field K]

@[expose] def stdTwoG
    (m : ℕ) (s : K) : ModGL F4.tag K :=
  pinnedX F4.tag K (stdTwoRoot 0) s * pinnedX F4.tag K (stdTwoRoot 1) (largeReeSigma m s)

@[expose] def twoCoordG
    (m : ℕ) (t : Fin 4) (s : K) : ModGL F4.tag K :=
  nTwo K t * stdTwoG m s * (nTwo K t)⁻¹

@[expose] def stdFourG
    (m : ℕ) (c d : K) : ModGL F4.tag K :=
  pinnedX F4.tag K (stdFourRoot 0) c * pinnedX F4.tag K (stdFourRoot 1) (largeReeSigma m c) *
    pinnedX F4.tag K (stdFourRoot 2) d *
      pinnedX F4.tag K (stdFourRoot 3) (largeReeSigma m d + c ^ 2 * largeReeSigma m c)

@[expose] def fourCoordG
    (m : ℕ) (f : Fin 4) (c d : K) : ModGL F4.tag K :=
  nFour K f * stdFourG m c d * (nFour K f)⁻¹

theorem stdTwoRoot_eq_single : stdTwoRoot 0 = Pi.single largeReeI4 1 ∧
    stdTwoRoot 1 = Pi.single largeReeI1 1 := by
  decide +kernel

theorem stdFourRoot_eq_largeReeRoot (i : Fin 4) : stdFourRoot i = largeReeRoot i := by
  fin_cases i <;> rfl

theorem stdFourG_eq_largeReeCoord
    (c d : K) : stdFourG m c d = largeReeCoord m K c d := by
  simp only [stdFourG, largeReeCoord, largeReeP, largeReeX, stdFourRoot_eq_largeReeRoot]
  rfl

theorem stdTwoG_eq_xUnit
    (s : K) :
    stdTwoG m s = xUnit F4.tag K largeReeI1 (largeReeSigma m s) * xUnit F4.tag K largeReeI4 s := by
  rw [stdTwoG, stdTwoRoot_eq_single.1, stdTwoRoot_eq_single.2, pinnedX_single, pinnedX_single]
  exact ((largeRee_commute_xx _ s).eq).symm

variable [CharP K F4.prime]

theorem twoCoordG_eq
    (t : Fin 4) (s : K) :
    twoCoordG m t s =
      pinnedX F4.tag K (twoRoot t 0) s * pinnedX F4.tag K (twoRoot t 1) (largeReeSigma m s) := by
  have e : ∀ n A B : ModGL F4.tag K, n * (A * B) * n⁻¹ = n * A * n⁻¹ * (n * B * n⁻¹) :=
    fun _ _ _ => by group
  rw [twoCoordG, stdTwoG, e, nTwo, conj_relElt_pinnedX _ (isRoot_stdTwoRoot 0),
    conj_relElt_pinnedX _ (isRoot_stdTwoRoot 1)]
  rfl

theorem fourCoordG_eq
    (f : Fin 4) (c d : K) :
    fourCoordG m f c d =
      pinnedX F4.tag K (fourRoot f 0) c * pinnedX F4.tag K (fourRoot f 1) (largeReeSigma m c) *
        pinnedX F4.tag K (fourRoot f 2) d *
          pinnedX F4.tag K (fourRoot f 3) (largeReeSigma m d + c ^ 2 * largeReeSigma m c) := by
  have e : ∀ n A B C D : ModGL F4.tag K, n * (A * B * C * D) * n⁻¹ =
      n * A * n⁻¹ * (n * B * n⁻¹) * (n * C * n⁻¹) * (n * D * n⁻¹) := fun _ _ _ _ _ => by group
  rw [fourCoordG, stdFourG, e, nFour, conj_relElt_pinnedX _ (isRoot_stdFourRoot 0),
    conj_relElt_pinnedX _ (isRoot_stdFourRoot 1), conj_relElt_pinnedX _ (isRoot_stdFourRoot 2),
    conj_relElt_pinnedX _ (isRoot_stdFourRoot 3)]
  rfl

variable [Finite K]

omit [CharP K F4.prime] in
theorem largeReeSigma_pow_two_pow (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    (largeReeSigma m s) ^ 2 ^ m = s := by
  have : Fintype K := Fintype.ofFinite K
  rw [largeReeSigma, ← pow_mul, show 2 * 2 ^ m * 2 ^ m = Fintype.card K by
    rw [← Nat.card_eq_fintype_card, hK]; ring, FiniteField.pow_card]

omit [CharP K F4.prime] in
theorem largeReeSigma_pow (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    largeReeSigma m (s ^ 2 ^ m) = s := by
  have : Fintype K := Fintype.ofFinite K
  rw [largeReeSigma, ← pow_mul, show 2 ^ m * (2 * 2 ^ m) = Fintype.card K by
    rw [← Nat.card_eq_fintype_card, hK]; ring, FiniteField.pow_card]

theorem stdTwoG_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    stdTwoG m s ∈ F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ := by
  have h := coe_reeFixedOrbitUnipotent_zero (K := K) (a := m) hK
  have hmem : xUnit F4.tag K largeReeI1 (largeReeSigma m s) *
      xUnit F4.tag K largeReeI4 ((largeReeSigma m s) ^ 2 ^ m) ∈
        (F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
    rw [h]
    exact ⟨_, rfl⟩
  rw [largeReeSigma_pow_two_pow hK] at hmem
  rw [stdTwoG_eq_xUnit]
  exact hmem

theorem exists_stdTwoG_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩) : ∃ s : K, stdTwoG m s = g := by
  have h := coe_reeFixedOrbitUnipotent_zero (K := K) (a := m) hK
  have hg' : g ∈ (F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := hg
  rw [h] at hg'
  obtain ⟨c, rfl⟩ := hg'
  exact ⟨c ^ 2 ^ m, by rw [stdTwoG_eq_xUnit, largeReeSigma_pow hK]⟩

omit [Finite K] [CharP K F4.prime] in
theorem stdTwoG_injective
    : Function.Injective (stdTwoG (K := K) m) := by
  intro s s' h
  have hinj := CFSG.LieType.Ree.list_ofFn_pinnedX_injective (τ := F4.tag)
    (fun i : Fin 2 => stdTwoRoot i) (by decide +kernel)
    (fun i => ⟨isRoot_stdTwoRoot i, by fin_cases i <;> decide +kernel⟩) K
  have h2 := @hinj ![s, largeReeSigma m s] ![s', largeReeSigma m s'] (by
    simpa [List.ofFn_succ, stdTwoG] using h)
  simpa using congrFun h2 0

theorem twoCoordG_mem_block
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (t : Fin 4) (s : K) :
    twoCoordG m t s ∈ largeReeBlockGroup K m (twoSet t) := by
  rw [twoSet, largeReeBlockGroup_eq_map K m (fixedRelElt_mem _)]
  exact ⟨stdTwoG m s, stdTwoG_mem hK s, rfl⟩

theorem fourCoordG_mem_block
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (f : Fin 4) (c d : K) :
    fourCoordG m f c d ∈ largeReeBlockGroup K m (fourSet f) := by
  rw [fourSet, largeReeBlockGroup_eq_map K m (fixedRelElt_mem _)]
  refine ⟨stdFourG m c d, ?_, rfl⟩
  rw [stdFourG_eq_largeReeCoord]
  exact largeReeCoord_mem hK c d

theorem exists_twoCoordG_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (t : Fin 4)
    {g : ModGL F4.tag K} (hg : g ∈ largeReeBlockGroup K m (twoSet t)) :
    ∃ s : K, twoCoordG m t s = g := by
  rw [twoSet, largeReeBlockGroup_eq_map K m (fixedRelElt_mem _)] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨s, rfl⟩ := exists_stdTwoG_eq hK hy
  exact ⟨s, rfl⟩

theorem exists_stdFourG_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩) : ∃ c d : K, stdFourG m c d = g := by
  obtain ⟨c, d, hcd⟩ := exists_largeReeCoord_eq hK hg
  exact ⟨c, d, (stdFourG_eq_largeReeCoord c d).trans hcd⟩

theorem exists_fourCoordG_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (f : Fin 4)
    {g : ModGL F4.tag K} (hg : g ∈ largeReeBlockGroup K m (fourSet f)) :
    ∃ c d : K, fourCoordG m f c d = g := by
  rw [fourSet, largeReeBlockGroup_eq_map K m (fixedRelElt_mem _)] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨c, d, rfl⟩ := exists_stdFourG_eq hK hy
  exact ⟨c, d, rfl⟩

omit [Finite K] [CharP K F4.prime] in
theorem twoCoordG_injective
    (t : Fin 4) : Function.Injective (twoCoordG (K := K) m t) := by
  intro s s' h
  apply stdTwoG_injective (m := m)
  simpa [twoCoordG] using h

theorem fourCoordG_injective
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (f : Fin 4) {c d c' d' : K}
    (h : fourCoordG m f c d = fourCoordG m f c' d') : c = c' ∧ d = d' := by
  have h' : stdFourG m c d = stdFourG m c' d' := by
    simpa [fourCoordG] using h
  have h'' := (stdFourG_eq_largeReeCoord c d).symm.trans
    (h'.trans (stdFourG_eq_largeReeCoord c' d'))
  have := (bijOn_largeReeCoord hK).2.1 (Set.mem_univ (c, d)) (Set.mem_univ (c', d')) h''
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end Blocks

section Node

variable {m : ℕ} {K : Type} [Field K]

theorem blockRoots_eq_orbitCertRoot :
    (twoRoot 0 0 = orbitCertRoot F4.tag 24 ∧ twoRoot 0 1 = orbitCertRoot F4.tag 33) ∧
    (twoRoot 1 0 = orbitCertRoot F4.tag 31 ∧ twoRoot 1 1 = orbitCertRoot F4.tag 40) ∧
    (twoRoot 2 0 = orbitCertRoot F4.tag 38 ∧ twoRoot 2 1 = orbitCertRoot F4.tag 42) ∧
    (twoRoot 3 0 = orbitCertRoot F4.tag 41 ∧ twoRoot 3 1 = orbitCertRoot F4.tag 45) ∧
    (fourRoot 0 0 = orbitCertRoot F4.tag 25 ∧ fourRoot 0 1 = orbitCertRoot F4.tag 27 ∧
      fourRoot 0 2 = orbitCertRoot F4.tag 28 ∧ fourRoot 0 3 = orbitCertRoot F4.tag 30) ∧
    (fourRoot 1 0 = orbitCertRoot F4.tag 26 ∧ fourRoot 1 1 = orbitCertRoot F4.tag 34 ∧
      fourRoot 1 2 = orbitCertRoot F4.tag 36 ∧ fourRoot 1 3 = orbitCertRoot F4.tag 39) ∧
    (fourRoot 2 0 = orbitCertRoot F4.tag 29 ∧ fourRoot 2 1 = orbitCertRoot F4.tag 37 ∧
      fourRoot 2 2 = orbitCertRoot F4.tag 43 ∧ fourRoot 2 3 = orbitCertRoot F4.tag 46) ∧
    (fourRoot 3 0 = orbitCertRoot F4.tag 35 ∧ fourRoot 3 1 = orbitCertRoot F4.tag 32 ∧
      fourRoot 3 2 = orbitCertRoot F4.tag 44 ∧ fourRoot 3 3 = orbitCertRoot F4.tag 47) := by
  decide +kernel

variable [CharP K F4.prime]

theorem sylowA_eq
    (a : K) : sylowA m K a = twoCoordG m 0 a := by
  obtain ⟨⟨h0, h1⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [twoCoordG_eq, h0, h1]
  rfl

theorem sylowJ_eq
    (j : K) : sylowJ m K j = twoCoordG m 1 j := by
  obtain ⟨-, ⟨h0, h1⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [twoCoordG_eq, h0, h1]
  rfl

theorem sylowK_eq
    (k : K) : sylowK m K k = twoCoordG m 2 k := by
  obtain ⟨-, -, ⟨h0, h1⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [twoCoordG_eq, h0, h1]
  rfl

theorem sylowL_eq
    (l : K) : sylowL m K l = twoCoordG m 3 l := by
  obtain ⟨-, -, -, ⟨h0, h1⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [twoCoordG_eq, h0, h1]
  rfl

theorem sylowB_eq
    (b c : K) : sylowB m K b c = fourCoordG m 0 b c := by
  obtain ⟨-, -, -, -, ⟨h0, h1, h2, h3⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [fourCoordG_eq, h0, h1, h2, h3]
  rfl

theorem sylowD_eq
    (d e : K) : sylowD m K d e = fourCoordG m 1 d e := by
  obtain ⟨-, -, -, -, -, ⟨h0, h1, h2, h3⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [fourCoordG_eq, h0, h1, h2, h3]
  rfl

theorem sylowF_eq
    (f g : K) : sylowF m K f g = fourCoordG m 2 f g := by
  obtain ⟨-, -, -, -, -, -, ⟨h0, h1, h2, h3⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [fourCoordG_eq, h0, h1, h2, h3]
  rfl

theorem sylowH_eq
    (h i : K) : sylowH m K h i = fourCoordG m 3 h i := by
  obtain ⟨-, -, -, -, -, -, -, ⟨h0, h1, h2, h3⟩⟩ := blockRoots_eq_orbitCertRoot
  rw [fourCoordG_eq, h0, h1, h2, h3]
  rfl

@[expose] def nodeBlock
    : Fin 8 → Set (Fin F4.tag.rank → ℤ) :=
  ![twoSet 0, fourSet 0, fourSet 1, fourSet 2, fourSet 3, twoSet 1, twoSet 2, twoSet 3]

@[expose] def nodePerm : Fin 8 → Fin 8 :=
  ![0, 4, 5, 6, 7, 1, 2, 3]

theorem nodeBlock_eq
    : nodeBlock = posBlock ∘ nodePerm := by
  funext k
  fin_cases k <;> rfl

theorem nodePerm_bijective : Function.Bijective nodePerm := by
  decide

theorem nodeBlock_injective :
    Function.Injective nodeBlock := by
  rw [nodeBlock_eq]
  exact posBlock_injective.comp nodePerm_bijective.1

theorem range_nodeBlock :
    Set.range nodeBlock = largeReePosBlocks := by
  rw [nodeBlock_eq, nodePerm_bijective.2.range_comp, range_posBlock]

@[expose] def nodeElt
    (m : ℕ) (c : Fin 12 → K) : Fin 8 → ModGL F4.tag K :=
  ![twoCoordG m 0 (c 0), fourCoordG m 0 (c 1) (c 2), fourCoordG m 1 (c 3) (c 4),
    fourCoordG m 2 (c 5) (c 6), fourCoordG m 3 (c 7) (c 8), twoCoordG m 1 (c 9),
    twoCoordG m 2 (c 10), twoCoordG m 3 (c 11)]

theorem sylowVec_eq_prod
    (c : Fin 12 → K) : sylowVec m K c = (List.ofFn (nodeElt m c)).prod := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, nodeElt,
    Matrix.cons_val_succ, Matrix.cons_val_zero, sylowVec, sylowV, sylowA_eq, sylowB_eq, sylowD_eq,
    sylowF_eq, sylowH_eq, sylowJ_eq, sylowK_eq, sylowL_eq, mul_assoc]

variable [Finite K]

theorem bijOn_nodeElt
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Set.BijOn (nodeElt (K := K) m) Set.univ
      (Set.univ.pi fun k => (largeReeBlockGroup K m (nodeBlock k) : Set (ModGL F4.tag K))) := by
  refine ⟨fun c _ k _ => ?_, fun c _ c' _ h => ?_, fun y hy => ?_⟩
  · fin_cases k
    · exact twoCoordG_mem_block hK 0 _
    · exact fourCoordG_mem_block hK 0 _ _
    · exact fourCoordG_mem_block hK 1 _ _
    · exact fourCoordG_mem_block hK 2 _ _
    · exact fourCoordG_mem_block hK 3 _ _
    · exact twoCoordG_mem_block hK 1 _
    · exact twoCoordG_mem_block hK 2 _
    · exact twoCoordG_mem_block hK 3 _
  · have h0 := twoCoordG_injective 0 (congrFun h 0)
    obtain ⟨h1, h2⟩ := fourCoordG_injective hK 0 (congrFun h 1)
    obtain ⟨h3, h4⟩ := fourCoordG_injective hK 1 (congrFun h 2)
    obtain ⟨h5, h6⟩ := fourCoordG_injective hK 2 (congrFun h 3)
    obtain ⟨h7, h8⟩ := fourCoordG_injective hK 3 (congrFun h 4)
    have h9 := twoCoordG_injective 1 (congrFun h 5)
    have h10 := twoCoordG_injective 2 (congrFun h 6)
    have h11 := twoCoordG_injective 3 (congrFun h 7)
    funext i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · have hy' : ∀ k, y k ∈ largeReeBlockGroup K m (nodeBlock k) := fun k => hy k (Set.mem_univ k)
    obtain ⟨s0, e0⟩ := exists_twoCoordG_eq hK 0 (hy' 0)
    obtain ⟨c1, d1, e1⟩ := exists_fourCoordG_eq hK 0 (hy' 1)
    obtain ⟨c2, d2, e2⟩ := exists_fourCoordG_eq hK 1 (hy' 2)
    obtain ⟨c3, d3, e3⟩ := exists_fourCoordG_eq hK 2 (hy' 3)
    obtain ⟨c4, d4, e4⟩ := exists_fourCoordG_eq hK 3 (hy' 4)
    obtain ⟨s5, e5⟩ := exists_twoCoordG_eq hK 1 (hy' 5)
    obtain ⟨s6, e6⟩ := exists_twoCoordG_eq hK 2 (hy' 6)
    obtain ⟨s7, e7⟩ := exists_twoCoordG_eq hK 3 (hy' 7)
    refine ⟨![s0, c1, d1, c2, d2, c3, d3, c4, d4, s5, s6, s7], Set.mem_univ _, ?_⟩
    funext k
    fin_cases k
    exacts [e0, e1, e2, e3, e4, e5, e6, e7]

theorem bijOn_sylowVec
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Set.BijOn (sylowVec m K) Set.univ (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) := by
  have h := (bijOn_list_prod_largeReeBlockGroup K m nodeBlock nodeBlock_injective
    range_nodeBlock).comp (bijOn_nodeElt hK)
  have e : (fun x : Fin 8 → ModGL F4.tag K => (List.ofFn x).prod) ∘ nodeElt m = sylowVec m K :=
    funext fun c => (sylowVec_eq_prod c).symm
  rwa [e] at h

end Node

section Valuation

variable {m : ℕ} {K : Type} [Field K]

@[expose] def coordVal (m : ℕ) (a b c d e f g h i j k l : K) : ℕ → K
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | 6 => g
  | 7 => h
  | 8 => i
  | 9 => j
  | 10 => k
  | 11 => l
  | 12 => largeReeSigma m a
  | 13 => largeReeSigma m b
  | 14 => largeReeSigma m c
  | 15 => largeReeSigma m d
  | 16 => largeReeSigma m e
  | 17 => largeReeSigma m f
  | 18 => largeReeSigma m g
  | 19 => largeReeSigma m h
  | 20 => largeReeSigma m i
  | 21 => largeReeSigma m j
  | 22 => largeReeSigma m k
  | 23 => largeReeSigma m l
  | _ => 0

@[expose] def sylowWord : Word :=
  [(24, [[0]]), (33, [[12]]), (25, [[1]]), (27, [[13]]), (28, [[2]]), (30, [[1, 1, 13], [14]]),
   (26, [[3]]), (34, [[15]]), (36, [[4]]), (39, [[3, 3, 15], [16]]), (29, [[5]]), (37, [[17]]),
   (43, [[6]]), (46, [[5, 5, 17], [18]]), (35, [[7]]), (32, [[19]]), (44, [[8]]),
   (47, [[7, 7, 19], [20]]), (31, [[9]]), (40, [[21]]), (38, [[10]]), (42, [[22]]), (41, [[11]]),
   (45, [[23]])]

theorem sylowV_eq_wordEval
    (a b c d e f g h i j k l : K) :
    sylowV m K a b c d e f g h i j k l =
      wordEval K (coordVal m a b c d e f g h i j k l) sylowWord := by
  simp only [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
    sylowX, wordEval, sylowWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, add_zero, coordVal, mul_assoc]
  ring_nf

end Valuation

section Sigma

variable {m : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_sigma (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∃ σ : K →+* K, (∀ c, σ c = largeReeSigma m c) ∧ ∀ c, σ (σ c) = c ^ 2 := by
  obtain ⟨-, σ, -, hσ, -, -, hσσ, -⟩ := large_Ree_field_powers m K hK
  exact ⟨σ.toRingHom, fun c => (hσ c).trans rfl, fun c => hσσ c⟩

omit [Finite K] in
theorem largeReeSigma_zero : largeReeSigma m (0 : K) = 0 :=
  zero_pow (by positivity)

omit [Finite K] in
theorem largeReeSigma_one : largeReeSigma m (1 : K) = 1 :=
  one_pow _

theorem largeReeSigma_sigma (hK : Nat.card K = 2 ^ (2 * m + 1)) (c : K) :
    largeReeSigma m (largeReeSigma m c) = c ^ 2 := by
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma hK
  rw [← hσ, ← hσ, hσσ]

omit [Finite K] in
theorem largeReeSigma_eq_zero_iff (c : K) : largeReeSigma m c = 0 ↔ c = 0 := by
  rw [largeReeSigma]
  exact pow_eq_zero_iff (by positivity)

omit [Finite K] in
theorem coordVal_add_twelve (a b c d e f g h i j k l : K) :
    ∀ n < 12, coordVal m a b c d e f g h i j k l (n + 12) =
      largeReeSigma m (coordVal m a b c d e f g h i j k l n) := by
  intro n hn
  interval_cases n <;> rfl

theorem polyEval_coordVal_sigma (hK : Nat.card K = 2 ^ (2 * m + 1)) [CharP K 2]
    (a b c d e f g h i j k l : K) {p : Poly} (hp : varsBelow 24 p = true) :
    polyEval (coordVal m a b c d e f g h i j k l) (polySubst (sigmaVar 12) p) =
      largeReeSigma m (polyEval (coordVal m a b c d e f g h i j k l) p) := by
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma hK
  rw [← hσ]
  exact polyEval_polySubst_sigmaVar σ hσσ _ (fun n hn => by
    rw [coordVal_add_twelve _ _ _ _ _ _ _ _ _ _ _ _ n hn, hσ]) hp

end Sigma

theorem eq_of_add_eq_zero_two {R : Type*} [CommRing R] [CharP R 2] {a b : R} (h : a + b = 0) :
    a = b := by
  rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, h]

theorem polyEval_eq_of_polySubst {R : Type} [CommRing R] [CharP R 2] {x : ℕ → R}
    {l : List (ℕ × Poly)} (hl : ∀ e ∈ l, polyEval x e.2 = x e.1) {p q : Poly}
    (h : polySubst (substOf l) p = q) : polyEval x p = polyEval x q := by
  rw [← h, polyEval_polySubst_of x (polyEval_substOf x hl)]

@[expose] def sigmaPoly (p : Poly) : Poly :=
  polySubst (sigmaVar 12) p

@[expose] def polySubstSeq : List (List (ℕ × Poly)) → Poly → Poly
  | [], p => p
  | l :: ls, p => polySubstSeq ls (polySubst (substOf l) p)

section Seq

variable {R : Type} [CommRing R] [CharP R 2]

theorem polyEval_polySubstSeq {x : ℕ → R} :
    ∀ {ls : List (List (ℕ × Poly))}, (∀ l ∈ ls, ∀ e ∈ l, polyEval x e.2 = x e.1) →
      ∀ p, polyEval x (polySubstSeq ls p) = polyEval x p
  | [], _, _ => rfl
  | l :: ls, h, p => by
    rw [polySubstSeq, polyEval_polySubstSeq (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
      polyEval_polySubst_of x (polyEval_substOf x (h l List.mem_cons_self))]

theorem polyEval_eq_zero_of_polySubstSeq {x : ℕ → R} {ls : List (List (ℕ × Poly))}
    (h : ∀ l ∈ ls, ∀ e ∈ l, polyEval x e.2 = x e.1) {p : Poly} (hp : polySubstSeq ls p = []) :
    polyEval x p = 0 := by
  rw [← polyEval_polySubstSeq h p, hp]
  rfl

end Seq

section SigmaPair

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem forall_mem_sigmaPair (hK : Nat.card K = 2 ^ (2 * m + 1)) (a b c d e f g h i j k l : K)
    {n : ℕ} (hn : n < 12) {p : Poly} (hp : varsBelow 24 p = true)
    (hpv : polyEval (coordVal m a b c d e f g h i j k l) p = coordVal m a b c d e f g h i j k l n) :
    ∀ q ∈ [(n, p), (n + 12, sigmaPoly p)], polyEval (coordVal m a b c d e f g h i j k l) q.2 =
      coordVal m a b c d e f g h i j k l q.1 := by
  intro q hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl
  · exact hpv
  · rw [sigmaPoly, polyEval_coordVal_sigma hK _ _ _ _ _ _ _ _ _ _ _ _ hp, hpv,
      coordVal_add_twelve _ _ _ _ _ _ _ _ _ _ _ _ n hn]

end SigmaPair

end CFSG.LieType.Ree.LargeReeInvolution

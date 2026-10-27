module

public import CFSG.LieType.Chevalley.E6SignedGraphCollection
public import CFSG.LieType.Chevalley.E6SignedGraphLongRoot
public import CFSG.LieType.Chevalley.E6SignedGraphStabilizer

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {K : Type} [Field K]

theorem uSL_add (a b : K) : uSL (a + b) = uSL a * uSL b := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [SL2_mul_apply, coe_uSL, add_comm]

theorem uSL_zero : uSL (0 : K) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

theorem conj_mem_commutator_of_mem {G : Type*} [Group G] {H : Subgroup G} {z x : G} (hz : z ∈ H)
    (hx : x ∈ ⁅H, H⁆) : z * x * z⁻¹ ∈ ⁅H, H⁆ := by
  have hH : H.map (MulAut.conj z).toMonoidHom = H :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hz)
  have h : (⁅H, H⁆).map (MulAut.conj z).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hH]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem smul_mem_orbits
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup) {O : Finset E6Vec}
    (hO : O ∈ orbits) :
    O.image (fun α => w • α) ∈ orbits ∧ orbitVec (O.image fun α => w • α) = w • orbitVec O := by
  obtain ⟨α, hα, hk, rfl⟩ := mem_orbits.1 hO
  rw [← TwistTag.E6.diagramOrbit_smul hw.1 α]
  refine ⟨mem_orbits.2 ⟨w • α, IsRoot.smul hα w, ?_, rfl⟩, ?_⟩
  · unfold keep at hk ⊢
    by_cases h : rho α = α
    · have hfix : α ∈ TwistTag.E6.fixedLattice := h
      have he := hw.2 α hfix
      have hw' : rho (w • α) = w • α := by rw [rho_smul hw.1, h]
      simp only [h, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hk
      simp only [hw', decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      have h2 := he.add hk
      rwa [sub_add_cancel] at h2
    · have hw' : rho (w • α) ≠ w • α := by
        rw [rho_smul hw.1]
        exact fun e => h (MulAction.injective w e)
      simp [hw']
  · rw [orbitVec_diagramOrbit, orbitVec_diagramOrbit, smul_vecOf hw.1]

theorem exists_lift_of_mem_weylGroup
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) :
    ∃ z ∈ rootGenerated K, z ∈ monomialSubgroup TwistTag.E6.tag K ∧ z ∈ fixedGroup K ∧
      MapsRootLines z w := by
  have hw' : w ∈ Subgroup.closure (Set.range gen) := hw
  clear hw
  induction hw' using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    obtain ⟨w', hw', a, he⟩ := exists_orbitImage_eq (simpleOrbit_spec i).1
    have hO : orbitImage w' a ∈ orbits := he ▸ (simpleOrbit_spec i).1
    refine ⟨orbitSL2 K w' a (nSL 1), range_orbitSL2_le_rootGenerated hw' hO ⟨_, rfl⟩,
      orbitSL2_nSL_mem_monomialSubgroup w' a 1,
      orbitSL2_mem_fixedGroup hw' (orbitSign_eq_one_of_mem_orbits hO) _, ?_⟩
    have h := mapsRootLines_orbitSL2_nSL (K := K) w' a 1
    rw [he] at h
    exact h
  | one => exact ⟨1, one_mem _, one_mem _, one_mem _, mapsRootLines_one⟩
  | mul w w' _ _ ih ih' =>
    obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := ih
    obtain ⟨z', hz', hzN', hzΓ', hzw'⟩ := ih'
    exact ⟨z * z', mul_mem hz hz', mul_mem hzN hzN', mul_mem hzΓ hzΓ', hzw.mul hzw'⟩
  | inv w _ ih =>
    obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := ih
    exact ⟨z⁻¹, inv_mem hz, inv_mem hzN, inv_mem hzΓ, hzw.inv⟩

theorem orbitFixed_smul_le
    {O : Finset E6Vec} (hO : O ∈ orbits)
    (hQ : orbitFixed K O ≤ ⁅rootGenerated K, rootGenerated K⁆) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ weylGroup) :
    orbitFixed K (O.image fun α => w • α) ≤ ⁅rootGenerated K, rootGenerated K⁆ := by
  obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := exists_lift_of_mem_weylGroup (K := K) hw
  have hroots : ∀ α ∈ O, IsRoot TwistTag.E6.tag α := fun α hα => by
    obtain ⟨⟨β, hβ, rfl⟩, -⟩ := hO
    exact TwistTag.E6.isRoot_of_mem_diagramOrbit hβ hα
  rw [← map_orbitFixed_conj hzN hzw hzΓ hroots]
  rintro _ ⟨x, hx, rfl⟩
  exact conj_mem_commutator_of_mem hz (hQ hx)

theorem orbitFixed_le_of_smul
    {O₀ : Finset E6Vec} (hO₀ : O₀ ∈ orbits)
    (hQ : orbitFixed K O₀ ≤ ⁅rootGenerated K, rootGenerated K⁆) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ weylGroup) {O : Finset E6Vec} (hO : O ∈ orbits) (hv : w • orbitVec O₀ = orbitVec O) :
    orbitFixed K O ≤ ⁅rootGenerated K, rootGenerated K⁆ := by
  obtain ⟨hP, hPv⟩ := smul_mem_orbits (weylGroup_le_parityGroup hw) hO₀
  rw [← injOn_orbitVec hP hO (hPv.trans hv)]
  exact orbitFixed_smul_le hO₀ hQ hw

theorem orbitFixed_simpleOrbit_zero_le
    (hK : ringChar K ≠ 2) :
    orbitFixed K (simpleOrbit 0) ≤ ⁅rootGenerated K, rootGenerated K⁆ := by
  obtain ⟨w₁, hw₁, a₁, he₁⟩ := exists_orbitImage_eq (simpleOrbit_spec 0).1
  obtain ⟨w₂, hw₂, a₂, he₂⟩ := exists_orbitImage_eq (simpleOrbit_spec 1).1
  have hO₁ : orbitImage w₁ a₁ ∈ orbits := he₁ ▸ (simpleOrbit_spec 0).1
  have hO₂ : orbitImage w₂ a₂ ∈ orbits := he₂ ▸ (simpleOrbit_spec 1).1
  have hs₁ := orbitSign_eq_one_of_mem_orbits (K := K) hO₁
  set h := orbitSL2 K w₂ a₂ (HSL (-1))
  have hh : h ∈ rootGenerated K := range_orbitSL2_le_rootGenerated hw₂ hO₂ ⟨_, rfl⟩
  set q : K → ModGL TwistTag.E6.tag K := fun c => orbitSL2 K w₁ a₁ (uSL c) with hqdef
  have hq : ∀ c, q c ∈ rootGenerated K := fun c =>
    range_orbitSL2_le_rootGenerated hw₁ hO₁ ⟨_, rfl⟩
  have hE : iform (∑ α ∈ orbitImage w₂ a₂, α)
      (w₁ • (Pi.single (TwistTag.E6.orbitMin a₁) 1 : E6Vec)) = -1 := by
    have hmul := iform_orbitVec_mul hw₂ hw₁ a₂ a₁
    have hv₁ : orbitVec (orbitImage w₁ a₁) = simpleVec 0 := by
      rw [he₁]
      exact (simpleOrbit_spec 0).2
    have hv₂ : orbitVec (orbitImage w₂ a₂) = simpleVec 1 := by
      rw [he₂]
      exact (simpleOrbit_spec 1).2
    rw [hv₁, hv₂, show iform (simpleVec 1) (simpleVec 1) = 4 by decide +kernel,
      show iform (simpleVec 1) (simpleVec 0) = -2 by decide +kernel] at hmul
    omega
  have hconj : ∀ c, h * q c * h⁻¹ = q (-c) := fun c => by
    have e := orbitTorus_conj_orbitSL2_uSL (K := K) hw₂ hw₁ a₂ a₁ (-1) c
    rw [hE] at e
    have h1 : (((-1 : Kˣ) ^ (-1 : ℤ) : Kˣ) : K) = -1 := by simp
    rw [h1, neg_one_mul] at e
    exact e
  have hadd : ∀ c d, q c * q d = q (c + d) := fun c d => by
    simp only [hqdef, ← map_mul, ← uSL_add]
  have hinv : ∀ c, (q c)⁻¹ = q (-c) := fun c =>
    inv_eq_of_mul_eq_one_right (by rw [hadd, add_neg_cancel, hqdef]; simp [uSL_zero])
  have hcomm : ∀ c, ⁅h, q c⁆ = q (-2 * c) := fun c => by
    rw [commutatorElement_def, hconj, hinv, hadd]
    ring_nf
  intro y hy
  rw [← he₁, ← SetLike.mem_coe, ← (orbitFixed_orbitImage_upper hw₁ hs₁).2] at hy
  obtain ⟨c, rfl⟩ := hy
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have e := hcomm (-c / 2)
  rw [show -2 * (-c / 2) = c by field_simp] at e
  change q c ∈ _
  rw [← e]
  exact Subgroup.commutator_mem_commutator hh (hq _)

theorem xUnit_three_mem_posFixed
    (c : K) :
    xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c ∈ posFixed K := by
  refine Subgroup.mem_inf.2 ⟨xUnit_mem_posUnipotent _ c, mem_fixedGroup.2
    ⟨xUnit_mem_adjointGroup _ _, commute_twistA_of_conj ?_ (conjD_xUnit_of_ne (by decide) c)⟩⟩
  rw [conjP_xUnit, show TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ by decide]

theorem yUnit_three_mem_negFixed
    (c : K) :
    yUnit TwistTag.E6.tag K ⟨3, by decide⟩ c ∈ negFixed K := by
  refine Subgroup.mem_inf.2 ⟨yUnit_mem_negUnipotent _ c, mem_fixedGroup.2
    ⟨yUnit_mem_adjointGroup _ _, commute_twistA_of_conj ?_ (conjD_yUnit_of_ne (by decide) c)⟩⟩
  rw [conjP_yUnit, show TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ by decide]

theorem weylElt_three_mem_rootGenerated :
    weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1 ∈ rootGenerated K := by
  rw [weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (le_sup_left (a := posFixed K) (xUnit_three_mem_posFixed _))
    (le_sup_right (a := posFixed K) (yUnit_three_mem_negFixed _)))
    (le_sup_left (a := posFixed K) (xUnit_three_mem_posFixed _))

theorem xUnit_pair_mem_posFixed
    (c : K) :
    xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c ∈
      posFixed K := by
  have hcomm : xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c =
      xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c :=
    (commute_xUnit_xUnit (t := TwistTag.E6) K (a := ⟨1, by decide⟩) (by decide) (by decide) c
      c).eq
  refine Subgroup.mem_inf.2 ⟨mul_mem (xUnit_mem_posUnipotent _ c) (xUnit_mem_posUnipotent _ c),
    mem_fixedGroup.2 ⟨mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _),
      commute_twistA_of_conj ?_ ?_⟩⟩
  · rw [conj_mul, conjP_xUnit, conjP_xUnit,
      show TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ by decide,
      show TwistTag.E6.perm ⟨4, by decide⟩ = ⟨2, by decide⟩ by decide, hcomm]
  · rw [conj_mul, conjD_xUnit_of_ne (by decide), conjD_xUnit_of_ne (by decide)]

theorem orbitFixed_simpleOrbit_three_le
    (hK : ringChar K ≠ 2) :
    orbitFixed K (simpleOrbit 3) ≤ ⁅rootGenerated K, rootGenerated K⁆ := by
  obtain ⟨ε, hε, hall⟩ := E6_signed_graph_long_root_two_commutator
  obtain ⟨-, hAZ, -, hcomm, -⟩ := hall K
  have hS4 : simpleOrbit 3 = {(Pi.single ⟨3, by decide⟩ 1 : E6Vec)} := by
    rw [simpleOrbit, diagramOrbit_eq, show rho (simpleRoot 3) = simpleRoot 3 by decide +kernel,
      Finset.pair_eq_singleton,
      show simpleRoot 3 = (Pi.single ⟨3, by decide⟩ 1 : E6Vec) by decide +kernel]
  have hY : longY K 1 ∈ rootGenerated K := by
    have hn := weylElt_three_mem_rootGenerated (K := K)
    exact mul_mem (mul_mem hn (le_sup_left (a := posFixed K) (xUnit_pair_mem_posFixed 1)))
      (inv_mem hn)
  have hZ : ∀ d, longZ K d ∈ rootGenerated K := fun d =>
    le_sup_right (a := posFixed K) (Subgroup.mem_inf.2
      ⟨mul_mem (yUnit_mem_negUnipotent _ d) (yUnit_mem_negUnipotent _ d),
        mem_fixedGroup.2 ⟨mul_mem (yUnit_mem_adjointGroup _ _) (yUnit_mem_adjointGroup _ _),
          hAZ d⟩⟩)
  intro x hx
  obtain ⟨hxU, -⟩ := Subgroup.mem_inf.1 hx
  rw [hS4, Finset.coe_singleton, rootSpan_singleton, mem_rootSubgroup] at hxU
  obtain ⟨c, rfl⟩ := hxU
  rw [pinnedX_single]
  have hε' : ((ε : ℤ) : K) ≠ 0 := by
    rcases hε with h | h <;> simp [h]
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have e := hcomm 1 (c / (2 * (ε : K)))
  rw [show 2 * (ε : K) * 1 * (c / (2 * (ε : K))) = c by field_simp] at e
  rw [← e]
  exact Subgroup.commutator_mem_commutator hY (hZ _)

theorem commutator_rootGenerated
    (hK : ringChar K ≠ 2) :
    ⁅rootGenerated K, rootGenerated K⁆ = rootGenerated K := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, -, -, h17, -, -, -, -⟩ :=
    E6_signed_graph_root_system_and_Weyl_stabilizer
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have key : ∀ O ∈ orbits, orbitFixed K O ≤ ⁅rootGenerated K, rootGenerated K⁆ := by
    intro O hO
    have hv : orbitVec O ∈ vecs := ⟨O, hO, rfl⟩
    rw [h17] at hv
    rcases hv with ⟨-, h4⟩ | ⟨-, h8⟩
    · have hm : orbitVec O ∈ {v | ∃ w ∈ weylGroup, w • simpleVec 0 = v} := by
        rw [h13]
        exact ⟨⟨O, hO, rfl⟩, h4⟩
      obtain ⟨w, hw, hwv⟩ := hm
      exact orbitFixed_le_of_smul (simpleOrbit_spec 0).1 (orbitFixed_simpleOrbit_zero_le hK) hw
        hO (by rw [(simpleOrbit_spec 0).2]; exact hwv)
    · have hm : orbitVec O ∈ {v | ∃ w ∈ weylGroup, w • simpleVec 3 = v} := by
        rw [h14]
        exact ⟨⟨O, hO, rfl⟩, h8⟩
      obtain ⟨w, hw, hwv⟩ := hm
      exact orbitFixed_le_of_smul (simpleOrbit_spec 3).1 (orbitFixed_simpleOrbit_three_le hK) hw
        hO (by rw [(simpleOrbit_spec 3).2]; exact hwv)
  calc rootGenerated K = ⨆ O ∈ orbits, orbitFixed K O := rootGenerated_eq_iSup hK
    _ ≤ ⁅rootGenerated K, rootGenerated K⁆ := iSup₂_le key

theorem rootGenerated_ne_bot :
    rootGenerated K ≠ ⊥ := by
  intro h
  have hx := le_sup_left (a := posFixed K) (b := negFixed K) (xUnit_three_mem_posFixed (1 : K))
  change _ ∈ rootGenerated K at hx
  rw [h, Subgroup.mem_bot] at hx
  exact one_ne_zero (xUnit_inj (hx.trans (xUnit_zero _).symm))

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley E6SignedGraph

theorem E6_signed_graph_root_generated_perfect
    (K : Type) [Field K] (hK : ringChar K ≠ 2) :
    rootGenerated K ≠ ⊥ ∧ ⁅rootGenerated K, rootGenerated K⁆ = rootGenerated K :=
  ⟨rootGenerated_ne_bot, commutator_rootGenerated hK⟩

end CFSG.LieType.Chevalley

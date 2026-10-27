module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.QuadFourExcluded
public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableBlockZ
public import CFSG.HardMathSupport.Cooperstein.Proving.OddShortInClassX
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

variable {G : Type} [Group G]

def auxBQ (B Q X : Subgroup G) (hBX : B ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : Subgroup G where
  carrier := {p | ∃ b ∈ B, ∃ q ∈ Q, p = b * q}
  mul_mem' := by
    rintro _ _ ⟨b1, hb1, q1, hq1, rfl⟩ ⟨b2, hb2, q2, hq2, rfl⟩
    have hc : b2⁻¹ * q1 * b2 ∈ Q := by
      have h := hQn b2⁻¹ (X.inv_mem (hBX hb2)) q1 hq1
      rwa [inv_inv] at h
    refine ⟨b1 * b2, B.mul_mem hb1 hb2, b2⁻¹ * q1 * b2 * q2, Q.mul_mem hc hq2, ?_⟩
    group
  one_mem' := ⟨1, B.one_mem, 1, Q.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨b, hb, q, hq, rfl⟩
    refine ⟨b⁻¹, B.inv_mem hb, b * q⁻¹ * b⁻¹, hQn b (hBX hb) q⁻¹ (Q.inv_mem hq), ?_⟩
    group

theorem auxBQ_le {B Q X Y : Subgroup G} (hBX : B ≤ X) (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hBY : B ≤ Y) (hQY : Q ≤ Y) : auxBQ B Q X hBX hQn ≤ Y := by
  rintro _ ⟨b, hb, q, hq, rfl⟩
  exact Y.mul_mem (hBY hb) (hQY hq)

theorem le_auxBQ_left {B Q X : Subgroup G} (hBX : B ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : B ≤ auxBQ B Q X hBX hQn :=
  fun b hb => ⟨b, hb, 1, Q.one_mem, (mul_one b).symm⟩

theorem le_auxBQ_right {B Q X : Subgroup G} (hBX : B ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : Q ≤ auxBQ B Q X hBX hQn :=
  fun q hq => ⟨1, B.one_mem, q, hq, (one_mul q).symm⟩

theorem lemB_pCoreOf_le (X : Subgroup G) : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.openPCoreOf_le 2 X

theorem index_pCore_block {B Q Y : Subgroup G} (hBY : B ≤ Y)
    (hK : B ⊓ Q = CFSG.Open.pCoreOf 2 B) :
    ((Q.subgroupOf Y).subgroupOf (B.subgroupOf Y)).index = (CFSG.pCore 2 B).index := by
  have hmemQ : ∀ z : ↥B, z ∈ CFSG.pCore 2 B ↔ (z : G) ∈ Q := by
    intro z
    have h1 : z ∈ CFSG.pCore 2 B ↔ (z : G) ∈ CFSG.Open.pCoreOf 2 B := by
      rw [pCoreOf_eq_map]
      constructor
      · intro hz
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      · intro hz
        obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz
        have hcz' : c = z := Subtype.ext hcz
        rwa [hcz'] at hc
    rw [h1, ← hK]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  let e : ↥(B.subgroupOf Y) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBY
  have hmap : ((Q.subgroupOf Y).subgroupOf (B.subgroupOf Y)).map (e : ↥(B.subgroupOf Y) →* ↥B)
      = CFSG.pCore 2 B := by
    ext z
    rw [hmemQ z]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwG : ((w : ↥Y) : G) = (z : G) := congrArg Subtype.val hwz
      rw [← hwG]
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hw)
    · intro hz
      exact ⟨⟨⟨(z : G), hBY z.2⟩, Subgroup.mem_subgroupOf.mpr z.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  rw [← hmap, Subgroup.index_map_equiv]

theorem solvableSylowNormalizerAll :
    AlternatingGeometry.SolvableSylowNormalizerAll := by
  intro G _ _ X S hX hA Y hQY hYX hsolv hSY hO3
  by_contra hYN
  have hYk : CFSG.Open.IsKGroup ↥Y := hX.of_le hYX
  have hCharY : CFSG.QuasithinUnique.CharTwo Y := charTwo_of_pCoreOf_le hA.charTwo hQY hYX
  have hQX : CFSG.Open.pCoreOf 2 X ≤ X := lemB_pCoreOf_le X
  have hQn : ∀ x ∈ X, ∀ q ∈ CFSG.Open.pCoreOf 2 X, x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    fun x hx q hq => pCoreOf_two_conj_mem X hx hq
  have hcgs : cgsIn Y S = Y ⊓ Subgroup.normalizer (S : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.cgsIn_eq_of_le hA hYX
  have hne : cgsIn Y S ≠ Y := by
    intro h
    apply hYN
    rw [hcgs] at h
    exact inf_eq_left.mp h
  obtain ⟨B, hBY, hBsub, hB, hBnot⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved G Y S hYk hCharY hSY hne
  have hBX : B ≤ X := hBY.trans hYX
  have hsolvB : Group.IsSolvable ↥B := by
    have := hsolv
    have : Group.IsSolvable ↥(B.subgroupOf Y) := inferInstance
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBY).surjective
  have : ((CFSG.Open.pCoreOf 2 X).subgroupOf Y).Normal := pCoreOf_subgroupOf_normal hYX hQY
  have hO3q : CFSG.pCore 3 (↥Y ⧸ (CFSG.Open.pCoreOf 2 X).subgroupOf Y) = ⊥ :=
    pCore_three_quot_eq_bot_of_R_form hQY (fun R hQR hRY hRn hk => hO3 R hQR hRY hRn hk)
  have hKn : ∀ l ∈ B, ∀ k ∈ B ⊓ CFSG.Open.pCoreOf 2 X,
      l * k * l⁻¹ ∈ B ⊓ CFSG.Open.pCoreOf 2 X := by
    intro l hl k hk
    obtain ⟨hkB, hkQ⟩ := Subgroup.mem_inf.mp hk
    exact Subgroup.mem_inf.mpr
      ⟨B.mul_mem (B.mul_mem hl hkB) (B.inv_mem hl), hQn l (hBX hl) k hkQ⟩
  have hK2 : ∀ k ∈ B ⊓ CFSG.Open.pCoreOf 2 X, ∃ n : ℕ, k ^ 2 ^ n = 1 := fun k hk =>
    pCoreOf_two_pow_eq_one (Subgroup.mem_inf.mp hk).2
  rcases dichotomy_of_solvable hB.1 hsolvB inf_le_left hKn hK2 with hbot | hQB
  ·
    have hY'Y : auxBQ B (CFSG.Open.pCoreOf 2 X) X hBX hQn ≤ Y :=
      auxBQ_le hBX hQn hBY hQY
    have hchain : Relation.ReflTransGen
        (fun H K : Subgroup G => H ≤ K ∧ (H.subgroupOf K).Normal)
        B (auxBQ B (CFSG.Open.pCoreOf 2 X) X hBX hQn) := by
      have h1 := isSubnormal_inf_of_le hBsub _ hY'Y
      rw [inf_eq_left.mpr (le_auxBQ_left hBX hQn)] at h1
      exact reflTransGen_of_isSubnormal h1
    have hBbot : B = ⊥ :=
      OddShortInClassX.eq_bot_of_K1_inClassX (Y := auxBQ B (CFSG.Open.pCoreOf 2 X) X hBX hQn)
        hA.charTwo hBX (auxBQ_le hBX hQn hBX hQX)
        (le_auxBQ_left hBX hQn) (le_auxBQ_right hBX hQn)
        (fun p hp => hp) hbot hB hchain
    exact hBnot (by rw [hBbot]; exact bot_le)
  ·
    have hK : B ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 B := hQB
    have hidx3 : ((((CFSG.Open.pCoreOf 2 X).subgroupOf Y).subgroupOf (B.subgroupOf Y))).index = 3 := by
      rw [index_pCore_block hBY hK]
      exact index_pCore_eq_three hB.1 hsolvB
    have hBQ : B ≤ CFSG.Open.pCoreOf 2 X :=
      le_of_index_three_block hBY (isSubnormal_subgroupOf_of_open hBsub) hO3q hidx3
    have hBS : B ≤ S := hBQ.trans (pCoreOf_le_of_isSylowTwoOf hYX hQY hSY)
    have hBcgs : B ≤ cgsIn Y S := by
      rw [hcgs]
      exact le_inf hBY (hBS.trans Subgroup.le_normalizer)
    exact hBnot hBcgs

theorem eightTwoExcluded_proved :
    AlternatingGeometry.EightTwoExcluded :=
  AlternatingGeometry.eightTwoExcluded_of_lemmaB solvableSylowNormalizerAll

theorem quadFourExcluded_proved :
    AlternatingGeometry.QuadFourExcluded :=
  AlternatingGeometry.quadFourExcluded_of_lemmaB solvableSylowNormalizerAll

end CFSG.HardMathSupport.Cooperstein.Proving

end

module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Basic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusion
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.EvenSmallLie
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)

section Centralizer

variable {M : Type*} [Group M]

theorem centralizer_map_eq_of_map_eq {B : Subgroup M} (ι : M ≃* M)
    (hι : B.map ι.toMonoidHom = B) :
    (centralizer (B : Set M)).map ι.toMonoidHom = centralizer (B : Set M) := by
  have key : ∀ κ : M ≃* M, B.map κ.toMonoidHom = B →
      (centralizer (B : Set M)).map κ.toMonoidHom ≤ centralizer (B : Set M) := by
    intro κ hκ
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [← hκ] at hh
    obtain ⟨b, hb, rfl⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hx b hb]
  refine le_antisymm (key ι hι) fun x hx => ?_
  have hι' : B.map ι.symm.toMonoidHom = B := by
    conv_lhs => rw [← hι]
    rw [Subgroup.map_map]
    convert Subgroup.map_id B
    ext y
    simp
  have hy : ι.symm x ∈ centralizer (B : Set M) := key ι.symm hι' ⟨x, hx, rfl⟩
  exact ⟨ι.symm x, hy, by simp⟩

theorem inf_centralizer_subgroupOf_eq {Mz B : Subgroup M} (hB : B ≤ Mz) :
    (Mz ⊓ centralizer (B : Set M)).subgroupOf Mz = centralizer ((B.subgroupOf Mz : Subgroup Mz) :
      Set Mz) := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_iff, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨-, hx⟩ h hh
    exact Subtype.ext (hx h (mem_subgroupOf.mp hh))
  · intro hx
    refine ⟨x.2, fun h hh => ?_⟩
    have := hx ⟨h, hB hh⟩ (mem_subgroupOf.mpr hh)
    exact congrArg Subtype.val this

end Centralizer

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_le_centralizer_singleton (e : L ≃* matrixProjectiveDerived Q)
    {B : Subgroup (matrixProjectiveDerived Q)} {w : matrixProjectiveDerived Q}
    (hB : B ≤ centralizer {w}) :
    (B.map e.symm.toMonoidHom).map L.subtype ≤ centralizer ({(e.symm w : G)} : Set G) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_singleton_iff.mp (hB hx)
  simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]

theorem le_centralizer_stabPairsBar_of_conj_eq_mul (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    {P₃ : HypPair Q} (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃)
    (hBq : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hBcard : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    (e : L ≃* matrixProjectiveDerived Q) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {g : G}
    (hg : g⁻¹ * t * g = t * (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G))
    (hzg : ∃ hz : g * (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) * g⁻¹ ∈ L,
      IsLongRoot Q (e ⟨_, hz⟩))
    {y₀ : matrixProjectiveDerived Q} (hy₀M : y₀ ∈ rootLeviBar Q ha.hypPair hb.hypPair)
    (hy₀B : y₀ ∈ centralizer (stabPairsBar Q a a' b b' : Set (matrixProjectiveDerived Q)))
    (hy₀1 : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀)) {S : Subgroup G} (hSperf : ⁅S, S⁆ = S)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSy : S ≤ centralizer ({(e.symm y₀ : G)} : Set G))
    (hzS : (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) ∈ S) :
    S ≤ centralizer ((((stabPairsBar Q a a' b b').map e.symm.toMonoidHom).map L.subtype :
      Subgroup G) : Set G) := by
  have h₁₂ := ha.orth hb hd
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  set z₀ := rootPairElt hQ h₁₂ h₁₃ h₂₃ with hz₀def
  set B := stabPairsBar Q a a' b b' with hBdef
  set Mz := rootLeviBar Q ha.hypPair hb.hypPair with hMzdef
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hBq.1.1
  have hCperf := commutator_centralizer_rootPairElt_of ha hb hd hQ h₁₃ h₂₃ hl0 hl1 hBperf
  have hC := centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  have hF3 : perfectCore (centralizer ({z₀} : Set (matrixProjectiveDerived Q))) =
      rootRadicalBar Q ha.hypPair hb.hypPair ⊔ Mz := by
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect hCperf]
    exact hC
  obtain ⟨hzL, hzl⟩ := hzg
  obtain ⟨c'', hc''⟩ := isConj_iff.mp (isConj_of_isLongRoot hQ h₁₂ h₁₃ h₂₃ hzl
    (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃))
  obtain ⟨φ', hφ', hφ'r, hφ'z⟩ := EPilot.exists_coords_conjugate e g hc''
  have hφ'z' : φ' z₀ = (e.symm z₀ : G) := by
    rw [hφ'z, MulEquiv.symm_apply_apply]
    group
  have hBM : B ≤ Mz := stabPairsBar_le_rootLeviBar ha hb
  have hMz : Mz ≤ centralizer {z₀} := hC ▸ le_sup_right
  have hJι : ∀ ι : Mz ≃* Mz, ((Mz ⊓ centralizer (B : Set _)).subgroupOf Mz).map ι.toMonoidHom =
      (Mz ⊓ centralizer (B : Set _)).subgroupOf Mz := by
    intro ι
    rw [inf_centralizer_subgroupOf_eq hBM]
    exact centralizer_map_eq_of_map_eq ι (map_stabPairsBar_subgroupOf_eq ha hb hd hBq hBcard ι)
  refine le_centralizer_of_coords_orth hset hOut e ht htC (rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃) hg
    hφ' hφ'r hφ'z' _ Mz hF3 (isPGroup_rootRadicalBar _ _) (rootLeviBar_le_normalizer h₁₂)
    (disjoint_rootRadicalBar_rootLeviBar h₁₂)
    (fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of ha hb hd hQ hT hBq N hN h2)
    inf_le_left hJι ?_ ⟨hy₀M, hy₀B⟩ hy₀1 hy₀o hSperf hSsimple hSt hSy hzS
    (fun x hx => by obtain ⟨_, ⟨y, -, rfl⟩, rfl⟩ := hx; exact (e.symm y).2)
    (map_le_centralizer_singleton e (hBM.trans hMz))
    (map_le_centralizer_singleton e fun x hx => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hy₀B x hx))
    (by rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hBperf])
  intro y hy hy1 hyo S' R' hS'y hS'gen hR'z hR'y hR'perf
  exact le_centralizer_of_model ha hb hd hQ h₁₃ h₂₃ hBq.2 hy.1 hy.2 hy1 hyo hS'y hS'gen hR'z hR'y
    hR'perf

end Core

section Torus

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

omit [Field K] in
theorem torusLin_single_of_ne' [Field K] {u v w : Fin d} (hwu : w ≠ u) (hwv : w ≠ v) (l : Kˣ) :
    torusLin u v l (Pi.single w (1 : K)) = Pi.single w 1 := by
  ext i
  rw [torusLin_apply]
  by_cases hi : i = w
  · subst hi
    simp [torusEntry, hwu, hwv]
  · simp [hi]

variable (a a' b b') in
@[expose] noncomputable def orthTorusLin (l : Kˣ) : (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  torusLin a a' l * torusLin b b' l⁻¹

theorem orthTorusLin_apply_of_inW (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b') (l : Kˣ)
    {x : Fin d → K} (hx : InW ha.hypPair hb.hypPair x) : orthTorusLin a a' b b' l x = x := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [IsHypCoord.hypPair_e, IsHypCoord.hypPair_f, ha.polar_left, ha.polar_right,
    hb.polar_left, hb.polar_right] at x1 x2 x3 x4
  ext i
  rw [orthTorusLin, LinearEquiv.mul_apply, torusLin_apply, torusLin_apply]
  by_cases h1 : i = a
  · subst h1; rw [x2]; ring
  by_cases h2 : i = a'
  · subst h2; rw [x1]; ring
  by_cases h3 : i = b
  · subst h3; rw [x4]; ring
  by_cases h4 : i = b'
  · subst h4; rw [x3]; ring
  simp [torusEntry, h1, h2, h3, h4]

theorem orthTorusLin_e (hd : PairDisjoint a a' b b') (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (l : Kˣ) :
    orthTorusLin a a' b b' l (Pi.single a 1) = (l : K) • Pi.single a 1 ∧
      orthTorusLin a a' b b' l (Pi.single a' 1) = ((l⁻¹ : Kˣ) : K) • Pi.single a' 1 ∧
      orthTorusLin a a' b b' l (Pi.single b 1) = ((l⁻¹ : Kˣ) : K) • Pi.single b 1 ∧
      orthTorusLin a a' b b' l (Pi.single b' 1) = (l : K) • Pi.single b' 1 := by
  simp only [orthTorusLin, LinearEquiv.mul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [torusLin_single_of_ne' hd.left_ne_left.symm hd.right_ne_left.symm,
      torusLin_single_left ha.ne]
  · rw [torusLin_single_of_ne' hd.left_ne_right.symm hd.right_ne_right.symm,
      torusLin_single_right ha.ne]
  · rw [torusLin_single_left hb.ne, map_smul, torusLin_single_of_ne' hd.left_ne_left hd.left_ne_right]
  · rw [torusLin_single_right hb.ne, map_smul,
      torusLin_single_of_ne' hd.right_ne_left hd.right_ne_right, inv_inv]

variable [Finite K] [CharP K 2]

theorem orthTorusLin_mem_orthDerived (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (l : Kˣ) : orthTorusLin a a' b b' l ∈ orthDerived Q :=
  mul_mem (ha.torusLin_mem_orthDerived l) (hb.torusLin_mem_orthDerived l⁻¹)

@[expose] noncomputable def orthTorusElt (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (l : Kˣ) : matrixProjectiveDerived Q :=
  projHom Q ⟨orthTorusLin a a' b b' l, orthTorusLin_mem_orthDerived ha hb l⟩

theorem orthTorusElt_spec (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {l : Kˣ} (hl : l ≠ 1) :
    orthTorusElt ha hb l ∈ rootLeviBar Q ha.hypPair hb.hypPair ∧
      orthTorusElt ha hb l ∈ centralizer (stabPairsBar Q a a' b b' :
        Set (matrixProjectiveDerived Q)) ∧
      orthTorusElt ha hb l ≠ 1 ∧ Odd (orderOf (orthTorusElt ha hb l)) := by
  classical
  have h₁₂ := ha.orth hb hd
  have hQ' := ha.exists_ne_zero
  set T := orthTorusLin a a' b b' l with hTdef
  obtain ⟨t1, t2, t3, t4⟩ := orthTorusLin_e hd ha hb l
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (ha.torusLin_mem_orthogonalGroup l) (hb.torusLin_mem_orthogonalGroup l⁻¹)
  have hll : ((l : K) * ((l⁻¹ : Kˣ) : K)) = 1 := by simp
  have hll' : (((l⁻¹ : Kˣ) : K) * (l : K)) = 1 := by simp
  have hTz : T * eichler Q ha.hypPair.e hb.hypPair.e = eichler Q ha.hypPair.e hb.hypPair.e * T := by
    rw [← mul_inv_eq_iff_eq_mul, eichler_conj hTO]
    simp only [IsHypCoord.hypPair_e]
    rw [t1, t3, eichler_smul_left, smul_smul, hll, one_smul]
  have hTz' : T * eichler Q ha.hypPair.f hb.hypPair.f =
      eichler Q ha.hypPair.f hb.hypPair.f * T := by
    rw [← mul_inv_eq_iff_eq_mul, eichler_conj hTO]
    simp only [IsHypCoord.hypPair_f]
    rw [t2, t4, eichler_smul_left, smul_smul, hll', one_smul]
  have hTL : T ∈ rootLevi Q ha.hypPair hb.hypPair :=
    ⟨⟨hTO, mem_centralizer_singleton_iff.mpr hTz⟩, mem_centralizer_singleton_iff.mpr hTz'⟩
  refine ⟨⟨⟨T, _⟩, mem_subgroupOf.mpr hTL, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩
    obtain ⟨⟨x1, x3⟩, x2, x4⟩ := mem_subgroupOf.mp hX
    have hXO : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ X.2
    have hcomm := commute_of_fixW_of_fix (g := T) (h := (X : (Fin d → K) ≃ₗ[K] (Fin d → K)))
      h₁₂ (fun x hx => orthTorusLin_apply_of_inW ha hb l hx) hXO ⟨x1, x3, x2, x4⟩
      ⟨by simp only [IsHypCoord.hypPair_e]; rw [t1, map_smul, x1],
        by simp only [IsHypCoord.hypPair_f]; rw [t2, map_smul, x3],
        by simp only [IsHypCoord.hypPair_e]; rw [t3, map_smul, x2],
        by simp only [IsHypCoord.hypPair_f]; rw [t4, map_smul, x4]⟩
    rw [orthTorusElt, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm.symm
  · intro h1
    rw [orthTorusElt, ← map_one (projHom Q)] at h1
    have h2 := congrArg Subtype.val (projHom_injective hQ' h1)
    have h3 := LinearEquiv.congr_fun h2 (Pi.single a 1)
    simp only [OneMemClass.coe_one] at h3
    rw [t1] at h3
    have h4 := congrFun h3 a
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4
    exact hl (Units.ext (by simpa using h4))
  ·
    have := Fintype.ofFinite K
    have hcomm : Commute (torusLin a a' l) (torusLin b b' l⁻¹) := by
      refine LinearEquiv.ext fun v => funext fun i => ?_
      simp only [LinearEquiv.mul_apply, torusLin_apply]
      ring
    have hpow : T ^ (Fintype.card K - 1) = 1 := by
      rw [hTdef, orthTorusLin, hcomm.mul_pow, ← map_pow, ← map_pow]
      have hl1 : l ^ (Fintype.card K - 1) = 1 :=
        Units.ext (by simpa using FiniteField.pow_card_sub_one_eq_one (l : K) l.ne_zero)
      rw [inv_pow, hl1, inv_one, map_one, map_one, one_mul]
    have hy : (orthTorusElt ha hb l) ^ (Fintype.card K - 1) = 1 := by
      rw [orthTorusElt, ← map_pow, ← map_one (projHom Q)]
      congr 1
      exact Subtype.ext (by simpa using hpow)
    have h2 : 2 ∣ Fintype.card K := by
      have := FiniteField.cast_card_eq_zero K
      exact (CharP.cast_eq_zero_iff K 2 _).mp this
    have hodd : Odd (Fintype.card K - 1) :=
      Nat.Even.sub_odd Fintype.card_pos (even_iff_two_dvd.mpr h2) odd_one
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hy)

end Torus

section TwoSided

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem exists_conj_eq_mul_forall_le_centralizer_of_twoSided (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    {P₃ : HypPair Q} (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃)
    (hBq : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hBcard : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    (e : L ≃* matrixProjectiveDerived Q) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G))
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot Q (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot Q (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    {y₀ : matrixProjectiveDerived Q} (hy₀M : y₀ ∈ rootLeviBar Q ha.hypPair hb.hypPair)
    (hy₀B : y₀ ∈ centralizer (stabPairsBar Q a a' b b' : Set (matrixProjectiveDerived Q)))
    (hy₀1 : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀)) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer ({(e.symm y₀ : G)} : Set G) →
        (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) ∈ S →
        S ≤ centralizer ((((stabPairsBar Q a a' b b').map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G) := by
  have h₁₂ := ha.orth hb hd
  set z₀ := rootPairElt hQ h₁₂ h₁₃ h₂₃ with hz₀def
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩⟩ := hR5
  obtain ⟨c', hc'⟩ := isConj_iff.mp (isConj_of_isLongRoot hQ h₁₂ h₁₃ h₂₃ hzl
    (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃))
  rw [← hz₀def] at hc'
  set c : L := e.symm c'⁻¹ with hcdef
  have htc : ∀ m ∈ L, t * m = m * t := fun m hm => (mem_centralizer_iff.mp htC m hm).symm
  have hcz : (c : G)⁻¹ * z * c = (e.symm z₀ : G) := by
    have h1 : (c⁻¹ * ⟨z, hzL⟩ * c : L) = e.symm z₀ := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hcdef,
        MulEquiv.apply_symm_apply, inv_inv, ← hc']
    rw [← h1]
    rfl
  have hxzx : x * z * x⁻¹ ∈ L := by
    obtain ⟨m, hm, hmz⟩ := hzx
    rw [← hmz]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show x * (x⁻¹ * m * x) * x⁻¹ = m by group]
    exact hm
  have hsymm : (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) = x * z * x⁻¹ := by
    set w : G := (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) with hw
    have h1 := coe_conjugateMulEquiv L x ((conjugateMulEquiv L x).symm ⟨z, hzx⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have h1' : z = x⁻¹ * w * x := h1
    calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [← h1']
  refine ⟨x * c, ?_, fun S hSperf hSsimple hSt hSy hzS => ?_⟩
  · rw [← hcz, show (x * (c : G))⁻¹ * t * (x * c) = (c : G)⁻¹ * (x⁻¹ * t * x) * c by group, hxz,
      show (c : G)⁻¹ * (t * z) * c = (c : G)⁻¹ * t * (z * c) by group, ← htc _ (inv_mem c.2)]
    group
  · refine le_centralizer_stabPairsBar_of_conj_eq_mul hset hOut hq ha hb hd hQ h₁₃ h₂₃ hBq hBcard
      e ht htC ?_ ?_ hy₀M hy₀B hy₀1 hy₀o hSperf hSsimple hSt hSy hzS
    · rw [← hcz, show (x * (c : G))⁻¹ * t * (x * c) = (c : G)⁻¹ * (x⁻¹ * t * x) * c by group,
        hxz, show (c : G)⁻¹ * (t * z) * c = (c : G)⁻¹ * t * (z * c) by group,
        ← htc _ (inv_mem c.2)]
      group
    · have he : x * (c : G) * (e.symm z₀ : G) * (x * c)⁻¹ = x * z * x⁻¹ := by
        rw [← hcz]; group
      refine ⟨he ▸ hxzx, ?_⟩
      have hzz : (⟨x * (c : G) * (e.symm z₀ : G) * (x * c)⁻¹, he ▸ hxzx⟩ : L) =
          (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := Subtype.ext (he.trans hsymm.symm)
      rw [hzz]
      exact hzl'

theorem exists_conj_eq_mul_forall_le_centralizer_minus (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQdef : Q = coordinateQuadMinus n K (by omega) β γ) (e : L ≃* matrixProjectiveDerived Q)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a a' b b' : Fin (2 * n)} (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate) {P₃ : HypPair Q}
    (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃)
    (hBq : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hBcard : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    {y₀ : matrixProjectiveDerived Q} (hy₀M : y₀ ∈ rootLeviBar Q ha.hypPair hb.hypPair)
    (hy₀B : y₀ ∈ centralizer (stabPairsBar Q a a' b b' : Set (matrixProjectiveDerived Q)))
    (hy₀1 : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀)) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer ({(e.symm y₀ : G)} : Set G) →
        (e.symm (rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃) : G) ∈ S →
        S ≤ centralizer ((((stabPairsBar Q a a' b b').map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK; omega
    · exact h
  have hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot Q (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot Q (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) := by
    subst hQdef
    obtain ⟨x, z, hz, hxz, hzl, hzl', -⟩ :=
      exists_conj_eq_mul_longRoot_twoSided_minus hset hn hK hq hirr e ht hKt
    exact ⟨x, z, hz, hxz, hzl, hzl'⟩
  have hOut : Group.IsSolvable (Outer L) := by
    subst hQdef
    exact isSolvable_outer_of_mulEquiv_minus hn hf hK hirr e
  exact exists_conj_eq_mul_forall_le_centralizer_of_twoSided hset.standardSetting hOut hq ha hb
    hd hQ h₁₃ h₂₃ hBq hBcard e ht (mem_centralizer_of_inf_eq hKt) hR5 hy₀M hy₀B hy₀1 hy₀o

end TwoSided

end CFSG.SeitzReduction.OmegaPilot

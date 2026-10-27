module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveLift
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSix

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem exists_sq_mem_of_lt {T P : Subgroup X} (hP2 : IsPGroup 2 P) (hTP : T < P) :
    ∃ y ∈ P, y ∈ Subgroup.normalizer (T : Set X) ∧ y ∉ T ∧ y * y ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup P := T.subgroupOf P with hIdef
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    obtain ⟨x, hxP, hxT⟩ := IsConcreteLE.exists_of_lt hTP
    have hx : (⟨x, hxP⟩ : P) ∈ I := by
      rw [htop]
      trivial
    exact hxT (Subgroup.mem_subgroupOf.mp hx)
  have : Group.IsNilpotent P := hP2.isNilpotent
  have hlt : I < Subgroup.normalizer (I : Set P) :=
    Group.normalizerCondition_of_isNilpotent (G := P) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : X) ∈ Subgroup.normalizer (T : Set X) := by
    have hxsub : x ∈ (Subgroup.normalizer (T : Set X)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq (le_of_lt hTP)]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  have hxT : (x : X) ∉ T := fun h => hxI (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨e, he⟩ := hP2 x
  have hex : ∃ k : ℕ, (x : X) ^ (2 ^ k) ∈ T :=
    ⟨e, by rw [show (x : X) ^ 2 ^ e = ((x ^ 2 ^ e : P) : X) by simp, he]; exact T.one_mem⟩
  classical
  obtain ⟨k, hk, hmin⟩ : ∃ k : ℕ, (x : X) ^ (2 ^ k) ∈ T ∧ ∀ m < k, (x : X) ^ (2 ^ m) ∉ T :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hk
    exact hxT hk
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hk' : (x : X) ^ (2 ^ k') ∉ T := hmin k' (Nat.lt_succ_self k')
  refine ⟨(x : X) ^ (2 ^ k'), P.pow_mem x.2 _, Subgroup.pow_mem _ hxNorm _, hk', ?_⟩
  rw [← pow_two, ← pow_mul, ← pow_succ]
  exact hk

theorem exists_invariant_sylow' {K P : Subgroup X} (hP : IsPGroup 2 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) :
    ∃ Q : Subgroup X, IsSylowOf 2 Q K ∧ P ≤ Subgroup.normalizer (Q : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hle⟩ := AschbacherTheorem3.exists_isSylowOf_le hP (le_sup_right : P ≤ K ⊔ P)
  refine ⟨S ⊓ K, hS.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hPK),
    fun p hp => ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hle hp), hPK hp⟩

end Abstract

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem conj_mem_factorZStar {i : Fin r} {c z : G} (hc : c ∈ aschbacherThm5Preimage D (Abar i))
    (hz : z ∈ factorZStar D Abar i) : c * z * c⁻¹ ∈ factorZStar D Abar i := by
  have hAH : aschbacherThm5Preimage D (Abar i) ≤ Subgroup.normalizer (D : Set G) :=
    (preimage_le D _).trans Subgroup.le_normalizer
  have hzA : z ∈ aschbacherThm5Preimage D (Abar i) := hz.1
  have hczA : c * z * c⁻¹ ∈ aschbacherThm5Preimage D (Abar i) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hzA) (Subgroup.inv_mem _ hc)
  have hzC := (Five.mem_factorZStar_iff (w := ⟨z, hAH hzA⟩) hzA).mp hz
  refine (Five.mem_factorZStar_iff (w := ⟨c * z * c⁻¹, hAH hczA⟩) hczA).mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcy : (toBar D ⟨c, hAH hc⟩)⁻¹ * y * toBar D ⟨c, hAH hc⟩ ∈
      bar D (aschbacherThm5Preimage D (Abar i)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (toBar_mem_bar D hc)) hy)
      (toBar_mem_bar D hc)
  have h1 := (Subgroup.mem_centralizer_iff.mp hzC) _ hcy
  have hsplit : toBar D ⟨c * z * c⁻¹, hAH hczA⟩ =
      toBar D ⟨c, hAH hc⟩ * toBar D ⟨z, hAH hzA⟩ * (toBar D ⟨c, hAH hc⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hsplit]
  calc y * (toBar D ⟨c, hAH hc⟩ * toBar D ⟨z, hAH hzA⟩ * (toBar D ⟨c, hAH hc⟩)⁻¹) =
        toBar D ⟨c, hAH hc⟩ * (((toBar D ⟨c, hAH hc⟩)⁻¹ * y * toBar D ⟨c, hAH hc⟩) *
          toBar D ⟨z, hAH hzA⟩) * (toBar D ⟨c, hAH hc⟩)⁻¹ := by group
    _ = toBar D ⟨c, hAH hc⟩ * (toBar D ⟨z, hAH hzA⟩ *
          ((toBar D ⟨c, hAH hc⟩)⁻¹ * y * toBar D ⟨c, hAH hc⟩)) * (toBar D ⟨c, hAH hc⟩)⁻¹ := by
        rw [h1]
    _ = toBar D ⟨c, hAH hc⟩ * toBar D ⟨z, hAH hzA⟩ * (toBar D ⟨c, hAH hc⟩)⁻¹ * y := by group

theorem le_normalizer_orbitProduct (hyp : Hyp61 G D r Abar) {P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) {I : Set (Fin r)}
    (hI : ∀ p ∈ P, ∀ k ∈ I, ∀ l, (aschbacherThm5Preimage D (Abar k)).map
      (MulAut.conj p).toMonoidHom = aschbacherThm5Preimage D (Abar l) → l ∈ I) :
    P ≤ Subgroup.normalizer (orbitProduct D Abar I : Set G) := by
  intro p hp
  apply AschbacherToolkit.mem_normalizer_of_conj_le
  have hle : orbitProduct D Abar I ≤
      (orbitProduct D Abar I).comap (MulAut.conj p).toMonoidHom := by
    refine iSup₂_le fun k hk => ?_
    obtain ⟨l, hl⟩ := hyp.hperm p (hPH hp) k
    rw [← Subgroup.map_le_iff_le_comap, hl]
    exact factor_le_orbitProduct (hI p hp k hk l hl)
  exact fun y hy => hle hy

theorem eq_one_of_mem_cross (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) (hr : 3 ≤ r) {i k : Fin r} {x : G}
    (hx : x ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g) {B : Subgroup G}
    (hBk : B ≤ centralizing D (Abar k)) {t : G}
    (ht : t ∈ (rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊔
      rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar i)) g) x) ⊓ B)
    (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) : t = 1 := by
  by_contra ht1
  have hC' := hC.conj g
  have hxH' : x⁻¹ ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [normalizer_rightConjugate]
    exact Subgroup.inv_mem _ hx
  obtain ⟨i', hi'⟩ := hC'.hyp.hperm x⁻¹ hxH' i
  have hLx : rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar i)) g) x =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i') := by
    rw [← hi', preimage_conjFactors]
    rfl
  obtain ⟨m, hmi, hmi'⟩ := Six.exists_third hr i i'
  have hLm : rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊔
      rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar i)) g) x ≤
        centralizing (rightConjugate D g) (conjFactors D Abar g m) := by
    rw [hLx, ← preimage_conjFactors D Abar g i]
    exact sup_le (factor_le_centralizing hC'.hyp.hcomm (Ne.symm hmi).symm)
      (factor_le_centralizing hC'.hyp.hcomm (Ne.symm hmi').symm)
  apply hg
  exact SixTools.mem_normalizer_of_fusion_conj hC (g := g) (y := t) ht2 ht1
    (centralizes_of_mem_centralizing (hBk ht.2))
    (centralizes_of_mem_centralizing (hLm ht.1))

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5

module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeTwoThree
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneP

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ThreeTen.conj_self_eq_of_centralizes {U : Subgroup G} {g u : G}
    (hg : g ∈ Subgroup.centralizer (U : Set G)) (hu : u ∈ U) : g * u * g⁻¹ = u := by
  rw [← Subgroup.mem_centralizer_iff.mp hg u hu, mul_inv_cancel_right]

omit [Finite G] in
theorem ThreeTen.mem_centralizer_conj_of_normalizes {U : Subgroup G} {g t : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) (ht : t ∈ Subgroup.centralizer (U : Set G)) :
    g * t * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hu' : g⁻¹ * u * g ∈ U := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
  have h := Subgroup.mem_centralizer_iff.mp ht _ hu'
  calc u * (g * t * g⁻¹) = g * ((g⁻¹ * u * g) * t) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = g * t * g⁻¹ * u := by group

theorem ThreeTen.le_of_isSylowOf_of_normalizes_two {T N P : Subgroup G} (hT : IsSylowOf 2 T N)
    (hP : IsPGroup 2 ↥P) (hPN : P ≤ N) (hTP : T ≤ Subgroup.normalizer (P : Set G)) : P ≤ T :=
  le_sup_right.trans (Nine.le_of_isSylowOf_of_le hT
    (IsPGroup.to_sup_of_normal_right' hT.2.1 hP hTP) le_sup_left (sup_le hT.1 hPN))

omit [Finite G] in
@[expose] def ThreeTen.oTwoStab (M U : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ M ⊓ Subgroup.centralizer (U : Set G) ∧
    ∀ q ∈ oTwoIn M, g * q * g⁻¹ * q⁻¹ ∈ U}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    refine ⟨mul_mem hg hh, fun q hq => ?_⟩
    have e : g * h * q * (g * h)⁻¹ * q⁻¹ =
        g * (h * q * h⁻¹ * q⁻¹) * g⁻¹ * (g * q * g⁻¹ * q⁻¹) := by group
    rw [e, ThreeTen.conj_self_eq_of_centralizes (Subgroup.mem_inf.mp hg).2 (hhq q hq)]
    exact mul_mem (hhq q hq) (hgq q hq)
  inv_mem' := by
    rintro g ⟨hg, hgq⟩
    refine ⟨inv_mem hg, fun q hq => ?_⟩
    have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ = g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e, ThreeTen.conj_self_eq_of_centralizes (inv_mem (Subgroup.mem_inf.mp hg).2)
      (inv_mem (hgq q hq))]
    exact inv_mem (hgq q hq)

omit [Finite G] in
theorem ThreeTen.isPGroup_oTwoStab {M U : Subgroup G} (hMc : IsCharacteristicP 2 ↥M)
    (hU : ∀ u ∈ U, u ^ 2 = 1) : IsPGroup 2 ↥(ThreeTen.oTwoStab M U) := by
  rintro ⟨g, ⟨hgM, hgC⟩, hgq⟩
  have hsq : g * g ∈ oTwoIn M := by
    refine ThreeSix.mem_oTwoIn_of_mem_centralizer hMc (mul_mem hgM hgM)
      (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
    obtain ⟨c, hc, hcq⟩ : ∃ c ∈ U, g * q * g⁻¹ = c * q := ⟨_, hgq q hq, by group⟩
    have h3 : g * g * q * (g * g)⁻¹ = q := by
      calc g * g * q * (g * g)⁻¹ = g * (g * q * g⁻¹) * g⁻¹ := by group
        _ = g * (c * q) * g⁻¹ := by rw [hcq]
        _ = (g * c * g⁻¹) * (g * q * g⁻¹) := by group
        _ = c * (c * q) := by rw [ThreeTen.conj_self_eq_of_centralizes hgC hc, hcq]
        _ = c ^ 2 * q := by rw [pow_two, mul_assoc]
        _ = q := by rw [hU c hc, one_mul]
    calc q * (g * g) = (g * g * q * (g * g)⁻¹) * (g * g) := by rw [h3]
      _ = g * g * q := by group
  obtain ⟨k, hk⟩ := isPGroup_oTwoIn M ⟨_, hsq⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h2 : (g * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [← pow_two] at h2
  simpa [pow_succ', pow_mul] using h2

theorem ThreeTen.mem_normalizer_oTwoStab {M U : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer (ThreeTen.oTwoStab M U : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  obtain ⟨htMC, htq⟩ := ht
  obtain ⟨htM, htC⟩ := Subgroup.mem_inf.mp htMC
  refine ⟨Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM),
    ThreeTen.mem_centralizer_conj_of_normalizes hgU htC⟩, fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g ∈ oTwoIn M := by
    simpa using conj_mem_oTwoIn (Subgroup.le_normalizer (M.inv_mem hgM)) hq
  have e : g * t * g⁻¹ * q * (g * t * g⁻¹)⁻¹ * q⁻¹ =
      g * (t * (g⁻¹ * q * g) * t⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hgU _).mp (htq _ hq')

theorem normalClosureIn_le_of_commutator_le {X M R W : Subgroup G} (hX : IsShortGroup ↥X)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) (hWR : W ≤ R)
    (hRW : ⁅R, W⁆ ≤ blockU X) :
    normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) W ≤ R := by
  have hRC : R ≤ Subgroup.centralizer (blockU X : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (blockU_le_inf_centralizer_of_isSylowOf hX hXM hR hu)).2 r hr).symm
  have hRM : R ≤ M := hR.1.trans inf_le_right
  have hQR : oTwoIn M ≤ R :=
    oTwoIn_le_of_isSylowOf_centralizerModCore_inf hX.residual_eq hXM hsub hR
  have hS2 := ThreeTen.isPGroup_oTwoStab (U := blockU X) hMc
    fun u hu => pow_two_eq_one_of_mem_blockU hX hu
  have hSM : ThreeTen.oTwoStab M (blockU X) ≤ M := fun g hg => (Subgroup.mem_inf.mp hg.1).1
  have hNS : ∀ g ∈ M ⊓ Subgroup.centralizer (blockU X : Set G),
      g ∈ Subgroup.normalizer (ThreeTen.oTwoStab M (blockU X) : Set G) := fun g hg =>
    ThreeTen.mem_normalizer_oTwoStab (Subgroup.mem_inf.mp hg).1
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hg).2)
  have hSC := le_centralizerModCore_of_le_normalizer hX.residual_eq hXM hsub hS2 hSM
    fun x hx => ThreeTen.mem_normalizer_oTwoStab (hXM hx) (le_normalizer_blockU X hx)
  have hSR : ThreeTen.oTwoStab M (blockU X) ≤ R :=
    ThreeTen.le_of_isSylowOf_of_normalizes_two hR hS2 (le_inf hSC hSM)
      fun r hr => hNS r (Subgroup.mem_inf.mpr ⟨hRM hr, hRC hr⟩)
  have hWS : W ≤ ThreeTen.oTwoStab M (blockU X) := fun w hw =>
    ⟨Subgroup.mem_inf.mpr ⟨hRM (hWR hw), hRC (hWR hw)⟩, fun q hq => by
      have h1 : ⁅q, w⁆ ∈ blockU X := hRW (Subgroup.commutator_mem_commutator (hQR hq) hw)
      have e : w * q * w⁻¹ * q⁻¹ = ⁅q, w⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact inv_mem h1⟩
  refine le_trans ((Subgroup.closure_le _).2 ?_) hSR
  rintro _ ⟨k, hk, w, hw, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hNS k hk) w).mp (hWS hw)

theorem ThreeTen.mem_normalizer_normalClosureIn {K W : Subgroup G} {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (normalClosureIn K W : Set G) := by
  have hle : normalClosureIn K W ≤ (normalClosureIn K W).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.subset_closure ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgK k).mp hk,
      g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgW w).mp hw, by group⟩
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have h := hle hz
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem ThreeTen.mem_normalizer_inf_centralizer_blockU {M U : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype fun _ hk => Subgroup.mem_inf.mpr
    ⟨M.mul_mem (M.mul_mem hgM (Subgroup.mem_inf.mp hk).1) (M.inv_mem hgM),
      ThreeTen.mem_centralizer_conj_of_normalizes hgU (Subgroup.mem_inf.mp hk).2⟩

theorem normalizer_normalClosureIn_le_of_threeOne {X M W : Subgroup G}
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hXM : X ≤ M) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hV2 : IsPGroup 2 ↥(normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) W))
    (hV1 : normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) W ≠ ⊥) :
    Subgroup.normalizer
      (normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) W : Set G) ≤ M := by
  obtain ⟨H, hNH, hH⟩ := exists_isMaximalTwoLocal_ge (isPLocal_normalizer_of_isPGroup hV2 hV1)
  have hXK : X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) ≤ Subgroup.normalizer
      (normalClosureIn (M ⊓ Subgroup.centralizer (blockU X : Set G)) W : Set G) :=
    sup_le (fun x hx => ThreeTen.mem_normalizer_normalClosureIn
        (ThreeTen.mem_normalizer_inf_centralizer_blockU (hXM hx) (le_normalizer_blockU X hx))
        (hXW hx))
      le_normalizer_normalClosureIn
  have hmem : H ∈ maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) :=
    ⟨hH, fun g hg => hNH (hXK hg)⟩
  rw [h31, Set.mem_singleton_iff] at hmem
  exact hmem ▸ hNH

end CFSG.CGT.PushingUpLit.ThmOne

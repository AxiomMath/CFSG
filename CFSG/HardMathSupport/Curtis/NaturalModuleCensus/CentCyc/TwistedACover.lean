module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBar
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

theorem exists_hypCoverBar {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hd : IdxTwistedA d.1) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ) (h : UnitaryFieldData 2 f K) (r ε : ℕ)
      (π : hypSU h r ε →* X), 1 ≤ r ∧ ε ≤ 1 ∧
      (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f) ∧ Function.Surjective π ∧
      ∀ g, π g = 1 ↔ g ∈ hypScalars h r ε := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r₀ q =>
    change q.p = 2 at hd
    have hc := SQTK.statedClassicalModel_twistedA r₀ q hv e
    rw [hd] at hc
    obtain ⟨⟨-, hf, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    obtain ⟨r, ε, hr, hε, hn⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ r₀ + 1 = 2 * r + ε :=
      ⟨(r₀ + 1) / 2, (r₀ + 1) % 2, by omega, by omega, by omega⟩
    rw [hn] at e' hn3 hnq
    have h := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
    obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
    let ψ := hypPSUEquivStatedProj h hR (by omega)
    refine ⟨K, hK, hKfin, q.exponent, h, r, ε,
      e'.symm.toMonoidHom.comp (ψ.toMonoidHom.comp (hypProj h r ε)), hr, hε,
      fun r₁ q₁ h₁ => ?_, ?_, fun g => ?_⟩
    · injection h₁ with h₃ h₂
      rw [← h₂, hqc]
    · exact e'.symm.surjective.comp (ψ.surjective.comp (hypProj_surjective h r ε))
    · change e'.symm (ψ (hypProj h r ε g)) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_hypProj]
  | _ => exact hd.elim

section Lift

variable {G X : Type*} [Group G] [Group X] {π : G →* X}

theorem exists_sylow_normalizer_le_comap_bar [Finite G] (hπ : Function.Surjective π)
    {J : Subgroup X} (S₀ : Sylow 2 X)
    (hS : Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤ J) :
    ∃ T : Sylow 2 G, Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J.comap π := by
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hπ 2 S₀
  refine ⟨T, fun y hy => ?_⟩
  rw [Subgroup.mem_comap]
  apply hS
  rw [← hT, Sylow.coe_mapSurjective]
  exact Subgroup.le_normalizer_map π ⟨y, hy, rfl⟩

theorem mem_perfectJoin_comap_sup (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    {J : Subgroup X} {t : G} (ht : π t ∈ perfectJoin J) :
    t ∈ perfectJoin (J.comap π) ⊔ π.ker := by
  have hkJ : π.ker ≤ J.comap π := fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact Subgroup.one_mem _
  have hmap := ToralCensus.map_perfectJoin_eq π hπ hker hkJ
  rw [Subgroup.map_comap_eq_self_of_surjective hπ] at hmap
  rw [← hmap] at ht
  obtain ⟨a, ha, hat⟩ := ht
  have hrest : a⁻¹ * t ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hat, inv_mul_cancel]
  have : t = a * (a⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ha hrest

theorem cycPerfect_comap_bar {Z : Subgroup G} (hZ : ∀ g, π g = 1 ↔ g ∈ Z) {m : ℕ}
    (hmZ : Nat.Coprime (Nat.card Z) m) {J : Subgroup X} (hcyc : CycPerfect m J) :
    ∀ V : Subgroup G, V ≤ J.comap π → ⁅V, V⁆ = V →
      ∀ Q : Subgroup G, Q ≤ V → IsPGroup m Q → IsCyclic Q := by
  intro V hVJ hV Q hQV hQ
  have hV' : V.map π ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hVJ hx
  have hVp : ⁅V.map π, V.map π⁆ = V.map π := by rw [← Subgroup.map_commutator, hV]
  have hQc : IsCyclic (Q.map π) := hcyc _ hV' hVp _ (Subgroup.map_mono hQV) (hQ.map π)
  refine isCyclic_of_injective (π.subgroupMap Q) fun x y hxy => ?_
  have hπxy : π ((x : G)⁻¹ * y) = 1 := by
    have h1 : ((π.subgroupMap Q x : ↥(Q.map π)) : X) = ((π.subgroupMap Q y : ↥(Q.map π)) : X) := by
      rw [hxy]
    have : π (x : G) = π (y : G) := h1
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have hZmem : (x : G)⁻¹ * y ∈ Z := (hZ _).mp hπxy
  have hQmem : (x : G)⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem x.2) y.2
  obtain ⟨k, hk⟩ := hQ ⟨_, hQmem⟩
  have hord : orderOf ((x : G)⁻¹ * y) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hmZ.pow_right k) (Subgroup.orderOf_dvd_natCard Z hZmem)
      (orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk))
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at hord
  exact Subtype.ext hord

theorem eq_bot_of_perfect_commute (hker : π.ker ≤ Subgroup.center G) {v : X} {t : G}
    (htv : π t = v)
    (htriv : ∀ V : Subgroup X, V ≤ Subgroup.centralizer ({v} : Set X) → ⁅V, V⁆ = V → V = ⊥)
    {V : Subgroup G} (hVc : ∀ w ∈ V, Commute w t) (hV : ⁅V, V⁆ = V) : V = ⊥ := by
  have hle : V.map π ≤ Subgroup.centralizer ({v} : Set X) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk, ← htv, ← map_mul, ← map_mul, (hVc w hw).eq]
  have hperf : ⁅V.map π, V.map π⁆ = V.map π := by rw [← Subgroup.map_commutator, hV]
  have hbot := htriv _ hle hperf
  have hVker : V ≤ π.ker := fun w hw => by
    have : π w ∈ V.map π := ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [← hV, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp (hker (hVker hb)) a)

end Lift

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

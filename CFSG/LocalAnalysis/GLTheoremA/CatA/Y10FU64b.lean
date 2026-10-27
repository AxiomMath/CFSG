module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU64a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk map_gLAPPrimeCore)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def N0 (p r : ℕ) (K : Subgroup G) : Subgroup ↥K :=
  GLAPPrimeCore p ↥K ⊓ GLAPPrimeCore r ↥K

instance n0_normal (p r : ℕ) (K : Subgroup G) : (N0 p r K).Normal := by
  unfold N0
  infer_instance

theorem map_N0 (p r : ℕ) (K : Subgroup G) (σ : MulAut ↥K) :
    (N0 p r K).map σ.toMonoidHom = N0 p r K := by
  unfold N0
  rw [Subgroup.map_inf _ _ _ σ.injective, map_gLAPPrimeCore p σ, map_gLAPPrimeCore r σ]

theorem n0_not_dvd {p r : ℕ} (hr : r.Prime) (K : Subgroup G) [Finite G] : ¬ r ∣ Nat.card (N0 p r K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h1 : Nat.Coprime r (Nat.card (GLAPPrimeCore r ↥K)) := CFSG.pPrimeCore_coprime_card
  have h2 : Nat.card (N0 p r K) ∣ Nat.card (GLAPPrimeCore r ↥K) :=
    Subgroup.card_dvd_of_le inf_le_right
  exact (Nat.Prime.coprime_iff_not_dvd hr).1 (Nat.Coprime.coprime_dvd_right h2 h1)


@[expose] noncomputable def actN0 (p r : ℕ) (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ N0 p r K) :=
  quotAutHom (N0 p r K) K.normalizerMonoidHom (fun γ => map_N0 p r K (K.normalizerMonoidHom γ))

theorem n0_le_core (p r : ℕ) (K : Subgroup G) : N0 p r K ≤ GLAPPrimeCore p ↥K := inf_le_left

@[expose] def n0ToBar (p r : ℕ) (K : Subgroup G) : (↥K ⧸ N0 p r K) →* (↥K ⧸ GLAPPrimeCore p ↥K) :=
  QuotientGroup.map (N0 p r K) (GLAPPrimeCore p ↥K) (MonoidHom.id _) (n0_le_core p r K)

theorem n0ToBar_mk (p r : ℕ) (K : Subgroup G) (k : K) :
    n0ToBar p r K (QuotientGroup.mk k) = QuotientGroup.mk k := rfl

theorem n0ToBar_surjective (p r : ℕ) (K : Subgroup G) : Function.Surjective (n0ToBar p r K) := by
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk k, rfl⟩

theorem n0ToBar_compat (p r : ℕ) (K : Subgroup G) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (x : ↥K ⧸ N0 p r K) : n0ToBar p r K (actN0 p r K γ x) = barAut p K γ (n0ToBar p r K x) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  unfold actN0
  rw [quotAutHom_mk, n0ToBar_mk, n0ToBar_mk, barAut_mk]

theorem n0ToBar_ker_central {p r : ℕ} (hp : p.Prime) (hr : r.Prime) [Finite G] {X K : Subgroup G}
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K) :
    (n0ToBar p r K).ker ≤ Subgroup.center (↥K ⧸ N0 p r K) := by
  intro z hz
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  have hh : h ∈ GLAPPrimeCore p ↥K := by
    have : (QuotientGroup.mk h : ↥K ⧸ GLAPPrimeCore p ↥K) = 1 := hz
    exact (QuotientGroup.eq_one_iff _).1 this
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (k * h)⁻¹ * (h * k) = (⁅k⁻¹, h⁻¹⁆)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  refine (N0 p r K).inv_mem ?_
  have h2 : ⁅h⁻¹, k⁻¹⁆ ∈ N0 p r K := mix_commutator_le hp hr hKp hKr
    (Subgroup.commutator_mem_commutator ((GLAPPrimeCore p ↥K).inv_mem hh) (Subgroup.mem_top _))
  have h3 : ⁅k⁻¹, h⁻¹⁆ = (⁅h⁻¹, k⁻¹⁆)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h3]
  exact (N0 p r K).inv_mem h2


theorem map_fixSubgroup_n0 {p r : ℕ} (hr : r.Prime) [Finite G] (K : Subgroup G) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hyr : y ^ r = 1) :
    (fixSubgroup (conjAut' K y hy)).map (QuotientGroup.mk' (N0 p r K)) =
      fixSubgroup (actN0 p r K ⟨y, hy⟩) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hFp : IsPGroup r ↥(Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set G)))) := by
    have h1 : (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ r = 1 :=
      Subtype.ext (by simpa using hyr)
    exact IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one h1)
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    show actN0 p r K ⟨y, hy⟩ (QuotientGroup.mk k) = QuotientGroup.mk k
    unfold actN0
    rw [quotAutHom_mk]
    exact congrArg QuotientGroup.mk (mem_fixSubgroup.1 hk)
  · intro hx
    have hx' : ∀ f ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set G))),
        quotAutHom (N0 p r K) K.normalizerMonoidHom
          (fun γ => map_N0 p r K (K.normalizerMonoidHom γ)) f x = x := by
      intro f hf
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      rw [map_zpow]
      have h1 : (actN0 p r K ⟨y, hy⟩) x = x := mem_fixSubgroup.1 hx
      have h2 : (actN0 p r K ⟨y, hy⟩) ∈ MulAction.stabilizer (MulAut (↥K ⧸ N0 p r K)) x :=
        h1
      exact (Subgroup.zpow_mem _ h2 m)
    obtain ⟨k, hkx, hkfix⟩ := exists_fixed_lift (N0 p r K) K.normalizerMonoidHom
      (fun γ => map_N0 p r K (K.normalizerMonoidHom γ)) hFp (n0_not_dvd hr K) x hx'
    refine ⟨k, ?_, hkx⟩
    exact mem_fixSubgroup.2 (hkfix _ (Subgroup.mem_zpowers _))


theorem mix_transfer {p r : ℕ} (hp : p.Prime) (hr : r.Prime) [Finite G] {X K J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hyr : y ^ r = 1)
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K)
    (hJ : GLAPComponent r (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    GLAPComponent r (fixSubgroup (barAut p K ⟨y, hy⟩))
      ((J.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K))) := by
  obtain ⟨hJK, hcomp'⟩ := glaPComponent_fixSubgroup_conjAut' hr K hy hJ
  have hker : Nat.Coprime r (Nat.card ↥(fixSubgroup (conjAut' K y hy) ⊓
      (QuotientGroup.mk' (N0 p r K)).ker)) := by
    rw [QuotientGroup.ker_mk']
    have h2 : Nat.card ↥(fixSubgroup (conjAut' K y hy) ⊓ N0 p r K) ∣ Nat.card (N0 p r K) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h2
      ((Nat.Prime.coprime_iff_not_dvd hr).2 (n0_not_dvd hr K))
  have h1 := glaPComponent_map hr (QuotientGroup.mk' (N0 p r K)) hker hcomp'
  rw [map_fixSubgroup_n0 hr K hy hyr] at h1
  have h2 := glaPComponent_map_fixSubgroup (n0ToBar p r K) (n0ToBar_ker_central hp hr hKp hKr)
    (actN0 p r K ⟨y, hy⟩) (barAut p K ⟨y, hy⟩) (n0ToBar_compat p r K ⟨y, hy⟩)
    (n0ToBar_surjective p r K) hr h1
  have e : (n0ToBar p r K).comp (QuotientGroup.mk' (N0 p r K)) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥K) := by
    ext k; rfl
  rw [Subgroup.map_map, e] at h2
  exact h2

end CFSG.LocalAnalysis.GLTheoremA.Y10F

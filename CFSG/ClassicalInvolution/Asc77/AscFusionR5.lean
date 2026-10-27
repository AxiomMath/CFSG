module

public import CFSG.ClassicalInvolution.Asc77.AscL62Pair
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.Asc77.AscFusionDiag

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem isQuatSub_of_isSylow2In (hp2 : p ≠ 2) {K V : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) (hV : IsSylow2In V K) : IsQuatSub V := by
  obtain ⟨e⟩ := hK.nonempty_equiv
  let φ : ↥K →* SL(2, GaloisField p f) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := fun x => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hF : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  let P : Sylow 2 ↥K := AscL62.sylowOfIsSylow2In'' hV
  have hP2 : IsPGroup 2 V := hV.2.1
  have hinj : Function.Injective (φ.comp (P : Subgroup ↥K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : φ (x : ↥K) = 1 := hx
    have hxN := (hφk _).mp hx1
    have hxV : ((x : ↥K) : G) ∈ V := by
      have : (x : ↥K) ∈ V.subgroupOf K := x.2
      exact this
    have hx2 : IsPGroup 2 (Subgroup.zpowers ((x : ↥K) : G)) :=
      hP2.to_le (Subgroup.zpowers_le.mpr hxV)
    have : ((x : ↥K) : G) = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
        (mem_oddCoreOf_iff.mpr ⟨(x : ↥K).2, hxN⟩) hx2
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨k, hk, ⟨q⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p f) hF
    (Sylow.mapSurjective (f := φ) hφs P)
  refine ⟨k, hk, ⟨?_⟩⟩
  have hcoe := Sylow.coe_mapSurjective (f := φ) hφs P
  let e2 : ↥(P : Subgroup ↥K) ≃* ↥((P : Subgroup ↥K).map φ) :=
    MulEquiv.ofBijective ((φ.comp (P : Subgroup ↥K).subtype).codRestrict ((P : Subgroup ↥K).map φ)
      (fun x => ⟨x, x.2, rfl⟩))
      ⟨fun a b h => hinj (congrArg Subtype.val h), by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe hV.1).symm.trans
    (e2.trans ((MulEquiv.subgroupCongr hcoe.symm).trans q))

theorem exists_twin_sylow (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K : Subgroup G} {z v : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hKz : IsUniqueInvolution K z)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v)
    (hvK : conjSub v⁻¹ K ≠ K) (hn : v * v ∈ Subgroup.normalizer (K : Set G)) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ v ∈ R ∧
      IsSylow2In (R ⊓ (K ⊔ conjSub v⁻¹ K)) (K ⊔ conjSub v⁻¹ K) ∧
      IsSylow2In (R ⊓ K) K ∧ IsSylow2In (R ⊓ conjSub v⁻¹ K) (conjSub v⁻¹ K) ∧
      (∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q) ∧
      ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K := by
  classical
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  obtain ⟨hK'mem, hK'z, hK'N, hKN', hcomm⟩ :=
    twin_facts_conj hp2 hq h₀ hK hKz hvz' hvK.symm
  set K' : Subgroup G := conjSub v⁻¹ K with hK'
  set M : Subgroup G := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  have hMN' : M ≤ Subgroup.normalizer (K' : Set G) := sup_le hKN' Subgroup.le_normalizer
  have hvM : v ∈ Subgroup.normalizer (M : Set G) := by
    apply AscHypOmega.mem_normalizer_of_conjSub_eq (n := v)
    have h1 : conjSub v M = conjSub v K ⊔ conjSub v K' := by
      rw [hM, conjSub, Subgroup.map_sup]
      rfl
    have h2 : conjSub v K' = K := by
      rw [hK', ← conjSub_mul, mul_inv_cancel, conjSub_one]
    have h3 : conjSub v K = K' := by
      have hn' : conjSub (v * v) K = K := conjSub_eq_of_mem_normalizer hn
      calc conjSub v K = conjSub (v⁻¹ * (v * v)) K := by congr 1; group
        _ = conjSub v⁻¹ (conjSub (v * v) K) := conjSub_mul _ _ _
        _ = K' := by rw [hn']
    rw [h1, h2, h3, sup_comm]
  set X : Subgroup G := M ⊔ Subgroup.zpowers v with hX
  have hXN : X ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hvM)
  obtain ⟨R, hRX, hvR⟩ := IsSylow2In.exists_ge hv2 (le_sup_right : Subgroup.zpowers v ≤ X)
  have hR2 : IsPGroup 2 R := hRX.2.1
  have hvR' : v ∈ R := hvR (Subgroup.mem_zpowers v)
  have hRM : IsSylow2In (R ⊓ M) M := isSylow2In_inf_of_le_normalizer hRX le_sup_left hXN
  have hRK : IsSylow2In (R ⊓ K) K := by
    have := isSylow2In_inf_of_le_normalizer hRM hKM hMN
    rwa [inf_assoc, inf_eq_right.mpr hKM] at this
  have hRK' : IsSylow2In (R ⊓ K') K' := by
    have := isSylow2In_inf_of_le_normalizer hRM hK'M hMN'
    rwa [inf_assoc, inf_eq_right.mpr hK'M] at this
  refine ⟨R, hR2, hvR', hRM, hRK, hRK', ?_, ?_⟩
  · intro q hq q' hq'
    have hqK : q ∈ K := hq.2
    have hq'K' : q' ∈ K' := hq'.2
    have h1 : ⁅q, q'⁆ ∈ oddCoreOf K :=
      (hcomm (Subgroup.commutator_mem_commutator hqK hq'K')).1
    have h2 : ⁅q, q'⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hq.1 hq'.1) (R.inv_mem hq.1)) (R.inv_mem hq'.1)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅q, q'⁆) :=
      hR2.to_le (Subgroup.zpowers_le.mpr h2)
    have h4 : ⁅q, q'⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h4)
  · intro q hq
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hvR') hq.1) hvR', ?_⟩
    have := conj_mem_conjSub (n := v⁻¹) hq.2
    rwa [inv_inv] at this

end CFSG.ClassicalInvolution.Asc77.AscFusion

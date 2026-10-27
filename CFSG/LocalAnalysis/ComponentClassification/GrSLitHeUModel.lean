module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZFactsModel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS

namespace HeGS


theorem gsFixedLayer_eq_heK0 {p : Equiv.Perm (Fin 8330)} (hpZ : p ∈ heZ0) (hp1 : p ≠ 1) :
    gsFixedLayer heP p = heK0 := by
  have hpZ' := hpZ
  rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff] at hpZ'
  obtain ⟨hpK, hpc⟩ := hpZ'
  have hconj : p ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
    rcases eq_of_comm_heK0 (heK0_le_heP hpK) (fun k hk => (hpc k hk).symm) with h | h | h | h
    · exact absurd h hp1
    · rw [h]
      exact ⟨1, one_mem _, by group⟩
    · rw [h]
      exact heGSU_mem_conjClass
    · rw [h]
      exact heGST0U_mem_conjClass
  obtain ⟨c, hc, rfl⟩ := hconj
  rw [HeLay.gsFixedLayer_conj hc]
  have hS : heK0.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizerIn heP (heGenPerm 0) := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_centralizerIn.mpr ⟨mul_mem (mul_mem (inv_mem hc) (heK0_le_heP hk)) hc, ?_⟩
    have h1 := hpc k hk
    calc c⁻¹ * k * c * heGenPerm 0 = c⁻¹ * (k * (c * heGenPerm 0 * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * heGenPerm 0 * c⁻¹) * k) * c := by rw [h1]
      _ = heGenPerm 0 * (c⁻¹ * k * c) := by group
  have hp : ⁅heK0.map (MulAut.conj c⁻¹).toMonoidHom, heK0.map (MulAut.conj c⁻¹).toMonoidHom⁆ =
      heK0.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [← map_commutator]
    exact congrArg _ HeLay.gsFixedLayer_t0.2.1
  have hK := le_heK0_of_perfect hS hp
  have hle : heK0 ≤ heK0.map (MulAut.conj c).toMonoidHom := by
    intro k hk
    have h1 : c⁻¹ * k * c ∈ heK0 := hK ⟨k, hk, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    exact ⟨c⁻¹ * k * c, h1, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  exact (eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj c).injective])).symm

end HeGS

open HeFM


theorem exists_twoA_four_of_held {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) :
    ∃ v₁ ∈ L, ∃ v₂ ∈ L, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
      v₁ * v₂ = v₂ * v₁ ∧ ∀ w ∈ L, (w = v₁ ∨ w = v₂ ∨ w = v₁ * v₂) →
        HeldTwoA L w ∧ v₁ ∈ (center ↥(gsFixedLayer L w)).map (gsFixedLayer L w).subtype ∧
          v₂ ∈ (center ↥(gsFixedLayer L w)).map (gsFixedLayer L w).subtype := by
  set φ : ↥L ≃* ↥heP := toP e with hφ
  have hp₁ : heGenPerm 0 ∈ heP := heGenPerm_mem (by norm_num)
  have hp₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ∈ heP := (mem_centralizerIn.mp HeGS.heGSU.2).1
  set q₁ : ↥heP := ⟨heGenPerm 0, hp₁⟩ with hq₁
  set q₂ : ↥heP := ⟨HeGS.heGSU, hp₂⟩ with hq₂
  have hc₂ := HeGS.heGSU_mem_conjClass
  have hc₁₂ := HeGS.heGST0U_mem_conjClass
  have ho₂ : orderOf (HeGS.heGSU : Equiv.Perm (Fin 8330)) = 2 := orderOf_of_mem_conjClass hc₂
  have ho₁₂ : orderOf (heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330))) = 2 :=
    orderOf_of_mem_conjClass hc₁₂
  have hs₁ : heGenPerm 0 * heGenPerm 0 = 1 := HeGS.heGenPerm0_sq
  have hs₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) * HeGS.heGSU = 1 := by
    rw [← sq, ← ho₂, pow_orderOf_eq_one]
  have hn₁ : heGenPerm 0 ≠ 1 := heA0_ne_one
  have hn₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ≠ 1 := fun h => by
    rw [h, orderOf_one] at ho₂
    norm_num at ho₂
  have hne : heGenPerm 0 ≠ (HeGS.heGSU : Equiv.Perm (Fin 8330)) := fun h => by
    rw [← h, hs₁, orderOf_one] at ho₁₂
    norm_num at ho₁₂
  have hcomm : heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330)) = HeGS.heGSU * heGenPerm 0 :=
    ((mem_centralizerIn.mp HeGS.heGSU.2).2).symm
  have hZ₁ : heGenPerm 0 ∈ heZ0 := HeGS.mem_heZ0_of_mem_ker HeGS.heGST0_mem_ker
  have hZ₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ∈ heZ0 :=
    HeGS.mem_heZ0_of_mem_ker HeGS.heGSU_mem_ker
  have hv : ∀ q : ↥heP, ((φ.symm q : ↥L) : X) ∈ L := fun q => (φ.symm q).2
  have hφv : ∀ q : ↥heP, φ ⟨(φ.symm q : X), hv q⟩ = q := fun q => MulEquiv.apply_symm_apply φ q
  have hinj : ∀ q q' : ↥heP, ((φ.symm q : ↥L) : X) = (φ.symm q' : X) → q = q' := fun q q' h =>
    φ.symm.injective (Subtype.ext h)
  have hmul : ∀ q q' : ↥heP, ((φ.symm q : ↥L) : X) * (φ.symm q' : X) = (φ.symm (q * q') : X) :=
    fun q q' => by rw [map_mul, coe_mul]
  have hone : ∀ q : ↥heP, ((φ.symm q : ↥L) : X) = 1 ↔ q = 1 := fun q => by
    constructor
    · intro h
      have h' : φ.symm q = 1 := Subtype.ext h
      rwa [MulEquiv.map_eq_one_iff] at h'
    · rintro rfl
      rw [map_one, coe_one]
  refine ⟨_, hv q₁, _, hv q₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmul, (hone _).mpr (Subtype.ext hs₁)]
  · rw [hmul, (hone _).mpr (Subtype.ext hs₂)]
  · exact fun h => hn₁ (congrArg Subtype.val ((hone q₁).mp h))
  · exact fun h => hn₂ (congrArg Subtype.val ((hone q₂).mp h))
  · exact fun h => hne (congrArg Subtype.val (hinj q₁ q₂ h))
  · rw [hmul, hmul, show q₁ * q₂ = q₂ * q₁ from Subtype.ext hcomm]
  · intro w hw hcases
    obtain ⟨q, hqw, hqZ, hq1⟩ : ∃ q : ↥heP, ((φ.symm q : ↥L) : X) = w ∧
        (q : Equiv.Perm (Fin 8330)) ∈ heZ0 ∧ (q : Equiv.Perm (Fin 8330)) ≠ 1 ∧
        (q : Equiv.Perm (Fin 8330)) ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
      rcases hcases with rfl | rfl | rfl
      · exact ⟨q₁, rfl, hZ₁, hn₁, ⟨1, one_mem _, by rw [hq₁]; group⟩⟩
      · exact ⟨q₂, rfl, hZ₂, hn₂, hc₂⟩
      · refine ⟨q₁ * q₂, (hmul q₁ q₂).symm, mul_mem hZ₁ hZ₂, ?_, hc₁₂⟩
        intro h
        apply hne
        have h' : heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330)) = 1 := h
        calc heGenPerm 0 = heGenPerm 0 * (HeGS.heGSU * HeGS.heGSU) := by rw [hs₂, mul_one]
          _ = (heGenPerm 0 * HeGS.heGSU) * HeGS.heGSU := by rw [mul_assoc]
          _ = HeGS.heGSU := by rw [h', one_mul]
    obtain ⟨hq1', hqc⟩ := hq1
    subst hqw
    have hwφ : φ ⟨(φ.symm q : X), hv q⟩ = q := hφv q
    have hKle : gsFixedLayer L (φ.symm q : X) ≤ L :=
      (gsFixedLayer_le_inf L _).trans inf_le_left
    have hK : HeT.trS φ (gsFixedLayer L (φ.symm q : X)) = heK0 := by
      rw [HeT.trS_gsFixedLayer φ (hv q), hwφ]
      exact HeGS.gsFixedLayer_eq_heK0 hqZ hq1'
    have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 →
        (y : X) ∈ (center ↥(gsFixedLayer L (φ.symm q : X))).map
          (gsFixedLayer L (φ.symm q : X)).subtype := by
      intro y hy
      rw [← mem_center_trS_iff φ hKle y, hK]
      exact hy
    refine ⟨(HeT.heldTwoA_iff φ (hv q)).mp ?_, hZ _ ?_, hZ _ ?_⟩
    · rw [hwφ]
      exact (HeLay.heldTwoA_heP_iff q.2 (orderOf_of_mem_conjClass hqc)).mpr hqc
    · rw [MulEquiv.apply_symm_apply]
      exact hZ₁
    · rw [MulEquiv.apply_symm_apply]
      exact hZ₂

theorem isPComponent_gsFixedLayer_of_held {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) {u : X} (hu : HeldTwoA L u) :
    IsPComponent 2 ((gsFixedLayer L u).subgroupOf (L ⊓ centralizer ({u} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hC : heP ⊓ centralizer ({(φ ⟨u, hu.1⟩ : Equiv.Perm (Fin 8330))} : Set _) =
      centralizerIn heP (heGenPerm 0) := by
    rw [hφ]
    rfl
  let ψ : ↥(L ⊓ centralizer ({u} : Set X)) ≃* ↥(centralizerIn heP (heGenPerm 0)) :=
    (HeT.restrEquiv φ hu.1).trans (MulEquiv.subgroupCongr hC)
  have h1 : (gsFixedLayer L u).subgroupOf (L ⊓ centralizer ({u} : Set X)) =
      pLayer ↥(L ⊓ centralizer ({u} : Set X)) 2 :=
    comap_map_eq_self_of_injective (subtype_injective _) _
  rw [h1]
  have hP := FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ
  obtain ⟨N, hNp, -, hlayer, -⟩ := HeLay.layer_t0
  rw [hlayer] at hP
  have h2 : pLayer ↥(L ⊓ centralizer ({u} : Set X)) 2 = N.map ψ.symm.toMonoidHom := by
    rw [← hP, map_map]
    have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, map_id]
  rw [h2]
  exact CatalogueBAlternating.pComponent_map_equiv 2 ψ.symm N hNp

end CFSG.ComponentClassification.GrSLit

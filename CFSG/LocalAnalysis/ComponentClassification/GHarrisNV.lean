module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisCV
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigH

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G]
  in
theorem S_le_normalizer_V : (D.S : Subgroup G) ≤ normalizer (D.V : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h := D.conj_mem_V (inv_mem hs) hv
    rwa [inv_inv] at h
  · have h := D.conj_mem_V hs hv
    rwa [show s⁻¹ * (s * v * s⁻¹) * s = v by group] at h

theorem eight_dvd_index (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥) :
    8 ∣ ((centralizer (D.V : Set G)).subgroupOf (normalizer (D.V : Set G))).index := by
  rw [D.centralizer_V_eq_Q hC hOM]
  have hQN : D.Q ≤ normalizer (D.V : Set G) :=
    D.centralizer_V_eq_Q hC hOM ▸ centralizer_le_normalizer D.V
  have h1 := (D.Q.subgroupOf (normalizer (D.V : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, D.card_Q] at h1
  have h2 : 512 ∣ Nat.card (normalizer (D.V : Set G)) := by
    rw [← D.card_S_eq]
    exact card_dvd_of_le D.S_le_normalizer_V
  rw [← h1, show (512 : ℕ) = 64 * 8 by norm_num] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 64) h2


theorem seven_dvd_index (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) :
    7 ∣ ((centralizer (D.V : Set G)).subgroupOf (normalizer (D.V : Set G))).index := by
  set z' : ↥D.V := ⟨D.z, D.z_mem_V⟩
  have horb : MulAction.orbit ↥(normalizer (D.V : Set G)) z' = {v | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨n, rfl⟩ h
      apply D.z_ne_one
      have h' : (n : G) * D.z * (n : G)⁻¹ = 1 := congrArg Subtype.val h
      calc D.z = (n : G)⁻¹ * ((n : G) * D.z * (n : G)⁻¹) * n := by group
        _ = 1 := by rw [h']; group
    · intro hv
      have hv1 : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
      obtain ⟨k, hk, hkz⟩ := D.exists_normalizer_V_conj h10 h20 v.2 hv1
      exact ⟨⟨k, hk⟩, Subtype.ext hkz⟩
  have h7 : (MulAction.stabilizer ↥(normalizer (D.V : Set G)) z').index = 7 := by
    rw [MulAction.index_stabilizer, horb, show {v : ↥D.V | v ≠ 1} = ({1} : Set ↥D.V)ᶜ from rfl,
      Set.ncard_compl, Set.ncard_singleton, D.card_V]
  rw [← h7]
  refine index_dvd_of_le fun n hn => ?_
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  change (n : G) * D.z * (n : G)⁻¹ = D.z
  rw [mem_subgroupOf, mem_centralizer_iff] at hn
  rw [← hn _ D.z_mem_V, mul_inv_cancel_right]

theorem exists_GL32_normalizer_V (hC : GorensteinHaradaThmCInput)
    (hOM : pPrimeCore 2 ↥D.M = ⊥) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) :
    ∃ θ : ↥(normalizer (D.V : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective θ ∧
      θ.ker = D.Q.subgroupOf (normalizer (D.V : Set G)) := by
  have h56 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 8)
    (D.seven_dvd_index h10 h20) (D.eight_dvd_index hC hOM)
  obtain ⟨θ, hθ, hker⟩ := exists_GL32_of_dvd_index D.isElemAbelian_V D.card_V h56
  exact ⟨θ, hθ, by rw [hker, D.centralizer_V_eq_Q hC hOM]⟩

end GHSylow

end CFSG.ComponentClassification.GHarris

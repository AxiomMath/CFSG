module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBLayer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover

namespace EndB

theorem exists_perfect_lift {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q] (π : K →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center K) (e : K) {A : Subgroup Q}
    (hAC : A ≤ centralizer {π e}) [hA : Group.IsPerfect ↥A] :
    ∃ B : Subgroup K, Group.IsPerfect ↥B ∧ B ≤ centralizer {e} ∧ B.map π = A := by
  set Ã := A.comap π with hÃ
  refine ⟨(perfectResidual ↥Ã).map Ã.subtype, isPerfect_perfectResidual_map Ã, ?_, ?_⟩
  ·
    have hκ : ∀ a : Ã, (a : K) * e * (a : K)⁻¹ * e⁻¹ ∈ center K := by
      intro a
      apply hker
      have h1 : π a * π e = π e * π a := mem_centralizer_singleton_iff.mp (hAC a.2)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    let κ : ↥Ã →* ↥(center K) :=
      { toFun := fun a => ⟨_, hκ a⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          have hb := mem_center_iff.mp (hκ b) (a : K)
          simp only [Subgroup.coe_mul, mul_inv_rev]
          calc (a : K) * b * e * ((b : K)⁻¹ * (a : K)⁻¹) * e⁻¹ =
              (a : K) * ((b : K) * e * (b : K)⁻¹ * e⁻¹) * e * (a : K)⁻¹ * e⁻¹ := by group
            _ = ((b : K) * e * (b : K)⁻¹ * e⁻¹) * (a : K) * e * (a : K)⁻¹ * e⁻¹ := by rw [hb]
            _ = (a : K) * e * (a : K)⁻¹ * e⁻¹ * ((b : K) * e * (b : K)⁻¹ * e⁻¹) := by
              have hc := mem_center_iff.mp (hκ b) ((a : K) * e * (a : K)⁻¹ * e⁻¹)
              calc ((b : K) * e * (b : K)⁻¹ * e⁻¹) * (a : K) * e * (a : K)⁻¹ * e⁻¹ =
                  ((b : K) * e * (b : K)⁻¹ * e⁻¹) * ((a : K) * e * (a : K)⁻¹ * e⁻¹) := by group
                _ = _ := hc.symm) }
    have hle : perfectResidual ↥Ã ≤ κ.ker := by
      refine le_trans ?_ (Abelianization.commutator_subset_ker κ)
      have h := iInf_le (fun n => derivedSeries ↥Ã n) 1
      rwa [derivedSeries_one] at h
    rintro _ ⟨a, ha, rfl⟩
    have h1 := MonoidHom.mem_ker.mp (hle ha)
    have h2 : (a : K) * e * (a : K)⁻¹ * e⁻¹ = 1 := congrArg Subtype.val h1
    rw [mem_centralizer_singleton_iff]
    calc (a : K) * e = (a : K) * e * (a : K)⁻¹ * e⁻¹ * e * a := by group
      _ = e * a := by rw [h2, one_mul]
  ·
    let φ : ↥Ã →* ↥A := (π.comp Ã.subtype).codRestrict A (fun a => a.2)
    have hφ : Function.Surjective φ := by
      rintro ⟨a, ha⟩
      obtain ⟨k, rfl⟩ := hπ a
      exact ⟨⟨k, ha⟩, rfl⟩
    have h1 := RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image φ hφ
    have h2 : π.comp Ã.subtype = A.subtype.comp φ := rfl
    rw [Subgroup.map_map, h2, ← Subgroup.map_map]
    change ((RankThreeCoreUniqueness.Helpers.perfectResidual ↥Ã).map φ).map A.subtype = A
    rw [h1, ← MonoidHom.range_eq_map, range_subtype]

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem isPGroup_ker (hJ : JLayer hs π) : IsPGroup 2 π.ker := by
  rw [hJ.ker]
  have h := hJ.center_le
  have h0 : 0 < Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :=
    Nat.card_pos
  rw [IsPGroup.iff_card]
  interval_cases hc : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem not_seven_dvd
    (hJ : JLayer hs π)
    {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    {q : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hq : q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (he2 : orderOf (π e) = 2) :
    ¬ 7 ∣ Nat.card ↥(centralizer {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q} with hC
  set φ : ↥C →* MulAut P := hJ.theta.comp C.subtype with hφ
  have hθ : hJ.theta ((e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q) =
      MulAut.conj (π e) := by
    rw [map_mul, (hJ.theta_eq_one_iff q).mpr hq, mul_one, hJ.theta_conj]
  have hker : IsPGroup 2 φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rintro _ ⟨g, hg, rfl⟩
      exact (hJ.theta_eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)
    have h1 : IsPGroup 2 ↥(φ.ker.map C.subtype) := pCore_isPGroup.to_le hle
    exact h1.of_equiv (equivMapOfInjective _ _ C.subtype_injective).symm
  have hrange : φ.range ≤ centralizer {MulAut.conj (π e)} := by
    rintro _ ⟨g, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hθ]
    change hJ.theta g * _ = _ * hJ.theta g
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp g.2)]
  have h7 := not_seven_dvd_centralizer_conj he2
  intro hdvd
  rw [← Subgroup.card_ker_mul_card_range φ] at hdvd
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp hdvd with h | h
  · obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hk] at h
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h)
    omega
  · exact h7 (h.trans (Subgroup.card_dvd_of_le hrange))

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit

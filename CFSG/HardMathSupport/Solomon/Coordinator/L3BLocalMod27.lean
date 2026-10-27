module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  Matrix

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {X : Type*} [Group X]
  (φ : X →* GL (Fin 3) K)

structure L3Model (π : Bool) (p f : ℕ) {K : Type} [Field K] {X : Type*} [Group X]
    (φ : X →* GL (Fin 3) K) : Prop where
  inj : Function.Injective φ
  range : ∀ g : GL (Fin 3) K, g ∈ φ.range ↔ g ∈ slPi π 3 (p ^ f) K

namespace L3Model

variable {φ}

theorem mem_sl (hφ : L3Model π p f φ) (x : X) : φ x ∈ slPi π 3 (p ^ f) K :=
  (hφ.range _).1 ⟨x, rfl⟩

theorem exists_of_mem_sl (hφ : L3Model π p f φ) {s : GL (Fin 3) K}
    (hs : s ∈ slPi π 3 (p ^ f) K) : ∃ x : X, φ x = s := (hφ.range s).2 hs

theorem mem_center_iff (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    (x : X) : x ∈ Subgroup.center X ↔ φ x ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  constructor
  · intro hx
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
    obtain ⟨y, rfl⟩ := hφ.exists_of_mem_sl hs
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply hφ.inj
    rw [map_mul, map_mul]
    exact commute_of_mem_statedScalars hx (φ y)

theorem center_pow (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    {z : X} (hz : z ∈ Subgroup.center X) : z ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨ξ, hξ⟩ := (hφ.mem_center_iff hK hq z).1 hz
  apply hφ.inj
  rw [map_pow, map_one, ← hξ, ← map_pow]
  have hdet := ((mem_slPi_iff hπ).1 (hφ.mem_sl z)).2
  have h3 : ξ ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have := det_scalar_three ξ
    rw [hξ] at this
    exact this.symm.trans hdet)
  rw [h3, map_one]

theorem scalar_mem_sl (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {ξ : Kˣ}
    (h3 : ξ ^ 3 = 1) : GeneralLinearGroup.scalar (Fin 3) ξ ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  refine (mem_slPi_iff hπ).2 ⟨(scalar_mem_glPi_iff hK ξ).2 ?_, ?_⟩
  · rw [mem_rootsOfUnity]
    obtain ⟨r, hr⟩ := three_dvd_qSubPi hq
    rw [hr, pow_mul, h3, one_pow]
  · rw [det_scalar_three]
    have := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

theorem card_center (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set u : Kˣ := Units.mk0 τ hτ0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ,
    Units.val_one])
  obtain ⟨z₀, hz₀⟩ := hφ.exists_of_mem_sl (scalar_mem_sl hK hq hu3)
  have hz₀c : z₀ ∈ Subgroup.center X := (hφ.mem_center_iff hK hq z₀).2 (by rw [hz₀]; exact ⟨u, rfl⟩)
  have hz₀3 : z₀ ^ 3 = 1 := hφ.center_pow hK hq hz₀c
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    rw [h, map_one] at hz₀
    have := scalar_injective_three (hz₀.symm.trans (map_one _).symm)
    exact hτ1 (by simpa [hu] using congrArg Units.val this)
  have hcen : Subgroup.center X = Subgroup.zpowers z₀ := by
    apply le_antisymm
    · intro z hz
      obtain ⟨ξ, hξ⟩ := (hφ.mem_center_iff hK hq z).1 hz
      have hz3 := hφ.center_pow hK hq hz
      have hξ3 : (ξ : K) ^ 3 = 1 := by
        have h1 : ξ ^ 3 = 1 := by
          apply scalar_injective_three
          rw [map_pow, hξ, ← map_pow, hz3, map_one, map_one]
        have := congrArg Units.val h1
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
      rcases cube_root_cases hτ hτ1 hξ3 with h | h | h
      · have : z = 1 := by
          apply hφ.inj
          have hξ1 : ξ = 1 := Units.ext (h.trans Units.val_one.symm)
          rw [map_one, ← hξ, hξ1, map_one]
        rw [this]; exact Subgroup.one_mem _
      · have : z = z₀ := by
          apply hφ.inj
          have hξu : ξ = u := Units.ext (by rw [h, hu, Units.val_mk0])
          rw [← hξ, hz₀, hξu]
        rw [this]; exact Subgroup.mem_zpowers z₀
      · have : z = z₀ ^ 2 := by
          apply hφ.inj
          rw [map_pow, hz₀, ← hξ, ← map_pow]
          congr 1
          apply Units.ext
          rw [h, Units.val_pow_eq_pow_val, hu, Units.val_mk0]
        rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z₀) 2
    · exact (Subgroup.zpowers_le).2 hz₀c
  rw [hcen, Nat.card_zpowers, orderOf_eq_prime hz₀3 hz₀1]

theorem exists_conj_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : X}
    (hx : x ∉ Subgroup.center X) (hx3 : x ^ 3 = 1) :
    ∃ g ∈ glPi π 3 (p ^ f) K, φ x = g * diagTau hτ * g⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hxZ : φ x ∉ zPi π 3 (p ^ f) K := by
    intro h
    exact hx ((hφ.mem_center_iff hK hq x).2 (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h))
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hord : orderOf (φ x) = 3 := by
    rw [orderOf_injective φ hφ.inj x, orderOf_eq_prime hx3 hx1]
  obtain ⟨g, hg, hgx⟩ := rank3II_4_10_three hK hq hτ hτ1 (hφ.mem_sl x) hxZ hord
  exact ⟨g, hg, eq_conj_of_inv_conj hgx⟩

end L3Model

@[expose] noncomputable def l3bIota (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) : X ⧸ Subgroup.center X →* ProjGenLinGroup (Fin 3) K :=
  QuotientGroup.lift _ ((ProjGenLinGroup.mk : GL (Fin 3) K →* _).comp φ) (by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mk_eq_one_iff_mem_statedScalars]
    exact (hφ.mem_center_iff hK hq x).1 hx)

theorem l3bIota_mk (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    (x : X) : l3bIota φ hK hq hφ (QuotientGroup.mk x) = ProjGenLinGroup.mk (φ x) := rfl

theorem l3bIota_injective (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) : Function.Injective (l3bIota φ hK hq hφ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  induction a using QuotientGroup.induction_on with
  | H x =>
    rw [l3bIota_mk, mk_eq_one_iff_mem_statedScalars] at ha
    exact (QuotientGroup.eq_one_iff x).2 ((hφ.mem_center_iff hK hq x).2 ha)

theorem l3bIota_surj (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ) :
    ∀ s ∈ slPi π 3 (p ^ f) K, ∃ m : X ⧸ Subgroup.center X,
      l3bIota φ hK hq hφ m = ProjGenLinGroup.mk s := by
  intro s hs
  obtain ⟨x, rfl⟩ := hφ.exists_of_mem_sl hs
  exact ⟨QuotientGroup.mk x, rfl⟩


end CFSG.HardMathSupport.Solomon.Coordinator

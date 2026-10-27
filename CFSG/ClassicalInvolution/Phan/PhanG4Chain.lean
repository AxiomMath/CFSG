module

public import CFSG.ClassicalInvolution.Phan.PhanG3Cent
public import CFSG.ClassicalInvolution.Phan.PhanD6Inf
public import CFSG.ClassicalInvolution.Phan.TitsChamber

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] (S : PhanFamilyD4 K p f G)

structure PhanChain (e : Fin 3 → Fin 4) (ψ : Su K p f 4 →* G) : Prop where
  inj : Function.Injective e
  le_range : ∀ (j : Fin 3) (A : Su K p f 2), ψ (blockEmb2 K p f 3 j A) ∈ (S.ι (e j)).range
  range_le : ∀ (j : Fin 3), ∀ r ∈ (S.ι (e j)).range,
    ∃ A : Su K p f 2, ψ (blockEmb2 K p f 3 j A) = r
  blk_inj : ∀ j : Fin 3, Function.Injective (ψ.comp (blockEmb2 K p f 3 j))
  torEq : ∀ j : Fin 3,
    ((ψ.comp (blockEmb2 K p f 3 j)).comp (torusTwo (unitaryInvolution K p f))).range =
      (tor S (e j)).range

variable {S}

section Torus

variable {e : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

theorem PhanChain.psi_torusEquiv (hg : GoodFamily S) (hch : PhanChain S e ψ)
    (s : Fin 3 → normOne (unitaryInvolution K p f)) :
    ∃ u : Fin 4 → normOne (unitaryInvolution K p f),
      ψ ((torusEquiv (unitaryInvolution K p f) 3 s : torus (unitaryInvolution K p f) 4) :
        Su K p f 4) = mTor S u ∧ (u = 1 → s = 1) := by
  have hα : ∀ j : Fin 3, ∃ α : normOne (unitaryInvolution K p f) ≃*
      normOne (unitaryInvolution K p f),
      ∀ g, tor S (e j) (α g) = ψ (blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) g)) :=
    fun j => exists_mulEquiv_comp_eq
      (a₁ := (ψ.comp (blockEmb2 K p f 3 j)).comp (torusTwo (unitaryInvolution K p f)))
      (a₂ := tor S (e j))
      ((hch.blk_inj j).comp (torusTwo_injective _))
      ((hg.inj (e j)).comp (torusTwo_injective _)) (hch.torEq j)
  choose α hαe using hα
  let c : Fin 3 → normOne (unitaryInvolution K p f) →* normOne (unitaryInvolution K p f) :=
    fun j => (α j).toMonoidHom
  have hcinj : ∀ j, Function.Injective (c j) := fun j => (α j).injective
  have hc : ∀ j g, ψ (blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) g)) =
      tor S (e j) (c j g) := fun j g => (hαe j g).symm
  have hs : s = Pi.mulSingle 0 (s 0) * Pi.mulSingle 1 (s 1) * Pi.mulSingle 2 (s 2) := by
    ext i
    fin_cases i <;> simp
  refine ⟨Pi.mulSingle (e 0) (c 0 (s 0)) * Pi.mulSingle (e 1) (c 1 (s 1)) *
    Pi.mulSingle (e 2) (c 2 (s 2)), ?_, ?_⟩
  · conv_lhs => rw [hs]
    simp only [map_mul, Subgroup.coe_mul, coe_torusEquiv_mulSingle, mTor_mulSingle, hc]
  · intro hu
    have h0 := congrFun hu (e 0)
    have h1 := congrFun hu (e 1)
    have h2 := congrFun hu (e 2)
    have n01 : e 0 ≠ e 1 := fun h => by simpa using hch.inj h
    have n02 : e 0 ≠ e 2 := fun h => by simpa using hch.inj h
    have n12 : e 1 ≠ e 2 := fun h => by simpa using hch.inj h
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne n01,
      Pi.mulSingle_eq_of_ne n01.symm, Pi.mulSingle_eq_of_ne n02, Pi.mulSingle_eq_of_ne n02.symm,
      Pi.mulSingle_eq_of_ne n12, Pi.mulSingle_eq_of_ne n12.symm, mul_one, one_mul,
      Pi.one_apply] at h0 h1 h2
    have k0 : s 0 = 1 := (injective_iff_map_eq_one (c 0)).1 (hcinj 0) _ h0
    have k1 : s 1 = 1 := (injective_iff_map_eq_one (c 1)).1 (hcinj 1) _ h1
    have k2 : s 2 = 1 := (injective_iff_map_eq_one (c 2)).1 (hcinj 2) _ h2
    ext i
    fin_cases i <;> simp [k0, k1, k2]

theorem PhanChain.psi_mem_torusSub (hg : GoodFamily S) (hch : PhanChain S e ψ) {t : Su K p f 4}
    (ht : t ∈ torus (unitaryInvolution K p f) 4) : ψ t ∈ torusSub S := by
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 3).surjective ⟨t, ht⟩
  obtain ⟨u, hu, -⟩ := hch.psi_torusEquiv hg s
  have : t = ((torusEquiv (unitaryInvolution K p f) 3 s : torus (unitaryInvolution K p f) 4) :
      Su K p f 4) := by rw [hs]
  rw [this, hu]
  exact mTor_mem_torusSub S u

end Torus

section Inj

variable {e : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

theorem isQuasisimple_su_four (hK : Nat.card K = (p ^ f) ^ 2) : IsQuasisimple (Su K p f 4) := by
  have h := (isQuasisimple_statedSU_of_card hK (n := 4) (by omega) (by
    intro h
    have : (4 : ℕ) = 3 := (Prod.mk.inj h).1
    omega)).1
  exact isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)).symm h

theorem PhanChain.injective (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) (hch : PhanChain S e ψ) : Function.Injective ψ := by
  have hquasi := isQuasisimple_su_four (K := K) (p := p) (f := f) hK
  obtain ⟨s₀, hs₀⟩ := exists_normOne_ne_one hK
  have hnt : ∃ k, ψ k ≠ 1 := by
    refine ⟨blockEmb2 K p f 3 0 (torusTwo (unitaryInvolution K p f) s₀), fun h1 => ?_⟩
    have h2' : torusTwo (unitaryInvolution K p f) s₀ = 1 :=
      (injective_iff_map_eq_one _).1 (hch.blk_inj 0) _ h1
    have h3 : s₀ = 1 := torusTwo_injective _ (by rw [h2', map_one])
    exact hs₀ (by rw [h3]; rfl)
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hquasi hnt
  rw [injective_iff_map_eq_one]
  intro g hg1
  have hcent := hker (MonoidHom.mem_ker.2 hg1)
  have htor : g ∈ torus (unitaryInvolution K p f) 4 :=
    eq_torus_of_comm_torus ⟨s₀, hs₀⟩ (by omega) fun t _ => by
      have := Subgroup.mem_center_iff.1 hcent t
      exact this.symm
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 3).surjective ⟨g, htor⟩
  obtain ⟨u, hu, hu1⟩ := hch.psi_torusEquiv hg s
  have hgs : g = ((torusEquiv (unitaryInvolution K p f) 3 s : torus (unitaryInvolution K p f) 4) :
      Su K p f 4) := by rw [hs]
  rw [hgs, hu] at hg1
  have : u = 1 := hg.mTor_injective hK h2 (by rw [hg1, map_one])
  have hs1 : s = 1 := hu1 this
  rw [hgs, hs1, map_one]
  rfl

theorem PhanChain.mem_torus_of_psi_mem (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) (hch : PhanChain S e ψ) {h : Su K p f 4} (hh : ψ h ∈ torusSub S) :
    h ∈ torus (unitaryInvolution K p f) 4 := by
  obtain ⟨s₀, hs₀⟩ := exists_normOne_ne_one hK
  refine eq_torus_of_comm_torus ⟨s₀, hs₀⟩ (by omega) fun t ht => ?_
  apply hch.injective hK hg h2
  rw [map_mul, map_mul]
  exact (torusSub_comm S (hch.psi_mem_torusSub hg ht) hh).symm

end Inj

end CFSG.ClassicalInvolution.PhanG

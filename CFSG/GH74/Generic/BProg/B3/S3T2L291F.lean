module

public import CFSG.GH74.Generic.BProg.B3.SolvLift

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B1 CFSG.GH74.GLS.C3.Layer1 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups commutatorElement

namespace S3T2L291

variable {G : Type} [Group G]

theorem exists_solvLift_mem {x y : G} {K E : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    [Finite G] (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h : SolvAdm x y K E Lb Ib) :
    ∃ I0 I1 : Subgroup G, SolvLift x y E Lb I0 I1 ∧
      ∀ (g : G) (hg : g ∈ centralizer ({x} : Set G)), g ∈ I1 → proj x ⟨g, hg⟩ ∈ Ib := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := h.setup
  have hEel := hset.E_ea
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hset.y_mem).symm
  have hE2 : IsPGroup 2 ↥E := IsElementaryAbelian.isPGroup 2 ↥E
  have hyE : y ∈ normalizer (E : Set G) := hset.E_norm y (Subgroup.subset_closure (by simp))
  have hxD : x ∈ (closure ({x, y} : Set G) : Subgroup G) := Subgroup.subset_closure (by simp)
  set Y : Subgroup G :=
    centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) : Set G) with hY
  have hYC : Y ≤ centralizer ({x} : Set G) := centralizer_sup_le_left_of_mem hxD
  set φ : ↥Y →* CentralizerBar x := projRes hYC with hφ
  set S : Subgroup (CentralizerBar x) :=
    centralizer ((imgBar x E : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) with hSdef
  have hrange : φ.range = centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S := by
    rw [hφ, range_projRes]
    exact imgBar_centralizer_sup hxy hset.y_ord hset.E_le hE2 hyE
  have hodd : ¬ 2 ∣ Nat.card φ.ker := not_two_dvd_card_ker_projRes hYC
  have hLbH : Lb ≤ centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K :=
    (exists_noncomm_two_elements_of_isQuasi2CompIn h.quasiL).1
  have hIbH0 : Ib ≤ extLayer2 (S ⊓ Lb) := SolvLiftBasic.isSolv2CompIn_le h.solvI
  have hH0 : extLayer2 (S ⊓ Lb) ≤ S ⊓ Lb := SolvLiftBasic.extLayer2_le _
  have hIbLb : Ib ≤ Lb := hIbH0.trans (hH0.trans inf_le_right)
  have hIbr : Ib ≤ φ.range := by
    rw [hrange]
    exact le_inf ((hIbLb.trans hLbH).trans inf_le_left) (hIbH0.trans (hH0.trans inf_le_left))
  set I1 : Subgroup G := (Ib.comap φ).map Y.subtype with hI1
  have hI1Y : I1 ≤ Y := Subgroup.map_subtype_le _
  have hI1Ib : ∀ (g : G) (hg : g ∈ centralizer ({x} : Set G)), g ∈ I1 →
      proj x ⟨g, hg⟩ ∈ Ib := by
    intro g hg hgI
    obtain ⟨z, hz, rfl⟩ := hgI
    exact hz
  refine ⟨oPrimeResidualOf 2 I1, I1, ⟨hI1Y, rfl, ?_, ?_, ?_, ?_, ?_⟩, hI1Ib⟩
  · exact le_antisymm (Balance.oPrimeResidualOf_le_self _)
      (oPrimeResidualOf_le_oPrimeResidualOf_self _)
  · exact SolvLiftBasic.exists_sl23_preimage φ hodd hIbr hI1
      (SolvLiftBasic.exists_sl23_of_isSolv2CompIn h.solvI)
  · refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
    obtain ⟨z, hz, rfl⟩ := hv
    have hzC : (z : G) ∈ centralizer ({x} : Set G) := hYC z.2
    have hzy : (z : G) * y = y * (z : G) :=
      commute_y_of_mem_centralizer_sup (x := x) (y := y) (E := E) z.2
    have hzLb : proj x ⟨(z : G), hzC⟩ ∈ Lb := hIbLb hz
    have hmem : (z : G) ∈ ((Lb.comap (proj x)).map (centralizer ({x} : Set G)).subtype) ⊓
        centralizer ({y} : Set G) :=
      ⟨⟨⟨(z : G), hzC⟩, hzLb, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hzy⟩
    exact Balance.mem_oPrimeResidualOf_of_two_element hmem h2
  · obtain ⟨-, a, b, haIb, hbIb, ⟨k1, hk1⟩, ⟨k2, hk2⟩, hab⟩ :=
      exists_noncomm_two_elements_of_isQuasi2CompIn (H := extLayer2 (S ⊓ Lb)) (Lb := Ib)
        (Or.inr h.solvI)
    obtain ⟨g₁, hg₁Y, hg₁I, ⟨m₁, hm₁⟩, hφ₁⟩ :=
      SolvLiftBasic.exists_two_element_preimage φ hodd hIbr hI1 haIb hk1
    obtain ⟨g₂, hg₂Y, hg₂I, ⟨m₂, hm₂⟩, hφ₂⟩ :=
      SolvLiftBasic.exists_two_element_preimage φ hodd hIbr hI1 hbIb hk2
    refine ⟨g₁, Balance.mem_oPrimeResidualOf_of_two_element hg₁I ⟨m₁, hm₁⟩, g₂,
      Balance.mem_oPrimeResidualOf_of_two_element hg₂I ⟨m₂, hm₂⟩, ⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩,
      fun hcom => hab ?_⟩
    have h1 : (⟨g₁, hg₁Y⟩ : ↥Y) * ⟨g₂, hg₂Y⟩ = ⟨g₂, hg₂Y⟩ * ⟨g₁, hg₁Y⟩ := Subtype.ext hcom
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hφ₁, hφ₂] at h2
    exact h2
  · intro e he he1
    have heC : e ∈ centralizer ({x} : Set G) := hset.E_le he
    have hxe : x * e = e * x := (Subgroup.mem_centralizer_singleton_iff.1 heC).symm
    have he2 : orderOf e = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) e he) he1
    have hbarE : bar x e ∈ imgBar x E := mem_imgBar.2 ⟨⟨e, heC⟩, he, (bar_of_mem heC).symm⟩
    have hbar1 : bar x e ≠ 1 := by
      intro h1
      rw [bar_of_mem heC] at h1
      have h3 := proj_odd x ⟨e, heC⟩ h1
      rw [Subgroup.orderOf_mk, he2] at h3
      exact absurd h3 (by decide)
    obtain ⟨Ie, hIe, hIbIe⟩ := h.exists_Ie (bar x e) hbarE hbar1
    have hI1A : I1 ≤ centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G) := by
      intro g hg
      refine Subgroup.mem_inf.2 ⟨hYC (hI1Y hg), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_mem_centralizer_sup (x := x) (y := y) (E := E) (hI1Y hg) he
    obtain ⟨V, hV, hIV⟩ := SolvLiftQuasi.exists_quasi_e hK hxe he2 hIe I1 hI1A (by
      intro g hg hgI h2
      refine hIbIe (Balance.mem_oPrimeResidualOf_of_two_element (hI1Ib g hg hgI) ?_)
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have h3 : (⟨g, hg⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ k) = 1 :=
        Subtype.ext (by simpa using hk)
      rw [← map_pow, h3, map_one])
    exact ⟨V, hV, hIV⟩

end S3T2L291

end CFSG.GH74.Generic.BProg.B3

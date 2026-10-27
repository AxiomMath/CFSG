module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4a

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def mbarKer {X : Type} [Group X] (M : Subgroup X) : Subgroup X :=
  (goldschmidtOddCore ↥M).map M.subtype

@[expose] def mbarPre {X : Type} [Group X] (M : Subgroup X) (J : Subgroup (Mbar M)) :
    Subgroup X :=
  (J.comap (mbarMk M)).map M.subtype

theorem mem_mbarKer_iff {X : Type} [Group X] (M : Subgroup X) (x : ↥M) :
    (x : X) ∈ mbarKer M ↔ mbarMk M x = 1 := by
  show M.subtype x ∈ (goldschmidtOddCore ↥M).map M.subtype ↔ mbarMk M x = 1
  rw [Subgroup.mem_map_iff_mem M.subtype_injective]
  simpa [mbarMk] using (QuotientGroup.eq_one_iff x).symm

theorem mem_mbarPre_iff {X : Type} [Group X] (M : Subgroup X) (J : Subgroup (Mbar M))
    (x : ↥M) : (x : X) ∈ mbarPre M J ↔ mbarMk M x ∈ J := by
  show M.subtype x ∈ (J.comap (mbarMk M)).map M.subtype ↔ mbarMk M x ∈ J
  rw [Subgroup.mem_map_iff_mem M.subtype_injective, Subgroup.mem_comap]

theorem mbarKer_le_mbarPre {X : Type} [Group X] (M : Subgroup X) (J : Subgroup (Mbar M)) :
    mbarKer M ≤ mbarPre M J := by
  intro z hz
  rw [mbarKer] at hz
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hz
  apply (mem_mbarPre_iff M J o).2
  have h1 : mbarMk M o = 1 := by
    rw [mbarMk]
    exact (QuotientGroup.eq_one_iff o).2 ho
  rw [h1]
  exact J.one_mem

instance mbarKer_normal {X : Type} [Group X] (M : Subgroup X) [M.Normal] :
    (mbarKer M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mbarKer] at hn ⊢
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hn
  refine Subgroup.mem_map.2 ⟨MulAut.conjNormal (H := M) g o, ?_, ?_⟩
  · have hmem := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := M) g).toMonoidHom ho
    rw [map_oddCore_conjNormal M g] at hmem
    exact hmem
  · simp [MulAut.conjNormal_apply]

theorem odd_card_mbarKer {X : Type} [Group X] [Finite X] (M : Subgroup X) :
    Odd (Nat.card (mbarKer M)) := by
  rw [mbarKer, Subgroup.card_map_of_injective M.subtype_injective]
  exact odd_card_goldschmidtOddCore

theorem mbarPre_isSubnormal {X : Type} [Group X] (M : Subgroup X) [M.Normal]
    (J : Subgroup (Mbar M)) [J.Normal] : (mbarPre M J).IsSubnormal := by
  have hBM : mbarPre M J ≤ M := Subgroup.map_subtype_le (J.comap (mbarMk M))
  have hsub : (mbarPre M J).subgroupOf M = J.comap (mbarMk M) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact mem_mbarPre_iff M J x
  have hN : ((mbarPre M J).subgroupOf M).Normal := by
    rw [hsub]
    exact Subgroup.Normal.comap (inferInstance : J.Normal) (mbarMk M)
  exact Subgroup.IsSubnormal.step (mbarPre M J) M hBM
    (Subgroup.Normal.isSubnormal (inferInstance : M.Normal)) hN

theorem mbarPre_quotient {X : Type} [Group X] (M : Subgroup X) [M.Normal]
    (J : Subgroup (Mbar M)) :
    Nonempty (↥(mbarPre M J) ⧸ (mbarKer M).subgroupOf (mbarPre M J) ≃* ↥J) := by
  classical
  have hBM : mbarPre M J ≤ M := Subgroup.map_subtype_le (J.comap (mbarMk M))
  let ψ : ↥(mbarPre M J) →* Mbar M := (mbarMk M).comp (Subgroup.inclusion hBM)
  have hψmem : ∀ b : ↥(mbarPre M J), ψ b ∈ J := fun b =>
    (mem_mbarPre_iff M J (Subgroup.inclusion hBM b)).1 (by simpa using b.2)
  let φ : ↥(mbarPre M J) →* ↥J := ψ.codRestrict J hψmem
  have hφval : ∀ b : ↥(mbarPre M J),
      ((φ b : ↥J) : Mbar M) = mbarMk M (Subgroup.inclusion hBM b) := fun _ => rfl
  have hφsurj : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M) j
    have hm' : mbarMk M m = j := hm
    have hmJ : mbarMk M m ∈ J := by rw [hm']; exact hj
    have hmB : (m : X) ∈ mbarPre M J := (mem_mbarPre_iff M J m).2 hmJ
    refine ⟨⟨(m : X), hmB⟩, ?_⟩
    apply Subtype.ext
    show mbarMk M (Subgroup.inclusion hBM ⟨(m : X), hmB⟩) = j
    have hmi : (Subgroup.inclusion hBM ⟨(m : X), hmB⟩ : ↥M) = m := Subtype.ext rfl
    rw [hmi, hm']
  have hker : (mbarKer M).subgroupOf (mbarPre M J) = φ.ker := by
    ext b
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hb
      apply Subtype.ext
      show mbarMk M (Subgroup.inclusion hBM b) = 1
      exact (mem_mbarKer_iff M (Subgroup.inclusion hBM b)).1 (by simpa using hb)
    · intro hb
      have hb' : mbarMk M (Subgroup.inclusion hBM b) = 1 := by
        rw [← hφval b]
        simpa using congrArg Subtype.val hb
      exact (mem_mbarKer_iff M (Subgroup.inclusion hBM b)).2 hb'
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)⟩

end CFSG.OddStandard.SmallF3.Omega

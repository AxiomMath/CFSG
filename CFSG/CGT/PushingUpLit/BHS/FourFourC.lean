module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic
public import CFSG.CGT.PushingUpLit.BHS.NatSL2

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp42

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

omit [Finite V] in
theorem dCore_conjSub {g : MulAut V} (hg : g ∈ P) : dCore P D (conjSub g M) = dCore P D M := by
  ext X
  constructor
  · rintro ⟨hXD, hX⟩
    refine ⟨hXD, fun y hy => ?_⟩
    have := hX (y * g⁻¹) (P.mul_mem hy (P.inv_mem hg))
    rwa [← conjSub_mul, inv_mul_cancel_right] at this
  · rintro ⟨hXD, hX⟩
    refine ⟨hXD, fun y hy => ?_⟩
    rw [← conjSub_mul]
    exact hX _ (P.mul_mem hy hg)

omit [Finite V] in
theorem conj (h : Hyp42 P D T M) {g : MulAut V} (hg : g ∈ P) :
    Hyp42 P D (conjSub g T) (conjSub g M) where
  toHyp41 := h.toHyp41
  syl := by
    have := isSylowOf_conjSub h.syl g
    rwa [conjSub_self_of_mem hg] at this
  le_M := conjSub_mono g h.le_M
  M_le := (conjSub_mono g h.M_le).trans (conjSub_self_of_mem hg).le
  ne_core := by
    rw [dCore_conjSub hg]
    exact h.ne_core
  normSet_le := by
    intro x hx
    have hxP : x ∈ P := hx.1
    have hmem : g⁻¹ * x * g ∈ setNormalizer P (dInter D T) := by
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg, fun A => ?_⟩
      have e : ∀ B : Subgroup (MulAut V), B ∈ dInter D T ↔
          conjSub g B ∈ dInter D (conjSub g T) := fun B => by
        rw [h.toHyp41.dInter_conjSub hg T]
        exact (FourTwoTools.conjSub_injective g).mem_set_image.symm
      have h1 : conjSub x (conjSub g A) = conjSub g (conjSub (g⁻¹ * x * g) A) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
      rw [e A, hx.2 (conjSub g A), h1, ← e]
    exact mem_conjSub_iff.2 (h.normSet_le hmem)
  cen_le := by
    intro x hx
    have hxP : x ∈ P := hx.1
    have hmem : g⁻¹ * x * g ∈ cenIn P (fixV T) := by
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg, fun u hu => ?_⟩
      have hgu : g u ∈ fixV (conjSub g T) := by
        rw [conjSub, Glauberman.fixV_map_conj]
        exact ⟨u, hu, rfl⟩
      have := hx.2 (g u) hgu
      simp only [MulAut.mul_apply]
      rw [this]
      simp
    exact mem_conjSub_iff.2 (h.cen_le hmem)

theorem exists_conj (h : Hyp42 P D T M) {g : MulAut V} (hg : g ∈ P) {A : Subgroup (MulAut V)}
    (hA2 : IsPGroup 2 A) (hAM : A ≤ conjSub g M) :
    ∃ T' : Subgroup (MulAut V), A ≤ T' ∧ Hyp42 P D T' (conjSub g M) := by
  have hc := h.conj hg
  have hTM : IsSylowOf 2 (conjSub g T) (conjSub g M) :=
    isSylowOf_of_le_of_le hc.syl hc.le_M hc.M_le
  obtain ⟨m, hmM, hm⟩ := FourTwoTools.exists_conjSub_ge hTM hA2 hAM
  have hmP : m ∈ P := hc.M_le hmM
  refine ⟨conjSub m (conjSub g T), hm, ?_⟩
  have h2 := h.conj (P.mul_mem hmP hg)
  rw [conjSub_mul, conjSub_mul, conjSub_self_of_mem (show m ∈ conjSub g M from hmM)] at h2
  exact h2

end Hyp42

omit [Finite V] in
theorem card_commV_zpowers_mul (s : MulAut V) :
    Nat.card (commV (Subgroup.zpowers s)) * Nat.card (fixV (Subgroup.zpowers s)) =
      Nat.card V := by
  have h1 := Subgroup.card_ker_mul_card_range (NatSL2.commMap s)
  rw [NatSL2.ker_commMap, ← NatSL2.commV_zpowers_eq_range] at h1
  rwa [mul_comm] at h1

end CFSG.CGT.PushingUpLit.BHS

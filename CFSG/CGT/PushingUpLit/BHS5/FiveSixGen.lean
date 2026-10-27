module

public import CFSG.CGT.PushingUpLit.BHS5.FiveSixQuot

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V]

theorem le_closure_odd_of_quot {P : Subgroup (MulAut V)} (hinj : Function.Injective (quotHom P))
    {E : Subgroup (MulAut V)} (hEP : E ≤ P)
    (h : (E.subgroupOf P).map (quotHom P) ≤
      Subgroup.closure {x | x ∈ (E.subgroupOf P).map (quotHom P) ∧ Odd (orderOf x)}) :
    E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)} := by
  set K : Subgroup (MulAut V) := Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)} with hK
  have hKE : K ≤ E := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hmap : (E.subgroupOf P).map (quotHom P) ≤ (K.subgroupOf P).map (quotHom P) := by
    refine h.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨hx, hodd⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hyE : (y : MulAut V) ∈ E := Subgroup.mem_subgroupOf.1 hy
    refine ⟨y, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨hyE, ?_⟩), rfl⟩
    rw [Subgroup.orderOf_coe y, ← orderOf_injective (quotHom P) hinj y]
    exact hodd
  intro x hx
  have hxP : x ∈ P := hEP hx
  obtain ⟨y, hy, hyx⟩ := hmap ⟨⟨x, hxP⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hy' : y = ⟨x, hxP⟩ := hinj hyx
  rw [hy'] at hy
  exact Subgroup.mem_subgroupOf.1 hy

omit [CommGroup V] in
theorem map_mem_commV_conj {W : Type} [CommGroup W] (E : Subgroup (MulAut W)) (t : MulAut W)
    {w : W} (hw : w ∈ commV E) : t w ∈ commV (conjSub t E) := by
  refine Subgroup.closure_induction (p := fun w _ => t w ∈ commV (conjSub t E)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x, hx, v, rfl⟩
    have h0 : (t * x * t⁻¹) (t v) = t (x v) := by simp [MulAut.mul_apply]
    have h1 : t (x v * v⁻¹) = (t * x * t⁻¹) (t v) * (t v)⁻¹ := by
      rw [map_mul, map_inv, h0]
    rw [h1]
    exact Subgroup.subset_closure ⟨t * x * t⁻¹, mem_conjSub_of_mem hx, t v, rfl⟩
  · rw [map_one]
    exact (commV (conjSub t E)).one_mem
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (commV (conjSub t E)).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (commV (conjSub t E)).inv_mem ha

end CFSG.CGT.PushingUpLit.BHS5

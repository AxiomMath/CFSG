module

public import CFSG.Quasithin.EmptyFaithful.E22PGen
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem exists_conj_map_le_and_centralizer_inf_eq_of_isSylowIn
    {Γ : Type*} [Group Γ] [Finite Γ]
    (P S H R : Subgroup Γ) (a t h : Γ)
    (hP : IsPGroup 2 P) (hPH : P ≤ H) (hSP : S ≤ P)
    (hS : IsSylowIn 2 S (H ⊓ Subgroup.centralizer ({t} : Set Γ)))
    (hR : IsSylowIn 2 R (H ⊓ Subgroup.centralizer ({a} : Set Γ)))
    (hh : h ∈ H)
    (hfuse : R ≤ Subgroup.centralizer ({h * t * h⁻¹} : Set Γ)) :
    ∃ g ∈ H,
      R.map (MulAut.conj g).toMonoidHom ≤ S ∧
      P ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set Γ) =
        R.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ht : Subgroup Γ := H ⊓ Subgroup.centralizer ({t} : Set Γ)
  let R0 : Subgroup Γ := R.map (MulAut.conj h⁻¹).toMonoidHom
  have hR0H : R0 ≤ H := by
    rintro x ⟨y, hy, rfl⟩
    have hhinv : (h⁻¹)⁻¹ ∈ H := by simpa using hh
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) ((hR.le hy).1)) hhinv
  have hR0C : R0 ≤ Subgroup.centralizer ({t} : Set Γ) := by
    rintro x ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hfuse hy)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc
      (MulAut.conj h⁻¹ y) * t = h⁻¹ * (y * (h * t * h⁻¹)) * h := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = h⁻¹ * ((h * t * h⁻¹) * y) * h := by rw [hy']
      _ = t * (MulAut.conj h⁻¹ y) := by
        simp [MulAut.conj_apply, mul_assoc]
  have hR0Ht : R0 ≤ Ht := le_inf hR0H hR0C
  have hR0P : IsPGroup 2 R0 := hR.isPGroup.map (MulAut.conj h⁻¹).toMonoidHom
  have hR0HtP : IsPGroup 2 (R0.subgroupOf Ht) := hR0P.comap_subtype (K := Ht)
  have hS_top : IsSylowIn 2 (S.subgroupOf Ht) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := S) (K := Ht) (H := Ht)
      hS.le le_rfl).mpr hS
    simpa using h
  obtain ⟨k, hk⟩ := E1.exists_conjSub_le_of_isSylowIn (G := Ht)
    (T := S.subgroupOf Ht) (A := R0.subgroupOf Ht) hS_top hR0HtP
  let g : Γ := (k : Γ) * h⁻¹
  have hgH : g ∈ H := H.mul_mem (Subgroup.mem_inf.mp k.2).1 (H.inv_mem hh)
  have hRg_le_S : R.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro y ⟨r, hr, rfl⟩
    have hxR0 : MulAut.conj h⁻¹ r ∈ R0 := ⟨r, hr, rfl⟩
    have hxHt : MulAut.conj h⁻¹ r ∈ Ht := hR0Ht hxR0
    have h1 : (⟨MulAut.conj h⁻¹ r, hxHt⟩ : Ht) ∈ R0.subgroupOf Ht := hxR0
    have h2 : (k * ⟨MulAut.conj h⁻¹ r, hxHt⟩ * k⁻¹ : Ht) ∈ S.subgroupOf Ht :=
      hk (A1b.mem_conjSub_of_mem h1)
    have h3 : ((k : Γ) * (MulAut.conj h⁻¹ r) * (k : Γ)⁻¹) ∈ S := h2
    convert h3 using 1
    simp [g, MulAut.conj_apply, mul_assoc]
  have hHmap : H.map (MulAut.conj g).toMonoidHom = H := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgH)
  have hRg_sylow : IsSylowIn 2 (R.map (MulAut.conj g).toMonoidHom)
      (H ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set Γ)) := by
    have h := (E1.isSylowIn_map_mulEquiv (p := 2) (e := MulAut.conj g)
      (P := R) (H := H ⊓ Subgroup.centralizer ({a} : Set Γ))).mpr hR
    rw [CFSG.centralizer_inter_map] at h
    rw [hHmap] at h
    simpa [MulAut.conj_apply] using h
  have hRg_sylowOf : CFSG.ABGLocalTools.IsSylowOf 2
      (R.map (MulAut.conj g).toMonoidHom)
      (H ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set Γ)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hRg_sylow.le, hRg_sylow.isPGroup, hRg_sylow.not_dvd_relIndex⟩
  let Q : Subgroup Γ := P ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set Γ)
  have hRg_le_Q : R.map (MulAut.conj g).toMonoidHom ≤ Q := by
    intro x hx
    exact ⟨hSP (hRg_le_S hx), (hRg_sylow.le hx).2⟩
  have hQ_le : Q ≤ H ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set Γ) :=
    le_inf (inf_le_left.trans hPH) inf_le_right
  have hQp : IsPGroup 2 Q := hP.to_inf_left
  have hQeq : Q = R.map (MulAut.conj g).toMonoidHom :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hRg_sylowOf hRg_le_Q hQ_le hQp
  exact ⟨g, hgH, hRg_le_S, hQeq⟩

end CFSG.GroupTheory

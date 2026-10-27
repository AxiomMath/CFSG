module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Setting

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

open Classical in
noncomputable def projFun (x : centralizer ({H.z} : Set G)) : H.M :=
  if h : (x : G) ∈ H.M then ⟨x, h⟩
  else ⟨x * H.z, ((H.mem_centralizer_iff).1 x.2).resolve_left h⟩

theorem projFun_of_mem {x : centralizer ({H.z} : Set G)} (h : (x : G) ∈ H.M) :
    ((H.projFun x : H.M) : G) = x := by
  simp [projFun, h]

theorem projFun_of_not_mem {x : centralizer ({H.z} : Set G)} (h : (x : G) ∉ H.M) :
    ((H.projFun x : H.M) : G) = x * H.z := by
  simp [projFun, h]

noncomputable def proj : centralizer ({H.z} : Set G) →* H.M where
  toFun := H.projFun
  map_one' := by
    apply Subtype.ext
    rw [H.projFun_of_mem (x := 1) (one_mem _)]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    have hxz : (x : G) * H.z = H.z * x := mem_centralizer_singleton_iff.1 x.2
    have hyz : (y : G) * H.z = H.z * y := mem_centralizer_singleton_iff.1 y.2
    have hmul : ((H.projFun x * H.projFun y : H.M) : G) =
        ((H.projFun x : H.M) : G) * (H.projFun y : H.M) := rfl
    by_cases hx : (x : G) ∈ H.M <;> by_cases hy : (y : G) ∈ H.M
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∈ H.M := mul_mem hx hy
      rw [hmul, H.projFun_of_mem hxy, H.projFun_of_mem hx, H.projFun_of_mem hy]
      rfl
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∉ H.M := fun h => hy (by
        have := mul_mem (inv_mem hx) h
        simpa using this)
      rw [hmul, H.projFun_of_not_mem hxy, H.projFun_of_mem hx, H.projFun_of_not_mem hy]
      change _ = (x : G) * ((y : G) * H.z)
      simp [mul_assoc]
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∉ H.M := fun h => hx (by
        have := mul_mem h (inv_mem hy)
        simpa using this)
      rw [hmul, H.projFun_of_not_mem hxy, H.projFun_of_not_mem hx, H.projFun_of_mem hy]
      change _ = (x : G) * H.z * (y : G)
      simp [mul_assoc, ← hyz]
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∈ H.M := by
        have h1 := (H.mem_centralizer_iff).1 x.2
        have h2 := (H.mem_centralizer_iff).1 y.2
        have hx' := h1.resolve_left hx
        have hy' := h2.resolve_left hy
        have := mul_mem hx' hy'
        have e : (x : G) * H.z * ((y : G) * H.z) = (x : G) * y := by
          calc (x : G) * H.z * ((y : G) * H.z) = (x : G) * (H.z * (y : G)) * H.z := by group
            _ = (x : G) * ((y : G) * H.z) * H.z := by rw [hyz]
            _ = (x : G) * y * (H.z * H.z) := by group
            _ = (x : G) * y := by rw [H.z_mul_self, mul_one]
        show (x : G) * (y : G) ∈ H.M
        rw [← e]
        exact this
      rw [hmul, H.projFun_of_mem hxy, H.projFun_of_not_mem hx, H.projFun_of_not_mem hy]
      change (x : G) * y = (x : G) * H.z * ((y : G) * H.z)
      calc (x : G) * y = (x : G) * y * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
        _ = (x : G) * (y * H.z) * H.z := by group
        _ = (x : G) * (H.z * y) * H.z := by rw [hyz]
        _ = (x : G) * H.z * ((y : G) * H.z) := by group

theorem proj_val {x : centralizer ({H.z} : Set G)} :
    (x : G) = ((H.proj x : H.M) : G) ∨ (x : G) = ((H.proj x : H.M) : G) * H.z := by
  by_cases h : (x : G) ∈ H.M
  · left; exact (H.projFun_of_mem h).symm
  · right
    show (x : G) = ((H.projFun x : H.M) : G) * H.z
    rw [H.projFun_of_not_mem h]
    calc (x : G) = (x : G) * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
      _ = (x : G) * H.z * H.z := by group

theorem exists_conj_le_V {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({H.z} : Set G)) :
    ∃ g ∈ H.M, P ≤ H.V.map (MulAut.conj g).toMonoidHom := by
  set C : Subgroup G := centralizer ({H.z} : Set G) with hC
  have hP' : IsPGroup 2 (P.comap C.subtype) := hP.comap_subtype
  set Q : Subgroup G := ((P.comap C.subtype).map H.proj).map H.M.subtype with hQ
  have hQp : IsPGroup 2 Q := (hP'.map H.proj).map _
  have hQM : Q ≤ H.M := by
    rintro _ ⟨l, _, rfl⟩
    exact l.2
  obtain ⟨g, hgM, hg⟩ := H.sylow_M Q hQM hQp
  have hzg : g * H.z * g⁻¹ = H.z := by
    have := H.comm_z hgM
    calc g * H.z * g⁻¹ = (H.z * g) * g⁻¹ := by rw [this]
      _ = H.z := by group
  refine ⟨g, hgM, fun x hx => ?_⟩
  set y : C := ⟨x, hPC hx⟩ with hy
  have hlQ : ((H.proj y : H.M) : G) ∈ Q := ⟨H.proj y, ⟨y, hx, rfl⟩, rfl⟩
  obtain ⟨e, he, hel⟩ := hg hlQ
  have hconj : ((MulAut.conj g).toMonoidHom e : G) = ((H.proj y : H.M) : G) := hel
  have hz' : (MulAut.conj g).toMonoidHom H.z = H.z := by
    simpa [MulAut.conj_apply] using hzg
  rcases H.proj_val (x := y) with h | h
  · refine ⟨e, mem_sup_left he, ?_⟩
    rw [hconj]
    exact h.symm
  · refine ⟨e * H.z, mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _)), ?_⟩
    rw [map_mul, hz', hconj]
    exact h.symm

end Setting

end CFSG.EvenSporadicStandard.ReeStd

module

public import CFSG.LargeExtraspecial.AS35CSmith
public import CFSG.LargeExtraspecial.DWSm77Aut
public import CFSG.LargeExtraspecial.DWSm77Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem trivialInter_conjBy
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    (h : G) :
    ∀ g t : G, g * (S.conjBy h).z * g⁻¹ ∈ (S.conjBy h).M →
      g * (S.conjBy h).z * g⁻¹ ≠ (S.conjBy h).z → t ∈ (S.conjBy h).QG →
        t ∈ (S.conjBy h).Qa g → t = 1 := by
  intro g t hgM hgne htQ hta
  have e1 : (h⁻¹ * g * h) * S.z * (h⁻¹ * g * h)⁻¹ =
      h⁻¹ * (g * (S.conjBy h).z * g⁻¹) * h := by
    rw [conjBy_z]
    group
  have h1 : (h⁻¹ * g * h) * S.z * (h⁻¹ * g * h)⁻¹ ∈ S.M := by
    rw [e1]
    exact (DW.Sm77.mem_conjBy_M_iff S).mp hgM
  have h2 : (h⁻¹ * g * h) * S.z * (h⁻¹ * g * h)⁻¹ ≠ S.z := by
    rw [e1]
    intro h'
    apply hgne
    rw [conjBy_z]
    calc g * (S.conjBy h).z * g⁻¹ = h * (h⁻¹ * (g * (S.conjBy h).z * g⁻¹) * h) * h⁻¹ := by
          group
      _ = h * S.z * h⁻¹ := by rw [h']
  have h3 : h⁻¹ * t * h ∈ S.QG := (DW.Sm77.mem_conjBy_QG_iff S).mp htQ
  have h4 : h⁻¹ * t * h ∈ S.Qa (h⁻¹ * g * h) := by
    rw [S.Qa_conjBy, S.Qa_eq_map, DW.Sm77.mem_map_conj] at hta
    rw [S.Qa_eq_map, DW.Sm77.mem_map_conj]
    have e2 : (h⁻¹ * g * h)⁻¹ * (h⁻¹ * t * h) * (h⁻¹ * g * h) = (g * h)⁻¹ * t * (g * h) := by
      group
    rw [e2]
    exact hta
  have h5 := H _ _ h1 h2 h3 h4
  calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
    _ = 1 := by rw [h5]; group

theorem commute_z_of_trivialInter
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    {j : G} (hjQ : j ∈ S.QG) (hj1 : j ≠ 1) {P : Subgroup G} (hP : IsPGroup 2 P) {f : G}
    (hfj : f * j = j * f) (hfP : f * S.z * f⁻¹ * S.z⁻¹ ∈ P) : f * S.z = S.z * f := by
  have hzX : S.z ∈ centralizer ({j} : Set G) :=
    mem_centralizer_singleton_iff.mpr (S.z_comm_QG hjQ).symm
  let zX : centralizer ({j} : Set G) := ⟨S.z, hzX⟩
  have hz1 : zX ≠ 1 := fun h => S.z_ne_one (congrArg Subtype.val h)
  have hz2 : zX * zX = 1 := Subtype.ext S.z_mul_z
  have hiso : ∀ c : centralizer ({j} : Set G),
      c * zX * c⁻¹ * zX = zX * (c * zX * c⁻¹) → c * zX * c⁻¹ = zX := by
    intro c hc
    have hc' : (c : G) * S.z * (c : G)⁻¹ * S.z = S.z * ((c : G) * S.z * (c : G)⁻¹) :=
      congrArg Subtype.val hc
    by_contra hne
    have hne' : (c : G) * S.z * (c : G)⁻¹ ≠ S.z := fun h => hne (Subtype.ext h)
    have hcj : (c : G) * j = j * c := mem_centralizer_singleton_iff.mp c.2
    exact hj1 (H c j (S.mem_M_iff.mpr hc') hne' hjQ (S.mem_Qa_of_commute hjQ hcj))
  obtain ⟨N, -, hNodd, hN⟩ := S10.exists_odd_normal_of_isolated zX hz1 hz2 hiso
  have hfX : f ∈ centralizer ({j} : Set G) := mem_centralizer_singleton_iff.mpr hfj
  have hmem : f * S.z * f⁻¹ * S.z⁻¹ ∈ N.map (centralizer ({j} : Set G)).subtype :=
    ⟨⟨f, hfX⟩ * zX * ⟨f, hfX⟩⁻¹ * zX⁻¹, hN ⟨f, hfX⟩, rfl⟩
  have hodd : Odd (Nat.card (N.map (centralizer ({j} : Set G)).subtype)) := by
    rw [card_map_of_injective (centralizer ({j} : Set G)).subtype_injective]
    exact hNodd
  have h1 := eq_one_of_mem_of_odd hodd hP hmem hfP
  calc f * S.z = f * S.z * f⁻¹ * S.z⁻¹ * (S.z * f) := by group
    _ = S.z * f := by rw [h1, one_mul]

theorem sq_eq_one_of_trivialInter
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {a : G} (haQ : a ∈ S.QG) (hax : a * x = x * a) : a ^ 2 = 1 := by
  rcases S.sq_eq_one_or_z haQ with h | h
  · exact h
  exfalso
  set T := S.conjBy g with hT
  have hTz : T.z = x := by rw [hT, conjBy_z, hgx]
  have haT : a ∈ T.M := by rw [T.mem_M_iff, hTz]; exact hax
  have hzT : S.z ∈ T.M := by rw [T.mem_M_iff, hTz]; exact (S.z_comm hxM).symm
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have hgM : g * S.z * g⁻¹ ∈ S.M := by rw [hgx]; exact hxM
  have hzQa : S.z ∉ S.Qa g := S.z_not_mem_Qa hW hne
  have hk4 : ∀ f ∈ T.QG, a ^ 4 * f * (a ^ 4)⁻¹ = f := by
    intro f _
    rw [S.pow_four_eq_one haQ]
    group
  have hC : ∀ f ∈ T.QG, a ^ 2 * f * (a ^ 2)⁻¹ = f → a * f * a⁻¹ = f := by
    intro f hf hf2
    rw [h] at hf2
    have hfz : f * S.z = S.z * f := by
      calc f * S.z = S.z * f * S.z⁻¹ * S.z := by rw [hf2]
        _ = S.z * f := by group
    have hfM : f ∈ S.M := S.mem_M_iff.mpr hfz
    have hkQ : a * f * a⁻¹ * f⁻¹ ∈ S.QG := by
      have := mul_mem haQ (S.conj_mem_QG hfM (inv_mem haQ))
      simpa [mul_assoc] using this
    have hkT : a * f * a⁻¹ * f⁻¹ ∈ S.Qa g := mul_mem (T.conj_mem_QG haT hf) (inv_mem hf)
    have hk1 := H g _ hgM hne hkQ hkT
    calc a * f * a⁻¹ = a * f * a⁻¹ * f⁻¹ * f := by group
      _ = f := by rw [hk1, one_mul]
  apply hzQa
  refine T.mem_QG_of_cl_conj hzT fun f hf => ?_
  rcases DW.Sm77.conj_sq_of_centralizer_le T le_rfl haT (fun f hf => T.conj_mem_QG haT hf) hk4
    hC hf with h' | h' <;> rw [h] at h'
  · rw [h']
  · rw [h', T.cl_mul_z hf]

end Setting

end CFSG.LargeExtraspecial

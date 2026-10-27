module

public import CFSG.LargeExtraspecial.S13FiveB
public import CFSG.LargeExtraspecial.S13Dich

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

theorem dich_of_row (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {τ t : S.O}
    (hτ : τ ∈ S.Lbar g) (hτE : τ ∉ Ebar S g K) (ht : t ∈ Ebar S g K) {e s x : S.M}
    (heP : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hea : S.cl (g * S.z * g⁻¹) ≠ S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹))
    (hs : S.cl ((s : G) * g * S.z * ((s : G) * g)⁻¹) =
      S.cl (g * S.z * g⁻¹) + S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹))
    (hτe : τ ∈ S.Lbar ((e : G) * g)) (hτs : τ ∈ S.Lbar ((s : G) * g))
    (hte : t ∈ S.Lbar ((e : G) * g)) (hts : t ∈ S.Lbar ((s : G) * g))
    (hxa : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hxe : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((e : G) * g)))
    (hxV : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∉ Vt S g t) :
    (∃ m : S.M, τ ∈ S.Lbar ((m : G) * g) ∧
      S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∉ Submodule.span (ZMod 2)
        {S.cl (g * S.z * g⁻¹), S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹)}) ∨
      τ * t ∈ S.Lbar ((x : G) * g) := by
  set a := S.cl (g * S.z * g⁻¹) with ha
  set pe := S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) with hpe
  set px := S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) with hpx
  set U := Submodule.span (ZMod 2) {a, pe} with hU
  have Ht := Ebar_le_Lbar ht
  have haU : a ∈ U := Submodule.subset_span (Set.mem_insert _ _)
  have heU : pe ∈ U := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hxU : px ∉ U := fun h => hxV ((Submodule.span_le.mpr (Set.insert_subset
    (cl_a_mem_Vt Ht) (Set.singleton_subset_iff.mpr (cl_mem_Vt hte)))) h)
  have hfτ := fix_of_mem_Lbar_inf hea hτ hτe hxa hxe
  have hft := fix_of_mem_Lbar_inf hea Ht hte hxa hxe
  have hτN := mem_normalizer_of_fix Y.haQ Y.hne (h := x) (S.Lbar_le_Mbar g hτ) hfτ
  have htN := mem_normalizer_of_fix Y.haQ Y.hne (h := x) (S.Lbar_le_Mbar g Ht) hft
  by_cases hL : ∃ m : S.M, τ ∈ S.Lbar ((m : G) * g) ∧
      S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∉ U
  · exact Or.inl hL
  right
  push Not at hL
  have hax : a ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := by
    have h1 := cl_mem_clSub_symm Y.H (h₁ := 1) (h₂ := x)
      (by simp only [OneMemClass.coe_one, one_mul]; exact hxa)
    simp only [OneMemClass.coe_one, one_mul] at h1
    exact h1
  have hex : pe ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := cl_mem_clSub_symm Y.H hxe
  have hτ1 : τ ∈ S.Lbar (((1 : S.M) : G) * g) := by simpa using hτ
  have ht1 : t ∈ S.Lbar (((1 : S.M) : G) * g) := by simpa using Ht
  have ha1 : S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) = a := by simp [ha]
  have hsU : S.cl ((s : G) * g * S.z * ((s : G) * g)⁻¹) ∈ U := by rw [hs]; exact add_mem haU heU
  have hkey : ∀ y ∈ S.Lbar ((x : G) * g), τ * y * τ⁻¹ = t * y * t⁻¹ := by
    intro y hy
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hy)
    have h2 : ∀ v : S.Qt, v + v = 0 := fun v => by
      rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rcases mem_span_cl_iff.mp (S.sub_mem_span_of_mem_clSub hy hax) with ha0 | ha0 <;>
      rcases mem_span_cl_iff.mp (S.sub_mem_span_of_mem_clSub hy hex) with he0 | he0
    ·
      have hfa := sub_eq_zero.mp ha0
      have hfe := sub_eq_zero.mp he0
      have hone : ∀ {l : S.O}, l ∈ S.Lbar g → l ∈ S.Lbar ((e : G) * g) →
          (∀ k ∈ K, k * (l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹) = (l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹) * k) →
          l ∈ normalizer (S.Lbar ((x : G) * g) : Set S.O) → l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ = 1 := by
        intro l hl hle hK hlN
        have hg : l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ S.Lbar g := by
          have h1 := Y.conj_mem_Lbar_of_fix (c := 1) (m := m) (l := l⁻¹)
            (by simpa using inv_mem hl) (by rw [ha1]; exact hfa)
          rw [show l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ = l * (S.ρ m * l⁻¹ * (S.ρ m)⁻¹) by group]
          exact mul_mem hl (by simpa using h1)
        have hge : l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ S.Lbar ((e : G) * g) := by
          have h1 := Y.conj_mem_Lbar_of_fix (inv_mem hle) hfe
          rw [show l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ = l * (S.ρ m * l⁻¹ * (S.ρ m)⁻¹) by group]
          exact mul_mem hle h1
        have hgx : l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ S.Lbar ((x : G) * g) :=
          mul_mem ((mem_normalizer_iff.mp hlN _).mp hy) (inv_mem hy)
        exact Y.eq_one_of_three' ((mem_Ebar).mpr ⟨hg, hK⟩) ⟨1, by simp⟩ ⟨e, rfl⟩ ⟨x, rfl⟩
          hg hge hgx hea heP hxa hxe hxU
      have hτ0 := hone hτ hτe (fun k hk => Y.comm_commute_K hτ hτE
        (MonoidHom.mem_range.mpr ⟨m, rfl⟩) hk) hτN
      have ht0 := hone Ht hte (fun k hk => comm_commute_K' Y.normal
        (fun k hk => ((mem_Ebar).mp ht).2 k hk) (MonoidHom.mem_range.mpr ⟨m, rfl⟩) hk) htN
      rw [mul_inv_eq_one.mp hτ0, mul_inv_eq_one.mp ht0]
    ·
      exact comm_eq_of_moved hCE Y hτ hτE ht hτ1 ht1 hτe hte hy hτN htN
        (by rw [ha1]; exact sub_eq_zero.mp ha0) (by rw [← he0]; abel) hxV hL heU hxU
    ·
      exact comm_eq_of_moved hCE Y hτ hτE ht hτe hte hτ1 ht1 hy hτN htN (sub_eq_zero.mp he0)
        (by rw [ha1, ← ha0]; abel) hxV hL (by rw [ha1]; exact haU) hxU
    ·
      have hfs : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl ((s : G) * g * S.z * ((s : G) * g)⁻¹)) =
          S.cl ((s : G) * g * S.z * ((s : G) * g)⁻¹) := by
        have e1 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + px := by
          rw [hpx, ← ha0]; abel
        have e2 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) pe = pe + px := by
          rw [hpx, ← he0]; abel
        rw [hs, map_add, e1, e2]
        calc a + px + (pe + px) = a + pe + (px + px) := by abel
          _ = a + pe := by rw [h2, add_zero]
      exact comm_eq_of_moved hCE Y hτ hτE ht hτs hts hτ1 ht1 hy hτN htN hfs
        (by rw [ha1, ← ha0]; abel) hxV hL (by rw [ha1]; exact haU) hxU
  have hττ : τ⁻¹ = τ := (eq_inv_of_mul_eq_one_left (mul_self_of_mem_Lbar S Y.haQ hτ)).symm
  have hcomm : ∀ y ∈ S.Lbar ((x : G) * g), τ * t * y = y * (τ * t) := by
    intro y hy
    have h1 := hkey y hy
    calc τ * t * y = τ * (t * y * t⁻¹) * t := by group
      _ = τ * (τ * y * τ⁻¹) * t := by rw [h1]
      _ = y * (τ * t) := by
        rw [hττ]
        simp only [← mul_assoc, mul_self_of_mem_Lbar S Y.haQ hτ, one_mul]
  have Yx : Hyp13 S ((x : G) * g) K := Y.mul rfl
  have hρxM : S.ρ x ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hl' : S.ρ x * (τ * t) * (S.ρ x)⁻¹ ∈ S.Lbar ((x : G) * g) :=
    conj_mem_Lbar_mul S x (mul_mem hτ Ht)
  have e : (S.ρ x)⁻¹ * (S.ρ x * (τ * t) * (S.ρ x)⁻¹) * (S.ρ x)⁻¹⁻¹ = τ * t := by group
  have key := conj_mem_Lbar_of_commute' Yx.haQ Yx.C hl' (inv_mem hρxM) (fun z hz => by
    rw [e]; exact hcomm z hz)
  rwa [e] at key

end Hyp13

end CFSG.LargeExtraspecial.S13

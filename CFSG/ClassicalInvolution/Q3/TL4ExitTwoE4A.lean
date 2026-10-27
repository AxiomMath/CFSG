module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.E4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem conjNormal_injective {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut ↥N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : g * x * g⁻¹ = x := by
    simpa [MulAut.conjNormal_apply] using
      congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) ⟨x, hx⟩)
  calc x * g = g * x * g⁻¹ * g := by rw [h1]
    _ = g * x := by group

theorem innSubgroup_le_range {N : Subgroup G} [N.Normal] :
    Q3NM.innSubgroup ↥N ≤ (MulAut.conjNormal : G →* MulAut ↥N).range := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, MulAut.conjNormal_val⟩

theorem oddCoreImg_centralizer_eq_bot [Finite G] {N : Subgroup G} [N.Normal]
    (hA : Q3NM.AutOddFree ↥N) (hC : Subgroup.centralizer (N : Set G) = ⊥) {z : G}
    (hz : orderOf z = 2) : oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  let e : G ≃* ↥(MulAut.conjNormal : G →* MulAut ↥N).range :=
    MonoidHom.ofInjective (conjNormal_injective hC)
  have hf : orderOf (e z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv e z (hA _ innSubgroup_le_range (e z) hf)

theorem eq_top_of_aut_inner {N : Subgroup G} [N.Normal]
    (hinn : ∀ α : MulAut ↥N, α ∈ Q3NM.innSubgroup ↥N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) : N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn⟩ := hinn (MulAut.conjNormal g)
  have hc : (n : G)⁻¹ * g ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hn ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    calc x * ((n : G)⁻¹ * g) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * g := by group
      _ = (n : G)⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]; rfl
      _ = (n : G)⁻¹ * g * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact n.2

theorem ambientQuatDatum_of_mem [Finite G] {Δ : Set (Subgroup G)}
    (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ)
    (hθ : ∀ z : G, orderOf z = 2 → oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥)
    {K : Subgroup G} (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) :
    Vtx.AmbientQuatDatum ⊤ K z := by
  have h2 : ∀ J ∈ Δ, IsPGroup 2 ↥J := fun J hJ => by
    obtain ⟨⟨zJ, hzJ⟩, -⟩ := h.hyp.omega1 J hJ
    exact PhilipHall.Frame.isPGroup_of_oddCent h.hyp hJ hzJ
      (hθ zJ (orderOf_eq_prime (by rw [sq]; exact hzJ.sq) hzJ.ne_one)) (h.twoGroup J hJ)
  refine ⟨le_top, h.quat K hK K (Vtx.isSylow2In_self (h2 K hK)), hz, fun c _ hcz => ?_⟩
  by_cases hcK : conjSub c K = K
  · exact Or.inl hcK
  · right
    have hz' : IsUniqueInvolution (conjSub c K) z := by
      have h1 := hz.conj c
      rwa [show c * z * c⁻¹ = z by rw [hcz, mul_inv_cancel_right]] at h1
    exact PhilipHall.Frame.OddQuot.commutes_of_twin_pgroup h.hyp h2 hK (h.hyp.conjInvariant c K hK)
      (Ne.symm hcK) hz hz'

theorem ambientQuatDatum_map {X : Type} [Group X] (φ : G →* X) (hφ : Function.Injective φ)
    {K : Subgroup G} {s : G} (hd : Vtx.AmbientQuatDatum ⊤ K s) :
    Vtx.AmbientQuatDatum φ.range (K.map φ) (φ s) := by
  obtain ⟨e⟩ := hd.q8
  refine ⟨Subgroup.map_le_range φ K, ⟨(K.equivMapOfInjective φ hφ).symm.trans e⟩,
    Vtx.isUniqueInvolution_map φ hφ hd.inv, ?_⟩
  rintro _ ⟨m, rfl⟩ hms
  have hm : m * s = s * m := hφ (by rw [map_mul, map_mul, hms])
  rw [conjSub_map]
  rcases hd.twins m (Subgroup.mem_top m) hm with h1 | h1
  · left
    rw [h1]
  · right
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h1 x hx y hy]

theorem conj_of_ident {X : Type} [Group X] {Δ : Set (Subgroup G)} (φ : G →* X)
    (hφ : Function.Injective φ) {Kc : Subgroup X}
    (hid : ∀ K ∈ Δ, ∃ m : G, conjSub (φ m) (K.map φ) = Kc) :
    ∀ J ∈ Δ, ∀ L ∈ Δ, ∃ g : G, conjSub g J = L := by
  intro J hJ L hL
  obtain ⟨m₁, h₁⟩ := hid J hJ
  obtain ⟨m₂, h₂⟩ := hid L hL
  refine ⟨m₂⁻¹ * m₁, Subgroup.map_injective hφ ?_⟩
  rw [← conjSub_map, map_mul, conjSub_mul, h₁, ← h₂, map_inv, conjSub_inv_conjSub]

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.E4

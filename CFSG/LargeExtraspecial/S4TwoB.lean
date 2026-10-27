module

public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.LargeExtraspecial.S4Span
public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem le_normalizer_of_isPGroup_of_weaklyClosed {L P : Subgroup X} (hLP : L ≤ P)
    (hP : IsPGroup 2 P)
    (hwc : ∀ x : X, L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set X) →
      L.map (MulAut.conj x).toMonoidHom = L) :
    P ≤ normalizer (L : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  by_contra hne
  set N := (normalizer (L : Set X)).subgroupOf P with hN
  have hNlt : N < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne fun y hy => ?_
    have : (⟨y, hy⟩ : P) ∈ N := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyn⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent N hNlt)
  apply hyn
  have hLN : ∀ u (hu : u ∈ L), (⟨u, hLP hu⟩ : P) ∈ N := fun u hu =>
    mem_subgroupOf.mpr (le_normalizer hu)
  have hmap : L.map (MulAut.conj (y : X)).toMonoidHom ≤ normalizer (L : Set X) := by
    rintro _ ⟨u, hu, rfl⟩
    have := (mem_normalizer_iff.mp hyN _).mp (hLN u hu)
    exact mem_subgroupOf.mp this
  exact mem_subgroupOf.mpr (mem_normalizer_of_map_conj_eq (hwc y hmap))

theorem exists_mem_conj_eq_of_weaklyClosed {L K : Subgroup X} [K.Normal] (hLK : L ≤ K)
    (hL : IsPGroup 2 L)
    (hwc : ∀ x : X, L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set X) →
      L.map (MulAut.conj x).toMonoidHom = L) (x : X) :
    ∃ k ∈ K, L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK' : IsPGroup 2 (L.subgroupOf K) :=
    hL.of_equiv (Subgroup.subgroupOfEquivOfLe hLK).symm
  obtain ⟨P, hP⟩ := hLK'.exists_le_sylow
  set S₀ := (P : Subgroup K).map K.subtype with hS₀
  have hLS : L ≤ S₀ := fun u hu => ⟨⟨u, hLK hu⟩, hP (mem_subgroupOf.mpr hu), rfl⟩
  have hS₀2 : IsPGroup 2 S₀ := P.isPGroup'.map K.subtype
  have hS₀N := le_normalizer_of_isPGroup_of_weaklyClosed hLS hS₀2 hwc
  have htop := Sylow.normalizer_sup_eq_top P
  have hx : x⁻¹ ∈ normalizer (S₀ : Set X) ⊔ K := htop ▸ mem_top _
  obtain ⟨n, hn, k, hk, hnk⟩ := mem_sup_of_normal_right.mp hx
  have hLn : L.map (MulAut.conj n⁻¹).toMonoidHom = L := by
    refine hwc _ ?_
    rintro _ ⟨u, hu, rfl⟩
    have := (mem_normalizer_iff.mp (inv_mem hn) u).mp (hLS hu)
    exact hS₀N this
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  have hxe : x = k⁻¹ * n⁻¹ := by
    rw [← inv_inj, mul_inv_rev, inv_inv, inv_inv, ← hnk]
  rw [hxe, show (MulAut.conj (k⁻¹ * n⁻¹)).toMonoidHom =
    (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj n⁻¹).toMonoidHom by ext; simp [mul_assoc],
    ← Subgroup.map_map, hLn]

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isReducible_of_le_centralizer (H : Hyp4 S g) {Z : Subgroup S.O} (hZ1 : Z ≠ ⊥)
    (hZn : ∀ m : S.M, ∀ z ∈ Z, S.ρ m * z * (S.ρ m)⁻¹ ∈ Z)
    (hZL : ∀ z ∈ Z, ∀ l ∈ S.Lbar g, z * l = l * z) : S.IsReducible := by
  have haL : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [H.fixSub_eq]
    exact Submodule.mem_span_singleton_self _
  have ha : S.cl (g * S.z * g⁻¹) ∈ fixSub S Z := by
    intro z hz
    have hmem : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ fixSub S (S.Lbar g) := by
      intro l hl
      rw [← coe_mul_apply, ← hZL z hz l hl, coe_mul_apply, haL l hl]
    rw [H.fixSub_eq] at hmem
    rcases CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mp hmem with h0 | h1
    · exact absurd ((LinearEquiv.map_eq_zero_iff _).mp h0)
        (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
    · exact h1
  refine ⟨fixSub S Z, fun h => ?_, fun h => ?_, fun m v hv => ?_⟩
  · rw [h] at ha
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne ((Submodule.mem_bot _).mp ha)
  · obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    ext v
    have : v ∈ fixSub S Z := h ▸ Submodule.mem_top
    exact this z hz
  · intro z hz
    have hz' := hZn m⁻¹ z hz
    rw [map_inv, inv_inv] at hz'
    have h1 := hv _ hz'
    rw [coe_mul_apply, coe_mul_apply] at h1
    have h2 := congrArg ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2

theorem isReducible_of_polar_eq_zero (H : Hyp4 S g)
    (h : ∀ m : S.M, polar S.q (S.cl (g * S.z * g⁻¹))
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0) :
    S.IsReducible := by
  set v := S.cl (g * S.z * g⁻¹) with hv
  set P : Set S.Qt := Set.range fun m : S.M => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
  set W := Submodule.span (ZMod 2) P
  have hvW : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
  have hP : ∀ x ∈ P, ∀ y ∈ P, S.q.polarBilin x y = 0 := by
    rintro _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩
    rw [polarBilin_apply_apply]
    have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ((S.ρ m₁)⁻¹).2
    calc polar S.q (((S.ρ m₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
          (((S.ρ m₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
        = polar S.q ((((S.ρ m₁)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((S.ρ m₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
          ((((S.ρ m₁)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((S.ρ m₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) := (hiso _ _).symm
      _ = polar S.q v (((S.ρ (m₁⁻¹ * m₂) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
          rw [inv_apply_apply_O, map_mul, map_inv, coe_mul_apply]
      _ = 0 := h _
  refine ⟨W, fun hW => ?_, fun hW => ?_, fun m w hw => ?_⟩
  · rw [hW] at hvW
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne ((Submodule.mem_bot _).mp hvW)
  · apply cl_conj_z_ne_zero S H.conj_mem H.conj_ne
    refine S.q_nondegenerate.1 v fun y => isotropic_span hP v hvW y ?_
    change y ∈ W
    rw [hW]
    exact Submodule.mem_top
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', rfl⟩ := hx
      rw [← coe_mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact W.smul_mem r hx

end CFSG.LargeExtraspecial.S4

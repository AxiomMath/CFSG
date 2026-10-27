module

public import CFSG.CGT.M24R.Assembly
public import CFSG.CGT.M24R.WrapCtx
public import CFSG.CGT.M24R.WrapM24Inv
public import CFSG.CGT.M24S.NSHolt
public import CFSG.CGT.M24S.NaturalSL

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Holt.General CFSG.Blueprint

variable {G : Type} [Group G]

theorem orderOf_ne_five_of_comm_conj {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) {z : G} (hzT : z ∈ T) (hz1 : z ≠ 1) (g f : G)
    (hf : f * (g⁻¹ * z * g) = g⁻¹ * z * g * f) : orderOf f ≠ 5 := by
  intro hf5
  have hNT := normalizer_eq_of_centralizer_eq h hL hC
  have hcz : g * f * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * f * g⁻¹ * z = g * (f * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * f) * g⁻¹ := by rw [hf]
      _ = z * (g * f * g⁻¹) := by group
  have hcH : g * f * g⁻¹ ∈ H := by
    rw [← hNT]
    exact hL.centralizer_le z hzT hz1 hcz
  have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hcH, hcz⟩)
  have ho : orderOf (g * f * g⁻¹) = orderOf f := MulEquiv.orderOf_eq (MulAut.conj g) f
  rw [ho, hf5, card_inf_centralizer_of_naturalSL h.le h.nat hzT hz1] at hdvd
  norm_num at hdvd

theorem forall_orderOf_ne_five_map {X : Subgroup G} (φ : ↥X ≃* ↥NativeSporadic.M24) (w : ↥X)
    (hw : ∀ f : G, f * (w : G) = (w : G) * f → orderOf f ≠ 5) :
    ∀ f ∈ NativeSporadic.M24,
      f * (φ w : Equiv.Perm (Fin 24)) = (φ w : Equiv.Perm (Fin 24)) * f → orderOf f ≠ 5 := by
  intro f hf hfc hf5
  have hc : φ.symm ⟨f, hf⟩ * w = w * φ.symm ⟨f, hf⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact Subtype.ext hfc
  refine hw (φ.symm ⟨f, hf⟩ : ↥X) (congrArg Subtype.val hc) ?_
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, φ.apply_symm_apply, ← Subgroup.orderOf_coe]
  exact hf5

theorem mem_of_conj_mem_of_mulEquiv_m24
    {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) {X : Subgroup G}
    (hX : Subgroup.normalizer (T : Set G) ≤ X) (φ : ↥X ≃* ↥NativeSporadic.M24) {z : G}
    (hzT : z ∈ T) (hz1 : z ≠ 1) {g : G} (hg : g⁻¹ * z * g ∈ X) : g ∈ X := by
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hzT)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (h.wc.1.2 z hzT) hz1
  let u : ↥X := ⟨z, hzX⟩
  let v : ↥X := ⟨g⁻¹ * z * g, hg⟩
  have hu5 : ∀ f : G, f * (u : G) = (u : G) * f → orderOf f ≠ 5 := fun f hf =>
    orderOf_ne_five_of_comm_conj h hL hC hzT hz1 1 f (by simpa using hf)
  have hv5 : ∀ f : G, f * (v : G) = (v : G) * f → orderOf f ≠ 5 :=
    orderOf_ne_five_of_comm_conj h hL hC hzT hz1 g
  have hu2 : orderOf ((φ u : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hz2
  have hv2 : orderOf ((φ v : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    have ho := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    simp only [MulAut.conj_apply, inv_inv] at ho
    exact ho.trans hz2
  obtain ⟨c, hc, hcv⟩ := m24_exists_conj_of_forall_orderOf_ne_five (φ u).2 (φ v).2 hu2 hv2
    (forall_orderOf_ne_five_map φ u hu5) (forall_orderOf_ne_five_map φ v hv5)
  have hxv : v = φ.symm ⟨c, hc⟩ * u * (φ.symm ⟨c, hc⟩)⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]
    exact Subtype.ext hcv
  obtain ⟨x, hxX, hxv'⟩ : ∃ x ∈ X, g⁻¹ * z * g = x * z * x⁻¹ :=
    ⟨_, (φ.symm ⟨c, hc⟩).2, congrArg Subtype.val hxv⟩
  have hgx : g * x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x * z = g * (x * z * x⁻¹) * x := by group
      _ = g * (g⁻¹ * z * g) * x := by rw [hxv']
      _ = z * (g * x) := by group
  have hgxX : g * x ∈ X := by
    apply hX
    exact hL.centralizer_le z hzT hz1 hgx
  have hgX := X.mul_mem hgxX (X.inv_mem hxX)
  rwa [mul_inv_cancel_right] at hgX

theorem eq_top_of_mulEquiv_m24
    [Finite G] [IsSimpleGroup G] (hHolt : CFSG.Holt.H78.HoltTheorem1) {T H : Subgroup G}
    (h : Hyp T H) (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T)
    {X : Subgroup G} (hX : Subgroup.normalizer (T : Set G) ≤ X)
    (φ : ↥X ≃* ↥NativeSporadic.M24) : X = ⊤ := by
  by_contra hXtop
  obtain ⟨S, hTS, -, z, hzT, hz1, hZ⟩ := hL.sylow
  have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
  have hz2 : z ^ 2 = 1 := h.wc.1.2 z hzT
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hzX : z ∈ X := hX (Subgroup.le_normalizer hzT)
  have hTrip : IsHoltTriple G (G ⧸ X) z ((1 : G) : G ⧸ X) := by
    refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, fun ω => ?_,
      ⟨S, hTS hzT, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
      show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
    exact ⟨fun hg => mem_of_conj_mem_of_mulEquiv_m24 h hL hC hX φ hzT hz1 hg,
      fun hg => X.mul_mem (X.mul_mem (X.inv_mem hg) hzX) hg⟩
  exact false_of_isHoltTriple hHolt hXtop (hL.card_sylow S) hZ hTrip

theorem isSporadic_m24_of_type4
    (hN8 : N8Statement) (hL2 : N8Statement → L2Statement8) (hR3 : R3Statement)
    (hR24 : R24Statement) (hHolt : CFSG.Holt.H78.HoltTheorem1) [Finite G] [IsSimpleGroup G]
    {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) (hcompl : HasComplement T H) {x g : G}
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) (hxg : x ∈ conjSubgroup g T)
    (hcx : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4) :
    NativeSporadic.IsSporadic G .M24 := by
  obtain ⟨X, hle, ⟨φ⟩⟩ := exists_mulEquiv_m24_of_parts hN8 hL2 hR3 hR24
    (m24CtxHyp_conjSubgroup_of_type4 h hL hC hcompl hxN hxT hxg hcx)
  have htop := eq_top_of_mulEquiv_m24 hHolt h hL hC (le_sup_left.trans hle) φ
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ⟩

end CFSG.CGT.M24R

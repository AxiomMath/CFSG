module

public import CFSG.LargeExtraspecial.AS35LPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35L

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Open CFSG.LieType.BorelTits

variable {X : Type} [Group X]

@[expose] def conjRestrict (L : Subgroup X) (u : X) (hu : ∀ x ∈ L, u * x * u⁻¹ ∈ L)
    (hu' : ∀ x ∈ L, u⁻¹ * x * u ∈ L) : L ≃* L where
  toFun x := ⟨u * x * u⁻¹, hu x x.2⟩
  invFun x := ⟨u⁻¹ * x * u, hu' x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjRestrict_apply (L : Subgroup X) (u : X) (hu : ∀ x ∈ L, u * x * u⁻¹ ∈ L)
    (hu' : ∀ x ∈ L, u⁻¹ * x * u ∈ L) (x : L) :
    ((conjRestrict L u hu hu' x : L) : X) = u * x * u⁻¹ := rfl

structure Hyp (Mb : Subgroup X) (D : Set X) (k : ℕ) : Prop where
  finite : Finite Mb
  two_le : 2 ≤ k
  sub : D ⊆ Mb
  conj : ∀ m ∈ Mb, ∀ d ∈ D, m * d * m⁻¹ ∈ D
  cls : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ closure D, g * a * g⁻¹ = b
  inv : ∀ d ∈ D, d * d = 1
  three : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)
  psu : Nonempty (closure D ⧸ center (closure D) ≃* PG (k + 2))
  core : ∀ N : Subgroup X, N ≤ Mb → Mb ≤ normalizer (N : Set X) → IsPGroup 2 N → N = ⊥

namespace Hyp

variable {Mb : Subgroup X} {D : Set X} {k : ℕ} (h : Hyp Mb D k)
include h

theorem closure_le : closure D ≤ Mb := (Subgroup.closure_le Mb).2 h.sub

theorem conj_mem_closure {m : X} (hm : m ∈ Mb) {x : X} (hx : x ∈ closure D) :
    m * x * m⁻¹ ∈ closure D := by
  have hle : closure D ≤ (closure D).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro d hd
    exact subset_closure (h.conj m hm d hd)
  exact hle hx

theorem isTClass {t : X} (ht : t ∈ D) :
    IsTClass (Subtype.val ⁻¹' D : Set (closure D)) where
  gen := Subgroup.closure_closure_coe_preimage
  nonempty := ⟨⟨t, subset_closure ht⟩, ht⟩
  cls a ha b hb := by
    obtain ⟨g, hg, hgab⟩ := h.cls _ ha _ hb
    exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩
  conj g a ha := h.conj g (h.closure_le g.2) a ha
  inv a ha := Subtype.ext (h.inv a ha)
  three a ha b hb := by
    rw [← Subgroup.orderOf_coe]
    exact h.three a ha b hb


theorem eq_one_of_centralizes {t : X} (ht : t ∈ D) {U : Subgroup X} (hUM : U ≤ Mb)
    (hU2 : ∀ u ∈ U, u * u = 1) (hUn : ∀ c ∈ Mb, c * t = t * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    {x : X} (hxU : x ∈ U) (hxD : ∀ a ∈ D, x * a = a * x) : x = 1 := by
  have := h.finite
  set C : Subgroup X := Mb ⊓ centralizer D with hC
  have hCM : C ≤ Mb := inf_le_left
  have : Finite C := Finite.of_injective _ (Subgroup.inclusion_injective hCM)
  have hmemC : ∀ y, y ∈ C ↔ y ∈ Mb ∧ ∀ a ∈ D, a * y = y * a := by
    intro y
    rw [hC, mem_inf, mem_centralizer_iff]
  have hle : U ⊓ C ≤ pCoreOf 2 C := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun c hc => ?_) fun y => ⟨1, ?_⟩
    · obtain ⟨hcM, hcD⟩ := (hmemC c).1 hc
      have hct : c * t = t * c := (hcD t ht).symm
      have hcinv : c⁻¹ * t = t * c⁻¹ := by
        calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
          _ = t * c⁻¹ := by group
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨hyU, hyC⟩ := mem_inf.1 hy
        exact mem_inf.2 ⟨hUn c hcM hct y hyU, C.mul_mem (C.mul_mem hc hyC) (C.inv_mem hc)⟩
      · intro hy
        obtain ⟨hyU, hyC⟩ := mem_inf.1 hy
        have h1 := hUn c⁻¹ (Mb.inv_mem hcM) hcinv _ hyU
        have h2 := C.mul_mem (C.mul_mem (C.inv_mem hc) hyC) (C.inv_mem (C.inv_mem hc))
        rw [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h1 h2
        exact mem_inf.2 ⟨h1, h2⟩
    · exact Subtype.ext (by simpa [sq] using hU2 _ (mem_inf.1 y.2).1)
  have hY2 : IsPGroup 2 (pCoreOf 2 C) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := C) 2).map C.subtype
  have hMC : Mb ≤ normalizer (C : Set X) := by
    intro m hm
    rw [mem_normalizer_iff]
    have key : ∀ m ∈ Mb, ∀ y ∈ C, m * y * m⁻¹ ∈ C := by
      intro m hm y hy
      obtain ⟨hyM, hyD⟩ := (hmemC y).1 hy
      refine (hmemC _).2 ⟨mul_mem (mul_mem hm hyM) (inv_mem hm), fun a ha => ?_⟩
      have h1 := hyD _ (h.conj m⁻¹ (inv_mem hm) a ha)
      rw [inv_inv] at h1
      calc a * (m * y * m⁻¹) = m * ((m⁻¹ * a * m) * y) * m⁻¹ := by group
        _ = m * (y * (m⁻¹ * a * m)) * m⁻¹ := by rw [h1]
        _ = m * y * m⁻¹ * a := by group
    intro y
    refine ⟨key m hm y, fun hy => ?_⟩
    have := key m⁻¹ (inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hbot := h.core (pCoreOf 2 C) ((pCoreOf_le 2 C).trans hCM)
    (hMC.trans (normalizer_le_normalizer_pCoreOf 2 C)) hY2
  have hx : x ∈ U ⊓ C := ⟨hxU, (hmemC x).2 ⟨hUM hxU, fun a ha => (hxD a ha).symm⟩⟩
  have := hle hx
  rwa [hbot, mem_bot] at this

theorem one_not_mem {t : X} (ht : t ∈ D) : (1 : X) ∉ D := by
  intro h1
  obtain ⟨ψ⟩ := h.psu
  have hk := h.two_le
  have hD := h.isTClass ht
  obtain ⟨v, hv0, hv, hψ⟩ := hD.mem_DG hk ψ (a := 1) h1
  rw [QuotientGroup.mk_one, map_one] at hψ
  exact tq_ne_one (by omega) hv0 hv hψ

theorem mul_not_mem {t d : X} (ht : t ∈ D) (hd : d ∈ D) (hdt : d * t = t * d) (hne : d ≠ t) :
    t * d ∉ D := by
  intro htd
  obtain ⟨ψ⟩ := h.psu
  have hk := h.two_le
  have hD := h.isTClass ht
  obtain ⟨hZ, hS, -⟩ := pg_facts hk
  set t' : closure D := ⟨t, subset_closure ht⟩
  set d' : closure D := ⟨d, subset_closure hd⟩
  have hne' : ψ (QuotientGroup.mk d') ≠ ψ (QuotientGroup.mk t') := fun h' =>
    hne (congrArg Subtype.val (hD.mk_injOn hk ψ hd ht (ψ.injective h')))
  obtain ⟨cb, hcb, hcbd, hcbt⟩ := AS35J.exists_commute_not_commute_of_pair
    (pair_DG (by omega)) hZ hS (hD.mem_DG hk ψ (a := d') hd) (hD.mem_DG hk ψ (a := t') ht) hne'
  obtain ⟨c', hc', rfl⟩ := hD.exists_eq hk ψ hcb
  have hcd : (c' : X) * d = d * c' :=
    congrArg Subtype.val ((hD.commute_iff hk ψ hc' hd).2 hcbd)
  have hct : (c' : X) * t ≠ t * c' := fun h' =>
    hcbt ((hD.commute_iff hk ψ hc' ht).1 (Subtype.ext h'))
  have h3 : orderOf ((c' : X) * t) = 3 := by
    rcases h.three _ hc' t ht with h1 | h1 | h1
    · exact absurd (AS35J.commute_of_orderOf_mul_le_two (h.inv _ hc') (h.inv t ht)
        (Or.inl h1)) hct
    · exact absurd (AS35J.commute_of_orderOf_mul_le_two (h.inv _ hc') (h.inv t ht)
        (Or.inr h1)) hct
    · exact h1
  have hd1 : d ≠ 1 := fun h1 => h.one_not_mem ht (h1 ▸ hd)
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by rw [sq, h.inv d hd]) hd1
  have hcomm : Commute ((c' : X) * t) d := by
    change (c' : X) * t * d = d * (c' * t)
    rw [mul_assoc, ← hdt, ← mul_assoc, hcd, mul_assoc]
  have h6 : orderOf ((c' : X) * (t * d)) = 6 := by
    rw [← mul_assoc, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, hd2]; norm_num),
      h3, hd2]
  have h7 := h.three _ hc' _ htd
  rw [h6] at h7
  simp at h7

theorem le_zpowers {t : X} (ht : t ∈ D) {U : Subgroup X} (hUM : U ≤ Mb)
    (hU2 : ∀ u ∈ U, u * u = 1) (htU : t ∈ U)
    (hUn : ∀ c ∈ Mb, c * t = t * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) : U ≤ zpowers t := by
  obtain ⟨ψ⟩ := h.psu
  have hk := h.two_le
  have hD := h.isTClass ht
  set t' : closure D := ⟨t, subset_closure ht⟩ with ht'def
  have ht' : t' ∈ (Subtype.val ⁻¹' D : Set (closure D)) := ht
  have htt : t * t = 1 := h.inv t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mul_self (hU2 a ha) (hU2 b hb) (hU2 _ (U.mul_mem ha hb))
  have hcent : ∀ x ∈ U, (∀ a ∈ D, x * a = a * x) → x = 1 := fun x hx hxD =>
    h.eq_one_of_centralizes ht hUM hU2 hUn hx hxD
  have hcenter : ∀ x : closure D, x ∈ center (closure D) → ∀ a ∈ D, (x : X) * a = a * x := by
    intro x hx a ha
    exact congrArg Subtype.val (mem_center_iff.1 hx ⟨a, subset_closure ha⟩).symm
  have hW := hD.mk_eq_one_or_eq_of_normalized hk ψ ht' (W := U.comap (closure D).subtype)
    (fun w hw => Subtype.ext (hU2 _ hw)) htU (fun g hg w hw => by
      have hgt : (g : X) * t = t * g := by
        have h1 := congrArg Subtype.val hg
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
        calc (g : X) * t = (g : X) * t * (g : X)⁻¹ * g := by group
          _ = t * g := by rw [h1]
      exact hUn g (h.closure_le g.2) hgt w hw)
  have hUL : ∀ u ∈ U, u ∈ closure D → u = 1 ∨ u = t := by
    intro u huU hu
    rcases hW ⟨u, hu⟩ huU with h1 | h1
    · left
      have hZ : (⟨u, hu⟩ : closure D) ∈ center (closure D) := by
        rw [← QuotientGroup.eq_one_iff]
        exact ψ.injective (by rw [h1, map_one])
      exact hcent u huU (hcenter _ hZ)
    · right
      have hZ : t'⁻¹ * ⟨u, hu⟩ ∈ center (closure D) := QuotientGroup.eq.1 (ψ.injective h1.symm)
      have h2 := hcent (t⁻¹ * u) (U.mul_mem (U.inv_mem htU) huU) (hcenter _ hZ)
      rw [inv_mul_eq_one] at h2
      exact h2.symm
  have hfix : ∀ u ∈ U, ∀ d ∈ D, d * t = t * d → u * d * u⁻¹ = d := by
    intro u huU d hd hdt
    have hdM := h.sub hd
    have hudD : u * d * u⁻¹ ∈ D := h.conj u (hUM huU) d hd
    have hw : d * u * d⁻¹ * u⁻¹ ∈ U := U.mul_mem (hUn d hdM hdt u huU) (U.inv_mem huU)
    have hwL : d * u * d⁻¹ * u⁻¹ ∈ closure D := by
      rw [show d * u * d⁻¹ * u⁻¹ = d * (u * d * u⁻¹)⁻¹ by group]
      exact mul_mem (subset_closure hd) (inv_mem (subset_closure hudD))
    rcases hUL _ hw hwL with h1 | h1
    · calc u * d * u⁻¹ = (d * u * d⁻¹ * u⁻¹)⁻¹ * d := by group
        _ = d := by rw [h1, inv_one, one_mul]
    · exfalso
      have he : u * d * u⁻¹ = t * d := by
        calc u * d * u⁻¹ = (d * u * d⁻¹ * u⁻¹)⁻¹ * d := by group
          _ = t * d := by rw [h1, htinv]
      by_cases hdt' : d = t
      · subst hdt'
        have := hUcomm u huU d htU
        apply h.one_not_mem hd
        rw [← htt, ← he, this, mul_inv_cancel_right]
        exact hd
      · exact h.mul_not_mem ht hd hdt hdt' (he ▸ hudD)
  intro u huU
  have huM := hUM huU
  have hconjL : ∀ x ∈ closure D, u * x * u⁻¹ ∈ closure D := fun x hx =>
    h.conj_mem_closure huM hx
  have hconjL' : ∀ x ∈ closure D, u⁻¹ * x * u ∈ closure D := fun x hx => by
    simpa using h.conj_mem_closure (inv_mem huM) hx
  set β := conjRestrict (closure D) u hconjL hconjL' with hβ
  have hβD : ∀ a ∈ (Subtype.val ⁻¹' D : Set (closure D)), β a ∈ (Subtype.val ⁻¹' D) :=
    fun a ha => h.conj u huM a ha
  have hβt : β t' = t' := Subtype.ext (by
    rw [conjRestrict_apply, ht'def, hUcomm u huU t htU, mul_inv_cancel_right])
  have hβC : ∀ a ∈ (Subtype.val ⁻¹' D : Set (closure D)), a * t' = t' * a → β a = a :=
    fun a ha hat => Subtype.ext (by
      rw [conjRestrict_apply]
      exact hfix u huU a ha (congrArg Subtype.val hat))
  rcases hD.eq_or_eq_conj_of_fix hk ψ ht' β hβD hβt hβC with h1 | h1
  · have hu1 : u = 1 := hcent u huU fun a ha => by
      have h2 := congrArg Subtype.val (h1 ⟨a, subset_closure ha⟩ ha)
      rw [conjRestrict_apply] at h2
      calc u * a = u * a * u⁻¹ * u := by group
        _ = a * u := by rw [h2]
    rw [hu1]
    exact one_mem _
  · have htu : t * u = 1 := hcent (t * u) (U.mul_mem htU huU) fun a ha => by
      have h2 := congrArg Subtype.val (h1 ⟨a, subset_closure ha⟩ ha)
      rw [conjRestrict_apply] at h2
      simp only [Subgroup.coe_mul] at h2
      calc t * u * a = t * (u * a * u⁻¹) * u := by group
        _ = t * (t * a * t) * u := by rw [h2]
        _ = a * (t * u) := by rw [← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc]
    rw [show u = t⁻¹ by rw [eq_inv_iff_mul_eq_one, mul_comm_of_mul_self (hU2 u huU) htt
      (by rw [show u * t * (u * t) = (u * t) * (u * t) from rfl]; exact hU2 _ (U.mul_mem huU htU)),
      htu]]
    exact inv_mem (mem_zpowers t)

end Hyp

end CFSG.LargeExtraspecial.AS35L

module

public import CFSG.Goldschmidt.Steps.G36Basic
import CFSG.Goldschmidt.Steps.G3b35Setup
import CFSG.Walter.Bender1970.S38.Types
public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.Goldschmidt

namespace G76

open CFSG.Open CFSG.Walter
open scoped Pointwise

section TypeII

variable {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

theorem eq_sylow_of_typeII
    (h : G36Hyp L A₀ T₀) (hII : IsGoldTypeII L) :
    A₀ = (T₀ : Subgroup L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZodd, hL⟩ := hII
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : IsSimpleGroup (L ⧸ Z) := h.quasisimple.2
  have hnab : ∃ a b : L ⧸ Z, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L
      h.quasisimple
  have hB : Bender38Type (L ⧸ Z) :=
    bender38Type_of_isTypeL2_or_isTypeJR hnab (hL.imp (fun h2 => Or.inr h2) id)
  set Vg := (T₀ : Subgroup L) with hVg
  have hTZ : ∀ t ∈ Vg, t ∈ Z → t = 1 := by
    intro t ht htZ
    obtain ⟨k, hk⟩ := h.exists_pow_eq_one ht
    exact eq_one_of_pow_two_pow_eq_one hZodd htZ hk
  have hinj : ∀ s ∈ Vg, ∀ t ∈ Vg, π s = π t → s = t := by
    intro s hs t ht hst
    have hz : s⁻¹ * t ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hst
    have := hTZ _ (Vg.mul_mem (Vg.inv_mem hs) ht) hz
    rw [inv_mul_eq_one] at this
    exact this
  set Tb : Sylow 2 (L ⧸ Z) := T₀.mapSurjective hπs with hTb
  have hTbcoe : (Tb : Subgroup (L ⧸ Z)) = Vg.map π := Sylow.coe_mapSurjective _ _
  have hsq : ∀ t ∈ Vg, t ^ 2 = 1 := by
    intro t ht
    have h1 : π t ^ 2 = 1 := (hB.sylow Tb).1 (π t) (by rw [hTbcoe]; exact ⟨t, ht, rfl⟩)
    apply hTZ _ (Vg.pow_mem ht 2)
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_pow] at h1
    exact h1
  have hconjL : ∀ u ∈ Vg, ∀ v ∈ Vg, u ≠ 1 → v ≠ 1 → ∃ g : L, g * u * g⁻¹ = v := by
    intro u hu v hv hu1 hv1
    have hord : ∀ w ∈ Vg, w ≠ 1 → orderOf (π w) = 2 := by
      intro w hw hw1
      apply orderOf_eq_prime
      · rw [← map_pow, hsq w hw, map_one]
      · intro h1
        exact hw1 (hinj w hw 1 Vg.one_mem (by rw [h1, map_one]))
    obtain ⟨c, hc⟩ := isConj_iff.mp (hB.isConj _ _ (hord u hu hu1) (hord v hv hv1))
    obtain ⟨g, rfl⟩ := hπs c
    refine ⟨g, ?_⟩
    set w := g * u * g⁻¹ with hw
    have hz : w⁻¹ * v ∈ Z := by
      rw [← QuotientGroup.eq]
      rw [← map_mul, ← map_inv, ← map_mul] at hc
      exact hc
    have hw2 : w * w = 1 := by
      rw [← sq, hw, conj_pow, hsq u hu, mul_one, mul_inv_cancel]
    have hv2 : v * v = 1 := by rw [← sq]; exact hsq v hv
    have hzc := Subgroup.mem_center_iff.mp hz
    have hz2 : (w⁻¹ * v) ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      calc (w⁻¹ * v) * (w⁻¹ * v) = ((w⁻¹ * v) * w⁻¹) * v := by group
        _ = (w⁻¹ * (w⁻¹ * v)) * v := by rw [← hzc w⁻¹]
        _ = (w * w)⁻¹ * (v * v) := by group
        _ = 1 := by rw [hw2, hv2, inv_one, one_mul]
    have h1 := eq_one_of_pow_two_pow_eq_one hZodd hz hz2
    rw [inv_mul_eq_one] at h1
    exact h1
  obtain ⟨a₀, ha₀A, ha₀Z⟩ : ∃ a ∈ A₀, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h.not_le_center hcon
  have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀Z (h1 ▸ Z.one_mem)
  apply le_antisymm h.le
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]
    exact A₀.one_mem
  obtain ⟨g, hg⟩ := hconjL a₀ (h.le ha₀A) t ht ha₀1 ht1
  have := h.closed a₀ ha₀A g⁻¹ (by rw [inv_inv, hg]; exact ht)
  rwa [inv_inv, hg] at this

end TypeII

section Inner

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_centralizer_of_isPGroup_two {L A : Subgroup G}
    (hLq : CFSG.Open.IsQuasisimple L) (hAL : A ≤ L) (hAab : IsMulCommutative A)
    (hA2 : IsPGroup 2 A) (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A)
    {w : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (hwA : w ∈ Subgroup.centralizer (A : Set G))
    (hwL : w ∈ Subgroup.normalizer (L : Set G)) :
    w ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hLM : L ≤ M := Subgroup.le_normalizer
  have hAM : A ≤ M := hAL.trans hLM
  set L' := L.subgroupOf M with hL'
  set A' := A.subgroupOf M with hA'
  have : L'.Normal := Subgroup.normal_in_normalizer
  have hLq' : CFSG.Open.IsQuasisimple L' :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hLM) hLq
  have hA'L' : A' ≤ L' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hAL (Subgroup.mem_subgroupOf.mp hx))
  have hA'ab : IsMulCommutative A' :=
    Subgroup.comap_injective_isMulCommutative (H := A) M.subtype_injective
  have hA'2 : IsPGroup 2 A' := hA2.comap_subtype
  have hA'max : ∀ P : Subgroup M, P ≤ L' → IsPGroup 2 P → A' ≤ P → P = A' := by
    intro P hPL hP2 hAP
    have h1 : P.map M.subtype = A := by
      refine hAmax _ ?_ (hP2.map _) ?_
      · rintro _ ⟨p, hp, rfl⟩
        exact hPL hp
      · intro x hx
        exact ⟨⟨x, hAM hx⟩, hAP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    rw [hA', ← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hw' : IsPGroup 2 (Subgroup.zpowers (⟨w, hwL⟩ : M)) := by
    refine (hw.comap_subtype (K := M)).to_le ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers w
  have hwA' : (⟨w, hwL⟩ : M) ∈ Subgroup.centralizer (A' : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwA x (Subgroup.mem_subgroupOf.mp hx))
  have h := G3b.mem_sup_centralizer_of_isPGroup_two hLq' hA'L' hA'ab hA'2 hA'max hw' hwA'
  have h2 := Subgroup.mem_map_of_mem M.subtype h
  rw [Subgroup.map_sup] at h2
  have hle1 : L'.map M.subtype ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hx
  have hle2 : (Subgroup.centralizer (L' : Set M)).map M.subtype ≤
      Subgroup.centralizer (L : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hc ⟨l, hLM hl⟩ (Subgroup.mem_subgroupOf.mpr hl))
  exact sup_le_sup hle1 hle2 h2

theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {x : X} {e : ℕ}
    (hx : x ^ 2 ^ e = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_acts_of_sylow {K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple K)
    (P : Sylow 2 K) (hPab : IsMulCommutative (P : Subgroup K)) {w : G}
    (hw : IsPGroup 2 (Subgroup.zpowers w)) (hwP : ∀ p ∈ (P : Subgroup K), w * (p : G) = p * w)
    (hwK : w ∈ Subgroup.normalizer (K : Set G)) :
    ∃ b ∈ (P : Subgroup K), ∀ k ∈ K, w * k * w⁻¹ = (b : G) * k * (b : G)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := (P : Subgroup K).map K.subtype with hBdef
  have hBK : B ≤ K := Subgroup.map_subtype_le _
  have hBab : IsMulCommutative B := Subgroup.map_isMulCommutative _ _
  have hB2 : IsPGroup 2 B := P.isPGroup'.map _
  have hBmax : ∀ Q : Subgroup G, Q ≤ K → IsPGroup 2 Q → B ≤ Q → Q = B := by
    intro Q hQK hQ2 hBQ
    have hPQ : (P : Subgroup K) ≤ Q.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hBQ ⟨x, hx, rfl⟩)
    have h1 := P.is_maximal' (hQ2.comap_subtype (K := K)) hPQ
    rw [hBdef, ← h1, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hQK]
  have hwB : w ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    exact (hwP p hp).symm
  have hmem := mem_sup_centralizer_of_isPGroup_two hKq hBK hBab hB2 hBmax hw hwB hwK
  have hset : ((K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) =
      (K : Set G) * (Subgroup.centralizer (K : Set G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K _ (Subgroup.centralizer_le_normalizer _)
  have hmem' : w ∈ ((K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := hmem
  rw [hset] at hmem'
  obtain ⟨k, hk, c, hc, hkc⟩ := Set.mem_mul.mp hmem'
  have hcx : ∀ x ∈ K, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hc x hx
  have hkc' : Commute k c := hcx k hk
  have hkP : ∀ p ∈ (P : Subgroup K), k * (p : G) = p * k := by
    intro p hp
    have h1 := hwP p hp
    rw [← hkc] at h1
    have h2 := hcx p p.2
    calc k * (p : G) = k * p * c * c⁻¹ := by group
      _ = k * (c * p) * c⁻¹ := by rw [mul_assoc k, h2]
      _ = p * (k * c) * c⁻¹ := by rw [← mul_assoc, h1]
      _ = p * k := by group
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set k' : K := ⟨k, hk⟩ with hk'
  obtain ⟨e, he⟩ := hw ⟨w, Subgroup.mem_zpowers w⟩
  have hwe : w ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hk2 : k' ^ 2 ^ e ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 : k ^ 2 ^ e * c ^ 2 ^ e = 1 := by rw [← hkc'.mul_pow, hkc, hwe]
    have h2 : k ^ 2 ^ e = (c ^ 2 ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (y : G) * c ^ 2 ^ e = c ^ 2 ^ e * y := by
      have := (Commute.pow_right (hcx y y.2) (2 ^ e))
      exact this
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, hk']
    rw [h2]
    calc (y : G) * (c ^ 2 ^ e)⁻¹ = (c ^ 2 ^ e)⁻¹ * (c ^ 2 ^ e * y) * (c ^ 2 ^ e)⁻¹ := by group
      _ = (c ^ 2 ^ e)⁻¹ * ((y : G) * c ^ 2 ^ e) * (c ^ 2 ^ e)⁻¹ := by rw [h3]
      _ = (c ^ 2 ^ e)⁻¹ * y := by group
  set Pb : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hPb
  have hPbcoe : (Pb : Subgroup (K ⧸ Subgroup.center K)) = (P : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  have hπk2 : π k' ^ 2 ^ e = 1 := by
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk2
  have hzp : IsPGroup 2 (Subgroup.zpowers (π k')) := isPGroup_zpowers_of_pow_eq_one hπk2
  have hzN : Subgroup.zpowers (π k') ≤
      Subgroup.normalizer ((Pb : Subgroup (K ⧸ Subgroup.center K)) : Set _) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff, hPbcoe]
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hkP p hp).symm
  have hsup := Pb.isPGroup'.to_sup_of_normal_left' hzp hzN
  have heq := Pb.is_maximal' hsup le_sup_left
  have hπkP : π k' ∈ (Pb : Subgroup (K ⧸ Subgroup.center K)) := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [hPbcoe] at hπkP
  obtain ⟨b, hb, hbk⟩ := hπkP
  have hz : b⁻¹ * k' ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq]
    exact hbk
  refine ⟨b, hb, fun x hx => ?_⟩
  have hzx : (b : G)⁻¹ * k * x = x * ((b : G)⁻¹ * k) := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
    simpa [hk', mul_assoc] using this.symm
  have hcx' := hcx x hx
  rw [← hkc]
  calc k * c * x * (k * c)⁻¹ = k * (c * x) * c⁻¹ * k⁻¹ := by group
    _ = k * (x * c) * c⁻¹ * k⁻¹ := by rw [hcx']
    _ = (b : G) * ((b : G)⁻¹ * k * x) * k⁻¹ := by group
    _ = (b : G) * (x * ((b : G)⁻¹ * k)) * k⁻¹ := by rw [hzx]
    _ = (b : G) * x * (b : G)⁻¹ := by group

omit [Finite G] in
theorem commutator_acts_trivially {K : Subgroup G} {x y b c : G} (hb : b ∈ K) (hc : c ∈ K)
    (hx : ∀ k ∈ K, x * k * x⁻¹ = b * k * b⁻¹) (hy : ∀ k ∈ K, y * k * y⁻¹ = c * k * c⁻¹)
    (hbc : b * c = c * b) : ∀ k ∈ K, k * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * k := by
  have hx' : ∀ k ∈ K, x⁻¹ * k * x = b⁻¹ * k * b := by
    intro k hk
    have h1 := hx (b⁻¹ * k * b) (K.mul_mem (K.mul_mem (K.inv_mem hb) hk) hb)
    have h2 : b * (b⁻¹ * k * b) * b⁻¹ = k := by group
    rw [h2] at h1
    calc x⁻¹ * k * x = x⁻¹ * (x * (b⁻¹ * k * b) * x⁻¹) * x := by rw [h1]
      _ = b⁻¹ * k * b := by group
  have hy' : ∀ k ∈ K, y⁻¹ * k * y = c⁻¹ * k * c := by
    intro k hk
    have h1 := hy (c⁻¹ * k * c) (K.mul_mem (K.mul_mem (K.inv_mem hc) hk) hc)
    have h2 : c * (c⁻¹ * k * c) * c⁻¹ = k := by group
    rw [h2] at h1
    calc y⁻¹ * k * y = y⁻¹ * (y * (c⁻¹ * k * c) * y⁻¹) * y := by rw [h1]
      _ = c⁻¹ * k * c := by group
  intro k hk
  have hk1 : c⁻¹ * k * c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hc) hk) hc
  have hk2 : b⁻¹ * (c⁻¹ * k * c) * b ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hb) hk1) hb
  have hk3 : c * (b⁻¹ * (c⁻¹ * k * c) * b) * c⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hc hk2) (K.inv_mem hc)
  have hconj : (x * y * x⁻¹ * y⁻¹) * k * (x * y * x⁻¹ * y⁻¹)⁻¹ = k := by
    calc (x * y * x⁻¹ * y⁻¹) * k * (x * y * x⁻¹ * y⁻¹)⁻¹ =
        x * (y * (x⁻¹ * (y⁻¹ * k * y) * x) * y⁻¹) * x⁻¹ := by group
      _ = x * (y * (b⁻¹ * (c⁻¹ * k * c) * b) * y⁻¹) * x⁻¹ := by rw [hy' k hk, hx' _ hk1]
      _ = x * (c * (b⁻¹ * (c⁻¹ * k * c) * b) * c⁻¹) * x⁻¹ := by rw [hy _ hk2]
      _ = b * (c * (b⁻¹ * (c⁻¹ * k * c) * b) * c⁻¹) * b⁻¹ := by rw [hx _ hk3]
      _ = (b * c) * b⁻¹ * c⁻¹ * k * c * b * c⁻¹ * b⁻¹ := by group
      _ = (c * b) * b⁻¹ * c⁻¹ * k * c * b * c⁻¹ * b⁻¹ := by rw [hbc]
      _ = k * (c * b) * c⁻¹ * b⁻¹ := by group
      _ = k * (b * c) * c⁻¹ * b⁻¹ := by rw [hbc]
      _ = k := by group
  calc k * (x * y * x⁻¹ * y⁻¹) =
      ((x * y * x⁻¹ * y⁻¹) * k * (x * y * x⁻¹ * y⁻¹)⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
        rw [hconj]
    _ = (x * y * x⁻¹ * y⁻¹) * k := by group

end Inner

end G76

end CFSG.Goldschmidt

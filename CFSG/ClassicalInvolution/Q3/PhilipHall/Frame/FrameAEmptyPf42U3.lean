module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf41U3

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open

section OddCore

theorem exists_pow_conj_eq_of_odd_orderOf {G : Type*} [Group G] {x u : G} (hx : x * x = 1)
    (hu : u * u = 1) (h : Odd (orderOf (x * u))) :
    ∃ k : ℕ, (x * u) ^ k * x * ((x * u) ^ k)⁻¹ = u := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hc : (x * u) ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one (x * u)
  have hconj : x * (x * u) * x⁻¹ = (x * u)⁻¹ := by
    rw [mul_inv_rev, hui, hxi, ← mul_assoc, hx, one_mul]
  have h2 : x * ((x * u) ^ m)⁻¹ * x⁻¹ = (x * u) ^ m := by
    calc x * ((x * u) ^ m)⁻¹ * x⁻¹ = (x * (x * u) ^ m * x⁻¹)⁻¹ := conj_inv.symm
      _ = ((x * (x * u) * x⁻¹) ^ m)⁻¹ := by rw [conj_pow]
      _ = (x * u) ^ m := by rw [hconj, inv_pow, inv_inv]
  have h3 : (x * u) ^ (m + m) = (x * u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    convert hc using 2
    ring
  calc (x * u) ^ m * x * ((x * u) ^ m)⁻¹
      = (x * u) ^ m * (x * ((x * u) ^ m)⁻¹ * x⁻¹) * x := by group
    _ = (x * u) ^ (m + m) * x := by rw [h2, pow_add]
    _ = u := by rw [h3, mul_inv_rev, hui, hxi, mul_assoc, hx, mul_one]

theorem odd_card_classicalInvolutionOddCore (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (classicalInvolutionOddCore G)) :=
  CFSG.ComponentClassification.OddCore.odd_card G

theorem odd_orderOf_of_mem_classicalInvolutionOddCore {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ classicalInvolutionOddCore G) : Odd (orderOf x) :=
  (odd_card_classicalInvolutionOddCore G).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)

theorem eq_one_of_mem_classicalInvolutionOddCore_of_mul_self {G : Type*} [Group G] [Finite G]
    {x : G} (hx : x ∈ classicalInvolutionOddCore G) (h2 : x * x = 1) : x = 1 := by
  have hodd := odd_orderOf_of_mem_classicalInvolutionOddCore hx
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem map_classicalInvolutionOddCore_equiv {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (e : A ≃* B) :
    (classicalInvolutionOddCore A).map e.toMonoidHom = classicalInvolutionOddCore B := by
  apply le_antisymm
  · exact CFSG.ComponentClassification.OddCore.maximal B _
      ((inferInstance : (classicalInvolutionOddCore A).Normal).map _ e.surjective)
      (by rw [Subgroup.card_map_of_injective e.injective];
          exact odd_card_classicalInvolutionOddCore A)
  · have hle : (classicalInvolutionOddCore B).map e.symm.toMonoidHom ≤
        classicalInvolutionOddCore A :=
      CFSG.ComponentClassification.OddCore.maximal A _
        ((inferInstance : (classicalInvolutionOddCore B).Normal).map _ e.symm.surjective)
        (by rw [Subgroup.card_map_of_injective e.symm.injective];
            exact odd_card_classicalInvolutionOddCore B)
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

end OddCore

section Preimage

variable {G : Type} [Group G]

private abbrev preimg (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) : Subgroup G :=
  N.comap (QuotientGroup.mk' (classicalInvolutionOddCore G))

private theorem mem_preimg {N : Subgroup (G ⧸ classicalInvolutionOddCore G)} {x : G} :
    x ∈ preimg N ↔ (x : G ⧸ classicalInvolutionOddCore G) ∈ N := Iff.rfl

private theorem oddCore_le_preimg (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) :
    classicalInvolutionOddCore G ≤ preimg N := by
  intro x hx
  rw [mem_preimg, (QuotientGroup.eq_one_iff x).mpr hx]
  exact N.one_mem

private theorem index_preimg (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) :
    (preimg N).index = N.index :=
  Subgroup.index_comap_of_surjective N (QuotientGroup.mk'_surjective _)

private theorem mul_self_mem_preimg {N : Subgroup (G ⧸ classicalInvolutionOddCore G)}
    (h : N.index = 2) (g : G) : g * g ∈ preimg N :=
  Subgroup.mul_self_mem_of_index_two (by rw [index_preimg, h]) g

private theorem commutator_le_preimg {N : Subgroup (G ⧸ classicalInvolutionOddCore G)}
    (h : N.index = 2) : commutator G ≤ preimg N := by
  have h2 : (preimg N).index = 2 := by rw [index_preimg, h]
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff]
  tauto

private theorem preimg_le_sup {N : Subgroup (G ⧸ classicalInvolutionOddCore G)}
    (hN : ⁅N, N⁆ = N) : preimg N ≤ commutator G ⊔ classicalInvolutionOddCore G := by
  intro g hg
  have hgN : (g : G ⧸ classicalInvolutionOddCore G) ∈ N := hg
  have hle : N ≤ (commutator G).map (QuotientGroup.mk' (classicalInvolutionOddCore G)) := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    calc N = ⁅N, N⁆ := hN.symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
  obtain ⟨c, hc, hcg⟩ := hle hgN
  have hcg' : c⁻¹ * g ∈ classicalInvolutionOddCore G := QuotientGroup.eq.mp hcg
  have hmem : c * (c⁻¹ * g) ∈ commutator G ⊔ classicalInvolutionOddCore G :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hcg')
  simpa using hmem

private theorem preimg_eq {N : Subgroup (G ⧸ classicalInvolutionOddCore G)} (h : N.index = 2)
    (hN : ⁅N, N⁆ = N) : preimg N = commutator G ⊔ classicalInvolutionOddCore G :=
  le_antisymm (preimg_le_sup hN) (sup_le (commutator_le_preimg h) (oddCore_le_preimg N))

private theorem commutator_subgroup_self_of_simple {M : Type} [Group M] (N : Subgroup M)
    [IsSimpleGroup ↥N] (hnab : ∃ a b : ↥N, a * b ≠ b * a) : ⁅N, N⁆ = N := by
  have hp : commutator ↥N = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1
  have h1 : (commutator ↥N).map N.subtype = ⁅N, N⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h1, hp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem exists_lift_preimg {N : Subgroup (G ⧸ classicalInvolutionOddCore G)} (n : ↥N) :
    ∃ g ∈ preimg N, (g : G ⧸ classicalInvolutionOddCore G) = n := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore G) (n : G ⧸ _)
  refine ⟨g, ?_, hg⟩
  change (g : G ⧸ classicalInvolutionOddCore G) ∈ N
  rw [show (g : G ⧸ classicalInvolutionOddCore G) = n from hg]
  exact n.2

private def preimgHom (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) : ↥(preimg N) →* ↥N :=
  ((QuotientGroup.mk' (classicalInvolutionOddCore G)).comp (preimg N).subtype).codRestrict N
    (fun x => x.2)

private theorem preimgHom_surjective (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) :
    Function.Surjective (preimgHom N) := by
  intro n
  obtain ⟨g, hg, hgn⟩ := exists_lift_preimg n
  exact ⟨⟨g, hg⟩, Subtype.ext hgn⟩

private theorem ker_preimgHom (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) :
    (preimgHom N).ker = (classicalInvolutionOddCore G).subgroupOf (preimg N) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

private theorem image_mul_self {N : Subgroup (G ⧸ classicalInvolutionOddCore G)} {x : G}
    (hx : x ∈ preimg N) (hx2 : x * x = 1) :
    (⟨(x : G ⧸ classicalInvolutionOddCore G), hx⟩ : ↥N) *
      ⟨(x : G ⧸ classicalInvolutionOddCore G), hx⟩ = 1 := by
  apply Subtype.ext
  change (x : G ⧸ classicalInvolutionOddCore G) * (x : G ⧸ classicalInvolutionOddCore G) = 1
  rw [← QuotientGroup.mk_mul, hx2]
  rfl

section Finite

variable [Finite G]

private theorem oddCore_preimg (N : Subgroup (G ⧸ classicalInvolutionOddCore G)) [N.Normal] :
    classicalInvolutionOddCore ↥(preimg N) =
      (classicalInvolutionOddCore G).subgroupOf (preimg N) := by
  haveI : (preimg N).Normal := ‹N.Normal›.comap _
  have h : (classicalInvolutionOddCore ↥(preimg N)).map (preimg N).subtype =
      preimg N ⊓ classicalInvolutionOddCore G :=
    CFSG.ComponentClassification.OddCore.normal_intersection G (preimg N)
  rw [inf_eq_right.mpr (oddCore_le_preimg N)] at h
  calc classicalInvolutionOddCore ↥(preimg N)
      = ((classicalInvolutionOddCore ↥(preimg N)).map (preimg N).subtype).comap
          (preimg N).subtype :=
        (Subgroup.comap_map_eq_self_of_injective (preimg N).subtype_injective _).symm
    _ = (classicalInvolutionOddCore G).subgroupOf (preimg N) := by rw [h]; rfl

private noncomputable def preimgQuotEquiv (N : Subgroup (G ⧸ classicalInvolutionOddCore G))
    [N.Normal] : ↥(preimg N) ⧸ classicalInvolutionOddCore ↥(preimg N) ≃* ↥N :=
  (QuotientGroup.quotientMulEquivOfEq ((oddCore_preimg N).trans (ker_preimgHom N).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (preimgHom N) (preimgHom_surjective N))

private theorem isQuasisimple_preimg_quot (N : Subgroup (G ⧸ classicalInvolutionOddCore G))
    [N.Normal] (hs : IsSimpleGroup ↥N) (hnab : ∃ a b : ↥N, a * b ≠ b * a) :
    CFSG.IsQuasisimple (↥(preimg N) ⧸ classicalInvolutionOddCore ↥(preimg N)) :=
  CFSG.IsQuasisimple.of_mulEquiv (preimgQuotEquiv N)
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1

variable {N : Subgroup (G ⧸ classicalInvolutionOddCore G)}

private theorem image_ne_one {x : G} (hx : x ∈ preimg N) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    (⟨(x : G ⧸ classicalInvolutionOddCore G), hx⟩ : ↥N) ≠ 1 := by
  intro h
  apply hx1
  have h1 : (x : G ⧸ classicalInvolutionOddCore G) = 1 := congrArg Subtype.val h
  exact eq_one_of_mem_classicalInvolutionOddCore_of_mul_self
    ((QuotientGroup.eq_one_iff x).mp h1) hx2

private theorem conj_preimg
    (hconj : ∀ x y : ↥N, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → ∃ h : ↥N, h * x * h⁻¹ = y) :
    ∀ x ∈ preimg N, x * x = 1 → x ≠ 1 → ∀ y ∈ preimg N, y * y = 1 → y ≠ 1 →
      ∃ h ∈ preimg N, h * x * h⁻¹ = y := by
  intro x hx hx2 hx1 y hy hy2 hy1
  obtain ⟨n, hn⟩ := hconj _ _ (image_mul_self hx hx2) (image_ne_one hx hx2 hx1)
    (image_mul_self hy hy2) (image_ne_one hy hy2 hy1)
  obtain ⟨h₀, hh₀, hh₀n⟩ := exists_lift_preimg n
  have hu2 : (h₀ * x * h₀⁻¹) * (h₀ * x * h₀⁻¹) = 1 := by
    calc (h₀ * x * h₀⁻¹) * (h₀ * x * h₀⁻¹) = h₀ * (x * x) * h₀⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have huy : ((h₀ * x * h₀⁻¹ : G) : G ⧸ classicalInvolutionOddCore G) =
      (y : G ⧸ classicalInvolutionOddCore G) := by
    have h1 : ((n * ⟨(x : G ⧸ classicalInvolutionOddCore G), hx⟩ * n⁻¹ : ↥N) :
        G ⧸ classicalInvolutionOddCore G) = (y : G ⧸ classicalInvolutionOddCore G) :=
      congrArg Subtype.val hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hh₀n] at h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact h1
  have hc : (h₀ * x * h₀⁻¹) * y ∈ classicalInvolutionOddCore G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, huy, ← QuotientGroup.mk_mul, hy2]
    rfl
  obtain ⟨k, hk⟩ := exists_pow_conj_eq_of_odd_orderOf hu2 hy2
    (odd_orderOf_of_mem_classicalInvolutionOddCore hc)
  refine ⟨((h₀ * x * h₀⁻¹) * y) ^ k * h₀, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (oddCore_le_preimg N (Subgroup.pow_mem _ hc k)) hh₀
  · calc ((h₀ * x * h₀⁻¹) * y) ^ k * h₀ * x * (((h₀ * x * h₀⁻¹) * y) ^ k * h₀)⁻¹
        = ((h₀ * x * h₀⁻¹) * y) ^ k * (h₀ * x * h₀⁻¹) * (((h₀ * x * h₀⁻¹) * y) ^ k)⁻¹ := by
          group
      _ = y := hk

private theorem sqrt_preimg
    (hsq : ∀ x : ↥N, x * x = 1 → x ≠ 1 → ∃ k : ↥N, k * k = x ∧ k ^ 4 = 1) :
    ∀ x ∈ preimg N, x * x = 1 → x ≠ 1 → ∃ k ∈ preimg N, k * k = x ∧ k ^ 4 = 1 := by
  intro x hx hx2 hx1
  obtain ⟨n, hn2, hn4⟩ := hsq _ (image_mul_self hx hx2) (image_ne_one hx hx2 hx1)
  obtain ⟨k₀, hk₀, hk₀n⟩ := exists_lift_preimg n
  have hw : ((k₀ * k₀ : G) : G ⧸ classicalInvolutionOddCore G) =
      (x : G ⧸ classicalInvolutionOddCore G) := by
    rw [QuotientGroup.mk_mul, hk₀n]
    exact congrArg Subtype.val hn2
  have h4 : k₀ ^ 4 ∈ classicalInvolutionOddCore G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hk₀n]
    have h1 := congrArg Subtype.val hn4
    simpa using h1
  obtain ⟨s, hs_def⟩ : ∃ s, s = orderOf (k₀ ^ 4) := ⟨_, rfl⟩
  have hs : Odd s := hs_def ▸ odd_orderOf_of_mem_classicalInvolutionOddCore h4
  have hk₁ : k₀ ^ s ∈ preimg N := Subgroup.pow_mem _ hk₀ s
  have hk₁4 : (k₀ ^ s) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hs_def]
    exact pow_orderOf_eq_one _
  have hxs : x ^ s = x := by
    obtain ⟨m, hm⟩ := hs
    rw [hm, pow_succ, pow_mul, pow_two, hx2, one_pow, one_mul]
  have hu2 : (k₀ ^ s * k₀ ^ s) * (k₀ ^ s * k₀ ^ s) = 1 := by
    rw [← hk₁4]
    generalize k₀ ^ s = K
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hπu : ((k₀ ^ s * k₀ ^ s : G) : G ⧸ classicalInvolutionOddCore G) =
      (x : G ⧸ classicalInvolutionOddCore G) := by
    rw [← ((Commute.refl k₀).mul_pow s), QuotientGroup.mk_pow, hw, ← QuotientGroup.mk_pow, hxs]
  have hc : x * (k₀ ^ s * k₀ ^ s) ∈ classicalInvolutionOddCore G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hπu, ← QuotientGroup.mk_mul, hx2]
    rfl
  obtain ⟨k, hk⟩ := exists_pow_conj_eq_of_odd_orderOf hx2 hu2
    (odd_orderOf_of_mem_classicalInvolutionOddCore hc)
  have hgO : (x * (k₀ ^ s * k₀ ^ s)) ^ k ∈ classicalInvolutionOddCore G :=
    Subgroup.pow_mem _ hc k
  refine ⟨((x * (k₀ ^ s * k₀ ^ s)) ^ k)⁻¹ * k₀ ^ s * (x * (k₀ ^ s * k₀ ^ s)) ^ k, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem (oddCore_le_preimg N hgO)) hk₁)
      (oddCore_le_preimg N hgO)
  · generalize (x * (k₀ ^ s * k₀ ^ s)) ^ k = g at hk hgO ⊢
    calc g⁻¹ * k₀ ^ s * g * (g⁻¹ * k₀ ^ s * g) = g⁻¹ * (k₀ ^ s * k₀ ^ s) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hk]
      _ = x := by group
  · generalize (x * (k₀ ^ s * k₀ ^ s)) ^ k = g
    rw [show g⁻¹ * k₀ ^ s * g = g⁻¹ * k₀ ^ s * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk₁4]
    group

end Finite

end Preimage

theorem u3LayerFacts_of_equiv {T : Type} [Group T] [Finite T] {H : Subgroup T} {G : Type}
    [Group G] [Finite G] (e : G ≃* ↥H) (Λ : Subgroup G)
    (hΛ : Λ = commutator G ⊔ classicalInvolutionOddCore G)
    (hq : CFSG.IsQuasisimple (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    (hsq : ∀ g : G, g * g ∈ Λ)
    (hconj : ∀ x ∈ Λ, x * x = 1 → x ≠ 1 → ∀ y ∈ Λ, y * y = 1 → y ≠ 1 →
      ∃ h ∈ Λ, h * x * h⁻¹ = y)
    (hsqrt : ∀ x ∈ Λ, x * x = 1 → x ≠ 1 → ∃ k ∈ Λ, k * k = x ∧ k ^ 4 = 1)
    (hmod : ∃ (N : Type) (_ : Group N), CFSG.Blueprint.LieModel N .PSU 3 3 1 ∧
      Nonempty ((↥Λ ⧸ classicalInvolutionOddCore ↥Λ) ≃* N) ∧ 2 * Nat.card N ≤ Nat.card G) :
    U3LayerFacts H := by
  let f : G →* T := H.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.injective
  have hrange : f.range = H := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e g).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩
  have hL : layerU3 H = Λ.map f := by
    have hcomm : (commutator G).map f = ⁅H, H⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
    have hodd : (classicalInvolutionOddCore G).map f =
        (classicalInvolutionOddCore ↥H).map H.subtype := by
      rw [← map_classicalInvolutionOddCore_equiv e, Subgroup.map_map]
    rw [hΛ, Subgroup.map_sup, hcomm, hodd]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (CFSG.IsQuasisimple.congr (QuotientGroup.congr (classicalInvolutionOddCore ↥Λ)
      (classicalInvolutionOddCore ↥(Λ.map f)) (Subgroup.equivMapOfInjective Λ f hf)
      (map_classicalInvolutionOddCore_equiv _))).mp hq
  · intro x hx
    rw [hL]
    obtain ⟨g, rfl⟩ : x ∈ f.range := by rw [hrange]; exact hx
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem f (hsq g)
  · intro x hx hx2 hx1 y hy hy2 hy1
    rw [hL] at hx hy ⊢
    obtain ⟨gx, hgx, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨gy, hgy, rfl⟩ := Subgroup.mem_map.mp hy
    have hgx2 : gx * gx = 1 := hf (by rw [map_mul, map_one]; exact hx2)
    have hgy2 : gy * gy = 1 := hf (by rw [map_mul, map_one]; exact hy2)
    have hgx1 : gx ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hgy1 : gy ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨h, hh, hhxy⟩ := hconj gx hgx hgx2 hgx1 gy hgy hgy2 hgy1
    exact ⟨f h, Subgroup.mem_map_of_mem f hh, by rw [← hhxy, map_mul, map_mul, map_inv]⟩
  · intro x hx hx2 hx1
    rw [hL] at hx ⊢
    obtain ⟨gx, hgx, rfl⟩ := Subgroup.mem_map.mp hx
    have hgx2 : gx * gx = 1 := hf (by rw [map_mul, map_one]; exact hx2)
    have hgx1 : gx ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨k, hk, hkk, hk4⟩ := hsqrt gx hgx hgx2 hgx1
    exact ⟨f k, Subgroup.mem_map_of_mem f hk, by rw [← map_mul, hkk],
      by rw [← map_pow, hk4, map_one]⟩
  · obtain ⟨N, _, hN, ⟨eN⟩, hcard⟩ := hmod
    refine ⟨N, inferInstance, hN, ?_, hcard.trans_eq (Nat.card_congr e.toEquiv)⟩
    rw [hL]
    exact ⟨(QuotientGroup.congr (classicalInvolutionOddCore ↥Λ)
      (classicalInvolutionOddCore ↥(Λ.map f)) (Subgroup.equivMapOfInjective Λ f hf)
      (map_classicalInvolutionOddCore_equiv _)).symm.trans eN⟩

theorem frameC201U3Section_of_model
    (hconj : ∀ (N : Type) [Group N], CFSG.Blueprint.LieModel N .PSU 3 3 1 →
      ∀ x y : N, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → ∃ h : N, h * x * h⁻¹ = y)
    (hsq : ∀ (N : Type) [Group N], CFSG.Blueprint.LieModel N .PSU 3 3 1 →
      ∀ x : N, x * x = 1 → x ≠ 1 → ∃ k : N, k * k = x ∧ k ^ 4 = 1)
    (hsimple : ∀ (N : Type) [Group N], CFSG.Blueprint.LieModel N .PSU 3 3 1 →
      IsSimpleGroup N ∧ ∃ a b : N, a * b ≠ b * a) :
    FrameC201U3Section := by
  intro T _ _ H hrow
  obtain ⟨N, hNn, hidx, hmodel⟩ := hrow
  haveI := hNn
  obtain ⟨hNs, hNab⟩ := hsimple ↥N hmodel
  haveI := hNs
  have hcard : 2 * Nat.card ↥N ≤ Nat.card ↥(⊤ : Subgroup ↥H) := by
    rw [← hidx, Subgroup.index_mul_card]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  exact u3LayerFacts_of_equiv Subgroup.topEquiv (preimg N)
    (preimg_eq hidx (commutator_subgroup_self_of_simple N hNab))
    (isQuasisimple_preimg_quot N hNs hNab) (mul_self_mem_preimg hidx)
    (conj_preimg (hconj ↥N hmodel)) (sqrt_preimg (hsq ↥N hmodel))
    ⟨↥N, inferInstance, hmodel, ⟨preimgQuotEquiv N⟩, hcard⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

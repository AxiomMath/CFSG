module

public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedOrderFourConjugate

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

variable {G : Type u} [Group G]

section Conjugates

theorem centralizer_map_conj (T : Subgroup G) (g : G) :
    Subgroup.centralizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (T : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    MulAut.conj_symm_apply]
  constructor
  · intro h t ht
    have h1 := h (g * t * g⁻¹) ⟨t, ht, rfl⟩
    calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * t := by group
  · rintro h _ ⟨t, ht, rfl⟩
    have h1 := h t ht
    change g * t * g⁻¹ * x = x * (g * t * g⁻¹)
    calc g * t * g⁻¹ * x = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by rw [h1]
      _ = x * (g * t * g⁻¹) := by group

theorem card_normalizerMonoidHom_range_map_conj [Finite G] (T : Subgroup G) (g : G) :
    Nat.card (T.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom.range =
      Nat.card T.normalizerMonoidHom.range := by
  have key : ∀ H : Subgroup G, Nat.card (Subgroup.normalizer (H : Set G)) =
      Nat.card H.normalizerMonoidHom.range * Nat.card (Subgroup.centralizer (H : Set G)) := by
    intro H
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup H.normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Subgroup.normalizerMonoidHom_ker, card_subgroupOf_eq,
      inf_eq_left.mpr (Subgroup.centralizer_le_normalizer _)] at h
    exact h
  have hN : Nat.card (Subgroup.normalizer
      ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.normalizer (T : Set G)) := by
    rw [← Subgroup.map_equiv_normalizer_eq, card_map_conj]
  have hC : Nat.card (Subgroup.centralizer
      ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.centralizer (T : Set G)) := by
    rw [centralizer_map_conj, card_map_conj]
  have h1 := key (T.map (MulAut.conj g).toMonoidHom)
  have h2 := key T
  rw [hN, hC] at h1
  have hpos : 0 < Nat.card (Subgroup.centralizer (T : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)

theorem map_subtype_map_conj (K : Subgroup G) (P : Subgroup K) (a : K) :
    (P.map (MulAut.conj a).toMonoidHom).map K.subtype =
      (P.map K.subtype).map (MulAut.conj (a : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

variable {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)

include hn f in
theorem kleinFour_conj_in_sylow (V W : Subgroup G) (hV : V ≤ S) (hW : W ≤ S) [IsKleinFour V]
    [IsKleinFour W] : ∃ g ∈ (S : Subgroup G), W = V.map (MulAut.conj g).toMonoidHom := by
  have : IsKleinFour (V.subgroupOf S) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hV).symm
  have : IsKleinFour (W.subgroupOf S) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hW).symm
  obtain ⟨g, -, hg⟩ := kleinFour_conj hn f (V.subgroupOf S) (W.subgroupOf S)
  refine ⟨g, g.2, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hW, hg, map_subtype_map_conj,
    Subgroup.map_subgroupOf_eq_of_le hV]

include hn f in
theorem quaternionEight_conj_in_sylow (Q Q' : Subgroup G) (hQ : Q ≤ S) (hQ' : Q' ≤ S)
    (eQ : Nonempty (Q ≃* QuaternionGroup 2)) (eQ' : Nonempty (Q' ≃* QuaternionGroup 2)) :
    ∃ g ∈ (S : Subgroup G), Q' = Q.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, hconj, -⟩ := quaternion_eight_subgroups_aux n hn f rfl rfl rfl rfl
  obtain ⟨e⟩ := eQ
  obtain ⟨e'⟩ := eQ'
  obtain ⟨g, -, hg⟩ := hconj (Q.subgroupOf S) (Q'.subgroupOf S)
    ⟨(Subgroup.subgroupOfEquivOfLe hQ).trans e⟩ ⟨(Subgroup.subgroupOfEquivOfLe hQ').trans e'⟩
  refine ⟨g, g.2, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hQ', hg, map_subtype_map_conj,
    Subgroup.map_subgroupOf_eq_of_le hQ]

end Conjugates

section Elementary

theorem SemidihedralFusionChain.composite_preserves {S : Subgroup G} {k : ℕ}
    (c : SemidihedralFusionChain S k) (Φ : G → Prop)
    (hΦ : ∀ i : Fin k, ∀ y : c.supports i, Φ y → Φ (c.automorphisms i y))
    (x : c.subgroups 0) (hx : Φ x) : Φ (c.composite x) := by
  have key : ∀ i : Fin (k + 1), Φ (c.prefixMap i x) := by
    intro i
    refine Fin.induction ?_ (fun j ih => ?_) i
    · rw [c.prefix_zero]
      exact hx
    · rw [c.prefix_succ, c.step_coe]
      exact hΦ j _ ih
  exact key (Fin.last k)

theorem exists_sylow_actor_of_range_eq (S : Subgroup G) (T : Subgroup G)
    (hAut : T.normalizerMonoidHom.range = ((S ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom)
    (h : G) (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    ∃ s ∈ S, ∀ x ∈ T, h⁻¹ * x * h = s⁻¹ * x * s := by
  have hmem : T.normalizerMonoidHom ⟨h⁻¹, Subgroup.inv_mem _ hh⟩ ∈
      T.normalizerMonoidHom.range := ⟨_, rfl⟩
  rw [hAut] at hmem
  obtain ⟨r', hr', hr'eq⟩ := hmem
  refine ⟨(r' : G)⁻¹, Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp hr').1, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut T => ((φ ⟨x, hx⟩ : T) : G)) hr'eq
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  rw [inv_inv]
  simpa using h1.symm

theorem eq_of_involutions_of_quaternionEight {Q : Subgroup G} (e : Q ≃* QuaternionGroup 2)
    {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1)
    (hb1 : b ≠ 1) : a = b := by
  have key : ∀ (c : G) (hc : c ∈ Q), c ^ 2 = 1 → c ≠ 1 → e ⟨c, hc⟩ = QuaternionGroup.a 2 := by
    intro c hc hc2 hc1
    have h := quaternionGroup_two_sq_eq_one (e ⟨c, hc⟩) (by
      rw [← map_pow, show (⟨c, hc⟩ : Q) ^ 2 = 1 from Subtype.ext (by simpa using hc2), map_one])
    rcases h with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hc1
    · exact h
  exact congrArg Subtype.val (e.injective ((key a ha ha2 ha1).trans (key b hb hb2 hb1).symm))

theorem orderOf_conj_inv (h y : G) : orderOf (h⁻¹ * y * h) = orderOf y := by
  have h1 := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) y
  simpa only [MulAut.conj_apply, inv_inv] using h1

end Elementary

section ChainSteps

theorem chain_step_fixes_central_involution {S : Subgroup G} {k : ℕ}
    (ch : SemidihedralFusionChain S k) {z : G} (hzS : ∀ s ∈ S, s⁻¹ * z * s = z)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hall : ∀ W : Subgroup G, W ≤ S → IsKleinFour W → W.normalizerMonoidHom.range =
      ((S ⊓ Subgroup.normalizer (W : Set G)).subgroupOf
        (Subgroup.normalizer (W : Set G))).map W.normalizerMonoidHom) :
    ∀ i : Fin k, ∀ y : ch.supports i, (y : G) = z → (ch.automorphisms i y : G) = z := by
  intro i y hy
  have hzT : z ∈ ch.supports i := hy ▸ y.2
  obtain ⟨h, hstep, hα⟩ := ch.realized i
  rw [hα y, hy]
  rcases hstep with ⟨-, hhS⟩ | ⟨hK, hhN⟩ | ⟨⟨e⟩, hhN⟩
  · exact hzS h hhS
  · obtain ⟨s, hsS, hs⟩ := exists_sylow_actor_of_range_eq S (ch.supports i)
      (hall _ (ch.support_le i) hK) h hhN
    rw [hs _ hzT]
    exact hzS s hsS
  · have hconjT : h⁻¹ * z * h ∈ ch.supports i := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) z).mp hzT
      simpa using h1
    refine eq_of_involutions_of_quaternionEight e hconjT hzT ?_ ?_ hz2 hz1
    · have h1 : (h⁻¹ * z * h) ^ 2 = h⁻¹ * z ^ 2 * h := by
        rw [sq, sq]
        group
      rw [h1, hz2]
      group
    · intro h1
      apply hz1
      have h2 : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
      rw [h2, h1]
      group

theorem chain_step_preserves_normal {S : Subgroup G} {k : ℕ} (ch : SemidihedralFusionChain S k)
    {A : Subgroup G} (hA : ∀ s ∈ S, ∀ y ∈ A, s⁻¹ * y * s ∈ A)
    (hall : ∀ W : Subgroup G, W ≤ S → Nonempty (W ≃* QuaternionGroup 2) →
      W.normalizerMonoidHom.range = ((S ⊓ Subgroup.normalizer (W : Set G)).subgroupOf
        (Subgroup.normalizer (W : Set G))).map W.normalizerMonoidHom) :
    ∀ i : Fin k, ∀ y : ch.supports i, ((y : G) ∈ A ∧ orderOf (y : G) = 4) →
      ((ch.automorphisms i y : G) ∈ A ∧ orderOf (ch.automorphisms i y : G) = 4) := by
  rintro i y ⟨hyA, hy4⟩
  obtain ⟨h, hstep, hα⟩ := ch.realized i
  rw [hα y, orderOf_conj_inv]
  refine ⟨?_, hy4⟩
  rcases hstep with ⟨-, hhS⟩ | ⟨hK, -⟩ | ⟨hQ', hhN⟩
  · exact hA h hhS _ hyA
  · exfalso
    have hsq : (y ^ 2 : ch.supports i) = 1 := by
      have h1 := Monoid.pow_exponent_eq_one y
      rwa [hK.exponent_two] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hsq)
    rw [hy4] at hdvd
    norm_num at hdvd
  · obtain ⟨s, hsS, hs⟩ := exists_sylow_actor_of_range_eq S (ch.supports i)
      (hall _ (ch.support_le i) hQ') h hhN
    rw [hs _ y.2]
    exact hA s hsS _ hyA

end ChainSteps

section Fullness

variable [Finite G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)

omit [Finite G] in
include hn in
theorem z_conj_sylow (s : G) (hs : s ∈ (S : Subgroup G)) :
    s⁻¹ * ((f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) : S) : G) * s =
      ((f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) : S) : G) := by
  have hhalf : 2 ^ (n - 1) / 2 = 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hz := image_z_mem_center hn f
  rw [hhalf] at hz
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨s, hs⟩)
  simp only [Subgroup.coe_mul] at h
  rw [mul_assoc, ← h]
  group

omit [Finite G] in
include hn in
theorem conj_mem_rotation (s : G) (hs : s ∈ (S : Subgroup G)) (y : G)
    (hy : y ∈ (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).map (S : Subgroup G).subtype) :
    s⁻¹ * y * s ∈ (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).map (S : Subgroup G).subtype := by
  have hnorm : (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).Normal :=
    Subgroup.normal_of_index_eq_two (sd_index_two hn f)
  obtain ⟨a, ha, rfl⟩ := hy
  refine ⟨(⟨s, hs⟩ : S)⁻¹ * a * (⟨s, hs⟩ : S), ?_, rfl⟩
  have h := hnorm.conj_mem a ha (⟨s, hs⟩ : S)⁻¹
  rwa [inv_inv] at h

include hn f in
theorem kleinFour_normalizer_image_eq_top [Group.IsPerfect G] (V : Subgroup G) (hVS : V ≤ S)
    (hV : IsKleinFour V) : V.normalizerMonoidHom.range = ⊤ := by
  by_contra hV₀
  have hall : ∀ W : Subgroup G, W ≤ S → IsKleinFour W → W.normalizerMonoidHom.range =
      (((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G)).subgroupOf
        (Subgroup.normalizer (W : Set G))).map W.normalizerMonoidHom := by
    intro W hWS hW
    obtain ⟨g, -, hg⟩ := kleinFour_conj_in_sylow hn S f V W hVS hWS
    have hcard : Nat.card W.normalizerMonoidHom.range = Nat.card V.normalizerMonoidHom.range := by
      subst hg
      exact card_normalizerMonoidHom_range_map_conj V g
    obtain ⟨-, -, -, -, -, -, -, hK, -⟩ :=
      four_and_quaternion_eight_local_normalizer_quotients n hn S f W hWS (Or.inl hW)
    obtain ⟨-, -, -, halt⟩ := hK hW
    rcases halt with ⟨heq, -⟩ | ⟨htop, -⟩
    · exact heq
    · exfalso
      have h6V := (kleinFour_automorphism_action (V := V)).2.1
      have h6W := (kleinFour_automorphism_action (V := W)).2.1
      have : Finite (MulAut V) := Nat.finite_of_card_ne_zero (by rw [h6V]; norm_num)
      apply hV₀
      rw [← Subgroup.card_eq_iff_eq_top, ← hcard, htop, Subgroup.card_top, h6W, h6V]
  obtain ⟨hz2, -, hzall⟩ := semidihedral_derived_involutions_conjugate n hn S f
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = ((f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) : S) : G) :=
    ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : G, t = ((f (CFSG.Semidihedral.s n) : S) : G) := ⟨_, rfl⟩
  rw [← hzdef] at hz2 hzall
  have hn3 : 3 ≤ n := by omega
  have hzS : z ∈ (S : Subgroup G) := hzdef ▸ Subtype.property _
  have htS : t ∈ (S : Subgroup G) := htdef ▸ Subtype.property _
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, s_eq_element n hn3, image_reflection_orderOf_eq_two_iff,
      ZMod.val_zero]
  obtain ⟨c, hc⟩ := isConj_iff.mp ((hzall Group.IsPerfect.commutator_eq_top t).mp ht2)
  have hcz : c⁻¹ * z * c = t := by
    rw [← hc]
    group
  have hPS : Subgroup.zpowers z ≤ S := Subgroup.zpowers_le.mpr hzS
  have hPg : (Subgroup.zpowers z).map (MulAut.conj c⁻¹).toMonoidHom ≤ S := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have h : (MulAut.conj c⁻¹).toMonoidHom z = t := by
      rw [← hcz]
      simp
    rw [h]
    exact htS
  obtain ⟨k, ch, hfirst, -, hcomp⟩ := semidihedral_fusion_chain n hn S f _ hPS c hPg
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzsq : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2] at h
  have hzcent : ∀ s ∈ (S : Subgroup G), s⁻¹ * z * s = z := fun s hs => by
    rw [hzdef]
    exact z_conj_sylow hn S f s hs
  have hΦ := chain_step_fixes_central_involution ch hzcent hzsq hz1 hall
  have hpres := ch.composite_preserves (fun y => y = z) hΦ
    ⟨z, hfirst ▸ Subgroup.mem_zpowers z⟩ rfl
  rw [hcomp, hcz] at hpres
  apply sd_s_notMem hn f
  have h1 : f (CFSG.Semidihedral.s n) = f (CFSG.Semidihedral.r n) ^ 2 ^ (n - 2) :=
    Subtype.ext (htdef ▸ hzdef ▸ hpres)
  rw [h1]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

include hn f in
theorem quaternionEight_normalizer_image_eq_top [Group.IsPerfect G] (Q : Subgroup G)
    (hQS : Q ≤ S) (hQ : Nonempty (Q ≃* QuaternionGroup 2)) : Q.normalizerMonoidHom.range = ⊤ := by
  by_contra hQ₀
  have hall : ∀ W : Subgroup G, W ≤ S → Nonempty (W ≃* QuaternionGroup 2) →
      W.normalizerMonoidHom.range = (((S : Subgroup G) ⊓
        Subgroup.normalizer (W : Set G)).subgroupOf
          (Subgroup.normalizer (W : Set G))).map W.normalizerMonoidHom := by
    intro W hWS hW
    obtain ⟨g, -, hg⟩ := quaternionEight_conj_in_sylow hn S f Q W hQS hWS hQ hW
    have hcard : Nat.card W.normalizerMonoidHom.range = Nat.card Q.normalizerMonoidHom.range := by
      subst hg
      exact card_normalizerMonoidHom_range_map_conj Q g
    obtain ⟨-, -, -, -, -, -, -, -, hQ8⟩ :=
      four_and_quaternion_eight_local_normalizer_quotients n hn S f W hWS (Or.inr hW)
    obtain ⟨-, -, halt, -⟩ := hQ8 hW
    rcases halt with ⟨heq, -⟩ | ⟨htop, -⟩
    · exact heq
    · exfalso
      have h24Q := (quaternionEight_automorphism_action hQ).2.1
      have h24W := (quaternionEight_automorphism_action hW).2.1
      have : Finite (MulAut Q) := Nat.finite_of_card_ne_zero (by rw [h24Q]; norm_num)
      apply hQ₀
      rw [← Subgroup.card_eq_iff_eq_top, ← hcard, htop, Subgroup.card_top, h24W, h24Q]
  obtain ⟨hv4, -, hvall⟩ := semidihedral_derived_order_four_conjugate n hn S f
  obtain ⟨v, hvdef⟩ : ∃ v : G, v = ((f (CFSG.Semidihedral.r n) ^ (2 ^ (n - 1) / 4) : S) : G) :=
    ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : G,
      x = ((f (CFSG.Semidihedral.r n) * f (CFSG.Semidihedral.s n) : S) : G) := ⟨_, rfl⟩
  rw [← hvdef] at hv4 hvall
  have hn3 : 3 ≤ n := by omega
  have hvA : v ∈ (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).map (S : Subgroup G).subtype :=
    hvdef ▸ ⟨_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _, rfl⟩
  have hxA : x ∉ (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).map (S : Subgroup G).subtype := by
    rintro ⟨a, ha, hax⟩
    have hax' : a = f (CFSG.Semidihedral.r n) * f (CFSG.Semidihedral.s n) :=
      Subtype.ext (hax.trans hxdef)
    apply sd_s_notMem hn f
    have h1 : f (CFSG.Semidihedral.s n) = (f (CFSG.Semidihedral.r n))⁻¹ * a := by
      rw [hax']
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) ha
  have hx4 : orderOf x = 4 := by
    have h := image_zpow_mul_s_eq hn3 f 1
    rw [zpow_one] at h
    have hm1 : modulus n ≠ 1 := by
      rw [modulus]
      exact (Nat.one_lt_two_pow (by omega)).ne'
    rw [hxdef, Subgroup.orderOf_coe, h, equiv_orderOf, outside_order_four_iff, Int.cast_one,
      ZMod.val_one'' hm1]
  obtain ⟨c, hc⟩ := isConj_iff.mp ((hvall Group.IsPerfect.commutator_eq_top x).mp hx4)
  have hcv : c⁻¹ * v * c = x := by
    rw [← hc]
    group
  have hvS : v ∈ (S : Subgroup G) := hvdef ▸ Subtype.property _
  have hxS : x ∈ (S : Subgroup G) := hxdef ▸ Subtype.property _
  have hPS : Subgroup.zpowers v ≤ S := Subgroup.zpowers_le.mpr hvS
  have hPg : (Subgroup.zpowers v).map (MulAut.conj c⁻¹).toMonoidHom ≤ S := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have h : (MulAut.conj c⁻¹).toMonoidHom v = x := by
      rw [← hcv]
      simp
    rw [h]
    exact hxS
  obtain ⟨k, ch, hfirst, -, hcomp⟩ := semidihedral_fusion_chain n hn S f _ hPS c hPg
  have hΦ := chain_step_preserves_normal ch (fun s hs y hy => conj_mem_rotation hn S f s hs y hy)
    hall
  have hpres := ch.composite_preserves
    (fun y => y ∈ (Subgroup.zpowers (f (CFSG.Semidihedral.r n))).map (S : Subgroup G).subtype ∧
      orderOf y = 4) hΦ ⟨v, hfirst ▸ Subgroup.mem_zpowers v⟩ ⟨hvA, hv4⟩
  rw [hcomp, hcv] at hpres
  exact hxA hpres.1

end Fullness

@[expose] def SemidihedralFullFusionStep (S T : Subgroup G) (α : MulAut T) : Prop :=
  (T = S ∧ ∃ s ∈ S, ∀ x : T, (α x : G) = s⁻¹ * (x : G) * s) ∨ IsKleinFour T ∨
    Nonempty (T ≃* QuaternionGroup 2)

structure SemidihedralFullFusionChain (S : Subgroup G) (k : ℕ) where
  subgroups : Fin (k + 1) → Subgroup G
  supports : Fin k → Subgroup G
  automorphisms : (i : Fin k) → MulAut (supports i)
  subgroup_le : ∀ i, subgroups i ≤ S
  support_le : ∀ i, supports i ≤ S
  domain_le : ∀ i, subgroups i.castSucc ≤ supports i
  image_eq : ∀ i,
    (((subgroups i.castSucc).subgroupOf (supports i)).map
      (automorphisms i).toMonoidHom).map (supports i).subtype = subgroups i.succ
  permitted : ∀ i, SemidihedralFullFusionStep S (supports i) (automorphisms i)

namespace SemidihedralFullFusionChain

variable {S : Subgroup G} {k : ℕ} (c : SemidihedralFullFusionChain S k)

@[expose] def step (i : Fin k) : c.subgroups i.castSucc →* c.subgroups i.succ where
  toFun x := ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩, by
    rw [← c.image_eq i]
    exact Subgroup.mem_map.mpr
      ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩,
        Subgroup.mem_map.mpr ⟨⟨x, c.domain_le i x.property⟩, x.property, rfl⟩, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G)) (map_one (c.automorphisms i))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G))
      (map_mul (c.automorphisms i) ⟨x, c.domain_le i x.property⟩ ⟨y, c.domain_le i y.property⟩)

@[expose] def prefixMap : (i : Fin (k + 1)) → c.subgroups 0 →* c.subgroups i :=
  Fin.induction (MonoidHom.id _) (fun i f => (c.step i).comp f)

@[expose] def composite : c.subgroups 0 →* c.subgroups (Fin.last k) :=
  c.prefixMap (Fin.last k)

@[expose] def toFusionChain (hreal : ∀ i, ∃ h : G, SemidihedralFusionStep S (c.supports i) h ∧
    ∀ x : c.supports i, (c.automorphisms i x : G) = h⁻¹ * (x : G) * h) :
    SemidihedralFusionChain S k where
  subgroups := c.subgroups
  supports := c.supports
  automorphisms := c.automorphisms
  subgroup_le := c.subgroup_le
  support_le := c.support_le
  domain_le := c.domain_le
  image_eq := c.image_eq
  realized := hreal

theorem toFusionChain_composite (hreal : ∀ i, ∃ h : G,
    SemidihedralFusionStep S (c.supports i) h ∧
      ∀ x : c.supports i, (c.automorphisms i x : G) = h⁻¹ * (x : G) * h) (x : c.subgroups 0) :
    ((c.toFusionChain hreal).composite x : G) = c.composite x := rfl

end SemidihedralFullFusionChain

@[expose] def SemidihedralFusionChain.toFullFusionChain {S : Subgroup G} {k : ℕ}
    (c : SemidihedralFusionChain S k) : SemidihedralFullFusionChain S k where
  subgroups := c.subgroups
  supports := c.supports
  automorphisms := c.automorphisms
  subgroup_le := c.subgroup_le
  support_le := c.support_le
  domain_le := c.domain_le
  image_eq := c.image_eq
  permitted := fun i => by
    obtain ⟨h, hs, hα⟩ := c.realized i
    rcases hs with ⟨hT, hh⟩ | ⟨hK, -⟩ | ⟨hQ, -⟩
    · exact Or.inl ⟨hT, h, hh, hα⟩
    · exact Or.inr (Or.inl hK)
    · exact Or.inr (Or.inr hQ)

theorem SemidihedralFusionChain.toFullFusionChain_composite {S : Subgroup G} {k : ℕ}
    (c : SemidihedralFusionChain S k) (x : c.subgroups 0) :
    (c.toFullFusionChain.composite x : G) = c.composite x := rfl

end CFSG.Semidihedral.Local

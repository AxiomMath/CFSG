module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

section Lift

variable {K : Type*} [Group K] [Finite K]

theorem exists_isPGroup_lift (N : Subgroup K) [N.Normal] (hN : Odd (Nat.card N))
    {C : Subgroup K} {V : Subgroup (K ⧸ N)} (hV : IsPGroup 2 V)
    (hVC : V ≤ C.map (QuotientGroup.mk' N)) :
    ∃ W : Subgroup K, W ≤ C ∧ IsPGroup 2 W ∧ Nat.card W = Nat.card V ∧
      W.map (QuotientGroup.mk' N) = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := QuotientGroup.mk' N
  set Y := C ⊓ V.comap f
  have hYmap : Y.map f = V := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro v hv
      obtain ⟨c, hc, rfl⟩ := hVC hv
      exact ⟨c, ⟨hc, hv⟩, rfl⟩
  have hrel : ∀ X : Subgroup K, N.relIndex X = Nat.card (X.map f) := fun X => by
    have h := Subgroup.relIndex_ker X f
    rwa [QuotientGroup.ker_mk'] at h
  have hcard : Nat.card Y = Nat.card V * Nat.card (N ⊓ Y : Subgroup K) := by
    have h1 := Subgroup.relIndex_mul_card N Y
    rw [hrel, hYmap] at h1
    exact h1.symm
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  obtain ⟨W0, hW0⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) 2 (n := n)
    (by rw [hcard, hn]; exact Dvd.intro _ rfl)
  set W := W0.map Y.subtype
  have hWcard : Nat.card W = 2 ^ n := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hW0]
  have hWY : W ≤ Y := Subgroup.map_subtype_le W0
  have hW2 : IsPGroup 2 W := IsPGroup.of_card hWcard
  have hdisj : N ⊓ W = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hWcard]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_left.mpr hN).symm
  have hWmap : Nat.card (W.map f) = Nat.card W := by
    have h1 := Subgroup.relIndex_mul_card N W
    rw [hrel, hdisj, Subgroup.card_bot, mul_one] at h1
    exact h1
  refine ⟨W, hWY.trans inf_le_left, hW2, by rw [hWcard, hn], ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · exact (Subgroup.map_mono hWY).trans hYmap.le
  · rw [hWmap, hWcard, hn]

theorem exists_fourGroup_lift (N : Subgroup K) [N.Normal] (hN : Odd (Nat.card N))
    {C : Subgroup K} {V : Subgroup (K ⧸ N)} (hV : AschbacherKnownGroup.IsFourGroup V)
    (hVC : V ≤ C.map (QuotientGroup.mk' N)) :
    ∃ W : Subgroup K, W ≤ C ∧ AschbacherKnownGroup.IsFourGroup W ∧
      W.map (QuotientGroup.mk' N) = V := by
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.2]; norm_num)
  obtain ⟨W, hWC, hW2, hWcard, hWV⟩ := exists_isPGroup_lift N hN hV2 hVC
  have hinj := fun {u v : K} (hu : u ∈ W) (hv : v ∈ W) =>
    AschbacherToolkit.quotient_injective_on_of_isPGroup N hN hW2 hu hv
  have hVc := hV.1.1
  refine ⟨W, hWC, ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩, hWV⟩
  · apply hinj (W.mul_mem a.2 b.2) (W.mul_mem b.2 a.2)
    have ha : QuotientGroup.mk' N (a : K) ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ a.2
    have hb : QuotientGroup.mk' N (b : K) ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ b.2
    have := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : V) ⟨_, hb⟩)
    simpa only [map_mul, Subgroup.coe_mul] using this
  · apply hinj (W.pow_mem hx 2) W.one_mem
    have hxV : QuotientGroup.mk' N x ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ hx
    rw [map_pow, hV.1.2 _ hxV, map_one]
  · rw [hWcard]
    exact hV.2

end Lift

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem quotientEmbedding_onQuotient (h : Subgroup.normalizer (D : Set G))
    (q : D ⧸ aschbacherThm5OddCore D) :
    quotientEmbedding D (onQuotient D h q) =
      toBar D h * quotientEmbedding D q * (toBar D h)⁻¹ := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
  rw [onQuotient_mk, quotientEmbedding_mk, quotientEmbedding_mk]
  change toBar D (Subgroup.inclusion Subgroup.le_normalizer (onD D h d)) =
    toBar D h * toBar D (Subgroup.inclusion Subgroup.le_normalizer d) * (toBar D h)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

omit [Finite G] in
theorem onQuotient_involutive {h : Subgroup.normalizer (D : Set G)} (hh : (h : G) ^ 2 = 1)
    (q : D ⧸ aschbacherThm5OddCore D) : onQuotient D h (onQuotient D h q) = q := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
  rw [onQuotient_mk, onQuotient_mk]
  congr 1
  apply Subtype.ext
  rw [onD_apply, onD_apply]
  have hinv : (h : G)⁻¹ = h := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hh]
  rw [hinv]
  calc (h : G) * (h * d * h) * h = (h : G) ^ 2 * d * (h : G) ^ 2 := by
        simp only [pow_two, mul_assoc]
    _ = d := by rw [hh, one_mul, mul_one]

omit [Finite G] in
theorem map_onQuotient_factor (h : Subgroup.normalizer (D : Set G)) {i j : Fin r}
    (hij : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj (h : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar j)) :
    (Abar i).map (onQuotient D h).toMonoidHom = Abar j := by
  apply preimage_injective D
  rw [← preimage_conjugate, hij]

omit [Finite G] in
theorem centralizes_iff_mem_centralizer_quotient (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D))
    (d : D) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Ā) d.val ↔
      QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈
        Subgroup.centralizer (Ā : Set (D ⧸ aschbacherThm5OddCore D)) := by
  rw [centralizes_iff_quotient_commutes, Subgroup.mem_centralizer_iff]
  exact forall₂_congr fun a _ => eq_comm

omit [Finite G] in
theorem quotientEmbedding_mem_centralizer {Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)}
    {v : D ⧸ aschbacherThm5OddCore D}
    (hv : v ∈ Subgroup.centralizer (Ā : Set (D ⧸ aschbacherThm5OddCore D))) :
    quotientEmbedding D v ∈
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D Ā) : Set (Bar D)) := by
  rw [← map_quotientEmbedding, Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hv) a ha]

theorem no_four_group_quotient (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {V : Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hV : AschbacherKnownGroup.IsFourGroup V)
    (hfix : ∀ v ∈ V, onQuotient D ⟨t, h.mem⟩ v = v)
    (hgood : ∀ v ∈ V, v ≠ 1 → ∃ k : Fin r,
      v ∈ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D))) : False := by
  set H := Subgroup.normalizer (D : Set G)
  set t' : H := ⟨t, h.mem⟩
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.orderOf_eq
  set ι := quotientEmbedding D
  have hι := quotientEmbedding_injective D
  have hVc : V.map ι ≤ (Subgroup.centralizer ({t'} : Set H)).map (toBar D) := by
    have hcent := AschbacherToolkit.centralizer_quotient_odd (coreIn D) (coreIn_odd D) t' ht'
    change V.map ι ≤ (Subgroup.centralizer ({t'} : Set H)).map (QuotientGroup.mk' (coreIn D))
    rw [← hcent]
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj := quotientEmbedding_onQuotient t' v
    rw [hfix v hv] at hconj
    change ι v * toBar D t' = toBar D t' * ι v
    calc ι v * toBar D t' = toBar D t' * ι v * (toBar D t')⁻¹ * toBar D t' := by
          rw [← hconj]
      _ = toBar D t' * ι v := by group
  obtain ⟨W, hWC, hW4, hWV⟩ := exists_fourGroup_lift (coreIn D) (coreIn_odd D)
    (isFourGroup_map hV ι hι) hVc
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW4.2]; norm_num)
  apply no_four_group_conjugate hin hC (h.not_mem hC.hyp) (U := W.map H.subtype)
  · rintro _ ⟨w, hw, rfl⟩
    apply h.centralizer_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwt := Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
    exact congrArg Subtype.val hwt
  · exact isFourGroup_map hW4 _ H.subtype_injective
  · rintro _ ⟨w, hw, rfl⟩ hne
    have hw1 : w ≠ 1 := fun hw1 => hne (by rw [hw1, map_one])
    have hwV : toBar D w ∈ V.map ι := hWV ▸ Subgroup.mem_map_of_mem _ hw
    obtain ⟨v, hv, hvw⟩ := hwV
    have hv1 : v ≠ 1 := by
      rintro rfl
      apply hw1
      apply AschbacherToolkit.quotient_injective_on_of_isPGroup (coreIn D) (coreIn_odd D) hW2
        hw W.one_mem
      change toBar D w = toBar D 1
      rw [← hvw, map_one, map_one]
    obtain ⟨k, hk⟩ := hgood v hv hv1
    have hcent : toBar D w ∈
        Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar k)) : Set (Bar D)) := by
      rw [← hvw]
      exact quotientEmbedding_mem_centralizer hk
    have hcz := (centralizes_iff_mem_centralizer D (aschbacherThm5Preimage D (Abar k))
      (preimage_le D _) w).mpr hcent
    exact centralizer_le_of_centralizes hC k (two_power_of_sq (by
      have := hW4.1.2 w hw
      change (w : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one])) hne hcz

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5

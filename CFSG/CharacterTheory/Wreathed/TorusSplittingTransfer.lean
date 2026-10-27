module

public import CFSG.CharacterTheory.Wreathed.DerivedCentralizerBoundaryInvariance
public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLift
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.Wreathed.TorusSplitting

variable {G : Type*} [Group G]

theorem map_subgroupOf_eq {H K : Subgroup G} (h : H ≤ K) : (H.subgroupOf K).map K.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h]

theorem mem_iff_of_map_eq {K : Subgroup G} {H' : Subgroup K} {H : Subgroup G}
    (h : H'.map K.subtype = H) (x : K) : x ∈ H' ↔ (x : G) ∈ H := by
  rw [← h]
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm

theorem map_sup_subgroupOf {K W A : Subgroup G} (hW : W ≤ K) (hA : A ≤ K) :
    (W.subgroupOf K ⊔ A.subgroupOf K).map K.subtype = W ⊔ A := by
  rw [Subgroup.map_sup, map_subgroupOf_eq hW, map_subgroupOf_eq hA]

theorem map_commutator_subgroupOf {K H : Subgroup G} (hH : H ≤ K) :
    ⁅H.subgroupOf K, H.subgroupOf K⁆.map K.subtype = ⁅H, H⁆ := by
  rw [Subgroup.map_commutator, map_subgroupOf_eq hH]

theorem closure_eq_top_of_map {K C : Subgroup G} (hCK : C ≤ K) (w a : K)
    (hgen : Subgroup.closure ((C : Set G) ∪ {(w : G), (a : G)}) = K) :
    Subgroup.closure (((C.subgroupOf K : Subgroup K) : Set K) ∪ {w, a}) = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have himg : K.subtype '' (((C.subgroupOf K : Subgroup K) : Set K) ∪ {w, a}) =
      (C : Set G) ∪ {(w : G), (a : G)} := by
    ext x
    simp only [Set.mem_image, Set.mem_union, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Set.mem_insert_iff, Set.mem_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy | rfl | rfl, rfl⟩
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (hx | rfl | rfl)
      · exact ⟨⟨x, hCK hx⟩, Or.inl hx, rfl⟩
      · exact ⟨w, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨a, Or.inr (Or.inr rfl), rfl⟩
  rw [himg, hgen]

theorem boundary_invariance_in_subgroup [Finite G] (Mg : Subgroup G)
    (C K : Subgroup G) (hCM : C ≤ Mg) (hKC : K ≤ C)
    (hCn : ∀ g ∈ Mg, ∀ c ∈ C, g * c * g⁻¹ ∈ C) (hKn : ∀ g ∈ Mg, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKodd : Odd (Nat.card K)) (w a : G) (hwM : w ∈ Mg) (haM : a ∈ Mg)
    (hw : w * w = 1) (ha : Odd (orderOf a)) (hwa : w⁻¹ * a * w = a⁻¹)
    (hgen : Subgroup.closure ((C : Set G) ∪ {w, a}) = Mg)
    (A W : Subgroup G) (hAK : A ≤ K) (hWK : W ≤ K)
    (hAn : ∀ k ∈ K, ∀ x ∈ A, k * x * k⁻¹ ∈ A) (hWn : ∀ k ∈ K, ∀ x ∈ W, k * x * k⁻¹ ∈ W)
    (hWcyc : IsCyclic W) (hWA : W ⊓ A = ⊥) (hWAc : ∀ x ∈ W, ∀ y ∈ A, x * y = y * x)
    (hBC : ∀ c ∈ C, ∀ b ∈ W ⊔ A, c * b * c⁻¹ ∈ W ⊔ A)
    (hKB : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ W ⊔ A)
    (hCKB : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ W ⊔ A)
    (hwA : ∀ x ∈ A, w * x * w⁻¹ ∈ A) (hwW : ∀ x ∈ W, w * x * w⁻¹ ∈ W)
    (hwAc : ∀ x ∈ A, w * x = x * w) (hwKB : ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ W ⊔ A)
    (hcent : ∀ k ∈ K, (∀ x ∈ ⁅K, K⁆, k * x * k⁻¹ * x⁻¹ ∈ A) ↔ k ∈ W ⊔ A) :
    (∀ g ∈ Mg, ∀ b ∈ W ⊔ A, g * b * g⁻¹ ∈ W ⊔ A) ∧
      ∀ g ∈ Mg, ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ W ⊔ A := by
  have hKM : K ≤ Mg := hKC.trans hCM
  have hAM : A ≤ Mg := hAK.trans hKM
  have hWM : W ≤ Mg := hWK.trans hKM
  have : (C.subgroupOf Mg).Normal := ⟨fun c hc g => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact hCn g g.2 c hc⟩
  have : (K.subgroupOf Mg).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g g.2 k hk⟩
  have : IsCyclic (W.subgroupOf Mg) := (Subgroup.subgroupOfEquivOfLe hWM).isCyclic.mpr hWcyc
  have hB : ∀ x : Mg, x ∈ W.subgroupOf Mg ⊔ A.subgroupOf Mg ↔ (x : G) ∈ W ⊔ A :=
    mem_iff_of_map_eq (map_sup_subgroupOf hWM hAM)
  have hK' : ∀ x : Mg, x ∈ ⁅K.subgroupOf Mg, K.subgroupOf Mg⁆ ↔ (x : G) ∈ ⁅K, K⁆ :=
    mem_iff_of_map_eq (map_commutator_subgroupOf hKM)
  have hK'K : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy =>
    K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hK'M : ⁅K, K⁆ ≤ Mg := hK'K.trans hKM
  have hcardK : Nat.card (K.subgroupOf Mg) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hwMt : (⟨w, hwM⟩ : Mg) * ⟨w, hwM⟩ = 1 := Subtype.ext hw
  have haMt : Odd (orderOf (⟨a, haM⟩ : Mg)) := by rw [← Subgroup.orderOf_coe]; exact ha
  have hwaMt : (⟨w, hwM⟩ : Mg)⁻¹ * ⟨a, haM⟩ * ⟨w, hwM⟩ = (⟨a, haM⟩ : Mg)⁻¹ := Subtype.ext hwa
  obtain ⟨-, -, -, -, -, hBn, htriv, -⟩ :=
    characteristic_derived_centralizer_forces_boundary_invariance (C.subgroupOf Mg)
      (K.subgroupOf Mg) (fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hKC hx) (by rw [hcardK]; exact hKodd)
      ⟨w, hwM⟩ ⟨a, haM⟩ hwMt haMt hwaMt (closure_eq_top_of_map hCM ⟨w, hwM⟩ ⟨a, haM⟩ hgen)
      (A.subgroupOf Mg) (W.subgroupOf Mg)
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hAK hx)
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hWK hx)
      (fun k hk x hx => by
        rw [Subgroup.mem_subgroupOf] at hk hx ⊢
        exact hAn k hk x hx)
      (fun k hk x hx => by
        rw [Subgroup.mem_subgroupOf] at hk hx ⊢
        exact hWn k hk x hx)
      (by
        rw [eq_bot_iff]
        intro x hx
        have h : (x : G) ∈ W ⊓ A := ⟨Subgroup.mem_subgroupOf.mp hx.1,
          Subgroup.mem_subgroupOf.mp hx.2⟩
        rw [hWA, Subgroup.mem_bot] at h
        exact Subgroup.mem_bot.mpr (Subtype.ext h))
      (fun x hx y hy => Subtype.ext (hWAc x (Subgroup.mem_subgroupOf.mp hx) y
        (Subgroup.mem_subgroupOf.mp hy)))
      (fun c hc b hb => (hB _).mpr (hBC c (Subgroup.mem_subgroupOf.mp hc) b ((hB b).mp hb)))
      (fun x hx y hy => (hB _).mpr (hKB x (Subgroup.mem_subgroupOf.mp hx) y
        (Subgroup.mem_subgroupOf.mp hy)))
      (fun c hc k hk => (hB _).mpr (hCKB c (Subgroup.mem_subgroupOf.mp hc) k
        (Subgroup.mem_subgroupOf.mp hk)))
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hwA x hx)
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hwW x hx)
      (fun x hx => Subtype.ext (hwAc x (Subgroup.mem_subgroupOf.mp hx)))
      (fun k hk => (hB _).mpr (hwKB k (Subgroup.mem_subgroupOf.mp hk)))
      (fun k hk => by
        rw [hB]
        refine Iff.trans ?_ (hcent k (Subgroup.mem_subgroupOf.mp hk))
        constructor
        · intro h x hx
          have := h ⟨x, hK'M hx⟩ ((hK' _).mpr hx)
          exact Subgroup.mem_subgroupOf.mp this
        · intro h x hx
          exact Subgroup.mem_subgroupOf.mpr (h x ((hK' x).mp hx)))
  refine ⟨fun g hg b hb => ?_, fun g hg k hk => ?_⟩
  · have h := hBn.conj_mem ⟨b, (sup_le hWM hAM) hb⟩ ((hB _).mpr hb) ⟨g, hg⟩
    exact (hB _).mp h
  · exact (hB _).mp (htriv ⟨g, hg⟩ ⟨k, hKM hk⟩ (Subgroup.mem_subgroupOf.mpr hk))

theorem ker_conjNormal_normalizer (V : Subgroup G) :
    (MulAut.conjNormal : Subgroup.normalizer (V : Set G) →*
        MulAut (V.subgroupOf (Subgroup.normalizer (V : Set G)))).ker =
      (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := congrArg (fun φ : MulAut (V.subgroupOf (Subgroup.normalizer (V : Set G))) =>
      ((φ ⟨⟨v, Subgroup.le_normalizer hv⟩, Subgroup.mem_subgroupOf.mpr hv⟩ :
        V.subgroupOf (Subgroup.normalizer (V : Set G))) : G)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    have h2 : (x : G) * v * (x : G)⁻¹ = v := h1
    calc v * (x : G) = (x : G) * v * (x : G)⁻¹ * (x : G) := by rw [h2]
      _ = (x : G) * v := by group
  · intro h
    ext ⟨⟨v, hvM⟩, hv⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    have hv' : v ∈ V := Subgroup.mem_subgroupOf.mp hv
    change (x : G) * v * (x : G)⁻¹ = v
    rw [← h v hv', mul_inv_cancel_right]

theorem conjNormal_surjective_of_card [Finite G] (V : Subgroup G) (hV4 : IsKleinFour V)
    (hsix : Nat.card (Subgroup.normalizer (V : Set G) ⧸
      (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) = 6) :
    Function.Surjective (MulAut.conjNormal : Subgroup.normalizer (V : Set G) →*
      MulAut (V.subgroupOf (Subgroup.normalizer (V : Set G)))) := by
  have hle : V ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer
  have hV4' : IsKleinFour (V.subgroupOf (Subgroup.normalizer (V : Set G))) :=
    ⟨by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]; exact hV4.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)]
         exact hV4.exponent_two⟩
  have hAut := CFSG.GorensteinWalter.kleinFourAut_card
    (V.subgroupOf (Subgroup.normalizer (V : Set G)))
  have hrange : Nat.card (MulAut.conjNormal : Subgroup.normalizer (V : Set G) →*
      MulAut (V.subgroupOf (Subgroup.normalizer (V : Set G)))).range = 6 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      ker_conjNormal_normalizer]
    exact hsix
  have : Finite (MulAut (V.subgroupOf (Subgroup.normalizer (V : Set G)))) :=
    Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have htop := Subgroup.eq_top_of_card_eq _ (hrange.trans hAut.symm)
  exact MonoidHom.range_eq_top.mp htop

theorem mem_centralizer_subgroupOf_iff (V : Subgroup G) (x : Subgroup.normalizer (V : Set G)) :
    x ∈ Subgroup.centralizer ((V.subgroupOf (Subgroup.normalizer (V : Set G)) :
        Subgroup (Subgroup.normalizer (V : Set G))) : Set (Subgroup.normalizer (V : Set G))) ↔
      (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v, Subgroup.le_normalizer hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
  · intro h v hv
    exact Subtype.ext (h v (Subgroup.mem_subgroupOf.mp hv))

theorem cycling_lift_in_normalizer [Finite G] (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : m = 2 ^ n)
    (s t : G) (hs : orderOf s = m) (ht : orderOf t = m) (hst : Commute s t)
    (hdisj : Disjoint (Subgroup.zpowers s) (Subgroup.zpowers t))
    (U V K : Subgroup G) (hU : U = Subgroup.zpowers s ⊔ Subgroup.zpowers t)
    (hV : V = Subgroup.closure {s ^ (m / 2), t ^ (m / 2)}) (hV4 : IsKleinFour V)
    (hKn : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hK : Odd (Nat.card K)) (hCV : Subgroup.centralizer (V : Set G) = K ⊔ U)
    (hsix : Nat.card (Subgroup.normalizer (V : Set G) ⧸
      (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) = 6)
    (w : G) (hwN : w ∈ Subgroup.normalizer (V : Set G)) (hw : orderOf w = 2)
    (hws : w⁻¹ * s * w = t) (hwt : w⁻¹ * t * w = s) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ a ∈ Subgroup.normalizer (V : Set G), orderOf a = 3 ^ b ∧
      (∀ v ∈ V, v ≠ 1 → a * v * a⁻¹ ≠ v) ∧ (∀ v ∈ V, a ^ 3 * v * (a ^ 3)⁻¹ = v) ∧
      w⁻¹ * a * w = a⁻¹ ∧
      Subgroup.closure ((Subgroup.centralizer (V : Set G) : Set G) ∪ {w, a}) =
        Subgroup.normalizer (V : Set G) := by
  set Mg := Subgroup.normalizer (V : Set G) with hMg
  have hCM : Subgroup.centralizer (V : Set G) ≤ Mg := Subgroup.centralizer_le_normalizer _
  have hUC : U ≤ Subgroup.centralizer (V : Set G) := hCV ▸ le_sup_right
  have hKC : K ≤ Subgroup.centralizer (V : Set G) := hCV ▸ le_sup_left
  have hsU : s ∈ U := hU ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have htU : t ∈ U := hU ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hsM : s ∈ Mg := hCM (hUC hsU)
  have htM : t ∈ Mg := hCM (hUC htU)
  have hVM : V ≤ Mg := Subgroup.le_normalizer
  have hUM : U ≤ Mg := hUC.trans hCM
  have hKM : K ≤ Mg := hKC.trans hCM
  have : (K.subgroupOf Mg).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g g.2 k hk⟩
  let s' : Mg := ⟨s, hsM⟩
  let t' : Mg := ⟨t, htM⟩
  have hzs : (Subgroup.zpowers s').map Mg.subtype = Subgroup.zpowers s := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hzt : (Subgroup.zpowers t').map Mg.subtype = Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hU' : U.subgroupOf Mg = Subgroup.zpowers s' ⊔ Subgroup.zpowers t' := by
    apply Subgroup.map_injective Mg.subtype_injective
    rw [map_subgroupOf_eq hUM, Subgroup.map_sup, hzs, hzt, hU]
  have hV' : V.subgroupOf Mg = Subgroup.closure {s' ^ (m / 2), t' ^ (m / 2)} := by
    apply Subgroup.map_injective Mg.subtype_injective
    rw [map_subgroupOf_eq hVM, MonoidHom.map_closure, hV]
    congr 1
    ext x
    simp [s', t', Set.image_insert_eq]
  have hCV' : Subgroup.centralizer ((V.subgroupOf Mg : Subgroup Mg) : Set Mg) =
      K.subgroupOf Mg ⊔ U.subgroupOf Mg := by
    apply Subgroup.map_injective Mg.subtype_injective
    rw [map_sup_subgroupOf hKM hUM, ← hCV]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_centralizer_subgroupOf_iff V y).mp hy
    · intro hx
      exact ⟨⟨x, hCM hx⟩, (mem_centralizer_subgroupOf_iff V ⟨x, hCM hx⟩).mpr hx, rfl⟩
  have hdisj' : Disjoint (Subgroup.zpowers s') (Subgroup.zpowers t') := by
    rw [Subgroup.disjoint_def] at hdisj ⊢
    intro x hx hy
    have hx' : (x : G) ∈ Subgroup.zpowers s := hzs ▸ Subgroup.mem_map_of_mem Mg.subtype hx
    have hy' : (x : G) ∈ Subgroup.zpowers t := hzt ▸ Subgroup.mem_map_of_mem Mg.subtype hy
    exact Subtype.ext (hdisj hx' hy')
  have hcardK : Nat.card (K.subgroupOf Mg) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  obtain ⟨b, hb, a', ha'ord, ha'cyc, ha'3, ha'w, ha'gen⟩ :=
    full_base_four_group_action_has_inverted_odd_cycling_lift n hn m hm s' t'
      ((Subgroup.orderOf_coe s').symm.trans hs) ((Subgroup.orderOf_coe t').symm.trans ht)
      (Subtype.ext hst) hdisj' (U.subgroupOf Mg) hU' (V.subgroupOf Mg) hV' (K.subgroupOf Mg)
      (by rw [hcardK]; exact hK) hCV' (conjNormal_surjective_of_card V hV4 hsix) ⟨w, hwN⟩
      ((Subgroup.orderOf_coe (⟨w, hwN⟩ : Mg)).symm.trans hw) (Subtype.ext hws) (Subtype.ext hwt)
  refine ⟨b, hb, a', a'.2, (Subgroup.orderOf_coe a').trans ha'ord, fun v hv hv1 h => ?_,
    fun v hv => ?_, congrArg Subtype.val ha'w, ?_⟩
  · exact ha'cyc ⟨v, hVM hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
      (fun h1 => hv1 (congrArg Subtype.val h1)) (Subtype.ext h)
  · exact congrArg Subtype.val (ha'3 ⟨v, hVM hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
  · have h := congrArg (Subgroup.map Mg.subtype) ha'gen
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    refine Eq.trans ?_ h
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_union, SetLike.mem_coe, Set.mem_insert_iff,
      Set.mem_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro (hx | hx | hx)
      · exact ⟨⟨x, hCM hx⟩, Or.inl ((mem_centralizer_subgroupOf_iff V _).mpr hx), rfl⟩
      · exact ⟨⟨w, hwN⟩, Or.inr (Or.inl rfl), hx.symm⟩
      · exact ⟨a', Or.inr (Or.inr rfl), hx.symm⟩
    · rintro ⟨y, hy | rfl | rfl, rfl⟩
      · exact Or.inl ((mem_centralizer_subgroupOf_iff V y).mp hy)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

end CFSG.Wreathed.TorusSplitting

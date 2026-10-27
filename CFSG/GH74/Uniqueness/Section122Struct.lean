module

public import CFSG.GH74.Uniqueness.Section122Bender

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.inter_subset_rootCenter
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) {x : X}
    (hx : x ∈ Z ∩ (M : Set X)) :
    x ∈ (Bender.rootCenter (Q : Subgroup c.L)).map c.L.subtype := by
  have hc := hBL.benderCore Q (c.tL_mul_self S.invariant) (Ctx12.tL_not_mem_borel hQ)
  have hxL : x ∈ c.L := S.inter_subset_L c hx
  have hxB : (⟨x, hxL⟩ : c.L) ∈ Bender.borel (Q : Subgroup c.L) := by
    change _ ∈ normalizer _
    rw [← hQ]
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hx.2, hxL⟩)
  have hxo : orderOf (⟨x, hxL⟩ : c.L) = 2 := by
    rw [orderOf_mk]
    exact S.invariant.1 x hx.1
  exact ⟨⟨x, hxL⟩, hc.center_of_involution _ hxB hxo, rfl⟩

theorem ZDSetup.mem_inter_of_mem_rootCenter
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) {y : ↥c.L}
    (hy : y ∈ Bender.rootCenter (Q : Subgroup c.L)) (hy1 : y ≠ 1) :
    (y : X) ∈ Z ∩ (M : Set X) := by
  have hc := hBL.benderCore Q (c.tL_mul_self S.invariant) (Ctx12.tL_not_mem_borel hQ)
  obtain ⟨hyB, hyo⟩ := hc.involution_iff.mpr ⟨hy, hy1⟩
  have hyM : y ∈ (M ⊓ c.L).subgroupOf c.L := by
    rw [hQ]
    exact hyB
  exact ⟨hinv y y.2 (by rw [orderOf_coe]; exact hyo), (mem_inf.mp (mem_subgroupOf.mp hyM)).1⟩

theorem ZDSetup.zHull_eq_map_rootCenter
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) :
    zHull Z M = (Bender.rootCenter (Q : Subgroup c.L)).map c.L.subtype := by
  apply le_antisymm
  · exact (closure_le _).mpr fun x hx => S.inter_subset_rootCenter c hBL hQ hx
  · rintro _ ⟨y, hy, rfl⟩
    by_cases hy1 : y = 1
    · rw [hy1, map_one]
      exact one_mem _
    · exact subset_closure (S.mem_inter_of_mem_rootCenter c hBL hQ hinv hy hy1)

theorem ZDSetup.inter_eq_zHull_diff
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) :
    Z ∩ (M : Set X) = (zHull Z M : Set X) \ {1} := by
  ext x
  constructor
  · intro hx
    refine ⟨subset_closure hx, fun h1 => ?_⟩
    have h2 := S.invariant.1 x hx.1
    rw [Set.mem_singleton_iff.mp h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · rintro ⟨hx, hx1⟩
    rw [SetLike.mem_coe, S.zHull_eq_map_rootCenter c hBL hQ hinv] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one]; exact Set.mem_singleton _)
    exact S.mem_inter_of_mem_rootCenter c hBL hQ hinv hy hy1

theorem ZDSetup.card_zHull
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) :
    Nat.card ↥(zHull Z M) = 2 ^ n := by
  have hc := hBL.benderCore Q (c.tL_mul_self S.invariant) (Ctx12.tL_not_mem_borel hQ)
  rw [S.zHull_eq_map_rootCenter c hBL hQ hinv, card_map_of_injective c.L.subtype_injective,
    hc.card_center]

theorem ZDSetup.isElemAbelian_zHull
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) :
    Open.IsElemAbelian 2 (zHull Z M) := by
  have hc := hBL.benderCore Q (c.tL_mul_self S.invariant) (Ctx12.tL_not_mem_borel hQ)
  rw [S.zHull_eq_map_rootCenter c hBL hQ hinv]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul,
      (Bender.mem_rootCenter_iff.mp hb').2 a' (Bender.mem_rootCenter_iff.mp ha').1]
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, sq, hc.center_sq y hy, map_one]

theorem Ctx12.kGrp_le_D_inf_L (hZ : IsInvariantInvolutionSet Z) (c : Ctx12 Z M) :
    kGrp M c.t ≤ c.D ⊓ c.L := by
  refine le_inf ?_ c.kGrp_le_L
  change ⁅zpowers c.t, pPrimeCoreIn c.D⁆ ≤ c.D
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have ht2 : c.t * c.t = 1 := hZ.mul_self_eq_one c.ht
  have hg₂D : g₂ ∈ c.D := pPrimeCoreIn_le _ hg₂
  rcases eq_one_or_eq_of_mem_zpowers ht2 hg₁ with rfl | rfl
  · rw [commutatorElement_one_left]
    exact one_mem _
  · rw [commutatorElement_def]
    exact c.D.mul_mem (c.conj_mem_D hZ hg₂D) (c.D.inv_mem hg₂D)

theorem Ctx12.invertedSet_subset_kGrp (c : Ctx12 Z M) :
    CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t ⊆ (kGrp M c.t : Set X) := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet
    (odd_card_pPrimeCoreIn c.D) hx
  have hcomm : ⁅c.t, d⁻¹⁆ = d ^ 2 := by
    calc ⁅c.t, d⁻¹⁆ = (c.t * d * c.t⁻¹)⁻¹ * d := by rw [commutatorElement_def]; group
      _ = d ^ 2 := by rw [hd.2, inv_inv, sq]
  rw [SetLike.mem_coe, ← hcomm]
  exact commutator_mem_commutator (mem_zpowers c.t) ((pPrimeCoreIn c.D).inv_mem hd.1)

theorem ZDSetup.lemma122f
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L))
    (hinv : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z) :
    (kGrp M c.t : Set X) = CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t ∧
      kGrp M c.t = c.D ⊓ c.L ∧ IsCyclic ↥(c.D ⊓ c.L) ∧ Nat.card ↥(c.D ⊓ c.L) = 2 ^ n - 1 := by
  have hc := hBL.benderCore Q (c.tL_mul_self S.invariant) (Ctx12.tL_not_mem_borel hQ)
  have hDL := Ctx12.map_subtype_cartan hQ
  have hcard : Nat.card ↥(c.D ⊓ c.L) = 2 ^ n - 1 := by
    rw [← hDL, card_map_of_injective c.L.subtype_injective, hc.card_cartan, mul_one]
  have hcyc : IsCyclic ↥(c.D ⊓ c.L) := by
    rw [← hDL]
    have := hc.isCyclic
    exact isCyclic_of_surjective (equivMapOfInjective _ _ c.L.subtype_injective)
      (MulEquiv.surjective _)
  have hI : Nat.card ↥(CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t) = 2 ^ n - 1 := by
    rw [(S.prodDisc.prop36d S.invariant c.ht c.htM c.hz c.hzM).1, zNum,
      S.inter_eq_zHull_diff c hBL hQ hinv, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (show (1 : X) ∈ (zHull Z M : Set X) from one_mem _),
      ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (S.card_zHull c hBL hQ hinv)
  have hIK := c.invertedSet_subset_kGrp
  have hKDL := c.kGrp_le_D_inf_L S.invariant
  have hIDL : CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t =
      ((c.D ⊓ c.L : Subgroup X) : Set X) := by
    refine Set.eq_of_subset_of_ncard_le (hIK.trans hKDL) ?_ (Set.toFinite _)
    have h1 : (↑(c.D ⊓ c.L) : Set X).ncard = 2 ^ n - 1 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    have h2 : (CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t).ncard = 2 ^ n - 1 := by
      rw [← Nat.card_coe_set_eq]
      exact hI
    rw [h1, h2]
  have hK : kGrp M c.t = c.D ⊓ c.L := by
    refine le_antisymm hKDL fun x hx => hIK ?_
    rw [hIDL]
    exact hx
  exact ⟨by rw [hK, hIDL], hK, hcyc, hcard⟩

theorem ZDSetup.centralizer_L_le_D (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    centralizer (c.L : Set X) ≤ c.D := by
  intro y hy
  have hyz : c.z * y = y * c.z := mem_centralizer_iff.mp hy c.z c.z_mem_L
  have hyt : c.t * y = y * c.t := mem_centralizer_iff.mp hy c.t c.t_mem_L
  have hyM : y ∈ M :=
    S.prodDisc.centralizer_le_of_mem c.hz c.hzM (mem_centralizer_singleton_iff.mpr hyz.symm)
  refine mem_inf.mpr ⟨hyM, Bender.mem_conjugate_iff_mul_inv.mpr ?_⟩
  rw [hyt, mul_inv_cancel_right]
  exact hyM

theorem Ctx12.not_normalizer_le (c : Ctx12 Z M) : ¬ normalizer (c.L : Set X) ≤ M :=
  fun hle => c.htM (hle (le_normalizer c.t_mem_L))

theorem Ctx12.nonempty_inter_normalizer (c : Ctx12 Z M) :
    (Z ∩ ((normalizer (c.L : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
  ⟨c.z, c.hz, mem_inf.mpr ⟨le_normalizer c.z_mem_L, c.hzM⟩⟩

theorem ZDSetup.zHull_normalizer_le (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    zHull Z (normalizer (c.L : Set X)) ≤ c.L := by
  refine (closure_le _).mpr fun y hy => ?_
  obtain ⟨l, hl, hly⟩ := S.exists_conj_zHull c.not_normalizer_le c.nonempty_inter_normalizer c.hz
    (le_normalizer c.z_mem_L) c.hzM hy.1 hy.2
  have hlN : l⁻¹ ∈ normalizer (c.L : Set X) := inv_mem (Cor713.zHull_le _ hl)
  have h1 := (mem_normalizer_iff.mp hlN c.z).mp c.z_mem_L
  rw [inv_inv] at h1
  rw [SetLike.mem_coe, ← hly]
  exact h1

theorem ZDSetup.normalizer_L_eq
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    (normalizer (c.L : Set X) : Set X) = (c.L : Set X) * (c.D : Set X) := by
  have hZ := S.invariant
  have hc := hBL.benderCore Q (c.tL_mul_self hZ) (Ctx12.tL_not_mem_borel hQ)
  have hDN : c.D ≤ normalizer (c.L : Set X) :=
    S.prodDisc.le_normalizer_lSubgroup hZ c.ht c.htM c.hz c.hzM
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, l, hl, rfl⟩ :=
      S.cor713_exists_mul_eq c.not_normalizer_le c.nonempty_inter_normalizer hx
    have hlL : l ∈ c.L := S.zHull_normalizer_le c hl
    obtain ⟨hmN, hmM⟩ := mem_inf.mp hm
    have ht'L : m⁻¹ * c.t * m ∈ c.L := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hmN) c.t).mp c.t_mem_L
      rwa [inv_inv] at h1
    have ht'2 : (⟨_, ht'L⟩ : c.L) * ⟨_, ht'L⟩ = 1 := by
      apply Subtype.ext
      change m⁻¹ * c.t * m * (m⁻¹ * c.t * m) = 1
      calc m⁻¹ * c.t * m * (m⁻¹ * c.t * m) = m⁻¹ * (c.t * c.t) * m := by group
        _ = 1 := by rw [hZ.mul_self_eq_one c.ht]; group
    have ht'B : (⟨_, ht'L⟩ : c.L) ∉ Bender.borel (Q : Subgroup c.L) := by
      intro hB
      have h1 : (⟨_, ht'L⟩ : c.L) ∈ (M ⊓ c.L).subgroupOf c.L := by
        rw [hQ]
        exact hB
      have h2 : m⁻¹ * c.t * m ∈ M := (mem_inf.mp (mem_subgroupOf.mp h1)).1
      apply c.htM
      have h3 := M.mul_mem (M.mul_mem hmM h2) (M.inv_mem hmM)
      rwa [show m * (m⁻¹ * c.t * m) * m⁻¹ = c.t by group] at h3
    obtain ⟨b, hb, hbt⟩ := hc.exists_conj_eq ht'2 ht'B
    have hbt' : m⁻¹ * c.t * m = (b : X)⁻¹ * c.t * b := congrArg Subtype.val hbt
    have hbM : (b : X) ∈ M := by
      have h1 : b ∈ (M ⊓ c.L).subgroupOf c.L := by
        rw [hQ]
        exact hb
      exact (mem_inf.mp (mem_subgroupOf.mp h1)).1
    have hyM : m * (b : X)⁻¹ ∈ M := M.mul_mem hmM (M.inv_mem hbM)
    have hyt : c.t * (m * (b : X)⁻¹) = m * (b : X)⁻¹ * c.t := by
      have h1 : (m * (b : X)⁻¹)⁻¹ * c.t * (m * (b : X)⁻¹) = c.t := by
        calc (m * (b : X)⁻¹)⁻¹ * c.t * (m * (b : X)⁻¹)
            = (b : X) * (m⁻¹ * c.t * m) * (b : X)⁻¹ := by group
          _ = (b : X) * ((b : X)⁻¹ * c.t * b) * (b : X)⁻¹ := by rw [hbt']
          _ = c.t := by group
      calc c.t * (m * (b : X)⁻¹)
          = m * (b : X)⁻¹ * ((m * (b : X)⁻¹)⁻¹ * c.t * (m * (b : X)⁻¹)) := by group
        _ = m * (b : X)⁻¹ * c.t := by rw [h1]
    have hyD : m * (b : X)⁻¹ ∈ c.D := by
      refine mem_inf.mpr ⟨hyM, Bender.mem_conjugate_iff_mul_inv.mpr ?_⟩
      rw [hyt, mul_inv_cancel_right]
      exact hyM
    have hbl : (b : X) * l ∈ c.L := c.L.mul_mem b.2 hlL
    have hconj : m * (b : X)⁻¹ * ((b : X) * l) * (m * (b : X)⁻¹)⁻¹ ∈ c.L :=
      (mem_normalizer_iff.mp (hDN hyD) _).mp hbl
    refine Set.mem_mul.mpr ⟨_, hconj, m * (b : X)⁻¹, hyD, ?_⟩
    group
  · rintro ⟨l, hl, d, hd, rfl⟩
    exact mul_mem (le_normalizer hl) (hDN hd)

theorem ZDSetup.nM_eq_L (S : ZDSetup X Z M) (c : Ctx12 Z M) {n i : ℕ}
    (hBL : Bender.BenderType ↥c.L n i 1) {Q : Sylow 2 ↥c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∃ T : Subgroup X, T ≤ c.L ⊓ M ∧ IsPGroup 2 T ∧ ABGLocalTools.IsSylowOf 2 T (c.L ⊓ M) ∧
      (∀ g ∈ c.L ⊓ M, ∀ x ∈ T, g * x * g⁻¹ ∈ T) ∧
      ((M ⊓ normalizer (c.L : Set X) : Subgroup X) : Set X) = (T : Set X) * (c.D : Set X) := by
  have hZ := S.invariant
  have hc := hBL.benderCore Q (c.tL_mul_self hZ) (Ctx12.tL_not_mem_borel hQ)
  have hDN : c.D ≤ normalizer (c.L : Set X) :=
    S.prodDisc.le_normalizer_lSubgroup hZ c.ht c.htM c.hz c.hzM
  have hN := S.normalizer_L_eq c hBL hQ
  refine ⟨(Q : Subgroup c.L).map c.L.subtype, Ctx12.map_sylow_le hQ, Q.isPGroup'.map _,
    Ctx12.isSylowOf_map_sylow hQ, ?_, ?_⟩
  · intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hgB : (⟨g, (mem_inf.mp hg).1⟩ : c.L) ∈ normalizer ((Q : Subgroup c.L) : Set c.L) := by
      rw [← hQ]
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨(mem_inf.mp hg).2, (mem_inf.mp hg).1⟩)
    exact ⟨_, (mem_normalizer_iff.mp hgB x').mp hx', rfl⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨hxM, hxN⟩ := mem_inf.mp hx
      have hx' : x ∈ (c.L : Set X) * (c.D : Set X) := by
        rw [← hN]
        exact hxN
      obtain ⟨l, hl, d, hd, rfl⟩ := hx'
      have hlM : l ∈ M := by
        have h1 := M.mul_mem hxM (M.inv_mem (mem_inf.mp hd).1)
        rwa [mul_inv_cancel_right] at h1
      have hlB : (⟨l, hl⟩ : c.L) ∈ Bender.borel (Q : Subgroup c.L) := by
        change _ ∈ normalizer _
        rw [← hQ]
        exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hlM, hl⟩)
      rw [← hc.sup_eq] at hlB
      have hcQ : Bender.cartan (Q : Subgroup c.L) c.tL ≤
          normalizer ((Q : Subgroup c.L) : Set c.L) := Bender.cartan_le_borel _ _
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hcQ] at hlB
      obtain ⟨q, hq, k, hk, hqk⟩ := hlB
      have hkD : (k : X) ∈ c.D := by
        have h1 : (k : X) ∈ (Bender.cartan (Q : Subgroup c.L) c.tL).map c.L.subtype :=
          ⟨k, hk, rfl⟩
        rw [Ctx12.map_subtype_cartan hQ] at h1
        exact h1.1
      refine Set.mem_mul.mpr ⟨q, ⟨q, hq, rfl⟩, k * d, c.D.mul_mem hkD hd, ?_⟩
      rw [← mul_assoc]
      congr 1
      exact congrArg Subtype.val hqk
    · rintro ⟨a, ha, d, hd, rfl⟩
      have haLM := Ctx12.map_sylow_le hQ ha
      refine mem_inf.mpr ⟨M.mul_mem (mem_inf.mp haLM).2 (mem_inf.mp hd).1, ?_⟩
      exact mul_mem (le_normalizer (mem_inf.mp haLM).1) (hDN hd)

end CFSG.GH74.Uniqueness

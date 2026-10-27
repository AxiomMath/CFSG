module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open scoped commutatorElement

namespace AlternatingFour

private def invol : Fin 3 → alternatingGroup (Fin 4) :=
  ![⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

private def label (w : alternatingGroup (Fin 4)) : Fin 3 :=
  if w = invol 0 then 0 else if w = invol 1 then 1 else 2

private theorem label_invol : ∀ i : Fin 3, label (invol i) = i := by decide

private theorem conj_invol : ∀ (g : alternatingGroup (Fin 4)) (i : Fin 3),
    g * invol i * g⁻¹ = invol (label (g * invol i * g⁻¹)) := by decide

private theorem label_conj_inv (g : alternatingGroup (Fin 4)) (i : Fin 3) :
    label (g⁻¹ * invol (label (g * invol i * g⁻¹)) * g) = i := by
  rw [← conj_invol, show g⁻¹ * (g * invol i * g⁻¹) * g = invol i by group, label_invol]

private def labelPerm (g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 3) where
  toFun i := label (g * invol i * g⁻¹)
  invFun i := label (g⁻¹ * invol i * g)
  left_inv := label_conj_inv g
  right_inv i := by simpa using label_conj_inv g⁻¹ i

private theorem sign_labelPerm : ∀ g : alternatingGroup (Fin 4),
    Equiv.Perm.sign (labelPerm g) = 1 := by decide

private theorem labelPerm_eq_one_iff : ∀ g : alternatingGroup (Fin 4),
    labelPerm g = 1 ↔ g * g = 1 := by decide

private theorem exists_labelPerm_eq : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 →
    ∃ g : alternatingGroup (Fin 4), labelPerm g = σ := by decide

private def toAltThree : alternatingGroup (Fin 4) →* alternatingGroup (Fin 3) where
  toFun g := ⟨labelPerm g, Equiv.Perm.mem_alternatingGroup.mpr (sign_labelPerm g)⟩
  map_one' := Subtype.ext (Equiv.ext fun i => by
    change label (1 * invol i * 1⁻¹) = i
    rw [one_mul, inv_one, mul_one, label_invol])
  map_mul' g h := Subtype.ext (Equiv.ext fun i => by
    change label (g * h * invol i * (g * h)⁻¹) = label (g * invol (label (h * invol i * h⁻¹)) * g⁻¹)
    rw [← conj_invol, mul_inv_rev]
    group)

private theorem toAltThree_surjective : Function.Surjective toAltThree := fun σ => by
  obtain ⟨g, hg⟩ := exists_labelPerm_eq σ (Equiv.Perm.mem_alternatingGroup.mp σ.2)
  exact ⟨g, Subtype.ext hg⟩

private def vec (w : alternatingGroup (Fin 4)) : Fin 3 → ZMod 2 :=
  fun j => if w * w = 1 ∧ w ≠ 1 ∧ w ≠ invol j then 1 else 0

private theorem sum_vec : ∀ w : alternatingGroup (Fin 4), ∑ j, vec w j = 0 := by decide

private theorem vec_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    vec (a * b) = vec a + vec b := by decide

private theorem vec_conj (g w : alternatingGroup (Fin 4)) (i : Fin 3) :
    vec (g * w * g⁻¹) i = vec w ((labelPerm g)⁻¹ i) := by
  have hi : invol ((labelPerm g)⁻¹ i) = g⁻¹ * invol i * g := by
    have h := conj_invol g⁻¹ i
    rw [inv_inv] at h
    exact h.symm
  have h1 : g * w * g⁻¹ * (g * w * g⁻¹) = 1 ↔ w * w = 1 := by
    rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, conj_eq_one_iff]
  have h2 : g * w * g⁻¹ = invol i ↔ w = g⁻¹ * invol i * g := by
    constructor
    · intro h
      rw [← h]
      group
    · intro h
      rw [h]
      group
  simp only [vec, hi, h1, h2, ne_eq, conj_eq_one_iff]

private theorem exists_vec_eq : ∀ x : Fin 3 → ZMod 2, ∑ i, x i = 0 →
    ∃ w : alternatingGroup (Fin 4), w * w = 1 ∧ vec w = x := by decide

private theorem eq_one_of_vec_eq_zero : ∀ w : alternatingGroup (Fin 4), w * w = 1 → vec w = 0 →
    w = 1 := by decide

private theorem vec_mem (w : alternatingGroup (Fin 4)) : vec w ∈ evenWeight 3 :=
  sum_vec w

private theorem sq_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    a * b * (a * b) = 1 := by decide

private theorem sq_or_cube : ∀ x : alternatingGroup (Fin 4), x * x = 1 ∨ x ^ 3 = 1 := by decide

private theorem exists_cube_mul_cube : ∃ t : alternatingGroup (Fin 4), t ^ 3 = 1 ∧
    ∀ x : alternatingGroup (Fin 4), x ^ 3 = 1 ∨ (t⁻¹ * x) ^ 3 = 1 :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    by decide, by decide⟩

private theorem sq_eq_one_of_commute : ∀ g : alternatingGroup (Fin 4),
    (∀ v, v * v = 1 → g * v = v * g) → g * g = 1 := by decide

private theorem eq_one_of_forall_commute : ∀ v : alternatingGroup (Fin 4), v * v = 1 →
    (∀ g, g * v = v * g) → v = 1 := by decide

private theorem exists_commutator_eq : ∀ v : alternatingGroup (Fin 4), v * v = 1 →
    ∃ w g : alternatingGroup (Fin 4), w * w = 1 ∧ ⁅w, g⁆ = v := by decide

private theorem exists_conj_eq : ∀ v w : alternatingGroup (Fin 4), v * v = 1 → w * w = 1 →
    v ≠ 1 → w ≠ 1 → ∃ g, g * v * g⁻¹ = w := by decide

private theorem exists_involution : ∃ v : alternatingGroup (Fin 4), v * v = 1 ∧ v ≠ 1 :=
  ⟨invol 0, by decide⟩

private def fourGroup : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {σ | σ * σ = 1}
  mul_mem' {a b} ha hb := sq_mul a b ha hb
  one_mem' := mul_one 1
  inv_mem' {a} ha := by
    change a⁻¹ * a⁻¹ = 1
    rw [← mul_inv_rev, show a * a = 1 from ha, inv_one]

private theorem eq_one_of_cube_of_two_pow {X : Type*} [Group X] {x : X} {k : ℕ} (h3 : x ^ 3 = 1)
    (h2 : x ^ 2 ^ k = 1) : x = 1 := by
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

private theorem mem_pCore_iff (x : alternatingGroup (Fin 4)) :
    x ∈ CFSG.pCore 2 (alternatingGroup (Fin 4)) ↔ x * x = 1 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rcases sq_or_cube x with h | h
    · exact h
    · rw [eq_one_of_cube_of_two_pow h hk', mul_one]
  · intro hx
    have hn : fourGroup.Normal := ⟨fun n hn g => by
      change g * n * g⁻¹ * (g * n * g⁻¹) = 1
      rw [show g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ by group,
        show n * n = 1 from hn, mul_one, mul_inv_cancel]⟩
    have hp : IsPGroup 2 fourGroup := fun y => ⟨1, Subtype.ext (by
      rw [pow_one, sq]
      exact y.2)⟩
    exact (le_sSup (show fourGroup ∈ {K : Subgroup _ | K.Normal ∧ IsPGroup 2 K} from ⟨hn, hp⟩) :
      fourGroup ≤ CFSG.pCore 2 (alternatingGroup (Fin 4))) hx

private theorem vec_one : vec 1 = 0 := by decide

private theorem mul_comm_of_sq {X : Type*} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

end AlternatingFour

section Transport

open AlternatingFour

variable {G : Type*} [Group G] {Y : Subgroup G} (e : Y ≃* alternatingGroup (Fin 4))

include e

private theorem mem_pCore_of_mulEquiv (y : Y) : y ∈ CFSG.pCore 2 Y ↔ (y : G) * y = 1 := by
  have h1 : y ∈ CFSG.pCore 2 Y ↔ e y ∈ CFSG.pCore 2 (alternatingGroup (Fin 4)) := by
    rw [← CFSG.pCore_map_iso 2 e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h1, mem_pCore_iff, ← map_mul, ← map_one e, e.injective.eq_iff, Subtype.ext_iff]
  rfl

private theorem mem_blockQ_of_mulEquiv (x : G) : x ∈ blockQ Y ↔ x ∈ Y ∧ x * x = 1 := by
  change x ∈ (Open.pCore 2 Y).map Y.subtype ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_pCore_of_mulEquiv e y).mp hy⟩
  · rintro ⟨hx, hxx⟩
    exact ⟨⟨x, hx⟩, (mem_pCore_of_mulEquiv e ⟨x, hx⟩).mpr hxx, rfl⟩

private theorem sq_apply_of_mulEquiv {y : Y} (hy : (y : G) * y = 1) : e y * e y = 1 := by
  rw [← map_mul, show y * y = 1 from Subtype.ext hy, map_one]

private theorem sq_symm_apply_of_mulEquiv {v : alternatingGroup (Fin 4)} (hv : v * v = 1) :
    (e.symm v : G) * e.symm v = 1 := by
  rw [← Subgroup.coe_mul, ← map_mul, hv, map_one, Subgroup.coe_one]

private theorem blockU_eq_of_mulEquiv : blockU Y = blockQ Y := by
  refine le_antisymm (commutator_le_left_of_le_normalizer
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Y)) fun x hx => ?_
  obtain ⟨hxY, hxx⟩ := (mem_blockQ_of_mulEquiv e x).mp hx
  obtain ⟨w, g, hw, hwg⟩ := exists_commutator_eq (e ⟨x, hxY⟩) (sq_apply_of_mulEquiv e hxx)
  have hx' : ((e.symm ⁅w, g⁆ : Y) : G) = x := by
    rw [hwg, MulEquiv.symm_apply_apply]
  rw [← hx', map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (g₁ := (e.symm w : G)) (g₂ := (e.symm g : G))
    ((mem_blockQ_of_mulEquiv e _).mpr ⟨(e.symm w).2, sq_symm_apply_of_mulEquiv e hw⟩)
    (e.symm g).2

private theorem blockZ_eq_of_mulEquiv : blockZ Y = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [blockZ, blockU_eq_of_mulEquiv e] at hx
  obtain ⟨hxY, hxx⟩ := (mem_blockQ_of_mulEquiv e x).mp hx.1
  have hc : ∀ g, g * e ⟨x, hxY⟩ = e ⟨x, hxY⟩ * g := fun g => by
    have h := Subgroup.mem_centralizer_iff.mp hx.2 _ (e.symm g).2
    have h' : e.symm g * ⟨x, hxY⟩ = ⟨x, hxY⟩ * e.symm g := Subtype.ext h
    simpa using congrArg e h'
  have h1 := eq_one_of_forall_commute _ (sq_apply_of_mulEquiv e hxx) hc
  rw [← map_one e, e.injective.eq_iff] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

private theorem ker_of_mulEquiv : (toAltThree.comp e.toMonoidHom).ker = CFSG.pCore 2 Y := by
  ext y
  rw [MonoidHom.mem_ker, mem_pCore_of_mulEquiv e]
  constructor
  · intro h
    have h1 : labelPerm (e y) = 1 := congrArg Subtype.val h
    rw [labelPerm_eq_one_iff, ← map_mul, ← map_one e, e.injective.eq_iff] at h1
    exact congrArg Subtype.val h1
  · intro h
    have h1 : y * y = 1 := Subtype.ext h
    apply Subtype.ext
    change labelPerm (e y) = 1
    rw [labelPerm_eq_one_iff, ← map_mul, h1, map_one]

private theorem eq_top_of_isPGroup_quotient (N : Subgroup Y) [N.Normal]
    (hN : IsPGroup 2 (Y ⧸ N)) : N = ⊤ := by
  have hcube : ∀ y : Y, y ^ 3 = 1 → y ∈ N := fun y hy => by
    obtain ⟨k, hk⟩ := hN (y : Y ⧸ N)
    have h3 : (y : Y ⧸ N) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff y).mp (eq_one_of_cube_of_two_pow h3 hk)
  obtain ⟨t, ht, hx⟩ := exists_cube_mul_cube
  have hsymm : ∀ c, c ^ 3 = 1 → e.symm c ∈ N := fun c hc =>
    hcube _ (by rw [← map_pow, hc, map_one])
  refine eq_top_iff.mpr fun y _ => ?_
  rcases hx (e y) with h | h
  · simpa using hsymm _ h
  · have hy : y = e.symm t * e.symm (t⁻¹ * e y) := by
      rw [← map_mul, mul_inv_cancel_left, MulEquiv.symm_apply_apply]
    rw [hy]
    exact N.mul_mem (hsymm t ht) (hsymm _ h)

private theorem charTwo_of_mulEquiv : CharTwo Y := by
  rintro x ⟨hxY, hxC⟩
  have hc : ∀ v, v * v = 1 → e ⟨x, hxY⟩ * v = v * e ⟨x, hxY⟩ := fun v hv => by
    have h := Subgroup.mem_centralizer_iff.mp hxC _
      ((mem_blockQ_of_mulEquiv e _).mpr ⟨(e.symm v).2, sq_symm_apply_of_mulEquiv e hv⟩)
    have h' : e.symm v * ⟨x, hxY⟩ = ⟨x, hxY⟩ * e.symm v := Subtype.ext h
    simpa using (congrArg e h').symm
  have h2 : (⟨x, hxY⟩ : Y) * ⟨x, hxY⟩ = 1 :=
    e.injective (by rw [map_mul, map_one, sq_eq_one_of_commute _ hc])
  exact (mem_blockQ_of_mulEquiv e x).mpr ⟨hxY, congrArg Subtype.val h2⟩

private theorem card_quotient_of_mulEquiv : Nat.card (Y ⧸ CFSG.pCore 2 Y) = 3 := by
  have hs : Function.Surjective (toAltThree.comp e.toMonoidHom) :=
    toAltThree_surjective.comp e.surjective
  rw [← ker_of_mulEquiv e, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    hs).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem isShort2_of_mulEquiv : IsShort2 Y := by
  have hU := blockU_eq_of_mulEquiv e
  have hZ := blockZ_eq_of_mulEquiv e
  have hQ := mem_blockQ_of_mulEquiv e
  refine ⟨fun N _ hN => eq_top_of_isPGroup_quotient e N hN, charTwo_of_mulEquiv e, ⟨?_, ?_⟩,
    Or.inr (card_quotient_of_mulEquiv e), ?_, ?_⟩
  · rw [hU]
    refine le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact mul_comm_of_sq ((hQ y).mp hy).2 ((hQ x).mp hx).2 ((hQ _).mp ((blockQ Y).mul_mem hy hx)).2
  · intro x hx
    rw [hU] at hx
    rw [sq]
    exact ((hQ x).mp hx).2
  · rw [hZ, hU]
    obtain ⟨v, hv, hv1⟩ := exists_involution
    refine bot_lt_iff_ne_bot.mpr fun hbot => hv1 ?_
    have h : ((e.symm v : Y) : G) ∈ blockQ Y :=
      (hQ _).mpr ⟨(e.symm v).2, sq_symm_apply_of_mulEquiv e hv⟩
    rw [hbot, Subgroup.mem_bot] at h
    have h' : e.symm v = 1 := Subtype.ext h
    simpa using congrArg e h'
  · intro W _ hWU hYW
    rw [hZ, hU]
    rw [hU] at hWU
    by_cases hW : W = ⊥
    · exact Or.inl hW
    refine Or.inr (le_antisymm hWU fun z hz => ?_)
    obtain ⟨⟨x, hxW⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨hxY, hxx⟩ := (hQ x).mp (hWU hxW)
    obtain ⟨hzY, hzz⟩ := (hQ z).mp hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact W.one_mem
    have hne : ∀ {y : G} (hy : y ∈ Y), y ≠ 1 → e ⟨y, hy⟩ ≠ 1 := fun hy hy1 h =>
      hy1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    obtain ⟨g, hg⟩ := exists_conj_eq _ _ (sq_apply_of_mulEquiv e hxx)
      (sq_apply_of_mulEquiv e hzz) (hne hxY hx1') (hne hzY hz1)
    have hz' : z = (e.symm g : G) * x * (e.symm g : G)⁻¹ := by
      have h := congrArg (fun w => (e.symm w : G)) hg
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      exact h.symm
    rw [hz']
    exact (Subgroup.mem_normalizer_iff.mp (hYW (e.symm g).2) x).mp hxW

private theorem isAltType_of_mulEquiv : IsAltType Y 3 := by
  have hU := blockU_eq_of_mulEquiv e
  have hZ := blockZ_eq_of_mulEquiv e
  have hQ := mem_blockQ_of_mulEquiv e
  have hle : blockU Y ≤ Y := fun u hu => ((hQ u).mp (hU ▸ hu)).1
  have hsq : ∀ u : blockU Y, e (Subgroup.inclusion hle u) * e (Subgroup.inclusion hle u) = 1 :=
    fun u => sq_apply_of_mulEquiv e ((hQ u).mp (hU ▸ u.2)).2
  let β : blockU Y →* Multiplicative (evenWeight 3) :=
    { toFun := fun u => Multiplicative.ofAdd ⟨vec (e (Subgroup.inclusion hle u)), vec_mem _⟩
      map_one' := by
        rw [map_one, map_one, ← ofAdd_zero]
        exact congrArg Multiplicative.ofAdd (Subtype.ext vec_one)
      map_mul' := fun u₁ u₂ => by
        rw [← ofAdd_add]
        congr 1
        apply Subtype.ext
        change vec (e (Subgroup.inclusion hle (u₁ * u₂))) =
          vec (e (Subgroup.inclusion hle u₁)) + vec (e (Subgroup.inclusion hle u₂))
        rw [map_mul, map_mul, vec_mul _ _ (hsq u₁) (hsq u₂)] }
  refine ⟨toAltThree.comp e.toMonoidHom, toAltThree_surjective.comp e.surjective,
    ker_of_mulEquiv e, β, fun x => ?_, ?_, fun ℓ u v hv i => ?_⟩
  · obtain ⟨w, hw, hwx⟩ := exists_vec_eq _ (Multiplicative.toAdd x).2
    have hwU : ((e.symm w : Y) : G) ∈ blockU Y :=
      hU ▸ (hQ _).mpr ⟨(e.symm w).2, sq_symm_apply_of_mulEquiv e hw⟩
    refine ⟨⟨_, hwU⟩, ?_⟩
    change Multiplicative.ofAdd ⟨vec (e (Subgroup.inclusion hle ⟨_, hwU⟩)), _⟩ = x
    have he : Subgroup.inclusion hle ⟨_, hwU⟩ = e.symm w := Subtype.ext rfl
    simp only [he, MulEquiv.apply_symm_apply, hwx]
    rfl
  · rw [hZ, Subgroup.bot_subgroupOf]
    refine eq_bot_iff.mpr fun u hu => ?_
    have h0 : vec (e (Subgroup.inclusion hle u)) = 0 :=
      congrArg Subtype.val (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hu))
    have h1 := eq_one_of_vec_eq_zero _ (hsq u) h0
    rw [← map_one e, e.injective.eq_iff] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using congrArg Subtype.val h1))
  · have hι : e (Subgroup.inclusion hle v) =
        e ℓ * e (Subgroup.inclusion hle u) * (e ℓ)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext hv)
    change vec (e (Subgroup.inclusion hle v)) i =
      vec (e (Subgroup.inclusion hle u)) ((labelPerm (e ℓ))⁻¹ i)
    rw [hι, vec_conj]

end Transport

section ClassX

variable {G : Type} [Group G]

theorem inClassXBlock_of_mulEquiv_alternatingFour {Y : Subgroup G}
    (hY : Nonempty (↥Y ≃* alternatingGroup (Fin 4))) : InClassXBlock Y := by
  obtain ⟨e⟩ := hY
  exact ⟨isShort2_of_mulEquiv e, Or.inr ⟨1, le_rfl, isAltType_of_mulEquiv e⟩⟩

end ClassX

end CFSG.AGLEmbedding

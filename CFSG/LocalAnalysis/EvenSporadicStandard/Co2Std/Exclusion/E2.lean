module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Delta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Descend
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {G : Type} [Group G] [Finite G]
variable {L A T : Subgroup G} {z t : G}

theorem Hyp.z_sq (h : Hyp G L A T z t) : z * z = 1 := h.set.z_sq

theorem Hyp.zpowers_le_centralizer_A (h : Hyp G L A T z t) :
    zpowers z ≤ centralizer (A : Set G) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro a ha
  exact h.commute_of_mem (h.jc.le ha)

theorem Hyp.z_not_mem_L (h : Hyp G L A T z t) : z ∉ L := fun hz =>
  h.set.z_ne (mem_bot.1 (h.set.disjoint.le_bot ⟨hz, mem_zpowers z⟩))

theorem Hyp.B_inf_L (h : Hyp G L A T z t) : B A z ⊓ L = A := by
  refine le_antisymm ?_ (le_inf le_sup_left h.jc.le)
  rintro x ⟨hx, hxL⟩
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_A hx
  have hbL : b ∈ L := by
    have : a⁻¹ * (a * b) ∈ L := mul_mem (inv_mem (h.jc.le ha)) hxL
    rwa [inv_mul_cancel_left] at this
  rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with rfl | rfl
  · simpa using ha
  · exact absurd hbL h.z_not_mem_L

theorem Hyp.elemAb_B (h : Hyp G L A T z t) : IsElementaryAbelian 2 ↥(B A z) := by
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  letI : IsElementaryAbelian 2 ↥(zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by rw [pow_two]; exact h.set.z_sq)
  exact IsElementaryAbelian.sup_of_le_centralizer h.zpowers_le_centralizer_A

theorem Hyp.card_B (h : Hyp G L A T z t) : Nat.card (B A z) = 2 ^ 11 := by
  have hd : Disjoint A (zpowers z) := h.set.disjoint.mono_left h.jc.le
  have hcard := Nat.card_congr (mulEquivProdSup h.zpowers_le_centralizer_A hd).toEquiv
  rw [Nat.card_prod, h.jc.module.card, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact h.set.z_sq) h.set.z_ne] at hcard
  change Nat.card ↥(A ⊔ zpowers z) = 2 ^ 11
  rw [← hcard]
  norm_num

theorem Hyp.centralizer_B (h : Hyp G L A T z t) : centralizer (B A z : Set G) = B A z := by
  change centralizer ((A ⊔ zpowers z : Subgroup G) : Set G) = A ⊔ zpowers z
  letI : IsElementaryAbelian 2 ↥(A ⊔ zpowers z) := h.elemAb_B
  refine le_antisymm ?_ (Subgroup.le_centralizer (H := A ⊔ zpowers z))
  intro x hx
  have hxz : x ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hx z (mem_sup_right (mem_zpowers z))).symm
  rw [h.set.centralizer_z] at hxz
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer
      (le_centralizer_zpowers_of_centralizer_eq h.set.centralizer_z) hxz
  have hbC : b ∈ centralizer (A : Set G) := h.zpowers_le_centralizer_A hb
  have hxCA : l * b ∈ centralizer (A : Set G) :=
    Subgroup.centralizer_le (fun a ha => mem_sup_left ha) hx
  have hlC : l ∈ centralizer (A : Set G) := by
    have h1 : l * b * b⁻¹ ∈ centralizer (A : Set G) := mul_mem hxCA (inv_mem hbC)
    rwa [mul_inv_cancel_right] at h1
  have hlA : l ∈ A := by
    rw [← h.jc.centralizer_eq]
    exact ⟨hl, hlC⟩
  rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with hb1 | hbz
  · rw [hb1, mul_one]
    exact mem_sup_left hlA
  · rw [hbz]
    exact mul_mem_sup hlA (mem_zpowers z)

theorem Hyp.zpowers_le_centralizer_B (h : Hyp G L A T z t) :
    zpowers z ≤ centralizer (A ⊔ zpowers z : Subgroup G) := by
  rw [le_centralizer_iff]
  refine sup_le ?_ (Subgroup.le_centralizer (H := zpowers z))
  rw [le_centralizer_iff]
  exact h.zpowers_le_centralizer_A

theorem Hyp.M_inf_centralizer (h : Hyp G L A T z t) :
    M A z ⊓ centralizer ({z} : Set G) = (L ⊓ normalizer (A : Set G)) ⊔ zpowers z := by
  change normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
    (L ⊓ normalizer (A : Set G)) ⊔ zpowers z
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxM, hxz⟩
    rw [h.set.centralizer_z] at hxz
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer
        (le_centralizer_zpowers_of_centralizer_eq h.set.centralizer_z) hxz
    have hbC : b ∈ centralizer ((A ⊔ zpowers z : Subgroup G) : Set G) :=
      h.zpowers_le_centralizer_B hb
    have hlB : l ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) := by
      have h1 : l * b * b⁻¹ ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) :=
        mul_mem hxM (Subgroup.centralizer_le_normalizer _ (inv_mem hbC))
      rwa [mul_inv_cancel_right] at h1
    have hlN : l ∈ L ⊓ normalizer (A : Set G) := by
      refine ⟨hl, Subgroup.mem_normalizer_fintype fun a ha => ?_⟩
      have h1 : l * a * l⁻¹ ∈ A ⊔ zpowers z :=
        (mem_normalizer_iff.1 hlB a).1 (mem_sup_left ha)
      have h2 : l * a * l⁻¹ ∈ L := mul_mem (mul_mem hl (h.jc.le ha)) (inv_mem hl)
      have h3 : l * a * l⁻¹ ∈ (A ⊔ zpowers z : Subgroup G) ⊓ L := ⟨h1, h2⟩
      change l * a * l⁻¹ ∈ B A z ⊓ L at h3
      rwa [h.B_inf_L] at h3
    exact mul_mem_sup hlN hb
  · refine sup_le ?_ ?_
    · rintro x ⟨hxL, hxN⟩
      have hxz : x ∈ normalizer (zpowers z : Set G) := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [show (zpowers z : Set G) = Subgroup.closure {z} from by
          rw [Subgroup.zpowers_eq_closure], Subgroup.centralizer_closure]
        exact mem_centralizer_singleton_iff.mpr (h.commute_of_mem hxL)
      refine ⟨?_, ?_⟩
      · exact Subgroup.inf_normalizer_le_normalizer_sup A (zpowers z) ⟨hxN, hxz⟩
      · exact mem_centralizer_singleton_iff.mpr (h.commute_of_mem hxL)
    · rintro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      refine ⟨?_, ?_⟩
      · exact Subgroup.le_normalizer (mem_sup_right (zpow_mem_zpowers z k))
      · exact mem_centralizer_singleton_iff.mpr (Commute.zpow_left (Commute.refl z) k).eq

theorem Hyp.conj_mem (h : Hyp G L A T z t) {m : G} (hm : m ∈ M A z) :
    z⁻¹ * (m * z * m⁻¹) ∈ A := by
  change m ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) at hm
  have hmzB : m * z * m⁻¹ ∈ A ⊔ zpowers z :=
    (mem_normalizer_iff.1 hm z).1 (mem_sup_right (mem_zpowers z))
  obtain ⟨a, ha, b, hb, hmb⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_A hmzB
  rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with hb1 | hbz
  · exfalso
    refine h.not_conj a (h.jc.le ha) (isConj_iff.2 ⟨m, ?_⟩)
    rw [hmb, hb1, mul_one]
  · have h2 : m * z * m⁻¹ = a * z := by rw [hmb, hbz]
    have h3 : z⁻¹ * (a * z) = a := by
      calc z⁻¹ * (a * z) = z⁻¹ * (z * a) := by rw [h.commute_of_mem (h.jc.le ha)]
        _ = (z⁻¹ * z) * a := by rw [mul_assoc]
        _ = a := by rw [inv_mul_cancel, one_mul]
    rw [h2, h3]
    exact ha

theorem Hyp.A_le_T (h : Hyp G L A T z t) : A ≤ T := by
  have hA2 : IsPGroup 2 ↥A := h.jc.module.elemAb.isPGroup 2 ↥A
  have hAT2 : IsPGroup 2 (A ⊔ T : Subgroup G) := hA2.to_sup_of_normal_left' h.set.pgroup h.jc.T_le
  have hleL : (A ⊔ T : Subgroup G) ≤ L := sup_le h.jc.le h.set.le
  have hmax := h.set.maximal (A ⊔ T) hleL hAT2 le_sup_right
  calc A ≤ A ⊔ T := le_sup_left
    _ = T := hmax

private theorem isElementaryAbelian_range {X Y : Type*} [Group X] [Group Y] {p : ℕ} [Fact p.Prime]
    (φ : X →* Y) [IsElementaryAbelian p X] : IsElementaryAbelian p ↥(φ.range) := by
  haveI : IsElementaryAbelian p ↥(⊤ : Subgroup X) := by
    refine
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm' a.1 b.1)⟩⟩
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p X) a.1
  rw [MonoidHom.range_eq_map]
  exact IsElementaryAbelian.map φ

theorem eq_A_of_elemAb_le_T (h : Hyp G L A T z t) {X : Subgroup G} (hXT : X ≤ T)
    (hXe : IsElementaryAbelian 2 ↥X) (hXcard : 2 ^ 10 ≤ Nat.card X) : X = A := by
  letI : IsElementaryAbelian 2 ↥X := hXe
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  have hXL : X ≤ L := hXT.trans h.set.le
  have hXle : X ≤ L ⊓ normalizer (A : Set G) := le_inf hXL (hXT.trans h.jc.T_le)
  let φ : ↥X →* MulAut ↥A := (conjN L A).comp (Subgroup.inclusion hXle)
  have hφapply : ∀ (x : ↥X) (a : ↥A),
      (((φ x) a : ↥A) : G) = (x : G) * (a : G) * (x : G)⁻¹ :=
    fun x a => conjN_apply (L := L) (A := A) (x := ⟨x, hXle x.2⟩) a
  have hker : ∀ x : ↥X, x ∈ φ.ker ↔ (x : G) ∈ A := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx1
      have hxC : (x : G) ∈ centralizer (A : Set G) := by
        rw [mem_centralizer_iff]
        intro a ha
        have h2 : (φ x) ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hx1]; rfl
        have h3 : (x : G) * a * (x : G)⁻¹ = a := by
          rw [← hφapply x ⟨a, ha⟩]
          exact congrArg (fun z : ↥A => (z : G)) h2
        have h4 : (x : G) * a = a * (x : G) := by
          calc (x : G) * a = (x : G) * a * (x : G)⁻¹ * (x : G) := by group
            _ = a * (x : G) := by rw [h3]
        exact h4.symm
      have hmem : (x : G) ∈ L ⊓ centralizer (A : Set G) := ⟨hXL x.2, hxC⟩
      rwa [h.jc.centralizer_eq] at hmem
    · intro hxA
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      show (x : G) * (a : G) * (x : G)⁻¹ = (a : G)
      have hcomm : (x : G) * (a : G) = (a : G) * (x : G) :=
        congrArg Subtype.val (mul_comm' (⟨(x : G), hxA⟩ : ↥A) a)
      rw [hcomm]
      group
  have hrange_bot : φ.range = ⊥ := by
    by_contra hne
    have hYQ : φ.range ≤ autImage L A := by
      rintro _ ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXle x, rfl⟩
    have hYe : IsElementaryAbelian 2 ↥(φ.range) := isElementaryAbelian_range φ
    have hoff := h.jc.module.noOffenders φ.range hYQ hYe hne
    let Z : Type := {a : ↥A // ∀ y ∈ (φ.range : Subgroup (MulAut ↥A)), y a = a}
    have hfix : Nat.card ↥(φ.ker) ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective
        (fun x : ↥(φ.ker) => (⟨⟨((x.1 : ↥X) : G), (hker (x.1 : ↥X)).1 x.2⟩, ?_⟩ : Z)) ?_
      · rintro y hy
        obtain ⟨x', rfl⟩ := hy
        apply Subtype.ext
        rw [hφapply x' ⟨((x.1 : ↥X) : G), (hker (x.1 : ↥X)).1 x.2⟩]
        have hcomm : (x' : G) * ((x.1 : ↥X) : G) = ((x.1 : ↥X) : G) * x' :=
          congrArg Subtype.val (mul_comm' x' (x.1 : ↥X))
        rw [hcomm]
        group
      · intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Z => ((z.1 : ↥A) : G)) hxy
    have hlt : Nat.card ↥X < 2 ^ 10 := by
      calc Nat.card ↥X = Nat.card ↥(φ.ker) * Nat.card ↥(φ.range) :=
            (Subgroup.card_ker_mul_card_range φ).symm
        _ ≤ Nat.card Z * Nat.card ↥(φ.range) := Nat.mul_le_mul_right _ hfix
        _ = Nat.card ↥(φ.range) * Nat.card Z := mul_comm _ _
        _ < 2 ^ 10 := hoff
    omega
  have hXA : X ≤ A := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : φ ⟨x, hx⟩ ∈ φ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hrange_bot] at h2
      simpa using h2
    exact (hker ⟨x, hx⟩).1 h1
  refine Subgroup.eq_of_le_of_card_ge hXA ?_
  rw [h.jc.module.card]
  exact hXcard

theorem Hyp.zpowers_le_centralizer_T (h : Hyp G L A T z t) :
    zpowers z ≤ centralizer (T : Set G) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro t' ht'
  exact h.commute_of_mem (h.set.le ht')

theorem Hyp.isPGroup_P (h : Hyp G L A T z t) :
    IsPGroup 2 (T ⊔ zpowers z : Subgroup G) ∧ T.relIndex (T ⊔ zpowers z) = 2 :=
  CFSG.EvenSporadicStandard.Co2Std.isPGroup_sup_zpowers
    (orderOf_eq_prime (by rw [pow_two]; exact h.set.z_sq) h.set.z_ne)
    h.set.pgroup h.zpowers_le_centralizer_T (h.set.disjoint.mono_left h.set.le)

theorem Hyp.P_le_normalizer_T (h : Hyp G L A T z t) :
    (T ⊔ zpowers z : Subgroup G) ≤ normalizer (T : Set G) := by
  have hzn : zpowers z ≤ normalizer (T : Set G) :=
    h.zpowers_le_centralizer_T.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  exact sup_le Subgroup.le_normalizer hzn

theorem eq_B_of_elemAb_le_P (h : Hyp G L A T z t) {Y : Subgroup G}
    (hYP : Y ≤ T ⊔ zpowers z) (hYe : IsElementaryAbelian 2 ↥Y)
    (hYcard : 2 ^ 11 ≤ Nat.card Y) : Y = B A z := by
  letI : IsElementaryAbelian 2 ↥Y := hYe
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  let P : Subgroup G := T ⊔ zpowers z
  have hYP' : Y ≤ P := hYP
  have hTrel : T.relIndex P = 2 := h.isPGroup_P.2
  have hPn : P ≤ normalizer (T : Set G) := h.P_le_normalizer_T
  letI : (T.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPn
  let q : ↥Y →* P ⧸ (T.subgroupOf P) :=
    (QuotientGroup.mk' (T.subgroupOf P)).comp (Subgroup.inclusion hYP')
  have hker : q.ker = (Y ⊓ T).subgroupOf Y := by
    rw [show q = (QuotientGroup.mk' (T.subgroupOf P)).comp (Subgroup.inclusion hYP') from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hrange : Nat.card ↥(q.range) ≤ 2 := by
    have h1 : Nat.card ↥(q.range) ≤ Nat.card (P ⧸ (T.subgroupOf P)) :=
      Nat.card_le_card_of_injective (fun x : ↥(q.range) => (x.1 : P ⧸ (T.subgroupOf P)))
        (fun x y hxy => Subtype.ext hxy)
    have h2 : Nat.card (P ⧸ (T.subgroupOf P)) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hTrel
    omega
  have hYT10 : 2 ^ 10 ≤ Nat.card ↥(Y ⊓ T) := by
    have hcardY : Nat.card ↥Y = Nat.card ↥(Y ⊓ T) * Nat.card ↥(q.range) := by
      have h1 : Nat.card ↥Y = Nat.card ↥(q.ker) * Nat.card ↥(q.range) :=
        (Subgroup.card_ker_mul_card_range q).symm
      rw [h1, hker]
      congr 1
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ T ≤ Y)).toEquiv
    have h1 : Nat.card ↥Y ≤ Nat.card ↥(Y ⊓ T) * 2 := by
      rw [hcardY]
      exact Nat.mul_le_mul_left _ hrange
    have h2 : 2 ^ 11 = 2 * 2 ^ 10 := by norm_num
    omega
  have hYTe : IsElementaryAbelian 2 ↥(Y ⊓ T) := IsElementaryAbelian.of_le hYe inf_le_left
  have hYTA : Y ⊓ T = A := eq_A_of_elemAb_le_T h inf_le_right hYTe hYT10
  have hAY : A ≤ Y := by rw [← hYTA]; exact inf_le_left
  have hCPA : P ⊓ centralizer (A : Set G) = B A z := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxP, hxC⟩
      have hxP' : x ∈ T ⊔ zpowers z := hxP
      obtain ⟨t', ht', b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_T hxP'
      have ht'C : t' ∈ centralizer (A : Set G) := by
        have h1 : t' * b * b⁻¹ ∈ centralizer (A : Set G) :=
          mul_mem hxC (inv_mem (h.zpowers_le_centralizer_A hb))
        rwa [mul_inv_cancel_right] at h1
      have ht'A : t' ∈ A := by
        rw [← h.jc.centralizer_eq]
        exact ⟨h.set.le ht', ht'C⟩
      exact mul_mem_sup ht'A hb
    · refine le_inf ?_ ?_
      · exact sup_le (h.A_le_T.trans le_sup_left) le_sup_right
      · exact sup_le (Subgroup.le_centralizer (H := A)) h.zpowers_le_centralizer_A
  have hYB : Y ≤ B A z := by
    rw [← hCPA]
    refine le_inf hYP' ?_
    intro y hy
    rw [mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (mul_comm' (⟨a, hAY ha⟩ : ↥Y) ⟨y, hy⟩)
  exact Subgroup.eq_of_le_of_card_ge hYB (by rw [h.card_B]; exact hYcard)

theorem Hyp.normalizer_P_le_M (h : Hyp G L A T z t) :
    normalizer ((T ⊔ zpowers z : Subgroup G) : Set G) ≤ M A z := by
  intro n hn
  change n ∈ normalizer ((B A z : Subgroup G) : Set G)
  rw [mem_normalizer_iff_map_conj_eq]
  have hBP : B A z ≤ T ⊔ zpowers z := sup_le (h.A_le_T.trans le_sup_left) le_sup_right
  have hYP : (B A z).map (MulAut.conj n).toMonoidHom ≤ T ⊔ zpowers z := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact (mem_normalizer_iff.1 hn b).1 (hBP hb)
  have hYcard : 2 ^ 11 ≤ Nat.card ↥((B A z).map (MulAut.conj n).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective, h.card_B]
  have hYe : IsElementaryAbelian 2 ↥((B A z).map (MulAut.conj n).toMonoidHom) := by
    letI : IsElementaryAbelian 2 ↥(B A z) := h.elemAb_B
    exact IsElementaryAbelian.map (MulAut.conj n).toMonoidHom
  exact eq_B_of_elemAb_le_P h hYP hYe hYcard

theorem Hyp.P_le_centralizer_z (h : Hyp G L A T z t) :
    (T ⊔ zpowers z : Subgroup G) ≤ centralizer ({z} : Set G) := by
  refine sup_le ?_ ?_
  · intro t' ht'
    exact mem_centralizer_singleton_iff.mpr (h.commute_of_mem (h.set.le ht'))
  · intro w hw
    rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hw with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr (by group)
    · exact mem_centralizer_singleton_iff.mpr (by group)

theorem Hyp.center_P_cases (h : Hyp G L A T z t) {c : G}
    (hcP : c ∈ T ⊔ zpowers z) (hc : ∀ p ∈ (T ⊔ zpowers z : Subgroup G), p * c = c * p) :
    c = 1 ∨ c = t ∨ c = z ∨ c = t * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_T hcP
  have hbz : ∀ s ∈ T, s * b = b * s := by
    intro s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (h.commute_of_mem (h.set.le hs)) k).eq
  have hacomm : ∀ s ∈ T, s * a = a * s := by
    intro s hs
    have h1 : s * (a * b) = (a * b) * s := hc s (mem_sup_left hs)
    have h2 : s * a * b = a * s * b := by
      calc s * a * b = s * (a * b) := by group
        _ = (a * b) * s := h1
        _ = a * (b * s) := by group
        _ = a * (s * b) := by rw [hbz s hs]
        _ = a * s * b := by group
    exact mul_right_cancel h2
  rcases h.set.center_eq a ha hacomm with ha1 | hat
  · rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with hb1 | hbz2
    · left; rw [ha1, hb1, mul_one]
    · right; right; left; rw [ha1, hbz2, one_mul]
  · rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with hb1 | hbz2
    · right; left; rw [hat, hb1, mul_one]
    · right; right; right; rw [hat, hbz2]

theorem Hyp.z_mem_centralizer_P (h : Hyp G L A T z t) :
    z ∈ centralizer ((T ⊔ zpowers z : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_T hp
  have hbz : b * z = z * b := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_left (Commute.refl z) k).eq
  calc a * b * z = a * (b * z) := by group
    _ = a * (z * b) := by rw [hbz]
    _ = (a * z) * b := by group
    _ = (z * a) * b := by rw [h.commute_of_mem (h.set.le ha)]
    _ = z * (a * b) := by group

theorem Hyp.tz_mem_centralizer_P (h : Hyp G L A T z t) :
    t * z ∈ centralizer ((T ⊔ zpowers z : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_T hp
  have hzt : z * t = t * z := (h.commute_of_mem h.set.t_mem).symm
  have hbt : b * t = t * b := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_left (Commute.symm (h.commute_of_mem h.set.t_mem)) k).eq
  have habt : (a * b) * t = t * (a * b) := by
    calc (a * b) * t = a * (b * t) := by group
      _ = a * (t * b) := by rw [hbt]
      _ = (a * t) * b := by group
      _ = (t * a) * b := by rw [h.set.t_comm a ha]
      _ = t * (a * b) := by group
  have habz : (a * b) * z = z * (a * b) := by
    have hbz : b * z = z * b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_left (Commute.refl z) k).eq
    calc (a * b) * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [hbz]
      _ = (a * z) * b := by group
      _ = (z * a) * b := by rw [h.commute_of_mem (h.set.le ha)]
      _ = z * (a * b) := by group
  calc a * b * (t * z) = ((a * b) * t) * z := by group
    _ = (t * (a * b)) * z := by rw [habt]
    _ = t * ((a * b) * z) := by group
    _ = t * (z * (a * b)) := by rw [habz]
    _ = (t * z) * (a * b) := by group

theorem Hyp.exists_conj_z_eq_tz (h : Hyp G L A T z t) :
    ∃ n ∈ M A z, n * z * n⁻¹ = t * z := by
  classical
  let P : Subgroup G := T ⊔ zpowers z
  have hP2 : IsPGroup 2 P := h.isPGroup_P.1
  by_cases hbig : ∃ R : Subgroup G, IsPGroup 2 R ∧ P < R
  · obtain ⟨R, hR2, hPR⟩ := hbig
    obtain ⟨n, hnR, hnP, hnd⟩ := exists_mem_normalizer_not_mem hR2 hPR
    have hnN : n ∈ normalizer (P : Set G) :=
      Subgroup.mem_normalizer_fintype fun p hp => (hnd p (hPR.le hp)).1 hp
    have hnN' : n ∈ normalizer ((T ⊔ zpowers z : Subgroup G) : Set G) := hnN
    have hnC : n ∉ centralizer ({z} : Set G) := by
      intro hnC
      have hn2 : IsPGroup 2 (zpowers n : Subgroup G) := hR2.to_le (zpowers_le.2 hnR)
      have hQ2 : IsPGroup 2 (zpowers n ⊔ P : Subgroup G) :=
        hn2.to_sup_of_normal_right' hP2 (zpowers_le.2 hnN)
      have hQle : (zpowers n ⊔ P : Subgroup G) ≤ centralizer ({z} : Set G) := by
        refine sup_le ?_ ?_
        · intro w hw
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
          exact mem_centralizer_singleton_iff.mpr
            (Commute.zpow_left (mem_centralizer_singleton_iff.mp hnC) k).eq
        · intro q hq
          exact h.P_le_centralizer_z hq
      have hQint : (zpowers n ⊔ P : Subgroup G) ⊓ L = T :=
        h.set.maximal ((zpowers n ⊔ P) ⊓ L) inf_le_right (hQ2.to_le inf_le_left)
          (le_inf ((show T ≤ P from le_sup_left).trans le_sup_right) h.set.le)
      have hQleP : (zpowers n ⊔ P : Subgroup G) ≤ P := by
        intro q hq
        have hqC : q ∈ centralizer ({z} : Set G) := hQle hq
        rw [h.set.centralizer_z] at hqC
        obtain ⟨l, hl, b, hb, hqeq⟩ :=
          exists_mul_of_mem_sup_of_le_centralizer
            (le_centralizer_zpowers_of_centralizer_eq h.set.centralizer_z) hqC
        have hbP : b ∈ P := mem_sup_right hb
        have hbQ : b ∈ (zpowers n ⊔ P : Subgroup G) := mem_sup_right hbP
        have hq' : l * b ∈ (zpowers n ⊔ P : Subgroup G) := by rw [← hqeq]; exact hq
        have hlQ : l ∈ (zpowers n ⊔ P : Subgroup G) := by
          have h1 : l * b * b⁻¹ ∈ (zpowers n ⊔ P : Subgroup G) := mul_mem hq' (inv_mem hbQ)
          rwa [mul_inv_cancel_right] at h1
        have hlT : l ∈ T := by
          rw [← hQint]
          exact ⟨hlQ, hl⟩
        rw [hqeq]
        exact mul_mem_sup hlT hb
      exact hnP (hQleP (mem_sup_left (mem_zpowers n)))
    have hz'P : n * z * n⁻¹ ∈ P := (mem_normalizer_iff.1 hnN z).1 (mem_sup_right (mem_zpowers z))
    have hz'cent : ∀ p ∈ P, p * (n * z * n⁻¹) = (n * z * n⁻¹) * p := by
      intro p hp
      have hninv : n⁻¹ ∈ normalizer (P : Set G) := inv_mem hnN
      have h1 : n⁻¹ * p * n ∈ P := by
        simpa using (mem_normalizer_iff.1 hninv p).1 hp
      have hzz : z * (n⁻¹ * p * n) = (n⁻¹ * p * n) * z := by
        have h2 : (n⁻¹ * p * n) ∈ centralizer ({z} : Set G) := h.P_le_centralizer_z h1
        exact mem_centralizer_iff.1 h2 z (by simp)
      have hzz' : (n⁻¹ * p * n) * z = z * (n⁻¹ * p * n) := hzz.symm
      calc p * (n * z * n⁻¹) = n * ((n⁻¹ * p * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * p * n)) * n⁻¹ := by rw [hzz']
        _ = (n * z * n⁻¹) * p := by group
    have hz'eq : n * z * n⁻¹ = t * z := by
      rcases h.center_P_cases hz'P hz'cent with h1 | h1 | h1 | h1
      · exfalso
        apply h.set.z_ne
        calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
          _ = 1 := by rw [h1]; group
      · exfalso
        exact h.not_conj t h.set.t_mem (isConj_iff.2 ⟨n, h1⟩)
      · exfalso
        exact hnC (mem_centralizer_singleton_iff.mpr (by
          calc n * z = (n * z * n⁻¹) * n := by group
            _ = z * n := by rw [h1]))
      · exact h1
    exact ⟨n, h.normalizer_P_le_M hnN', hz'eq⟩
  · push Not at hbig
    have hPmax : ∀ {Q : Subgroup G}, IsPGroup 2 Q → P ≤ Q → Q = P := by
      intro Q hQ hPQ
      rcases eq_or_lt_of_le hPQ with h | h
      · exact h.symm
      · exact absurd h (hbig Q hQ)
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let S : Sylow 2 G := ⟨P, hP2, by intro Q hQ hPQ; exact hPmax hQ hPQ⟩
    obtain ⟨g, hg⟩ := isConj_iff.1 h.conj_zt
    have hx : t * z ∈ centralizer (P : Set G) := h.tz_mem_centralizer_P
    have hy : g⁻¹ * (t * z) * g ∈ centralizer (P : Set G) := by
      have h1 : g⁻¹ * (t * z) * g = z := by
        rw [← hg]; group
      rw [h1]
      exact h.z_mem_centralizer_P
    obtain ⟨n, hnN, hnconj⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer (t * z) g hx hy
    have hnN' : n ∈ normalizer ((T ⊔ zpowers z : Subgroup G) : Set G) := hnN
    have hz : z = n⁻¹ * (t * z) * n := by
      rw [← hnconj]
      rw [← hg]
      group
    refine ⟨n, h.normalizer_P_le_M hnN', ?_⟩
    nth_rewrite 1 [hz]
    group

theorem Hyp.M_le_normalizer (h : Hyp G L A T z t) :
    M A z ≤ normalizer (A : Set G) := by
  classical
  let S : Set G := {d : G | ∃ m ∈ M A z, d = z⁻¹ * (m * z * m⁻¹)}
  let D : Subgroup G := Subgroup.closure S
  have hDA : D ≤ A := by
    refine (Subgroup.closure_le A).2 ?_
    rintro d ⟨m, hm, rfl⟩
    exact h.conj_mem hm
  have hDnormM : ∀ m' ∈ M A z, ∀ d ∈ D, m' * d * m'⁻¹ ∈ D := by
    intro m' hm' d hd
    have hT : S ⊆ (D.comap (MulAut.conj m').toMonoidHom : Set G) := by
      rintro d ⟨m, hm, rfl⟩
      change (MulAut.conj m').toMonoidHom (z⁻¹ * (m * z * m⁻¹)) ∈ D
      have h1 : z⁻¹ * (m' * z * m'⁻¹) ∈ D := Subgroup.subset_closure ⟨m', hm', rfl⟩
      have h2 : z⁻¹ * ((m' * m) * z * (m' * m)⁻¹) ∈ D :=
        Subgroup.subset_closure ⟨m' * m, mul_mem hm' hm, rfl⟩
      have h3 : (MulAut.conj m').toMonoidHom (z⁻¹ * (m * z * m⁻¹)) =
          (z⁻¹ * (m' * z * m'⁻¹))⁻¹ * (z⁻¹ * ((m' * m) * z * (m' * m)⁻¹)) := by
        change m' * (z⁻¹ * (m * z * m⁻¹)) * m'⁻¹ =
          (z⁻¹ * (m' * z * m'⁻¹))⁻¹ * (z⁻¹ * ((m' * m) * z * (m' * m)⁻¹))
        group
      rw [h3]
      exact mul_mem (inv_mem h1) h2
    exact (Subgroup.closure_le (D.comap (MulAut.conj m').toMonoidHom)).2 hT hd
  have hDinvNL : ∀ x ∈ L ⊓ normalizer (A : Set G), ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    rintro x ⟨hxL, hxN⟩ d hd
    have hxM : x ∈ M A z := h.le_M ⟨hxL, hxN⟩
    have hxzinv : x * z⁻¹ = z⁻¹ * x :=
      (Commute.inv_right (show Commute x z from h.commute_of_mem hxL)).eq
    have hxinvz : x⁻¹ * z * x = z := by
      have h1 : x⁻¹ * z = z * x⁻¹ := by
        calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← h.commute_of_mem hxL]
          _ = z * x⁻¹ := by group
      rw [h1]
      group
    have hT : S ⊆ (D.comap (MulAut.conj x).toMonoidHom : Set G) := by
      rintro d ⟨m, hm, rfl⟩
      change (MulAut.conj x).toMonoidHom (z⁻¹ * (m * z * m⁻¹)) ∈ D
      have hxm : x * m * x⁻¹ ∈ M A z := mul_mem (mul_mem hxM hm) (inv_mem hxM)
      have h1 : z⁻¹ * ((x * m * x⁻¹) * z * (x * m * x⁻¹)⁻¹) ∈ D :=
        Subgroup.subset_closure ⟨x * m * x⁻¹, hxm, rfl⟩
      have h2 : (MulAut.conj x).toMonoidHom (z⁻¹ * (m * z * m⁻¹)) =
          z⁻¹ * ((x * m * x⁻¹) * z * (x * m * x⁻¹)⁻¹) := by
        change x * (z⁻¹ * (m * z * m⁻¹)) * x⁻¹ =
          z⁻¹ * ((x * m * x⁻¹) * z * (x * m * x⁻¹)⁻¹)
        calc x * (z⁻¹ * (m * z * m⁻¹)) * x⁻¹
            = (x * z⁻¹) * (m * z * m⁻¹) * x⁻¹ := by group
          _ = (z⁻¹ * x) * (m * z * m⁻¹) * x⁻¹ := by rw [hxzinv]
          _ = z⁻¹ * (x * m * z * m⁻¹ * x⁻¹) := by group
          _ = z⁻¹ * (x * m * x⁻¹ * z * x * m⁻¹ * x⁻¹) := by
              have e : x * m * z * m⁻¹ * x⁻¹ = x * m * x⁻¹ * z * x * m⁻¹ * x⁻¹ := by
                calc x * m * z * m⁻¹ * x⁻¹
                    = x * m * (x⁻¹ * z * x) * m⁻¹ * x⁻¹ := by rw [hxinvz]
                  _ = x * m * x⁻¹ * z * x * m⁻¹ * x⁻¹ := by group
              rw [e]
          _ = z⁻¹ * ((x * m * x⁻¹) * z * (x * m * x⁻¹)⁻¹) := by group
      rw [h2]
      exact h1
    exact (Subgroup.closure_le (D.comap (MulAut.conj x).toMonoidHom)).2 hT hd
  have htD : t ∈ D := by
    obtain ⟨n, hnM, hnz⟩ := h.exists_conj_z_eq_tz
    have h1 : z⁻¹ * (n * z * n⁻¹) ∈ D := Subgroup.subset_closure ⟨n, hnM, rfl⟩
    have h2 : z⁻¹ * (n * z * n⁻¹) = t := by
      rw [hnz]
      calc z⁻¹ * (t * z) = z⁻¹ * (z * t) := by rw [h.commute_of_mem h.set.t_mem]
        _ = t := by group
    rwa [h2] at h1
  have hUinv : ∀ g ∈ ⁅autImage L A, autImage L A⁆, ∀ u ∈ D.subgroupOf A, g u ∈ D.subgroupOf A := by
    intro g hg u hu
    have hgQ : g ∈ autImage L A := by
      have h1 := Subgroup.commutator_le_sup (autImage L A) (autImage L A) hg
      rwa [sup_idem] at h1
    obtain ⟨x, rfl⟩ := hgQ
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    rw [conjN_apply (L := L) (A := A)]
    exact hDinvNL x x.2 u hu
  have hcases := h.jc.module.irreducible_derived (D.subgroupOf A) hUinv
  have hUne : D.subgroupOf A ≠ ⊥ := by
    intro hbot
    have h1 : (⟨t, h.jc.t_mem⟩ : ↥A) ∈ D.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact htD
    rw [hbot] at h1
    exact h.set.t_ne (congrArg Subtype.val (mem_bot.1 h1))
  have hUtop : D.subgroupOf A = ⊤ := hcases.resolve_left hUne
  have hDAeq : D = A := by
    refine le_antisymm hDA ?_
    intro a ha
    have h1 : (⟨a, ha⟩ : ↥A) ∈ D.subgroupOf A := by
      rw [hUtop]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at h1
  intro m hm
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h2 : m * a * m⁻¹ ∈ D := hDnormM m hm a (by rw [hDAeq]; exact ha)
    rwa [hDAeq] at h2
  · intro ha
    have h2 : m⁻¹ * (m * a * m⁻¹) * m ∈ D := by
      simpa using hDnormM m⁻¹ (inv_mem hm) (m * a * m⁻¹) (by rw [hDAeq]; exact ha)
    rw [hDAeq] at h2
    rwa [show m⁻¹ * (m * a * m⁻¹) * m = a from by group] at h2

private theorem deltaHom_ker (h : Hyp G L A T z t) :
    (deltaHom fun m hm => h.conj_mem hm).ker = (B A z).subgroupOf (R₀ A z) := by
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hr1
    have h1 : delta z (r : G) = 1 := by simpa using congrArg Subtype.val hr1
    have h2 : (r : G) * z * (r : G)⁻¹ = z := by
      rw [← mul_delta z (r : G), h1, mul_one]
    have hrCz : (r : G) ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (by
        calc (r : G) * z = ((r : G) * z * (r : G)⁻¹) * (r : G) := by group
          _ = z * (r : G) := by rw [h2])
    have hrMem : (r : G) ∈ M A z ⊓ centralizer ({z} : Set G) := ⟨r.2.1, hrCz⟩
    rw [h.M_inf_centralizer] at hrMem
    obtain ⟨l, hl, b, hb, hrlb⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer
        (show zpowers z ≤ centralizer ((L ⊓ normalizer (A : Set G)) : Set G) from by
          rw [zpowers_le, mem_centralizer_iff]
          intro y hy
          exact h.commute_of_mem hy.1) hrMem
    have hlA : l ∈ A := by
      rw [← h.jc.centralizer_eq]
      refine ⟨hl.1, ?_⟩
      have hrC : l * b ∈ centralizer (A : Set G) := by rw [← hrlb]; exact r.2.2
      have h3 : l * b * b⁻¹ ∈ centralizer (A : Set G) :=
        Subgroup.mul_mem _ hrC (Subgroup.inv_mem _ (h.zpowers_le_centralizer_A hb))
      rwa [mul_inv_cancel_right] at h3
    rw [hrlb]
    exact mul_mem_sup hlA hb
  · intro hr
    have h1 : (r : G) ∈ B A z := hr
    letI : IsElementaryAbelian 2 ↥(B A z) := h.elemAb_B
    have hzB : z ∈ B A z := mem_sup_right (mem_zpowers z)
    have hrz : (r : G) * z = z * (r : G) :=
      congrArg Subtype.val (mul_comm' (⟨(r : G), h1⟩ : ↥(B A z)) ⟨z, hzB⟩)
    apply Subtype.ext
    show delta z (r : G) = 1
    rw [delta, hrz]
    group

theorem Hyp.R₀_conj_mem (h : Hyp G L A T z t) {x : G}
    (hx : x ∈ L ⊓ normalizer (A : Set G)) {r : G} (hr : r ∈ R₀ A z) :
    x * r * x⁻¹ ∈ R₀ A z := by
  have hxM : x ∈ M A z := h.le_M hx
  have hcent : x * r * x⁻¹ ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : x⁻¹ * a * x ∈ A := (mem_normalizer_iff''.1 hx.2 a).1 ha
    have hrC : r ∈ centralizer (A : Set G) := hr.2
    have hcomm : (x⁻¹ * a * x) * r = r * (x⁻¹ * a * x) :=
      mem_centralizer_iff.1 hrC _ ha'
    have hconj : (x * r * x⁻¹) * a * (x * r * x⁻¹)⁻¹ = a := by
      calc (x * r * x⁻¹) * a * (x * r * x⁻¹)⁻¹
          = x * r * (x⁻¹ * a * x) * r⁻¹ * x⁻¹ := by group
        _ = x * (r * (x⁻¹ * a * x)) * r⁻¹ * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * r) * r⁻¹ * x⁻¹ := by rw [← hcomm]
        _ = a := by group
    have h1 : (x * r * x⁻¹) * a = a * (x * r * x⁻¹) := by
      have h3 := congrArg (fun z => z * (x * r * x⁻¹)) hconj
      simpa [mul_assoc] using h3
    exact h1.symm
  have h1 : x * r ∈ M A z := Subgroup.mul_mem (M A z) hxM hr.1
  have h2 : x * r * x⁻¹ ∈ M A z := Subgroup.mul_mem (M A z) h1 (Subgroup.inv_mem (M A z) hxM)
  exact ⟨h2, hcent⟩

private theorem delta_range_invariant (h : Hyp G L A T z t) :
    ∀ g ∈ autImage L A, ∀ a ∈ (deltaHom fun m hm => h.conj_mem hm).range,
      g a ∈ (deltaHom fun m hm => h.conj_mem hm).range := by
  rintro g ⟨x, rfl⟩ a ⟨r, rfl⟩
  refine ⟨⟨(x : G) * (r : G) * (x : G)⁻¹, h.R₀_conj_mem x.2 r.2⟩, ?_⟩
  apply Subtype.ext
  rw [coe_deltaHom_apply, Hyp.delta_conj h x.2.1, conjN_apply, coe_deltaHom_apply]
  rfl

private theorem delta_range_eq_bot_or_top (h : Hyp G L A T z t) :
    (deltaHom fun m hm => h.conj_mem hm).range = ⊥ ∨
      (deltaHom fun m hm => h.conj_mem hm).range = ⊤ := by
  refine h.jc.module.irreducible_derived (deltaHom fun m hm => h.conj_mem hm).range ?_
  intro g hg u hu
  have hgQ : g ∈ autImage L A := by
    have h1 := Subgroup.commutator_le_sup (autImage L A) (autImage L A) hg
    rwa [sup_idem] at h1
  exact delta_range_invariant h g hgQ u hu

private theorem card_eq_card_orbit_mul_card_stabilizer (M : Subgroup G) (z : G) :
    Nat.card ↥M =
      Nat.card {g : G // ∃ m : ↥M, (m : G) * z * (m : G)⁻¹ = g} *
        Nat.card ↥(M ⊓ centralizer ({z} : Set G)) := by
  classical
  letI : MulAction ↥M G := MulAction.compHom G (MulAut.conj.comp M.subtype)
  haveI hM : Fintype ↥M := Fintype.ofFinite _
  haveI ho : Fintype ↥(MulAction.orbit ↥M z) := Fintype.ofFinite _
  haveI hs : Fintype ↥(MulAction.stabilizer ↥M z) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥M) (X := G) z
  have horb : Nat.card ↥(MulAction.orbit ↥M z) =
      Nat.card {g : G // ∃ m : ↥M, (m : G) * z * (m : G)⁻¹ = g} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => ?_))
    rw [MulAction.mem_orbit_iff]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, by rw [← hm]; rfl⟩, fun ⟨m, hm⟩ => ⟨m, hm⟩⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥M z) =
      Nat.card ↥(M ⊓ centralizer ({z} : Set G)) := by
    have hmap : (MulAction.stabilizer ↥M z).map M.subtype =
        M ⊓ centralizer ({z} : Set G) := by
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        change (m : G) * z * (m : G)⁻¹ = z at hm
        refine ⟨m.2, mem_centralizer_singleton_iff.mpr ?_⟩
        calc (m : G) * z = ((m : G) * z * (m : G)⁻¹) * (m : G) := by group
          _ = z * (m : G) := by rw [hm]
      · rintro ⟨hxM, hxC⟩
        refine ⟨⟨x, hxM⟩, ?_, rfl⟩
        change (⟨x, hxM⟩ : ↥M) • z = z
        have h1 : x * z = z * x := mem_centralizer_singleton_iff.mp hxC
        calc (⟨x, hxM⟩ : ↥M) • z = x * z * x⁻¹ := rfl
          _ = z := by rw [h1]; group
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := M.subtype) M.subtype_injective).symm
  have h' : Nat.card (MulAction.orbit ↥M z) *
      Nat.card (MulAction.stabilizer ↥M z) = Nat.card ↥M := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact h
  calc Nat.card ↥M = Nat.card (MulAction.orbit ↥M z) *
        Nat.card (MulAction.stabilizer ↥M z) := h'.symm
    _ = Nat.card {g : G // ∃ m : ↥M, (m : G) * z * (m : G)⁻¹ = g} *
        Nat.card ↥(M ⊓ centralizer ({z} : Set G)) := by rw [horb, hstab]

theorem Hyp.conjN_ker (h : Hyp G L A T z t) :
    (conjN L A).ker = A.subgroupOf (L ⊓ normalizer (A : Set G)) := by
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx1
    have hxC : (x : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h2 : (conjN L A) x ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hx1]; rfl
      have h3 : (x : G) * a * (x : G)⁻¹ = a := by
        simpa [conjN_apply] using congrArg (fun z : ↥A => (z : G)) h2
      have h4 : (x : G) * a = a * (x : G) := by
        calc (x : G) * a = (x : G) * a * (x : G)⁻¹ * (x : G) := by group
          _ = a * (x : G) := by rw [h3]
      exact h4.symm
    exact le_of_eq h.jc.centralizer_eq
      (show (x : G) ∈ L ⊓ centralizer (A : Set G) from ⟨x.2.1, hxC⟩)
  · intro hxA
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    show (x : G) * (a : G) * (x : G)⁻¹ = (a : G)
    have hcomm : (x : G) * (a : G) = (a : G) * (x : G) :=
      congrArg Subtype.val (mul_comm' (⟨(x : G), hxA⟩ : ↥A) a)
    rw [hcomm]
    group

theorem Hyp.card_N_L (h : Hyp G L A T z t) :
    Nat.card ↥(L ⊓ normalizer (A : Set G)) = 2 ^ 10 * 887040 := by
  have hcard := Subgroup.card_ker_mul_card_range (conjN L A)
  rw [h.conjN_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_inf h.jc.le Subgroup.le_normalizer)).toEquiv,
    h.jc.module.card] at hcard
  have hQ : Nat.card ↥(conjN L A).range = 887040 := h.jc.module.card_Q
  rw [hQ] at hcard
  exact hcard.symm

theorem Hyp.card_centralizer_M (h : Hyp G L A T z t) :
    Nat.card ↥(M A z ⊓ centralizer ({z} : Set G)) = 2 ^ 11 * 887040 := by
  rw [h.M_inf_centralizer]
  have hd : Disjoint (L ⊓ normalizer (A : Set G)) (zpowers z) :=
    h.set.disjoint.mono_left inf_le_left
  have hcomm : zpowers z ≤ centralizer ((L ⊓ normalizer (A : Set G)) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    exact h.commute_of_mem hy.1
  have h1 : Nat.card ↥((L ⊓ normalizer (A : Set G)) ⊔ zpowers z) =
      Nat.card ↥(L ⊓ normalizer (A : Set G)) * 2 := by
    rw [← Nat.card_congr (mulEquivProdSup hcomm hd).toEquiv, Nat.card_prod, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact h.set.z_sq) h.set.z_ne]
  rw [h1, h.card_N_L]
  norm_num

private theorem delta_range_eq_top (h : Hyp G L A T z t) :
    (deltaHom fun m hm => h.conj_mem hm).range = ⊤ := by
  classical
  let ψ : ↥(M A z) →* MulAut ↥A :=
    A.normalizerMonoidHom.comp (Subgroup.inclusion h.M_le_normalizer)
  have hψapply : ∀ (m : ↥(M A z)) (a : ↥A),
      ((ψ m a : ↥A) : G) = (m : G) * (a : G) * (m : G)⁻¹ := fun m a => rfl
  have hψker : ψ.ker = (R₀ A z).subgroupOf (M A z) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hm1
      have hC : (m : G) ∈ centralizer (A : Set G) := by
        rw [mem_centralizer_iff]
        intro a ha
        have h2 : ψ m ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hm1]; rfl
        have h3 : (m : G) * a * (m : G)⁻¹ = a := by
          rw [← hψapply m ⟨a, ha⟩]
          exact congrArg (fun z : ↥A => (z : G)) h2
        have h4 : (m : G) * a = a * (m : G) := by
          calc (m : G) * a = (m : G) * a * (m : G)⁻¹ * (m : G) := by group
            _ = a * (m : G) := by rw [h3]
        exact h4.symm
      exact ⟨m.2, hC⟩
    · rintro ⟨-, hC⟩
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      show (m : G) * (a : G) * (m : G)⁻¹ = (a : G)
      have h1 : (a : G) * (m : G) = (m : G) * (a : G) := mem_centralizer_iff.1 hC a a.2
      rw [← h1]
      group
  have hψker_card : Nat.card ↥(ψ.ker) = Nat.card ↥(R₀ A z) := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : R₀ A z ≤ M A z)).toEquiv
  have hQ_le : autImage L A ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨(x : G), h.le_M x.2⟩, rfl⟩
  let Orb : Set G := {g | ∃ m : ↥(M A z), (m : G) * z * (m : G)⁻¹ = g}
  rcases delta_range_eq_bot_or_top h with hbot | htop
  · exfalso
    have hR₀ : R₀ A z = B A z := by
      refine le_antisymm ?_ h.B_le_R₀
      intro r hr
      have h1 : (⟨r, hr⟩ : ↥(R₀ A z)) ∈
          (deltaHom fun m hm => h.conj_mem hm).ker := by
        rw [MonoidHom.mem_ker]
        have h2 : (deltaHom fun m hm => h.conj_mem hm) ⟨r, hr⟩ ∈
            (deltaHom fun m hm => h.conj_mem hm).range := ⟨_, rfl⟩
        rw [hbot] at h2
        simpa using h2
      rw [deltaHom_ker h] at h1
      exact h1
    have hcardR : Nat.card ↥(R₀ A z) = 2 ^ 11 := by rw [hR₀]; exact h.card_B
    have hM1 : Nat.card ↥(M A z) = Nat.card ↥Orb * (2 ^ 11 * 887040) := by
      have h1 := card_eq_card_orbit_mul_card_stabilizer (M A z) z
      rw [h.card_centralizer_M] at h1
      exact h1
    have hM2 : Nat.card ↥(M A z) = Nat.card ↥(R₀ A z) * Nat.card ↥(ψ.range) := by
      rw [← hψker_card]
      exact (Subgroup.card_ker_mul_card_range ψ).symm
    have hX : Nat.card ↥(ψ.range) = Nat.card ↥Orb * 887040 := by
      have hEq : Nat.card ↥Orb * (2 ^ 11 * 887040) =
          Nat.card ↥(R₀ A z) * Nat.card ↥(ψ.range) := by rw [← hM1, hM2]
      rw [hcardR] at hEq
      set O := Nat.card ↥Orb with hO
      set X := Nat.card ↥(ψ.range) with hX'
      change X = O * 887040
      have hEq' : (O * 887040) * 2 ^ 11 = X * 2 ^ 11 := by
        calc (O * 887040) * 2 ^ 11 = O * (2 ^ 11 * 887040) := by ring
          _ = 2 ^ 11 * X := hEq
          _ = X * 2 ^ 11 := by ring
      omega
    let S : Set ↥A := {a | a ≠ 1 ∧ z * (a : G) ∈ Orb}
    have hS1 : 1 ∉ S := fun h1 => h1.1 rfl
    have hSinv : ∀ g ∈ autImage L A, ∀ s ∈ S, g s ∈ S := by
      rintro g ⟨x, rfl⟩ s ⟨hs1, hs2⟩
      have hxM : (x : G) ∈ M A z := h.le_M x.2
      refine ⟨?_, ?_⟩
      · intro h0
        apply hs1
        have h0' : s = 1 := by
          have := congrArg (fun t : ↥A => ((conjN L A x)⁻¹) t) h0
          simpa using this
        exact h0'
      · obtain ⟨m, hm⟩ := hs2
        refine ⟨⟨(x : G) * (m : G) * (x : G)⁻¹, ?_⟩, ?_⟩
        · exact Subgroup.mul_mem (M A z) (Subgroup.mul_mem (M A z) hxM m.2)
            (Subgroup.inv_mem (M A z) hxM)
        · have hxinvz : (x : G)⁻¹ * z * (x : G) = z := by
            have h1 : (x : G)⁻¹ * z = z * (x : G)⁻¹ :=
              (Commute.inv_left (show Commute (x : G) z from h.commute_of_mem x.2.1)).eq
            rw [h1]
            group
          have hxsz : (((conjN L A x) s : ↥A) : G) = (x : G) * (s : G) * (x : G)⁻¹ :=
            conjN_apply (L := L) (A := A) x s
          rw [hxsz]
          calc (x : G) * (m : G) * (x : G)⁻¹ * z * ((x : G) * (m : G) * (x : G)⁻¹)⁻¹
              = (x : G) * (m : G) * ((x : G)⁻¹ * z * (x : G)) * (m : G)⁻¹ * (x : G)⁻¹ := by
                group
            _ = (x : G) * (m : G) * z * (m : G)⁻¹ * (x : G)⁻¹ := by rw [hxinvz]
            _ = (x : G) * ((m : G) * z * (m : G)⁻¹) * (x : G)⁻¹ := by group
            _ = (x : G) * (z * (s : G)) * (x : G)⁻¹ := by rw [hm]
            _ = z * ((x : G) * (s : G) * (x : G)⁻¹) := by
                calc (x : G) * (z * (s : G)) * (x : G)⁻¹
                    = ((x : G) * z * (x : G)⁻¹) *
                        ((x : G) * (s : G) * (x : G)⁻¹) := by group
                  _ = z * ((x : G) * (s : G) * (x : G)⁻¹) := by
                      rw [show (x : G) * z * (x : G)⁻¹ = z from by
                        rw [h.commute_of_mem x.2.1]; group]
    have hSncard := h.jc.module.invariant_ncard S hS1 hSinv
    have hOrb_eq : Orb = (fun a : ↥A => z * (a : G)) '' (S ∪ ({1} : Set ↥A)) := by
      ext g
      constructor
      · intro hg
        obtain ⟨m, hm⟩ := hg
        have hgB : g ∈ B A z := by
          have h1 : g = m * z * m⁻¹ := hm.symm
          rw [h1]
          have hmM : (m : G) ∈ M A z := m.2
          exact (mem_normalizer_iff.1 hmM z).1 (mem_sup_right (mem_zpowers z))
        have hgA : g ∉ A := by
          intro hgA
          exact h.not_conj g (h.jc.le hgA) (isConj_iff.2 ⟨(m : G), hm⟩)
        obtain ⟨a, ha, b, hb, hgab⟩ :=
          exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer_A hgB
        rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with hb1 | hbz
        · exfalso
          apply hgA
          rw [hgab, hb1, mul_one]
          exact ha
        · have hga : g = a * z := by rw [hgab, hbz]
          have hza : z * a = g := by
            rw [hga]
            exact (h.commute_of_mem (h.jc.le ha)).symm
          refine ⟨⟨a, ha⟩, ?_, hza⟩
          by_cases ha1 : a = 1
          · exact Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext ha1))
          · exact Or.inl ⟨fun hcon => ha1 (congrArg Subtype.val hcon),
              ⟨m, by rw [hza]; exact hm⟩⟩
      · rintro ⟨a, ha, rfl⟩
        rcases ha with ⟨-, haOrb⟩ | ha1
        · exact haOrb
        · have ha' : a = 1 := Set.mem_singleton_iff.mp ha1
          have hz1 : z * (a : G) = z := by rw [ha', Subgroup.coe_one, mul_one]
          show z * (a : G) ∈ Orb
          rw [hz1]
          exact ⟨1, by simp⟩
    have hOrbS : Nat.card ↥Orb = S.ncard + 1 := by
      rw [hOrb_eq]
      have hinj : Function.Injective (fun a : ↥A => z * (a : G)) := by
        intro a b hab
        have h1 := congrArg (fun y : G => z⁻¹ * y) hab
        simpa [mul_assoc] using h1
      rw [Nat.card_coe_set_eq, Set.ncard_image_of_injective _ hinj]
      have hun : S ∪ ({1} : Set ↥A) = insert 1 S := by
        ext x
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
        tauto
      rw [hun, Set.ncard_insert_of_notMem hS1]
    have hX2 : Nat.card ↥(ψ.range) = (S.ncard + 1) * 887040 := by rw [hX, hOrbS]
    have h31 : ¬ 31 ∣ Nat.card ↥(ψ.range) := by
      rw [hX2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSncard
      rcases hSncard with h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
    have h37 : ¬ 37 ∣ Nat.card ↥(ψ.range) := by
      rw [hX2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSncard
      rcases hSncard with h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
    have h43 : ¬ 43 ∣ Nat.card ↥(ψ.range) := by
      rw [hX2]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSncard
      rcases hSncard with h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
    have hover : ψ.range = autImage L A :=
      h.jc.module.overgroup ψ.range hQ_le h31 h37 h43
    have hcardX : Nat.card ↥(ψ.range) = 887040 := by
      rw [hover, h.jc.module.card_Q]
    have hS0 : S.ncard = 0 := by
      have h3 : (S.ncard + 1) * 887040 = 1 * 887040 := by rw [← hX2, hcardX]
      have h4 : S.ncard + 1 = 1 := by omega
      omega
    have hOrb1 : Nat.card ↥Orb = 1 := by rw [hOrbS, hS0]
    have hzOrb : z ∈ Orb := ⟨1, by simp⟩
    obtain ⟨n, hnM, hnz⟩ := h.exists_conj_z_eq_tz
    have htzOrb : t * z ∈ Orb := ⟨⟨n, hnM⟩, hnz⟩
    have hne : (⟨z, hzOrb⟩ : ↥Orb) ≠ ⟨t * z, htzOrb⟩ := by
      intro hcon
      have h1 : z = t * z := congrArg Subtype.val hcon
      have h2 : t = 1 := by
        have h3 := congrArg (fun y : G => y * z⁻¹) h1
        have h4 : (1 : G) = t := by simpa [mul_assoc] using h3
        exact h4.symm
      exact h.set.t_ne h2
    haveI : Nontrivial ↥Orb := ⟨⟨⟨z, hzOrb⟩, ⟨t * z, htzOrb⟩, hne⟩⟩
    have h2 : 1 < Nat.card ↥Orb := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  · exact htop

theorem Hyp.e2Facts (h : Hyp G L A T z t) : E2Facts L A z where
  centralizer_B := h.centralizer_B
  M_inf_centralizer := h.M_inf_centralizer
  M_le := h.M_le_normalizer
  conj_mem := fun m hm => h.conj_mem hm
  conj_surj := by
    intro a ha
    have hsurj : (deltaHom fun m hm => h.conj_mem hm).range = ⊤ := delta_range_eq_top h
    have hmem : (⟨a, ha⟩ : ↥A) ∈ (deltaHom fun m hm => h.conj_mem hm).range := by
      rw [hsurj]
      exact Subgroup.mem_top _
    obtain ⟨r, hr⟩ := hmem
    refine ⟨(r : G), r.2, ?_⟩
    have hr' : (((deltaHom fun m hm => h.conj_mem hm) r : ↥A) : G) = a :=
      congrArg Subtype.val hr
    have h1 : (((deltaHom fun m hm => h.conj_mem hm) r : ↥A) : G) = delta z (r : G) :=
      coe_deltaHom_apply _ r
    rw [h1] at hr'
    simp only [delta] at hr'
    calc (r : G) * z * (r : G)⁻¹ = z * (z⁻¹ * ((r : G) * z * (r : G)⁻¹)) := by group
      _ = z * a := by rw [hr']
  card_R₀ := by
    have hsurj : (deltaHom fun m hm => h.conj_mem hm).range = ⊤ := delta_range_eq_top h
    have hcard := Subgroup.card_ker_mul_card_range (deltaHom fun m hm => h.conj_mem hm)
    rw [deltaHom_ker h, hsurj] at hcard
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.B_le_R₀).toEquiv,
      h.card_B, Subgroup.card_top, h.jc.module.card] at hcard
    rw [← hcard]
    norm_num

end CFSG.EvenSporadicStandard.Co2Std.Exclusion

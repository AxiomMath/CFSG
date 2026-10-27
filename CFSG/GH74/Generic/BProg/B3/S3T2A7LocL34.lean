module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.KGroups.CoverL34

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Blueprint CFSG.GH74 Subgroup

theorem exists_elem_preimage
    {K J : Type} [Group K] [Group J] (π : K →* J) (hπ : Function.Surjective π)
    (hZc : ∀ w ∈ π.ker, ∀ g : K, g * w = w * g) (hZ2 : ∀ w ∈ π.ker, w ^ 2 = 1)
    (hJ : LieModel J .PSL 3 2 2) :
    ∃ A : Subgroup K, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 16 * Nat.card π.ker := by
  obtain ⟨e⟩ := KGroups.L34.equiv_of_lieModel hJ
  have hind := KGroups.indepCheck_sound KGroups.L34.indep_ok
  have hA := KGroups.preimage_elementary_model π hπ π.ker rfl hZc hZ2
    KGroups.L34.QP.originalSubgroup e KGroups.L34.QE.originalSubgroup KGroups.L34.QE_le
    (KGroups.sqOneCheck_sound _ KGroups.L34.QE_ok KGroups.L34.QE_sq) KGroups.L34.eg0
    (KGroups.conj_of_words _ _ KGroups.L34.gens_mem _ KGroups.L34.QE_ok KGroups.L34.conj_ok)
    KGroups.L34.eg0 KGroups.L34.eg1 KGroups.L34.eg2 KGroups.L34.mem0 KGroups.L34.mem1
    KGroups.L34.mem2 hind.1 hind.2.1 hind.2.2.1 hind.2.2.2.1 hind.2.2.2.2.1 hind.2.2.2.2.2.1
    hind.2.2.2.2.2.2
  refine ⟨_, ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ((hA a a.2).2 b b.2),
    fun a ha => (hA a ha).1⟩, ?_⟩
  have hQE : Nat.card KGroups.L34.QE.originalSubgroup = 16 := by
    rw [KGroups.card_group _ KGroups.L34.QE_ok, KGroups.L34.QE_valid.2]
  have hcardE : Nat.card ((KGroups.L34.QE.originalSubgroup.subgroupOf
      KGroups.L34.QP.originalSubgroup).comap e.toMonoidHom) = 16 := by
    rw [KGroups.card_comap_of_surjective e.toMonoidHom e.surjective]
    have h1 : Nat.card e.toMonoidHom.ker = 1 := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
      simp
    rw [h1, mul_one, ← hQE]
    exact Nat.card_congr (subgroupOfEquivOfLe KGroups.L34.QE_le).toEquiv
  rw [KGroups.card_comap_of_surjective π hπ, hcardE]

theorem false_of_center
    {J : Type} [Group J] [Finite J] (hJ : SectionalTwoRankLE J 4)
    (hL : LieModel (J ⧸ center J) .PSL 3 2 2) {z : J} (hz : z ∈ center J) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : False := by
  let Q : Subgroup J :=
    { carrier := {x | ∃ c ∈ center J, c ^ 2 = x}
      mul_mem' := by
        rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
        exact ⟨c * d, mul_mem hc hd, (Commute.mul_pow (mem_center_iff.mp hd c) 2)⟩
      one_mem' := ⟨1, one_mem _, one_pow 2⟩
      inv_mem' := by
        rintro _ ⟨c, hc, rfl⟩
        exact ⟨c⁻¹, inv_mem hc, inv_pow c 2⟩ }
  have hQZ : Q ≤ center J := by
    rintro _ ⟨c, hc, rfl⟩
    exact pow_mem hc 2
  have hQn : Q.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hQZ hx) g, mul_inv_cancel_right]
    exact hx⟩
  let π : J ⧸ Q →* J ⧸ center J :=
    QuotientGroup.map Q (center J) (MonoidHom.id J) fun x hx => hQZ hx
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(g : J ⧸ Q), rfl⟩
  have hker : ∀ x : J, (x : J ⧸ Q) ∈ π.ker ↔ x ∈ center J := fun x => by
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff x
  have hZc : ∀ w ∈ π.ker, ∀ g : J ⧸ Q, g * w = w * g := by
    intro w hw g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp ((hker x).mp hw) y]
  have hZ2 : ∀ w ∈ π.ker, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨x, (hker x).mp hw, rfl⟩
  obtain ⟨y, hyZ, hyQ⟩ : ∃ y ∈ center J, y ∉ Q := by
    by_contra hcon
    have hall : ∀ y ∈ center J, y ∈ Q := fun y hy => by
      by_contra hyQ
      exact hcon ⟨y, hy, hyQ⟩
    let s : ↥(center J) → ↥(center J) := fun c => ⟨c ^ 2, pow_mem c.2 2⟩
    have hs : Function.Surjective s := fun c => by
      obtain ⟨d, hd, hdc⟩ := hall c c.2
      exact ⟨⟨d, hd⟩, Subtype.ext hdc⟩
    have hinj := Finite.injective_iff_surjective.mpr hs
    have h1 : s ⟨z, hz⟩ = s 1 := Subtype.ext (by simp [s, hz2])
    exact hz1 (congrArg Subtype.val (hinj h1))
  have hker1 : 1 < Nat.card π.ker := by
    rw [one_lt_card_iff_ne_bot]
    intro hbot
    have hy := (hker y).mpr hyZ
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at hy
    exact hyQ hy
  obtain ⟨A, hA, hcard⟩ := exists_elem_preimage π hπ hZc hZ2 hL
  have hle := (hJ.quotient Q).card_le_of_elementary A hA
  omega

theorem eq_one_or_eq_of_mem_zpowers {Y : Type} [Group Y] {z c : Y} (hz2 : z ^ 2 = 1)
    (hc : c ∈ zpowers z) : c = 1 ∨ c = z := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hzz, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hzz, one_zpow, one_mul]

theorem sq_eq_one_of_mem_zpowers {Y : Type} [Group Y] {z c : Y} (hz2 : z ^ 2 = 1)
    (hc : c ∈ zpowers z) : c ^ 2 = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers hz2 hc with rfl | rfl
  · exact one_pow 2
  · exact hz2

theorem false_of_not_mem
    {Y : Type} [Group Y] [Finite Y] (hY : SectionalTwoRankLE Y 4) (L : Subgroup Y)
    (hL : LieModel (↥L ⧸ center ↥L) .PSL 3 2 2) {z : Y} (hzc : z ∈ center Y)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hz : z ∉ L) : False := by
  have hZz : zpowers z ≤ center Y := zpowers_le.mpr hzc
  have hcomm : ∀ (l : ↥L) (c : ↥(zpowers z)), Commute (L.subtype l) ((zpowers z).subtype c) :=
    fun l c => mem_center_iff.mp (hZz c.2) l
  let Φ : ↥L × ↥(zpowers z) →* Y := L.subtype.noncommCoprod (zpowers z).subtype hcomm
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨l, c⟩ h
    have h' : (l : Y) * c = 1 := h
    rcases eq_one_or_eq_of_mem_zpowers hz2 c.2 with hc | hc
    · rw [hc, mul_one] at h'
      exact Prod.ext (Subtype.ext h') (Subtype.ext hc)
    · exfalso
      apply hz
      rw [← hc, eq_inv_of_mul_eq_one_right h']
      exact inv_mem l.2
  have h1 : SectionalTwoRankLE (↥L × ↥(zpowers z)) 4 := SectionalTwoRankLE.of_injective Φ hΦ hY
  let ρ : ↥L × ↥(zpowers z) →* (↥L ⧸ center ↥L) × ↥(zpowers z) :=
    (QuotientGroup.mk' (center ↥L)).prodMap (MonoidHom.id _)
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, c⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center ↥L) q
    exact ⟨(l, c), rfl⟩
  have h2 := SectionalTwoRankLE.of_surjective ρ hρ h1
  let π := MonoidHom.fst (↥L ⧸ center ↥L) ↥(zpowers z)
  have hπ : Function.Surjective π := fun q => ⟨(q, 1), rfl⟩
  have hmem : ∀ w ∈ π.ker, w.1 = 1 := fun w hw => hw
  have hZc : ∀ w ∈ π.ker, ∀ g, g * w = w * g := by
    intro w hw g
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hmem w hw]
    · exact mem_center_iff.mp (hZz w.2.2) g.2
  have hZ2 : ∀ w ∈ π.ker, w ^ 2 = 1 := by
    intro w hw
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hmem w hw]
    · simpa using sq_eq_one_of_mem_zpowers hz2 w.2.2
  have hker1 : 1 < Nat.card π.ker := by
    rw [one_lt_card_iff_ne_bot]
    intro hbot
    have hw : ((1 : ↥L ⧸ center ↥L), (⟨z, mem_zpowers z⟩ : ↥(zpowers z))) ∈ π.ker := rfl
    rw [hbot, mem_bot] at hw
    exact hz1 (congrArg (fun w => (w.2 : Y)) hw)
  obtain ⟨A, hA, hcard⟩ := exists_elem_preimage π hπ hZc hZ2 hL
  have hle := h2.card_le_of_elementary A hA
  omega

theorem cell125_L34 :
    S3T2A7.Cell125 S3T2A7.L34 := by
  intro Y _ _ L B X₀ z hS hL _ _
  have := hS.B_el
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B) z hS.z_mem
  by_cases hzL : z ∈ L
  · have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hS.z_cent g)
    exact false_of_center (hS.sec4.subgroup L) hL hzc (by ext; simpa using hz2)
      (fun h => hS.z_ne (congrArg Subtype.val h))
  · exact false_of_not_mem hS.sec4 L hL hS.z_cent hz2 hS.z_ne hzL

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

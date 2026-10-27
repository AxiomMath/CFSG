module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSection
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdStandard

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (centralizer (S : Set G) : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro c
  simp only [mem_centralizer_iff]
  constructor
  · intro hc s hs
    have hs' : y⁻¹ * s * y ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem hy) s).mp hs
      simpa using this
    have h := hc _ hs'
    calc s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by rw [h]
      _ = y * c * y⁻¹ * s := by group
  · intro hc s hs
    have hs' : y * s * y⁻¹ ∈ S := (mem_normalizer_iff.mp hy s).mp hs
    have h := hc _ hs'
    have h2 : y * (s * c) * y⁻¹ = y * (c * s) * y⁻¹ := by
      calc y * (s * c) * y⁻¹ = y * s * y⁻¹ * (y * c * y⁻¹) := by group
        _ = y * c * y⁻¹ * (y * s * y⁻¹) := h
        _ = y * (c * s) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem conjugate_eq_of_mem_normalizer {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : conjugate X g = X := by
  ext y
  rw [mem_conjugate_iff]
  exact (mem_normalizer_iff.mp hg y).symm

theorem eq_of_le_normalizer {J L : Subgroup H} (hJ : IsQuasisimple J) (hL : IsQuasisimple L)
    (hJL : J ≤ L) (hn : L ≤ normalizer (J : Set H)) : J = L := by
  have : (J.subgroupOf L).Normal :=
    (normal_subgroupOf_iff hJL).mpr fun j l hj hl => (mem_normalizer_iff.mp (hn hl) j).mp hj
  rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hL (J.subgroupOf L) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQuasisimple hJ
    apply hab
    have ha : (⟨a, hJL a.2⟩ : L) ∈ center L := h (mem_subgroupOf.mpr a.2)
    have := congrArg Subtype.val ((mem_center_iff.mp ha) ⟨b, hJL b.2⟩)
    exact Subtype.ext this.symm
  · refine le_antisymm hJL fun l hl => ?_
    have : (⟨l, hl⟩ : L) ∈ J.subgroupOf L := h ▸ mem_top _
    exact mem_subgroupOf.mp this

variable {L J : Subgroup H}

theorem secπ_mem_centralizer {c : secN L} (hc : (c : H) ∈ centralizer (J : Set H)) :
    secπ L c ∈ centralizer (secImg L J : Set (secN L ⧸ secD L)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [coe_mul]
  exact (mem_centralizer_iff.mp hc) j (mem_subgroupOf.mp hj)

theorem exists_of_mem_centralizer_secImg (hJL : J ≤ L) (hJ : ⁅J, J⁆ = J)
    {y : secN L ⧸ secD L} (hy : y ∈ centralizer (secImg L J : Set (secN L ⧸ secD L))) :
    ∃ c : secN L, (c : H) ∈ centralizer (J : Set H) ∧ secπ L c = y := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (secD L) y
  exact ⟨c, mem_centralizer_of_secπ_mem hJL hJ hy, rfl⟩

theorem secπ_mem_normalizer {g : secN L} (hg : (g : H) ∈ normalizer (J : Set H)) :
    secπ L g ∈ normalizer (secImg L J : Set (secN L ⧸ secD L)) := by
  apply le_normalizer_map (secπ L)
  refine mem_map_of_mem _ ?_
  rw [mem_normalizer_iff]
  intro h
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [coe_mul, coe_inv]
  exact mem_normalizer_iff.mp hg h

theorem orderOf_secπ_eq_two {t : secN L} (ht2 : orderOf (t : H) = 2)
    (htL : (t : H) ∉ centralizer (L : Set H)) : orderOf (secπ L t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · have h1 : (t : H) ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one _
    have h : t ^ 2 = 1 := Subtype.ext (by simpa using h1)
    rw [← map_pow, h, map_one]
  · intro h
    exact htL ((secπ_eq_one_iff t).mp h)

theorem odd_card_inf_conjugate_secImg (hJ : IsStandardSubgroup J) (hJL : J ≤ L) {g : secN L}
    (hg : (g : H) ∉ normalizer (centralizer (J : Set H) : Set H)) :
    Odd (Nat.card ↥(centralizer (secImg L J : Set (secN L ⧸ secD L)) ⊓
      conjugate (centralizer (secImg L J : Set (secN L ⧸ secD L))) (secπ L g))) := by
  have hJp := commutator_self_eq_of_isQuasisimple hJ.1
  set CJ := centralizer (J : Set H) with hCJ
  set P : Subgroup (secN L) := (CJ ⊓ conjugate CJ g).subgroupOf (secN L) with hP
  have hle : centralizer (secImg L J : Set (secN L ⧸ secD L)) ⊓
      conjugate (centralizer (secImg L J : Set (secN L ⧸ secD L))) (secπ L g) ≤
        P.map (secπ L) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    obtain ⟨c, hc, rfl⟩ := exists_of_mem_centralizer_secImg hJL hJp hy1
    refine ⟨c, mem_subgroupOf.mpr (mem_inf.mpr ⟨hc, ?_⟩), rfl⟩
    rw [mem_conjugate_iff] at hy2 ⊢
    have h1 : secπ L (g * c * g⁻¹) ∈ centralizer (secImg L J : Set (secN L ⧸ secD L)) := by
      rwa [map_mul, map_mul, map_inv]
    have h2 := mem_centralizer_of_secπ_mem hJL hJp h1
    simpa using h2
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.card_map_dvd P (secπ L)
  have h3 : Nat.card P ∣ Nat.card ↥(CJ ⊓ conjugate CJ g) := by
    have : Nat.card P = Nat.card ↥((CJ ⊓ conjugate CJ g) ⊓ secN L) := by
      rw [← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective (secN L).subtype_injective]
    rw [this]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat (hJ.2.2.1 g hg) (h1.trans (h2.trans h3))

theorem isStandardSubgroup_secImg (hJ : IsStandardSubgroup J) (hJL : J ≤ L) {t : H}
    (htN : t ∈ secN L) (htJ : t ∈ centralizer (J : Set H)) (ht2 : orderOf t = 2)
    (htL : t ∉ centralizer (L : Set H)) : IsStandardSubgroup (secImg L J) := by
  have hJp := commutator_self_eq_of_isQuasisimple hJ.1
  have hJN : J ≤ secN L := hJL.trans (le_secN L)
  set CJb := centralizer (secImg L J : Set (secN L ⧸ secD L)) with hCJb
  have htb : secπ L ⟨t, htN⟩ ∈ CJb := secπ_mem_centralizer htJ
  have htb2 : orderOf (secπ L ⟨t, htN⟩) = 2 := orderOf_secπ_eq_two ht2 htL
  have heven : Even (Nat.card CJb) :=
    even_iff_two_dvd.mpr (htb2 ▸ Subgroup.orderOf_dvd_natCard _ htb)
  have hkey : ∀ g : secN L, secπ L g ∈ normalizer (CJb : Set (secN L ⧸ secD L)) →
      (g : H) ∈ normalizer (centralizer (J : Set H) : Set H) := by
    intro g hg
    by_contra hg'
    have hodd := odd_card_inf_conjugate_secImg hJ hJL hg'
    rw [← hCJb, conjugate_eq_of_mem_normalizer hg, inf_idem] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  refine ⟨?_, heven, ?_, ?_, ?_⟩
  ·
    refine LieType.CurtisTits.isQuasisimple_of_surjective hJ.1 (secRes_surjective hJN) ?_
    by_contra hall
    push Not at hall
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQuasisimple hJ.1
    apply hab
    have ha := (secRes_eq_one_iff hJN a).mp (hall a)
    exact Subtype.ext ((mem_centralizer_iff.mp ha) b (hJL b.2)).symm
  ·
    intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (secD L) gb
    refine odd_card_inf_conjugate_secImg hJ hJL fun hg => hgb ?_
    exact normalizer_le_normalizer_centralizer _ (secπ_mem_normalizer (hJ.2.2.2.1 ▸ hg))
  ·
    refine le_antisymm (fun gb hgb => ?_) (normalizer_le_normalizer_centralizer _)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (secD L) gb
    exact secπ_mem_normalizer (hJ.2.2.2.1 ▸ hkey g hgb)
  ·
    intro gb hcomm
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (secD L) gb
    apply hJ.2.2.2.2 (g : H)
    refine commutator_eq_bot_of_le_of_perfect (M := L ⊓ centralizer (L : Set H)) hJp
      (fun m hm => mem_centralizer_iff.mpr fun j hj =>
        (mem_centralizer_iff.mp (mem_inf.mp hm).2 j (hJL hj))) ?_
    rw [commutator_le]
    intro j hj x hx
    rw [mem_conjugate_iff] at hx
    have hxL : x ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem g.2) _).mp (hJL hx)
      simpa [mul_assoc] using this
    have hxN : x ∈ secN L := le_secN L hxL
    have hjN : j ∈ secN L := le_secN L (hJL hj)
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem (hJL hj) hxL) (L.inv_mem (hJL hj))) (L.inv_mem hxL)
    · have h1 : secπ L ⟨j, hjN⟩ ∈ secImg L J := secπ_mem_secImg hj
      have h2 : secπ L ⟨x, hxN⟩ ∈ conjugate (secImg L J) (secπ L g) := by
        rw [mem_conjugate_iff, ← map_inv, ← map_mul, ← map_mul]
        exact secπ_mem_secImg (by simpa using hx)
      have h3 := commutator_mem_commutator h1 h2
      rw [hcomm, mem_bot, ← map_commutatorElement, secπ_eq_one_iff] at h3
      have he : ((⁅(⟨j, hjN⟩ : secN L), ⟨x, hxN⟩⁆ : secN L) : H) = ⁅j, x⁆ := by
        simp [commutatorElement_def]
      rw [← he]
      exact h3

theorem secImg_ne_secImg_self (hJ : IsQuasisimple J) (hL : IsQuasisimple L) (hJL : J ≤ L)
    (hne : J ≠ L) : secImg L J ≠ secImg L L := by
  intro heq
  refine hne (eq_of_le_normalizer hJ hL hJL fun l hl => ?_)
  have hlN : l ∈ secN L := le_secN L hl
  have hl' : secπ L ⟨l, hlN⟩ ∈ secImg L J := heq ▸ secπ_mem_secImg hl
  obtain ⟨j₀, hj₀, hj₀l⟩ := hl'
  have hz : ((j₀⁻¹ * ⟨l, hlN⟩ : secN L) : H) ∈ centralizer (L : Set H) := by
    rw [← secπ_eq_one_iff, map_mul, map_inv, hj₀l, inv_mul_cancel]
  rw [mem_normalizer_iff]
  intro j
  set z : H := ((j₀⁻¹ * ⟨l, hlN⟩ : secN L) : H) with hzdef
  have hlz : l = (j₀ : H) * z := by simp [hzdef]
  have hzc : ∀ y ∈ L, y * z = z * y := fun y hy => (mem_centralizer_iff.mp hz) y hy
  have hj₀J : (j₀ : H) ∈ J := mem_subgroupOf.mp hj₀
  constructor
  · intro hj
    have h1 : l * j * l⁻¹ = (j₀ : H) * j * (j₀ : H)⁻¹ := by
      rw [hlz]
      have := hzc j (hJL hj)
      calc (j₀ : H) * z * j * ((j₀ : H) * z)⁻¹ = (j₀ : H) * (z * j) * z⁻¹ * (j₀ : H)⁻¹ := by
            group
        _ = (j₀ : H) * (j * z) * z⁻¹ * (j₀ : H)⁻¹ := by rw [this]
        _ = (j₀ : H) * j * (j₀ : H)⁻¹ := by group
    rw [h1]
    exact J.mul_mem (J.mul_mem hj₀J hj) (J.inv_mem hj₀J)
  · intro hj
    have hjL : j ∈ L := by
      have h1 : l * j * l⁻¹ ∈ L := hJL hj
      have := L.mul_mem (L.mul_mem (L.inv_mem hl) h1) hl
      simpa [mul_assoc] using this
    have h1 : l * j * l⁻¹ = (j₀ : H) * j * (j₀ : H)⁻¹ := by
      rw [hlz]
      have := hzc j hjL
      calc (j₀ : H) * z * j * ((j₀ : H) * z)⁻¹ = (j₀ : H) * (z * j) * z⁻¹ * (j₀ : H)⁻¹ := by
            group
        _ = (j₀ : H) * (j * z) * z⁻¹ * (j₀ : H)⁻¹ := by rw [this]
        _ = (j₀ : H) * j * (j₀ : H)⁻¹ := by group
    rw [h1] at hj
    have := J.mul_mem (J.mul_mem (J.inv_mem hj₀J) hj) hj₀J
    simpa [mul_assoc] using this

theorem smallSource_secImg {H : Type} [Group H] {L J : Subgroup H} (hJ : IsQuasisimple J)
    (hJL : J ≤ L) (hs : SmallSource J) : SmallSource (secImg L J) := by
  have hJN : J ≤ secN L := hJL.trans (le_secN L)
  have e := LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hJ (secRes_surjective hJN)
    (ker_secRes_le_center hJL)
  have hZ : Odd (Nat.card (center J)) → Odd (Nat.card (center (secImg L J))) := fun h => by
    rw [LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hJ (secRes_surjective hJN)
      (ker_secRes_le_center hJL)]
    exact Odd.of_dvd_nat h (Subgroup.card_map_dvd _ _)
  rcases hs with ⟨p, f, hp, hp2, hf, h5, hm, hodd⟩ | ⟨⟨e7⟩, hodd⟩ | h34
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e hm, hZ hodd⟩
  · exact Or.inr (Or.inl ⟨⟨e.symm.trans e7⟩, hZ hodd⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv e h34))

end CFSG.ComponentClassification.RestrictedStd

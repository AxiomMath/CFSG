module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGJ
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJ
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (pElementSubgroup pElementSubgroup_le)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankThreeTheoremC
  (zja_isQuasisimple_of_simple zja_pElementSubgroup_subgroupOf zja_characteristic_map
    isPComponent_of_normal)
open CFSG.LocalAnalysis.RankFourTheoremC (zj_applyGe KFactZJFactorizationGe)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem isChevSimple_of_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsChevSimple 2 K) : IsChevSimple 2 K' := by
  rcases h with ⟨i, hi, ⟨e'⟩⟩ | ⟨i, hi, ⟨e'⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans e'⟩⟩

namespace KGData

variable (d : KGData p H D S B L M z) [hDn : (D.subgroupOf H).Normal]

include d

theorem eq_bot_of_normal {W : Subgroup (QA H D)} (hWK : W ≤ img H D L)
    (hWn : ∀ k ∈ img H D L, ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hcop : Nat.Coprime p (Nat.card W)) :
    W = ⊥ := by
  haveI := d.simple_img
  set W' : Subgroup ↥(img H D L) := W.subgroupOf (img H D L) with hW'
  have hW'n : W'.Normal := ⟨fun n hn g => hWn g.1 g.2 n.1 hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W' with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hWK hx⟩ : ↥(img H D L)) ∈ W' := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hle : img H D L ≤ W := fun x hx => by
      have : (⟨x, hx⟩ : ↥(img H D L)) ∈ W' := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have hpK : p ∣ Nat.card (img H D L) := by
      have h1 : orderOf (⟨qmk H D ⟨z, d.z_mem_H⟩,
          mem_img.mpr ⟨⟨z, d.z_mem_H⟩, d.z_mem_L, rfl⟩⟩ : ↥(img H D L)) = p := by
        rw [Subgroup.orderOf_mk]
        exact d.zb_order
      rw [← h1]
      exact orderOf_dvd_natCard _
    exact (Nat.Prime.coprime_iff_not_dvd d.prime).mp hcop (hpK.trans (Subgroup.card_dvd_of_le hle))

theorem pPrimeCore_eq {X : Subgroup G} (hX : X = pElementSubgroup p L ⊔ S) :
    CFSG.pPrimeCore p ↥X = D.subgroupOf X := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hXH : X ≤ H := hX ▸ d.X_le_H
  have hDX : D ≤ X := hX ▸ d.D_le_X
  have hDXn : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (hXH.trans d.H_le_D)
  apply le_antisymm
  · intro x hx
    have := d.N_le_D hX (N := CFSG.pPrimeCore p ↥X) CFSG.pPrimeCore_normal
      CFSG.pPrimeCore_coprime_card
    exact this ⟨x, hx, rfl⟩
  · refine le_sSup ⟨hDXn, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd d.prime).mpr d.not_dvd_D

theorem pCore_eq {X : Subgroup G} (hX : X = pElementSubgroup p L ⊔ S) :
    CFSG.pCore 2 ↥X = D.subgroupOf X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hXH : X ≤ H := hX ▸ d.X_le_H
  have hDX : D ≤ X := hX ▸ d.D_le_X
  have hDXn : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (hXH.trans d.H_le_D)
  apply le_antisymm
  · rw [← d.pPrimeCore_eq hX]
    refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
    rw [hk]
    have hp2 : p ≠ 2 := by have := d.five_le; omega
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes d.prime Nat.prime_two).mpr hp2)
  · exact le_sSup ⟨hDXn, d.D_two.comap_subtype⟩

theorem exists_inj {X : Subgroup G} (hX : X = pElementSubgroup p L ⊔ S) :
    ∃ φ : (↥X ⧸ CFSG.pPrimeCore p ↥X) →* QA H D, Function.Injective φ ∧
      ∀ x : ↥X, φ (QuotientGroup.mk' (CFSG.pPrimeCore p ↥X) x) =
        qmk H D ⟨x, (hX ▸ d.X_le_H) x.2⟩ := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hXH : X ≤ H := hX ▸ d.X_le_H
  have hpP := d.pPrimeCore_eq hX
  let ι : ↥X →* QA H D := (qmk H D).comp (Subgroup.inclusion hXH)
  have hle : CFSG.pPrimeCore p ↥X ≤ ι.ker := by
    intro x hx
    rw [hpP] at hx
    rw [MonoidHom.mem_ker]
    exact (qmk_eq_one_iff (H := H) (D := D)).mpr hx
  refine ⟨QuotientGroup.lift (CFSG.pPrimeCore p ↥X) ι hle, ?_, fun x => rfl⟩
  refine (injective_iff_map_eq_one _).mpr fun y hy => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : qmk H D (Subgroup.inclusion hXH x) = 1 := hy
  have hxD : (x : G) ∈ D := (qmk_eq_one_iff (H := H) (D := D)).mp hx
  have hmem : x ∈ CFSG.pPrimeCore p ↥X := by
    rw [hpP]
    exact hxD
  exact (QuotientGroup.eq_one_iff x).mpr hmem

end KGData

namespace KGData3

variable (d3 : KGData3 p H D S B L M z) [hDn : (D.subgroupOf H).Normal]

include d3

theorem chev_or_alt (hzj : KFactZJFactorizationGe) :
    IsChevSimple 2 ↥(img H D L) ∨ ∃ n, Nonempty (↥(img H D L) ≃* alternatingGroup (Fin n)) := by
  have d : KGData p H D S B L M z := d3.toData
  have hp := d.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := d.five_le; omega
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = pElementSubgroup p L ⊔ S := ⟨_, rfl⟩
  have hXH : X ≤ H := hX ▸ d.X_le_H
  have hJX : pElementSubgroup p L ≤ X := hX ▸ le_sup_left
  have hSX : S ≤ X := hX ▸ le_sup_right
  have hDX : D ≤ X := hX ▸ d.D_le_X
  have himgX : img H D X = img H D L ⊔ img H D S := hX ▸ d.img_X
  have hXnJ : X ≤ normalizer ((pElementSubgroup p L : Subgroup G) : Set G) := by
    rw [hX]
    exact d.X_le_normalizer_pES
  have hDXn : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (hXH.trans d.H_le_D)
  have hJXn : ((pElementSubgroup p L).subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJX).mpr hXnJ
  have hpP := d.pPrimeCore_eq hX
  have hpC := d.pCore_eq hX
  obtain ⟨φ, hφinj, hφ⟩ := d.exists_inj hX
  set L' : Subgroup (↥X ⧸ CFSG.pPrimeCore p ↥X) :=
    ((pElementSubgroup p L).subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥X)) with hL'
  have hmap : L'.map φ = img H D L := by
    rw [← d.img_pES_eq]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hxJ, rfl⟩, rfl⟩
      rw [hφ x]
      exact mem_img.mpr ⟨⟨x, hXH x.2⟩, hxJ, rfl⟩
    · intro hy
      obtain ⟨h, hhJ, rfl⟩ := mem_img.mp hy
      have hhX : (h : G) ∈ X := hJX hhJ
      refine ⟨QuotientGroup.mk' _ ⟨h, hhX⟩, ⟨⟨h, hhX⟩, hhJ, rfl⟩, ?_⟩
      rw [hφ ⟨h, hhX⟩]
  let e : ↥L' ≃* ↥(img H D L) :=
    (Subgroup.equivMapOfInjective L' φ hφinj).trans (MulEquiv.subgroupCongr hmap)
  haveI := d.simple_img
  have hLs : IsSimpleGroup ↥L' := e.isSimpleGroup
  have hLnab : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := d.nonab_img
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hLn : L'.Normal := Subgroup.Normal.map hJXn _ (QuotientGroup.mk'_surjective _)
  have hLc : centralizer (L' : Set (↥X ⧸ CFSG.pPrimeCore p ↥X)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine hφinj ?_
    rw [map_one]
    have hxH : (x : G) ∈ H := hXH x.2
    have hmem : φ (QuotientGroup.mk x) ∈ img H D L ⊔ img H D S := by
      have h1 : φ (QuotientGroup.mk x) = qmk H D ⟨x, hxH⟩ := hφ x
      rw [h1, ← himgX]
      exact mem_img.mpr ⟨⟨x, hxH⟩, x.2, rfl⟩
    refine KGQ.eq_one_of_centralizes d.cfg hmem fun k hk => ?_
    have hk' : k ∈ L'.map φ := by rw [hmap]; exact hk
    obtain ⟨l', hl', rfl⟩ := hk'
    have h2 := congrArg φ (mem_centralizer_iff.mp hy l' hl')
    rw [map_mul, map_mul] at h2
    exact h2.symm
  have hLcomp : CFSG.IsComponent L' :=
    ⟨zja_isQuasisimple_of_simple hLnab, hLn.isSubnormal⟩
  have hJp : pElementSubgroup p ((pElementSubgroup p L).subgroupOf X) =
      (pElementSubgroup p L).subgroupOf X :=
    zja_pElementSubgroup_subgroupOf hJX (pES_pES L)
  have hJc : CFSG.IsPComponent p ((pElementSubgroup p L).subgroupOf X) :=
    isPComponent_of_normal hp hJXn hJp hLcomp rfl
  have hsec := d3.catalog X hXH
  have hcharTwo : centralizer ((CFSG.pCore 2 ↥X : Subgroup ↥X) : Set ↥X) ≤
      CFSG.pCore 2 ↥X := by
    rw [hpC]
    intro x hx
    have hxC : (x : G) ∈ centralizer (D : Set G) := by
      rw [mem_centralizer_iff]
      intro dd hdd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨dd, hDX hdd⟩ hdd)
    exact d3.charTwo ⟨hXH x.2, hxC⟩
  have hrkp : ∀ E : Subgroup ↥X, IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
    intro E hE
    obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card hp hE
    have hle : E.map X.subtype ≤ H := by
      rintro _ ⟨e, he, rfl⟩
      exact hXH e.2
    have hcard : Nat.card (E.map X.subtype) = p ^ k := by
      rw [Subgroup.card_map_of_injective X.subtype_injective, hk]
    have hk2 : k ≤ 2 :=
      (SU1.le_pRank hp.one_lt hle (CFSG.Open.IsElemAbelian.map hE _) hcard).trans d3.rank_H
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk2
  have hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 ↥X) (CFSG.pPrimeCore p ↥X) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hpC, hpP]
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_rfl, d.D_two.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_self]
    norm_num
  have hV : IsPGroup 2 ↥(S.subgroupOf X) := d.S_two.comap_subtype
  have hcore : CFSG.pCore 2 ↥X ≤ S.subgroupOf X := by
    rw [hpC]
    intro x hx
    exact d.D_lt_S.le hx
  have hJ0 : ¬ 3 ∣ Nat.card ↥⁅(pElementSubgroup p L).subgroupOf X,
      (CFSG.pPrimeCore p ↥((pElementSubgroup p L).subgroupOf X)).map
        ((pElementSubgroup p L).subgroupOf X).subtype⁆ := by
    set Jy := (pElementSubgroup p L).subgroupOf X with hJy
    set O : Subgroup ↥X := (CFSG.pPrimeCore p ↥Jy).map Jy.subtype with hO
    have hOn : ∀ g ∈ Jy, ∀ o ∈ O, g * o * g⁻¹ ∈ O := by
      rintro g hg _ ⟨o', ho', rfl⟩
      exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pPrimeCore_normal.conj_mem o' ho' _, by simp⟩
    have hOJ : ∀ o ∈ O, (o : G) ∈ pElementSubgroup p L := by
      rintro _ ⟨o', _, rfl⟩
      exact o'.2
    have hOD : O ≤ D.subgroupOf X := by
      set O' : Subgroup G := O.map X.subtype with hO'
      set W : Subgroup (QA H D) := img H D O' with hW
      have hWK : W ≤ img H D L := by
        rintro _ hx
        obtain ⟨o, ho, rfl⟩ := mem_img.mp hx
        obtain ⟨o'', ho'', hoo⟩ := ho
        have : (o : G) ∈ pElementSubgroup p L := by
          rw [← hoo]
          exact hOJ o'' ho''
        exact mem_img.mpr ⟨o, (pElementSubgroup_le L) this, rfl⟩
      have hWn : ∀ k ∈ img H D L, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
        intro k hk w hw
        rw [← d.img_pES_eq] at hk
        obtain ⟨j, hj, rfl⟩ := mem_img.mp hk
        obtain ⟨o, ho, rfl⟩ := mem_img.mp hw
        obtain ⟨o'', ho'', hoo⟩ := ho
        have hjX : (j : G) ∈ X := hJX hj
        have hjy : (⟨j, hjX⟩ : ↥X) ∈ Jy := hj
        have hconj := hOn ⟨j, hjX⟩ hjy o'' ho''
        refine mem_img.mpr ⟨j * o * j⁻¹, ⟨⟨j, hjX⟩ * o'' * ⟨j, hjX⟩⁻¹, hconj, ?_⟩, ?_⟩
        · have hoo' : (o'' : G) = (o : G) := hoo
          show (j : G) * (o'' : G) * (j : G)⁻¹ = (j : G) * (o : G) * (j : G)⁻¹
          rw [hoo']
        · rw [map_mul, map_mul, map_inv]
      have hcop : Nat.Coprime p (Nat.card W) := by
        refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := O'.subgroupOf H)
          (qmk H D)) ?_
        have hO'H : O' ≤ H := (Subgroup.map_subtype_le O).trans hXH
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'H).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective,
          Subgroup.card_map_of_injective Jy.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
      have hW0 := d.eq_bot_of_normal hWK hWn hcop
      intro o ho
      have hoH : (o : G) ∈ H := hXH o.2
      have hmem : qmk H D ⟨o, hoH⟩ ∈ W :=
        mem_img.mpr ⟨⟨o, hoH⟩, ⟨o, ho, rfl⟩, rfl⟩
      rw [hW0, Subgroup.mem_bot] at hmem
      exact (qmk_eq_one_iff (H := H) (D := D)).mp hmem
    have hcomm : ⁅Jy, O⁆ ≤ D.subgroupOf X := by
      refine le_trans (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_) hOD
      rw [commutatorElement_def]
      exact O.mul_mem (hOn g₁ hg₁ g₂ hg₂) (O.inv_mem hg₂)
    intro h3
    have h4 := h3.trans (Subgroup.card_dvd_of_le hcomm)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv] at h4
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.D_two
    rw [hk] at h4
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  have hnc : ∀ Z : Subgroup ↥X, Z ≤ S.subgroupOf X → Z ≠ ⊥ →
      (Z.subgroupOf (S.subgroupOf X)).Characteristic →
      ¬ (pElementSubgroup p L).subgroupOf X ≤ normalizer (Z : Set ↥X) ⊔ CFSG.pPrimeCore p ↥X := by
    intro Z hZV hZ1 hZc hcov
    set Z' : Subgroup G := Z.map X.subtype with hZ'
    have hZ'S : Z' ≤ S := by
      rintro _ ⟨z', hz', rfl⟩
      exact hZV hz'
    have hZ'1 : Z' ≠ ⊥ := fun h =>
      hZ1 ((Subgroup.map_eq_bot_iff_of_injective Z X.subtype_injective).mp h)
    have hZ'c : (Z'.subgroupOf S).Characteristic := by
      let eV : ↥(S.subgroupOf X) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSX
      have hchar := zja_characteristic_map eV hZc
      have heq : (Z.subgroupOf (S.subgroupOf X)).map eV.toMonoidHom = Z'.subgroupOf S := by
        ext x
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s.1, hs, rfl⟩
        · intro hx
          obtain ⟨z', hz', hzx⟩ := hx
          have hz'S : z' ∈ S.subgroupOf X := by
            show (z' : G) ∈ S
            have : (z' : G) = (x : G) := hzx
            rw [this]
            exact x.2
          exact ⟨⟨z', hz'S⟩, hz', Subtype.ext hzx⟩
      rw [← heq]
      exact hchar
    have hNZ' := d3.char_le Z' hZ'S hZ'1 hZ'c
    have hJM : pElementSubgroup p L ≤ M := by
      intro j hj
      have hjX : (j : G) ∈ X := hJX hj
      have hj' : (⟨j, hjX⟩ : ↥X) ∈ (pElementSubgroup p L).subgroupOf X := hj
      obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp (hcov hj')
      have haM : (a : G) ∈ M := hNZ' (mem_normalizer_map_subtype ha)
      have hnD : (n : G) ∈ D := by
        rw [hpP] at hn
        exact hn
      have h5 : (a : G) * (n : G) = j := congrArg Subtype.val han
      rw [← h5]
      exact M.mul_mem haM (d.D_le_M hnD)
    apply d.not_le_img
    rw [← d.img_pES_eq]
    rintro _ hx
    obtain ⟨j, hj, rfl⟩ := mem_img.mp hx
    exact mem_img.mpr ⟨j, hJM hj, rfl⟩
  have key := zj_applyGe hp hp2 hzj hsec hcharTwo hrkp hsylow hJXn hJc hLs hLnab hLn hLc rfl hJp
    hV hcore hJ0 hnc
  rcases key with h | ⟨n, ⟨e'⟩⟩
  · exact Or.inl (isChevSimple_of_equiv e
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo h))
  · exact Or.inr ⟨n, ⟨e.symm.trans e'⟩⟩

end KGData3

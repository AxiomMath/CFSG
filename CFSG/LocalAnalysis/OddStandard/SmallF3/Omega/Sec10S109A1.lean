module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109W
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10A_jElem_mem {P : Subgroup G} {n : G} (hn : n ∈ normalizer (P : Set G)) :
    ∀ x ∈ JElem P, n * x * n⁻¹ ∈ JElem P := by
  have hP : ∀ x, x ∈ P → n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  intro x hx
  have hle : (JElem P).map (MulAut.conj n).toMonoidHom ≤ JElem P := by
    rw [JElem, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨x', ⟨A, hA, hxA⟩, rfl⟩
    refine ⟨CFSG.conjugate A n⁻¹, sec4_isMaxElemAbelianIn_conjugate hA n⁻¹ ?_, ?_⟩
    · intro u hu
      have hu' : n⁻¹ * u * n ∈ A := by simpa using mem_conjugate_iff'.mp hu
      have e : u = n * (n⁻¹ * u * n) * n⁻¹ := by group
      rw [e]
      exact hP _ (hA.1 hu')
    · rw [mem_conjugate_iff']
      have e : n⁻¹ * (n * x' * n⁻¹) * n = x' := by group
      simpa [MulAut.conj_apply, e] using hxA
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hx)

theorem sec10A_mem_normalizer_jElem {P : Subgroup G} {n : G} (hn : n ∈ normalizer (P : Set G)) :
    n ∈ normalizer ((JElem P : Subgroup G) : Set G) :=
  sec10W_mem_normalizer_of (sec10A_jElem_mem hn) (by
    intro x hx
    simpa using sec10A_jElem_mem ((normalizer (P : Set G)).inv_mem hn) x hx)

theorem sec10A_mem_normalizer_inf {X Y : Subgroup G} {n : G} (hX : n ∈ normalizer (X : Set G))
    (hY : n ∈ normalizer (Y : Set G)) : n ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX x, hY x]

theorem sec10A_conj_sup {X Y : Subgroup G} {c : G} (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) : ∀ x ∈ X ⊔ Y, c * x * c⁻¹ ∈ X ⊔ Y := by
  intro x hx
  have hle : (X ⊔ Y).map (MulAut.conj c).toMonoidHom ≤ X ⊔ Y := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hX a ha
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hY a ha
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hx)

theorem sec10A_mem_omega1 {S : Subgroup G} {x : G} (hxS : x ∈ S) (hxc : ∀ s ∈ S, s * x = x * s)
    (hx2 : x * x = 1) : x ∈ omega1 (centerIn S) := by
  have hxZ : x ∈ centerIn S := by
    rw [centerIn, Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxc (y : G) y.2)
  rw [omega1]
  exact Subgroup.subset_closure ⟨hxZ, by rw [pow_two]; exact hx2⟩

theorem sec10A_fix_z [Finite G] (h37 : Asc82Lemma37) (h103 : Asc82Lemma103)
    (h105 : Asc82Lemma105) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n⁻¹ * z * n = z := by
  obtain ⟨ht2sq, hz2sq, -, -, htz, htzc⟩ := sec10D_basic hb hctx
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2 : orderOf t = 2 := hctx.involution
  have hz_omega : z ∈ omega1 (centerIn S) :=
    sec10A_mem_omega1 hctx.mem_S hctx.central hz2sq
  have hconj_omega : n⁻¹ * z * n ∈ omega1 (centerIn S) := sec10_conj_mem_omega1 hn hz_omega
  have hconj_sup : n⁻¹ * z * n ∈ zpowers z ⊔ zpowers t := by
    rwa [h103 G t L S z hctx.toSec10Z] at hconj_omega
  have hconj_ord : orderOf (n⁻¹ * z * n) = 2 := by
    rw [orderOf_conjugate_eq]
    exact hz2
  rcases sec10_two_elem_cases htzc.symm hz2 ht2 hconj_sup hconj_ord with h | h | h
  · exact h
  · exact absurd h (sec10_not_conj_z h37 hctx n)
  · exfalso
    obtain ⟨g1, hg1⟩ := h105 G t L S z K1 K2 hctx
    apply sec10_not_conj_z h37 hctx (n * g1⁻¹)
    calc (n * g1⁻¹)⁻¹ * z * (n * g1⁻¹) = g1 * (n⁻¹ * z * n) * g1⁻¹ := by group
      _ = g1 * (t * z) * g1⁻¹ := by rw [h]
      _ = g1 * (g1⁻¹ * t * g1) * g1⁻¹ := by rw [hg1]
      _ = t := by group

theorem sec10A_t_cases [Finite G] (h37 : Asc82Lemma37) (h103 : Asc82Lemma103)
    (h105 : Asc82Lemma105) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n⁻¹ * t * n = t ∨ n⁻¹ * t * n = t * z := by
  obtain ⟨ht2sq, hz2sq, -, -, htz, htzc⟩ := sec10D_basic hb hctx
  obtain ⟨-, -, -, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2 : orderOf t = 2 := hctx.involution
  have hnz : n⁻¹ * z * n = z := sec10A_fix_z h37 h103 h105 hb hctx hn
  have ht_omega : t ∈ omega1 (centerIn S) :=
    sec10A_mem_omega1 htS (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp
      (hctx.sylow.1 hs)) ht2sq
  have hconj_omega : n⁻¹ * t * n ∈ omega1 (centerIn S) := sec10_conj_mem_omega1 hn ht_omega
  have hconj_sup : n⁻¹ * t * n ∈ zpowers z ⊔ zpowers t := by
    rwa [h103 G t L S z hctx.toSec10Z] at hconj_omega
  have hconj_ord : orderOf (n⁻¹ * t * n) = 2 := by
    rw [orderOf_conjugate_eq]
    exact ht2
  rcases sec10_two_elem_cases htzc.symm hz2 ht2 hconj_sup hconj_ord with h | h | h
  · exfalso
    apply htz
    calc t = n * (n⁻¹ * t * n) * n⁻¹ := by group
      _ = n * z * n⁻¹ := by rw [h]
      _ = n * (n⁻¹ * z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  · exact Or.inl h
  · exact Or.inr h

theorem sec10A_cent_mem_M [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {n : G}
    (hnS : n ∈ normalizer (S : Set G)) (hnt : n * t = t * n) : n ∈ secM t S L := by
  have hnL : n ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec3SettingLB n
      (Subgroup.mem_centralizer_singleton_iff.mpr hnt)
  have hnB : n ∈ normalizer ((JElem (S ⊓ L) : Subgroup G) : Set G) :=
    sec10A_mem_normalizer_jElem (sec10A_mem_normalizer_inf hnS hnL)
  have hnBi : n⁻¹ ∈ normalizer ((JElem (S ⊓ L) : Subgroup G) : Set G) :=
    (normalizer ((JElem (S ⊓ L) : Subgroup G) : Set G)).inv_mem hnB
  have hct : ∀ c : G, c * t = t * c → ∀ x ∈ zpowers t, c * x * c⁻¹ ∈ zpowers t := by
    intro c hc x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : c * t ^ k = t ^ k * c := (Commute.zpow_right (show Commute c t from hc) k).eq
    have e : c * t ^ k * c⁻¹ = t ^ k := by
      calc c * t ^ k * c⁻¹ = (t ^ k * c) * c⁻¹ := by rw [hcomm]
        _ = t ^ k := by group
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  have hnti : n⁻¹ * t = t * n⁻¹ := by
    calc n⁻¹ * t = n⁻¹ * (t * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * t) * n⁻¹ := by rw [hnt]
      _ = t * n⁻¹ := by group
  show n ∈ normalizer ((JElem (S ⊓ L) ⊔ zpowers t : Subgroup G) : Set G)
  refine sec10W_mem_normalizer_of ?_ ?_
  · exact sec10A_conj_sup (fun x hx => (Subgroup.mem_normalizer_iff.mp hnB x).mp hx)
      (hct n hnt)
  · intro x hx
    have := sec10A_conj_sup (c := n⁻¹) (fun x hx => (Subgroup.mem_normalizer_iff.mp hnBi x).mp hx)
      (hct n⁻¹ hnti) x hx
    simpa using this

theorem sec10A_normalE32_conj {S X : Subgroup G} {g : G} (hg : g ∈ normalizer (S : Set G))
    (hX : IsNormalE32In S X) : IsNormalE32In S (CFSG.conjugate X g) := by
  obtain ⟨hXS, hXe, hXn⟩ := hX
  have hg' : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hg
  have hcard : Nat.card (CFSG.conjugate X g) = Nat.card X :=
    (Nat.card_congr (Subgroup.equivMapOfInjective X (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toEquiv).symm
  refine ⟨?_, ⟨sec4_isElemAbelian_conjugate hXe.1 g, hcard.trans hXe.2⟩, ?_⟩
  · intro u hu
    exact (hg' u).mpr (hXS (mem_conjugate_iff'.mp hu))
  · refine ⟨fun a ha s => ?_⟩
    have ha' : g * (a : G) * g⁻¹ ∈ X := mem_conjugate_iff'.mp (Subgroup.mem_subgroupOf.mp ha)
    have hs' : g * (s : G) * g⁻¹ ∈ S := (hg' s).mp s.2
    have hmem : (⟨g * (s : G) * g⁻¹, hs'⟩ : ↥S) *
        (⟨g * (a : G) * g⁻¹, hXS ha'⟩ : ↥S) * (⟨g * (s : G) * g⁻¹, hs'⟩ : ↥S)⁻¹ ∈
        X.subgroupOf S :=
      hXn.conj_mem _ (Subgroup.mem_subgroupOf.mpr ha') _
    have hmem' : (g * (s : G) * g⁻¹) * (g * (a : G) * g⁻¹) * (g * (s : G) * g⁻¹)⁻¹ ∈ X :=
      Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.mem_subgroupOf]
    rw [mem_conjugate_iff']
    have e : g * ((s * a * s⁻¹ : ↥S) : G) * g⁻¹ =
        (g * (s : G) * g⁻¹) * (g * (a : G) * g⁻¹) * (g * (s : G) * g⁻¹)⁻¹ := by
      push_cast
      group
    rw [e]
    exact hmem'

theorem sec10A_sq_mem_M [Finite G] (h107c : Asc82Lemma107c) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {n : G}
    (hn : n ∈ normalizer (S : Set G)) (hnM : n ∉ secM t S L) : n * n ∈ secM t S L := by
  rcases h107c G t L S z K1 K2 hctx with hJ | ⟨r, hrS, hr2, -, hne, hX⟩
  · exfalso
    apply hnM
    show n ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    rw [hJ]
    exact sec10A_mem_normalizer_jElem hn
  · have hA : IsNormalE32In S (secA t S L) := (hX _).mpr (Or.inl rfl)
    have hA2 : IsNormalE32In S (secA2 t r K1 K2) := (hX _).mpr (Or.inr rfl)
    have hninv : n⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hn
    have hmem : ∀ (X : Subgroup G) (y : G), y ∈ CFSG.conjugate X n⁻¹ ↔ n⁻¹ * y * n ∈ X := by
      intro X y
      simpa using (mem_conjugate_iff' (H := X) (g := n⁻¹) (x := y))
    have h1 : CFSG.conjugate (secA t S L) n⁻¹ = secA2 t r K1 K2 := by
      rcases (hX _).mp (sec10A_normalE32_conj hninv hA) with h | h
      · exfalso
        apply hnM
        rw [Subgroup.mem_normalizer_iff] at *
        show n ∈ normalizer ((secA t S L : Subgroup G) : Set G)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have := hmem (secA t S L) (n * x * n⁻¹)
        rw [h] at this
        have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
        rw [e] at this
        exact this.symm
      · exact h
    have h2 : CFSG.conjugate (secA2 t r K1 K2) n⁻¹ = secA t S L := by
      rcases (hX _).mp (sec10A_normalE32_conj hninv hA2) with h | h
      · exact h
      · exfalso
        apply hne
        ext y
        have e1 := hmem (secA t S L) (n * y * n⁻¹)
        have e2 := hmem (secA2 t r K1 K2) (n * y * n⁻¹)
        rw [h1] at e1
        rw [h] at e2
        have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
        rw [e] at e1 e2
        exact e2.symm.trans e1
    show n * n ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have a1 := hmem (secA t S L) (n * x * n⁻¹)
    have a2 := hmem (secA2 t r K1 K2) (n * (n * x * n⁻¹) * n⁻¹)
    rw [h1] at a1
    rw [h2] at a2
    have e1 : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    have e2 : n⁻¹ * (n * (n * x * n⁻¹) * n⁻¹) * n = n * x * n⁻¹ := by group
    rw [e1] at a1
    rw [e2] at a2
    have e3 : n * n * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
    rw [e3]
    exact (a2.trans a1).symm

theorem sec10A_exists_odd_pow [Finite G] (g0 : G) :
    ∃ m : ℕ, Odd m ∧ IsPGroup 2 ↥(zpowers (g0 ^ m)) := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g0).ne'
  refine ⟨m, hm, ?_⟩
  have hpow : (g0 ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hk]
    exact pow_orderOf_eq_one g0
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers]; exact hj)

theorem sec10A_part1 [Finite G] (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hb : Asc82Basic10)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) (hneg : ¬ normalizer (S : Set G) ≤ secM t S L) :
    ∃ g : G, g ∈ normalizer (S : Set G) ∧ g ∉ secM t S L ∧ IsPGroup 2 ↥(zpowers g) ∧
      g⁻¹ * t * g = t * z ∧ g⁻¹ * z * g = z := by
  obtain ⟨g0, hg0N, hg0M⟩ := SetLike.not_le_iff_exists.mp hneg
  obtain ⟨m, hm, hg2⟩ := sec10A_exists_odd_pow g0
  have hgN : g0 ^ m ∈ normalizer (S : Set G) := Subgroup.pow_mem _ hg0N m
  have hsq : g0 * g0 ∈ secM t S L := sec10A_sq_mem_M h.l107c hctx hg0N hg0M
  have hgM : g0 ^ m ∉ secM t S L := by
    intro hgM
    apply hg0M
    obtain ⟨f, rfl⟩ := hm
    have e1 : (g0 * g0) ^ f = g0 ^ (2 * f) := by rw [← pow_two, ← pow_mul]
    have e2 : ((g0 * g0) ^ f)⁻¹ * g0 ^ (2 * f + 1) = g0 := by
      rw [e1, pow_succ, inv_mul_cancel_left]
    rw [← e2]
    exact (secM t S L).mul_mem ((secM t S L).inv_mem (Subgroup.pow_mem _ hsq f)) hgM
  have hz : (g0 ^ m)⁻¹ * z * g0 ^ m = z := sec10A_fix_z h3.l37 h.l103 h.l105 hb hctx hgN
  rcases sec10A_t_cases h3.l37 h.l103 h.l105 hb hctx hgN with ht | ht
  · exfalso
    apply hgM
    refine sec10A_cent_mem_M h3.l36 hctx hgN ?_
    calc g0 ^ m * t = g0 ^ m * ((g0 ^ m)⁻¹ * t * g0 ^ m) := by rw [ht]
      _ = t * g0 ^ m := by group
  · exact ⟨g0 ^ m, hgN, hgM, hg2, ht, hz⟩

end CFSG.OddStandard.SmallF3.Omega

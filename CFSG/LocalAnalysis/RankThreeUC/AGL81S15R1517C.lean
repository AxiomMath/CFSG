module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

section BarTransfer

variable {X : Type} [Group X] [Finite X]

theorem out1517_of_bar_aux_not_dvd_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup X}
    (hN : IsPGroup 2 N) : ¬ p ∣ Nat.card N := by
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn]
  intro hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem out1517_of_bar_aux_injOn {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) {P : Subgroup X}
    (hP : IsPGroup 3 P) :
    ∀ x ∈ P, ∀ y ∈ P, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : P ⊓ N = ⊥ := disjoint_iff.1 (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P N hP hN)
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ P ⊓ N := ⟨P.mul_mem (P.inv_mem hx) hy, QuotientGroup.eq.1 hxy⟩
  rw [hbot, mem_bot, inv_mul_eq_one] at hmem
  exact hmem

theorem out1517_of_bar_aux_card_map {Y : Type*} [Group Y] (f : X →* Y) {P : Subgroup X}
    (h : ∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y) : Nat.card (P.map f) = Nat.card P := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn h]
  rfl

theorem out1517_of_bar_aux_normalizer_map_eq {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N)
    {D : Subgroup X} (hD : IsPGroup 3 D) :
    Subgroup.normalizer ((D.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      (Subgroup.normalizer (D : Set X)).map (QuotientGroup.mk' N) :=
  (CFSG.RankThree.PartTwo.Sec4.map_normalizer_eq_of_not_dvd Nat.prime_three N
    (out1517_of_bar_aux_not_dvd_card Nat.prime_three (by norm_num) hN) hD).symm

theorem out1517_of_bar_aux_centralizer_map_eq {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N)
    {D : Subgroup X} (hD : IsPGroup 3 D) :
    Subgroup.centralizer ((D.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      (Subgroup.centralizer (D : Set X)).map (QuotientGroup.mk' N) := by
  have hinj := out1517_of_bar_aux_injOn hN hD
  apply le_antisymm
  · intro z hz
    have hzn := Subgroup.centralizer_le_normalizer _ hz
    rw [out1517_of_bar_aux_normalizer_map_eq hN hD] at hzn
    obtain ⟨y, hy, rfl⟩ := hzn
    refine ⟨y, Subgroup.mem_centralizer_iff.2 fun d hd => ?_, rfl⟩
    have hyd : y * d * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hy d).1 hd
    have hc := Subgroup.mem_centralizer_iff.1 hz (QuotientGroup.mk' N d)
      (Subgroup.mem_map_of_mem _ hd)
    have h1 : QuotientGroup.mk' N (y * d * y⁻¹) = QuotientGroup.mk' N d := by
      rw [map_mul, map_mul, map_inv, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := hinj _ hyd _ hd h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hy d hd]

theorem nonTrans_of_bar
    (h : ∀ E : Subgroup (X ⧸ CFSG.pCore 2 X), IsElemAbelian 3 E → Nat.card E = 9 →
      NonTrans1517 E) :
    ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 → NonTrans1517 E := by
  intro E hE hcard
  have hinj := out1517_of_bar_aux_injOn (CFSG.pCore_isPGroup (p := 2) (G := X)) hE.isPGroup
  obtain ⟨a, ha, b, hb, ha1, hb1, hnorm⟩ := h (E.map (QuotientGroup.mk' (CFSG.pCore 2 X)))
    (hE.map _) (by rw [out1517_of_bar_aux_card_map _ hinj]; exact hcard)
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  refine ⟨a', ha', b', hb', fun h1 => ha1 (by rw [h1, map_one]),
    fun h1 => hb1 (by rw [h1, map_one]), fun g hg hgab => ?_⟩
  refine hnorm (QuotientGroup.mk' (CFSG.pCore 2 X) g)
    (Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hg)) ?_
  have h2 := congrArg (QuotientGroup.mk' (CFSG.pCore 2 X)) hgab
  rw [map_mul, map_mul, map_inv] at h2
  exact h2

theorem out1517_of_bar_aux_isElemAbelian_of_map {Y : Type*} [Group Y] (f : X →* Y) {q : ℕ}
    {P : Subgroup X} (hf : ∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y)
    (h : IsElemAbelian q (P.map f)) : IsElemAbelian q P := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf _ (P.mul_mem a.2 b.2) _ (P.mul_mem b.2 a.2) ?_)⟩⟩,
    fun x hx => hf _ (P.pow_mem hx q) _ P.one_mem ?_⟩
  · simp only [Subgroup.coe_mul, map_mul]
    exact h.comm (Subgroup.mem_map_of_mem f a.2) (Subgroup.mem_map_of_mem f b.2)
  · rw [map_pow, h.2 _ (Subgroup.mem_map_of_mem f hx), map_one]

theorem out1517_of_bar_aux_isCyclic_center {Y : Type*} [Group Y] (f : X →* Y) {P : Subgroup X}
    (hf : ∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y)
    (h : IsCyclic ↥(Subgroup.center ↥(P.map f))) : IsCyclic ↥(Subgroup.center ↥P) := by
  haveI := h
  let e : P →* P.map f := f.subgroupMap P
  have he : Function.Surjective e := f.subgroupMap_surjective P
  have hec : ∀ z ∈ Subgroup.center ↥P, e z ∈ Subgroup.center ↥(P.map f) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := he g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g']
  let g : Subgroup.center ↥P →* Subgroup.center ↥(P.map f) :=
    (e.comp (Subgroup.center ↥P).subtype).codRestrict _ (fun z => hec z z.2)
  refine isCyclic_of_injective g fun z1 z2 hz => ?_
  have h12 : e z1 = e z2 := congrArg Subtype.val hz
  have h3 : f z1 = f z2 := congrArg Subtype.val h12
  exact Subtype.ext (Subtype.ext (hf _ z1.1.2 _ z2.1.2 h3))

theorem out1517_of_bar_aux_caseA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup X} [N.Normal]
    (hN : IsPGroup 2 N) {D : Subgroup X} (hD : Nat.card D = 3)
    (h : CaseA1517 p (D.map (QuotientGroup.mk' N))) : CaseA1517 p D := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by rw [hD]; norm_num)
  obtain ⟨_, hrk, hns⟩ := h
  rw [out1517_of_bar_aux_centralizer_map_eq hN hD3] at hrk hns
  refine ⟨hD, hrk.trans (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp _ ?_ _),
    fun hsolv => hns
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map _ hsolv)⟩
  rw [QuotientGroup.ker_mk']
  exact out1517_of_bar_aux_not_dvd_card hp hp2 hN

theorem out1517_of_bar_aux_isSylowOf_map {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N)
    {D P : Subgroup X} (hD : IsPGroup 3 D)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (D : Set X))) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.map (QuotientGroup.mk' N))
      (Subgroup.normalizer ((D.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [out1517_of_bar_aux_normalizer_map_eq hN hD]
  obtain ⟨Q, rfl⟩ := hP
  let ψ : Subgroup.normalizer (D : Set X) →*
      (Subgroup.normalizer (D : Set X)).map (QuotientGroup.mk' N) :=
    (QuotientGroup.mk' N).subgroupMap _
  have hψ : Function.Surjective ψ := (QuotientGroup.mk' N).subgroupMap_surjective _
  refine ⟨Q.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem out1517_of_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Out1517 (X ⧸ CFSG.pCore 2 X) p) : Out1517 X p := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hD3 : ∀ D : Subgroup X, Nat.card D = 3 → IsPGroup 3 D := fun D hD =>
    IsPGroup.of_card (n := 1) (by rw [hD]; norm_num)
  have hcard : ∀ D : Subgroup X, Nat.card D = 3 →
      Nat.card (D.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = 3 := fun D hD => by
    rw [out1517_of_bar_aux_card_map _ (out1517_of_bar_aux_injOn hN (hD3 D hD)), hD]
  refine ⟨fun D hD => ?_, fun E hE hE9 => ?_, fun D hD hnot P hP => ?_⟩
  · have h1 := h.dvd _ (hcard D hD)
    rw [out1517_of_bar_aux_centralizer_map_eq hN (hD3 D hD)] at h1
    exact h1.trans (Subgroup.card_map_dvd _ _)
  · have hinj := out1517_of_bar_aux_injOn hN hE.isPGroup
    obtain ⟨Db, hDbE, hDb⟩ := h.caseA (E.map (QuotientGroup.mk' (CFSG.pCore 2 X))) (hE.map _)
      (by rw [out1517_of_bar_aux_card_map _ hinj]; exact hE9)
    obtain ⟨D0, hD0E, hD0⟩ : ∃ D0 ≤ E, D0.map (QuotientGroup.mk' (CFSG.pCore 2 X)) = Db := by
      refine ⟨E ⊓ Db.comap (QuotientGroup.mk' (CFSG.pCore 2 X)), inf_le_left, ?_⟩
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx.2
      · intro hy
        obtain ⟨x, hxE, rfl⟩ := hDbE hy
        exact ⟨x, ⟨hxE, hy⟩, rfl⟩
    have hD0c : Nat.card D0 = 3 := by
      have h3 : Nat.card (D0.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = 3 := by
        rw [hD0]; exact hDb.1
      rwa [out1517_of_bar_aux_card_map _ (fun x hx y hy => hinj x (hD0E hx) y (hD0E hy))] at h3
    refine ⟨D0, hD0E, out1517_of_bar_aux_caseA hp hp2 hN hD0c ?_⟩
    rw [hD0]
    exact hDb
  · have hnot' : ¬ CaseA1517 p (D.map (QuotientGroup.mk' (CFSG.pCore 2 X))) := fun hc =>
      hnot (out1517_of_bar_aux_caseA hp hp2 hN hD hc)
    have hPinj := out1517_of_bar_aux_injOn hN hP.isPGroup
    obtain ⟨hshape, hrk⟩ := h.shape _ (hcard D hD) hnot' _
      (out1517_of_bar_aux_isSylowOf_map hN (hD3 D hD) hP)
    have hrank : 3 ≤ CFSG.Open.pRank 3 P := by
      refine hrk.trans
        (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three _ ?_ _)
      rw [QuotientGroup.ker_mk']
      exact out1517_of_bar_aux_not_dvd_card Nat.prime_three (by norm_num) hN
    refine ⟨?_, hrank⟩
    rcases hshape with ⟨hea, h27⟩ | hcyc
    · exact Or.inl ⟨out1517_of_bar_aux_isElemAbelian_of_map _ hPinj hea,
        by rwa [out1517_of_bar_aux_card_map _ hPinj] at h27⟩
    · exact Or.inr (out1517_of_bar_aux_isCyclic_center _ hPinj hcyc)

end BarTransfer

end CFSG.LocalAnalysis.RankThreeUC.S15

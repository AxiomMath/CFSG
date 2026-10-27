module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.Stage2.Local.P27.OddGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

variable {A B : Type} [Group A] [Group B]

private lemma commutator_sup_center_le {G : Type*} [Group G] (X Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) : ⁅X ⊔ Z, X ⊔ Z⁆ ≤ X := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro y1 hy1 y2 hy2
  obtain ⟨x1, hx1, z1, hz1, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := X) (t := Z)).mp hy1
  obtain ⟨x2, hx2, z2, hz2, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := X) (t := Z)).mp hy2
  have hz1c : Commute z1 (x2 * z2) :=
    ((Subgroup.mem_center_iff.mp (hZ hz1)) (x2 * z2)).symm
  have hz2c : Commute x1 z2 := (Subgroup.mem_center_iff.mp (hZ hz2)) x1
  have hcomm : ⁅x1 * z1, x2 * z2⁆ = ⁅x1, x2⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul x1 z1 (x2 * z2),
      commutatorElement_mul_right_eq_mul_conj x1 x2 z2, hz1c.commutator_eq,
      hz2c.commutator_eq]
    group
  rw [hcomm]
  exact Subgroup.commutator_le_self X (Subgroup.commutator_mem_commutator hx1 hx2)

theorem t5_layer_perfect (C : Subgroup A) :
    Group.IsPerfect ↥(CFSG.inSubgroup CFSG.layer C) := by
  have h : Group.IsPerfect ↥(CFSG.layer ↥C) := CFSG.LocalCores.layer_isPerfect
  exact h.map C.subtype

theorem t5_xout_eq_layer [Finite A] (f : A →* B) {t : A} (ht : t ∈ Subgroup.center A)
    (ht2 : t * t = 1) (hker : f.ker ≤ Subgroup.zpowers t) {C : Subgroup A} (htC : t ∈ C)
    (h : (twoPrimeRes (twoRes C)).map f = (CFSG.inSubgroup CFSG.layer C).map f) :
    twoPrimeRes (twoRes C) = CFSG.inSubgroup CFSG.layer C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup A := CFSG.inSubgroup CFSG.layer C
  let D : Subgroup A := twoRes C
  let X : Subgroup A := twoPrimeRes D
  let Z : Subgroup A := Subgroup.zpowers t
  have hEC : E ≤ C := Subgroup.map_subtype_le (CFSG.layer ↥C)
  have hDC : D ≤ C := (Subgroup.closure_le C).mpr fun _ hg => hg.1
  have hXD : X ≤ D := (Subgroup.closure_le D).mpr fun _ hg => hg.1
  have hZc : Z ≤ Subgroup.center A := Subgroup.zpowers_le.mpr ht
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  have hZmem : ∀ z ∈ Z, z = 1 ∨ z = t := by
    intro z hz
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨m, rfl⟩ := hz
    obtain ⟨n, hn | hn⟩ := Int.even_or_odd' m
    · left; rw [hn, zpow_mul, zpow_two, ht2, one_zpow]
    · right; rw [hn, zpow_add, zpow_mul, zpow_two, ht2, one_zpow, one_mul, zpow_one]
  have hXEZ : X ≤ E ⊔ Z := by
    intro x hxX
    have hfx : f x ∈ E.map f := by
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩
    obtain ⟨e, heE, hefx⟩ := Subgroup.mem_map.mp hfx
    have hkerx : e⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hefx, inv_mul_cancel]
    exact (Subgroup.mem_sup_of_normal_right (s := E) (t := Z)).mpr
      ⟨e, heE, e⁻¹ * x, hker hkerx, by group⟩
  have hEXZ : E ≤ X ⊔ Z := by
    intro e heE
    have hfe : f e ∈ X.map f := by
      rw [h]
      exact Subgroup.mem_map.mpr ⟨e, heE, rfl⟩
    obtain ⟨x, hxX, hfxe⟩ := Subgroup.mem_map.mp hfe
    have hkerx : x⁻¹ * e ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfxe, inv_mul_cancel]
    exact (Subgroup.mem_sup_of_normal_right (s := X) (t := Z)).mpr
      ⟨x, hxX, x⁻¹ * e, hker hkerx, by group⟩
  have hYX : ⁅X ⊔ Z, X ⊔ Z⁆ ≤ X := commutator_sup_center_le X Z hZc
  have hEX : E ≤ X := by
    have hperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp (t5_layer_perfect C)
    calc E = ⁅E, E⁆ := hperf.symm
      _ ≤ ⁅X ⊔ Z, X ⊔ Z⁆ := Subgroup.commutator_mono hEXZ hEXZ
      _ ≤ X := hYX
  suffices hXle : X ≤ E by exact le_antisymm hXle hEX
  by_contra hne
  obtain ⟨x, hxX, hxE⟩ := SetLike.not_le_iff_exists.mp hne
  obtain ⟨e, heE, z, hzZ, hez⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := E) (t := Z)).mp (hXEZ hxX)
  have hx_et : x = e * t := by
    rcases hZmem z hzZ with hz1 | hzt
    · exfalso
      exact hxE (by rw [← hez, hz1, mul_one]; exact heE)
    · rw [← hez, hzt]
  have htX : t ∈ X := by
    have heX : e ∈ X := hEX heE
    have : t = e⁻¹ * x := by rw [hx_et]; group
    rw [this]; exact X.mul_mem (X.inv_mem heX) hxX
  have htE : t ∉ E := fun htE =>
    hxE (by rw [hx_et]; exact E.mul_mem heE htE)
  have htD : t ∈ D := hXD htX
  have hEnormC : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
    intro c hc e he
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp he
    haveI : (CFSG.layer ↥C).Characteristic := CFSG.LocalCores.layer_characteristic
    have hconj : (⟨c, hc⟩ : ↥C) * l * (⟨c, hc⟩ : ↥C)⁻¹ ∈ CFSG.layer ↥C :=
      (inferInstance : (CFSG.layer ↥C).Normal).conj_mem l hl ⟨c, hc⟩
    exact Subgroup.mem_map.mpr ⟨_, hconj, rfl⟩
  have hE'D : E ≤ D := hEX.trans hXD
  let D' := ↥D
  let E' : Subgroup D' := E.subgroupOf D
  let X' : Subgroup D' := X.subgroupOf D
  have hE'X' : E' ≤ X' := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hEX (Subgroup.mem_subgroupOf.mp hy))
  have hE'normal : E'.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hE'D]
    intro e d he hd
    exact hEnormC d (hDC hd) e he
  haveI : E'.Normal := hE'normal
  let Q := D' ⧸ E'
  let q : Q := QuotientGroup.mk' E' ⟨t, htD⟩
  have hq_ne : q ≠ 1 := by
    intro hq1
    apply htE
    have : (⟨t, htD⟩ : D') ∈ E' :=
      (QuotientGroup.eq_one_iff (N := E') ⟨t, htD⟩).mp hq1
    exact Subgroup.mem_subgroupOf.mp this
  have hq_sq : q * q = 1 := by
    have h1 : (⟨t, htD⟩ : D') * ⟨t, htD⟩ = 1 := by
      apply Subtype.ext; simpa using ht2
    calc q * q = QuotientGroup.mk' E' (⟨t, htD⟩ * ⟨t, htD⟩) :=
          (map_mul (QuotientGroup.mk' E') ⟨t, htD⟩ ⟨t, htD⟩).symm
      _ = QuotientGroup.mk' E' 1 := by rw [h1]
      _ = 1 := map_one _
  have hq_central : ∀ v : Q, q * v = v * q := by
    intro v
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective E' v
    change QuotientGroup.mk' E' ⟨t, htD⟩ * QuotientGroup.mk' E' d =
      QuotientGroup.mk' E' d * QuotientGroup.mk' E' ⟨t, htD⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ht (d : A)).symm
  let Xq : Subgroup Q := X'.map (QuotientGroup.mk' E')
  have hXq_le : Xq ≤ Subgroup.zpowers q := by
    intro y hy
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨x', hx'X', rfl⟩ := Subgroup.mem_map.mp hy
    have hxX : (x' : A) ∈ X := Subgroup.mem_subgroupOf.mp hx'X'
    obtain ⟨e, heE, z, hzZ, hez⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := E) (t := Z)).mp (hXEZ hxX)
    rcases hZmem z hzZ with hz1 | hzt
    · refine ⟨0, ?_⟩
      rw [zpow_zero]
      have hx'e : x' = (⟨e, hE'D heE⟩ : D') := by
        apply Subtype.ext; rw [← hez, hz1, mul_one]
      rw [hx'e]
      exact ((QuotientGroup.eq_one_iff (N := E') (⟨e, hE'D heE⟩ : D')).mpr
        (Subgroup.mem_subgroupOf.mpr heE)).symm
    · refine ⟨1, ?_⟩
      rw [zpow_one]
      have hx'et : x' = (⟨e, hE'D heE⟩ : D') * ⟨t, htD⟩ := by
        apply Subtype.ext; rw [← hez, hzt]; rfl
      rw [hx'et, map_mul]
      have he1 : QuotientGroup.mk' E' (⟨e, hE'D heE⟩ : D') = 1 :=
        (QuotientGroup.eq_one_iff (N := E') _).mpr (Subgroup.mem_subgroupOf.mpr heE)
      rw [he1, one_mul]
  have hq_mem_Xq : q ∈ Xq := Subgroup.mem_map.mpr
    ⟨⟨t, htD⟩, Subgroup.mem_subgroupOf.mpr htX, rfl⟩
  have hXq_eq : Xq = Subgroup.zpowers q :=
    le_antisymm hXq_le (Subgroup.zpowers_le.mpr hq_mem_Xq)
  have hq_ord : orderOf q = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hq_sq
    · exact hq_ne
  have hXq_center : Xq ≤ Subgroup.center Q := by
    rw [hXq_eq, Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro v; exact (hq_central v).symm
  haveI : Xq.Normal := Subgroup.normal_of_le_center hXq_center
  have hX'index_odd : ¬ 2 ∣ X'.index := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 D'))
    have hPX' : (P : Subgroup D') ≤ X' := by
      intro p hp
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨p.2, ?_⟩
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥(P : Subgroup D'))
      refine ⟨k, ?_⟩
      have h1 : orderOf (⟨p, hp⟩ : ↥(P : Subgroup D')) = orderOf p :=
        Subgroup.orderOf_mk p hp
      have h2 : orderOf (p : A) = orderOf p := (Subgroup.orderOf_mk (p : A) p.2).symm
      rw [h2, ← h1]; exact hk
    intro h2
    haveI : P.FiniteIndex := inferInstance
    exact P.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hPX'))
  have hindex_map : Xq.index = X'.index := by
    have hk : (QuotientGroup.mk' E').ker ≤ X' := by
      rw [QuotientGroup.ker_mk']; exact hE'X'
    exact Subgroup.index_map_eq (H := X') (QuotientGroup.mk'_surjective E') hk
  have hXq_index_odd : ¬ 2 ∣ Xq.index := by rw [hindex_map]; exact hX'index_odd
  have hD_eq : twoRes D = D := by
    refine le_antisymm ((Subgroup.closure_le D).mpr fun _ hg => hg.1) ?_
    exact (Subgroup.closure_le (twoRes D)).mpr fun g hg =>
      Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hg.1, hg.2⟩, hg.2⟩
  have hD'gen : Subgroup.closure {y : D' | Odd (orderOf y)} = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := D)).mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have hset : D.subtype '' {y : D' | Odd (orderOf y)} =
        {g : A | g ∈ D ∧ Odd (orderOf g)} := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : Odd (orderOf y) := hy
        exact ⟨y.2, by
          show Odd (orderOf (y : A))
          rwa [Subgroup.orderOf_coe]⟩
      · rintro ⟨hgD, hgodd⟩
        refine ⟨⟨g, hgD⟩, ?_, rfl⟩
        show Odd (orderOf (⟨g, hgD⟩ : D'))
        rwa [Subgroup.orderOf_mk]
    rw [hset]
    exact hD_eq
  have hgenQ : Subgroup.closure {y : Q | Odd (orderOf y)} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective E' y
    have hd : d ∈ Subgroup.closure {y : D' | Odd (orderOf y)} :=
      hD'gen ▸ Subgroup.mem_top d
    have hm : QuotientGroup.mk' E' d ∈
        (Subgroup.closure {y : D' | Odd (orderOf y)}).map (QuotientGroup.mk' E') :=
      Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    rw [MonoidHom.map_closure] at hm
    exact (Subgroup.closure_mono fun z hz => by
      rcases hz with ⟨d', hd', rfl⟩
      exact Odd.of_dvd_nat hd' (orderOf_map_dvd (QuotientGroup.mk' E') d')) hm
  have hc : ∀ u ∈ (⊤ : Subgroup Q), IsPGroup 2 ↥(Subgroup.zpowers u) →
      ∀ v ∈ (⊤ : Subgroup Q), u * v = v * u := by
    intro u _ hu v _
    have huXq : u ∈ Xq := by
      obtain ⟨k, hk⟩ :=
        hu.exists_orderOf_eq_pow (⟨u, Subgroup.mem_zpowers u⟩ : ↥(Subgroup.zpowers u))
      have hk' : orderOf u = 2 ^ k :=
        (Subgroup.orderOf_mk u (Subgroup.mem_zpowers u)).symm.trans hk
      have hodd : Odd Xq.index := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]; exact hXq_index_odd
      have hcop : Nat.Coprime (2 ^ k) Xq.index :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
      have hdiv1 : orderOf (QuotientGroup.mk' Xq u : Q ⧸ Xq) ∣ 2 ^ k :=
        hk' ▸ orderOf_map_dvd (QuotientGroup.mk' Xq) u
      have hdiv2 : orderOf (QuotientGroup.mk' Xq u : Q ⧸ Xq) ∣ Xq.index := by
        rw [Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      have hone : orderOf (QuotientGroup.mk' Xq u : Q ⧸ Xq) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hdiv1 hdiv2
      exact (QuotientGroup.eq_one_iff (N := Xq) u).mp (orderOf_eq_one_iff.mp hone)
    have hcent := hXq_center huXq
    rw [Subgroup.mem_center_iff] at hcent
    exact (hcent v).symm
  have hoddQ : Odd (Nat.card Q) := by
    have h := CFSG.GH74.GLS.Stage2.Local.P27.odd_card_of_generated_by_odd
      (Y := Q) (V := ⊤) (S := {y : Q | Odd (orderOf y)})
      (fun s hs => ⟨trivial, hs⟩) hgenQ.ge hc
    simpa [Subgroup.card_top] using h
  have h2dvd : 2 ∣ Nat.card Q := by
    have hcardXq : Nat.card Xq = 2 := by rw [hXq_eq, Nat.card_zpowers, hq_ord]
    rw [← hcardXq]
    have hdvd := Subgroup.card_dvd_of_le (le_top : Xq ≤ (⊤ : Subgroup Q))
    rwa [Subgroup.card_top] at hdvd
  exact (Nat.not_even_iff_odd.mpr hoddQ) (even_iff_two_dvd.mpr h2dvd)

end CFSG.OddStandard.SmallF3.Omega

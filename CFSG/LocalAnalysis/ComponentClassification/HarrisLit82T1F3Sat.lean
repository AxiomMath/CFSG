module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace F3

theorem mem_fusionZStar_of_mem_center {X : Type*} [Group X] {x : X} (hx : x ∈ center X) :
    x ∈ Open.fusionZStar X := by
  unfold Open.fusionZStar
  rw [mem_comap, mem_center_iff]
  intro g
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    mem_center_iff.mp hx g₀]

theorem orderOf_mul_of_commute {X : Type*} [Group X] {z z₁ : X} (hz : orderOf z = 2)
    (hz₁ : orderOf z₁ = 2) (hc : z * z₁ = z₁ * z) (hne : z₁ ≠ z) : orderOf (z * z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz₁2 : z₁ ^ 2 = 1 := hz₁ ▸ pow_orderOf_eq_one z₁
  refine orderOf_eq_prime ?_ ?_
  · rw [(show Commute z z₁ from hc).mul_pow, hz2, hz₁2, one_mul]
  · intro h1
    apply hne
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
    rw [← hzi]
    exact eq_inv_of_mul_eq_one_right h1

theorem mem_oPrimeResidualOf {X : Type*} [Group X] {J : Subgroup X} {g : X} (hgJ : g ∈ J)
    (hg : orderOf g = 2) : g ∈ GH74.GLS.oPrimeResidualOf 2 J := by
  refine ⟨⟨g, hgJ⟩, Subgroup.subset_closure ⟨1, ?_⟩, rfl⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hg, pow_orderOf_eq_one]

section Saturate

variable {G : Type} [Group G] [Finite G]

theorem saturate {J A : Subgroup G} (hJA : J ≤ A) (hJs : (J.subgroupOf A).IsSubnormal) :
    J ⊔ (pPrimeCore 2 ↥A).map A.subtype ≤ A ∧
      ((J ⊔ (pPrimeCore 2 ↥A).map A.subtype).subgroupOf A).IsSubnormal ∧
      (pPrimeCore 2 ↥(J ⊔ (pPrimeCore 2 ↥A).map A.subtype)).map
          (J ⊔ (pPrimeCore 2 ↥A).map A.subtype).subtype = (pPrimeCore 2 ↥A).map A.subtype ∧
      Nonempty (↥(J ⊔ (pPrimeCore 2 ↥A).map A.subtype) ⧸
          pPrimeCore 2 ↥(J ⊔ (pPrimeCore 2 ↥A).map A.subtype) ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (pPrimeCore 2 ↥A).map A.subtype with hNdef
  set S := J ⊔ N with hSdef
  have hNA : N ≤ A := map_subtype_le _
  have hSA : S ≤ A := sup_le hJA hNA
  have hNsub : N.subgroupOf A = pPrimeCore 2 ↥A :=
    comap_map_eq_self_of_injective A.subtype_injective _
  have hSsub : S.subgroupOf A = J.subgroupOf A ⊔ pPrimeCore 2 ↥A := by
    rw [hSdef, subgroupOf_sup hJA hNA, hNsub]
  have hSs : (S.subgroupOf A).IsSubnormal := by
    rw [hSsub]
    exact CFSG.GroupTheory.isSubnormal_sup hJs (Normal.isSubnormal inferInstance)
  refine ⟨hSA, hSs, ?_, ?_⟩
  ·
    have key := CFSG.LocalCores.prime_set_core_subnormal_intersection
      {q : Nat.Primes | q.val ≠ 2} hSs
    have hle : pPrimeCore 2 ↥A ≤ S.subgroupOf A := by
      rw [hSsub]
      exact le_sup_right
    rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore, inf_eq_right.mpr hle] at key
    let e : ↥(S.subgroupOf A) ≃* ↥S := subgroupOfEquivOfLe hSA
    rw [← pPrimeCore_map_iso 2 e, map_map, hNdef, ← key, map_map]
    rfl
  ·
    have hNS : N ≤ S := le_sup_right
    have hJS : J ≤ S := le_sup_left
    have hNn : (N.subgroupOf S).Normal := by
      rw [normal_subgroupOf_iff hNS]
      rintro _ k ⟨n, hn, rfl⟩ hk
      have hkA := hSA hk
      refine ⟨⟨k, hkA⟩ * n * ⟨k, hkA⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥A)).conj_mem n hn _,
        ?_⟩
      simp
    have hNodd : ¬ 2 ∣ Nat.card ↥(N.subgroupOf S) := by
      have h1 : Nat.card ↥(N.subgroupOf S) = Nat.card ↥(pPrimeCore 2 ↥A) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hNS).toEquiv, hNdef,
          card_map_of_injective A.subtype_injective]
      rw [h1]
      exact fun h => (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two ↥A))
        (even_iff_two_dvd.mpr h)
    let f₁ : ↥S →* ↥S ⧸ N.subgroupOf S := QuotientGroup.mk' _
    have hf₁ : Function.Surjective f₁ := QuotientGroup.mk'_surjective _
    have hk₁ : ¬ 2 ∣ Nat.card f₁.ker := by
      rw [QuotientGroup.ker_mk']
      exact hNodd
    let f₂ : ↥J →* ↥S ⧸ N.subgroupOf S := f₁.comp (inclusion hJS)
    have hf₂ : Function.Surjective f₂ := by
      rw [← MonoidHom.range_eq_top]
      have hle : J.subgroupOf S ⊔ N.subgroupOf S ≤ f₂.range.comap f₁ := by
        refine sup_le ?_ ?_
        · intro x hx
          exact ⟨⟨(x : G), hx⟩, rfl⟩
        · intro x hx
          have h1 : f₁ x = 1 := by
            rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
            exact hx
          rw [mem_comap, h1]
          exact one_mem _
      have htop : f₂.range.comap f₁ = ⊤ :=
        top_le_iff.mp ((codisjoint_iff.mp (codisjoint_subgroupOf_sup J N)).ge.trans hle)
      rw [← map_comap_eq_self_of_surjective hf₁ f₂.range, htop, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hf₁]
    have hk₂ : ¬ 2 ∣ Nat.card f₂.ker := by
      have hle : f₂.ker.map (inclusion hJS) ≤ f₁.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have hc : Nat.card f₂.ker ∣ Nat.card f₁.ker := by
        rw [← card_map_of_injective (inclusion_injective hJS)]
        exact card_dvd_of_le hle
      exact fun h => hk₁ (h.trans hc)
    obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f₁ hf₁ hk₁
    obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f₂ hf₂ hk₂
    exact ⟨e₁.trans e₂.symm⟩

theorem isSolvableTwoComponentIn_sup {J A : Subgroup G} (hJA : J ≤ A)
    (hJs : (J.subgroupOf A).IsSubnormal) (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) :
    IsSolvableTwoComponentIn (J ⊔ (pPrimeCore 2 ↥A).map A.subtype) A ∧
      Nonempty (↥(J ⊔ (pPrimeCore 2 ↥A).map A.subtype) ⧸
        pPrimeCore 2 ↥(J ⊔ (pPrimeCore 2 ↥A).map A.subtype) ≃* SL(2, ZMod 3)) := by
  obtain ⟨h1, h2, h3, ⟨e'⟩⟩ := saturate hJA hJs
  exact ⟨⟨h1, h2, h3, .inr ⟨e'.trans e⟩⟩, ⟨e'.trans e⟩⟩

end Saturate

theorem map_inf_subnormal {G : Type} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).IsSubnormal) (x : ↥A) {J : Subgroup ↥A}
    (hJ : J ≤ centralizer {x}) (hJs : (J.subgroupOf (centralizer {x})).IsSubnormal) :
    J.map A.subtype ≤ B ⊓ centralizer {(x : G)} ∧
      ((J.map A.subtype).subgroupOf (B ⊓ centralizer {(x : G)})).IsSubnormal := by
  set C := centralizer ({x} : Set ↥A) with hC
  have hCA : C.map A.subtype = A ⊓ centralizer {(x : G)} := map_subtype_centralizer_mem x
  let eC : ↥C ≃* ↥(C.map A.subtype) := C.equivMapOfInjective A.subtype A.subtype_injective
  have hmap : (J.subgroupOf C).map eC.toMonoidHom =
      (J.map A.subtype).subgroupOf (C.map A.subtype) := by
    ext y
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, hwy⟩
      exact ⟨⟨w, hJ hw⟩, hw, Subtype.ext hwy⟩
  have h1 : ((J.map A.subtype).subgroupOf (C.map A.subtype)).IsSubnormal :=
    hmap ▸ hJs.map eC.surjective
  rw [hCA] at h1
  have hle1 : J.map A.subtype ≤ A ⊓ centralizer {(x : G)} := hCA ▸ map_mono hJ
  have hle : A ⊓ centralizer {(x : G)} ≤ B ⊓ centralizer {(x : G)} := inf_le_inf_right _ hAB
  have h2 : ((A ⊓ centralizer {(x : G)}).subgroupOf (B ⊓ centralizer {(x : G)})).IsSubnormal := by
    have h := hA.comap (inclusion (inf_le_left : B ⊓ centralizer {(x : G)} ≤ B))
    convert h using 1
    ext y
    simp only [mem_subgroupOf, mem_inf, mem_comap, coe_inclusion]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2.2⟩⟩
  exact ⟨hle1.trans hle, CFSG.GroupTheory.isSubnormal_subgroupOf_trans hle1 hle h1 h2⟩

theorem exists_lift_section {X : Type} [Group X] [Finite X] {β u : X}
    (huβ : u ∈ centralizer ({β} : Set X)) (hu : orderOf u = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})
    (hYs : (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})).IsSubnormal) :
    ∃ P : Subgroup X, P ≤ centralizer {β} ⊓ centralizer {u} ∧
      (P.subgroupOf (centralizer {β} ⊓ centralizer {u})).IsSubnormal ∧
      (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ P) ∧
      Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let u' : ↥M := ⟨u, huβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({u'} : Set ↥M)
  have hu'2 : u' * u' = 1 := Subtype.ext (by
    change u * u = 1
    rw [← sq, ← hu, pow_orderOf_eq_one])
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :=
    map_centralizer_eq (odd_card_pPrimeCore_two ↥M) hu'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two ↥M)) (even_iff_two_dvd.mpr
      (h2.trans hc))
  let P₀ := (Y.subgroupOf
    (centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})).comap φ
  have hP₀s : P₀.IsSubnormal := hYs.comap φ
  let g : ↥P₀ →* ↥Y := ((centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :
    Set (MBar β))).subtype.comp (φ.comp P₀.subtype)).codRestrict Y (fun x => x.2)
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := hφs ⟨y, hYle hy⟩
    have hcP : c ∈ P₀ := by
      change φ c ∈ Y.subgroupOf _
      rw [hc]
      exact hy
    refine ⟨⟨c, hcP⟩, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hc
    exact h1
  have hgk : ¬ 2 ∣ Nat.card g.ker := by
    have hle : g.ker.map P₀.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : g x = 1 := hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h2 := congrArg Subtype.val hx'
      exact h2
    have hc : Nat.card g.ker ∣ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective P₀.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => hφk (h2.trans hc)
  obtain ⟨e₀⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hgs hgk
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {u} := map_subtype_centralizer_mem u'
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {u}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  have hPle : (P₀.map C.subtype).map M.subtype ≤ centralizer {β} ⊓ centralizer {u} := by
    rw [← hCX]
    exact map_mono (map_subtype_le P₀)
  have hPeq : ((P₀.map C.subtype).map M.subtype).subgroupOf
      (centralizer {β} ⊓ centralizer {u}) = P₀.map eC.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((eC y : ↥(centralizer ({β} : Set X) ⊓ centralizer {u})) : X) = x :=
        congrArg Subtype.val hyx
      exact ⟨(y : ↥M), ⟨y, hy, rfl⟩, h1⟩
  let eP : ↥P₀ ≃* ↥((P₀.map C.subtype).map M.subtype) :=
    (P₀.equivMapOfInjective C.subtype C.subtype_injective).trans
      ((P₀.map C.subtype).equivMapOfInjective M.subtype M.subtype_injective)
  refine ⟨(P₀.map C.subtype).map M.subtype, hPle, by rw [hPeq]; exact hP₀s.map eC.surjective,
    ?_, ⟨(QuotientGroup.congr _ _ eP.symm (pPrimeCore_map_iso 2 eP.symm)).trans e₀⟩⟩
  intro w hw hwu hwY
  have hwu' : (⟨w, hw⟩ : ↥M) ∈ C := by
    rw [mem_centralizer_singleton_iff] at hwu ⊢
    exact Subtype.ext hwu
  have hwP : (⟨⟨w, hw⟩, hwu'⟩ : ↥C) ∈ P₀ := hwY
  exact ⟨⟨w, hw⟩, ⟨⟨⟨w, hw⟩, hwu'⟩, hwP, rfl⟩, rfl⟩

theorem lift_solvable {X : Type} [Group X] [Finite X] {β u : X}
    (huβ : u ∈ centralizer ({β} : Set X)) (hu : orderOf u = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})
    (hYs : (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})).IsSubnormal)
    (eY : ↥Y ⧸ pPrimeCore 2 ↥Y ≃* SL(2, ZMod 3)) :
    ∃ J : Subgroup X, IsSolvableTwoComponentIn J (centralizer {β} ⊓ centralizer {u}) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) ∧
      ∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ J := by
  obtain ⟨P, hPle, hPs, hmem, ⟨eP⟩⟩ := exists_lift_section huβ hu hYle hYs
  obtain ⟨hJ, hJe⟩ := isSolvableTwoComponentIn_sup hPle hPs (eP.trans eY)
  exact ⟨_, hJ, hJe, fun w hw hwu hwY => mem_sup_left (hmem w hw hwu hwY)⟩

end F3

end CFSG.ComponentClassification.HarrisLit.T1

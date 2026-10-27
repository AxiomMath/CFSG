module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBack
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SpinCover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.LieType.Universal.Spin
  CliffordAlgebra
open scoped MatrixGroups

section General

variable {G : Type} [Group G]

theorem isTwoComponentIn_inf_of_subnormal {L A J : Subgroup G} (hLA : L ≤ A)
    (hL : (L.subgroupOf A).IsSubnormal) (C : Subgroup G) (hJ : IsTwoComponentIn J (L ⊓ C)) :
    IsTwoComponentIn J (A ⊓ C) := by
  have hle : L ⊓ C ≤ A ⊓ C := inf_le_inf_right C hLA
  have h1 : ((L ⊓ C).subgroupOf (A ⊓ C)).IsSubnormal := by
    have h := hL.comap (inclusion (inf_le_left : A ⊓ C ≤ A))
    convert h using 1
    ext x
    simp only [mem_subgroupOf, mem_inf, mem_comap, coe_inclusion]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  exact ⟨hJ.1.trans hle, CFSG.GroupTheory.isSubnormal_subgroupOf_trans hJ.1 hle hJ.2.1 h1,
    hJ.2.2⟩

theorem normal_subgroupOf_map {G' : Type*} [Group G'] (f : G →* G') {J C : Subgroup G}
    (hJC : J ≤ C) (h : (J.subgroupOf C).Normal) : ((J.map f).subgroupOf (C.map f)).Normal := by
  rw [normal_subgroupOf_iff (map_mono hJC)]
  rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
  exact ⟨c * a * c⁻¹, (normal_subgroupOf_iff hJC).mp h a c ha hc, by simp⟩

theorem map_subtype_centralizer_mem {A : Subgroup G} (x : ↥A) :
    (centralizer ({x} : Set ↥A)).map A.subtype = A ⊓ centralizer {(x : G)} := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨hyA, hy⟩
    refine ⟨⟨y, hyA⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    exact mem_centralizer_singleton_iff.mp hy

theorem exists_mbarEquiv_of_mem_center {X : Type} [Group X] {β : X} (hβ : β ∈ center X) :
    ∃ e : MBar β ≃* X ⧸ pPrimeCore 2 X, ∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)),
      e (QuotientGroup.mk ⟨w, hw⟩) = (QuotientGroup.mk w : X ⧸ pPrimeCore 2 X) := by
  have htop : centralizer ({β} : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_singleton_iff]
    exact mem_center_iff.mp hβ g
  let ε : ↥(centralizer ({β} : Set X)) ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  exact ⟨QuotientGroup.congr _ _ ε (pPrimeCore_map_iso 2 ε), fun w hw =>
    QuotientGroup.congr_mk _ _ _ _ _⟩

end General

section Lift

variable {X : Type} [Group X] [Finite X]

theorem exists_lift_of_mbarEquiv {β u : X} (huβ : u ∈ centralizer ({β} : Set X))
    (hu : orderOf u = 2) {S : Type} [Group S] [Finite S] (Φ : MBar β ≃* S) {J : Subgroup S}
    (hJ : IsTwoComponentIn J (centralizer {Φ (QuotientGroup.mk ⟨u, huβ⟩)}))
    (hJn : (J.subgroupOf (centralizer {Φ (QuotientGroup.mk ⟨u, huβ⟩)})).Normal) :
    ∃ J' : Subgroup X, IsTwoComponentIn J' (centralizer {β} ⊓ centralizer {u}) ∧
      (J'.subgroupOf (centralizer {β} ⊓ centralizer {u})).Normal ∧
      (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (∃ k : ℕ, orderOf w = 2 ^ k) → Φ (QuotientGroup.mk ⟨w, hw⟩) ∈ J → w ∈ J') ∧
      Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  set ū : MBar β := QuotientGroup.mk ⟨u, huβ⟩ with hū
  set Y := J.map Φ.symm.toMonoidHom with hY
  have hcen : (centralizer ({Φ ū} : Set S)).map Φ.symm.toMonoidHom = centralizer {ū} := by
    rw [map_centralizer_singleton_mulEquiv, MulEquiv.symm_apply_apply]
  have hYle : Y ≤ centralizer {ū} := hcen ▸ map_mono hJ.1
  have hYc : IsTwoComponentIn Y (centralizer {ū}) :=
    hcen ▸ L35.isTwoComponentIn_map_of_injective _ Φ.symm.injective hJ
  have hYn : (Y.subgroupOf (centralizer {ū})).Normal :=
    hcen ▸ normal_subgroupOf_map Φ.symm.toMonoidHom hJ.1 hJn
  obtain ⟨J', hJ'le, hJ'c, hJ'mem, hJ'gen, -, g, hgs, hgk⟩ :=
    exists_lift_twoComponent huβ hu hYle ((isTwoComponentIn_iff hYle).mp hYc)
  have hmemY : ∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)),
      (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y ↔ Φ (QuotientGroup.mk ⟨w, hw⟩) ∈ J := by
    intro w hw
    rw [hY, mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨J', (isTwoComponentIn_iff hJ'le).mpr hJ'c, ?_, fun w hw hwu hk hwJ =>
    hJ'mem w hw hwu hk ((hmemY w hw).mpr hwJ), ?_⟩
  ·
    rw [normal_subgroupOf_iff hJ'le]
    intro a x ha hx
    have hxβ : x ∈ centralizer ({β} : Set X) := hx.1
    have hxu : x ∈ centralizer ({u} : Set X) := hx.2
    let S' := J'.comap (MulAut.conj x).toMonoidHom
    have hle : J' ≤ S' := by
      refine hJ'gen S' fun w hw hwu hk hwY => ?_
      show x * w * x⁻¹ ∈ J'
      have hc : x * w * x⁻¹ ∈ centralizer ({β} : Set X) :=
        mul_mem (mul_mem hxβ hw) (inv_mem hxβ)
      refine hJ'mem _ hc (mul_mem (mul_mem hxu hwu) (inv_mem hxu)) ?_ ?_
      · obtain ⟨k, hk⟩ := hk
        exact ⟨k, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hk]⟩
      ·
        have hxC : (QuotientGroup.mk ⟨x, hxβ⟩ : MBar β) ∈ centralizer {ū} := by
          rw [mem_centralizer_singleton_iff]
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          exact mem_centralizer_singleton_iff.mp hxu
        have hconj := (normal_subgroupOf_iff hYle).mp hYn _ _ hwY hxC
        have heq : (QuotientGroup.mk ⟨x * w * x⁻¹, hc⟩ : MBar β) =
            QuotientGroup.mk ⟨x, hxβ⟩ * QuotientGroup.mk ⟨w, hw⟩ *
              (QuotientGroup.mk ⟨x, hxβ⟩)⁻¹ := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          rfl
        rw [heq]
        exact hconj
    exact hle ha
  ·
    obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hgs hgk
    let eY : ↥Y ≃* ↥J := (J.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).symm
    exact ⟨e₁.trans (QuotientGroup.congr _ _ eY (pPrimeCore_map_iso 2 eY))⟩

end Lift

section SpinSeven

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_center_of_le_centralizer {z : G} {L : Subgroup G} (hLz : L ≤ centralizer {z})
    (hzL : z ∈ L) : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hLz g.2)

theorem eq_of_mem_center_spinSeven {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ center (spinGroup (quadOdd 3 K))) (hx1 : x ≠ 1) :
    x = spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rw [center_spinGroup_quadOdd_eq_ker h2 le_rfl] at hx
  rcases (mem_ker_spinAction_iff _ (nondegenerate_quadOdd 3 K) x).mp hx with h | h
  · exact absurd h hx1
  · exact h

theorem isSLTwoOver_quot_of_equiv {A B : Type} [Group A] [Group B] [Finite B] {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (h5 : 5 ≤ p ^ k)
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (hB : IsSLTwoOver (p ^ k) B) :
    IsSLTwoOver (p ^ k) (A ⧸ pPrimeCore 2 A) := by
  obtain ⟨-, -, -, hO⟩ := Lemma47.sl2_facts hp hp2 hk h5 hB
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hB
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(e.trans
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)).trans eF⟩⟩

theorem exists_lift_to_ambient {z u : G} {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) (huL : u ∈ L) (hu : orderOf u = 2)
    (hu'z : (⟨u, huL⟩ : ↥L) ∈ centralizer ({⟨z, hzL⟩} : Set ↥L)) {S : Type} [Group S] [Finite S]
    (Φ : MBar (⟨z, hzL⟩ : ↥L) ≃* S) {J : Subgroup S}
    (hJ : IsTwoComponentIn J (centralizer {Φ (QuotientGroup.mk ⟨⟨u, huL⟩, hu'z⟩)}))
    (hJn : (J.subgroupOf (centralizer {Φ (QuotientGroup.mk ⟨⟨u, huL⟩, hu'z⟩)})).Normal) :
    ∃ J' : Subgroup G, IsTwoComponentIn J' (centralizer {z} ⊓ centralizer {u}) ∧ J' ≤ L ∧
      (J'.subgroupOf (L ⊓ centralizer {u})).Normal ∧
      (∀ (w : G) (hwL : w ∈ L) (hw : (⟨w, hwL⟩ : ↥L) ∈ centralizer ({⟨z, hzL⟩} : Set ↥L)),
        w ∈ centralizer {u} → (∃ k : ℕ, orderOf w = 2 ^ k) →
          Φ (QuotientGroup.mk ⟨⟨w, hwL⟩, hw⟩) ∈ J → w ∈ J') ∧
      Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  obtain ⟨J'', hJ''c, hJ''n, hJ''mem, ⟨eQ⟩⟩ := exists_lift_of_mbarEquiv hu'z hu' Φ hJ hJn
  have htop : centralizer ({⟨z, hzL⟩} : Set ↥L) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_singleton_iff]
    exact mem_center_iff.mp (mem_center_of_le_centralizer hL.1 hzL) g
  have hCL : (centralizer ({⟨z, hzL⟩} : Set ↥L) ⊓ centralizer {(⟨u, huL⟩ : ↥L)}).map L.subtype =
      L ⊓ centralizer {u} := by
    rw [htop, top_inf_eq, map_subtype_centralizer_mem]
  have hJL : IsTwoComponentIn (J''.map L.subtype) (L ⊓ centralizer {u}) :=
    hCL ▸ L35.isTwoComponentIn_map_of_injective L.subtype L.subtype_injective hJ''c
  refine ⟨J''.map L.subtype, isTwoComponentIn_inf_of_subnormal hL.1 hL.2.1 _ hJL,
    map_subtype_le J'', hCL ▸ normal_subgroupOf_map L.subtype hJ''c.1 hJ''n, ?_, ?_⟩
  · intro w hwL hw hwu hk hwJ
    have hwu' : (⟨w, hwL⟩ : ↥L) ∈ centralizer {(⟨u, huL⟩ : ↥L)} := by
      rw [mem_centralizer_singleton_iff] at hwu ⊢
      exact Subtype.ext hwu
    obtain ⟨k, hk⟩ := hk
    exact ⟨⟨w, hwL⟩, hJ''mem _ hw hwu' ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩ hwJ, rfl⟩
  · let e : ↥J'' ≃* ↥(J''.map L.subtype) := J''.equivMapOfInjective L.subtype L.subtype_injective
    exact ⟨(QuotientGroup.congr _ _ e.symm (pPrimeCore_map_iso 2 e.symm)).trans eQ⟩

omit [Finite G] in
theorem mem_of_map_center_eq_zpowers {J : Subgroup G} {y : G}
    (h : (center ↥J).map J.subtype = zpowers y) : y ∈ J := by
  have hy : y ∈ (center ↥J).map J.subtype := h ▸ mem_zpowers y
  obtain ⟨a, -, rfl⟩ := hy
  exact a.2

theorem spinSeven_three_at {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {x : spinGroup (quadOdd 3 K)}
    (hx : orderOf x = 2) (hxZ : x ∉ center (spinGroup (quadOdd 3 K))) :
    ∃ J₁ J₂ J₃ : Subgroup (spinGroup (quadOdd 3 K)),
      (IsTwoComponentIn J₁ (centralizer {x}) ∧ (J₁.subgroupOf (centralizer {x})).Normal ∧
        IsSLTwoOver (p ^ f) ↥J₁ ∧
        spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero ∈ J₁) ∧
      (IsTwoComponentIn J₂ (centralizer {x}) ∧ (J₂.subgroupOf (centralizer {x})).Normal ∧
        IsSLTwoOver (p ^ f) ↥J₂ ∧ x ∈ J₂) ∧
      (IsTwoComponentIn J₃ (centralizer {x}) ∧ (J₃.subgroupOf (centralizer {x})).Normal ∧
        IsSLTwoOver (p ^ f) ↥J₃ ∧
        spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero * x ∈ J₃) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  set ν := spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero with hν
  obtain ⟨z, t, J₁, J₂, J₃, hz2, hZ, ht2, htZ, hJ₁, hJ₂, hJ₃, hn₁, hn₂, hn₃, hs₁, hs₂, hs₃, hc₁,
    hc₂, hc₃⟩ := spinSeven_lemma410c (K := K) hp hp2 hK h5
  have hzν : z = ν := by
    have hzc : z ∈ center (spinGroup (quadOdd 3 K)) := hZ ▸ mem_zpowers z
    refine eq_of_mem_center_spinSeven h2 hzc ?_
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hνc : ν ∈ center (spinGroup (quadOdd 3 K)) := hzν ▸ (hZ ▸ mem_zpowers z)
  obtain ⟨g₁, hg₁⟩ := spinSeven_lemma410b hodd (by omega) hx hxZ
  obtain ⟨g₂, hg₂⟩ := spinSeven_lemma410b hodd (by omega) ht2 htZ
  set c := g₁ * g₂⁻¹ with hc
  have hct : MulAut.conj c t = x := by
    rw [MulAut.conj_apply, ← hg₁, ← hg₂, hc]
    group
  have hcen : (centralizer ({t} : Set (spinGroup (quadOdd 3 K)))).map
      (MulAut.conj c).toMonoidHom = centralizer {x} := by
    rw [map_centralizer_singleton_mulEquiv, hct]
  have hcν : MulAut.conj c ν = ν := by
    rw [MulAut.conj_apply, mem_center_iff.mp hνc c, mul_inv_cancel_right]
  have key : ∀ {J : Subgroup (spinGroup (quadOdd 3 K))}, IsTwoComponentIn J (centralizer {t}) →
      (J.subgroupOf (centralizer {t})).Normal → IsSLTwoOver (p ^ f) ↥J →
      IsTwoComponentIn (J.map (MulAut.conj c).toMonoidHom) (centralizer {x}) ∧
        ((J.map (MulAut.conj c).toMonoidHom).subgroupOf (centralizer {x})).Normal ∧
        IsSLTwoOver (p ^ f) ↥(J.map (MulAut.conj c).toMonoidHom) := fun hJ hn hs =>
    ⟨hcen ▸ L35.isTwoComponentIn_map_of_injective _ (MulAut.conj c).injective hJ,
      hcen ▸ normal_subgroupOf_map _ hJ.1 hn, isSLTwoOver_map_mulEquiv _ hs⟩
  refine ⟨J₁.map (MulAut.conj c).toMonoidHom, J₂.map (MulAut.conj c).toMonoidHom,
    J₃.map (MulAut.conj c).toMonoidHom, ⟨(key hJ₁ hn₁ hs₁).1, (key hJ₁ hn₁ hs₁).2.1,
      (key hJ₁ hn₁ hs₁).2.2, ?_⟩, ⟨(key hJ₂ hn₂ hs₂).1, (key hJ₂ hn₂ hs₂).2.1,
      (key hJ₂ hn₂ hs₂).2.2, ?_⟩, ⟨(key hJ₃ hn₃ hs₃).1, (key hJ₃ hn₃ hs₃).2.1,
      (key hJ₃ hn₃ hs₃).2.2, ?_⟩⟩
  · exact ⟨ν, hzν ▸ mem_of_map_center_eq_zpowers hc₁, hcν⟩
  · exact ⟨t, mem_of_map_center_eq_zpowers hc₂, hct⟩
  · refine ⟨t * z, mem_of_map_center_eq_zpowers hc₃, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, map_mul, hct, hzν, hcν]
    exact mem_center_iff.mp hνc x

theorem odd_card_pPrimeCore_two (L : Type) [Group L] [Finite L] :
    Odd (Nat.card (pPrimeCore 2 L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card))

theorem spinSeven_lift_three {z u : G} {L : Subgroup G} {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L)) (huL : u ∈ L)
    (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L)) :
    ∃ J₁ J₂ J₃ : Subgroup G,
      (IsTwoComponentIn J₁ (centralizer {z} ⊓ centralizer {u}) ∧ J₁ ≤ L ∧
        (J₁.subgroupOf (L ⊓ centralizer {u})).Normal ∧
        IsSLTwoOver (p ^ f) (↥J₁ ⧸ pPrimeCore 2 ↥J₁) ∧ z ∈ J₁) ∧
      (IsTwoComponentIn J₂ (centralizer {z} ⊓ centralizer {u}) ∧ J₂ ≤ L ∧
        (J₂.subgroupOf (L ⊓ centralizer {u})).Normal ∧
        IsSLTwoOver (p ^ f) (↥J₂ ⧸ pPrimeCore 2 ↥J₂) ∧ u ∈ J₂) ∧
      (IsTwoComponentIn J₃ (centralizer {z} ⊓ centralizer {u}) ∧ J₃ ≤ L ∧
        (J₃.subgroupOf (L ⊓ centralizer {u})).Normal ∧
        IsSLTwoOver (p ^ f) (↥J₃ ⧸ pPrimeCore 2 ↥J₃) ∧ z * u ∈ J₃) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinOdd h5 hcov
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have hz'c := mem_center_of_le_centralizer hL.1 hzL
  have hu'z : (⟨u, huL⟩ : ↥L) ∈ centralizer ({⟨z, hzL⟩} : Set ↥L) := by
    rw [mem_centralizer_singleton_iff]
    exact mem_center_iff.mp hz'c _
  have hz'z : (⟨z, hzL⟩ : ↥L) ∈ centralizer ({⟨z, hzL⟩} : Set ↥L) :=
    mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨e₀, he₀⟩ := exists_mbarEquiv_of_mem_center hz'c
  set Φ := e₀.trans e₁ with hΦ
  have hΦw : ∀ (w : ↥L) (hw : w ∈ centralizer ({⟨z, hzL⟩} : Set ↥L)),
      Φ (QuotientGroup.mk ⟨w, hw⟩) = e₁ (QuotientGroup.mk w) := fun w hw => by
    rw [hΦ, MulEquiv.trans_apply, he₀]
  have hOodd := odd_card_pPrimeCore_two ↥L
  have hx2 : orderOf (Φ (QuotientGroup.mk ⟨⟨u, huL⟩, hu'z⟩)) = 2 := by
    rw [hΦw, MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hu)
  have hxZ : Φ (QuotientGroup.mk ⟨⟨u, huL⟩, hu'z⟩) ∉ center (spinGroup (quadOdd 3 K)) := by
    rw [hΦw, mem_center_mulEquiv_iff]
    exact huZ
  obtain ⟨Y₁, Y₂, Y₃, ⟨hY₁, hn₁, hs₁, hν₁⟩, ⟨hY₂, hn₂, hs₂, hu₂⟩, ⟨hY₃, hn₃, hs₃, hν₃⟩⟩ :=
    spinSeven_three_at hp hp2 hK h5 hx2 hxZ
  have hΦz : Φ (QuotientGroup.mk ⟨⟨z, hzL⟩, hz'z⟩) =
      spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero := by
    have hz2 : orderOf (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 2 :=
      orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hz)
    rw [hΦw]
    refine eq_of_mem_center_spinSeven h2 ?_ ?_
    · rw [mem_center_mulEquiv_iff, mem_center_iff]
      intro g
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz'c g₀]
    · intro h1
      rw [← MulEquiv.orderOf_eq e₁, h1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
  have : Finite (spinGroup (quadOdd 3 K)) := Finite.of_equiv _ e₁.toEquiv
  obtain ⟨J₁, hJ₁c, hJ₁L, hJ₁n, hJ₁mem, ⟨hq₁⟩⟩ :=
    exists_lift_to_ambient hL hzL huL hu hu'z Φ hY₁ hn₁
  obtain ⟨J₂, hJ₂c, hJ₂L, hJ₂n, hJ₂mem, ⟨hq₂⟩⟩ :=
    exists_lift_to_ambient hL hzL huL hu hu'z Φ hY₂ hn₂
  obtain ⟨J₃, hJ₃c, hJ₃L, hJ₃n, hJ₃mem, ⟨hq₃⟩⟩ :=
    exists_lift_to_ambient hL hzL huL hu hu'z Φ hY₃ hn₃
  have hzu : z ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hL.1 huL)).symm
  have huu : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  refine ⟨J₁, J₂, J₃, ⟨hJ₁c, hJ₁L, hJ₁n, isSLTwoOver_quot_of_equiv hp hp2 hf h5 hq₁ hs₁, ?_⟩,
    ⟨hJ₂c, hJ₂L, hJ₂n, isSLTwoOver_quot_of_equiv hp hp2 hf h5 hq₂ hs₂, ?_⟩,
    ⟨hJ₃c, hJ₃L, hJ₃n, isSLTwoOver_quot_of_equiv hp hp2 hf h5 hq₃ hs₃, ?_⟩⟩
  · exact hJ₁mem z hzL hz'z hzu ⟨1, by rw [pow_one]; exact hz⟩ (by rw [hΦz]; exact hν₁)
  · exact hJ₂mem u huL hu'z huu ⟨1, by rw [pow_one]; exact hu⟩ hu₂
  · have hzuL : z * u ∈ L := mul_mem hzL huL
    have hzu' : (⟨z * u, hzuL⟩ : ↥L) ∈ centralizer ({⟨z, hzL⟩} : Set ↥L) := by
      rw [mem_centralizer_singleton_iff]
      exact mem_center_iff.mp hz'c _
    have hcomm : z * u = u * z := (mem_centralizer_singleton_iff.mp hzu)
    have hord : ∃ k : ℕ, orderOf (z * u) = 2 ^ k := by
      have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
      have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
      have h1 : (z * u) ^ 2 = 1 := by
        rw [(show Commute z u from hcomm).mul_pow, hz2, hu2, one_mul]
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one h1 : orderOf (z * u) ∣ 2 ^ 1)
      exact ⟨k, hk⟩
    refine hJ₃mem (z * u) hzuL hzu' (mul_mem hzu huu) hord ?_
    have hprod : (QuotientGroup.mk ⟨⟨z * u, hzuL⟩, hzu'⟩ : MBar (⟨z, hzL⟩ : ↥L)) =
        QuotientGroup.mk ⟨⟨z, hzL⟩, hz'z⟩ * QuotientGroup.mk ⟨⟨u, huL⟩, hu'z⟩ := by
      rw [← QuotientGroup.mk_mul]
      rfl
    rw [hprod, map_mul, hΦz]
    exact hν₃

theorem spinSeven_conj_of_involution {L : Subgroup G} {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L)) {u v : G} (huL : u ∈ L)
    (hvL : v ∈ L) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L))
    (hvZ : (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L)) :
    ∃ x ∈ L, x * u * x⁻¹ = v := by
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinOdd h5 hcov
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hOodd := odd_card_pPrimeCore_two ↥L
  have h2u : orderOf (e₁ (QuotientGroup.mk (⟨u, huL⟩ : ↥L))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hu)
  have h2v : orderOf (e₁ (QuotientGroup.mk (⟨v, hvL⟩ : ↥L))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hv)
  obtain ⟨g₁, hg₁⟩ := spinSeven_lemma410b hodd (by omega) h2u
    (by rw [mem_center_mulEquiv_iff]; exact huZ)
  obtain ⟨g₂, hg₂⟩ := spinSeven_lemma410b hodd (by omega) h2v
    (by rw [mem_center_mulEquiv_iff]; exact hvZ)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e₁.symm (g₂ * g₁⁻¹))
  have hconj : (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      (QuotientGroup.mk g : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk ⟨u, huL⟩ *
        (QuotientGroup.mk g : ↥L ⧸ pPrimeCore 2 ↥L)⁻¹ := by
    apply e₁.injective
    rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, ← hg₁, ← hg₂]
    group
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hv' : orderOf (⟨v, hvL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hv
  have huu : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := by
    rw [← pow_two, ← hu', pow_orderOf_eq_one]
  have hvv : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := by
    rw [← pow_two, ← hv', pow_orderOf_eq_one]
  obtain ⟨x, hx⟩ := exists_conj_of_mk_conj hOodd hvv huu hconj
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end SpinSeven

end CFSG.ComponentClassification.HarrisLit.T1

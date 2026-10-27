module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cICent
public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def redJ1 (J R : Subgroup G) : Subgroup G := J ⊓ centralizer (R : Set G)

@[expose] def redJ0 (J R : Subgroup G) : Subgroup G := O2Of (redJ1 J R)

theorem redJ1_le_J (J R : Subgroup G) : redJ1 J R ≤ J := inf_le_left

theorem redJ0_le_redJ1 (J R : Subgroup G) : redJ0 J R ≤ redJ1 J R := Subgroup.map_subtype_le _

theorem redJ0_le_J (J R : Subgroup G) : redJ0 J R ≤ J := (redJ0_le_redJ1 J R).trans inf_le_left

theorem redJ0_comm (J R : Subgroup G) : ∀ x ∈ redJ0 J R, ∀ r ∈ R, x * r = r * x := by
  intro x hx r hr
  have h : x ∈ centralizer (R : Set G) := (redJ0_le_redJ1 J R hx).2
  exact (mem_centralizer_iff.mp h r hr).symm

@[expose] def hatMap (J : Subgroup G) {X : Subgroup G} (h : X ≤ J) : ↥X →* ↥J ⧸ pPrimeCore 2 ↥J :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp (Subgroup.inclusion h)

theorem hatMap_apply (J : Subgroup G) {X : Subgroup G} (h : X ≤ J) (x : ↥X) :
    hatMap J h x = QuotientGroup.mk (⟨x, h x.2⟩ : ↥J) := rfl

theorem mem_ker_hatMap (J : Subgroup G) {X : Subgroup G} (h : X ≤ J) (x : ↥X) :
    x ∈ (hatMap J h).ker ↔ (x : G) ∈ pPrimeCoreOf 2 J := by
  rw [MonoidHom.mem_ker, hatMap_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact ⟨⟨x, h x.2⟩, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, h x.2⟩ := Subtype.ext hyx
    rwa [this] at hy

end Defs

section Cover

variable {G : Type} [Group G] [Finite G]

theorem odd_card_pPrimeCoreOf_J (J : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 J)) := by
  have h : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥J)) := pPrimeCore_coprime_card (p := 2)
  have h2 : Nat.card ↥(pPrimeCoreOf 2 J) = Nat.card ↥(pPrimeCore 2 ↥J) :=
    Subgroup.card_map_of_injective J.subtype_injective
  rw [h2]
  exact Nat.coprime_two_left.mp h

omit [Finite G] in
theorem conj_mem_pPrimeCoreOf_of_mem {J : Subgroup G} {g y : G} (hg : g ∈ J)
    (hy : y ∈ pPrimeCoreOf 2 J) : g * y * g⁻¹ ∈ pPrimeCoreOf 2 J := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹,
    (pPrimeCore_normal (p := 2) (G := ↥J)).conj_mem y' hy' ⟨g, hg⟩, by simp⟩

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf_of_mem {J : Subgroup G} {g : G} (hg : g ∈ J) :
    g ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_pPrimeCoreOf_of_mem hg hy, fun hy => ?_⟩
  have h := conj_mem_pPrimeCoreOf_of_mem (inv_mem hg) hy
  simpa [mul_assoc] using h

theorem exists_cover_centralizer {J R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hC : R ≤ centralizerSection J (pPrimeCoreOf 2 J)) :
    ∀ j ∈ J, ∃ x ∈ J ⊓ centralizer (R : Set G), ∃ n ∈ pPrimeCoreOf 2 J, j = x * n := by
  intro j hj
  have hNJ : pPrimeCoreOf 2 J ≤ J := Subgroup.map_subtype_le _
  have hRn : ∀ r ∈ R, r ∈ normalizer (J : Set G) ∧
      r ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) ∧
      ∀ k ∈ J, ⁅k, r⁆ ∈ pPrimeCoreOf 2 J := fun r hr => hC hr
  set M : Subgroup G := J ⊔ R with hM
  have hJM : J ≤ M := le_sup_left
  have hRM : R ≤ M := le_sup_right
  have hNorm : M ≤ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) := by
    refine sup_le (fun g hg => mem_normalizer_pPrimeCoreOf_of_mem hg) (fun r hr => (hRn r hr).2.1)
  have hNM : pPrimeCoreOf 2 J ≤ M := hNJ.trans hJM
  let N' : Subgroup ↥M := (pPrimeCoreOf 2 J).subgroupOf M
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hNorm
  have hN'odd : Odd (Nat.card N') := by
    have : Nat.card ↥N' = Nat.card ↥(pPrimeCoreOf 2 J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    rw [this]
    exact odd_card_pPrimeCoreOf_J J
  let W' : Subgroup ↥M := R.subgroupOf M
  have hW' : IsPGroup 2 ↥W' := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
  let c : ↥M := ⟨j, hJM hj⟩
  have hc : ∀ w ∈ W', QuotientGroup.mk' N' w * QuotientGroup.mk' N' c =
      QuotientGroup.mk' N' c * QuotientGroup.mk' N' w := by
    intro w hw
    have hwR : (w : G) ∈ R := hw
    have h1 : ⁅j, (w : G)⁆ ∈ pPrimeCoreOf 2 J := (hRn _ hwR).2.2 j hj
    have h2 : ⁅c, w⁆ ∈ N' := by
      show (⁅c, w⁆ : ↥M).1 ∈ pPrimeCoreOf 2 J
      exact h1
    have h3 : QuotientGroup.mk' N' ⁅c, w⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa using h3)).symm
  obtain ⟨x, hx1, hx2⟩ := exists_mem_centralizer_coset N' hN'odd W' hW' c hc
  have hxc : c⁻¹ * x ∈ N' := by
    have : QuotientGroup.mk' N' (c⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hx1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hxc' : (c⁻¹ * x).1 ∈ pPrimeCoreOf 2 J := hxc
  have hxJ : (x : G) ∈ J := by
    have h1 : (x : G) = j * (c⁻¹ * x).1 := by simp [c]
    rw [h1]
    exact mul_mem hj (hNJ hxc')
  refine ⟨x.1, ⟨hxJ, ?_⟩, ((c⁻¹ * x).1)⁻¹, inv_mem hxc', ?_⟩
  · show (x : G) ∈ centralizer (R : Set G)
    rw [mem_centralizer_iff]
    intro r hr
    have := mem_centralizer_iff.mp hx2 ⟨r, hRM hr⟩ (show (⟨r, hRM hr⟩ : ↥M) ∈ W' from hr)
    exact congrArg Subtype.val this
  · simp [c]


theorem redJ0_cover {J R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hC : R ≤ centralizerSection J (pPrimeCoreOf 2 J))
    (hperf : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J)) :
    ∀ j ∈ J, ∃ x ∈ redJ0 J R, ∃ n ∈ pPrimeCoreOf 2 J, j = x * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥(redJ1 J R) →* ↥J ⧸ pPrimeCore 2 ↥J := hatMap J (redJ1_le_J J R)
  have hcov := exists_cover_centralizer hR hC
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, n, hn, hjx⟩ := hcov j j.2
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hatMap_apply]
    obtain ⟨n', hn', rfl⟩ := hn
    have h1 : (⟨x, (redJ1_le_J J R) hx⟩ : ↥J)⁻¹ * j = n' := by
      apply Subtype.ext
      simp [hjx]
    exact QuotientGroup.eq.mpr (h1 ▸ hn')
  set O : Subgroup ↥(redJ1 J R) := oResidual 2 ↥(redJ1 J R) with hO
  let B : Subgroup (↥J ⧸ pPrimeCore 2 ↥J) := O.map f
  have hBn : B.Normal := Subgroup.Normal.map inferInstance f hsurj
  have hOn : O.Normal := CFSG.RankThree.Transfer.oResidual_normal 2 _
  have hQ : IsPGroup 2 (↥(redJ1 J R) ⧸ O) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le O le_rfl
  have hQB : IsPGroup 2 ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ B) := by
    let g : ↥(redJ1 J R) →* (↥J ⧸ pPrimeCore 2 ↥J) ⧸ B := (QuotientGroup.mk' B).comp f
    have hg : O ≤ g.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨y, hy, rfl⟩
    exact hQ.of_surjective (QuotientGroup.lift O g hg)
      (fun q => by
        obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨y, rfl⟩ := hsurj q'
        exact ⟨QuotientGroup.mk y, rfl⟩)
  have hres : oResidual 2 (↥J ⧸ pPrimeCore 2 ↥J) ≤ B :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.oResidual_le_of_isPGroup_quotient hQB
  have htop : B = ⊤ := by
    rw [eq_top_iff]
    refine le_trans ?_ hres
    exact CFSG.GH74.GLS.Stage1.Main.perfect_le_oResidual ⊤
      (Group.IsPerfect.ofSurjective
        (f := (Subgroup.topEquiv (G := ↥J ⧸ pPrimeCore 2 ↥J)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥J ⧸ pPrimeCore 2 ↥J)).symm.surjective)
  intro j hj
  obtain ⟨x, hx, n, hn, hjx⟩ := hcov j hj
  have hxB : f ⟨x, hx⟩ ∈ B := by rw [htop]; trivial
  obtain ⟨y, hy, hyx⟩ := hxB
  refine ⟨(y : G), ⟨y, hy, rfl⟩, ((y : G)⁻¹ * x) * n, ?_, ?_⟩
  · have hm : ((y : G)⁻¹ * x) ∈ pPrimeCoreOf 2 J := by
      have : (y⁻¹ * ⟨x, hx⟩ : ↥(redJ1 J R)) ∈ (hatMap J (redJ1_le_J J R)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      exact (mem_ker_hatMap J (redJ1_le_J J R) _).mp this
    exact mul_mem hm hn
  · rw [hjx]; group


theorem l31_reduce {H J R : Subgroup G} (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J))) :
    IsPGroup 2 ↥R ∧ R ≤ H ∧ R ≤ centralizerSection J (pPrimeCoreOf 2 J) ∧
      (∀ x ∈ redJ0 J R, ∀ r ∈ R, x * r = r * x) ∧ redJ0 J R ≤ J ∧
      (∀ j ∈ J, ∃ x ∈ redJ0 J R, ∃ n ∈ pPrimeCoreOf 2 J, j = x * n) := by
  have hle : R ≤ H ⊓ centralizerSection J (pPrimeCoreOf 2 J) := hR.le
  have hpg : IsPGroup 2 ↥R := hR.isPGroup
  have hperf : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) := (TwoThin.isQuasisimple_hat hJ).1
  exact ⟨hpg, hle.trans inf_le_left, hle.trans inf_le_right, redJ0_comm J R, redJ0_le_J J R,
    redJ0_cover hpg (hle.trans inf_le_right) hperf⟩

end Cover

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

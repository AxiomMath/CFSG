module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma34
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec3
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut
public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_sylow_le_center_of_sz {A : Type} [Group A] [Finite A]
    (hA : commutator A = ⊤) {a : ℕ} (ha : 1 ≤ a) (e : A ⧸ center A ≃* Sz a)
    (heven : Even (Nat.card (center A))) (P : Sylow 2 A) :
    centralizer ((P : Subgroup A) : Set A) ≤ center A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.LieType.Steinberg.oddPart (center A) le_rfl with hNdef
  have hNZ : N ≤ center A := fun _ hc => hc.1
  have hN : N ≤ (QuotientGroup.mk' (center A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hNZ
  set η₀ : A ⧸ N →* A ⧸ center A := QuotientGroup.lift N (QuotientGroup.mk' (center A)) hN
  set η : A ⧸ N →* Sz a := e.toMonoidHom.comp η₀
  have : Group.IsPerfect (A ⧸ N) :=
    ⟨commutator_eq_top_of_surjective (QuotientGroup.mk'_surjective N) hA⟩
  have hsurj₀ : Function.Surjective η₀ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) q
    exact ⟨x, rfl⟩
  have hsurj : Function.Surjective η := e.surjective.comp hsurj₀
  have hker : η.ker = (center A).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_lift,
      QuotientGroup.ker_mk']
  have hcen : η.ker ≤ center (A ⧸ N) := by
    rw [hker]
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hc g)]
  have hp : IsPGroup 2 η.ker := by
    rintro ⟨x, hx⟩
    rw [hker] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨k, hk⟩ := CFSG.LieType.Steinberg.exists_pow_two_pow_mem_oddPart (le_refl (center A)) hc
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hne : η.ker ≠ ⊥ := by
    obtain ⟨⟨c, hc⟩, hco⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hco' : orderOf c = 2 := by rw [← hco, Subgroup.orderOf_mk]
    intro hb
    have hmem : QuotientGroup.mk' N c ∈ η.ker := by
      rw [hker]
      exact ⟨c, hc, rfl⟩
    rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have := hmem.2
    rw [hco'] at this
    exact absurd this (by decide)
  have hC := (CFSG.ShultStronglyClosedTI.suzukiCover_native_nontrivial_Sylow_centralizer a ha η
    hsurj hcen hp hne).1 (P.mapSurjective (QuotientGroup.mk'_surjective N))
  intro x hx
  have hx' : QuotientGroup.mk' N x ∈ centralizer
      ((P.mapSurjective (QuotientGroup.mk'_surjective N) : Sylow 2 (A ⧸ N)) : Set (A ⧸ N)) := by
    rw [mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ (P : Subgroup A).map (QuotientGroup.mk' N) := by
      rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N)]
      exact hp
    obtain ⟨p, hp'', rfl⟩ := hp'
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx p hp'')]
  rw [hC, hker] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  have h1 : z⁻¹ * x ∈ N := QuotientGroup.eq.mp hzx
  have := mul_mem hz (hNZ h1)
  simpa using this

theorem exponent_two_of_triple {Y : Type*} [Group Y] {W Z : Subgroup Y}
    (hZc : Z ≤ center Y) (hZ2 : ∀ z ∈ Z, z * z = 1) (hcomm : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ Z)
    (hsq : ∀ x ∈ W, x * x ∈ Z)
    (htrans : ∀ x ∈ W, ∀ y ∈ W, x ∉ Z → y ∉ Z → x * x = y * y)
    (hbig : ∀ x ∈ W, ∀ y ∈ W, ∃ w ∈ W, w ∉ Z ∧ x⁻¹ * w ∉ Z ∧ y⁻¹ * w ∉ Z ∧ (x * y)⁻¹ * w ∉ Z) :
    ∀ x ∈ W, x * x = 1 := by
  by_cases hWZ : ∃ x₀ ∈ W, x₀ ∉ Z
  · obtain ⟨x₀, hx₀W, hx₀Z⟩ := hWZ
    set c := x₀ * x₀ with hc
    have hcZ : c ∈ Z := hsq x₀ hx₀W
    have key : ∀ x ∈ W, ∀ y ∈ W, x ∉ Z → y ∉ Z → x⁻¹ * y ∉ Z → ⁅y, x⁆ = c⁻¹ := by
      intro x hx y hy hxZ hyZ hxyZ
      have hxy : x * y ∉ Z := by
        intro h'
        apply hxyZ
        have h2 : x⁻¹ * y = (x * x)⁻¹ * (x * y) := by group
        rw [h2]
        exact Z.mul_mem (Z.inv_mem (hsq x hx)) h'
      have hcm : ⁅y, x⁆ ∈ center Y := hZc (hcomm y hy x hx)
      have h1 := CFSG.ProperTwoGeneratedCore.Lemma37.CoverExclusion.mul_mul_self_eq hcm
      rw [htrans (x * y) (W.mul_mem hx hy) x₀ hx₀W hxy hx₀Z, htrans x hx x₀ hx₀W hxZ hx₀Z,
        htrans y hy x₀ hx₀W hyZ hx₀Z] at h1
      have hcc : c * c * c⁻¹ = c := by group
      calc ⁅y, x⁆ = ⁅y, x⁆ * c * c * c⁻¹ * c⁻¹ := by group
        _ = c * c⁻¹ * c⁻¹ := by rw [show ⁅y, x⁆ * c * c = c from h1.symm]
        _ = c⁻¹ := by group
    obtain ⟨y, hyW, hyZ, hy1, -, -⟩ := hbig x₀ hx₀W 1 W.one_mem
    obtain ⟨w, hwW, hwZ, hw1, hw2, hw3⟩ := hbig x₀ hx₀W y hyW
    have hyx := key x₀ hx₀W y hyW hx₀Z hyZ hy1
    have hwx := key x₀ hx₀W w hwW hx₀Z hwZ hw1
    have hywZ : y * w ∉ Z := by
      intro h'
      apply hw2
      have h2 : y⁻¹ * w = (y * y)⁻¹ * (y * w) := by group
      rw [h2]
      exact Z.mul_mem (Z.inv_mem (hsq y hyW)) h'
    have hxywZ : x₀⁻¹ * (y * w) ∉ Z := by
      intro h'
      apply hw3
      have h2 : (x₀ * y)⁻¹ * w =
          ⁅y⁻¹, x₀⁻¹⁆ * (x₀⁻¹ * (y * y)⁻¹ * x₀) * (x₀⁻¹ * (y * w)) := by
        rw [commutatorElement_def]
        group
      rw [h2]
      refine Z.mul_mem (Z.mul_mem (hcomm _ (W.inv_mem hyW) _ (W.inv_mem hx₀W)) ?_) h'
      have hyyc := hZc (Z.inv_mem (hsq y hyW))
      rw [mul_assoc, ← (mem_center_iff.mp hyyc x₀), inv_mul_cancel_left]
      exact Z.inv_mem (hsq y hyW)
    have hywx := key x₀ hx₀W (y * w) (W.mul_mem hyW hwW) hx₀Z hywZ hxywZ
    have hmul := CFSG.ProperTwoGeneratedCore.Lemma37.CoverExclusion.commutatorElement_mul_left_eq
      (y := y) (hZc (hcomm w hwW x₀ hx₀W))
    rw [hywx, hwx, hyx] at hmul
    have hc1 : c = 1 := by
      have : c⁻¹ = 1 := by
        calc c⁻¹ = c⁻¹ * c⁻¹ * c := by group
          _ = c⁻¹ * c := by rw [← hmul]
          _ = 1 := by group
      rwa [inv_eq_one] at this
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact hZ2 x hxZ
    · rw [htrans x hx x₀ hx₀W hxZ hx₀Z]
      exact hc1
  · push Not at hWZ
    exact fun x hx => hZ2 x (hWZ x hx)

omit [Finite G] in
theorem mem_normalizer_centralizer {T : Subgroup G} {g : G}
    (hg : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer ((centralizer (T : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hy t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
      simpa using this
    have := hy _ ht'
    calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * t := by group
  · intro hy t ht
    have ht' : g * t * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg t).mp ht
    have := hy _ ht'
    calc t * y = g⁻¹ * ((g * t * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * t * g⁻¹)) * g := by rw [this]
      _ = y * t := by group

omit [Finite G] in
theorem mem_sylow_of_mem_center {L : Subgroup G} [Finite L] (P : Sylow 2 L) {z : L}
    (hz : z ∈ center L) {k : ℕ} (hzk : z ^ 2 ^ k = 1) : z ∈ (P : Subgroup L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers z) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L Q P
  have hzQ : z ∈ (Q : Subgroup L) := hQ (mem_zpowers z)
  rw [← hl, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hc : (MulAut.conj l)⁻¹ • z = z := by
    rw [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc,
      ← mem_center_iff.mp hz l, inv_mul_cancel_left]
  rw [hc]
  exact hzQ

theorem preimage_center_exponent_two {L : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (e : rankTwoQuot L ≃* Sz a) (P : Sylow 2 L)
    (hZ2 : ∀ z ∈ (P : Subgroup L) ⊓ center L, z * z = 1) :
    ∀ x ∈ (P : Subgroup L) ⊓ (((P : Subgroup L).map (QuotientGroup.mk' (center L))) ⊓
      centralizer ((((P : Subgroup L).map (QuotientGroup.mk' (center L))) : Subgroup
        (rankTwoQuot L)) : Set (rankTwoQuot L))).comap (QuotientGroup.mk' (center L)),
      x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center L) with hπ
  set Pb := P.mapSurjective (QuotientGroup.mk'_surjective (center L)) with hPb
  have hPbc : (Pb : Subgroup (rankTwoQuot L)) = (P : Subgroup L).map π :=
    Sylow.coe_mapSurjective _ P
  have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
  have hB : fusionBenderBorel (rankTwoQuot L) (2 ^ (2 * a + 1)) 2 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 a
      ha).map_mulEquiv e.symm
  obtain ⟨hSE, hZsq, hZcard, -⟩ := AschbacherToolkit.Bender.benderBorel_sylowCenter hB Pb
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Zb := (P : Subgroup L).map π ⊓ centralizer (((P : Subgroup L).map π : Subgroup
    (rankTwoQuot L)) : Set (rankTwoQuot L)) with hZb
  have hZbS : Zb = AschbacherToolkit.Bender.sylowCenter (Pb : Subgroup (rankTwoQuot L)) := by
    rw [hZb, AschbacherToolkit.Bender.sylowCenter, hPbc]
  set W := (P : Subgroup L) ⊓ Zb.comap π with hW
  set Z := (P : Subgroup L) ⊓ center L with hZ
  have hker : ∀ x : L, π x = 1 ↔ x ∈ center L := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZW : ∀ x ∈ W, x ∈ Z ↔ π x = 1 := fun x hx => ⟨fun h => (hker x).mpr h.2,
    fun h => ⟨hx.1, (hker x).mp h⟩⟩
  have hsqb : ∀ c ∈ Zb, c * c = 1 := fun c hc => by
    rw [hZbS] at hc
    rw [← sq]
    exact hZsq c hc
  refine exponent_two_of_triple (W := W) (Z := Z) inf_le_right hZ2 ?_ ?_ ?_ ?_
  ·
    intro x hx y hy
    refine ⟨P.1.mul_mem (P.1.mul_mem (P.1.mul_mem hx.1 hy.1) (P.1.inv_mem hx.1))
      (P.1.inv_mem hy.1), (hker _).mp ?_⟩
    have hxc := hx.2.2
    have hyP : π y ∈ (P : Subgroup L).map π := ⟨y, hy.1, rfl⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← mem_centralizer_iff.mp hxc _ hyP]
    group
  ·
    intro x hx
    exact ⟨P.1.mul_mem hx.1 hx.1, (hker _).mp (by rw [map_mul]; exact hsqb _ hx.2)⟩
  ·
    intro x hx y hy hxZ hyZ
    have hx1 : π x ≠ 1 := fun h => hxZ ((hZW x hx).mpr h)
    have hy1 : π y ≠ 1 := fun h => hyZ ((hZW y hy).mpr h)
    have hxS : π x ∈ AschbacherToolkit.Bender.sylowCenter (Pb : Subgroup (rankTwoQuot L)) :=
      hZbS ▸ hx.2
    have hyS : π y ∈ AschbacherToolkit.Bender.sylowCenter (Pb : Subgroup (rankTwoQuot L)) :=
      hZbS ▸ hy.2
    obtain ⟨nb, -, hnb⟩ :=
      (AschbacherToolkit.Bender.isStronglyEmbedded_of_fusion hSE).involutions_conjugate_in
      (le_normalizer (AschbacherToolkit.Bender.sylowCenter_le _ hyS)) ⟨hy1, hZsq _ hyS⟩
      (le_normalizer (AschbacherToolkit.Bender.sylowCenter_le _ hxS)) ⟨hx1, hZsq _ hxS⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (center L) nb
    have hnb' : π (n⁻¹ * y * n) = π x := by
      rw [map_mul, map_mul, map_inv]
      exact hnb
    set z := x⁻¹ * (n⁻¹ * y * n) with hz
    have hzc : z ∈ center L := (hker z).mp (by rw [hz, map_mul, map_inv, hnb', inv_mul_cancel])
    have hxx : x * x ∈ center L := (hker _).mp (by rw [map_mul]; exact hsqb _ hx.2)
    · have hyy : y * y ∈ center L := (hker _).mp (by rw [map_mul]; exact hsqb _ hy.2)
      have hconj : n⁻¹ * y * n = x * z := by rw [hz, mul_inv_cancel_left]
      have h1 : y * y = x * x * (z * z) := by
        have h2 : (n⁻¹ * y * n) * (n⁻¹ * y * n) = n⁻¹ * (y * y) * n := by group
        have h3 : n⁻¹ * (y * y) * n = y * y := by
          rw [mul_assoc, ← mem_center_iff.mp hyy n, inv_mul_cancel_left]
        rw [← h3, ← h2, hconj]
        have hzx : z * x = x * z := (mem_center_iff.mp hzc x).symm
        calc x * z * (x * z) = x * (z * x) * z := by group
          _ = x * (x * z) * z := by rw [hzx]
          _ = x * x * (z * z) := by group
      have hzz : z * z ∈ (P : Subgroup L) := by
        have : z * z = (x * x)⁻¹ * (y * y) := by
          rw [h1]
          group
        rw [this]
        exact P.1.mul_mem (P.1.inv_mem (P.1.mul_mem hx.1 hx.1)) (P.1.mul_mem hy.1 hy.1)
      have hz4 : z ^ 2 ^ 2 = 1 := by
        have := hZ2 (z * z) ⟨hzz, (center L).mul_mem hzc hzc⟩
        calc z ^ 2 ^ 2 = z * z * (z * z) := by norm_num [pow_succ, mul_assoc]
          _ = 1 := this
      have hzP := mem_sylow_of_mem_center P hzc hz4
      rw [h1, hZ2 z ⟨hzP, hzc⟩, mul_one]
  ·
    intro x hx y hy
    classical
    let s : Finset (AschbacherToolkit.Bender.sylowCenter (Pb : Subgroup (rankTwoQuot L))) :=
      {1, ⟨π x, hZbS ▸ hx.2⟩, ⟨π y, hZbS ▸ hy.2⟩, ⟨π x, hZbS ▸ hx.2⟩ * ⟨π y, hZbS ▸ hy.2⟩}
    have hs : s.card < Nat.card (AschbacherToolkit.Bender.sylowCenter
        (Pb : Subgroup (rankTwoQuot L))) := by
      rw [hZcard]
      calc s.card ≤ 4 := Finset.card_le_four
        _ < 2 ^ (2 * a + 1) := by omega
    obtain ⟨⟨wb, hwb⟩, hwbs⟩ :=
      CFSG.ProperTwoGeneratedCore.Lemma37.CoverExclusion.exists_notMem_of_card_lt s hs
    have hwbZ : wb ∈ Zb := hZbS ▸ hwb
    obtain ⟨w, hwP, hww⟩ := hwbZ.1
    have hwW : w ∈ W := ⟨hwP, show π w ∈ Zb by rw [hww]; exact hwbZ⟩
    have hne : ∀ u ∈ W, π u ≠ wb → u⁻¹ * w ∉ Z := fun u hu hu' hZu => hu' (by
      have h1 := (hZW _ (W.mul_mem (W.inv_mem hu) hwW)).mp hZu
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      rw [h1, hww])
    refine ⟨w, hwW, ?_, hne x hx ?_, hne y hy ?_, hne (x * y) (W.mul_mem hx hy) ?_⟩
    · have h1 := hne 1 W.one_mem (fun h => hwbs (by
        have he : (⟨wb, hwb⟩ : AschbacherToolkit.Bender.sylowCenter
            (Pb : Subgroup (rankTwoQuot L))) = 1 :=
          Subtype.ext (show wb = 1 by rw [← h, map_one])
        rw [he]
        exact Finset.mem_insert_self _ _))
      simpa using h1
    · intro h
      apply hwbs
      have he : (⟨wb, hwb⟩ : AschbacherToolkit.Bender.sylowCenter
          (Pb : Subgroup (rankTwoQuot L))) = ⟨π x, hZbS ▸ hx.2⟩ := Subtype.ext h.symm
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · intro h
      apply hwbs
      have he : (⟨wb, hwb⟩ : AschbacherToolkit.Bender.sylowCenter
          (Pb : Subgroup (rankTwoQuot L))) = ⟨π y, hZbS ▸ hy.2⟩ := Subtype.ext h.symm
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · intro h
      apply hwbs
      have he : (⟨wb, hwb⟩ : AschbacherToolkit.Bender.sylowCenter
          (Pb : Subgroup (rankTwoQuot L))) = ⟨π x, hZbS ▸ hx.2⟩ * ⟨π y, hZbS ▸ hy.2⟩ :=
        Subtype.ext (show wb = π x * π y by rw [← h, map_mul])
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

namespace BenderHyp

variable {L : Subgroup G}

theorem false_of_isSylowOf_top_of_sz
    (h : BenderHyp G L) (hF : Foundation) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) {T : Subgroup G} (hT : IsSylowOf 2 T (normalizer (L : Set G)))
    (hTLK : T ≤ L ⊔ centralizer (L : Set G)) (hTG : IsSylowOf 2 T ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Sec3 G L T := ⟨h, hT⟩
  set K := centralizer (L : Set G) with hKdef
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ K with hT₀def
  have hLp : commutator L = ⊤ := h.standard.1.1
  have hT₀el := hS.isElemAbelian_T₀ hF
  have htight := AS76b.tightlyEmbedded_centralizer h.standard
  have hNK := AS76b.normalizer_centralizer_eq h.standard
  have hTeq : T = T₁ ⊔ T₀ := by
    have := hS.inf_sup_eq
    rwa [inf_eq_left.mpr hTLK] at this
  have hT₀C : T₀ ≤ centralizer (T₁ : Set G) := fun t ht =>
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp ht.2 x hx.2
  have hT₁N : T₁ ≤ normalizer (T₀ : Set G) :=
    (le_centralizer_iff.mp hT₀C).trans (centralizer_le_normalizer _)
  obtain ⟨P, hP⟩ := hS.isSylowOf_T₁
  have hPT : ∀ p : L, p ∈ (P : Subgroup L) ↔ (p : G) ∈ T₁ := fun p => by
    show p ∈ (P : Subgroup L) ↔ (p : G) ∈ T ⊓ L
    rw [← hP]
    exact ⟨fun hp => ⟨p, hp, rfl⟩, fun ⟨q, hq, hqp⟩ => (Subtype.ext hqp : q = p) ▸ hq⟩
  obtain ⟨-, hT2, hTidx⟩ := isSylowOf_iff.mp hTG
  rw [relIndex_top_right] at hTidx
  let S : Sylow 2 G := hT2.toSylow hTidx
  have hSc : (S : Subgroup G) = T := IsPGroup.toSylow_coe hT2 hTidx
  have hZ2 : ∀ z ∈ (P : Subgroup L) ⊓ center L, z * z = 1 := by
    intro z hz
    have hzT := (hPT z).mp hz.1
    have hzK : (z : G) ∈ K := RankTwoBender.centerIn_le_centralizer L ⟨z, hz.2, rfl⟩
    apply Subtype.ext
    simpa [sq] using hT₀el.2 (z : G) ⟨hzT.1, hzK⟩
  have hW2 := preimage_center_exponent_two ha e P hZ2
  set W := (P : Subgroup L) ⊓ (((P : Subgroup L).map (QuotientGroup.mk' (center L))) ⊓
    centralizer ((((P : Subgroup L).map (QuotientGroup.mk' (center L))) : Subgroup
      (rankTwoQuot L)) : Set (rankTwoQuot L))).comap (QuotientGroup.mk' (center L)) with hWdef
  set W' := W.map L.subtype with hW'def
  have hW'el : IsElemAbelian 2 W' := by
    have hexp : ∀ x ∈ W', x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hW2 x hx)
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => by rw [sq]; exact hexp x hx⟩
    apply Subtype.ext
    have hinv : ∀ z ∈ W', z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_right (hexp z hz)
    have hxy := hexp _ (W'.mul_mem x.2 y.2)
    simp only [coe_mul]
    calc (x : G) * y = ((x : G) * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = (y : G)⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
      _ = y * x := by rw [hinv _ y.2, hinv _ x.2]
  have hW'L : W' ≤ L := map_subtype_le _
  have hW'T₁ : W' ≤ T₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hPT x).mp hx.1
  have hT₀W' : T₀ ≤ centralizer (W' : Set G) := fun t ht =>
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp ht.2 x (hW'L hx)
  set A := W' ⊔ T₀ with hAdef
  have hAel : IsElemAbelian 2 A := isElemAbelian_sup hW'el hT₀el hT₀W'
  have hAT : A ≤ T := sup_le (hW'T₁.trans inf_le_left) inf_le_left
  have hA1 : A ≠ ⊥ := fun hb => hS.T₀_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
  have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
  have hB : fusionBenderBorel (rankTwoQuot L) (2 ^ (2 * a + 1)) 2 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 a
      ha).map_mulEquiv e.symm
  have hq : 2 ≤ 2 ^ (2 * a + 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ 2 * a + 1 by omega))
  set Pb := P.mapSurjective (QuotientGroup.mk'_surjective (center L)) with hPb
  have hPbc : (Pb : Subgroup (rankTwoQuot L)) = (P : Subgroup L).map
      (QuotientGroup.mk' (center L)) := Sylow.coe_mapSurjective _ P
  have hinvA : ∀ x ∈ T, x ^ 2 = 1 → x ∈ A := by
    intro x hx hx2
    obtain ⟨y, hy, t, ht, rfl⟩ :=
      CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hT₁N (hTeq ▸ hx)
    have hyt : y * t = t * y := mem_centralizer_iff.mp (hT₀C ht) y hy
    have hy2 : y ^ 2 = 1 := by
      have ht2 : t ^ 2 = 1 := hT₀el.2 t ht
      rw [Commute.mul_pow hyt 2, ht2, mul_one] at hx2
      exact hx2
    set p : L := ⟨y, hy.2⟩ with hpdef
    have hpP : p ∈ (P : Subgroup L) := (hPT p).mpr hy
    have hp2 : p ^ 2 = 1 := Subtype.ext (by simpa [hpdef] using hy2)
    have hpPb : QuotientGroup.mk' (center L) p ∈ (Pb : Subgroup (rankTwoQuot L)) := by
      rw [hPbc]
      exact ⟨p, hpP, rfl⟩
    have hpW : p ∈ W := by
      refine ⟨hpP, ?_⟩
      show QuotientGroup.mk' (center L) p ∈ ((P : Subgroup L).map (QuotientGroup.mk' (center L)) ⊓
        centralizer ((((P : Subgroup L).map (QuotientGroup.mk' (center L))) : Subgroup
          (rankTwoQuot L)) : Set (rankTwoQuot L)))
      refine ⟨⟨p, hpP, rfl⟩, ?_⟩
      have h1 := Asc76X.mem_centralizer_of_fusionBenderBorel hB hq Pb hpPb
        (by rw [← map_pow, hp2, map_one])
      rwa [hPbc] at h1
    exact A.mul_mem (mem_sup_left ⟨p, hpW, rfl⟩) (mem_sup_right ht)
  have hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A := by
    intro b hb g hg
    rw [hSc] at hg
    apply hinvA _ hg
    have hb2 : b ^ 2 = 1 := hAel.2 b hb
    rw [sq, show g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g by group, ← sq, hb2,
      mul_one, inv_mul_cancel]
  exact h.lemma34 S (hSc ▸ hAT) hAel.1 hA1 hcl

theorem false_of_sz_even_center
    (h : BenderHyp G L) (hF : Foundation) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) (heven : Even (Nat.card (center L))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have hS : Sec3 G L T := ⟨h, hT⟩
  set K := centralizer (L : Set G) with hKdef
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ K with hT₀def
  have hLp : commutator L = ⊤ := h.standard.1.1
  have hT₀el := hS.isElemAbelian_T₀ hF
  have htight := AS76b.tightlyEmbedded_centralizer h.standard
  have hNK := AS76b.normalizer_centralizer_eq h.standard
  have hTLK : T ≤ L ⊔ K := by
    intro t ht
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨t, ht⟩
    exact mem_sup_centralizer_of_sz hLp ha e (hT.le ht) (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hTeq : T = T₁ ⊔ T₀ := by
    have := hS.inf_sup_eq
    rwa [inf_eq_left.mpr hTLK] at this
  have hT₀C : T₀ ≤ centralizer (T₁ : Set G) := fun t ht =>
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp ht.2 x hx.2
  have hT₁N : T₁ ≤ normalizer (T₀ : Set G) :=
    (le_centralizer_iff.mp hT₀C).trans (centralizer_le_normalizer _)
  obtain ⟨P, hP⟩ := hS.isSylowOf_T₁
  have hcov := centralizer_sylow_le_center_of_sz hLp ha e heven P
  have hPT : ∀ p : L, p ∈ (P : Subgroup L) ↔ (p : G) ∈ T₁ := fun p => by
    show p ∈ (P : Subgroup L) ↔ (p : G) ∈ T ⊓ L
    rw [← hP]
    exact ⟨fun hp => ⟨p, hp, rfl⟩, fun ⟨q, hq, hqp⟩ => (Subtype.ext hqp : q = p) ▸ hq⟩
  have hZT : T ⊓ centralizer (T : Set G) = T₀ := by
    apply le_antisymm
    · rintro z ⟨hzT, hzC⟩
      obtain ⟨x, hx, t, ht, rfl⟩ :=
        CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hT₁N (hTeq ▸ hzT)
      have hxL : x ∈ L := hx.2
      have hxC : (⟨x, hxL⟩ : L) ∈ centralizer ((P : Subgroup L) : Set L) := by
        rw [mem_centralizer_iff]
        intro p hp
        have hpT₁ := (hPT p).mp hp
        apply Subtype.ext
        have h1 := mem_centralizer_iff.mp hzC p (hpT₁.1)
        have h2 : (p : G) * t = t * p := mem_centralizer_iff.mp (hT₀C ht) p hpT₁
        simp only [coe_mul]
        calc (p : G) * x = (p : G) * (x * t) * t⁻¹ := by group
          _ = x * t * p * t⁻¹ := by rw [h1]
          _ = x * (t * p) * t⁻¹ := by group
          _ = x * (p * t) * t⁻¹ := by rw [h2]
          _ = x * p := by group
      have hxK : x ∈ K := by
        have := hcov hxC
        exact RankTwoBender.centerIn_le_centralizer L ⟨⟨x, hxL⟩, this, rfl⟩
      exact ⟨T.mul_mem hx.1 ht.1, K.mul_mem hxK ht.2⟩
    · intro t ht
      refine ⟨ht.1, ?_⟩
      have hTC : T ≤ centralizer (T₀ : Set G) := by
        rw [hTeq]
        exact sup_le (le_centralizer_iff.mp hT₀C) (le_centralizer_iff_isMulCommutative.mpr hT₀el.1)
      exact le_centralizer_iff.mp hTC ht
  obtain ⟨E, hET, -, hE4⟩ := hS.exists_four_le
  have hT₀even : Even (Nat.card T₀) :=
    even_iff_two_dvd.mpr ((show 2 ∣ 4 by norm_num).trans (hE4 ▸ card_dvd_of_le hET))
  have hNT : normalizer (T : Set G) ≤ normalizer (L : Set G) := by
    intro g hg
    have hg₀ : g ∈ normalizer (T₀ : Set G) := by
      rw [← hZT]
      exact mem_normalizer_inf hg (mem_normalizer_centralizer hg)
    rw [← hNK]
    exact AS76b.Lemma37.normalizer_le_of_le_of_even htight inf_le_right hT₀even hg₀
  have hTG : IsSylowOf 2 T ⊤ :=
    AS76b.Lemma37.isSylowOf_of_isSylowOf_inf_normalizer (by
      rw [top_inf_eq]
      exact hT.of_le le_normalizer hNT)
  exact h.false_of_isSylowOf_top_of_sz hF ha e hT hTLK hTG

theorem odd_card_center
    (h : BenderHyp G L) (hF : Foundation) : Odd (Nat.card (center L)) := by
  have hLp : commutator L = ⊤ := h.standard.1.1
  rcases rankTwoBenderType_iff.mp h.bender with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact odd_card_center_of_psl2 hLp hm e
  · exact odd_card_center_of_psu3 hLp hm e
  · rcases Nat.even_or_odd (Nat.card (center L)) with heven | hodd
    · exact (h.false_of_sz_even_center hF ha e heven).elim
    · exact hodd

end BenderHyp

end CFSG.ComponentClassification.GMS78

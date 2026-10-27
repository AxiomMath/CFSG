module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResE81Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResE81
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLem17
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Inv

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem e81Data_of_half
    {L A B C D : Subgroup G} {z : G} (hs : LocalSetting G L z) (hF : FirstHalfData L z A B C D)
    (hlem : DResH.Lem17 L A B) {E : Subgroup G} (hE : CSideHalf L A z E) :
    ∃ X Q1 T1 : Subgroup G, E81Data D X Q1 T1 E z := by
  obtain ⟨hc, hint, hN, hcard⟩ := hE
  obtain ⟨T, hT9, hTc, hT3, hTN, hTfaith⟩ := hlem
  let δ : E →* G := diagHom hc
  have hδinj : Function.Injective δ := diagHom_injective hc hint
  have hδval : ∀ a : E, δ a = a * (z * a * z⁻¹) := fun a => rfl
  have hrangeN : δ.range ≤ egNL L A := by
    rintro _ ⟨a, rfl⟩
    exact hN a a.2
  let H : Subgroup (egNL L A) := δ.range.subgroupOf (egNL L A)
  have hHidx : H.index = 2 := by
    have hHcard : Nat.card H = Nat.card E := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrangeN).toEquiv]
      exact (Nat.card_congr (MonoidHom.ofInjective hδinj).toEquiv).symm
    have h1 := H.card_mul_index
    have hpos : 0 < Nat.card E := Nat.card_pos
    rw [hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard.symm)
  obtain ⟨-, φ, -, hAφ, -, -, -, hidx⟩ := sym6Index_of_type hF.pair.sextet
  have hHφ : H = (alternatingGroup (Fin 6)).comap φ := (hidx H).1 hHidx
  have hAle : A ≤ δ.range := by
    intro a ha
    have haN : a ∈ egNL L A := ⟨Subgroup.le_normalizer ha, hF.pair.1 ha⟩
    have h1 : (⟨a, haN⟩ : egNL L A) ∈ φ.ker := hAφ (mem_subgroupOf.2 ha)
    have h2 : (⟨a, haN⟩ : egNL L A) ∈ H := by
      rw [hHφ]
      exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 h1]; exact one_mem _)
    exact mem_subgroupOf.1 h2
  have hBle : B ≤ δ.range := by
    intro b hb
    by_cases hbA : b ∈ A
    · exact hAle hbA
    · have hbN : b ∈ egNL L A := hF.compat.B_le_NA hb
      let t : egNL L A := ⟨b, hbN⟩
      have htt : t * t = 1 := Subtype.ext (hF.octad.elem.2 b hb)
      have hcomm := hF.compat.comm_A b hb hbA
      have h16 := card_fix_eq_of_comm hF.sextet.elem.1
        (by rw [hF.compat.card_inf, hF.sextet.card_A]) hbN.1 hcomm.1 hcomm.2
      have h8 := (card_fix_involution_of_type hF.pair.sextet H hHidx t htt hbA).2
      by_contra hnot
      have := h8 (fun h => hnot (mem_subgroupOf.1 h))
      rw [show Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 16 from h16] at this
      exact absurd this (by norm_num)
  have hTle : T ≤ δ.range := by
    intro x hx
    have hxN : x ∈ egNL L A := (hTN x hx).1
    have : (⟨x, hxN⟩ : egNL L A) ∈ H := Sym6.mem_of_index_two_of_cube hHidx
      (Subtype.ext (by show x * x * x = 1; rw [← pow_three']; exact hT3 x hx))
    exact mem_subgroupOf.1 this
  have hABle : A ⊔ B ≤ δ.range := sup_le hAle hBle
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hs.order_z] at this
    simpa [sq] using this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzV : z ∈ egM B z := Subgroup.le_normalizer (mem_sup_right (mem_zpowers z))
  have hXD : liftSub δ B ≤ D := by
    intro x hx
    obtain ⟨a, haB, rfl⟩ := mem_liftSub.1 hx
    have haa : a * a = 1 := hδinj (by rw [map_mul, map_one]; exact hF.octad.elem.2 _ haB)
    have hxx : (a : G) * a = 1 := congrArg Subtype.val haa
    have hxinv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right hxx
    have hcentr : ∀ b ∈ B, (a : G) * b = b * a := by
      intro b hb
      obtain ⟨c, rfl⟩ := hBle hb
      have hcB : δ c ∈ B := hb
      have hac : a * c = c * a :=
        hδinj (by rw [map_mul, map_mul]; exact hF.octad.elem.1 _ haB _ hcB)
      have hac' : (a : G) * c = c * a := congrArg Subtype.val hac
      have h1 := hc a a.2 c c.2
      rw [hδval c]
      calc (a : G) * ((c : G) * (z * c * z⁻¹)) = ((a : G) * c) * (z * c * z⁻¹) := by group
        _ = (c * a) * (z * c * z⁻¹) := by rw [hac']
        _ = (c : G) * ((a : G) * (z * c * z⁻¹)) := by group
        _ = (c : G) * ((z * c * z⁻¹) * a) := by rw [h1]
        _ = ((c : G) * (z * c * z⁻¹)) * a := by group
    have hxz : (a : G) * z * (a : G)⁻¹ = (δ a) * z := by
      rw [hδval, hxinv]
      group
    have hxV : ∀ v ∈ B ⊔ zpowers z, (a : G) * v * (a : G)⁻¹ ∈ B ⊔ zpowers z := by
      intro v hv
      have : B ⊔ zpowers z ≤ (B ⊔ zpowers z).comap (MulAut.conj (a : G)).toMonoidHom := by
        refine sup_le (fun b hb => ?_) ?_
        · show (a : G) * b * (a : G)⁻¹ ∈ B ⊔ zpowers z
          rw [hcentr b hb]
          rw [mul_inv_cancel_right]
          exact mem_sup_left hb
        · rw [zpowers_le]
          show (a : G) * z * (a : G)⁻¹ ∈ B ⊔ zpowers z
          rw [hxz]
          exact mul_mem (mem_sup_left haB) (mem_sup_right (mem_zpowers z))
      exact this hv
    have hxM : (a : G) ∈ egM B z := by
      show (a : G) ∈ normalizer ((B ⊔ zpowers z : Subgroup G) : Set G)
      rw [mem_normalizer_iff]
      intro v
      refine ⟨hxV v, fun hv => ?_⟩
      have h1 := hxV _ hv
      have h2 : (a : G) * ((a : G) * v * (a : G)⁻¹) * (a : G)⁻¹ = v := by
        calc (a : G) * ((a : G) * v * (a : G)⁻¹) * (a : G)⁻¹
            = ((a : G) * a) * v * ((a : G) * a)⁻¹ := by group
          _ = v := by rw [hxx]; group
      rwa [h2] at h1
    have hxC : (a : G) ∈ centralizer (B : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact (hcentr b hb).symm
    rcases hF.nData.lam_eq (a : G) ⟨hxM, hxC⟩ with h | h
    · exact h
    · have h2 := hF.nData.elem.2 _ h
      have h3 : z * (a : G) * z⁻¹ = (a : G)⁻¹ := by
        have : z * (a : G) * z⁻¹ * (a : G) = 1 := by
          rw [hzinv]
          simpa only [mul_assoc] using h2
        exact eq_inv_of_mul_eq_one_left this
      have h4 : δ a = 1 := by rw [hδval, h3, mul_inv_cancel]
      have h5 : a = 1 := hδinj (by rw [h4, map_one])
      have h6 : (a : G) = 1 := by rw [h5]; rfl
      rw [h6]
      exact one_mem D
  have hconjD : conjSub z (liftSub δ B) ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hF.nData.norm z hzV x (hXD hx)
  have hcommX : ∀ x ∈ liftSub δ B, ∀ y ∈ conjSub z (liftSub δ B), x * y = y * x := by
    intro x hx y hy
    obtain ⟨y0, hy0, rfl⟩ := mem_conjSub.1 hy
    exact hc x (liftSub_le δ B hx) y0 (liftSub_le δ B hy0)
  have hcardX : Nat.card (liftSub δ B) = 16 := by
    rw [card_liftSub hδinj hBle]
    exact hF.octad.card_B
  have hcardXz : Nat.card (conjSub z (liftSub δ B)) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj z).injective, hcardX]
  have hcardprod : Nat.card (commProd _ _ hcommX) = 256 := by
    rw [card_commProd hcommX ?_, hcardX, hcardXz]
    intro x hx1 hx2
    obtain ⟨x0, hx0, hxx⟩ := mem_conjSub.1 hx2
    have h1 := hint x0 (liftSub_le δ B hx0) (hxx ▸ liftSub_le δ B hx1)
    rw [← hxx, h1]
    simp
  have hDeq : D = liftSub δ B ⊔ conjSub z (liftSub δ B) := by
    have hle : liftSub δ B ⊔ conjSub z (liftSub δ B) ≤ D := sup_le hXD hconjD
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [← commProd_eq_sup hcommX, hcardprod, hF.nData.card]
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 6) (by rw [hF.sextet.card_A]; norm_num)
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 4) (by rw [hF.octad.card_B]; norm_num)
  have hApB : IsPGroup 2 (A ⊔ B : Subgroup G) :=
    hA2.to_sup_of_normal_left' hB2 (fun b hb => (hF.compat.B_le_NA hb).1)
  have hABN : A ⊔ B ≤ normalizer (B : Set G) :=
    sup_le (fun a ha => (hF.compat.A_le_NB ha).1) Subgroup.le_normalizer
  have hTAB : ∀ s ∈ T, ∀ s' ∈ A ⊔ B, s * s' * s⁻¹ ∈ A ⊔ B := by
    intro s hs s' hs'
    have hsA : s ∈ normalizer (A : Set G) := (hTN s hs).1.1
    have hsB : s ∈ normalizer (B : Set G) := (hTN s hs).2
    have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj s).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact mem_sup_left ((mem_normalizer_iff.1 hsA a).1 ha)
      · exact mem_sup_right ((mem_normalizer_iff.1 hsB b).1 hb)
    exact this hs'
  refine ⟨liftSub δ B, liftSub δ (A ⊔ B), liftSub δ T, ?_⟩
  exact
    { hz := hzz
      hcomm := hc
      hint := hint
      hXE := liftSub_le δ B
      hD := hDeq
      hXQ := liftSub_mono δ le_sup_right
      hQE := liftSub_le δ _
      hTE := liftSub_le δ T
      hQ2 := liftSub_isPGroup hδinj hApB
      hXn := liftSub_normalizes δ fun s hs s' hs' => (mem_normalizer_iff.1 (hABN hs) s').1 hs'
      hTn := liftSub_normalizes δ hTAB
      hTX := liftSub_normalizes δ fun s hs s' hs' => (mem_normalizer_iff.1 (hTN s hs).2 s').1 hs'
      hT9 := by rw [card_liftSub hδinj hTle]; exact hT9
      hTc := by
        intro a ha b hb
        obtain ⟨a', ha', rfl⟩ := mem_liftSub.1 ha
        obtain ⟨b', hb', rfl⟩ := mem_liftSub.1 hb
        have : a' * b' = b' * a' := hδinj (by rw [map_mul, map_mul]; exact hTc _ ha' _ hb')
        exact congrArg Subtype.val this
      hT3 := by
        intro a ha
        obtain ⟨a', ha', rfl⟩ := mem_liftSub.1 ha
        have : a' ^ 3 = 1 := hδinj (by rw [map_pow, map_one]; exact hT3 _ ha')
        simpa using congrArg Subtype.val this
      hfaith := by
        intro τ hτ hτ1
        obtain ⟨a, ha, rfl⟩ := mem_liftSub.1 hτ
        have ha1 : δ a ≠ 1 := fun h => hτ1 (by rw [hδinj (h.trans (map_one δ).symm)]; rfl)
        obtain ⟨y, hyA, hy⟩ := hTfaith (δ a) ha ha1
        obtain ⟨c, hcy, hcQ⟩ := exists_mem_liftSub hABle (mem_sup_left hyA)
        refine ⟨c, hcQ, fun hmem => hy ?_⟩
        obtain ⟨e, he, hee⟩ := mem_liftSub.1 hmem
        have hee' : e = a * c * a⁻¹ * c⁻¹ := Subtype.ext hee
        rw [hee', map_mul, map_mul, map_mul, map_inv, map_inv, hcy] at he
        exact he }

end CFSG.EvenSporadicStandard.M24Std.DRes

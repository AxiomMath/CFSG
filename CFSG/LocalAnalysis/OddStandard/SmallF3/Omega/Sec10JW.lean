module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec10J_conj_mem_twoCoreIn {X : Subgroup G} {c : G}
    (hmem : ∀ x ∈ X, c * x * c⁻¹ ∈ X) (hmem' : ∀ x ∈ X, c⁻¹ * x * c ∈ X)
    {x : G} (hx : x ∈ twoCoreIn X) : c * x * c⁻¹ ∈ twoCoreIn X := by
  change x ∈ (pCore 2 ↥X).map X.subtype at hx
  obtain ⟨y, hy, rfl⟩ := hx
  let φ : ↥X ≃* ↥X :=
    { toFun := fun z => ⟨c * (z : G) * c⁻¹, hmem z z.2⟩
      invFun := fun z => ⟨c⁻¹ * (z : G) * c, hmem' z z.2⟩
      left_inv := fun z => Subtype.ext (by group)
      right_inv := fun z => Subtype.ext (by group)
      map_mul' := fun z w => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : φ y ∈ pCore 2 ↥X :=
    (Subgroup.characteristic_iff_le_comap.mp
      (inferInstance : (pCore 2 ↥X).Characteristic)) φ hy
  exact ⟨φ y, hφ, rfl⟩

private lemma sec10J_conj_mem_K [Finite G] (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hcz : c ∈ centralizer ({z} : Set G)) :
    ∀ x ∈ K1 ⊔ K2, c * x * c⁻¹ ∈ K1 ⊔ K2 := by
  have hczc : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hciz : c⁻¹ * z = z * c⁻¹ := hczc.inv_left.eq
  rw [sec10K0_pockets_sup hP5 hpsp hctx]
  intro x hx
  unfold oTwoRes at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      have hyL : y ∈ L := hy.1.1
      have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy.1.2
      refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hcN y).mp hyL
      · change c * y * c⁻¹ ∈ centralizer ({z} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (c * y * c⁻¹) * z = c * y * (c⁻¹ * z) := by simp only [mul_assoc]
          _ = c * (y * z) * c⁻¹ := by rw [hciz]; simp only [mul_assoc]
          _ = c * (z * y) * c⁻¹ := by rw [hyz]
          _ = (c * z) * y * c⁻¹ := by simp only [mul_assoc]
          _ = (z * c) * y * c⁻¹ := by rw [hczc.eq]
          _ = z * (c * y * c⁻¹) := by simp only [mul_assoc]
      · have hconj : orderOf (c * y * c⁻¹) = orderOf y := by
          rw [← MulAut.conj_apply c y]
          exact (MulAut.conj c).orderOf_eq y
        rw [hconj]
        exact hy.2
  | one => simpa using Subgroup.one_mem (Subgroup.closure _)
  | mul y w _ _ ihy ihw => simpa only [conj_mul] using Subgroup.mul_mem _ ihy ihw
  | inv y _ ihy => simpa only [conj_inv] using Subgroup.inv_mem _ ihy

private lemma sec10J_conj_mem_secQ [Finite G] (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hcz : c ∈ centralizer ({z} : Set G)) :
    ∀ x ∈ secQ K1 K2, c * x * c⁻¹ ∈ secQ K1 K2 := by
  intro x hx
  exact sec10J_conj_mem_twoCoreIn
    (sec10J_conj_mem_K hP5 hpsp hctx hcN hcz)
    (fun x hx => by
      have h := sec10J_conj_mem_K hP5 hpsp hctx
        ((normalizer (L : Set G)).inv_mem hcN)
        ((centralizer ({z} : Set G)).inv_mem hcz) x hx
      simpa only [inv_inv] using h) hx

theorem sec10J_Q_le [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    secQ K1 K2 ≤ S ⊓ L := by
  obtain ⟨hpsp, -, -, -, -, hsylL⟩ := hb G t L S z hctx.toSec10Z
  have hSz : S ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs)
  have hPY : S ⊓ L ≤ L ⊓ centralizer ({z} : Set G) :=
    le_inf inf_le_right (le_trans inf_le_left hSz)
  have hKY : K1 ⊔ K2 ≤ L ⊓ centralizer ({z} : Set G) :=
    sup_le hctx.pocket1.2.1 hctx.pocket2.2.1
  have hQY : secQ K1 K2 ≤ L ⊓ centralizer ({z} : Set G) :=
    le_trans (Subgroup.map_subtype_le (pCore 2 ↥(K1 ⊔ K2))) hKY
  have hYnorm : L ⊓ centralizer ({z} : Set G) ≤ normalizer (secQ K1 K2 : Set G) := by
    intro c hc
    have hcN : c ∈ normalizer (L : Set G) := Subgroup.le_normalizer hc.1
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
    · intro hx
      exact sec10J_conj_mem_secQ hP5 hpsp hctx hcN hc.2 x hx
    · intro hx
      have h := sec10J_conj_mem_secQ hP5 hpsp hctx
        ((normalizer (L : Set G)).inv_mem hcN)
        ((centralizer ({z} : Set G)).inv_mem hc.2) (c * x * c⁻¹) hx
      have h' : c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x := by group
      rwa [h'] at h
  have hPnorm : S ⊓ L ≤ normalizer (secQ K1 K2 : Set G) := fun c hc => hYnorm (hPY hc)
  have hQ2 : IsPGroup 2 (secQ K1 K2) :=
    IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥(K1 ⊔ K2))) (K1 ⊔ K2).subtype
  have hsylY : IsSylow2Of (S ⊓ L) (L ⊓ centralizer ({z} : Set G)) := by
    refine ⟨hPY, hsylL.2.1, ?_⟩
    intro hdvd
    have hmul := Subgroup.relIndex_mul_relIndex (H := S ⊓ L)
      (K := L ⊓ centralizer ({z} : Set G)) (L := L) hPY inf_le_left
    exact hsylL.2.2 (hmul ▸ dvd_mul_of_dvd_left hdvd _)
  have hsupY : secQ K1 K2 ⊔ (S ⊓ L) ≤ L ⊓ centralizer ({z} : Set G) := sup_le hQY hPY
  have hsup2 : IsPGroup 2 ↥(secQ K1 K2 ⊔ (S ⊓ L)) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hsylL.2.1 hPnorm
  have heq : secQ K1 K2 ⊔ (S ⊓ L) = S ⊓ L := hsylY.eq_of_le hsupY hsup2 le_sup_right
  exact le_trans le_sup_left (le_of_eq heq)

theorem sec10J_Q_normal [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ s ∈ S, ∀ x ∈ secQ K1 K2, s * x * s⁻¹ ∈ secQ K1 K2 := by
  obtain ⟨hpsp, -, -, -, hSN, -⟩ := hb G t L S z hctx.toSec10Z
  intro s hs x hx
  exact sec10J_conj_mem_secQ hP5 hpsp hctx (hSN hs)
    (Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs)) x hx

theorem sec10J_t_notin_Q [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    t ∉ secQ K1 K2 := by
  obtain ⟨-, -, htnotL, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  intro htQ
  exact htnotL (le_trans (sec10J_Q_le hP5 hb hctx) inf_le_right htQ)

theorem sec10J_mem_W [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ w ∈ secW t K1 K2, ∃ q ∈ secQ K1 K2, w = q ∨ w = q * t := by
  obtain ⟨-, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hQL : secQ K1 K2 ≤ L := le_trans (sec10J_Q_le hP5 hb hctx) inf_le_right
  have hcomm : ∀ h ∈ secQ K1 K2, ∀ k ∈ zpowers t, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hht : h * t = t * h := Subgroup.mem_centralizer_iff.mp htC h (hQL hh)
    exact (Commute.zpow_right (show Commute h t from hht) i).eq
  intro w hw
  obtain ⟨h, hh, k, hk, hwk⟩ := exists_mul_of_mem_sup_of_commute hcomm hw
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hti : t ^ i = t ^ (i % 2) := by
    refine (zpow_eq_zpow_iff_modEq).mpr ?_
    rw [hctx.involution]
    exact (Int.mod_modEq i 2).symm
  have hk' : k = t ^ (i % 2) := by rw [← hi, hti]
  rcases Int.emod_two_eq_zero_or_one i with hi0 | hi1
  · refine ⟨h, hh, Or.inl ?_⟩
    rw [hwk, hk', hi0]; simp
  · refine ⟨h, hh, Or.inr ?_⟩
    rw [hwk, hk', hi1]; simp

theorem sec10J_W_le [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    secW t K1 K2 ≤ S := by
  obtain ⟨-, -, -, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  change secQ K1 K2 ⊔ zpowers t ≤ S
  exact sup_le (le_trans (sec10J_Q_le hP5 hb hctx) inf_le_left) (Subgroup.zpowers_le.mpr htS)

theorem sec10J_W_normal [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ s ∈ S, ∀ w ∈ secW t K1 K2, s * w * s⁻¹ ∈ secW t K1 K2 := by
  intro s hs w hw
  obtain ⟨q, hq, hwq | hwq⟩ := sec10J_mem_W hP5 hb hctx w hw
  · rw [hwq]
    change s * q * s⁻¹ ∈ secQ K1 K2 ⊔ zpowers t
    exact Subgroup.mem_sup_left (sec10J_Q_normal hP5 hb hctx s hs q hq)
  · rw [hwq]
    have hst : s * t * s⁻¹ = t := by
      have hstc : Commute s t := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
      rw [hstc.eq]; group
    rw [show s * (q * t) * s⁻¹ = (s * q * s⁻¹) * (s * t * s⁻¹) by group, hst]
    change (s * q * s⁻¹) * t ∈ secQ K1 K2 ⊔ zpowers t
    exact Subgroup.mul_mem (secQ K1 K2 ⊔ zpowers t)
      (Subgroup.mem_sup_left (sec10J_Q_normal hP5 hb hctx s hs q hq))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

end CFSG.OddStandard.SmallF3.Omega

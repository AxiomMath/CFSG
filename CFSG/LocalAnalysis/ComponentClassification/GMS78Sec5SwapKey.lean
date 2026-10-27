module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SwapSylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SwapSpan

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}


theorem SwapElt.exists_conj_of_conj_mem {w : G} (hw : SwapElt L T R R₂ w)
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {x g : G} (hg : g * x * g⁻¹ ∈ gmsA L T) :
    ∃ h : G, h * x * h⁻¹ ∈ gmsA L T ∧
      ∀ z ∈ R ⊔ zpowers w, z * x = x * z → h * z * h⁻¹ ∈ R ⊔ zpowers w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₁ : Subgroup G := R ⊔ zpowers w with hS₁
  have hS₁G := hw.isSylowOf_top hS h34 hR₂ h4 hne hcomm
  set C := centralizer ({x} : Set G) with hCdef
  set P := S₁.comap (MulAut.conj g).toMonoidHom with hP
  have hmemP : ∀ z, z ∈ P ↔ g * z * g⁻¹ ∈ S₁ := fun z => Iff.rfl
  have hPC : P ≤ C := by
    intro z hz
    rw [hCdef, mem_centralizer_singleton_iff]
    have h1 := hw.commute_gmsA hS h34 hR₂ h4 hne hcomm ((hmemP z).mp hz) hg
    calc z * x = g⁻¹ * (g * z * g⁻¹ * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
      _ = x * z := by group
  have hPG : IsSylowOf 2 P ⊤ := isSylowOf_of_card le_top
    ((Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun _ => Iff.rfl)).trans
      hS₁G.card_eq)
  obtain ⟨S, hSC, hRS⟩ := AS76b.exists_isSylowOf_le (inf_le_right : S₁ ⊓ C ≤ C)
    ((hw.isPGroup_sup hS).to_le inf_le_left)
  obtain ⟨k, hkC, hk⟩ := (hPG.of_le hPC le_top).exists_mem_conj hSC
  have hkx : k⁻¹ * x * k = x := by
    have h1 : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
    calc k⁻¹ * x * k = k⁻¹ * (k * x) := by rw [h1]; group
      _ = x := by group
  refine ⟨g * k⁻¹, ?_, fun z hz hzx => ?_⟩
  · have e : g * k⁻¹ * x * (g * k⁻¹)⁻¹ = g * (k⁻¹ * x * k) * g⁻¹ := by group
    rw [e, hkx]
    exact hg
  · have hzC : z ∈ S₁ ⊓ C := mem_inf.mpr ⟨hz, by
      rw [hCdef, mem_centralizer_singleton_iff]; exact hzx⟩
    have e : g * k⁻¹ * z * (g * k⁻¹)⁻¹ = g * (k⁻¹ * z * k) * g⁻¹ := by group
    rw [e]
    exact (hmemP _).mp ((hk z).mp (hRS hzC))

theorem false_of_closure_eq_top {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) {x h : G} (hxA : x ∉ gmsA L T)
    (hhx : h * x * h⁻¹ ∈ gmsA L T) {X : Set (BinaryGaloisField (2 * a + 1))}
    (hX : ∀ w ∈ X, ∃ b ∈ gmsA L T, h * b * h⁻¹ ∈ gmsA L T ∧ v b = w)
    (htop : AddSubgroup.closure X = ⊤) : False := by
  set A₁s := (gmsA L T).comap (MulAut.conj h).toMonoidHom with hA₁s
  have hmemA : ∀ z, z ∈ A₁s ↔ h * z * h⁻¹ ∈ gmsA L T := fun z => Iff.rfl
  have hv1 : v 1 = 0 := by
    have h1 := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h1
    linear_combination -h1
  let B : AddSubgroup (BinaryGaloisField (2 * a + 1)) :=
    { carrier := v '' ((gmsA L T ⊓ A₁s : Subgroup G) : Set G)
      add_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', mul_mem hb hb', hC.v_mul b (mem_inf.mp hb).1 b' (mem_inf.mp hb').1⟩
      zero_mem' := ⟨1, one_mem _, hv1⟩
      neg_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b, hb, (CharTwo.neg_eq _).symm⟩ }
  have hsub : X ⊆ (B : Set _) := by
    intro w hw
    obtain ⟨b, hb, hbs, rfl⟩ := hX w hw
    exact ⟨b, mem_inf.mpr ⟨hb, hbs⟩, rfl⟩
  have hle := (AddSubgroup.closure_le B).mpr hsub
  rw [htop] at hle
  have hall : ∀ b₀ ∈ gmsA L T, b₀ ∈ A₁s := by
    intro b₀ hb₀
    obtain ⟨b₁, hb₁, hvb⟩ := hle (AddSubgroup.mem_top (v b₀))
    obtain ⟨hb₁A, hb₁s⟩ := mem_inf.mp hb₁
    have h1 := hC.v_mul b₀ hb₀ b₁ hb₁A
    rw [← hvb, CharTwo.add_self_eq_zero] at h1
    rw [eq_inv_of_mul_eq_one_left (hC.v_inj _ (mul_mem hb₀ hb₁A) h1)]
    exact inv_mem hb₁s
  have hcard : Nat.card A₁s = Nat.card (gmsA L T) :=
    Nat.card_congr ((MulAut.conj h).toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have heq : gmsA L T = A₁s := eq_of_le_of_card_ge (fun b hb => hall b hb) hcard.le
  exact hxA (heq ▸ (hmemA x).mpr hhx)

theorem SwapElt.false_of_conj_mem_R {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    (hC : RCoords L T R R₂ a v φ 0 0 ⊤) {x g : G} (hx : x ∈ R) (hxA : x ∉ gmsA L T)
    (hg : g * x * g⁻¹ ∈ gmsA L T) : False := by
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  obtain ⟨h, hhx, hhz⟩ := hw.exists_conj_of_conj_mem hS h34 hR₂ h4 hne hcomm hg
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hsqA : ∀ z ∈ R, z ^ 2 ∈ gmsA L T := fun z hz =>
    (hC.ker _ (pow_mem hz 2)).mp (by rw [sq, hC.mul z hz z hz]; exact CharTwo.add_self_eq_zero _)
  have hcommute : ∀ z ∈ R, VLike.commMap a 0 (φ x) (φ z) = 0 → z * x = x * z := by
    intro z hz h0
    rw [← hC.comm x hx z hz] at h0
    have h1 := hC.v_inj _ (hS.commutator_mem_gmsA h34 hx hz) h0
    calc z * x = x * z * x⁻¹ * z⁻¹ * (z * x) := by rw [h1, one_mul]
      _ = x * z := by group
  let Y : AddSubgroup (BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)) :=
    { carrier := {z | ∃ t ∈ R, t * x = x * t ∧ h * t * h⁻¹ ∈ R ∧ φ t = z}
      add_mem' := by
        rintro _ _ ⟨t, ht, htx, hth, rfl⟩ ⟨t', ht', htx', hth', rfl⟩
        refine ⟨t * t', mul_mem ht ht', ?_, ?_, hC.mul t ht t' ht'⟩
        · calc t * t' * x = t * (x * t') := by rw [mul_assoc, htx']
            _ = x * (t * t') := by rw [← mul_assoc, htx, mul_assoc]
        · have e : h * (t * t') * h⁻¹ = h * t * h⁻¹ * (h * t' * h⁻¹) := by group
          rw [e]
          exact mul_mem hth hth'
      zero_mem' := ⟨1, one_mem _, by group, by simp, hφ1⟩
      neg_mem' := by
        rintro _ ⟨t, ht, htx, hth, rfl⟩
        refine ⟨t⁻¹, inv_mem ht, ?_, ?_, ?_⟩
        · calc t⁻¹ * x = t⁻¹ * (x * t) * t⁻¹ := by group
            _ = t⁻¹ * (t * x) * t⁻¹ := by rw [htx]
            _ = x * t⁻¹ := by group
        · have e : h * t⁻¹ * h⁻¹ = (h * t * h⁻¹)⁻¹ := by group
          rw [e]
          exact inv_mem hth
        · have h1 := hC.mul t ht t⁻¹ (inv_mem ht)
          rw [mul_inv_cancel, hφ1] at h1
          exact (neg_eq_of_add_eq_zero_right h1.symm).symm }
  have hYi : ∀ z z' : BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1), VLike.commMap a 0 (φ x) z = 0 →
      VLike.commMap a 0 (φ x) z' = 0 → z ∉ Y → z' ∉ Y → z + z' ∈ Y := by
    intro z z' hz hz' hzY hz'Y
    obtain ⟨t, ht, rfl⟩ := hC.surj z (AddSubgroup.mem_top _)
    obtain ⟨t', ht', rfl⟩ := hC.surj z' (AddSubgroup.mem_top _)
    have htx := hcommute t ht hz
    have htx' := hcommute t' ht' hz'
    have h1 : h * t * h⁻¹ * w⁻¹ ∈ R := by
      refine (hw.mem_sup_iff.mp (hhz t (mem_sup_left ht) htx)).resolve_left fun hth => ?_
      exact hzY ⟨t, ht, htx, hth, rfl⟩
    have h2 : h * t' * h⁻¹ * w⁻¹ ∈ R := by
      refine (hw.mem_sup_iff.mp (hhz t' (mem_sup_left ht') htx')).resolve_left fun hth => ?_
      exact hz'Y ⟨t', ht', htx', hth, rfl⟩
    refine ⟨t * t', mul_mem ht ht', ?_, ?_, hC.mul t ht t' ht'⟩
    · calc t * t' * x = t * (x * t') := by rw [mul_assoc, htx']
        _ = x * (t * t') := by rw [← mul_assoc, htx, mul_assoc]
    · have e : h * (t * t') * h⁻¹ =
          (h * t * h⁻¹ * w⁻¹) * (w * (h * t' * h⁻¹ * w⁻¹) * w⁻¹) * w ^ 2 := by
        rw [sq]; group
      rw [e]
      exact mul_mem (mul_mem h1 ((mem_normalizer_iff.mp hw.mem_normalizer _).mp h2)) hw.sq_mem
  have htop := VLike.closure_eq_top_of_index_le_two (a := a) hS.one_le hK (c := 0) (e := 0)
    (x := φ x) hYi
  refine false_of_closure_eq_top hC hxA hhx (X := VLike.sqMap a 0 0 '' Y) ?_ htop
  rintro _ ⟨_, ⟨t, ht, -, hth, rfl⟩, rfl⟩
  refine ⟨t ^ 2, hsqA t ht, ?_, hC.sq t ht⟩
  have e : h * t ^ 2 * h⁻¹ = (h * t * h⁻¹) ^ 2 := by rw [sq, sq]; group
  rw [e]
  exact hsqA _ hth

theorem SwapElt.false_of_conj_mem_not_R {w : G} (hw : SwapElt L T R R₂ w)
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    (hC : RCoords L T R R₂ a v φ 0 0 ⊤) {x g : G} (hx : x ∈ R ⊔ zpowers w) (hxR : x ∉ R)
    (hg : g * x * g⁻¹ ∈ gmsA L T) : False := by
  classical
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  have hxA : x ∉ gmsA L T := fun h => hxR (hS.T_le (Sec3.SzR.gmsA_le_T h))
  have hr₀ : x * w⁻¹ ∈ R := (hw.mem_sup_iff.mp hx).resolve_left hxR
  have hx2 : x * x = 1 := by
    have h1 := (hS.facts.sylow hS.sec3).2.1 _ hg
    have e : (g * x * g⁻¹) ^ 2 = g * (x * x) * g⁻¹ := by rw [sq]; group
    rw [e] at h1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hsqA : ∀ z ∈ R, z ^ 2 ∈ gmsA L T := fun z hz =>
    (hC.ker _ (pow_mem hz 2)).mp (by rw [sq, hC.mul z hz z hz]; exact CharTwo.add_self_eq_zero _)
  have hxN : x ∈ normalizer (R : Set G) := by
    have e : x = x * w⁻¹ * w := by group
    rw [e]
    exact mul_mem (le_normalizer hr₀) hw.mem_normalizer
  have hxRR : ∀ z ∈ R, x * z * x⁻¹ ∈ R := fun z hz => (mem_normalizer_iff.mp hxN z).mp hz
  obtain ⟨κ₀, hκ₀, hwφ⟩ := hw.exists_phi_conj hS h34 hR₂ h4 hne hcomm hC
  have hxφ : ∀ z ∈ R, φ (x * z * x⁻¹) = ((φ z).1, (φ z).2.2 / κ₀, κ₀ * (φ z).2.1) := by
    intro z hz
    have hwz : w * z * w⁻¹ ∈ R := (mem_normalizer_iff.mp hw.mem_normalizer z).mp hz
    have e : x * z * x⁻¹ = ((x * w⁻¹) * (w * z * w⁻¹) * (x * w⁻¹)⁻¹ * (w * z * w⁻¹)⁻¹) *
        (w * z * w⁻¹) := by group
    rw [e, hC.mul _ (mul_mem (mul_mem (mul_mem hr₀ hwz) (inv_mem hr₀)) (inv_mem hwz)) _ hwz,
      (hC.ker _ (mul_mem (mul_mem (mul_mem hr₀ hwz) (inv_mem hr₀)) (inv_mem hwz))).mpr
        (hS.commutator_mem_gmsA h34 hr₀ hwz), zero_add, hwφ z hz]
  obtain ⟨kx, hkx⟩ : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := (hw.isPGroup_sup hS) ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxT₁ : x ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    have e : x = x * w⁻¹ * w := by group
    rw [e]
    exact mul_mem (hS.le_normalizer_T₁ h34 hr₀)
      (hw.mem_normalizer_T₁ hS h34 hR₂ h4 hne hcomm)
  obtain ⟨-, hxT⟩ := hS.conj_eq_of_two_elt hxT₁ hkx
  obtain ⟨h, hhx, hhz⟩ := hw.exists_conj_of_conj_mem hS h34 hR₂ h4 hne hcomm hg
  have hA₁x : ∀ b ∈ gmsA L T, b * x = x * b := fun b hb =>
    (hw.commute_gmsA hS h34 hR₂ h4 hne hcomm hx hb).symm
  obtain ⟨b₁, hb₁, hb₁R⟩ : ∃ b ∈ gmsA L T, h * b * h⁻¹ ∉ R := by
    by_contra hall
    push Not at hall
    obtain ⟨b, hb, hbA⟩ : ∃ b ∈ gmsA L T, h * b * h⁻¹ ∉ gmsA L T := by
      by_contra hall'
      push Not at hall'
      set A₁s := (gmsA L T).comap (MulAut.conj h).toMonoidHom with hA₁s
      have hcard : Nat.card A₁s = Nat.card (gmsA L T) :=
        Nat.card_congr ((MulAut.conj h).toEquiv.subtypeEquiv fun _ => Iff.rfl)
      have heq : gmsA L T = A₁s := eq_of_le_of_card_ge (fun b hb => hall' b hb) hcard.le
      exact hxA (heq ▸ (show x ∈ A₁s from hhx))
    exact hw.false_of_conj_mem_R hS h34 hR₂ h4 hne hcomm hC (hall b hb) hbA
      (g := h⁻¹) (by simpa [mul_assoc] using hb)
  have hb₁S : h * b₁ * h⁻¹ * w⁻¹ ∈ R :=
    (hw.mem_sup_iff.mp (hhz b₁ (mem_sup_left (hS.T_le (Sec3.SzR.gmsA_le_T hb₁)))
      (hA₁x b₁ hb₁))).resolve_left hb₁R
  have hstep2 : ∀ u : BinaryGaloisField (2 * a + 1),
      ∃ z ∈ R, z * x = x * z ∧ h * z * h⁻¹ ∈ R ∧ (φ z).1 = u := by
    intro u
    obtain ⟨z₁, hz₁, hz₁φ⟩ := hC.surj (u, 0, 0) (AddSubgroup.mem_top _)
    obtain ⟨t, ht, r, hr, s, hs, rfl⟩ := hS.exists_decomp h34 hR₂ hz₁
    have htR : t ∈ R := hS.T_le (mem_inf.mp ht).1
    have hrR := hR₂.le_R hr
    have hsR : s ∈ R := hS.T_le (mem_inf.mp hs).1
    have htu : (φ t).1 = u := by
      have h1 := congrArg Prod.fst hz₁φ
      rw [hC.mul _ (mul_mem htR hrR) _ hsR, hC.mul _ htR _ hrR] at h1
      simp only [Prod.fst_add, (hC.of_R₂ r hr).1, (hC.of_T₀ s hs).1, add_zero] at h1
      exact h1
    set α := x * t * x⁻¹ * t⁻¹ with hα
    have hαA : α ∈ gmsA L T := hxT t ht
    obtain ⟨s₀, hs₀⟩ := VLike.pow_two_pow_surjective (K := BinaryGaloisField (2 * a + 1)) 1
      (κ₀ * v α)
    simp only [pow_one] at hs₀
    obtain ⟨v₀, hv₀, hv₀φ⟩ := hC.T₀_surj s₀ (AddSubgroup.mem_top _)
    have hv₀R : v₀ ∈ R := hS.T_le (mem_inf.mp hv₀).1
    obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = x * v₀ * x⁻¹ := ⟨_, rfl⟩
    have hr₂R : r₂ ∈ R := hr₂ ▸ hxRR v₀ hv₀R
    have hr₂φ : φ r₂ = (0, s₀ / κ₀, 0) := by
      rw [hr₂, hxφ v₀ hv₀R, hv₀φ]
      simp
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = r₂ * v₀ * r₂⁻¹ * v₀⁻¹ := ⟨_, rfl⟩
    have hc₀A : c₀ ∈ gmsA L T := hc₀ ▸ hS.commutator_mem_gmsA h34 hr₂R hv₀R
    have hvc₀ : v c₀ = v α := by
      rw [hc₀, hC.comm _ hr₂R _ hv₀R, hr₂φ, hv₀φ]
      simp only [VLike.commMap, zero_mul, mul_zero, add_zero, zero_add]
      rw [show s₀ * (s₀ / κ₀) = s₀ ^ 2 / κ₀ by ring, hs₀]
      field_simp
    have hv1 : v 1 = 0 := by
      have h3 := hC.v_mul 1 (one_mem _) 1 (one_mem _)
      rw [mul_one] at h3
      linear_combination -h3
    have hαc₀ : α = c₀ := by
      have h1 := hC.v_mul α hαA c₀⁻¹ (inv_mem hc₀A)
      have hinv : v c₀⁻¹ = v c₀ := by
        have h2 := hC.v_mul c₀ hc₀A c₀⁻¹ (inv_mem hc₀A)
        rw [mul_inv_cancel, hv1] at h2
        linear_combination -h2 - v c₀ * (CharTwo.two_eq_zero :
          (2 : BinaryGaloisField (2 * a + 1)) = 0)
      rw [hinv, hvc₀, CharTwo.add_self_eq_zero] at h1
      have := hC.v_inj _ (mul_mem hαA (inv_mem hc₀A)) h1
      exact mul_inv_eq_one.mp this
    obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = t * r₂ * v₀ := ⟨_, rfl⟩
    have hz₀R : z₀ ∈ R := hz₀ ▸ mul_mem (mul_mem htR hr₂R) hv₀R
    have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx2).symm
    have hz₀x : z₀ * x = x * z₀ := by
      have hxv₀ : x * r₂ * x⁻¹ = v₀ := by
        rw [hr₂, hxinv]
        calc x * (x * v₀ * x) * x = (x * x) * v₀ * (x * x) := by group
          _ = v₀ := by rw [hx2]; group
      have hxt : x * t * x⁻¹ = α * t := by rw [hα]; group
      have hct : c₀ * t = t * c₀ := (hS.commute_gmsA htR hc₀A).symm
      have e1 : x * z₀ * x⁻¹ = α * t * v₀ * r₂ := by
        calc x * z₀ * x⁻¹ = (x * t * x⁻¹) * (x * r₂ * x⁻¹) * (x * v₀ * x⁻¹) := by
              rw [hz₀]; group
          _ = α * t * v₀ * r₂ := by rw [hxt, hxv₀, ← hr₂]
      have e2 : z₀ = α * t * v₀ * r₂ := by
        have h1 : r₂ * v₀ = c₀ * v₀ * r₂ := by rw [hc₀]; group
        calc z₀ = t * (r₂ * v₀) := by rw [hz₀]; group
          _ = t * (c₀ * v₀ * r₂) := by rw [h1]
          _ = (t * c₀) * v₀ * r₂ := by group
          _ = (c₀ * t) * v₀ * r₂ := by rw [hct]
          _ = α * t * v₀ * r₂ := by rw [hαc₀]
      have e3 : x * z₀ * x⁻¹ = z₀ := by rw [e1, e2]
      calc z₀ * x = (x * z₀ * x⁻¹) * x := by rw [e3]
        _ = x * z₀ := by group
    have hz₀u : (φ z₀).1 = u := by
      rw [hz₀, hC.mul _ (mul_mem htR hr₂R) _ hv₀R, hC.mul _ htR _ hr₂R, hr₂φ, hv₀φ]
      simp [htu]
    by_cases hz₀h : h * z₀ * h⁻¹ ∈ R
    · exact ⟨z₀, hz₀R, hz₀x, hz₀h, hz₀u⟩
    · have hb₁R' : b₁ ∈ R := hS.T_le (Sec3.SzR.gmsA_le_T hb₁)
      refine ⟨z₀ * b₁, mul_mem hz₀R hb₁R', ?_, ?_, ?_⟩
      · calc z₀ * b₁ * x = z₀ * (x * b₁) := by rw [mul_assoc, hA₁x b₁ hb₁]
          _ = x * (z₀ * b₁) := by rw [← mul_assoc, hz₀x, mul_assoc]
      · have h1 : h * z₀ * h⁻¹ * w⁻¹ ∈ R :=
          (hw.mem_sup_iff.mp (hhz z₀ (mem_sup_left hz₀R) hz₀x)).resolve_left hz₀h
        have e : h * (z₀ * b₁) * h⁻¹ =
            (h * z₀ * h⁻¹ * w⁻¹) * (w * (h * b₁ * h⁻¹ * w⁻¹) * w⁻¹) * w ^ 2 := by
          rw [sq]; group
        rw [e]
        exact mul_mem (mul_mem h1 ((mem_normalizer_iff.mp hw.mem_normalizer _).mp hb₁S))
          hw.sq_mem
      · rw [hC.mul _ hz₀R _ hb₁R', (hC.ker _ hb₁R').mpr hb₁, add_zero, hz₀u]
  have hfix : ∀ z ∈ R, z * x = x * z → (φ z).2.1 = (φ z).2.2 / κ₀ := by
    intro z hz hzx
    have e : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hzx]
        _ = z := by group
    have h1 := hxφ z hz
    rw [e] at h1
    exact congrArg (fun p => p.2.1) h1
  refine false_of_closure_eq_top hC hxA hhx (X := Set.univ) (fun w' _ => ?_)
    (AddSubgroup.closure_univ)
  obtain ⟨u, u', huu'⟩ := VLike.exists_polar_eq hS.one_le hK w'
  obtain ⟨z, hz, hzx, hzh, hzu⟩ := hstep2 u
  obtain ⟨z', hz', hzx', hzh', hzu'⟩ := hstep2 u'
  refine ⟨z * z' * z⁻¹ * z'⁻¹, hS.commutator_mem_gmsA h34 hz hz', ?_, ?_⟩
  · have e : h * (z * z' * z⁻¹ * z'⁻¹) * h⁻¹ = (h * z * h⁻¹) * (h * z' * h⁻¹) *
        (h * z * h⁻¹)⁻¹ * (h * z' * h⁻¹)⁻¹ := by group
    rw [e]
    exact hS.commutator_mem_gmsA h34 hzh hzh'
  · rw [hC.comm z hz z' hz', ← huu', ← hzu, ← hzu']
    simp only [VLike.commMap, zero_mul, add_zero, hfix z hz hzx, hfix z' hz' hzx']
    field_simp
    ring_nf
    have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
    simp [h2]

end Sec3.SzR

end CFSG.ComponentClassification.GMS78

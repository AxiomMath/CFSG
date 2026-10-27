module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Kap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_not_comm_of_quasisimple {X : Subgroup G} (hX : IsQuasisimple ↥X)
    (h : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) : False := by
  obtain ⟨-, -, a, b, hab⟩ := hX
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (h _ a.2 _ b.2)

theorem s7f_conj_mem_centralizer {Y : Subgroup G} {e c : G} (he : e ∈ normalizer (Y : Set G))
    (hc : c ∈ centralizer (Y : Set G)) : e * c * e⁻¹ ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : e⁻¹ * y * e ∈ Y := by
    have h := (Subgroup.mem_normalizer_iff.mp ((normalizer (Y : Set G)).inv_mem he) y).mp hy
    rwa [inv_inv] at h
  have h := hc _ hy'
  calc y * (e * c * e⁻¹) = e * ((e⁻¹ * y * e) * c) * e⁻¹ := by group
    _ = e * (c * (e⁻¹ * y * e)) * e⁻¹ := by rw [h]
    _ = e * c * e⁻¹ * y := by group

theorem s7f_layerCent_le (L : Subgroup G) (s : G) : layerCent L s ≤ L :=
  (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)))).trans inf_le_left

theorem s7f_not_mem_tB [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B E : Subgroup G} (hE : Sec7E G t L S z g B E) {b : G}
    {Y : Subgroup G} (hEY : E ≤ normalizer (Y : Set G)) (hXq : IsQuasisimple ↥(layerCent L b))
    (hXY : layerCent L b ≤ Y) {a : G} (ha : a ∈ cosetSet t B)
    (haY : a ∈ centralizer (Y : Set G)) : False := by
  obtain ⟨b₀, hb₀, rfl⟩ := ha
  have hc := hE.choice
  have hEB : ∀ e ∈ E, ∀ c ∈ B, e * c * e⁻¹ = c := by
    intro e he c hc'
    have h := Subgroup.mem_centralizer_iff.mp (hE.sylow.1 he).2 c hc'
    rw [← h, mul_inv_cancel_right]
  have htB : ∀ b' ∈ B, t * b' ∈ centralizer (Y : Set G) := by
    intro b' hb'
    obtain ⟨e, he, het⟩ :=
      hE.trans (t * (b' * b₀⁻¹)) ⟨b' * b₀⁻¹, B.mul_mem hb' (B.inv_mem hb₀), rfl⟩
    have h1 := s7f_conj_mem_centralizer (hEY he) haY
    have h2 : e * (t * b₀) * e⁻¹ = t * b' := by
      calc e * (t * b₀) * e⁻¹ = (e * t * e⁻¹) * (e * b₀ * e⁻¹) := by group
        _ = t * (b' * b₀⁻¹) * b₀ := by rw [het, hEB e he b₀ hb₀]
        _ = t * b' := by group
    rwa [h2] at h1
  have ht : t ∈ centralizer (Y : Set G) := by simpa using htB 1 B.one_mem
  have hBY : ∀ b' ∈ B, b' ∈ centralizer (Y : Set G) := by
    intro b' hb'
    have e : b' = t⁻¹ * (t * b') := by group
    rw [e]
    exact (centralizer (Y : Set G)).mul_mem ((centralizer (Y : Set G)).inv_mem ht) (htB b' hb')
  have hXB : layerCent L b ≤ B := by
    rw [← (hP.aut_B G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B
      hc.normalE16).2.1]
    intro x hx
    refine ⟨s7f_layerCent_le L b hx, Subgroup.mem_centralizer_iff.mpr fun c hc' => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hBY c hc') x (hXY hx)).symm
  haveI : IsMulCommutative B := hc.normalE16.2.1.1.1
  exact s7f_not_comm_of_quasisimple hXq fun x hx y hy =>
    Subgroup.mul_comm_of_mem_isMulCommutative (H := B) (hXB hx) (hXB hy)

theorem s7f_not_om6m_of_om6p [Finite G] {L : Subgroup G} (hL : IsOm6P L) (hM : IsOm6M L) :
    False := by
  have h1 := ctrQ_of_l43 hL.1 hL.2
  have h2 := ctrQ_of_u43 hM.1 hM.2
  rw [h1] at h2
  exact absurd h2 (by norm_num)

theorem s7f_cent_B_layer [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (h79a : Asc82Lemma79a) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hbt : InducesTypeSome L b 6 1 2 (-1)) :
    B ⊓ centralizer ((layerCent L b : Subgroup G) : Set G) = zpowers b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLP : IsOm6P L := hc.ctx.isOm6P
  have hsq : ∀ x ∈ B, x ^ 2 = 1 := hc.normalE16.2.1.1.2
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hsq b hbB) hb1
  have hbL : b ∈ L := (hc.normalE16.1 hbB).2
  have hbN : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hX : IsL29 (layerCent L b) := hP.layer_i2 G L hLP b hb2 hbN hbt
  have hXc : IsComponentIn (layerCent L b) (L ⊓ centralizer ({b} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hX))
  have hXF : InFStar (layerCent L b) := Or.inr ⟨hXc.isQuasisimple, Or.inl hX⟩
  set R := B ⊓ centralizer ((layerCent L b : Subgroup G) : Set G) with hR
  have hR2 : IsPGroup 2 R := fun x =>
    ⟨1, Subtype.ext (by simpa using hsq (x : G) x.2.1)⟩
  have hRle : R ≤ normalizer (L : Set G) ⊓ centralizer ((layerCent L b : Subgroup G) : Set G) :=
    fun x hx => ⟨Subgroup.le_normalizer (hc.normalE16.1 hx.1).2, hx.2⟩
  have hbR : b ∈ R := by
    refine ⟨hbB, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXc.1 hx).2
  have h0 : centralizer (L : Set G) ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxR⟩
    have hxL : x ∈ L := (hc.normalE16.1 hxR.1).2
    have hmem : x ∈ centerIn L := by
      refine Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rwa [hP.center_triv G L hLP] at hmem
  have hcard : Nat.card R ≤ 2 := by
    rcases hF.aut_cent G L b (layerCent L b) (Or.inl hLP) hb2 hbN hXc hXF
        (fun _ => h79a G t L S z g B hc) R hR2 hRle with h | h | h | h
    · rwa [← Subgroup.inf_relIndex_right, h0, Subgroup.relIndex_bot_left] at h
    · exact (s7f_not_om6m_of_om6p hLP h.2.1).elim
    · exact (s7f_not_om6m_of_om6p hLP h.2.1).elim
    · exfalso
      obtain ⟨φ, hsurj, -⟩ := h.2.2
      obtain ⟨r, hr⟩ := hsurj (Multiplicative.ofAdd 1)
      have hr2 : r ^ 2 = 1 := Subtype.ext (by simpa using hsq (r : G) r.2.1)
      have h1 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 := by
        rw [← hr, ← map_pow, hr2, map_one]
      exact absurd h1 (by decide)
  have hzp : zpowers b ≤ R := (Subgroup.zpowers_le (G := G)).mpr hbR
  exact (Subgroup.eq_of_le_of_card_ge hzp (by rw [Nat.card_zpowers, hb2]; exact hcard)).symm

theorem s7f_cent_A [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (h78 : Asc82Lemma78) (h79a : Asc82Lemma79a) {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec7E G t L S z g B E) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hbt : InducesTypeSome L b 6 1 2 (-1)) {Y : Subgroup G}
    (hYb : Y ≤ centralizer ({b} : Set G)) (hEY : E ≤ normalizer (Y : Set G))
    (hXq : IsQuasisimple ↥(layerCent L b)) (hXY : layerCent L b ≤ Y) :
    centralizer (Y : Set G) ⊓ ASub S B = zpowers b := by
  have hc := hE.choice
  have hBX := s7f_cent_B_layer h36 hP hF h79a hc hbB hb1 hbt
  apply le_antisymm
  · rintro a ⟨haY, haA⟩
    obtain ⟨j, b', hb', rfl⟩ := (sec710_mem_A h78 hc).mp haA
    have ht2 : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [hc.ctx.involution] at h
    have hmod : t ^ (j % 2) = t ^ j := by
      have h := zpow_mod_orderOf t j
      rwa [hc.ctx.involution] at h
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · rw [← hmod, h0, zpow_zero, one_mul] at haY ⊢
      rw [← hBX]
      refine ⟨hb', Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp haY x (hXY hx)
    · rw [← hmod, h1, zpow_one] at haY
      exact (s7f_not_mem_tB h36 hP hE hEY hXq hXY ⟨b', hb', rfl⟩ haY).elim
  · rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, sec79_B_le_A hc hbB⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hYb hy))

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylG
public import CFSG.ClassicalInvolution.Q3.Sec13EndDEQ2Iso
import CFSG.ClassicalInvolution.Q3.TL4D1ML32D

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

omit h in
private theorem dewp1_image_mul (q a : G) (X : Set (Subgroup G)) :
    conjSub (q * a) '' X = conjSub q '' (conjSub a '' X) := by
  rw [Set.image_image]
  congr 1
  funext K
  exact conjSub_mul q a K

omit h in
private theorem dewp1_conjSub_one_image (X : Set (Subgroup G)) : conjSub (1 : G) '' X = X := by
  rw [show conjSub (1 : G) = id from funext conjSub_one, Set.image_id]

private theorem dewp1_fix {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {n : G} (hn : n ∈ pSpan X) : conjSub n '' X = X := by
  let T : Subgroup G :=
    { carrier := {g : G | conjSub g '' X = X}
      mul_mem' := fun {a c} ha hc => by
        have ha' : conjSub a '' X = X := ha
        have hc' : conjSub c '' X = X := hc
        show conjSub (a * c) '' X = X
        rw [dewp1_image_mul, hc', ha']
      one_mem' := by
        show conjSub 1 '' X = X
        exact dewp1_conjSub_one_image X
      inv_mem' := fun {a} ha => by
        have ha' : conjSub a '' X = X := ha
        show conjSub a⁻¹ '' X = X
        calc conjSub a⁻¹ '' X = conjSub a⁻¹ '' (conjSub a '' X) := by rw [ha']
          _ = conjSub (a⁻¹ * a) '' X := (dewp1_image_mul a⁻¹ a X).symm
          _ = X := by
            rw [inv_mul_cancel]
            exact dewp1_conjSub_one_image X }
  have hsub : pSpan X ≤ T := by
    refine pSpan_le fun K hK => ?_
    intro k hk
    exact (h.forall_conjSub_image_eq_iff_mem S hb hX (hX.1 hK)).mpr hK k hk
  exact hsub hn

omit h in
private theorem dewp1_dual_add {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) : f + g ∈ DE2Hyp.deq2Dual Ω := by
  simp only [DE2Hyp.deq2Dual, Set.mem_setOf_eq] at hf hg ⊢
  obtain ⟨hf1, hf0, hfm⟩ := hf
  obtain ⟨hg1, hg0, hgm⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · simp [hf1, hg1]
  · intro x hx
    simp [hf0 x hx, hg0 x hx]
  · intro x hx y hy
    simp only [Pi.add_apply, hfm x hx y hy, hgm x hx y hy]
    ring

private theorem dewp1_dual_sep {w u : G} (hw : w ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    (hw1 : w ≠ 1) (hu1 : u ≠ 1) (hwu : w ≠ u) :
    ∃ φ ∈ DE2Hyp.deq2Dual Ω, φ w = 0 ∧ φ u = 1 := by
  obtain ⟨f, hf, hfne⟩ := h.exists_dual_ne hu (one_mem _) hu1
  obtain ⟨g, hg, hgne⟩ := h.exists_dual_ne hw hu hwu
  have hf1 : f 1 = 0 := hf.1
  have hfu : f u = 1 := by
    rcases zmod2_cases (f u) with h0 | h0
    · exact absurd (h0.trans hf1.symm) hfne
    · exact h0
  rcases zmod2_cases (f w) with hfw | hfw
  · exact ⟨f, hf, hfw, hfu⟩
  · rcases zmod2_cases (g w) with hgw | hgw
    · have hgu : g u = 1 := by
        rcases zmod2_cases (g u) with h0 | h0
        · exact absurd (hgw.trans h0.symm) hgne
        · exact h0
      exact ⟨g, hg, hgw, hgu⟩
    · have hgu : g u = 0 := by
        rcases zmod2_cases (g u) with h0 | h0
        · exact h0
        · exact absurd (hgw.trans h0.symm) hgne
      refine ⟨f + g, dewp1_dual_add hf hg, ?_, ?_⟩
      · show f w + g w = 0
        rw [hfw, hgw]
        decide
      · show f u + g u = 1
        rw [hfu, hgu]
        decide

omit h in
private theorem dewp1_conjSub_eq_of_comm {g : G} {L : Subgroup G}
    (hc : ∀ y ∈ L, y * g = g * y) : conjSub g L = L := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have hw := hc _ hy
    have e : y = g⁻¹ * y * g := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = (g⁻¹ * y * g) * g * g⁻¹ := by rw [hw]
        _ = g⁻¹ * y * g := by group
    rw [e]
    exact hy
  · intro hy
    have e : g⁻¹ * y * g = y := by
      rw [mul_assoc, hc y hy, inv_mul_cancel_left]
    rw [e]
    exact hy

omit h in
private theorem dewp1_shift_mem {S : TwinShift Ω} {b : Lab2} {K : Subgroup G} (hK : K ∈ Ω)
    {u : G} (hu : IsUniqueInvolution K u) : S.shift b K ∈ dew1V Ω u := by
  obtain ⟨hsΩ, z, hKz, hsz⟩ := S.shift_mem b K hK
  have hzu : z = u := hKz.eq hu
  subst hzu
  unfold dew1V
  exact ⟨hsΩ, hsz⟩

omit h in
private theorem dewp1_dewDelta_le {S : TwinShift Ω} {b : Lab2} {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {K : Subgroup G} (hK : K ∈ X) :
    dewDelta K (S.shift b K) ≤ pSpan X := by
  unfold dewDelta
  exact inf_le_left.trans (sup_le (le_pSpan hK) (le_pSpan (hX.2.1 K hK)))

private theorem dewp1_conj_elt {S : TwinShift Ω} {b : Lab2} {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {u₁ u₂ : G} (hu₁ : u₁ ∈ zGroup Ω) (hu₂ : u₂ ∈ zGroup Ω)
    (hu₁1 : u₁ ≠ 1) (hu₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    ∃ k ∈ pSpan X, k * u₁ * k⁻¹ = u₂ := by
  have hc : u₁ * u₂ = u₂ * u₁ := h.zGroup_comm u₁ hu₁ u₂ hu₂
  have hsq : u₁ * u₁ = 1 := h.zGroup_mul_self u₁ hu₁
  have hw : u₁ * u₂ ∈ zGroup Ω := (zGroup Ω).mul_mem hu₁ hu₂
  have hw1 : u₁ * u₂ ≠ 1 := by
    intro e
    apply hne
    have h2 : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h2, inv_eq_of_mul_eq_one_right hsq]
  have hw2 : u₁ * u₂ ≠ u₁ := by
    intro e
    apply hu₂1
    exact mul_left_cancel (e.trans (mul_one u₁).symm)
  obtain ⟨L, hL, hLw⟩ := h.pt_exists_mem S hX hw hw1
  obtain ⟨φ, hφ, hφw, hφu⟩ := dewp1_dual_sep h hw hu₁ hw1 hu₁1 hw2
  obtain ⟨k, hkL, hk⟩ := h.exists_mem_isElationOf (hX.1 hL) hLw hφ hφw
  refine ⟨k, le_pSpan hL hkL, ?_⟩
  have hku := hk u₁ hu₁
  have hφu1 : φ u₁ ≠ 0 := by
    rw [hφu]
    decide
  rw [if_neg hφu1] at hku
  rw [hku]
  calc u₁ * u₂ * u₁ = u₁ * (u₂ * u₁) := mul_assoc _ _ _
    _ = u₁ * (u₁ * u₂) := by rw [← hc]
    _ = (u₁ * u₁) * u₂ := (mul_assoc _ _ _).symm
    _ = u₂ := by rw [hsq, one_mul]

private theorem dewp1_lam_swap {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {z : G} (hz : z ∈ zGroup Ω) (hz1 : z ≠ 1) :
    ∃ a ∈ pSpan X, a ∈ pCore 2 G ∧ S.lam a z = b := by
  classical
  have hcard : ({1, z} : Finset G).card < Nat.card (zGroup Ω) := by
    rw [h.card_zGroup]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨w, hw, hwS⟩ := TL4.exists_mem_not_mem (E := zGroup Ω) ({1, z} : Finset G) hcard
  have hw1 : w ≠ 1 := fun e => hwS (by simp [e])
  have hwz : w ≠ z := fun e => hwS (by simp [e])
  obtain ⟨φ, hφ, hφw, hφz⟩ := dewp1_dual_sep h hw hz hw1 hz1 hwz
  obtain ⟨L, hL, hLw⟩ := h.pt_exists_mem S hX hw hw1
  obtain ⟨a, ha, hlam⟩ := (h.lam_dewDelta_range S hb (hX.1 hL) hLw).2 φ hφ hφw
  refine ⟨a, dewp1_dewDelta_le hX hL ha, dewDelta_le_pCore _ _ ha, ?_⟩
  rw [hlam z, hφz, one_smul]

private theorem dewp1_conj_mem {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ X) (hK₂ : K₂ ∈ X) :
    ∃ g ∈ pSpan X, conjSub g K₁ = K₂ := by
  obtain ⟨z₁, hz₁⟩ := h.exists_isUniqueInvolution (hX.1 hK₁)
  obtain ⟨z₂, hz₂⟩ := h.exists_isUniqueInvolution (hX.1 hK₂)
  have hz₁D : z₁ ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K₁, hX.1 hK₁, hz₁⟩)
  have hz₂D : z₂ ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K₂, hX.1 hK₂, hz₂⟩)
  obtain ⟨g₀, hg₀H, hg₀⟩ : ∃ g ∈ pSpan X, g * z₁ * g⁻¹ = z₂ := by
    by_cases he : z₁ = z₂
    · exact ⟨1, one_mem _, by rw [he]; simp⟩
    · exact dewp1_conj_elt h hX hz₁D hz₂D hz₁.ne_one hz₂.ne_one he
  have hK' : conjSub g₀ K₁ ∈ X := by
    have hmem : conjSub g₀ K₁ ∈ conjSub g₀ '' X := ⟨K₁, hK₁, rfl⟩
    rwa [dewp1_fix h hb hX hg₀H] at hmem
  have hK'inv : IsUniqueInvolution (conjSub g₀ K₁) z₂ := by
    have := hz₁.conj g₀
    rwa [hg₀] at this
  have htw : conjSub g₀ K₁ ∈ twinSet Ω K₂ ∩ X := ⟨⟨hX.1 hK', z₂, hz₂, hK'inv⟩, hK'⟩
  rw [h.pt_twin_inter S hb hX hK₂] at htw
  rcases Set.mem_insert_iff.mp htw with h1 | h1
  · exact ⟨g₀, hg₀H, h1⟩
  · have h1' : conjSub g₀ K₁ = S.shift b K₂ := Set.mem_singleton_iff.mp h1
    obtain ⟨a, haH, hapC, hlam⟩ := dewp1_lam_swap h hb hX hz₂D hz₂.ne_one
    have hsh : S.shift b K₂ ∈ dew1V Ω z₂ := dewp1_shift_mem (hX.1 hK₂) hz₂
    have hak : conjSub a (S.shift b K₂) = K₂ := by
      rw [h.lam_spec S hapC hsh, hlam, S.shift_shift_self b (hX.1 hK₂)]
    exact ⟨a * g₀, mul_mem haH hg₀H, by rw [conjSub_mul, h1', hak]⟩

theorem de2Hyp_point (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) :
    DE2Hyp {L : Subgroup ↥(pSpan X) | ∃ K ∈ X, L = K.subgroupOf (pSpan X)} := by
  have hX' : IsDewPoint S b X := hX
  have hXΩ : ∀ K ∈ X, K ∈ Ω := fun K hK => hX'.1 hK
  have hKH : ∀ K ∈ X, K ≤ pSpan X := fun K hK => le_pSpan hK
  have hDH : zGroup Ω ≤ pSpan X := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · obtain ⟨L, hL, hLx⟩ := h.pt_exists_mem S hX' hx hx1
      exact le_pSpan hL hLx.mem
  have hinvD : ∀ K ∈ X, ∀ z : G, IsUniqueInvolution K z → z ∈ zGroup Ω :=
    fun K hK z hz => h.mem_zGroup_iff.mpr (Or.inr ⟨K, hXΩ K hK, hz⟩)
  have hset : {L : Subgroup ↥(pSpan X) | ∃ K ∈ X, L = K.subgroupOf (pSpan X)} =
      restrictFamily X (pSpan X) := by
    ext L
    constructor
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, hKH K hK, rfl⟩
    · rintro ⟨K, hK, -, rfl⟩
      exact ⟨K, hK, rfl⟩
  rw [hset]
  have hdown : ∀ K ∈ X, ∀ u : ↥(pSpan X), IsUniqueInvolution (K.subgroupOf (pSpan X)) u →
      IsUniqueInvolution K (u : G) :=
    fun K hK u hu => isUniqueInvolution_of_subgroupOf hu (hKH K hK)
  have hup : ∀ (K : Subgroup G) (hK : K ∈ X) (z : G) (hz : IsUniqueInvolution K z),
      IsUniqueInvolution (K.subgroupOf (pSpan X)) (⟨z, hKH K hK hz.mem⟩ : ↥(pSpan X)) :=
    fun K hK z hz => isUniqueInvolution_subgroupOf hz (hKH K hK)
  have hinvX : ∀ n ∈ pSpan X, ∀ K ∈ X, conjSub n K ∈ X := by
    intro n hn K hK
    have hmem : conjSub n K ∈ conjSub n '' X := ⟨K, hK, rfl⟩
    rwa [dewp1_fix h hb hX' hn] at hmem
  have hzG : zGroup (restrictFamily X (pSpan X)) = (zGroup Ω).subgroupOf (pSpan X) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨L, hL, hLu⟩
      obtain ⟨K, hK, -, rfl⟩ := hL
      exact Subgroup.mem_subgroupOf.mpr (hinvD K hK u.1 (hdown K hK u hLu))
    · intro u hu
      rw [Subgroup.mem_subgroupOf] at hu
      by_cases hu1 : (u : G) = 1
      · have hu' : u = 1 := Subtype.ext hu1
        rw [hu']
        exact one_mem _
      · obtain ⟨K, hK, hKu⟩ := h.pt_exists_mem S hX' hu hu1
        exact Subgroup.subset_closure
          ⟨K.subgroupOf (pSpan X), ⟨K, hK, hKH K hK, rfl⟩, hup K hK u.1 hKu⟩
  have hcardZ : Nat.card (zGroup (restrictFamily X (pSpan X))) = 8 := by
    rw [hzG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, h.card_zGroup]
  have hdNorm : ∀ L ∈ restrictFamily X (pSpan X),
      zGroup (restrictFamily X (pSpan X)) ≤ Subgroup.normalizer (L : Set ↥(pSpan X)) := by
    rintro _ ⟨K, hK, -, rfl⟩ x hx
    rw [hzG, Subgroup.mem_subgroupOf] at hx
    have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) := h.dNorm K (hXΩ K hK) hx
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hxN y.1
  have hperp : Perp9 (restrictFamily X (pSpan X)) := by
    rintro _ ⟨K, hK, -, rfl⟩ _ ⟨K', hK', -, rfl⟩ hc z j hz hj
    have hc' : Commutes K K' := by
      intro x hx y hy
      have e := hc ⟨x, hKH K hK hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hKH K' hK' hy⟩
        (Subgroup.mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val e
    exact Subtype.ext
      (h.perp K (hXΩ K hK) K' (hXΩ K' hK') hc' z.1 j.1 (hdown K hK z hz) (hdown K' hK' j hj))
  have htwo : ∀ J ∈ restrictFamily X (pSpan X), IsPGroup 2 J := by
    rintro _ ⟨K, hK, -, rfl⟩
    exact (h.two K (hXΩ K hK)).comap_subtype
  have hcard8 : ∀ J ∈ restrictFamily X (pSpan X), Nat.card J = 8 := by
    rintro _ ⟨K, hK, hKH', rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH').toEquiv]
    exact h.card K (hXΩ K hK)
  have hmap : (pSpan (restrictFamily X (pSpan X))).map (pSpan X).subtype = pSpan X := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun K hK => ?_)
    have hKmem : K.subgroupOf (pSpan X) ∈ restrictFamily X (pSpan X) :=
      ⟨K, hK, hKH K hK, rfl⟩
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hKH K hK hx⟩, le_pSpan hKmem (Subgroup.mem_subgroupOf.mpr hx),
      rfl⟩
  have hgen : pSpan (restrictFamily X (pSpan X)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : G) ∈ (pSpan (restrictFamily X (pSpan X))).map (pSpan X).subtype := by
      rw [hmap]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  have htrans : ∀ L ∈ restrictFamily X (pSpan X), ∀ L' ∈ restrictFamily X (pSpan X),
      ∃ g : ↥(pSpan X), conjSub g L = L' := by
    rintro _ ⟨K₁, hK₁, -, rfl⟩ _ ⟨K₂, hK₂, -, rfl⟩
    obtain ⟨g, hgH, hg⟩ := dewp1_conj_mem h hb hX' hK₁ hK₂
    refine ⟨⟨g, hgH⟩, ?_⟩
    rw [conjSub_subgroupOf]
    show (conjSub g K₁).subgroupOf (pSpan X) = K₂.subgroupOf (pSpan X)
    rw [hg]
  have hcenter : Subgroup.center ↥(pSpan X) = ⊥ := by
    classical
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_center_iff] at hg
    have hcomm : ∀ x ∈ pSpan X, x * (g : G) = (g : G) * x :=
      fun x hx => congrArg Subtype.val (hg ⟨x, hx⟩)
    have hgC : (g : G) ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hcomm d (hDH hd)
    rw [h.centralizer_zGroup_eq_pCore] at hgC
    have hlam : ∀ u ∈ zGroup Ω, u ≠ 1 → S.lam (g : G) u = 0 := by
      intro u hu hu1
      obtain ⟨L, hL, hLu⟩ := h.pt_exists_mem S hX' hu hu1
      have hcL : conjSub (g : G) L = L :=
        dewp1_conjSub_eq_of_comm (fun y hy => hcomm y (hKH L hL hy))
      have hLd : L ∈ dew1V Ω u := by
        unfold dew1V
        exact ⟨hXΩ L hL, hLu⟩
      exact (h.conjSub_eq_iff_lam_eq_zero S hgC hLd).mp hcL
    have hlam0 : ∀ x : G, S.lam (g : G) x = 0 := by
      intro x
      by_cases hx : x ∈ zGroup Ω
      · by_cases hx1 : x = 1
        · exact h.lam_eq_zero_of_not_mem S (Or.inr hx1)
        · exact hlam x hx hx1
      · exact h.lam_eq_zero_of_not_mem S (Or.inl hx)
    have hgD : (g : G) ∈ zGroup Ω := (h.lam_eq_zero_iff S hgC).mp hlam0
    have hg1 : (g : G) = 1 := by
      by_contra hne
      have hcard : ({1, (g : G)} : Finset G).card < Nat.card (zGroup Ω) := by
        rw [h.card_zGroup]
        exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
      obtain ⟨t, htD, ht⟩ := TL4.exists_mem_not_mem (E := zGroup Ω) ({1, (g : G)} : Finset G) hcard
      have ht1 : t ≠ 1 := fun e => ht (by simp [e])
      have ht2 : t ≠ (g : G) := fun e => ht (by simp [e])
      obtain ⟨k, hkH, hk⟩ := dewp1_conj_elt h hX' hgD htD hne ht1 (Ne.symm ht2)
      have hkc : k * (g : G) = (g : G) * k := hcomm k hkH
      have hkk : k * (g : G) * k⁻¹ = (g : G) := by
        rw [hkc, mul_inv_cancel_right]
      exact ht2 (hk.symm.trans hkk)
    exact Subtype.ext hg1
  have hinO2 : ∀ L ∈ restrictFamily X (pSpan X), ∀ u : ↥(pSpan X),
      IsUniqueInvolution L u → ∃ Q : Subgroup ↥(pSpan X), Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    rintro _ ⟨K, hK, -, rfl⟩ u hu
    have hKu : IsUniqueInvolution K (u : G) := hdown K hK u hu
    obtain ⟨Q₀, hQ₀n, hQ₀2, huQ₀⟩ := h.inO2 K (hXΩ K hK) (u : G) hKu
    have hQ₀le : Q₀ ≤ pCore 2 G := le_sSup ⟨hQ₀n, hQ₀2⟩
    refine ⟨(pCore 2 G).subgroupOf (pSpan X),
      (CFSG.pCore_normal (p := 2) (G := G)).subgroupOf _,
      (CFSG.pCore_isPGroup (p := 2) (G := G)).comap_subtype, ?_⟩
    exact Subgroup.mem_subgroupOf.mpr (hQ₀le huQ₀)
  have htwin : ∀ L ∈ restrictFamily X (pSpan X),
      (twinSet (restrictFamily X (pSpan X)) L).ncard = 2 := by
    rintro _ ⟨K, hK, hKH', rfl⟩
    have himage : twinSet (restrictFamily X (pSpan X)) (K.subgroupOf (pSpan X)) =
        (fun K' : Subgroup G => K'.subgroupOf (pSpan X)) '' (twinSet Ω K ∩ X) := by
      ext J
      constructor
      · rintro ⟨⟨K', hK', -, rfl⟩, z, hz, hJz⟩
        exact ⟨K', ⟨⟨hXΩ K' hK', z.1, hdown K hK z hz, hdown K' hK' _ hJz⟩, hK'⟩, rfl⟩
      · rintro ⟨K', ⟨⟨hK'Ω, z, hKz, hK'z⟩, hK'X⟩, rfl⟩
        unfold twinSet
        exact ⟨⟨K', hK'X, hKH K' hK'X, rfl⟩, ⟨⟨z, hKH K hK hKz.mem⟩, hup K hK z hKz,
          hup K' hK'X z hK'z⟩⟩
    have hinj : Set.InjOn (fun K' : Subgroup G => K'.subgroupOf (pSpan X)) (twinSet Ω K ∩ X) := by
      intro K₁ hK₁ K₂ hK₂ e
      have e' : K₁.subgroupOf (pSpan X) = K₂.subgroupOf (pSpan X) := e
      calc K₁ = (K₁.subgroupOf (pSpan X)).map (pSpan X).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le (hKH K₁ hK₁.2)).symm
        _ = (K₂.subgroupOf (pSpan X)).map (pSpan X).subtype := by rw [e']
        _ = K₂ := Subgroup.map_subgroupOf_eq_of_le (hKH K₂ hK₂.2)
    rw [himage, hinj.ncard_image]
    exact hX'.2.2.1 K (hXΩ K hK)
  have hyp : HypOmegaGen (restrictFamily X (pSpan X)) := by
    refine CFSG.ClassicalInvolution.Q3.TL4.hypOmegaGen_restrict_of (pSpan X)
      (fun K hK => hKH K hK) hinvX (fun K hK => h.hyp.omega1 K (hXΩ K hK)) (fun K hK => ?_)
      (fun K hK J hJ P Q hP hQ => h.hyp.omega3 K (hXΩ K hK) J (hXΩ J hJ) P Q hP hQ)
      (fun K hK J hJ hne => h.hyp.omega4 K (hXΩ K hK) J (hXΩ J hJ) hne)
      (fun K hK J hJ hne => h.hyp.omega5 K (hXΩ K hK) J (hXΩ J hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (h.two K (hXΩ K hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  exact ⟨⟨hyp, htwo, hcard8, hgen, htrans, hcenter, hinO2, hperp, hdNorm, hcardZ⟩, htwin⟩

omit h in
private theorem dewp2_fano_det : ∀ x y : Fin 7, (∀ ℓ ∈ AE.fanoLines, y ∈ ℓ → x ∈ ℓ) → x = y := by
  decide +kernel

omit h in
private abbrev dewp2_V4 : List (Equiv.Perm (Fin 4)) := [1, AE.d₁, AE.d₂, AE.d₃]

omit h in
private theorem dewp2_V4_mul : ∀ c ∈ dewp2_V4, ∀ c' ∈ dewp2_V4, c * c' ∈ dewp2_V4 := by
  decide +kernel

omit h in
private theorem dewp2_V4_inv : ∀ c ∈ dewp2_V4, c⁻¹ ∈ dewp2_V4 := by
  decide +kernel

omit h in
private theorem dewp2_V4_join : ∀ c ∈ dewp2_V4,
    ∃ a ∈ AE.kList, ∃ b ∈ AE.kStarList, a * b = AE.Wr.ofPerm c := by
  decide +kernel

omit h in
private theorem dewp2_V4_perm_kQ : ∀ a ∈ AE.kList, a.perm ∈ dewp2_V4 := by
  decide +kernel

omit h in
private theorem dewp2_V4_perm_kQStar : ∀ a ∈ AE.kStarList, a.perm ∈ dewp2_V4 := by
  decide +kernel

omit h in
private def dewp2_Ph : Equiv.Perm (Fin 7) →* AE.AEQ 7 where
  toFun σ := AE.mkQ 7 (AE.Wr.ofPerm σ)
  map_one' := by
    show AE.mkQ 7 (AE.Wr.ofPerm 1) = 1
    rw [AE.ofPerm_one, map_one]
  map_mul' σ τ := by
    show AE.mkQ 7 (AE.Wr.ofPerm (σ * τ)) = AE.mkQ 7 (AE.Wr.ofPerm σ) * AE.mkQ 7 (AE.Wr.ofPerm τ)
    rw [← map_mul, AE.ofPerm_mul]

omit h in
private theorem dewp2_Ph_injective : Function.Injective dewp2_Ph := by
  intro σ τ h
  have h' : AE.mkQ 7 (AE.Wr.ofPerm σ) = AE.mkQ 7 (AE.Wr.ofPerm τ) := h
  rcases AE.mkQ_eq_iff.mp h' with h1 | h1
  · have h2 := congrArg AE.Wr.perm h1
    rw [AE.Wr.mul_perm, AE.Wr.inv_perm] at h2
    have h3 : σ⁻¹ * τ = 1 := h2
    exact inv_mul_eq_one.mp h3
  · exfalso
    have hl : ((AE.Wr.ofPerm σ)⁻¹ * AE.Wr.ofPerm τ).vec 0 = 0 := by
      simp [AE.Wr.mul_vec, AE.Wr.inv_vec, AE.Wr.ofPerm]
    rw [h1] at hl
    exact absurd hl (by decide)

omit h in
private def dewp2_pm : AE.AEQ 7 →* Equiv.Perm (Fin 7) :=
  QuotientGroup.lift (AE.piSub 7) (AE.permHom 7) (by
    intro a ha
    rcases ha with rfl | rfl
    · rfl
    · rfl)

omit h in
private theorem dewp2_pm_mk (a : AE.Wr 7) : dewp2_pm (AE.mkQ 7 a) = a.perm := rfl

omit h in
private theorem dewp2_pm_Ph (σ : Equiv.Perm (Fin 7)) : dewp2_pm (dewp2_Ph σ) = σ := rfl

omit h in
private theorem dewp2_mem_l32 {σ : Equiv.Perm (Fin 7)} (h : dewp2_Ph σ ∈ AE.e64Sub) :
    σ ∈ AE.l32 := by
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp h
  have hwe' : AE.mkQ 7 w = AE.mkQ 7 (AE.Wr.ofPerm σ) := hwe
  have hw' := (Subgroup.mem_inf.mp hw).2
  have hwl : w.perm ∈ AE.l32 := Subgroup.mem_comap.mp hw'
  have hp : w.perm⁻¹ * σ = 1 := by
    rcases AE.mkQ_eq_iff.mp hwe' with h1 | h1
    · have h2 := congrArg AE.Wr.perm h1
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm] at h2
      exact h2
    · have h2 := congrArg AE.Wr.perm h1
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm] at h2
      exact h2
  have hσ : σ = w.perm := (inv_mul_eq_one.mp hp).symm
  rw [hσ]
  exact hwl

omit h in
private theorem dewp2_Ph_mem_e64 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ AE.l32) :
    dewp2_Ph σ ∈ AE.e64Sub :=
  ⟨AE.Wr.ofPerm σ, AE.ofPerm_mem_aeSubOver hσ (TL4.l32_sign σ hσ), rfl⟩

omit h in
private theorem dewp2_card_l32 : Nat.card (AE.l32 : Subgroup (Equiv.Perm (Fin 7))) = 168 :=
  (Nat.card_congr TL4.sl3TwoEquivL32.toEquiv).symm.trans TL4.card_sl3Two

omit h in
private theorem dewp2_card_M : Nat.card ↥(AE.l32.map dewp2_Ph) = 168 := by
  rw [Subgroup.card_map_of_injective dewp2_Ph_injective, dewp2_card_l32]

omit h in
private theorem dewp2_embedVec_zero (ι : Fin 4 ↪ Fin 7) : AE.embedVec ι 0 = 0 := by
  funext x
  unfold AE.embedVec
  split_ifs <;> simp

omit h in
private theorem dewp2_mem_join {α : Finset (Fin 7)} (h : α.card = 4) {c : Equiv.Perm (Fin 4)}
    (hc : c ∈ dewp2_V4) :
    dewp2_Ph (AE.embedPerm (AE.emb α h) c) ∈ AE.memBar α h true ⊔ AE.memBar α h false := by
  obtain ⟨a, ha, b, hb, hab⟩ := dewp2_V4_join c hc
  have hmem : AE.Wr.ofPerm c ∈ AE.kQ ⊔ AE.kQStar := by
    rw [← hab]
    exact Subgroup.mul_mem_sup (AE.mem_kQ.mpr ha) (AE.mem_kQStar.mpr hb)
  have hemb : AE.embed (AE.emb α h) (AE.Wr.ofPerm c) ∈
      AE.memK (AE.emb α h) ⊔ AE.memKStar (AE.emb α h) := by
    have := Subgroup.mem_map_of_mem (AE.embed (AE.emb α h)) hmem
    rwa [Subgroup.map_sup] at this
  have hfix : AE.embed (AE.emb α h) (AE.Wr.ofPerm c) =
      AE.Wr.ofPerm (AE.embedPerm (AE.emb α h) c) := by
    refine AE.Wr.ext ?_ ?_
    · rw [AE.embed_vec]
      exact dewp2_embedVec_zero _
    · rw [AE.embed_perm]
      rfl
  have key := Subgroup.mem_map_of_mem (AE.mkQ 7) hemb
  rw [Subgroup.map_sup] at key
  rw [hfix] at key
  exact key

omit h in
private theorem dewp2_sigma_stab {α : Finset (Fin 7)} (h : α.card = 4) {σ : Equiv.Perm (Fin 7)}
    (hc : dewp2_Ph σ * AE.zBar α h = AE.zBar α h * dewp2_Ph σ) :
    ∀ y ∈ α, σ y ∈ α := by
  have hc' : AE.mkQ 7 (AE.Wr.ofPerm σ) * AE.mkQ 7 (AE.zOf (AE.emb α h)) =
      AE.mkQ 7 (AE.zOf (AE.emb α h)) * AE.mkQ 7 (AE.Wr.ofPerm σ) := hc
  rcases AE.comm_or_of_mkQ_comm hc' with h1 | h1
  · intro y hy
    have hy' : y ∈ Set.range (AE.emb α h) := by rw [AE.range_emb]; exact hy
    have := AE.perm_mem_of_comm_zOf (b := AE.Wr.ofPerm σ) h1.symm hy'
    rw [AE.range_emb] at this
    exact this
  · exfalso
    have hnot : ∀ y ∈ α, σ.symm y ∉ α := by
      intro y hy hmem
      have hv := congrArg (fun a => AE.Wr.vec a y) h1
      have hyr : y ∈ Set.range (AE.emb α h) := by rw [AE.range_emb]; exact hy
      have hmr : σ.symm y ∈ Set.range (AE.emb α h) := by rw [AE.range_emb]; exact hmem
      simp only [AE.Wr.mul_vec, AE.zOf_vec_apply, AE.zOf_perm, AE.Wr.ofPerm, AE.Wr.allOnes,
        AE.Wr.one_perm, Equiv.Perm.one_apply, hyr, hmr, if_true, Pi.zero_apply, zero_add,
        add_zero] at hv
      exact absurd hv (by decide)
    have hsub : α.map σ.symm.toEmbedding ⊆ αᶜ := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_compl.mpr (hnot y hy)
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Finset.card_compl, Fintype.card_fin, h] at this
    omega

omit h in
private theorem dewp2_eq_one_of_lines {σ : Equiv.Perm (Fin 7)}
    (hσ : ∀ ℓ ∈ AE.fanoLines, ∀ y, σ y ∈ ℓ → y ∈ ℓ) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  have := dewp2_fano_det x (σ x) (fun ℓ hℓ => hσ ℓ hℓ x)
  rw [Equiv.Perm.one_apply]
  exact this.symm

omit h in
private theorem dewp2_V_inj : ∀ i j : Fin 4,
    (![1, AE.d₁, AE.d₂, AE.d₃] : Fin 4 → Equiv.Perm (Fin 4)) i =
      (![1, AE.d₁, AE.d₂, AE.d₃] : Fin 4 → Equiv.Perm (Fin 4)) j → i = j := by
  decide +kernel

omit h in
private def dewp2_Hι (ι : Fin 4 ↪ Fin 7) : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {σ | ∃ c ∈ dewp2_V4, σ = AE.embedPerm ι c}
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c * c', dewp2_V4_mul c hc c' hc', (AE.embedPerm_mul ι c c').symm⟩
  one_mem' := ⟨1, by simp [dewp2_V4], (AE.embedPerm_one ι).symm⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c⁻¹, dewp2_V4_inv c hc, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← AE.embedPerm_mul, mul_inv_cancel, AE.embedPerm_one]

omit h in
private theorem dewp2_memBar_le {α : Finset (Fin 7)} (h : α.card = 4) (b : Bool) :
    AE.memBar α h b ≤ (dewp2_Hι (AE.emb α h)).comap dewp2_pm := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_comap, dewp2_pm_mk]
  cases b
  · have ha2 : a ∈ AE.memKStar (AE.emb α h) := ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha2
    exact ⟨a'.perm, dewp2_V4_perm_kQStar a' ha', rfl⟩
  · have ha2 : a ∈ AE.memK (AE.emb α h) := ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha2
    exact ⟨a'.perm, dewp2_V4_perm_kQ a' ha', rfl⟩

omit h in
private theorem dewp2_count {α : Finset (Fin 7)} (h : α.card = 4)
    (h1 : AE.memBar α h true ≤ AE.e64Sub) (h2 : AE.memBar α h false ≤ AE.e64Sub) :
    Nat.card ↥((AE.l32.map dewp2_Ph) ⊓ (AE.memBar α h true ⊔ AE.memBar α h false)) = 4 := by
  set ι := AE.emb α h with hι
  set J := AE.memBar α h true ⊔ AE.memBar α h false with hJdef
  have hJe : J ≤ AE.e64Sub := sup_le h1 h2
  have hJH : J ≤ (dewp2_Hι ι).comap dewp2_pm :=
    sup_le (dewp2_memBar_le h true) (dewp2_memBar_le h false)
  let V : Fin 4 → Equiv.Perm (Fin 4) := ![1, AE.d₁, AE.d₂, AE.d₃]
  have hV : ∀ i, V i ∈ dewp2_V4 := by
    intro i
    fin_cases i <;> simp [V, dewp2_V4]
  have hVinj : ∀ i j, V i = V j → i = j := dewp2_V_inj
  let e : Fin 4 → AE.AEQ 7 := fun i => dewp2_Ph (AE.embedPerm ι (V i))
  have he_mem : ∀ i, e i ∈ J := fun i => dewp2_mem_join h (hV i)
  have he_inj : Function.Injective e := by
    intro i j hij
    have h3 := dewp2_Ph_injective hij
    have hV' : V i = V j := by
      refine Equiv.ext fun k => ?_
      have h4 := congrArg (fun σ : Equiv.Perm (Fin 7) => σ (ι k)) h3
      simp only [AE.embedPerm_apply] at h4
      exact ι.injective h4
    exact hVinj i j hV'
  have hrange : ((AE.l32.map dewp2_Ph ⊓ J : Subgroup (AE.AEQ 7)) : Set (AE.AEQ 7)) =
      Set.range e := by
    ext x
    constructor
    · rintro ⟨hxM, hxJ⟩
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hxM
      have hpm : σ ∈ dewp2_Hι ι := by
        have := Subgroup.mem_comap.mp (hJH hxJ)
        rwa [dewp2_pm_Ph] at this
      obtain ⟨c, hc, hσc⟩ := hpm
      have hci : ∃ i, V i = c := by
        simp only [dewp2_V4, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨0, by simp [V]⟩
        · exact ⟨1, by simp [V]⟩
        · exact ⟨2, by simp [V]⟩
        · exact ⟨3, by simp [V]⟩
      obtain ⟨i, rfl⟩ := hci
      exact ⟨i, by simp only [e]; rw [hσc]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨AE.embedPerm ι (V i), ?_, rfl⟩, he_mem i⟩
      exact dewp2_mem_l32 (hJe (he_mem i))
  have hcard : Nat.card ↥((AE.l32.map dewp2_Ph) ⊓ J) = Nat.card (Set.range e) := by
    rw [← hrange]
    rfl
  rw [hcard, Nat.card_range_of_injective he_inj, Nat.card_eq_fintype_card, Fintype.card_fin]

omit h in
private theorem dewp2_conj_involution {Ω : Set (Subgroup G)} (S : TwinShift Ω) {b : Lab2}
    {K : Subgroup G} {z g : G} (hKΩ : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution (S.shift b K) z) (hg : g ∈ dewA S b) : g * z * g⁻¹ = z := by
  have hc := hz.conj g
  rcases hg.2 K hKΩ with h1 | h1
  · rw [h1] at hc
    exact (hz.eq hc).symm
  · rw [h1] at hc
    exact (hz'.eq hc).symm

omit h in
private theorem dewp2_phi_involution {T : Type} [Group T] {φ : T →* AE.AEQ 7}
    (hφ : Function.Injective φ) {A : Subgroup T} {α : Finset (Fin 7)} {hα : α.card = 4}
    {c : Bool} (hA : A.map φ = AE.memBar α hα c) {w : T} (hw : w ∈ A) (hw1 : w ≠ 1)
    (hw2 : w * w = 1) : φ w = AE.zBar α hα := by
  have hmem : φ w ∈ AE.memBar α hα c := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem φ hw
  have hsq : φ w * φ w = 1 := by rw [← map_mul, hw2, map_one]
  have hne : φ w ≠ 1 := by
    intro h1
    apply hw1
    apply hφ
    rw [h1, map_one]
  rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hmem hsq with h2 | h2
  · exact absurd h2 hne
  · exact h2

omit h in
private theorem dewp2_alpha_eq {T : Type} [Group T] {φ : T →* AE.AEQ 7}
    (hφ : Function.Injective φ) {A A' : Subgroup T} {α α' : Finset (Fin 7)}
    {hα : α.card = 4} {hα' : α'.card = 4} {c c' : Bool}
    (hA : A.map φ = AE.memBar α hα c) (hA' : A'.map φ = AE.memBar α' hα' c')
    {w : T} (hw : w ∈ A) (hw' : w ∈ A') (hw1 : w ≠ 1) (hw2 : w * w = 1) : α = α' := by
  have e1 := dewp2_phi_involution hφ hA hw hw1 hw2
  have e2 := dewp2_phi_involution hφ hA' hw' hw1 hw2
  exact AE.eq_of_zBar_eq (by norm_num) (e1.symm.trans e2)

theorem exists_good_pointComplement (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) :
    ∃ L : Subgroup G, L ≤ pSpan X ∧ Nat.card L = 168 ∧ L ⊓ dewA S b = ⊥ ∧
      ∀ K ∈ X, Nat.card ↥(L ⊓ (K ⊔ S.shift b K)) = 4 := by
  classical
  have hXΩ : ∀ K ∈ X, K ∈ Ω := fun K hK => hX.1 hK
  have hXsh : ∀ K ∈ X, S.shift b K ∈ X := fun K hK => hX.2.1 K hK
  obtain ⟨Ω', hΩ'⟩ : ∃ Ω' : Set (Subgroup ↥(pSpan X)),
      Ω' = {L | ∃ K ∈ X, L = K.subgroupOf (pSpan X)} := ⟨_, rfl⟩
  have hA : DE2Hyp Ω' := by
    rw [hΩ']
    exact de2Hyp_point h S hb hX
  obtain ⟨I⟩ := DE2Hyp.nonempty_aeIdentOn_e64 hA
  have hgen : pSpan Ω' = ⊤ := hA.gen
  have hTmem : ∀ y : ↥(pSpan X), y ∈ pSpan Ω' := fun y => by
    rw [hgen]
    exact Subgroup.mem_top y
  have hιinj : Function.Injective ((pSpan X).subtype.comp (pSpan Ω').subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hφinj : Function.Injective I.φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center ↥(pSpan Ω') := I.ker_le (MonoidHom.mem_ker.mpr hx)
    have hxG : x.1 ∈ Subgroup.center ↥(pSpan X) := by
      rw [Subgroup.mem_center_iff] at hxc ⊢
      intro g
      have h2 := congrArg Subtype.val (hxc ⟨g, hTmem g⟩)
      simpa using h2
    rw [hA.center, Subgroup.mem_bot] at hxG
    exact Subtype.ext hxG
  set ιT : ↥(pSpan Ω') →* G := (pSpan X).subtype.comp (pSpan Ω').subtype with hιT
  have hιinj' : Function.Injective ιT := hιinj
  have hAK_map : ∀ K ∈ X, ((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')).map ιT = K := by
    intro K hK
    have hKP : K ≤ pSpan X := le_pSpan hK
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
    · intro hg
      refine ⟨⟨⟨g, hKP hg⟩, hTmem ⟨g, hKP hg⟩⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hg)
  set Mm : Subgroup (AE.AEQ 7) := AE.l32.map dewp2_Ph with hMm
  have hMle : Mm ≤ AE.e64Sub := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact dewp2_Ph_mem_e64 hσ
  have hmemBar_le : ∀ α ∈ AE.e64Sets, ∀ (hα : α.card = 4) (c : Bool),
      AE.memBar α hα c ≤ AE.e64Sub := by
    intro α hαmem hα c
    obtain ⟨L₀, _, hL₀⟩ := I.label_surj α hαmem hα c
    have hle : AE.memBar α hα c ≤ I.φ.range := by
      rw [← hL₀]
      rintro _ ⟨x, _, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rw [I.range_eq] at hle
    exact hle
  have hlabel : ∀ K ∈ X, ∃ α ∈ AE.e64Sets, ∃ (hα : α.card = 4) (c : Bool),
      ((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')).map I.φ = AE.memBar α hα c := by
    intro K hK
    have hmem : K.subgroupOf (pSpan X) ∈ Ω' := by
      rw [hΩ']
      exact ⟨K, hK, rfl⟩
    obtain ⟨α, hαmem, hα, c, hc⟩ := I.label _ hmem
    exact ⟨α, hαmem, hα, c, hc⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup G, L = (Mm.comap I.φ).map ιT := ⟨_, rfl⟩
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · rw [hLdef]
    rintro _ ⟨x, _, rfl⟩
    exact x.1.2
  · rw [hLdef, Subgroup.card_map_of_injective hιinj']
    have h2 : Nat.card ↥((Mm.comap I.φ).map I.φ) = Nat.card ↥(Mm.comap I.φ) :=
      Subgroup.card_map_of_injective hφinj
    rw [Subgroup.map_comap_eq, I.range_eq, inf_eq_right.mpr hMle] at h2
    rw [← h2]
    exact dewp2_card_M
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgL, hgA⟩ := Subgroup.mem_inf.mp hg
    rw [hLdef] at hgL
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgL
    rw [Subgroup.mem_comap] at hx
    obtain ⟨σ, hσ, hσx⟩ := Subgroup.mem_map.mp hx
    have hcomm : ∀ ℓ ∈ AE.fanoLines, ∀ y, σ y ∈ ℓ → y ∈ ℓ := by
      intro ℓ hℓ y hy
      by_contra hyℓ
      have hαmem : ℓᶜ ∈ AE.e64Sets := ⟨ℓ, hℓ, rfl⟩
      have hcard : (ℓᶜ).card = 4 := AE.fanoLines_compl_card ℓ hℓ
      obtain ⟨L₀, hL₀mem, hL₀⟩ := I.label_surj (ℓᶜ) hαmem hcard true
      rw [hΩ'] at hL₀mem
      obtain ⟨K₀, hK₀, rfl⟩ := hL₀mem
      obtain ⟨_, z₀, hz₀, hz₀'⟩ := S.shift_mem b K₀ (hXΩ K₀ hK₀)
      have hw₀mem : (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) ∈
          (K₀.subgroupOf (pSpan X)).subgroupOf (pSpan Ω') :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hz₀.mem)
      have hw₀1 : (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) ≠ 1 := by
        intro h1
        apply hz₀.ne_one
        have := congrArg ιT h1
        exact this
      have hw₀2 : (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) *
          (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) = 1 := by
        apply hιinj'
        rw [map_mul, map_one]
        exact hz₀.sq
      have hφw₀ := dewp2_phi_involution hφinj hL₀ hw₀mem hw₀1 hw₀2
      have hconj := dewp2_conj_involution S (hXΩ K₀ hK₀) hz₀ hz₀' hgA
      have hcommG : ιT x * z₀ = z₀ * ιT x := by
        calc ιT x * z₀ = (ιT x * z₀ * (ιT x)⁻¹) * ιT x := by group
          _ = z₀ * ιT x := by rw [hconj]
      have hxw : x * (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) =
          (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) * x :=
        hιinj' (by rw [map_mul, map_mul]; exact hcommG)
      have hφcomm : I.φ x * I.φ (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) =
          I.φ (⟨⟨z₀, le_pSpan hK₀ hz₀.mem⟩, hTmem _⟩ : ↥(pSpan Ω')) * I.φ x := by
        rw [← map_mul, ← map_mul, hxw]
      rw [← hσx, hφw₀] at hφcomm
      have hst := dewp2_sigma_stab hcard hφcomm y (Finset.mem_compl.mpr hyℓ)
      exact (Finset.mem_compl.mp hst) hy
    have hσ1 : σ = 1 := dewp2_eq_one_of_lines hcomm
    rw [hσ1, map_one] at hσx
    have hx1 : x = 1 := hφinj (by rw [map_one]; exact hσx.symm)
    rw [hx1, map_one, Subgroup.mem_bot]
  · intro K hK
    have hK' : S.shift b K ∈ X := hXsh K hK
    obtain ⟨α, hαmem, hα, c₁, hlab₁⟩ := hlabel K hK
    obtain ⟨α', hα'mem, hα', c₂, hlab₂⟩ := hlabel (S.shift b K) hK'
    obtain ⟨_, z, hzK, hzK'⟩ := S.shift_mem b K (hXΩ K hK)
    have hzX : z ∈ pSpan X := le_pSpan hK hzK.mem
    have hwA : (⟨⟨z, hzX⟩, hTmem _⟩ : ↥(pSpan Ω')) ∈
        (K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω') :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hzK.mem)
    have hwA' : (⟨⟨z, hzX⟩, hTmem _⟩ : ↥(pSpan Ω')) ∈
        ((S.shift b K).subgroupOf (pSpan X)).subgroupOf (pSpan Ω') :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hzK'.mem)
    have hw1 : (⟨⟨z, hzX⟩, hTmem _⟩ : ↥(pSpan Ω')) ≠ 1 := by
      intro h1
      apply hzK.ne_one
      have := congrArg ιT h1
      exact this
    have hw2 : (⟨⟨z, hzX⟩, hTmem _⟩ : ↥(pSpan Ω')) * (⟨⟨z, hzX⟩, hTmem _⟩ : ↥(pSpan Ω')) = 1 := by
      apply hιinj'
      rw [map_mul, map_one]
      exact hzK.sq
    have hαα' : α = α' := dewp2_alpha_eq hφinj hlab₁ hlab₂ hwA hwA' hw1 hw2
    subst hαα'
    have hc : c₁ ≠ c₂ := by
      intro hc
      subst hc
      have hAeq := Subgroup.map_injective hφinj (hlab₁.trans hlab₂.symm)
      have hKeq : K = S.shift b K := by
        have h3 := congrArg (Subgroup.map ιT) hAeq
        rwa [hAK_map K hK, hAK_map _ hK'] at h3
      exact hb ((S.shift_free b K (hXΩ K hK)) hKeq.symm)
    have hKK : K ⊔ S.shift b K =
        (((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')) ⊔
          (((S.shift b K).subgroupOf (pSpan X)).subgroupOf (pSpan Ω'))).map ιT := by
      rw [Subgroup.map_sup, hAK_map K hK, hAK_map _ hK']
    have hmain : L ⊓ (K ⊔ S.shift b K) =
        ((Mm.comap I.φ) ⊓ (((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')) ⊔
          (((S.shift b K).subgroupOf (pSpan X)).subgroupOf (pSpan Ω')))).map ιT := by
      rw [hLdef, hKK, ← Subgroup.map_inf_eq _ _ ιT hιinj']
    rw [hmain, Subgroup.card_map_of_injective hιinj']
    have hφcard : Nat.card ↥((Mm.comap I.φ) ⊓ (((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')) ⊔
          (((S.shift b K).subgroupOf (pSpan X)).subgroupOf (pSpan Ω')))) =
        Nat.card ↥(((Mm.comap I.φ) ⊓ (((K.subgroupOf (pSpan X)).subgroupOf (pSpan Ω')) ⊔
          (((S.shift b K).subgroupOf (pSpan X)).subgroupOf (pSpan Ω')))).map I.φ) :=
      (Subgroup.card_map_of_injective hφinj).symm
    rw [hφcard, Subgroup.map_inf_eq _ _ I.φ hφinj, Subgroup.map_comap_eq, I.range_eq,
      inf_eq_right.mpr hMle, Subgroup.map_sup, hlab₁, hlab₂]
    cases c₁ <;> cases c₂
    · exact absurd rfl hc
    · rw [sup_comm]
      exact dewp2_count hα (hmemBar_le α hαmem hα true) (hmemBar_le α hαmem hα false)
    · exact dewp2_count hα (hmemBar_le α hαmem hα true) (hmemBar_le α hαmem hα false)
    · exact absurd rfl hc

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Red
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsL33
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Sylow

public section

namespace CFSG.QuasithinUnique.Unc25L33

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.QuasithinUnique.Unc25Small
  CFSG.QuasithinUnique.Unc25K1 CFSG.Sporadic.Schreier

theorem rr_pow (x : S3) (n : ℕ) : rr (x ^ n) = rpw (rr x) n := by
  induction n with
  | zero => rw [pow_zero, rr_one]; rfl
  | succ n ih => rw [pow_succ', rr_mul, ih]; rfl

theorem rpw_mem {x : R9} (hx : x ∈ P0R) (n : ℕ) : rpw x n ∈ P0R := by
  induction n with
  | zero => exact rone_mem_P0R
  | succ n ih => exact mul_mem_P0R x hx _ ih

@[expose] def ga : S3 := ofR9 sa sa_det

@[expose] def gb : S3 := ofR9 sb sb_det

theorem rr_ga : rr ga = sa := rr_ofR9 _ _

theorem rr_gb : rr gb = sb := rr_ofR9 _ _

theorem rr_word
    (i j : ℕ) : rr (ga ^ i * gb ^ j) = rmul (rpw sa i) (rpw sb j) := by
  rw [rr_mul, rr_pow, rr_pow, rr_ga, rr_gb]

@[expose] def P0 : Subgroup S3 where
  carrier := {x | rr x ∈ P0R}
  one_mem' := show rr 1 ∈ P0R by rw [rr_one]; exact rone_mem_P0R
  mul_mem' := fun {x y} (hx : rr x ∈ P0R) (hy : rr y ∈ P0R) =>
    show rr (x * y) ∈ P0R by rw [rr_mul]; exact mul_mem_P0R _ hx _ hy
  inv_mem' := fun {x} (hx : rr x ∈ P0R) => by
    have h16 : x ^ 16 = 1 := rr_inj (by rw [rr_pow, rr_one]; exact pow16_check _ hx)
    have hinv : x⁻¹ = x ^ 15 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      exact h16
    show rr x⁻¹ ∈ P0R
    rw [hinv, rr_pow]
    exact rpw_mem hx 15

theorem mem_P0 {x : S3} : x ∈ P0 ↔ rr x ∈ P0R := Iff.rfl

theorem exists_word_of_mem_P0
    {x : S3} (hx : x ∈ P0) : ∃ i j : ℕ, x = ga ^ i * gb ^ j := by
  obtain ⟨i, -, j, -, h⟩ := mem_P0R_iff.mp (mem_P0.mp hx)
  exact ⟨i, j, rr_inj (by rw [rr_word]; exact h)⟩

theorem ga_mem
    : ga ∈ P0 := mem_P0.mpr (by rw [rr_ga]; exact sa_mem_P0R)

theorem gb_mem
    : gb ∈ P0 := mem_P0.mpr (by rw [rr_gb]; exact sb_mem_P0R)

theorem exists_mem_of_mem_P0R
    {b : R9} (hb : b ∈ P0R) : ∃ a : S3, a ∈ P0 ∧ rr a = b := by
  obtain ⟨i, -, j, -, rfl⟩ := mem_P0R_iff.mp hb
  exact ⟨ga ^ i * gb ^ j, mem_P0.mpr (by rw [rr_word]; exact hb), rr_word i j⟩

theorem card_P0 : Nat.card P0 = 16 := by
  have h := card_eq_length (fun x : S3 => x ∈ P0) rr rr_inj P0R P0R_nodup (fun b =>
    ⟨fun hb => exists_mem_of_mem_P0R hb, fun ⟨a, ha, hab⟩ => hab ▸ mem_P0.mp ha⟩)
  rw [P0R_length] at h
  exact h

theorem isSylowTwoOf_P0 :
    IsSylowTwoOf P0 ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold IsSylowTwoOf
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card_P0]; norm_num), ?_⟩
  have hmul := Subgroup.card_mul_index P0
  rw [card_P0, card_S3] at hmul
  have h351 : P0.index = 351 := by omega
  have hrel : (P0.subgroupOf ⊤).index = P0.index := Subgroup.relIndex_top_right P0
  rw [hrel, h351]
  decide

@[expose] def a0 : ↥P0 := ⟨ga, ga_mem⟩

@[expose] def b0 : ↥P0 := ⟨gb, gb_mem⟩

theorem a0_pow : a0 ^ 8 = 1 := by
  apply Subtype.ext
  apply rr_inj
  show rr ((ga ^ 8 : S3)) = rr 1
  rw [rr_pow, rr_ga, rr_one]
  exact sa_pow

theorem gb_mul_self
    : gb * gb = 1 := rr_inj (by rw [rr_mul, rr_gb, rr_one]; exact sb_sq)

theorem b0_sq : b0 ^ 2 = 1 := by
  apply Subtype.ext
  show gb ^ 2 = 1
  rw [pow_two]
  exact gb_mul_self

theorem gb_conj : gb * ga * gb⁻¹ = ga ^ 3 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply rr_inj
  rw [rr_mul, rr_mul, rr_pow, rr_ga, rr_gb]
  exact sb_conj

theorem b0_conj : b0 * a0 * b0⁻¹ = a0 ^ 3 := by
  apply Subtype.ext
  exact gb_conj

theorem shape_P0 : Nonempty (↥P0 ≃* SemidihedralGroup 4) := by
  refine nonempty_mulEquiv_semidihedral a0 b0 a0_pow b0_sq b0_conj (fun x => ?_)
    (le_of_eq card_P0.symm)
  obtain ⟨i, j, hx⟩ := exists_word_of_mem_P0 x.2
  exact ⟨i, j, Subtype.ext (hx.trans (by simp [a0, b0]))⟩

theorem normalizer_le_P0
    : Subgroup.normalizer (P0 : Set S3) ≤ P0 := by
  intro g hg
  have h1 : g * ga * g⁻¹ ∈ P0 := (Subgroup.mem_normalizer_iff.mp hg ga).mp ga_mem
  have h2 : g * gb * g⁻¹ ∈ P0 := (Subgroup.mem_normalizer_iff.mp hg gb).mp gb_mem
  refine mem_P0.mpr (normProp_check (rr g) (rr_mem g) ⟨rr (g * ga * g⁻¹), mem_P0.mp h1, ?_⟩
    ⟨rr (g * gb * g⁻¹), mem_P0.mp h2, ?_⟩)
  · have : g * ga * g⁻¹ * g = g * ga := by group
    rw [← rr_ga, ← rr_mul, ← rr_mul, this]
  · have : g * gb * g⁻¹ * g = g * gb := by group
    rw [← rr_gb, ← rr_mul, ← rr_mul, this]

theorem rr_mem_invsP0 {x : S3} (hx1 : x ≠ 1) (hx2 : x * x = 1) (hxP : rr x ∈ P0R) :
    rr x ∈ invsP0 := by
  unfold invsP0
  rw [List.mem_filter]
  refine ⟨hxP, ?_⟩
  have h1 : rr x ≠ rone := fun h => hx1 (rr_inj (by rw [h, rr_one]))
  have h2 : rmul (rr x) (rr x) = rone := by rw [← rr_mul, hx2, rr_one]
  simp [h1, h2]

theorem four_P0 : ∀ F : Subgroup S3, F ≤ P0 → IsFourSubgroup F →
    Subgroup.centralizer (F : Set S3) = F ∧
      ∃ w ∈ Subgroup.normalizer (F : Set S3), orderOf w = 3 := by
  intro F hFP hF
  obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, rfl⟩ := exists_kleinFour_gens hF
  have hmem := Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht hs hc
  have htF : t ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem t).mpr (Or.inr (Or.inl rfl))
  have hsF : s ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have htP : rr t ∈ P0R := mem_P0.mp (hFP htF)
  have hsP : rr s ∈ P0R := mem_P0.mp (hFP hsF)
  have htI := rr_mem_invsP0 ht1 ht htP
  have hsI := rr_mem_invsP0 hs1 hs hsP
  have hne : rr t ≠ rr s := fun h => hts (rr_inj h)
  have hcomm : rmul (rr t) (rr s) = rmul (rr s) (rr t) := by rw [← rr_mul, ← rr_mul, hc.eq]
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro g hg
      have hgt : g * t = t * g := (Subgroup.mem_centralizer_iff.mp hg t htF).symm
      have hgs : g * s = s * g := (Subgroup.mem_centralizer_iff.mp hg s hsF).symm
      have key := centProp_check (rr g) (rr_mem g) (rr t) htI (rr s) hsI
        (by rw [← rr_mul, ← rr_mul, hgt]) (by rw [← rr_mul, ← rr_mul, hgs]) hne hcomm
      rw [hmem]
      rcases key with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (rr_inj (by rw [h, rr_one]))))
      · exact Or.inr (Or.inl (rr_inj h))
      · exact Or.inr (Or.inr (Or.inl (rr_inj h)))
      · exact Or.inl (rr_inj (by rw [h, rr_mul]))
    · intro f hf
      have := hF.1.1
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact setLike_mul_comm hg hf
  · obtain ⟨w, hwW, hw3, hw1, ⟨u1, hu1, hwt⟩, ⟨u2, hu2, hws⟩⟩ := W3_check _ htI _ hsI hne hcomm
    obtain ⟨W, hWval⟩ : ∃ W : S3, rr W = w := ⟨ofR9 w (W3_det w hwW), rr_ofR9 _ _⟩
    have hlist : ∀ u : R9, u ∈ [rone, rr t, rr s, rmul (rr t) (rr s)] →
        ∃ x ∈ kleinFourOfCommutingInvolutions t s ht hs hc, rr x = u := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, rr_one⟩
      · exact ⟨t, htF, rfl⟩
      · exact ⟨s, hsF, rfl⟩
      · exact ⟨t * s, Subgroup.mul_mem _ htF hsF, rr_mul t s⟩
    have hconj : ∀ f : S3, ∀ u : R9, u ∈ [rone, rr t, rr s, rmul (rr t) (rr s)] →
        rmul w (rr f) = rmul u w → W * f * W⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc := by
      intro f u hu hfu
      obtain ⟨x, hx, rfl⟩ := hlist u hu
      have : W * f = x * W := by
        apply rr_inj
        rw [rr_mul, rr_mul, hWval]
        exact hfu
      rw [mul_inv_eq_iff_eq_mul.mpr this]
      exact hx
    have hWt : W * t * W⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      hconj t u1 hu1 hwt
    have hWs : W * s * W⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      hconj s u2 hu2 hws
    have hnorm : W ∈ Subgroup.normalizer
        ((kleinFourOfCommutingInvolutions t s ht hs hc : Subgroup S3) : Set S3) := by
      refine mem_normalizer_of_conj_le fun f hf => ?_
      rw [hmem] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · have : W * (t * s) * W⁻¹ = (W * t * W⁻¹) * (W * s * W⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hWt hWs
      · exact hWt
      · exact hWs
      · rw [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
    have hW3 : W ^ 3 = 1 := by
      apply rr_inj
      rw [rr_pow, rr_one, hWval]
      exact hw3
    have hW1 : W ≠ 1 := fun h => hw1 (by rw [← hWval, h, rr_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨W, hnorm, orderOf_eq_prime hW3 hW1⟩

theorem sylowFourData_P0 :
    SylowFourData P0 :=
  { sylow := isSylowTwoOf_P0
    shape := Or.inr shape_P0
    normalizer_le := normalizer_le_P0
    four := four_P0 }

theorem rr_tauAut (x : S3) : rr (tauAut x) = rcof (rr x) := rr_tauFun x

theorem outer_fix_iff (g f : S3) :
    (MulAut.conj g * tauAut) f = f ↔ rmul (rr g) (rcof (rr f)) = rmul (rr f) (rr g) := by
  have h : (MulAut.conj g * tauAut) f = g * tauAut f * g⁻¹ := rfl
  rw [h, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h1
    have h2 := congrArg rr h1
    rw [rr_mul, rr_mul, rr_tauAut] at h2
    exact h2
  · intro h1
    apply rr_inj
    rw [rr_mul, rr_mul, rr_tauAut]
    exact h1

theorem outer_apply_mem
    {g x : S3} (hx : ∃ p ∈ P0R, rmul (rr g) (rcof (rr x)) = rmul p (rr g)) :
    (MulAut.conj g * tauAut) x ∈ P0 := by
  obtain ⟨p, hp, hpe⟩ := hx
  obtain ⟨q, hq, hqp⟩ := exists_mem_of_mem_P0R hp
  have h1 : g * tauAut x = q * g := by
    apply rr_inj
    rw [rr_mul, rr_mul, rr_tauAut, hqp]
    exact hpe
  have h2 : (MulAut.conj g * tauAut) x = q := by
    show g * tauAut x * g⁻¹ = q
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  rw [h2]
  exact hq

theorem map_le_of_gens
    {φ : MulAut S3} (ha : φ ga ∈ P0) (hb : φ gb ∈ P0) :
    ∀ p ∈ P0, φ p ∈ P0 := by
  intro p hp
  obtain ⟨i, j, rfl⟩ := exists_word_of_mem_P0 hp
  rw [map_mul, map_pow, map_pow]
  exact P0.mul_mem (P0.pow_mem ha i) (P0.pow_mem hb j)

theorem s3_fixes_P0
    (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) :
    ∀ F : Subgroup S3, F ≤ P0 → IsFourSubgroup F → ∀ φ : MulAut S3, (∀ f ∈ F, φ f = f) →
      ∀ y, φ y ∈ P0 ↔ y ∈ P0 := by
  intro F hFP hF φ hφ
  obtain ⟨g, hg | hg⟩ := aut_cases hb φ
  · have hgC : g ∈ Subgroup.centralizer (F : Set S3) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : g * f * g⁻¹ = f := by
        have := hφ f hf
        rw [hg] at this
        exact this
      calc f * g = (g * f * g⁻¹) * g := by rw [h1]
        _ = g * f := by group
    rw [(four_P0 F hFP hF).1] at hgC
    have hgP : g ∈ P0 := hFP hgC
    apply mem_iff_of_map_le
    intro p hp
    rw [hg]
    show g * p * g⁻¹ ∈ P0
    exact P0.mul_mem (P0.mul_mem hgP hp) (P0.inv_mem hgP)
  · obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, rfl⟩ := exists_kleinFour_gens hF
    have hmem := Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht hs hc
    have htF : t ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      (hmem t).mpr (Or.inr (Or.inl rfl))
    have hsF : s ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      (hmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have htI := rr_mem_invsP0 ht1 ht (mem_P0.mp (hFP htF))
    have hsI := rr_mem_invsP0 hs1 hs (mem_P0.mp (hFP hsF))
    have hne : rr t ≠ rr s := fun h => hts (rr_inj h)
    have hcomm : rmul (rr t) (rr s) = rmul (rr s) (rr t) := by rw [← rr_mul, ← rr_mul, hc.eq]
    rw [hg] at hφ
    have h1 := (outer_fix_iff g t).mp (hφ t htF)
    have h2 := (outer_fix_iff g s).mp (hφ s hsF)
    obtain ⟨hp1, hp2⟩ := fixProp_check (rr g) (rr_mem g) (rr t) htI (rr s) hsI h1 h2 hne hcomm
    rw [← rr_ga] at hp1
    rw [← rr_gb] at hp2
    rw [hg]
    exact mem_iff_of_map_le _ (map_le_of_gens (outer_apply_mem hp1) (outer_apply_mem hp2))

theorem s3_fixPointwiseInner_P0
    (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) :
    ∀ α : MulAut S3, (∀ y ∈ P0, α y = y) → α ∈ innerAut S3 := by
  intro α hα
  obtain ⟨g, hg | hg⟩ := aut_cases hb α
  · exact ⟨g, hg.symm⟩
  · exfalso
    rw [hg] at hα
    have h1 := (outer_fix_iff g ga).mp (hα ga ga_mem)
    have h2 := (outer_fix_iff g gb).mp (hα gb gb_mem)
    rw [rr_ga] at h1
    rw [rr_gb] at h2
    exact noFix_check (rr g) (rr_mem g) ⟨h1, h2⟩

theorem s3_smallListFacts
    (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) (hS : IsSimpleGroup S3) :
    SmallListFacts S3 :=
  { simple := hS
    out_two := fun φ => by
      obtain ⟨g, hg | hg⟩ := aut_cases hb φ
      · exact ⟨0, by rw [pow_zero, pow_one]; exact ⟨g, hg.symm⟩⟩
      · refine ⟨1, ?_⟩
        rw [pow_one, pow_two, hg, sq_conj_tau tauAut tau_tau g]
        exact ⟨g * tauAut g, rfl⟩
    sylow_shape := sylowFourData_P0.sylow_shape
    sylow_normalizer := sylowFourData_P0.sylow_normalizer
    four_normalizer := fun _ hF => sylowFourData_P0.four_normalizer hF
    four_fixes := four_fixes_of_sylow isSylowTwoOf_P0 (s3_fixes_P0 hb) }

theorem s3_fixPointwiseInner
    (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) :
    FixPointwiseInner S3 :=
  fixPointwiseInner_of_sylow isSylowTwoOf_P0 (s3_fixPointwiseInner_P0 hb)

theorem l33_facts
    (X : Type) [Group X] [Finite X] (h : StatedClassicalModel X .PSL 3 3 1) :
    SmallListFacts X ∧ FixPointwiseInner X := by
  obtain ⟨e₀⟩ := psl33_equiv h
  let e : X ≃* S3 := e₀.trans psl33EquivS3
  have hS : IsSimpleGroup S3 := by
    have := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 3 1 h).2
    exact e.symm.isSimpleGroup
  have hb := aut_card_S3 e (aut_card_le h)
  exact ⟨SmallListFacts.of_mulEquiv e (s3_smallListFacts hb hS),
    FixPointwiseInner.of_mulEquiv e (s3_fixPointwiseInner hb)⟩

end CFSG.QuasithinUnique.Unc25L33

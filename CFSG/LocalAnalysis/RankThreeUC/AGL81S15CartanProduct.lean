module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankQuotient
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open CFSG.Open

theorem pRank_quotient_le_of_commutative {A : Type} [Group A] [Finite A] {q : ℕ}
    (hq : q.Prime) (hcomm : ∀ a b : A, a * b = b * a) (M : Subgroup A) [M.Normal] :
    CFSG.Open.pRank q (⊤ : Subgroup (A ⧸ M)) ≤ CFSG.Open.pRank q (⊤ : Subgroup A) := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  let f : A →* A := powMonoidHom q
  let g : A ⧸ M →* A ⧸ M := powMonoidHom q
  have hK : CFSG.Open.IsElemAbelian q f.ker := by
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : A) (b : A))⟩⟩, ?_⟩
    intro x hx
    simpa [f] using hx
  have hK' : CFSG.Open.IsElemAbelian q g.ker := by
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : A ⧸ M) (b : A ⧸ M))⟩⟩, ?_⟩
    intro x hx
    simpa [g] using hx
  have hrankK : CFSG.Open.pRank q f.ker = CFSG.Open.pRank q (⊤ : Subgroup A) := by
    refine le_antisymm (CFSG.SectionRank.pRank_mono hq.one_lt le_top) ?_
    obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup A)
    have hEK : E ≤ f.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      simpa [f] using hE.2 x hx
    exact CFSG.SectionRank.le_pRank hq.one_lt hEK hE hEcard
  have hrankK' : CFSG.Open.pRank q g.ker = CFSG.Open.pRank q (⊤ : Subgroup (A ⧸ M)) := by
    refine le_antisymm (CFSG.SectionRank.pRank_mono hq.one_lt le_top) ?_
    obtain ⟨E, -, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup (A ⧸ M))
    have hEK : E ≤ g.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      simpa [g] using hE.2 x hx
    exact CFSG.SectionRank.le_pRank hq.one_lt hEK hE hEcard
  have hcardK : Nat.card f.ker = q ^ CFSG.Open.pRank q (⊤ : Subgroup A) := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hq hK, hrankK]
  have hcardK' : Nat.card g.ker = q ^ CFSG.Open.pRank q (⊤ : Subgroup (A ⧸ M)) := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hq hK', hrankK']
  let R : Subgroup A := f.range
  let R' : Subgroup (A ⧸ M) := g.range
  have hR' : R' = R.map (QuotientGroup.mk' M) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective M x
      refine Subgroup.mem_map.mpr ⟨a ^ q, ⟨a, rfl⟩, ?_⟩
      change (QuotientGroup.mk' M a) ^ q = QuotientGroup.mk' M (a ^ q)
      rw [map_pow]
    · rintro ⟨r, ⟨a, rfl⟩, rfl⟩
      refine ⟨QuotientGroup.mk' M a, ?_⟩
      change (QuotientGroup.mk' M a) ^ q = QuotientGroup.mk' M (a ^ q)
      rw [map_pow]
  have hA : Nat.card f.ker * Nat.card R = Nat.card A :=
    Subgroup.card_ker_mul_card_range f
  have hQ : Nat.card g.ker * Nat.card R' = Nat.card (A ⧸ M) :=
    Subgroup.card_ker_mul_card_range g
  have hQM : Nat.card (A ⧸ M) * Nat.card M = Nat.card A := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_mul_card (H := M)
  let ψ : R →* (A ⧸ M) := (QuotientGroup.mk' M).comp R.subtype
  have hψrange : ψ.range = R' := by
    rw [show ψ.range = R.map (QuotientGroup.mk' M) from ?_, hR']
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have hψker : ψ.ker = (M ⊓ R).subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨(QuotientGroup.eq_one_iff (x : A)).mp hx, x.2⟩
    · rintro ⟨hxM, -⟩
      exact (QuotientGroup.eq_one_iff (x : A)).mpr hxM
  have hψkercard : Nat.card ψ.ker = Nat.card ↥(M ⊓ R) := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hRcard : Nat.card ↥(M ⊓ R) * Nat.card R' = Nat.card R := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rwa [hψkercard, hψrange] at h
  have hCombine : Nat.card f.ker * (Nat.card ↥(M ⊓ R) * Nat.card R') =
      (Nat.card g.ker * Nat.card R') * Nat.card M := by
    calc Nat.card f.ker * (Nat.card ↥(M ⊓ R) * Nat.card R')
        = Nat.card f.ker * Nat.card R := by rw [hRcard]
      _ = Nat.card A := hA
      _ = Nat.card (A ⧸ M) * Nat.card M := hQM.symm
      _ = (Nat.card g.ker * Nat.card R') * Nat.card M := by rw [hQ]
  have hCancel : Nat.card f.ker * Nat.card ↥(M ⊓ R) = Nat.card g.ker * Nat.card M := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := R'))
    calc (Nat.card f.ker * Nat.card ↥(M ⊓ R)) * Nat.card R'
        = Nat.card f.ker * (Nat.card ↥(M ⊓ R) * Nat.card R') := by rw [mul_assoc]
      _ = (Nat.card g.ker * Nat.card R') * Nat.card M := hCombine
      _ = (Nat.card g.ker * Nat.card M) * Nat.card R' := by ring
  have hRinf : Nat.card ↥(M ⊓ R) ≤ Nat.card M := Subgroup.card_le_of_le inf_le_left
  have hle : Nat.card g.ker * Nat.card M ≤ Nat.card f.ker * Nat.card M := by
    rw [← hCancel]
    exact Nat.mul_le_mul_left _ hRinf
  have hkerle : Nat.card g.ker ≤ Nat.card f.ker :=
    Nat.le_of_mul_le_mul_right hle (Nat.card_pos (α := M))
  rw [hcardK', hcardK] at hkerle
  exact (Nat.pow_le_pow_iff_right hq.one_lt).1 hkerle

theorem one_lt_mS_of_cartan_product {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {H C N : Subgroup (X ⧸ gnC T)} {q : ℕ} (hq : q.Prime)
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hsup : H = C ⊔ N)
    (hC : C ≤ gnA T T₁ Ls) (hN : N ≤ gnA T T₂ Ls)
    (h3 : 3 ≤ CFSG.Open.pRank q H) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  have hCH : C ≤ H := by rw [hsup]; exact le_sup_left
  have hNH : N ≤ H := by rw [hsup]; exact le_sup_right
  letI : CommGroup ↥H :=
    { (inferInstance : Group ↥H) with
      mul_comm := fun a b => Subtype.ext (hHcomm a a.2 b b.2) }
  let CH : Subgroup ↥H := C.subgroupOf H
  let NH : Subgroup ↥H := N.subgroupOf H
  have hsupH : CH ⊔ NH = ⊤ := by
    calc CH ⊔ NH = (C ⊔ N).subgroupOf H := (Subgroup.subgroupOf_sup hCH hNH).symm
      _ = H.subgroupOf H := by rw [← hsup]
      _ = ⊤ := Subgroup.subgroupOf_self H
  let φ : CH →* (↥H ⧸ NH) := (QuotientGroup.mk' NH).comp CH.subtype
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective NH y
    have hx : x ∈ CH ⊔ NH := by rw [hsupH]; exact Subgroup.mem_top x
    obtain ⟨c, hc, n, hn, hcn⟩ := (Subgroup.mem_sup).1 hx
    refine ⟨⟨c, hc⟩, ?_⟩
    have hn1 : QuotientGroup.mk' NH n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show QuotientGroup.mk' NH c = QuotientGroup.mk' NH x
    calc QuotientGroup.mk' NH c = QuotientGroup.mk' NH c * QuotientGroup.mk' NH n := by
          rw [hn1, mul_one]
      _ = QuotientGroup.mk' NH (c * n) := by rw [map_mul]
      _ = QuotientGroup.mk' NH x := by rw [hcn]
  have hφker : φ.ker = NH.subgroupOf CH := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' NH (x : ↥H) = 1 ↔ (x : ↥H) ∈ NH
    exact QuotientGroup.eq_one_iff (x : ↥H)
  let e : CH ⧸ φ.ker ≃* (↥H ⧸ NH) :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  have hcommCH : ∀ a b : CH, a * b = b * a := fun a b => mul_comm a b
  have hquotRank : CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ NH)) ≤ CFSG.Open.pRank q C := by
    have h1 : CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ NH)) =
        CFSG.Open.pRank q (⊤ : Subgroup (CH ⧸ φ.ker)) :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e).symm
    rw [h1]
    have h2 := pRank_quotient_le_of_commutative (A := CH) hq hcommCH φ.ker
    have hCHrank : CFSG.Open.pRank q (⊤ : Subgroup CH) = CFSG.Open.pRank q C :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt
        (Subgroup.subgroupOfEquivOfLe hCH)).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C).symm
    exact h2.trans_eq hCHrank
  have hsub := CFSG.HardMathSupport.Timmesfeld.Proving.pRank_le_pRank_inf_add_pRank_map
    (G := ↥H) (p := q) hq (⊤ : Subgroup ↥H) NH
  have hsub' : CFSG.Open.pRank q (⊤ : Subgroup ↥H) ≤
      CFSG.Open.pRank q NH +
        CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ NH)) := by
    have hmap : (⊤ : Subgroup ↥H).map (QuotientGroup.mk' NH) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective NH)
    simpa [hmap] using hsub
  have hHrank : CFSG.Open.pRank q (⊤ : Subgroup ↥H) = CFSG.Open.pRank q H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  have hNHrank : CFSG.Open.pRank q NH = CFSG.Open.pRank q N := by
    calc CFSG.Open.pRank q NH = CFSG.Open.pRank q (⊤ : Subgroup NH) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup NH
      _ = CFSG.Open.pRank q (⊤ : Subgroup ↥N) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt
            (Subgroup.subgroupOfEquivOfLe hNH)
      _ = CFSG.Open.pRank q N := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup N).symm
  have hmain : CFSG.Open.pRank q H ≤ CFSG.Open.pRank q N + CFSG.Open.pRank q C := by
    calc CFSG.Open.pRank q H = CFSG.Open.pRank q (⊤ : Subgroup ↥H) := hHrank.symm
      _ ≤ CFSG.Open.pRank q NH + CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ NH)) := hsub'
      _ = CFSG.Open.pRank q N + CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ NH)) := by
            rw [hNHrank]
      _ ≤ CFSG.Open.pRank q N + CFSG.Open.pRank q C := add_le_add_right hquotRank _
  have hCmS : CFSG.Open.pRank q C ≤ mS T T₁ q Ls :=
    CFSG.SectionRank.pRank_mono hq.one_lt hC
  have hNmS : CFSG.Open.pRank q N ≤ mS T T₂ q Ls :=
    CFSG.SectionRank.pRank_mono hq.one_lt hN
  have hsum : 3 ≤ mS T T₂ q Ls + mS T T₁ q Ls :=
    le_trans (le_trans h3 hmain) (add_le_add hNmS hCmS)
  by_contra h
  push Not at h
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveAux
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscEightFive

open AscEightFour

section PerfectQuot

theorem eq_top_of_perfect_of_isSolvable {P : Type*} [Group P] (hP : commutator P = ⊤)
    (N : Subgroup P) [N.Normal] (hs : Group.IsSolvable (P ⧸ N)) : N = ⊤ := by
  have hc : commutator (P ⧸ N) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      ← Subgroup.map_commutator, ← commutator_def, hP]
  have hd : ∀ k, derivedSeries (P ⧸ N) k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
  obtain ⟨k, hk⟩ := (Group.isSolvable_def _).mp hs
  have htb : (⊤ : Subgroup (P ⧸ N)) = ⊥ := (hd k).symm.trans hk
  rw [eq_top_iff]
  intro x _
  have hx : (x : P ⧸ N) ∈ (⊥ : Subgroup (P ⧸ N)) := htb ▸ Subgroup.mem_top _
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hx)

theorem eq_top_of_perfect_of_odd_index {P : Type*} [Group P] [Finite P] (hP : commutator P = ⊤)
    (N : Subgroup P) [N.Normal] (hodd : ¬ 2 ∣ N.index) : N = ⊤ := by
  refine eq_top_of_perfect_of_isSolvable hP N ?_
  have : Odd (Nat.card (P ⧸ N)) := by
    rw [← Subgroup.index]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ this

theorem eq_top_of_perfect_of_isPGroup {P : Type*} [Group P] [Finite P] (hP : commutator P = ⊤)
    (N : Subgroup P) [N.Normal] (h2 : IsPGroup 2 (P ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_top_of_perfect_of_isSolvable hP N ?_
  have := h2.isNilpotent
  infer_instance

end PerfectQuot

section EightFiveCent

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

@[expose] noncomputable def cBar (X S L : Subgroup G) : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
  hBar X S L ⊓ Subgroup.centralizer (⋃ h ∈ hBar X S L,
    ((barM X L).map (MulAut.conj h).toMonoidHom : Set (↥X ⧸ CFSG.pCore 2 ↥X)))

theorem cBar_commute {c : ↥X ⧸ CFSG.pCore 2 ↥X} (hc : c ∈ cBar X S L)
    {h : ↥X ⧸ CFSG.pCore 2 ↥X} (hh : h ∈ hBar X S L) {y : ↥X ⧸ CFSG.pCore 2 ↥X}
    (hy : y ∈ (barM X L).map (MulAut.conj h).toMonoidHom) : y * c = c * y :=
  Subgroup.mem_centralizer_iff.mp hc.2 y (Set.mem_biUnion hh hy)

theorem hBar_le_normalizer_cBar :
    hBar X S L ≤ Subgroup.normalizer (cBar X S L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  apply le_normalizer_of_forall_map_conj_le
  rintro g hg _ ⟨c, hc, rfl⟩
  have key : g * c * g⁻¹ ∈ cBar X S L := by
    refine Subgroup.mem_inf.mpr ⟨(hBar X S L).mul_mem ((hBar X S L).mul_mem hg hc.1)
      ((hBar X S L).inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨h, hh, hyh⟩ := Set.mem_iUnion₂.mp hy
    have hy' : g⁻¹ * y * g ∈ (barM X L).map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
      obtain ⟨ℓ, hℓ, rfl⟩ := hyh
      exact ⟨ℓ, hℓ, by simp [mul_assoc]⟩
    have := cBar_commute hc ((hBar X S L).mul_mem ((hBar X S L).inv_mem hg) hh) hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * y := by group
  simpa using key

omit [Finite G] in
theorem pow_mul_mem_of_normalizes {Γ : Type*} [Group Γ] {C : Subgroup Γ} {s c : Γ}
    (hs : s ∈ Subgroup.normalizer (C : Set Γ)) (hc : c ∈ C) (m : ℕ) :
    (s ^ m)⁻¹ * (s * c) ^ m ∈ C := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : s⁻¹ * ((s ^ m)⁻¹ * (s * c) ^ m) * s ∈ C := by
      have hsi : s⁻¹ ∈ Subgroup.normalizer (C : Set Γ) := inv_mem hs
      have := (Subgroup.mem_normalizer_iff.mp hsi _).mp ih
      simpa using this
    have h2 := C.mul_mem h1 hc
    have : (s ^ (m + 1))⁻¹ * (s * c) ^ (m + 1) =
        s⁻¹ * ((s ^ m)⁻¹ * (s * c) ^ m) * s * c := by
      rw [pow_succ, pow_succ, mul_inv_rev]
      group
    rw [this]
    exact h2

theorem not_hBar_le (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ¬ hBar X S L ≤ cBar X S L ⊔ (hBar X S L ⊓
      Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X))) := by
  intro hle
  set Lb := barM X L with hLb
  set Sb := barM X S with hSb
  set Cb := cBar X S L with hCb
  set Hb := hBar X S L with hHb
  have hLH : Lb ≤ Hb := barM_le_dBar.trans le_sup_left
  have hSH : Sb ≤ Hb := le_sup_right
  have hCN : Hb ≤ Subgroup.normalizer (Cb : Set _) := hBar_le_normalizer_cBar
  have hdec : ∀ x ∈ Hb, ∃ n ∈ Hb ⊓ Subgroup.normalizer (Sb : Set _), ∃ c ∈ Cb, n * c = x := by
    intro x hx
    have hx' : x ∈ ((Hb ⊓ Subgroup.normalizer (Sb : Set _) ⊔ Cb : Subgroup _) : Set _) := by
      rw [sup_comm]; exact hle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hCN)] at hx'
    obtain ⟨n, hn, c, hc, rfl⟩ := hx'
    exact ⟨n, hn, c, hc, rfl⟩
  have hnorm : ∀ n ∈ Hb, n ∈ Subgroup.normalizer (Sb : Set _) →
      n ∈ Subgroup.normalizer ((Sb ⊔ Cb : Subgroup _) : Set _) := by
    intro n hnH hnS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnS ⊢
    rw [Subgroup.map_sup, hnS, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCN hnH)]
  set A := Lb ⊓ (Sb ⊔ Cb) with hA
  have hAn : (A.subgroupOf Lb).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr fun a ℓ ha hℓ => ?_
    refine ⟨Lb.mul_mem (Lb.mul_mem hℓ ha.1) (Lb.inv_mem hℓ), ?_⟩
    obtain ⟨n, ⟨hnH, hnS⟩, c, hc, rfl⟩ := hdec ℓ (hLH hℓ)
    have h1 : c * a * c⁻¹ ∈ Sb ⊔ Cb := (Sb ⊔ Cb).mul_mem ((Sb ⊔ Cb).mul_mem
      (Subgroup.mem_sup_right hc) ha.2) ((Sb ⊔ Cb).inv_mem (Subgroup.mem_sup_right hc))
    have h2 := (Subgroup.mem_normalizer_iff.mp (hnorm n hnH hnS) _).mp h1
    have : n * c * a * (n * c)⁻¹ = n * (c * a * c⁻¹) * n⁻¹ := by group
    rw [this]
    exact h2
  have hodd : ¬ 2 ∣ (A.subgroupOf Lb).index := by
    intro hd
    have hsylL := isSylowTwoOf_barM_inf hyp hL hsyl
    refine hsylL.2.2 (hd.trans (Subgroup.index_dvd_of_le ?_))
    intro x hx
    exact ⟨hx.2, Subgroup.mem_sup_left hx.1⟩
  have hperf : commutator ↥Lb = ⊤ := hL.component.2.2.1
  have hAtop := eq_top_of_perfect_of_odd_index hperf _ hodd
  have hLSC : Lb ≤ Sb ⊔ Cb := fun x hx =>
    (show (⟨x, hx⟩ : ↥Lb) ∈ A.subgroupOf Lb from hAtop ▸ Subgroup.mem_top _).2
  have hN2 : (Cb.subgroupOf Lb).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hCN (hLH g.2)) _).mp hc
  have h2 : IsPGroup 2 (↥Lb ⧸ Cb.subgroupOf Lb) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H ℓ =>
      have hℓ : (ℓ : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ ((Sb ⊔ Cb : Subgroup _) : Set _) := hLSC ℓ.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hSH.trans hCN)] at hℓ
      obtain ⟨s, hs, c, hc, hsc⟩ := hℓ
      obtain ⟨k, hk⟩ := AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup ⟨s, hs⟩
      have hs1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hsc' : s * c = ℓ := hsc
      have := pow_mul_mem_of_normalizes (hCN (hSH hs)) hc (2 ^ k)
      rw [hs1, inv_one, one_mul, hsc'] at this
      simpa using this
  have hCtop := eq_top_of_perfect_of_isPGroup hperf _ h2
  have hLC : Lb ≤ Cb := fun x hx =>
    (show (⟨x, hx⟩ : ↥Lb) ∈ Cb.subgroupOf Lb from hCtop ▸ Subgroup.mem_top _)
  have hcomm : ∀ a b : ↥Lb, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have h1 : (1 : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ Hb := one_mem _
    have hb : (b : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ Lb.map (MulAut.conj (1 : ↥X ⧸ _)).toMonoidHom :=
      ⟨b, b.2, by simp⟩
    exact (cBar_commute (hLC a.2) h1 hb).symm
  obtain ⟨-, hs⟩ := hL.component.2.2
  have hcen : Subgroup.center ↥Lb = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr fun y => hcomm y x
  have hall : ∀ x : ↥Lb ⧸ Subgroup.center ↥Lb, x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y => exact (QuotientGroup.eq_one_iff y).mpr (hcen ▸ Subgroup.mem_top y)
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  exact hab ((hall a).trans (hall b).symm)

end EightFiveCent

section EightFiveM

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

@[expose] noncomputable def nGrp5 (X S L : Subgroup G) : Subgroup G :=
  ((cBar X S L).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map X.subtype

@[expose] noncomputable def mGrp5 (X S L : Subgroup G) : Subgroup G :=
  nGrp5 X S L ⊔ (hGrp5 X S L ⊓ Subgroup.normalizer (S : Set G))

theorem nGrp5_le : nGrp5 X S L ≤ X := Subgroup.map_subtype_le _

theorem barM_nGrp5_le : barM X (nGrp5 X S L) ≤ cBar X S L := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

theorem not_hGrp5_le_mGrp5 (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : ¬ hGrp5 X S L ≤ mGrp5 X S L := by
  intro h
  apply not_hBar_le hyp hL hsyl
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
  have hx : (x : G) ∈ hGrp5 X S L := (mem_hGrp5 (x := x)).mpr hy
  have hK : hGrp5 X S L ⊓ Subgroup.normalizer (S : Set G) ≤ X := inf_le_left.trans hGrp5_le
  have hx' : x ∈ (mGrp5 X S L).subgroupOf X := h hx
  unfold mGrp5 at hx'
  rw [Subgroup.subgroupOf_sup nGrp5_le hK] at hx'
  have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hx'
  rw [Subgroup.map_sup] at hmap
  refine (sup_le_sup barM_nGrp5_le ?_) hmap
  exact le_inf (barM_le_of_le_hGrp5 inf_le_left) (barM_le_normalizer_barM inf_le_right)

theorem exists_block5 (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hK : CFSG.Open.IsKGroup ↥X) (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ Y : Subgroup G, CFSG.CGT.PushingUp.IsBlockOfInX (hGrp5 X S L) Y ∧ ¬ Y ≤ mGrp5 X S L := by
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hcg : cgsIn (hGrp5 X S L) S ≤ mGrp5 X S L :=
    le_sup_of_le_right (le_inf (cgsIn_le _ _)
      ((AscEightFour.cgsIn_mono hHX).trans (hyp.cgs.le.trans inf_le_right)))
  refine hLF.relative (LocalCGT.kProper_of_isKGroup (AscEightFour.isKGroup_mono hK hHX))
    (LocalCGT.isCharacteristicP_of_charTwo (charTwo_of_le hyp twoCore_le_hGrp5 hHX))
    (LocalCGT.isSylowOf_of_isSylowTwoOf (isSylowTwoOf_hGrp5 hyp hL hsyl)) ?_ ?_
    (not_hGrp5_le_mGrp5 hyp hL hsyl)
  · exact (LocalCGT.centralizer_inf_le_cgsIn hyp.twoRadical.isPGroup hyp.twoRadical.2.1).trans hcg
  · intro B hB hBS hBc
    exact (LocalCGT.normalizer_inf_le_cgsIn B hB hBS hBc).trans hcg

end EightFiveM

end AscEightFive

end CFSG.AGLEmbedding

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemO

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Vocab

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def CentModE (R : Subgroup Y) (f a : Y) : Prop :=
  ∀ b ∈ rLayer (Om R) f, a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf (rLayer (Om R) f)

@[expose] def aSub (R Z : Subgroup Y) (f : Y) : Subgroup Y :=
  Subgroup.closure {a | a ∈ Z ∧ CentModE R f a}

@[expose] def p23Orb (Z : Subgroup Y) (t e : Y) : Set Y :=
  {f | ∃ m ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y), f = m * e * m⁻¹}

structure P23ZData (t u e : Y) (Z : Subgroup Y) : Prop where
  comm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a
  sq : ∀ a ∈ Z, a * a = 1
  he : e ∈ Z
  ht : t ∈ Z
  le_t : Z ≤ Subgroup.centralizer ({t} : Set Y)
  le_u : Z ≤ Subgroup.centralizer ({u} : Set Y)
  frattini : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
    ∃ m ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y), c = o * m
  cover : Z ≤ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ⊔
    Subgroup.closure ({t} ∪ {f | ∃ c ∈ Subgroup.centralizer ({t} : Set Y), f = c * e * c⁻¹})

end Vocab

section Gen

variable {Y : Type} [Group Y] [Finite Y] {R Z : Subgroup Y} {t u e : Y}

theorem P23ZData.isPGroup (hZ : P23ZData t u e Z) : IsPGroup 2 Z := by
  intro a
  refine ⟨1, ?_⟩
  ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
  exact hZ.sq a a.2

theorem conjSub_eq_of_mem_normalizer {m : Y} {H : Subgroup Y}
    (hm : m ∈ Subgroup.normalizer (H : Set Y)) : conjSub m H = H := by
  ext x
  rw [mem_conjSub_iff]
  rw [Subgroup.mem_normalizer_iff] at hm
  have h := hm (m⁻¹ * x * m)
  rw [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h
  exact h

theorem rLayer_conj_le (m f : Y) :
    conjSub m (rLayer (Om R) f) ≤ rLayer (Om R) (m * f * m⁻¹) := by
  unfold rLayer
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have h1 : conjSub m Q ∈ RSet (Om R) := RSet.conj (Asc77.conjInvariant_conjClass _) hQ m
  have h2 : conjSub m Q ≤ Subgroup.centralizer ({m * f * m⁻¹} : Set Y) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hQC hx)
    calc x * (m * f * m⁻¹) = m * ((m⁻¹ * x * m) * f) * m⁻¹ := by group
      _ = m * (f * (m⁻¹ * x * m)) * m⁻¹ := by rw [this]
      _ = m * f * m⁻¹ * x := by group
  exact le_iSup₂_of_le (conjSub m Q) h1 (le_iSup_of_le h2 le_rfl)

theorem rLayer_conj (m f : Y) : rLayer (Om R) (m * f * m⁻¹) = conjSub m (rLayer (Om R) f) := by
  refine le_antisymm ?_ (rLayer_conj_le m f)
  have h := conjSub_mono (n := m) (rLayer_conj_le (R := R) m⁻¹ (m * f * m⁻¹))
  rw [conjSub_conjSub_inv, show m⁻¹ * (m * f * m⁻¹) * m⁻¹⁻¹ = f by group] at h
  exact h

theorem centModE_conj (m f a : Y) : CentModE R (m * f * m⁻¹) (m * a * m⁻¹) ↔ CentModE R f a := by
  unfold CentModE
  rw [rLayer_conj, Asc77.Thompson.oddCoreOf_conjSub_eq]
  constructor
  · intro h b hb
    have h1 := h (m * b * m⁻¹) (conj_mem_conjSub hb)
    rw [mem_conjSub_iff] at h1
    convert h1 using 1
    group
  · intro h b hb
    rw [mem_conjSub_iff] at hb
    have h1 := h _ hb
    rw [mem_conjSub_iff]
    convert h1 using 1
    group

theorem mem_aSub_iff {f : Y} (hZf : Z ≤ Subgroup.centralizer ({f} : Set Y)) {a : Y} :
    a ∈ aSub R Z f ↔ a ∈ Z ∧ CentModE R f a := by
  have hfix : ∀ c ∈ Z, conjSub c (rLayer (Om R) f) = rLayer (Om R) f := by
    intro c hc
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hZf hc)
    rw [← rLayer_conj, show c * f * c⁻¹ = f by rw [h1]; group]
  have hnorm : ∀ c ∈ Z, ∀ o ∈ oddCoreOf (rLayer (Om R) f), c * o * c⁻¹ ∈ oddCoreOf (rLayer (Om R) f) := by
    intro c hc o ho
    have hE := hfix c hc
    have h1 : c * o * c⁻¹ ∈ conjSub c (oddCoreOf (rLayer (Om R) f)) := conj_mem_conjSub ho
    rwa [← Asc77.Thompson.oddCoreOf_conjSub_eq, hE] at h1
  have hnormE : ∀ c ∈ Z, ∀ b ∈ rLayer (Om R) f, c⁻¹ * b * c ∈ rLayer (Om R) f := by
    intro c hc b hb
    have hE := hfix c⁻¹ (Z.inv_mem hc)
    have h1 : c⁻¹ * b * c⁻¹⁻¹ ∈ conjSub c⁻¹ (rLayer (Om R) f) := conj_mem_conjSub hb
    rw [hE, inv_inv] at h1
    exact h1
  let H : Subgroup Y :=
    { carrier := {a | a ∈ Z ∧ CentModE R f a}
      mul_mem' := by
        rintro a a' ⟨ha, hca⟩ ⟨ha', hca'⟩
        refine ⟨Z.mul_mem ha ha', fun b hb => ?_⟩
        have h1 := hnorm a ha _ (hca' b hb)
        have h2 := hca b hb
        have := Subgroup.mul_mem _ h1 h2
        convert this using 1
        group
      one_mem' := ⟨Z.one_mem, fun b _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, hca⟩
        refine ⟨Z.inv_mem ha, fun b hb => ?_⟩
        have h2 := Subgroup.inv_mem _ (hnorm a⁻¹ (Z.inv_mem ha) _ (hca b hb))
        convert h2 using 1
        group }
  have hH : aSub R Z f = H :=
    le_antisymm ((Subgroup.closure_le _).mpr fun a ha => ha) (fun a ha => Subgroup.subset_closure ha)
  rw [hH]
  rfl

theorem aSub_le (R Z : Subgroup Y) (f : Y) : aSub R Z f ≤ Z :=
  (Subgroup.closure_le _).mpr fun _ ha => ha.1

theorem P23ZData.le_cent (hZ : P23ZData t u e Z) {f : Y} (hf : f ∈ Z) :
    Z ≤ Subgroup.centralizer ({f} : Set Y) := fun a ha =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hZ.comm f hf a ha).symm

theorem P23ZData.orb_le (hZ : P23ZData t u e Z) {f : Y} (hf : f ∈ p23Orb Z t e) : f ∈ Z := by
  obtain ⟨m, hm, rfl⟩ := hf
  have h := conjSub_eq_of_mem_normalizer (Subgroup.mem_inf.mp hm).2
  rw [← h]
  exact conj_mem_conjSub hZ.he

theorem P23ZData.aSub_conj (hZ : P23ZData t u e Z) {m : Y}
    (hm : m ∈ Subgroup.normalizer (Z : Set Y)) :
    aSub R Z (m * e * m⁻¹) = conjSub m (aSub R Z e) := by
  have hmZ := conjSub_eq_of_mem_normalizer hm
  have hf : m * e * m⁻¹ ∈ Z := by rw [← hmZ]; exact conj_mem_conjSub hZ.he
  ext a
  rw [mem_aSub_iff (hZ.le_cent hf), mem_conjSub_iff, mem_aSub_iff (hZ.le_cent hZ.he)]
  have ha : a ∈ Z ↔ m⁻¹ * a * m ∈ Z := by
    conv_lhs => rw [← hmZ]
    rw [mem_conjSub_iff]
  rw [ha, ← centModE_conj (R := R) m e (m⁻¹ * a * m), show m * (m⁻¹ * a * m) * m⁻¹ = a by group]

theorem P23ZData.relIndex_aSub (hZ : P23ZData t u e Z) {f : Y} (hf : f ∈ p23Orb Z t e) :
    (aSub R Z f).relIndex Z = (aSub R Z e).relIndex Z := by
  obtain ⟨m, hm, rfl⟩ := hf
  have hmN := (Subgroup.mem_inf.mp hm).2
  rw [hZ.aSub_conj hmN]
  have h1 := Subgroup.relIndex_map_map_of_injective (aSub R Z e) Z
    (f := (MulAut.conj m).toMonoidHom) (fun a b h => (MulAut.conj m).injective h)
  have h2 : Z.map (MulAut.conj m).toMonoidHom = Z := conjSub_eq_of_mem_normalizer hmN
  rw [h2] at h1
  exact h1

theorem index_centralizer_eq_ncard' {G : Type*} [Group G] (x : G) :
    (Subgroup.centralizer {x}).index = {y | IsConj x y}.ncard := by
  have h1 : (Subgroup.centralizer {x}).index = (MulAction.stabilizer (ConjAct G) x).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective
  rw [h1, MulAction.index_stabilizer]
  congr 1
  ext y
  simp only [ConjAct.mem_orbit_conjAct, Set.mem_ofPred_eq]
  exact isConj_comm

theorem P23ZData.orb_ncard (hZ : P23ZData t u e Z) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y)) (xe : ↥C) (hxe : (xe : Y) = e) :
    (p23Orb Z t e).ncard = (Subgroup.centralizer {F7I.piC C xe}).index := by
  rw [index_centralizer_eq_ncard']
  have hZ2 := hZ.isPGroup
  have hZC : Z ≤ C := hCdef ▸ hZ.le_t
  have hNC : ∀ m ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y), m ∈ C :=
    fun m hm => hCdef ▸ (Subgroup.mem_inf.mp hm).1
  refine Set.ncard_congr (fun f hf => F7I.piC C ⟨f, hZC (hZ.orb_le hf)⟩) ?_ ?_ ?_
  · rintro f ⟨m, hm, rfl⟩
    refine isConj_iff.mpr ⟨F7I.piC C ⟨m, hNC m hm⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hxe]
  · intro f f' hf hf' h
    have := F7I.piC_inj hZ2 (hZ.orb_le hf) (hZ.orb_le hf') h
    exact congrArg Subtype.val this
  · intro q hq
    obtain ⟨c, rfl⟩ := isConj_iff.mp hq
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) c
    obtain ⟨o, ho, m, hm, hcom⟩ := hZ.frattini c₀ (hCdef ▸ c₀.2)
    have ho' : o ∈ oddCoreOf C := hCdef ▸ ho
    have hmC : m ∈ C := hNC m hm
    refine ⟨m * e * m⁻¹, ⟨m, hm, rfl⟩, ?_⟩
    have hq' : F7I.piC C ⟨m, hmC⟩ = F7I.piC C c₀ := by
      rw [F7I.piC_eq_iff]
      have : ((⟨m, hmC⟩⁻¹ * c₀ : ↥C) : Y) = m⁻¹ * o * m⁻¹⁻¹ := by
        show m⁻¹ * (c₀ : Y) = _
        rw [hcom]; group
      rw [this]
      exact mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer (C.inv_mem hmC)) ho'
    have hconj : F7I.piC C ⟨m * e * m⁻¹, hZC (hZ.orb_le ⟨m, hm, rfl⟩)⟩ =
        F7I.piC C ⟨m, hmC⟩ * F7I.piC C xe * (F7I.piC C ⟨m, hmC⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [hxe]
    refine hconj.trans ?_
    rw [hq']

theorem relIndex_ne_zero' (H K : Subgroup Y) : H.relIndex K ≠ 0 := by
  intro h
  have h1 := Subgroup.relIndex_mul_card H K
  rw [h, zero_mul] at h1
  exact (Nat.card_pos (α := ↥K)).ne' h1.symm

theorem relIndex_mul_card_of_le {H K : Subgroup Y} (hHK : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card H K
  rwa [inf_of_le_left hHK] at h1

theorem P23ZData.card_ge_32 (hZ : P23ZData t u e Z) (ht1 : t ≠ 1)
    (h9 : (p23Orb Z t e).ncard = 9) : 32 ≤ Nat.card Z := by
  classical
  set O := p23Orb Z t e with hOdef
  have hOZ : O ⊆ (Z : Set Y) := fun f hf => hZ.orb_le hf
  have htO : ∀ f ∈ O, t * f ∈ O → ∀ f' ∈ O, t * f' ∈ O := by
    rintro f ⟨m, hm, rfl⟩ ⟨m', hm', hm'e⟩ f' ⟨n, hn, rfl⟩
    have hmt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm).1
    have hnt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hn).1
    refine ⟨n * m⁻¹ * m', ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (Subgroup.inv_mem _ hm)) hm'
    · have hmt' : m * t * m⁻¹ = t := by rw [hmt, mul_inv_cancel_right]
      have hnt' : n⁻¹ * t * n = t := by rw [mul_assoc, ← hnt, inv_mul_cancel_left]
      have hte : t * e = m⁻¹ * (t * (m * e * m⁻¹)) * m := by
        calc t * e = m⁻¹ * (m * t * m⁻¹) * (m * e * m⁻¹) * m := by group
          _ = m⁻¹ * (t * (m * e * m⁻¹)) * m := by rw [hmt']; group
      rw [hm'e] at hte
      calc t * (n * e * n⁻¹) = n * (n⁻¹ * t * n) * e * n⁻¹ := by group
        _ = n * (t * e) * n⁻¹ := by rw [hnt']; group
        _ = n * m⁻¹ * m' * e * (n * m⁻¹ * m')⁻¹ := by rw [hte]; group
  have hdisj : ∀ f ∈ O, t * f ∉ O := by
    intro f hf htf
    have hfin : O.Finite := Set.toFinite O
    haveI : Fintype ↥O := hfin.fintype
    let σ : Function.End ↥O := fun x => ⟨t * x, htO f hf htf x x.2⟩
    have ht2 : t * t = 1 := by
      have := hZ.sq t hZ.ht
      exact this
    have hσ : σ ^ 2 ^ 1 = 1 := by
      funext x
      apply Subtype.ext
      show t * (t * (x : Y)) = x
      rw [← mul_assoc, ht2, one_mul]
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hσ
    have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨x, hx⟩ => ht1 ?_⟩
      have h1 : t * (x : Y) = x := congrArg Subtype.val hx
      calc t = t * x * (x : Y)⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    rw [hfix] at hmod
    have hcard : Fintype.card ↥O = 9 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, h9]
    rw [hcard] at hmod
    exact absurd hmod (by decide)
  have hinj : Function.Injective (fun f : Y => t * f) := mul_right_injective t
  have hU : (O ∪ (fun f => t * f) '' O).ncard = 18 := by
    rw [Set.ncard_union_eq, Set.ncard_image_of_injective _ hinj, h9]
    rw [Set.disjoint_left]
    rintro f hf ⟨f', hf', rfl⟩
    exact hdisj f' hf' hf
  have hsub : O ∪ (fun f => t * f) '' O ⊆ (Z : Set Y) := by
    rintro f (hf | ⟨f', hf', rfl⟩)
    · exact hOZ hf
    · exact Z.mul_mem hZ.ht (hOZ hf')
  have h18 : 18 ≤ Nat.card Z := by
    rw [← hU]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq (Z : Set Y)] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hZ.isPGroup)
  rw [hk] at h18 ⊢
  by_contra hlt
  have hk4 : k ≤ 4 := by
    by_contra h5
    exact hlt (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ k)))
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk4
  omega

end Gen



section Steps

@[expose] def P23E7ZEx (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∃ Z : Subgroup Y, P23ZData t u e Z

@[expose] def P23E7N7 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → (aSub R Z e).relIndex Z ≤ 4

@[expose] def P23E7LL1 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f ∈ p23Orb Z t e, f ≠ e →
          aSub R Z e ⊓ aSub R Z f ≠ ⊥ → (aSub R Z e ⊓ aSub R Z f).relIndex Z ≤ 8

@[expose] def P23E7LL2 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f₁ ∈ p23Orb Z t e, f₁ ≠ e →
          ∀ U : Subgroup Y, U ≤ aSub R Z e ⊓ aSub R Z f₁ → U ≠ ⊥ →
            ∀ f ∈ p23Orb Z t e, U ⊓ aSub R Z f ≠ ⊥ → U ≤ aSub R Z f

@[expose] def P23E7LL3 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f₁ ∈ p23Orb Z t e, f₁ ≠ e →
          ∀ U : Subgroup Y, U ≤ aSub R Z e ⊓ aSub R Z f₁ → U ≠ ⊥ →
            {f | f ∈ p23Orb Z t e ∧ U ≤ aSub R Z f}.ncard ≤ 7

variable {n : ℕ}

theorem p23E7Not9C_of_steps (h0 : P23E7ZEx n) (h7 : P23E7N7 n) (h1 : P23E7LL1 n) (h2 : P23E7LL2 n)
    (h3 : P23E7LL3 n) : P23E7Not9C n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ xe hxe h9
  obtain ⟨Z, hZd⟩ := h0 hcit hP Y R S t K' W u e g hc hno hE hZ
  have hC := CoreData.of_S hc.std.perp.core
  have ht1 : t ≠ 1 := (Inner.isUniqueInvolution_core hC.datum).ne_one
  have horb : (p23Orb Z t e).ncard = 9 := by rw [hZd.orb_ncard rfl xe hxe]; exact h9
  have hZ32 : 32 ≤ Nat.card Z := hZd.card_ge_32 ht1 horb
  set A := aSub R Z e with hAdef
  have hAZ : A ≤ Z := aSub_le R Z e
  have ha4 : A.relIndex Z ≤ 4 := h7 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd
  have hA8 : 8 ≤ Nat.card A := by
    have := relIndex_mul_card_of_le hAZ
    nlinarith
  have hb : ∀ f ∈ p23Orb Z t e, (aSub R Z f).relIndex A ≤ 2 := by
    intro f hf
    by_cases hfe : f = e
    · rw [hfe, Subgroup.relIndex_self]; omega
    have haf : (aSub R Z f).relIndex Z = A.relIndex Z := hZd.relIndex_aSub hf
    have hBZ : A ⊓ aSub R Z f ≤ Z := inf_le_left.trans hAZ
    have hB16 : (A ⊓ aSub R Z f).relIndex Z ≤ 16 := by
      have := (Subgroup.relIndex_inf_le :
        (A ⊓ aSub R Z f).relIndex Z ≤ A.relIndex Z * (aSub R Z f).relIndex Z)
      rw [haf] at this
      nlinarith
    have hBne : A ⊓ aSub R Z f ≠ ⊥ := by
      intro hB
      rw [hB, Subgroup.relIndex_bot_left] at hB16
      omega
    have h8 := h1 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd f hf hfe hBne
    have hmul := Subgroup.relIndex_mul_relIndex (A ⊓ aSub R Z f) A Z inf_le_left hAZ
    have hle : (aSub R Z f).relIndex A ≤ A.relIndex Z := by
      rw [← haf]
      exact Subgroup.relIndex_le_of_le_right hAZ (relIndex_ne_zero' _ _)
    rw [Subgroup.inf_relIndex_left] at hmul
    have hpos : 0 < (aSub R Z f).relIndex A := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
    nlinarith
  obtain ⟨f₁, hf₁, hf₁e⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (p23Orb Z t e).ncard) e
  set U := A ⊓ aSub R Z f₁ with hUdef
  have hUA : U ≤ A := inf_le_left
  have hUcard : 4 ≤ Nat.card U := by
    have := relIndex_mul_card_of_le hUA
    rw [hUdef, Subgroup.inf_relIndex_left] at this
    have := hb f₁ hf₁
    nlinarith
  have hUne : U ≠ ⊥ := by
    intro hU
    rw [hU, Subgroup.card_bot] at hUcard
    omega
  have hall : ∀ f ∈ p23Orb Z t e, U ≤ aSub R Z f := by
    intro f hf
    refine h2 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd f₁ hf₁ hf₁e U le_rfl hUne f hf ?_
    have hDA : U ⊓ aSub R Z f ≤ A := inf_le_left.trans hUA
    have hD4 : (U ⊓ aSub R Z f).relIndex A ≤ 4 := by
      have h1' := (Subgroup.relIndex_inf_le :
        (U ⊓ aSub R Z f).relIndex A ≤ U.relIndex A * (aSub R Z f).relIndex A)
      have h2' : U.relIndex A = (aSub R Z f₁).relIndex A := by
        rw [hUdef, Subgroup.inf_relIndex_left]
      rw [h2'] at h1'
      have := hb f₁ hf₁
      have := hb f hf
      nlinarith
    intro hD
    rw [hD, Subgroup.relIndex_bot_left] at hD4
    omega
  have hset : {f | f ∈ p23Orb Z t e ∧ U ≤ aSub R Z f} = p23Orb Z t e :=
    Set.ext fun f => ⟨fun h => h.1, fun h => ⟨h, hall f h⟩⟩
  have h7' := h3 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd f₁ hf₁ hf₁e U le_rfl hUne
  rw [hset, horb] at h7'
  omega

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

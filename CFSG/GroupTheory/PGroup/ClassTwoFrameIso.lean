module

public import CFSG.GroupTheory.PGroup.ClassTwoCoordinates

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective EBasis eSub
  eSub_eq_closure commute_eElt add_self_zmod2)
open scoped commutatorElement Matrix

variable {G G' : Type*} [Group G] [Group G']

structure IsQuotFrame {n : ℕ} (Q Z : Subgroup G) (f : Fin n → G) : Prop where
  le : Z ≤ Q
  mem : ∀ i, f i ∈ Q
  comm : ∀ y ∈ Z, ∀ i, y * f i = f i * y
  sq : ∀ i, f i ^ 2 ∈ Z
  cm : ∀ i j, ⁅f i, f j⁆ ∈ Z
  indep : ∀ v, eElt f v ∈ Z → v = 0
  card : Nat.card Q = 2 ^ n * Nat.card Z

private theorem eElt_of_mem_closure {d : ℕ} {z : Fin d → G}
    (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s)) {x : G}
    (hx : x ∈ Subgroup.closure (Set.range z)) : ∃ u, eElt z u = x := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact ⟨Pi.single t 1, eElt_single z t⟩
  | one => exact ⟨0, eElt_zero z⟩
  | mul a b _ _ ha hb =>
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    exact ⟨u + v, eElt_add hz2 hzz u v⟩
  | inv a _ ha =>
    obtain ⟨u, rfl⟩ := ha
    refine ⟨u, ?_⟩
    have h2 : eElt z u * eElt z u = 1 := by
      rw [← eElt_add hz2 hzz u u, add_self_zmod2, eElt_zero]
    exact (inv_eq_of_mul_eq_one_right h2).symm

private theorem card_coord (n : ℕ) : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
  rw [← Nat.card_congr (Multiplicative.ofAdd (α := Fin n → ZMod 2))]
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private noncomputable def eEltHom {d : ℕ} {Z : Subgroup G} {z : Fin d → G}
    (hzZ : ∀ t, z t ∈ Z) (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s)) :
    Multiplicative (Fin d → ZMod 2) →* ↥Z where
  toFun u := ⟨eElt z u.toAdd, eElt_mem_of_forall_mem hzZ u.toAdd⟩
  map_one' := Subtype.ext (by simpa using eElt_zero z)
  map_mul' u v := Subtype.ext (by simpa using eElt_add hz2 hzz u.toAdd v.toAdd)

private noncomputable def quotFrameHom {n : ℕ} {Q Z : Subgroup G} [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hfQ : ∀ i, f i ∈ Q) (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y)
    (hsq : ∀ i, f i ^ 2 ∈ Z) (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) :
    Multiplicative (Fin n → ZMod 2) →* ↥Q ⧸ Z.subgroupOf Q where
  toFun v := QuotientGroup.mk ⟨eElt f v.toAdd, eElt_mem_of_forall_mem hfQ v.toAdd⟩
  map_one' := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show eElt f 0 ∈ Z
    rw [eElt_zero]
    exact Z.one_mem
  map_mul' v w := by
    have h := eElt_add_mul_inv_mem hZc hsq hcm v.toAdd w.toAdd
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq_iff_div_mem.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h

private theorem quotFrameHom_apply {n : ℕ} {Q Z : Subgroup G} [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hfQ : ∀ i, f i ∈ Q) (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y)
    (hsq : ∀ i, f i ^ 2 ∈ Z) (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z)
    (v : Multiplicative (Fin n → ZMod 2)) :
    quotFrameHom hfQ hZc hsq hcm v =
      QuotientGroup.mk ⟨eElt f v.toAdd, eElt_mem_of_forall_mem hfQ v.toAdd⟩ := rfl

private theorem quotFrameHom_surjective {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q]
    [(Z.subgroupOf Q).Normal] {f : Fin n → G} (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q)
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (hgen : Q ≤ Subgroup.closure (Set.range f) ⊔ Z) :
    Function.Surjective (quotFrameHom hfQ hZc hsq hcm) := by
  let H : Subgroup ↥Q :=
    (quotFrameHom hfQ hZc hsq hcm).range.comap (QuotientGroup.mk' (Z.subgroupOf Q))
  have hH : ∀ x : ↥Q, x ∈ H ↔ (QuotientGroup.mk x : ↥Q ⧸ Z.subgroupOf Q) ∈
      (quotFrameHom hfQ hZc hsq hcm).range := fun x => Subgroup.mem_comap
  have hfH : ∀ i, (⟨f i, hfQ i⟩ : ↥Q) ∈ H := by
    intro i
    rw [hH]
    have h : (⟨eElt f (Pi.single i 1), eElt_mem_of_forall_mem hfQ _⟩ : ↥Q) = ⟨f i, hfQ i⟩ :=
      Subtype.ext (eElt_single f i)
    rw [← h]
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), quotFrameHom_apply hfQ hZc hsq hcm _⟩
  have hzH : ∀ z (hz : z ∈ Z), (⟨z, hZQ hz⟩ : ↥Q) ∈ H := by
    intro z hz
    rw [hH]
    have h1 : (QuotientGroup.mk (⟨z, hZQ hz⟩ : ↥Q) : ↥Q ⧸ Z.subgroupOf Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hz)
    rw [h1]
    exact (quotFrameHom hfQ hZc hsq hcm).range.one_mem
  have hsup : Subgroup.closure (Set.range f) ⊔ Z ≤ H.map (Subgroup.subtype Q) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨f i, hfQ i⟩, hfH i, rfl⟩
    · intro z hz
      exact ⟨⟨z, hZQ hz⟩, hzH z hz, rfl⟩
  have htop : H = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hsup (hgen x.2))
    rwa [show y = x from Subtype.ext hyx] at hy
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact (hH x).mp (htop ▸ Subgroup.mem_top x)

theorem eElt_indep_of_card {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q] [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q)
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (hgen : Q ≤ Subgroup.closure (Set.range f) ⊔ Z)
    (hcard : Nat.card Q = 2 ^ n * Nat.card Z) :
    ∀ v, eElt f v ∈ Z → v = 0 := by
  have hcardq : Nat.card (↥Q ⧸ Z.subgroupOf Q) = 2 ^ n := by
    have hW : Nat.card (Z.subgroupOf Q) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv
    have hpos : 0 < Nat.card Z := by
      haveI : Nonempty ↥Z := ⟨⟨1, Z.one_mem⟩⟩
      haveI : Finite ↥Z :=
        Finite.of_injective (Subgroup.inclusion hZQ) (Subgroup.inclusion_injective hZQ)
      exact Nat.card_pos
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf Q : Subgroup ↥Q)
    rw [hW, hcard] at h1
    exact (Nat.mul_right_cancel hpos h1).symm
  have hbij : Function.Bijective (quotFrameHom hfQ hZc hsq hcm) :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨quotFrameHom_surjective hZQ hfQ hZc hsq hcm hgen, by rw [hcardq, card_coord]⟩
  intro v hv
  have h1 : quotFrameHom hfQ hZc hsq hcm (Multiplicative.ofAdd v) = 1 := by
    rw [quotFrameHom_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hv)
  have h2 : Multiplicative.ofAdd v = (1 : Multiplicative (Fin n → ZMod 2)) := by
    apply hbij.1
    rw [h1, map_one]
  simpa using congrArg Multiplicative.toAdd h2

theorem isQuotFrame_of_card {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q] [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q)
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (hgen : Q ≤ Subgroup.closure (Set.range f) ⊔ Z)
    (hcard : Nat.card Q = 2 ^ n * Nat.card Z) :
    IsQuotFrame Q Z f :=
  { le := hZQ
    mem := hfQ
    comm := hZc
    sq := hsq
    cm := hcm
    indep := eElt_indep_of_card hZQ hfQ hZc hsq hcm hgen hcard
    card := hcard }

structure IsEBasisOf {d : ℕ} (Z : Subgroup G) (z : Fin d → G) : Prop where
  mem : ∀ t, z t ∈ Z
  ebasis : EBasis z
  span : ∀ y ∈ Z, ∃ u, y = eElt z u

theorem isEBasisOf_of_card {d : ℕ} {Z : Subgroup G} {z : Fin d → G} (hzZ : ∀ t, z t ∈ Z)
    (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s))
    (hgen : Z ≤ Subgroup.closure (Set.range z)) (hcard : Nat.card Z = 2 ^ d) :
    IsEBasisOf Z z := by
  classical
  haveI : Finite ↥Z :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero d (by decide))
  have hsurj : Function.Surjective (eEltHom hzZ hz2 hzz) := by
    intro y
    obtain ⟨u, hu⟩ := eElt_of_mem_closure hz2 hzz (hgen y.2)
    exact ⟨Multiplicative.ofAdd u, Subtype.ext hu⟩
  have hbij : Function.Bijective (eEltHom hzZ hz2 hzz) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by
      rw [hcard, card_coord]⟩
  have hne : ∀ c, eElt z c = 1 → c = 0 := by
    intro c hc
    have h1 : eEltHom hzZ hz2 hzz (Multiplicative.ofAdd c) = eEltHom hzZ hz2 hzz 1 := by
      apply Subtype.ext
      show eElt z c = eElt z 0
      rw [hc, eElt_zero]
    simpa using congrArg Multiplicative.toAdd (hbij.1 h1)
  refine ⟨hzZ, ⟨hz2, hzz, hne⟩, ?_⟩
  intro y hy
  obtain ⟨u, hu⟩ := eElt_of_mem_closure hz2 hzz (hgen hy)
  exact ⟨u, hu.symm⟩

noncomputable def frameQuotEquiv {n : ℕ} {Q Z : Subgroup G} {Q' Z' : Subgroup G'}
    [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal] [(Z'.subgroupOf Q').Normal]
    {f : Fin n → G} {f' : Fin n → G'} (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f') :
    ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q' :=
  (eEltQuotEquiv f hf.le hf.mem hf.comm hf.sq hf.cm hf.indep hf.card).symm.trans
    (eEltQuotEquiv f' hf'.le hf'.mem hf'.comm hf'.sq hf'.cm hf'.indep hf'.card)

private theorem frameQuotEquiv_apply {n : ℕ} {Q Z : Subgroup G} {Q' Z' : Subgroup G'}
    [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal] [(Z'.subgroupOf Q').Normal]
    {f : Fin n → G} {f' : Fin n → G'} (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    (x : ↥Q ⧸ Z.subgroupOf Q) :
    frameQuotEquiv hf hf' x =
      eEltQuotEquiv f' hf'.le hf'.mem hf'.comm hf'.sq hf'.cm hf'.indep hf'.card
        ((eEltQuotEquiv f hf.le hf.mem hf.comm hf.sq hf.cm hf.indep hf.card).symm x) := rfl

theorem frameQuotEquiv_mk_eElt {n : ℕ} {Q Z : Subgroup G} {Q' Z' : Subgroup G'}
    [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal] [(Z'.subgroupOf Q').Normal]
    {f : Fin n → G} {f' : Fin n → G'} (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    (v : Fin n → ZMod 2) :
    frameQuotEquiv hf hf'
        (QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hf.mem v⟩ : ↥Q ⧸ Z.subgroupOf Q) =
      (QuotientGroup.mk ⟨eElt f' v, eElt_mem_of_forall_mem hf'.mem v⟩ :
        ↥Q' ⧸ Z'.subgroupOf Q') := by
  have hfwd : eEltQuotEquiv f hf.le hf.mem hf.comm hf.sq hf.cm hf.indep hf.card
      (Multiplicative.ofAdd v) =
      (QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hf.mem v⟩ : ↥Q ⧸ Z.subgroupOf Q) :=
    eEltQuotEquiv_ofAdd f hf.le hf.mem hf.comm hf.sq hf.cm hf.indep hf.card v
  have hfwd' : eEltQuotEquiv f' hf'.le hf'.mem hf'.comm hf'.sq hf'.cm hf'.indep hf'.card
      (Multiplicative.ofAdd v) =
      (QuotientGroup.mk ⟨eElt f' v, eElt_mem_of_forall_mem hf'.mem v⟩ :
        ↥Q' ⧸ Z'.subgroupOf Q') :=
    eEltQuotEquiv_ofAdd f' hf'.le hf'.mem hf'.comm hf'.sq hf'.cm hf'.indep hf'.card v
  rw [frameQuotEquiv_apply, ← hfwd, ← hfwd', MulEquiv.symm_apply_apply]

private theorem mk_eq_mk_eElt_of_eq_mul {n : ℕ} {Q Z : Subgroup G} [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hf : IsQuotFrame Q Z f) {x : ↥Q} {v : Fin n → ZMod 2} {y : G}
    (hy : y ∈ Z) (hxy : (x : G) = eElt f v * y) :
    (QuotientGroup.mk x : ↥Q ⧸ Z.subgroupOf Q) =
      QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hf.mem v⟩ := by
  have hxeq : x = (⟨eElt f v, eElt_mem_of_forall_mem hf.mem v⟩ : ↥Q) * ⟨y, hf.le hy⟩ :=
    Subtype.ext hxy
  rw [hxeq, QuotientGroup.mk_mul]
  have hy1 : (QuotientGroup.mk (⟨y, hf.le hy⟩ : ↥Q) : ↥Q ⧸ Z.subgroupOf Q) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
  rw [hy1, mul_one]

private theorem exists_eElt_mul_mk {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q]
    [(Z.subgroupOf Q).Normal] {f : Fin n → G} (hf : IsQuotFrame Q Z f) (x : ↥Q) :
    ∃ v : Fin n → ZMod 2, ∃ y ∈ Z, (x : G) = eElt f v * y ∧
      (QuotientGroup.mk x : ↥Q ⧸ Z.subgroupOf Q) =
        QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hf.mem v⟩ := by
  obtain ⟨v, y, hy, hxy⟩ :=
    exists_eElt_mul hf.le hf.mem hf.comm hf.sq hf.cm hf.indep hf.card (x : G) x.2
  exact ⟨v, y, hy, hxy, mk_eq_mk_eElt_of_eq_mul hf hy hxy⟩

private theorem eq_eElt_mul_of_mk_eq {n : ℕ} {Q Z : Subgroup G} [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} (hf : IsQuotFrame Q Z f) {x : ↥Q} {u : Fin n → ZMod 2}
    (hx : (QuotientGroup.mk x : ↥Q ⧸ Z.subgroupOf Q) =
      QuotientGroup.mk ⟨eElt f u, eElt_mem_of_forall_mem hf.mem u⟩) :
    ∃ y ∈ Z, (x : G) = eElt f u * y := by
  have hz : (x : G) * (eElt f u)⁻¹ ∈ Z := by
    have h := QuotientGroup.eq_iff_div_mem.mp hx
    rw [Subgroup.mem_subgroupOf] at h
    simpa [div_eq_mul_inv] using h
  refine ⟨(x : G) * (eElt f u)⁻¹, hz, ?_⟩
  have hcomm : Commute ((x : G) * (eElt f u)⁻¹) (eElt f u) :=
    commute_eElt (v := f) (fun i => hf.comm _ hz i) u
  rw [← hcomm.eq]
  group

theorem frameQuotEquiv_mk_eq_iff {n : ℕ} {Q Z : Subgroup G} {Q' Z' : Subgroup G'}
    [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal] [(Z'.subgroupOf Q').Normal]
    {f : Fin n → G} {f' : Fin n → G'} (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    (x : ↥Q) (x' : ↥Q') :
    frameQuotEquiv hf hf' (QuotientGroup.mk x) = QuotientGroup.mk x' ↔
      ∃ v : Fin n → ZMod 2, ∃ y ∈ Z, ∃ y' ∈ Z',
        (x : G) = eElt f v * y ∧ (x' : G') = eElt f' v * y' := by
  constructor
  · intro h
    obtain ⟨v, y, hy, hxy, hv⟩ := exists_eElt_mul_mk hf x
    have hx' : (QuotientGroup.mk x' : ↥Q' ⧸ Z'.subgroupOf Q') =
        QuotientGroup.mk ⟨eElt f' v, eElt_mem_of_forall_mem hf'.mem v⟩ := by
      rw [← h, hv, frameQuotEquiv_mk_eElt]
    obtain ⟨y', hy', hxy'⟩ := eq_eElt_mul_of_mk_eq hf' hx'
    exact ⟨v, y, hy, y', hy', hxy, hxy'⟩
  · rintro ⟨v, y, hy, y', hy', hxy, hxy'⟩
    rw [mk_eq_mk_eElt_of_eq_mul hf hy hxy, mk_eq_mk_eElt_of_eq_mul hf' hy' hxy',
      frameQuotEquiv_mk_eElt]

private noncomputable def eEltMulEquiv {d : ℕ} {Z : Subgroup G} {z : Fin d → G}
    (he : EBasis z) (hzZ : ∀ t, z t ∈ Z) (hspan : ∀ y ∈ Z, ∃ u, y = eElt z u) :
    Multiplicative (Fin d → ZMod 2) ≃* ↥Z :=
  MulEquiv.ofBijective (eEltHom hzZ he.sq he.comm)
    ⟨fun u v huv => Multiplicative.ext (eElt_injective he (congrArg Subtype.val huv)),
      fun y => by
        obtain ⟨u, hu⟩ := hspan y y.2
        exact ⟨Multiplicative.ofAdd u, Subtype.ext hu.symm⟩⟩

private noncomputable def coordMulEquiv {d : ℕ} (μ ν : Matrix (Fin d) (Fin d) (ZMod 2))
    (hμν : μ * ν = 1) (hνμ : ν * μ = 1) :
    Multiplicative (Fin d → ZMod 2) ≃* Multiplicative (Fin d → ZMod 2) where
  toFun u := Multiplicative.ofAdd (μ *ᵥ u.toAdd)
  invFun u := Multiplicative.ofAdd (ν *ᵥ u.toAdd)
  left_inv u := by
    show Multiplicative.ofAdd (ν *ᵥ (μ *ᵥ u.toAdd)) = u
    rw [Matrix.mulVec_mulVec, hνμ, Matrix.one_mulVec]
    rfl
  right_inv u := by
    show Multiplicative.ofAdd (μ *ᵥ (ν *ᵥ u.toAdd)) = u
    rw [Matrix.mulVec_mulVec, hμν, Matrix.one_mulVec]
    rfl
  map_mul' u v := by
    have h : (u * v).toAdd = u.toAdd + v.toAdd := rfl
    show Multiplicative.ofAdd (μ *ᵥ (u * v).toAdd) =
      Multiplicative.ofAdd (μ *ᵥ u.toAdd) * Multiplicative.ofAdd (μ *ᵥ v.toAdd)
    rw [h, Matrix.mulVec_add]
    rfl

noncomputable def eBasisMulEquiv {d : ℕ} {Z : Subgroup G} {Z' : Subgroup G'} {z : Fin d → G}
    {z' : Fin d → G'} (hz : IsEBasisOf Z z) (hz' : IsEBasisOf Z' z')
    (μ ν : Matrix (Fin d) (Fin d) (ZMod 2)) (hμν : μ * ν = 1) (hνμ : ν * μ = 1) :
    ↥Z ≃* ↥Z' :=
  (eEltMulEquiv hz.ebasis hz.mem hz.span).symm.trans
    ((coordMulEquiv μ ν hμν hνμ).trans (eEltMulEquiv hz'.ebasis hz'.mem hz'.span))

theorem eBasisMulEquiv_apply {d : ℕ} {Z : Subgroup G} {Z' : Subgroup G'} {z : Fin d → G}
    {z' : Fin d → G'} (hz : IsEBasisOf Z z) (hz' : IsEBasisOf Z' z')
    (μ ν : Matrix (Fin d) (Fin d) (ZMod 2)) (hμν : μ * ν = 1) (hνμ : ν * μ = 1)
    {y : ↥Z} {u : Fin d → ZMod 2} (hy : (y : G) = eElt z u) :
    (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') = eElt z' (μ *ᵥ u) := by
  have hE : eEltMulEquiv hz.ebasis hz.mem hz.span (Multiplicative.ofAdd u) = y := by
    refine Subtype.ext ?_
    show eElt z u = (y : G)
    exact hy.symm
  have hsymm : (eEltMulEquiv hz.ebasis hz.mem hz.span).symm y = Multiplicative.ofAdd u := by
    rw [← hE, MulEquiv.symm_apply_apply]
  rw [show eBasisMulEquiv hz hz' μ ν hμν hνμ y =
    eEltMulEquiv hz'.ebasis hz'.mem hz'.span
      (coordMulEquiv μ ν hμν hνμ ((eEltMulEquiv hz.ebasis hz.mem hz.span).symm y)) from rfl,
    hsymm]
  rfl

private theorem conj_mem_of_le_normalizer {H R : Subgroup G}
    (h : R ≤ Subgroup.normalizer (H : Set G)) {r : G} (hr : r ∈ R) {x : G} (hx : x ∈ H) :
    r * x * r⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp (h hr) x).mp hx

private theorem frameQuotEquiv_mk_conj {n : ℕ} {Q Z : Subgroup G} {Q' Z' : Subgroup G'}
    [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal] [(Z'.subgroupOf Q').Normal]
    {f : Fin n → G} {f' : Fin n → G'} (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    {g : G} {g' : G'} (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z)
    (hg'Z : ∀ y ∈ Z', g' * y * g'⁻¹ ∈ Z') (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hg : ∀ j, g * f j * g⁻¹ * (eElt f fun i => M i j)⁻¹ ∈ Z)
    (hg' : ∀ j, g' * f' j * g'⁻¹ * (eElt f' fun i => M i j)⁻¹ ∈ Z') :
    ∀ (v w : ↥Q) (v' w' : ↥Q'), (w : G) = g * v * g⁻¹ →
      (w' : G') = g' * v' * g'⁻¹ →
        frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk v' →
          frameQuotEquiv hf hf' (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  intro v w v' w' hw hw' hfq
  obtain ⟨u, y, hy, _, hv⟩ := exists_eElt_mul_mk hf v
  have hv' : (QuotientGroup.mk v' : ↥Q' ⧸ Z'.subgroupOf Q') =
      QuotientGroup.mk ⟨eElt f' u, eElt_mem_of_forall_mem hf'.mem u⟩ := by
    rw [← hfq, hv, frameQuotEquiv_mk_eElt]
  have hqw := mk_conj_eq_mk_mulVec (g := g) hf.mem hf.comm hf.sq hf.cm hgZ M hg hv hw
  have hqw' := mk_conj_eq_mk_mulVec (g := g') hf'.mem hf'.comm hf'.sq hf'.cm hg'Z M hg' hv' hw'
  rw [hqw, hqw']
  exact frameQuotEquiv_mk_eElt hf hf' (M *ᵥ u)

private theorem frameQuotEquiv_conj_inv_step {n : ℕ} {Q Z R : Subgroup G}
    {Q' Z' R' : Subgroup G'} [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal]
    [(Z'.subgroupOf Q').Normal] {f : Fin n → G} {f' : Fin n → G'}
    (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    (hR'Q' : R' ≤ Subgroup.normalizer (Q' : Set G'))
    (hR'Z' : ∀ r ∈ R', ∀ y ∈ Z', r * y * r⁻¹ ∈ Z') (e : ↥R ≃* ↥R') (r : ↥R)
    (ih : ∀ (v w : ↥Q) (v' w' : ↥Q'), (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
        frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk v' →
          frameQuotEquiv hf hf' (QuotientGroup.mk w) = QuotientGroup.mk w') :
    ∀ (v w : ↥Q) (v' w' : ↥Q'), (w : G) = (↑(r⁻¹) : G) * v * (↑(r⁻¹) : G)⁻¹ →
      (w' : G') = (↑(e r⁻¹) : G') * v' * (↑(e r⁻¹) : G')⁻¹ →
        frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk v' →
          frameQuotEquiv hf hf' (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  intro v w v' w' hw hw' hfq
  have hv : (v : G) = (r : G) * w * (r : G)⁻¹ := by
    rw [hw, Subgroup.coe_inv]
    group
  have hv' : (v' : G') = (e r : G') * w' * (e r : G')⁻¹ := by
    rw [hw', map_inv, Subgroup.coe_inv]
    group
  obtain ⟨w'', hw''⟩ :=
    QuotientGroup.mk_surjective (frameQuotEquiv hf hf' (QuotientGroup.mk w))
  let w₂' : ↥Q' :=
    ⟨(e r : G') * w'' * (e r : G')⁻¹, conj_mem_of_le_normalizer hR'Q' (e r).2 w''.2⟩
  have hw₂' : (w₂' : G') = (e r : G') * w'' * (e r : G')⁻¹ := rfl
  have hkey : frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk w₂' :=
    ih w v w'' w₂' hv hw₂' hw''.symm
  have hveq : (QuotientGroup.mk v' : ↥Q' ⧸ Z'.subgroupOf Q') = QuotientGroup.mk w₂' := by
    rw [← hfq, hkey]
  have hz : (v' : G') * (w₂' : G')⁻¹ ∈ Z' := by
    have h := QuotientGroup.eq_iff_div_mem.mp hveq
    rw [Subgroup.mem_subgroupOf] at h
    simpa [div_eq_mul_inv] using h
  have hz' : ((e r : G')⁻¹) * ((v' : G') * (w₂' : G')⁻¹) * ((e r : G')⁻¹)⁻¹ ∈ Z' :=
    hR'Z' _ (R'.inv_mem (e r).2) _ hz
  have heq : ((e r : G')⁻¹) * ((v' : G') * (w₂' : G')⁻¹) * ((e r : G')⁻¹)⁻¹ =
      (w' : G') * (w'' : G')⁻¹ := by
    rw [hw₂', hv']
    group
  rw [heq] at hz'
  have hfinal : (QuotientGroup.mk w' : ↥Q' ⧸ Z'.subgroupOf Q') = QuotientGroup.mk w'' := by
    have h1 : (QuotientGroup.mk (w' * (w'')⁻¹ : ↥Q') : ↥Q' ⧸ Z'.subgroupOf Q') = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hz')
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact mul_inv_eq_one.mp h1
  rw [hfinal]
  exact hw''.symm

theorem frameQuotEquiv_conj_of_closure {n m : ℕ} {Q Z R : Subgroup G}
    {Q' Z' R' : Subgroup G'} [Finite ↥Q] [Finite ↥Q'] [(Z.subgroupOf Q).Normal]
    [(Z'.subgroupOf Q').Normal] {f : Fin n → G} {f' : Fin n → G'}
    (hf : IsQuotFrame Q Z f) (hf' : IsQuotFrame Q' Z' f')
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hRZ : ∀ r ∈ R, ∀ y ∈ Z, r * y * r⁻¹ ∈ Z)
    (hR'Q' : R' ≤ Subgroup.normalizer (Q' : Set G'))
    (hR'Z' : ∀ r ∈ R', ∀ y ∈ Z', r * y * r⁻¹ ∈ Z')
    (e : ↥R ≃* ↥R') (gen : Fin m → ↥R) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ l j, (gen l : G) * f j * (gen l : G)⁻¹ * (eElt f fun i => M l i j)⁻¹ ∈ Z)
    (hM' : ∀ l j, (e (gen l) : G') * f' j * (e (gen l) : G')⁻¹ *
      (eElt f' fun i => M l i j)⁻¹ ∈ Z') :
    ∀ (r : ↥R) (v w : ↥Q) (v' w' : ↥Q'), (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
        frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk v' →
          frameQuotEquiv hf hf' (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  have key : ∀ (r : ↥R), r ∈ Subgroup.closure (Set.range gen) →
      ∀ (v w : ↥Q) (v' w' : ↥Q'), (w : G) = (r : G) * v * (r : G)⁻¹ →
        (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
          frameQuotEquiv hf hf' (QuotientGroup.mk v) = QuotientGroup.mk v' →
            frameQuotEquiv hf hf' (QuotientGroup.mk w) = QuotientGroup.mk w' := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact frameQuotEquiv_mk_conj hf hf' (g := (gen l : G)) (g' := (e (gen l) : G'))
        (hRZ _ (gen l).2) (hR'Z' _ (e (gen l)).2) (M l) (hM l) (hM' l)
    | one =>
      intro v w v' w' hw hw' hfq
      have hw1 : w = v := Subtype.ext (by simpa using hw)
      have hw1' : w' = v' := Subtype.ext (by simpa using hw')
      rw [hw1, hw1']
      exact hfq
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      intro v w v' w' hw hw' hfq
      let v₂ : ↥Q := ⟨(r₂ : G) * v * (r₂ : G)⁻¹, conj_mem_of_le_normalizer hRQ r₂.2 v.2⟩
      let v₂' : ↥Q' :=
        ⟨(e r₂ : G') * v' * (e r₂ : G')⁻¹, conj_mem_of_le_normalizer hR'Q' (e r₂).2 v'.2⟩
      have hv₂ : (v₂ : G) = (r₂ : G) * v * (r₂ : G)⁻¹ := rfl
      have hv₂' : (v₂' : G') = (e r₂ : G') * v' * (e r₂ : G')⁻¹ := rfl
      have hmid : frameQuotEquiv hf hf' (QuotientGroup.mk v₂) = QuotientGroup.mk v₂' :=
        ih₂ v v₂ v' v₂' hv₂ hv₂' hfq
      refine ih₁ v₂ w v₂' w' ?_ ?_ hmid
      · rw [hw, Subgroup.coe_mul, hv₂]
        group
      · rw [hw', map_mul, Subgroup.coe_mul, hv₂']
        group
    | inv r _ ih => exact frameQuotEquiv_conj_inv_step hf hf' hR'Q' hR'Z' e r ih
  intro r
  exact key r (hgen ▸ Subgroup.mem_top r)

theorem eBasisMulEquiv_conj_of_closure {d m : ℕ} {Z R : Subgroup G} {Z' R' : Subgroup G'}
    {z : Fin d → G} {z' : Fin d → G'} (hz : IsEBasisOf Z z) (hz' : IsEBasisOf Z' z')
    (μ ν : Matrix (Fin d) (Fin d) (ZMod 2)) (hμν : μ * ν = 1) (hνμ : ν * μ = 1)
    (hRZ : ∀ r ∈ R, ∀ y ∈ Z, r * y * r⁻¹ ∈ Z)
    (e : ↥R ≃* ↥R') (gen : Fin m → ↥R) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (S : Fin m → Matrix (Fin d) (Fin d) (ZMod 2)) (hSμ : ∀ l, μ * S l = S l * μ)
    (hS : ∀ l t, (gen l : G) * z t * (gen l : G)⁻¹ = eElt z fun s => S l s t)
    (hS' : ∀ l t, (e (gen l) : G') * z' t * (e (gen l) : G')⁻¹ = eElt z' fun s => S l s t) :
    ∀ (r : ↥R) (y w : ↥Z), (w : G) = (r : G) * y * (r : G)⁻¹ →
      (eBasisMulEquiv hz hz' μ ν hμν hνμ w : G') =
        (e r : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') * (e r : G')⁻¹ := by
  have key : ∀ (r : ↥R), r ∈ Subgroup.closure (Set.range gen) → ∀ (y w : ↥Z),
      (w : G) = (r : G) * y * (r : G)⁻¹ →
        (eBasisMulEquiv hz hz' μ ν hμν hνμ w : G') =
          (e r : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') * (e r : G')⁻¹ := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      intro y w hw
      obtain ⟨u, hu⟩ := hz.span y y.2
      have hw' : (w : G) = eElt z (S l *ᵥ u) := by
        rw [hw, hu]
        exact conj_eElt_eq_mulVec hz.ebasis.sq hz.ebasis.comm (S l) (hS l) u
      rw [eBasisMulEquiv_apply hz hz' μ ν hμν hνμ hw',
        eBasisMulEquiv_apply hz hz' μ ν hμν hνμ hu,
        conj_eElt_eq_mulVec hz'.ebasis.sq hz'.ebasis.comm (S l) (hS' l) (μ *ᵥ u)]
      congr 1
      rw [Matrix.mulVec_mulVec, hSμ l, ← Matrix.mulVec_mulVec]
    | one =>
      intro y w hw
      have hwy : w = y := Subtype.ext (by simpa using hw)
      rw [hwy]
      simp
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      intro y w hw
      let w₂ : ↥Z := ⟨(r₂ : G) * (y : G) * (r₂ : G)⁻¹, hRZ _ r₂.2 _ y.2⟩
      have hw₂ : (w₂ : G) = (r₂ : G) * y * (r₂ : G)⁻¹ := rfl
      have hmid : (eBasisMulEquiv hz hz' μ ν hμν hνμ w₂ : G') =
          (e r₂ : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') * (e r₂ : G')⁻¹ :=
        ih₂ y w₂ hw₂
      have h₁ : (w : G) = (r₁ : G) * (w₂ : G) * (r₁ : G)⁻¹ := by
        rw [hw, Subgroup.coe_mul, hw₂]
        group
      calc (eBasisMulEquiv hz hz' μ ν hμν hνμ w : G') =
          (e r₁ : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ w₂ : G') * (e r₁ : G')⁻¹ :=
            ih₁ w₂ w h₁
        _ = (e r₁ : G') *
              ((e r₂ : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') * (e r₂ : G')⁻¹) *
              (e r₁ : G')⁻¹ := by rw [hmid]
        _ = (e (r₁ * r₂) : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') *
              (e (r₁ * r₂) : G')⁻¹ := by
            rw [map_mul, Subgroup.coe_mul]
            group
    | inv r _ ih =>
      intro y w hw
      have hw' : (y : G) = (r : G) * w * (r : G)⁻¹ := by
        rw [hw, Subgroup.coe_inv]
        group
      have h1 : (eBasisMulEquiv hz hz' μ ν hμν hνμ y : G') =
          (e r : G') * (eBasisMulEquiv hz hz' μ ν hμν hνμ w : G') * (e r : G')⁻¹ :=
        ih w y hw'
      rw [show (e r⁻¹ : G') = (e r : G')⁻¹ from by rw [map_inv, Subgroup.coe_inv]]
      rw [h1]
      group
  intro r
  exact key r (hgen ▸ Subgroup.mem_top r)

theorem sq_eElt_mul {n d : ℕ} {Z : Subgroup G} {f : Fin n → G} {z : Fin d → G}
    (hz : IsEBasisOf Z z) (hzf : ∀ t i, z t * f i = f i * z t)
    {sq : Fin n → Fin d → ZMod 2} {cm : Fin n → Fin n → Fin d → ZMod 2}
    (hsq : ∀ i, f i ^ 2 = eElt z (sq i)) (hcm : ∀ i j, i < j → ⁅f j, f i⁆ = eElt z (cm i j))
    (v : Fin n → ZMod 2) {y : G} (hy : y ∈ Z) (hyf : ∀ i, y * f i = f i * y) :
    (eElt f v * y) ^ 2 = eElt z (quadMapOfCoeffs sq cm v) := by
  obtain ⟨u, rfl⟩ := hz.span y hy
  have hy2 : eElt z u * eElt z u = 1 := by
    rw [← eElt_add hz.ebasis.sq hz.ebasis.comm u u, add_self_zmod2, eElt_zero]
  have hc : Commute (eElt f v) (eElt z u) :=
    commute_eElt (v := z)
      (fun t => (commute_eElt (v := f) (fun i => hzf t i) v).symm) u
  calc (eElt f v * eElt z u) ^ 2
      = (eElt f v) ^ 2 * (eElt z u) ^ 2 := Commute.mul_pow hc 2
    _ = eElt z (quadMapOfCoeffs sq cm v) := by
        rw [pow_two (eElt z u), hy2, mul_one]
        exact eElt_sq hz.ebasis.sq hz.ebasis.comm hzf hsq hcm v

end CFSG.GroupTheory

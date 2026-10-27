module

public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.KGFactC31NatSec

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

theorem eElt_append {Γ : Type*} [Group Γ] {m k : ℕ} (v : Fin m → Γ) (w : Fin k → Γ)
    (c : Fin m → ZMod 2) (d : Fin k → ZMod 2) :
    eElt (Fin.append v w) (Fin.append c d) = eElt v c * eElt w d := by
  unfold eElt
  have h : (fun i => Fin.append v w i ^ (Fin.append c d i).val) =
      Fin.append (fun i => v i ^ (c i).val) (fun i => w i ^ (d i).val) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right, Fin.append_right]
  rw [h, List.ofFn_fin_append, List.prod_append]

theorem eElt_mul_comm {M : Type*} [CommGroup M] {n : ℕ} (x y : Fin n → M) (c : Fin n → ZMod 2) :
    eElt (fun i => x i * y i) c = eElt x c * eElt y c := by
  simp only [eElt, List.prod_ofFn, mul_pow, Finset.prod_mul_distrib]

variable {G : Type} [Group G]

theorem eElt_mul_of_le {V : Subgroup G} [IsMulCommutative ↥V] {n : ℕ} {x y : Fin n → G}
    (hx : ∀ i, x i ∈ V) (hy : ∀ i, y i ∈ V) (c : Fin n → ZMod 2) :
    eElt (fun i => x i * y i) c = eElt x c * eElt y c := by
  let x' : Fin n → ↥V := fun i => ⟨x i, hx i⟩
  let y' : Fin n → ↥V := fun i => ⟨y i, hy i⟩
  have h1 := map_eElt (v := fun i => x' i * y' i) V.subtype c
  have h2 := map_eElt (v := x') V.subtype c
  have h3 := map_eElt (v := y') V.subtype c
  rw [eElt_mul_comm] at h1
  simp only [Subgroup.coe_subtype, map_mul, Subgroup.coe_mul] at h1 h2 h3
  rw [← h2, ← h3]
  exact h1.symm

variable {a₀ a₁ : Fin 3 → G} (ha₀ : EBasis a₀) (ha₁ : EBasis a₁)
  (hw : EBasis (Fin.append a₀ a₁)) (ha₂ : EBasis fun i => a₀ i * a₁ i)

include hw in
theorem a0_mem (i : Fin 3) : a₀ i ∈ eSub hw := by
  have h := mem_eSub hw (Fin.castAdd 3 i)
  rwa [Fin.append_left] at h

include hw in
theorem a1_mem (i : Fin 3) : a₁ i ∈ eSub hw := by
  have h := mem_eSub hw (Fin.natAdd 3 i)
  rwa [Fin.append_right] at h

include hw in
theorem eSub_a0_le : eSub ha₀ ≤ eSub hw := by
  rw [eSub_eq_closure ha₀, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact a0_mem hw i

include hw in
theorem eSub_a1_le : eSub ha₁ ≤ eSub hw := by
  rw [eSub_eq_closure ha₁, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact a1_mem hw i

include hw in
theorem isMulCommutative_eSub_append : IsMulCommutative ↥(eSub hw) :=
  IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm hw x y hx hy

include ha₁ hw in
theorem a1_not_mem_a0 (i : Fin 3) : a₁ i ∉ eSub ha₀ := by
  intro h
  obtain ⟨c, hc⟩ := (mem_eSub_iff ha₀ _).mp h
  have h1 : eElt (Fin.append a₀ a₁) (Fin.append c (Pi.single i 1)) = 1 := by
    rw [eElt_append, hc, eElt_single, ha₁.sq]
  have h2 := congrFun (hw.ne_one _ h1) (Fin.natAdd 3 i)
  rw [Fin.append_right, Pi.single_eq_same, Pi.zero_apply] at h2
  exact one_ne_zero h2

include ha₀ hw in
theorem a0_not_mem_a1 (i : Fin 3) : a₀ i ∉ eSub ha₁ := by
  intro h
  obtain ⟨c, hc⟩ := (mem_eSub_iff ha₁ _).mp h
  have h1 : eElt (Fin.append a₀ a₁) (Fin.append (Pi.single i 1) c) = 1 := by
    rw [eElt_append, hc, eElt_single, ha₀.sq]
  have h2 := congrFun (hw.ne_one _ h1) (Fin.castAdd 3 i)
  rw [Fin.append_left, Pi.single_eq_same, Pi.zero_apply] at h2
  exact one_ne_zero h2

include hw in
theorem diag_of_mem {x : G} (hx : x ∈ eSub ha₂) : ∃ e, x = eElt a₀ e * eElt a₁ e := by
  haveI := isMulCommutative_eSub_append hw
  obtain ⟨e, rfl⟩ := (mem_eSub_iff ha₂ x).mp hx
  exact ⟨e, eElt_mul_of_le (V := eSub hw) (a0_mem hw) (a1_mem hw) e⟩

include ha₀ ha₁ hw ha₂ in
theorem eMat_eq_of_diag {g : G} (hg₀ : g ∈ eNorm ha₀) (hg₁ : g ∈ eNorm ha₁)
    (hg₂ : g ∈ eNorm ha₂) : eMat ha₁ ⟨g, hg₁⟩ = eMat ha₀ ⟨g, hg₀⟩ := by
  ext r i
  set c := eCo ha₀ ⟨g, hg₀⟩ (Pi.single i 1) with hc
  set d := eCo ha₁ ⟨g, hg₁⟩ (Pi.single i 1) with hd
  have h0 : g * a₀ i * g⁻¹ = eElt a₀ c := by
    rw [hc, eElt_eCo, eElt_single]
  have h1 : g * a₁ i * g⁻¹ = eElt a₁ d := by
    rw [hd, eElt_eCo, eElt_single]
  have hmem : g * (a₀ i * a₁ i) * g⁻¹ ∈ eSub ha₂ :=
    (Subgroup.mem_normalizer_iff.mp hg₂ _).mp (mem_eSub ha₂ i)
  obtain ⟨e, he⟩ := diag_of_mem hw ha₂ hmem
  have h2 : g * (a₀ i * a₁ i) * g⁻¹ = (g * a₀ i * g⁻¹) * (g * a₁ i * g⁻¹) := by group
  rw [h2, h0, h1] at he
  have h3 : eElt (Fin.append a₀ a₁) (Fin.append c d) = eElt (Fin.append a₀ a₁) (Fin.append e e) := by
    rw [eElt_append, eElt_append, he]
  have h4 := eElt_injective hw h3
  have hce : c = e := funext fun j => by
    have := congrFun h4 (Fin.castAdd 3 j)
    rwa [Fin.append_left, Fin.append_left] at this
  have hde : d = e := funext fun j => by
    have := congrFun h4 (Fin.natAdd 3 j)
    rwa [Fin.append_right, Fin.append_right] at this
  show d r = c r
  rw [hce, hde]

@[expose] def unflat6 (c : Fin 6 → ZMod 2) : Fin 2 → Fin 3 → ZMod 2 :=
  ![fun j => c (Fin.castAdd 3 j), fun j => c (Fin.natAdd 3 j)]

theorem append_unflat6 (c : Fin 6 → ZMod 2) :
    Fin.append (m := 3) (n := 3) (unflat6 c 0) (unflat6 c 1) = c := by
  funext i
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

@[expose] def flat6Equiv : (Fin 2 → Fin 3 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun d := Fin.append (m := 3) (n := 3) (d 0) (d 1)
  invFun := unflat6
  left_inv d := by
    funext i
    fin_cases i
    · funext j
      show Fin.append (d 0) (d 1) (Fin.castAdd 3 j) = d 0 j
      rw [Fin.append_left]
    · funext j
      show Fin.append (d 0) (d 1) (Fin.natAdd 3 j) = d 1 j
      rw [Fin.append_right]
  right_inv := append_unflat6
  map_add' d d' := by
    funext i
    refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
    · show Fin.append ((d + d') 0) ((d + d') 1) (Fin.castAdd 3 j) =
        Fin.append (d 0) (d 1) (Fin.castAdd 3 j) + Fin.append (d' 0) (d' 1) (Fin.castAdd 3 j)
      rw [Fin.append_left, Fin.append_left, Fin.append_left]
      rfl
    · show Fin.append ((d + d') 0) ((d + d') 1) (Fin.natAdd 3 j) =
        Fin.append (d 0) (d 1) (Fin.natAdd 3 j) + Fin.append (d' 0) (d' 1) (Fin.natAdd 3 j)
      rw [Fin.append_right, Fin.append_right, Fin.append_right]
      rfl

@[expose] noncomputable def betaEquiv6 : ↥(eSub hw) ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  (ecoords hw).trans (AddEquiv.toMultiplicative flat6Equiv).symm

theorem toAdd_betaEquiv6 (x : ↥(eSub hw)) :
    Multiplicative.toAdd (betaEquiv6 hw x) = unflat6 (Multiplicative.toAdd (ecoords hw x)) := rfl

include ha₀ ha₁ ha₂ in
theorem coords_conj {g : G} (hgV : g ∈ eNorm hw) (hg₀ : g ∈ eNorm ha₀) (hg₁ : g ∈ eNorm ha₁)
    (hg₂ : g ∈ eNorm ha₂) (u v : ↥(eSub hw)) (huv : (v : G) = g * u * g⁻¹) :
    Multiplicative.toAdd (ecoords hw v) = Fin.append (m := 3) (n := 3)
      (eMat ha₀ ⟨g, hg₀⟩ *ᵥ unflat6 (Multiplicative.toAdd (ecoords hw u)) 0)
      (eMat ha₀ ⟨g, hg₀⟩ *ᵥ unflat6 (Multiplicative.toAdd (ecoords hw u)) 1) := by
  apply eElt_injective hw
  rw [eElt_ecoords, eElt_append, huv, ← eElt_ecoords hw u,
    ← append_unflat6 (Multiplicative.toAdd (ecoords hw u)), eElt_append]
  rw [show g * (eElt a₀ (unflat6 (Multiplicative.toAdd (ecoords hw u)) 0) *
      eElt a₁ (unflat6 (Multiplicative.toAdd (ecoords hw u)) 1)) * g⁻¹ =
      (g * eElt a₀ (unflat6 (Multiplicative.toAdd (ecoords hw u)) 0) * g⁻¹) *
        (g * eElt a₁ (unflat6 (Multiplicative.toAdd (ecoords hw u)) 1) * g⁻¹) from by group]
  rw [conj_eq_eElt_mulVec ha₀ ⟨g, hg₀⟩, conj_eq_eElt_mulVec ha₁ ⟨g, hg₁⟩,
    eMat_eq_of_diag ha₀ ha₁ hw ha₂ hg₀ hg₁ hg₂]
  rfl

include ha₀ ha₁ ha₂ in
theorem KConfig.conclK_of_e64 [Finite G] {L V MK : Subgroup G} (h : KConfig G L V MK)
    (hV : V = eSub hw) (hL0 : L ≤ eNorm ha₀) (hL1 : L ≤ eNorm ha₁) (hL2 : L ≤ eNorm ha₂)
    (hC0 : Subgroup.centralizer (eSub ha₀ : Set G) ⊓ eNorm ha₁ ≤ eSub hw) :
    ConclK G L V MK := by
  subst hV
  unfold ConclK
  haveI hcommV : IsMulCommutative ↥(eSub hw) := isMulCommutative_eSub_append hw
  have hA0V := eSub_a0_le ha₀ hw
  have hA1V := eSub_a1_le ha₁ hw
  have hV2 : IsPGroup 2 ↥(eSub hw) := IsPGroup.of_card (n := 6) (card_eSub hw)
  have hVL : eSub hw ≤ L := h.le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hLC : L ⊓ Subgroup.centralizer (eSub ha₀ : Set G) = eSub hw := by
    refine le_antisymm (fun x hx => hC0 ⟨hx.2, hL1 hx.1⟩) fun x hx =>
      ⟨hVL hx, Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hw y x (hA0V hy) hx⟩
  let α := E16.eNHom ha₀ hL0
  have hθ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (eSub ha₀ : Set G) :=
    fun l => E16.eNHom_eq_one_iff ha₀ hL0 l
  haveI : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect h.perfect⟩
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hsurj : Function.Surjective α := by
    rw [← MonoidHom.range_eq_top]
    rcases CFSG.Quasithin.J4Fam.eq_bot_or_top_of_isPerfect
        (fun H hH => CFSG.Quasithin.J4Fam.solvable_of_ne_top_card168 E8.card_statedSL3 hH)
        (Group.IsPerfect.range α) with hb | ht
    · exfalso
      have hLC : L ≤ Subgroup.centralizer (eSub ha₀ : Set G) := fun l hl => (hθ ⟨l, hl⟩).mp (by
        have : α ⟨l, hl⟩ ∈ α.range := ⟨_, rfl⟩
        rwa [hb, Subgroup.mem_bot] at this)
      have hLbot : L = ⊥ := eq_bot_of_perfect_of_isPGroup h.perfect
        (hV2.to_le fun l hl => hC0 ⟨hLC hl, hL1 hl⟩)
      apply h.ne_bot
      rw [eq_bot_iff]
      exact h.le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLbot.le)
    · exact ht
  have hker : α.ker = (eSub hw).subgroupOf L := ker_eNHom ha₀ hL0 hLC
  have hO : pCoreOf 2 L = eSub hw := by
    refine le_antisymm (fun x hx => ?_) h.le_pCoreOf
    rw [← hLC]
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 L hx,
      Subgroup.centralizer_le hA0V (h.pCoreOf_le hx)⟩
  have hpk : CFSG.pCore 2 ↥L = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf' L, hO, hker]
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have hpsl : IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := E8.isPSL_of_equiv3 eQ
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) := Or.inr (Or.inl hLM)
  let α₁ := E16.eNHom ha₁ hL1
  have hα₁ : α₁ = α := MonoidHom.ext fun l => Subtype.ext (Units.ext (by
    rw [E16.eNHom_coe, E16.eNHom_coe]
    exact eMat_eq_of_diag ha₀ ha₁ hw ha₂ (hL0 l.2) (hL1 l.2) (hL2 l.2)))
  let β : ↥(eSub hw) →* Multiplicative (Fin 2 → Fin 3 → ZMod 2) := (betaEquiv6 hw).toMonoidHom
  have hsum : IsSumOfNaturalModules L (eSub hw) ⊥ ((eSub hw).subgroupOf L)
      (StatedSL 3 (ZMod 2)) false 2 := by
    refine ⟨α, hsurj, hker, h.le_normalizer, bot_le, β, (betaEquiv6 hw).surjective, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
      exact (betaEquiv6 hw).injective
    · intro a u v huv i
      show Multiplicative.toAdd (betaEquiv6 hw v) i =
        (((α a : ↥(StatedSL 3 (ZMod 2))) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (betaEquiv6 hw u) i
      rw [E16.eNHom_coe, toAdd_betaEquiv6, toAdd_betaEquiv6,
        coords_conj ha₀ ha₁ hw ha₂ (h.le_normalizer a.2) (hL0 a.2) (hL1 a.2) (hL2 a.2) u v huv]
      fin_cases i
      · funext j
        show Fin.append _ _ (Fin.castAdd 3 j) = _
        rw [Fin.append_left]
        rfl
      · funext j
        show Fin.append _ _ (Fin.natAdd 3 j) = _
        rw [Fin.append_right]
        rfl
  have hFFL : IsFFModule (autOn L (eSub hw)) :=
    FFn.isFFModule_autOn_of_sum (n := 2) (k := 2) (by decide) (by norm_num) le_rfl hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub hw : Set G)) (eSub hw)) :=
    isFFModule_of_le (autOn_mono' h.le_normalizer) hFFL
  haveI hc0 : IsMulCommutative ↥(eSub ha₀) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm ha₀ x y hx hy
  haveI hc1 : IsMulCommutative ↥(eSub ha₁) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm ha₁ x y hx hy
  have hbin0 : BinaryNaturalSL (V := ↥(eSub ha₀)) (autOn L (eSub ha₀)) ⊤ ⊥ 3 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv hL0 (FFModel.nat (StatedSL 3 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot) (fun _ => rfl) α hsurj
      (fun a ha => (hθ a).mp ha)
      (MulEquiv.ofBijective (ecoords ha₀).toMonoidHom
        ⟨(ecoords ha₀).injective, (ecoords ha₀).surjective⟩)
      (fun a w w' hw' => by
        show (ecoords ha₀) w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α a) ((ecoords ha₀) w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd ((ecoords ha₀) w') = (((α a : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd ((ecoords ha₀) w)
        rw [E16.eNHom_coe]
        exact ecoords_conj ha₀ ⟨a, hL0 a.2⟩ w w' hw')
  have hsurj₁ : Function.Surjective α₁ := by rw [hα₁]; exact hsurj
  have hbin1 : BinaryNaturalSL (V := ↥(eSub ha₁)) (autOn L (eSub ha₁)) ⊤ ⊥ 3 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv hL1 (FFModel.nat (StatedSL 3 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot) (fun _ => rfl) α₁ hsurj₁
      (fun a ha => (E16.eNHom_eq_one_iff ha₁ hL1 a).mp ha)
      (MulEquiv.ofBijective (ecoords ha₁).toMonoidHom
        ⟨(ecoords ha₁).injective, (ecoords ha₁).surjective⟩)
      (fun a w w' hw' => by
        show (ecoords ha₁) w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α₁ a) ((ecoords ha₁) w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd ((ecoords ha₁) w') = (((α₁ a : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd ((ecoords ha₁) w)
        rw [E16.eNHom_coe]
        exact ecoords_conj ha₁ ⟨a, hL1 a.2⟩ w w' hw')
  let φ : ↥(eSub ha₀) ≃* ↥(eSub ha₁) := (ecoords ha₀).trans (ecoords ha₁).symm
  have hφ : IsLEquiv L φ := by
    intro l hl a a' ha'
    have h1 := ecoords_conj ha₀ ⟨l, hL0 hl⟩ a a' ha'
    have h2 : ((φ a' : ↥(eSub ha₁)) : G) = eElt a₁ (Multiplicative.toAdd (ecoords ha₀ a')) := by
      rw [← eElt_ecoords ha₁ (φ a')]
      show eElt a₁ (Multiplicative.toAdd ((ecoords ha₁) ((ecoords ha₁).symm ((ecoords ha₀) a')))) = _
      rw [MulEquiv.apply_symm_apply]
    have h3 : ((φ a : ↥(eSub ha₁)) : G) = eElt a₁ (Multiplicative.toAdd (ecoords ha₀ a)) := by
      rw [← eElt_ecoords ha₁ (φ a)]
      show eElt a₁ (Multiplicative.toAdd ((ecoords ha₁) ((ecoords ha₁).symm ((ecoords ha₀) a)))) = _
      rw [MulEquiv.apply_symm_apply]
    rw [h2, h3, h1, conj_eq_eElt_mulVec ha₁ ⟨l, hL1 hl⟩,
      eMat_eq_of_diag ha₀ ha₁ hw ha₂ (hL0 hl) (hL1 hl) (hL2 hl)]
  let W : Fin 2 → Subgroup G := ![eSub ha₀, eSub ha₁]
  have hdisj : Disjoint (eSub ha₀) (eSub ha₁) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx0, hx1⟩
    obtain ⟨c, rfl⟩ := (mem_eSub_iff ha₀ x).mp hx0
    obtain ⟨d, hd⟩ := (mem_eSub_iff ha₁ _).mp hx1
    have h1 : eElt (Fin.append a₀ a₁) (Fin.append c 0) = eElt (Fin.append a₀ a₁) (Fin.append 0 d) := by
      rw [eElt_append, eElt_append, eElt_zero, eElt_zero, mul_one, one_mul, hd]
    have h2 := eElt_injective hw h1
    have hc : c = 0 := funext fun j => by
      have := congrFun h2 (Fin.castAdd 3 j)
      rwa [Fin.append_left, Fin.append_left] at this
    rw [Subgroup.mem_bot, hc, eElt_zero]
  have hsupV : eSub ha₀ ⊔ eSub ha₁ = eSub hw := by
    refine le_antisymm (sup_le hA0V hA1V) ?_
    rw [eSub_eq_closure hw, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact Subgroup.mem_sup_left (mem_eSub ha₀ j)
    · rw [Fin.append_right]
      exact Subgroup.mem_sup_right (mem_eSub ha₁ j)
  have hnat : IsNaturalSumUnder 3 L (eSub hw) := by
    refine ⟨2, W, by norm_num, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hA0V, hL0, ⟨hc0, hbin0⟩⟩
      · exact ⟨hA1V, hL1, ⟨hc1, hbin1⟩⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
      · exact isXSectionIso₂_of_isLEquiv hφ
      · exact isXSectionIso₂_of_isLEquiv (hφ.symm hL0)
      · exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · exact (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
        (fun k => by fin_cases k <;> simp)).mpr hdisj
    · refine le_antisymm (iSup_le fun i => ?_) ?_
      · fin_cases i
        · exact hA0V
        · exact hA1V
      · rw [← hsupV]
        exact sup_le (le_iSup W 0) (le_iSup W 1)
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro _
    exact hnat
  · intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  · rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  · intro h3 _
    have h1 := LieModel.card_psu_three_three h3
    rw [hcardX] at h1
    norm_num at h1

end CFSG.SectionRank.QTK.Insp443

end

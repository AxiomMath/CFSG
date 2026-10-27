module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderMax
public import CFSG.HardMathSupport.RichardWeiss.Proving.EqualityOffender
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.HardMathSupport.RichardWeiss.Proving
open scoped commutatorElement

variable {G : Type} [Group G]

structure EOffenderData (S V : Subgroup G) : Prop where
  hVel : IsElemAbelian 2 V
  hVS : V ≤ S
  hSN : S ≤ Subgroup.normalizer (V : Set G)
  hle : ∀ A, IsMaxElemAbelian S A →
    (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V

@[expose] def cenS (S V : Subgroup G) : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ S

@[expose] def eOf (S V : Subgroup G) : Subgroup G := omegaOneCenterOf (thompsonJ (cenS S V))

variable {S V : Subgroup G}

theorem V_le_cenS (h : EOffenderData S V) : V ≤ cenS S V :=
  le_inf (fun _ hv => Subgroup.mem_centralizer_iff.2 fun _ hx =>
    (isElemAbelian_comm' h.hVel hx hv)) h.hVS

theorem EOffenderData.sup_le_cenS (h : EOffenderData S V) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ cenS S V :=
  sup_le (fun _ hx => ⟨hx.2, hA.1 hx.1⟩) (V_le_cenS h)

theorem eOf_le_thompsonJ (S V : Subgroup G) : eOf S V ≤ thompsonJ (cenS S V) :=
  omegaOneCenterOf_le _

theorem thompsonJ_cenS_le (S V : Subgroup G) : thompsonJ (cenS S V) ≤ cenS S V :=
  thompsonJ_le_self _

theorem isElemAbelian_eOf (S V : Subgroup G) : IsElemAbelian 2 (eOf S V) :=
  B2F.isElemAbelian_omegaOneCenterOf _

theorem eOf_comm_thompsonJ (S V : Subgroup G) {x y : G} (hx : x ∈ eOf S V)
    (hy : y ∈ thompsonJ (cenS S V)) : y * x = x * y :=
  (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf _ hx).2 y hy)

theorem eOf_le_cenS (S V : Subgroup G) : eOf S V ≤ cenS S V :=
  (eOf_le_thompsonJ S V).trans (thompsonJ_cenS_le S V)

variable [Finite G]

theorem EOffenderData.eq_relIndex (h : EOffenderData S V) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    (Subgroup.centralizer (A : Set G)).relIndex V =
      (Subgroup.centralizer (V : Set G)).relIndex A := by
  have h1 := h.hle A hA
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left] at h1
  exact le_antisymm (relIndex_le_of_isMaxElemAbelian hA h.hVel h.hVS) h1

theorem EOffenderData.isMax_sup (h : EOffenderData S V) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian (cenS S V) ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  have hmax := isMaxElemAbelian_sup_of_relIndex_le hA h.hVel h.hVS (h.hle A hA)
  exact ⟨h.sup_le_cenS hA, hmax.2.1, fun B hB hBe => hmax.2.2 B (hB.trans inf_le_right) hBe⟩

theorem EOffenderData.V_le_eOf (h : EOffenderData S V) : V ≤ eOf S V := by
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hA1 := h.isMax_sup hA
  have hVJ : V ≤ thompsonJ (cenS S V) :=
    sup_le_iff.1 (le_iSup₂_of_le _ hA1 le_rfl : _ ≤ thompsonJ (cenS S V)) |>.2
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hVJ hv, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩,
    h.hVel.2 v hv⟩
  have : g ∈ Subgroup.centralizer (V : Set G) := (thompsonJ_cenS_le S V hg).1
  exact (Subgroup.mem_centralizer_iff.1 this v hv).symm

theorem EOffenderData.eOf_le_sup (h : EOffenderData S V) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    eOf S V ≤ V ⊔ (eOf S V ⊓ Subgroup.centralizer (A : Set G)) := by
  classical
  set E := eOf S V with hE
  set K := A ⊓ Subgroup.centralizer (V : Set G) with hK
  have hA1 := h.isMax_sup hA
  have hKJ : K ≤ thompsonJ (cenS S V) :=
    (le_sup_left : K ≤ K ⊔ V).trans (le_iSup₂_of_le _ hA1 le_rfl)
  have hVE : V ≤ E := h.V_le_eOf
  have hES : E ≤ S := (eOf_le_cenS S V).trans inf_le_right
  have hKE : K ≤ A ⊓ Subgroup.centralizer (E : Set G) :=
    le_inf inf_le_left fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      (eOf_comm_thompsonJ S V hy (hKJ hx)).symm
  have hEel := isElemAbelian_eOf S V
  have b2 := relIndex_le_of_isMaxElemAbelian hA hEel hES
  have hne : ∀ H' : Subgroup G, ∀ L' : Subgroup G, H'.relIndex L' ≠ 0 := fun H' L' => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have b1 : (Subgroup.centralizer (E : Set G)).relIndex A ≤
      (Subgroup.centralizer (V : Set G)).relIndex A := by
    have := Subgroup.relIndex_le_of_le_left (L := A)
      (H := A ⊓ Subgroup.centralizer (V : Set G)) (K := A ⊓ Subgroup.centralizer (E : Set G))
      hKE (hne _ _)
    rwa [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left] at this
  have b3 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (A : Set G))
    hVE (hne _ _)
  have hq := h.eq_relIndex hA
  have hEq : (Subgroup.centralizer (A : Set G)).relIndex E =
      (Subgroup.centralizer (A : Set G)).relIndex V := by
    refine le_antisymm ?_ b3
    calc (Subgroup.centralizer (A : Set G)).relIndex E
        ≤ (Subgroup.centralizer (E : Set G)).relIndex A := b2
      _ ≤ (Subgroup.centralizer (V : Set G)).relIndex A := b1
      _ = _ := hq.symm
  set X := E ⊓ Subgroup.centralizer (A : Set G) with hX
  have hcomm : ∀ x ∈ X, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_omegaOneCenterOf hx.1 (hVE hy)
  have hprod := CFSG.Quasithin.H13.A7.card_sup_mul_card_inf_of_commute (X := X) (Y := V) hcomm
  have hXV : X ⊓ V = Subgroup.centralizer (A : Set G) ⊓ V := by
    ext x
    simp only [Subgroup.mem_inf, hX]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨⟨hVE h3, h2⟩, h3⟩⟩
  have hV := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G)) (K := V)
  have hE' := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G)) (K := E)
  rw [hXV] at hprod
  rw [hEq] at hE'
  have hXc : Nat.card X = Nat.card (Subgroup.centralizer (A : Set G) ⊓ E : Subgroup G) := by
    rw [hX, inf_comm]
  have hpos : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := Nat.card_pos
  have hW : Nat.card (X ⊔ V : Subgroup G) = Nat.card E := by
    have h1 : Nat.card (X ⊔ V : Subgroup G) *
        Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) =
        Nat.card E * Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := by
      rw [hprod, ← hE', ← hV, hXc]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hWE : X ⊔ V ≤ E := sup_le inf_le_left hVE
  have : X ⊔ V = E := Subgroup.eq_of_le_of_card_ge hWE (le_of_eq hW.symm)
  rw [sup_comm] at this
  exact this.ge

theorem EOffenderData.commutator_le (h : EOffenderData S V) :
    ⁅eOf S V, thompsonJ S⁆ ≤ V := by
  classical
  have hVN : ∀ y ∈ S, ∀ c ∈ V, y * c * y⁻¹ ∈ V := fun y hy c hc =>
    (Subgroup.mem_normalizer_iff.1 (h.hSN hy) c).1 hc
  have hEC : ∀ x ∈ eOf S V, ∀ c ∈ V, x * c * x⁻¹ = c := fun x hx c hc => by
    have : x ∈ Subgroup.centralizer (V : Set G) := (eOf_le_cenS S V hx).1
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 this c hc).symm
  have hgen : ∀ A, IsMaxElemAbelian S A → ∀ y ∈ A, y ∈ S ∧
      ∀ x ∈ eOf S V, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro A hA y hy
    refine ⟨hA.1 hy, fun x hx => ?_⟩
    have hxs := h.eOf_le_sup hA hx
    have hxs' : x ∈ Subgroup.closure
        ((V : Set G) ∪ ((eOf S V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)) := by
      rw [← Subgroup.sup_eq_closure]; exact hxs
    have hmain : ∀ x (hx : x ∈ Subgroup.closure
        ((V : Set G) ∪ ((eOf S V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G))),
        x ∈ eOf S V ∧ x * y * x⁻¹ * y⁻¹ ∈ V := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hxV | hxX
        · refine ⟨h.V_le_eOf hxV, ?_⟩
          have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [e]
          exact V.mul_mem hxV (hVN y (hA.1 hy) x⁻¹ (V.inv_mem hxV))
        · refine ⟨hxX.1, ?_⟩
          have hc : y * x = x * y := Subgroup.mem_centralizer_iff.1 hxX.2 y hy
          rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
          exact V.one_mem
      | one => exact ⟨Subgroup.one_mem _, by simp⟩
      | mul x x' hx hx' ihx ihx' =>
        obtain ⟨hxE, hq⟩ := ihx
        obtain ⟨hx'E, hq'⟩ := ihx'
        refine ⟨Subgroup.mul_mem _ hxE hx'E, ?_⟩
        have e : (x * x') * y * (x * x')⁻¹ * y⁻¹ =
            (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
        rw [e, hEC x hxE _ hq']
        exact V.mul_mem hq' hq
      | inv x hx ih =>
        obtain ⟨hxE, hq⟩ := ih
        refine ⟨Subgroup.inv_mem _ hxE, ?_⟩
        have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e, hEC x⁻¹ (Subgroup.inv_mem _ hxE) _ (V.inv_mem hq)]
        exact V.inv_mem hq
    exact (hmain x hxs').2
  have hone : (1 : G) ∈ S ∧ ∀ x ∈ eOf S V, x * 1 * x⁻¹ * (1 : G)⁻¹ ∈ V :=
    ⟨S.one_mem, fun x _ => by simp⟩
  have hmul : ∀ y y' : G, (y ∈ S ∧ ∀ x ∈ eOf S V, x * y * x⁻¹ * y⁻¹ ∈ V) →
      (y' ∈ S ∧ ∀ x ∈ eOf S V, x * y' * x⁻¹ * y'⁻¹ ∈ V) →
      (y * y' ∈ S ∧ ∀ x ∈ eOf S V, x * (y * y') * x⁻¹ * (y * y')⁻¹ ∈ V) := by
    rintro y y' ⟨hyS, hy⟩ ⟨hy'S, hy'⟩
    refine ⟨S.mul_mem hyS hy'S, fun x hx => ?_⟩
    have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
    rw [e]
    exact V.mul_mem (hy x hx) (hVN y hyS _ (hy' x hx))
  have hJ : ∀ y ∈ thompsonJ S, y ∈ S ∧ ∀ x ∈ eOf S V, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro y hy
    let P : G → Prop := fun y => y ∈ S ∧ ∀ x ∈ eOf S V, x * y * x⁻¹ * y⁻¹ ∈ V
    unfold thompsonJ at hy
    refine Subgroup.iSup_induction (C := P)
      (fun A : Subgroup G => ⨆ (_ : IsMaxElemAbelian S A), A) hy (fun A y hy => ?_) hone hmul
    exact Subgroup.iSup_induction (C := P) (fun _ : IsMaxElemAbelian S A => A) hy
      (fun hA y hy => hgen A hA y hy) hone hmul
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact (hJ y hy).2 x hx

theorem EOffenderData.thompsonJ_cenS_le_thompsonJ (h : EOffenderData S V) :
    thompsonJ (cenS S V) ≤ thompsonJ S := by
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hA1S : IsMaxElemAbelian S ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
    isMaxElemAbelian_sup_of_relIndex_le hA h.hVel h.hVS (h.hle A hA)
  have hA1Q := h.isMax_sup hA
  refine iSup₂_le fun B hB => ?_
  have hBS : IsMaxElemAbelian S B :=
    ⟨hB.1.trans inf_le_right, hB.2.1, fun C hC hCe =>
      (hA1S.2.2 C hC hCe).trans (hB.2.2 _ hA1Q.1 hA1Q.2.1)⟩
  exact le_iSup₂_of_le B hBS le_rfl

theorem EOffenderData.omegaOneCenter_le_eOf (h : EOffenderData S V) :
    omegaOneCenterOf (thompsonJ S) ≤ eOf S V := by
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hA1S : IsMaxElemAbelian S ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
    isMaxElemAbelian_sup_of_relIndex_le hA h.hVel h.hVS (h.hle A hA)
  have hA1Q := h.isMax_sup hA
  have hJQ := h.thompsonJ_cenS_le_thompsonJ
  refine (Subgroup.closure_le _).2 ?_
  rintro z ⟨⟨hzJ, hzC⟩, hz2⟩
  have hzcomm : ∀ a ∈ thompsonJ S, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_iff.1 hzC a ha
  have hzS : z ∈ S := thompsonJ_le_self S hzJ
  have hA1J : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ thompsonJ S :=
    le_iSup₂_of_le _ hA1S le_rfl
  have hzA1 : z ∈ (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V :=
    mem_of_commute_isMaxElemAbelian hA1S hzS hz2 fun a ha => hzcomm a (hA1J ha)
  have hA1JQ : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ thompsonJ (cenS S V) :=
    le_iSup₂_of_le _ hA1Q le_rfl
  have hzJQ : z ∈ thompsonJ (cenS S V) := hA1JQ hzA1
  exact Subgroup.subset_closure ⟨⟨hzJQ, Subgroup.mem_centralizer_iff.2 fun g hg =>
    hzcomm g (hJQ hg)⟩, hz2⟩

omit [Finite G] in
theorem mem_normalizer_thompsonJ_of_mem_normalizer {Q : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) :
    x ∈ Subgroup.normalizer (thompsonJ Q : Set G) := by
  have hmap : Q.map (MulAut.conj x).toMonoidHom = Q := by
    ext y
    rw [Subgroup.mem_map_equiv]
    have := Subgroup.mem_normalizer_iff.1 hx ((MulAut.conj x).symm y)
    simpa [MulAut.conj_symm_apply, mul_assoc] using this
  have hJ := thompsonJ_map_mulEquiv (MulAut.conj x) Q
  rw [hmap] at hJ
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : x * g * x⁻¹ ∈ (thompsonJ Q).map (MulAut.conj x).toMonoidHom := ⟨g, hg, by simp⟩
    rwa [hJ] at this
  · intro hg
    rw [← hJ] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    have : g' = g := by
      have h2 : x * g' * x⁻¹ = x * g * x⁻¹ := by simpa using hgg
      simpa using h2
    exact this ▸ hg'

omit [Finite G] in
theorem normalizer_le_normalizer_eOf (S V : Subgroup G) :
    Subgroup.normalizer (cenS S V : Set G) ≤ Subgroup.normalizer (eOf S V : Set G) :=
  fun _ hx => normalizer_le_normalizer_omegaOneCenterOf _
    (mem_normalizer_thompsonJ_of_mem_normalizer hx)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

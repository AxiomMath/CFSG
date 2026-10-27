module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

section Product

private theorem card_sup_mul_card_inf_of_normal' {G : Type*} [Group G] (A L : Subgroup G)
    [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem card_sup_mul_card_inf_aux {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

end Product

section Psi

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

@[expose] def psiAut (L : Subgroup (MulAut W)) (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : MulAut S :=
  (e.symm.trans (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAut L hb)
    (Subgroup.map_center_eq (conjAut L hb)))).trans e

theorem psiAut_mk (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (y : ↥L) :
    psiAut L e hb (e (QuotientGroup.mk y)) = e (QuotientGroup.mk (conjAut L hb y)) := by
  show e (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAut L hb)
    (Subgroup.map_center_eq (conjAut L hb)) (e.symm (e (QuotientGroup.mk y)))) = _
  rw [MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]

theorem mem_of_psiAut_inner [Finite W] (hW : ∀ w : W, w * w = 1) {E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    (e : CQ L ≃* S) {b : MulAut W} (hbE : b ∈ E) (s : S)
    (hs : ∀ x : S, psiAut L e (hE hbE) x = s * x * s⁻¹) : b ∈ L := by
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W)) := hE hbE
  let ψ : CQ L ≃* CQ L :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAut L hbN)
      (Subgroup.map_center_eq (conjAut L hbN))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center ↥L) (e.symm s)
  have hψ : ∀ q : CQ L, ψ q = QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹ := by
    intro q
    have h1 := hs (e q)
    have h1' : e (ψ q) = s * e q * s⁻¹ := by
      have : psiAut L e hbN (e q) = e (ψ (e.symm (e q))) := rfl
      rw [← h1, this, MulEquiv.symm_apply_apply]
    have h2 : e (ψ q) = e (QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hl, h1']
      simp
    exact e.injective h2
  set c : MulAut W := (l : MulAut W)⁻¹ * b with hc
  have hlN : (l : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.le_normalizer l.2
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normalizer (L : Set (MulAut W))).mul_mem
      ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hlN) hbN
  have hθ : ∀ x : ↥L, conjAut L hcN x = l⁻¹ * conjAut L hbN x * l := by
    intro x
    apply Subtype.ext
    show c * (x : MulAut W) * c⁻¹ = ((l : MulAut W)⁻¹) * (b * x * b⁻¹) * (l : MulAut W)
    rw [hc]
    group
  have hcentral : ∀ x : ↥L, x⁻¹ * conjAut L hcN x ∈ Subgroup.center ↥L := by
    intro x
    rw [← QuotientGroup.eq, hθ]
    have h3 : (QuotientGroup.mk (conjAut L hbN x) : CQ L) = ψ (QuotientGroup.mk x) := rfl
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h3, hψ]
    group
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun x => ⟨x⁻¹ * conjAut L hcN x, hcentral x⟩) (by
      intro x y
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (hcentral x) y⁻¹
      show (x * y)⁻¹ * conjAut L hcN (x * y) = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y)
      calc (x * y)⁻¹ * conjAut L hcN (x * y)
          = y⁻¹ * (x⁻¹ * conjAut L hcN x) * conjAut L hcN y := by
            rw [map_mul]; group
        _ = (x⁻¹ * conjAut L hcN x) * y⁻¹ * conjAut L hcN y := by rw [hz]
        _ = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y) := by group)
  have hfker : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hperf.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f g₁).2 (f g₂)).symm)
  have hcomm : ∀ x ∈ L, x * c = c * x := by
    intro x hx
    have h1 := f.mem_ker.1 (hfker (Subgroup.mem_top ⟨x, hx⟩))
    have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : MulAut W)) h1
    simp only [Subgroup.coe_one] at h2
    have h3 : (x : MulAut W)⁻¹ * (c * x * c⁻¹) = 1 := h2
    have h5 : c * x * c⁻¹ = x := (inv_mul_eq_one.1 h3).symm
    calc x * c = (c * x * c⁻¹) * c := by rw [h5]
      _ = c * x := by group
  have hcC : c ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.mem_centralizer_iff.2 hcomm
  have hcH : c ∈ L ⊔ E := Subgroup.mul_mem_sup (L.inv_mem l.2) hbE
  have hcL : c ∈ L := centralizer_inf_le hW hirr hE hEel ⟨hcH, hcC⟩
  have hbc : b = (l : MulAut W) * c := by rw [hc]; group
  rw [hbc]
  exact L.mul_mem l.2 hcL

theorem psiAut_one (e : CQ L ≃* S) (hb : (1 : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    psiAut L e hb = 1 := by
  ext x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hx : x = e (QuotientGroup.mk y) := by rw [hy]; simp
  rw [hx, psiAut_mk]
  show e (QuotientGroup.mk (conjAut L hb y)) = e (QuotientGroup.mk y)
  congr 2

theorem psiAut_mul (e : CQ L ≃* S) {b b' : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hb' : b' ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hbb' : b * b' ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    psiAut L e hbb' = psiAut L e hb * psiAut L e hb' := by
  ext x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hx : x = e (QuotientGroup.mk y) := by rw [hy]; simp
  rw [hx, MulAut.mul_apply, psiAut_mk, psiAut_mk, psiAut_mk]
  congr 2

@[expose] def psiHom (L : Subgroup (MulAut W)) (e : CQ L ≃* S) {E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) : ↥E →* MulAut S where
  toFun b := psiAut L e (hE b.2)
  map_one' := psiAut_one e _
  map_mul' b b' := psiAut_mul e (hE b.2) (hE b'.2) _

theorem psiHom_apply (e : CQ L ≃* S) {E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (b : ↥E) :
    psiHom L e hE b = psiAut L e (hE b.2) := rfl

end Psi

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_mul_card_inf_of_outer (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {k : ℕ}
    (hOut : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range)) :
    Nat.card E ≤ k * Nat.card ↥(E ⊓ L) := by
  classical
  have hfinW : Finite (MulAut W) := B42Disp.finite_mulAut
  have : Finite ↥L := inferInstance
  have : Finite (CQ L) := inferInstance
  have : Finite S := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) (fun f g h => MulEquiv.ext (congrFun h))
  let Φ : ↥E →* MulAut S := psiHom L e hE
  let B : Subgroup (MulAut S) := Φ.range
  let Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  have hBs : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by have := hEel.2 a a.2; simpa [pow_two] using this)
    rw [this, map_one]
  have hOutB := hOut B hBc hBs
  let M : Subgroup ↥E := Inn.comap Φ
  have hMN : M ≤ (E ⊓ L).subgroupOf E := by
    intro b hb
    obtain ⟨s, hs⟩ := hb
    refine (Subgroup.mem_subgroupOf).2 ⟨b.2, ?_⟩
    refine mem_of_psiAut_inner hW hperf hirr hE hEel e b.2 s fun x => ?_
    have h3 := congrArg (fun f : MulAut S => f x) hs
    simp only [MulAut.conj_apply] at h3
    exact h3.symm
  let Φ' : ↥E →* ↥B := Φ.rangeRestrict
  have hΦ' : Function.Surjective Φ' := Φ.rangeRestrict_surjective
  let K' : Subgroup ↥B := Inn.comap B.subtype
  have hM : M = K'.comap Φ' := rfl
  have hidx : M.index = K'.index := by
    rw [hM]; exact Subgroup.index_comap_of_surjective _ hΦ'
  have h1 := Subgroup.card_mul_index M
  have h2 := Subgroup.card_mul_index K'
  have hK' : Nat.card K' = Nat.card ↥(B ⊓ Inn) := by
    have : (B ⊓ Inn).subgroupOf B = K' := by
      ext x
      simp [Subgroup.mem_subgroupOf, K']
    rw [← this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hK'pos : 0 < Nat.card K' := Nat.card_pos
  have hEK : Nat.card ↥E * Nat.card K' = Nat.card ↥B * Nat.card M := by
    rw [← h1, ← h2, hidx]
    ring
  have hle : Nat.card ↥E * Nat.card K' ≤ (k * Nat.card M) * Nat.card K' := by
    rw [hEK]
    calc Nat.card ↥B * Nat.card M ≤ (k * Nat.card ↥(B ⊓ Inn)) * Nat.card M :=
          Nat.mul_le_mul_right _ hOutB
      _ = (k * Nat.card M) * Nat.card K' := by rw [hK']; ring
  have hEM : Nat.card ↥E ≤ k * Nat.card M := Nat.le_of_mul_le_mul_right hle hK'pos
  have hMc : Nat.card M ≤ Nat.card ↥((E ⊓ L).subgroupOf E) := Subgroup.card_le_of_le hMN
  have hNc : Nat.card ↥((E ⊓ L).subgroupOf E) = Nat.card ↥(E ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card ↥E ≤ k * Nat.card M := hEM
    _ ≤ k * Nat.card ↥(E ⊓ L) := Nat.mul_le_mul_left _ (hMc.trans hNc.le)

theorem card_sup_le_of_outer (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {k : ℕ}
    (hOut : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range)) :
    Nat.card ↥(L ⊔ E) ≤ k * Nat.card L := by
  have hfinW : Finite (MulAut W) := B42Disp.finite_mulAut
  have hEk := card_le_mul_card_inf_of_outer hW hperf hirr hE hEel e hOut
  have hprod := card_sup_mul_card_inf_aux hE
  rw [inf_comm] at hEk
  have hpos : 0 < Nat.card ↥(L ⊓ E) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [hprod]
  calc Nat.card ↥L * Nat.card ↥E ≤ Nat.card ↥L * (k * Nat.card ↥(L ⊓ E)) :=
        Nat.mul_le_mul_left _ hEk
    _ = k * Nat.card ↥L * Nat.card ↥(L ⊓ E) := by ring

theorem exclusion_of_card_lt_of_outer (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hL : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) {S : Type} [Group S] (e : CQ L ≃* S) {k : ℕ}
    (hOut : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range))
    (hlt : k * (Nat.card (Subgroup.center ↥L) * Nat.card S) < Nat.card W) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have hfinW : Finite (MulAut W) := B42Disp.finite_mulAut
  have hperf : Group.IsPerfect ↥L := hL.1
  have hsup := card_sup_le_of_outer hW hperf hirr hE hEel e hOut
  have hLc : Nat.card ↥L = Nat.card (Subgroup.center ↥L) * Nat.card S := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [this, mul_comm]
    congr 1
    exact Nat.card_congr e.toEquiv
  exact card_mul_card_fixV_lt_of_card_sup_lt hW hL hirr hE hEne hEel
    (lt_of_le_of_lt hsup (hLc ▸ hlt))

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

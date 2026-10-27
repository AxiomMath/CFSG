module

public import CFSG.CGT.PushingUpLit.BHS7.CoverTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

theorem card_sup_mul_card_inf_of_normal_aux {P : Type*} [Group P] (A N : Subgroup P)
    [N.Normal] :
    Nat.card (A ⊔ N : Subgroup P) * Nat.card (A ⊓ N : Subgroup P) =
      Nat.card A * Nat.card N := by
  have h1 : N.relIndex (A ⊔ N) = N.relIndex A := Subgroup.relIndex_sup_right A N
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := A ⊔ N)
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := A)
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3, mul_right_comm]

theorem aimg_commutative {P : Type*} [Group P] {S Q U : Subgroup P} (α : S ≃* S) (hUQ : U ≤ Q)
    (hUc : ∀ q ∈ Q, ∀ u ∈ U, q * u = u * q) :
    ∀ x ∈ aimg S α U, ∀ y ∈ aimg S α U, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_aimg.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_aimg.mp hy
  have h1 : a * b = b * a := Subtype.ext (hUc a (hUQ ha) b hb)
  have h2 : α a * α b = α b * α a := by rw [← map_mul, ← map_mul, h1]
  exact congrArg Subtype.val h2

theorem eq_sup_inf_centralizer_of_aimg
    {P : Type*} [Group P] [Finite P] {S Q U : Subgroup P} (α : S ≃* S)
    [Q.Normal] [U.Normal]
    (hQS : Q ≤ S) (hUQ : U ≤ Q) (hUc : ∀ q ∈ Q, ∀ u ∈ U, q * u = u * q)
    (hSα : S = Q ⊔ aimg S α U)
    (hZ : aimg S α U ⊓ Q = aimg S α (U ⊓ Subgroup.centralizer (S : Set P))) :
    Q = U ⊔ (Q ⊓ Subgroup.centralizer ((aimg S α U : Subgroup P) : Set P)) := by
  classical
  set U' := aimg S α U with hU'
  have hUS : U ≤ S := hUQ.trans hQS
  have hU'S : U' ≤ S := aimg_le
  set Z := U ⊓ Subgroup.centralizer (S : Set P) with hZdef
  set C := S ⊓ Subgroup.centralizer (U : Set P) with hCdef
  set R := Q ⊓ Subgroup.centralizer (U' : Set P) with hRdef
  have hZS : Z ≤ S := inf_le_left.trans hUS
  have hCS : C ≤ S := inf_le_left
  have hU'ab := aimg_commutative α hUQ hUc
  have hU'c : U' ≤ Subgroup.centralizer (U' : Set P) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hU'ab x hx y hy).symm
  have hĈ : aimg S α C = S ⊓ Subgroup.centralizer (U' : Set P) := by
    have := aimg_centralizer (S := S) (α := α) (Y := S) (Y' := U) hUS
    rwa [aimg_self] at this
  have hĈcard : Nat.card (S ⊓ Subgroup.centralizer (U' : Set P) : Subgroup P) = Nat.card C := by
    rw [← hĈ]; exact card_aimg hCS
  have hQĈ : (S ⊓ Subgroup.centralizer (U' : Set P)) ⊔ Q = S := by
    apply le_antisymm
    · exact sup_le inf_le_left hQS
    · exact hSα.le.trans (sup_le le_sup_right (le_sup_of_le_left (le_inf hU'S hU'c)))
  have hQĈinf : (S ⊓ Subgroup.centralizer (U' : Set P)) ⊓ Q = R := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hQS]
  have hUR : R ⊓ U = Z := by
    apply le_antisymm
    · rintro x ⟨⟨hxQ, hxc⟩, hxU⟩
      refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have hs' : s ∈ Q ⊔ U' := hSα ▸ hs
      have hcent : Q ⊔ U' ≤ Subgroup.centralizer ({x} : Set P) := by
        refine sup_le (fun q hq => ?_) (fun u hu => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (hUc q hq y hxU).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (Subgroup.mem_centralizer_iff.mp hxc u hu).symm
      exact (Subgroup.mem_centralizer_iff.mp (hcent hs') x rfl).symm
    · rintro x ⟨hxU, hxc⟩
      refine ⟨⟨hUQ hxU, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, hxU⟩
      exact Subgroup.mem_centralizer_iff.mp hxc y (hU'S hy)
  have e5 : Nat.card S * Nat.card Z = Nat.card U * Nat.card Q := by
    have h1 := card_sup_mul_card_inf_of_normal_aux U' Q
    rw [sup_comm U' Q, ← hSα, hZ, card_aimg hZS, card_aimg hUS] at h1
    exact h1
  have e6 : Nat.card S * Nat.card R = Nat.card C * Nat.card Q := by
    have h1 := card_sup_mul_card_inf_of_normal_aux (S ⊓ Subgroup.centralizer (U' : Set P)) Q
    rw [hQĈ, hQĈinf, hĈcard] at h1
    exact h1
  have e7 : Nat.card (U ⊔ R : Subgroup P) * Nat.card Z = Nat.card R * Nat.card U := by
    have h1 := card_sup_mul_card_inf_of_normal_aux R U
    rw [hUR, sup_comm] at h1
    exact h1
  have hpos : 0 < Nat.card Z * Nat.card S :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hUR' : Nat.card (U ⊔ R : Subgroup P) = Nat.card C := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (U ⊔ R : Subgroup P) * (Nat.card Z * Nat.card S)
        = (Nat.card (U ⊔ R : Subgroup P) * Nat.card Z) * Nat.card S := by rw [mul_assoc]
      _ = Nat.card R * Nat.card U * Nat.card S := by rw [e7]
      _ = Nat.card U * (Nat.card S * Nat.card R) := by
          rw [mul_comm (Nat.card R) (Nat.card U), mul_assoc, mul_comm (Nat.card R)]
      _ = Nat.card U * (Nat.card C * Nat.card Q) := by rw [e6]
      _ = Nat.card C * (Nat.card S * Nat.card Z) := by rw [e5]; ring
      _ = Nat.card C * (Nat.card Z * Nat.card S) := by rw [mul_comm (Nat.card S)]
  have hQC : Q ≤ C := fun q hq =>
    ⟨hQS hq, Subgroup.mem_centralizer_iff.mpr fun u hu => (hUc q hq u hu).symm⟩
  have hle : U ⊔ R ≤ Q := sup_le hUQ inf_le_left
  have hcard : Nat.card Q ≤ Nat.card (U ⊔ R : Subgroup P) := by
    rw [hUR']
    exact Subgroup.card_le_of_le hQC
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem commutator_mul_left_of_commute {G : Type*} [Group G] {a x e : G}
    (hax : a * x = x * a) (hae : a * e = e * a) : ⁅a * x, e⁆ = ⁅x, e⁆ := by
  have hax' : Commute a x := hax
  have hae' : Commute a e := hae
  have hxi : Commute a x⁻¹ := Commute.inv_right hax'
  have hc : Commute a (x * e * x⁻¹) := (hax'.mul_right hae').mul_right hxi
  calc ⁅a * x, e⁆ = a * (x * e * x⁻¹) * a⁻¹ * e⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅x, e⁆ := by
        rw [hc.eq, mul_inv_cancel_right]
        rfl

theorem commutator_inf_le_of_decomp
    {P : Type*} [Group P] {S Q E U U' R : Subgroup P} [Q.Normal] [U.Normal]
    (hSQ : S = Q ⊔ U') (hUE : U ≤ E) (hQR : Q = U ⊔ R)
    (hU'ab : ∀ x ∈ U', ∀ y ∈ U', x * y = y * x)
    (hRc : ∀ r ∈ R, ∀ x ∈ U', r * x = x * r)
    (hQE : ∀ q ∈ Q, ∀ e ∈ E, ⁅q, e⁆ ∈ U) :
    ∀ s₁ ∈ S ⊓ E, ∀ s₂ ∈ S ⊓ E, ⁅s₁, s₂⁆ ∈ U := by
  classical
  have hRQ : R ≤ Q := hQR ▸ le_sup_right
  have hdec : ∀ s ∈ S ⊓ E, ∃ u ∈ U, ∃ a ∈ U', ∃ r ∈ R, a * r ∈ E ∧ s = u * (a * r) := by
    intro s hs
    obtain ⟨q, hq, a, ha, hqa⟩ := Subgroup.mem_sup_of_normal_left.mp (hSQ ▸ hs.1)
    obtain ⟨u, hu, r, hr, hur⟩ := Subgroup.mem_sup_of_normal_left.mp (hQR ▸ hq)
    have hs' : s = u * (a * r) := by
      rw [← hqa, ← hur, mul_assoc, hRc r hr a ha]
    refine ⟨u, hu, a, ha, r, hr, ?_, hs'⟩
    have h2 : u * (a * r) ∈ E := hs' ▸ hs.2
    have h3 : u⁻¹ * (u * (a * r)) ∈ E := E.mul_mem (E.inv_mem (hUE hu)) h2
    simpa using h3
  intro s₁ hs₁ s₂ hs₂
  obtain ⟨u₁, hu₁, a₁, ha₁, r₁, hr₁, hε₁, rfl⟩ := hdec s₁ hs₁
  obtain ⟨u₂, hu₂, a₂, ha₂, r₂, hr₂, hε₂, rfl⟩ := hdec s₂ hs₂
  have h1 : a₁ * r₁ = r₁ * a₁ := (hRc r₁ hr₁ a₁ ha₁).symm
  have h2 : a₁ * (a₂ * r₂) = (a₂ * r₂) * a₁ := by
    rw [← mul_assoc, hU'ab a₁ ha₁ a₂ ha₂, mul_assoc, mul_assoc, hRc r₂ hr₂ a₁ ha₁]
  have hε : ⁅a₁ * r₁, a₂ * r₂⁆ ∈ U := by
    rw [commutator_mul_left_of_commute h1 h2]
    exact hQE r₁ (hRQ hr₁) _ hε₂
  have hmk : ∀ u : P, u ∈ U → ∀ x : P,
      QuotientGroup.mk' U (u * x) = QuotientGroup.mk' U x := by
    intro u hu x
    have h1 : QuotientGroup.mk' U u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    rw [map_mul, h1, one_mul]
  have h3 : QuotientGroup.mk' U ⁅u₁ * (a₁ * r₁), u₂ * (a₂ * r₂)⁆ =
      QuotientGroup.mk' U ⁅a₁ * r₁, a₂ * r₂⁆ := by
    rw [map_commutatorElement, map_commutatorElement, hmk u₁ hu₁, hmk u₂ hu₂]
  have h4 : QuotientGroup.mk' U ⁅a₁ * r₁, a₂ * r₂⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hε
  exact (QuotientGroup.eq_one_iff _).mp (h3.trans h4)

theorem inf_le_of_aimg_cover
    {P : Type*} [Group P] [Finite P] {S Q E U : Subgroup P} (α : S ≃* S)
    [Q.Normal] [E.Normal] [U.Normal]
    (hQS : Q ≤ S) (hU : U = ⁅Q, E⁆) (hUc : ∀ q ∈ Q, ∀ u ∈ U, q * u = u * q)
    (hSα : S = Q ⊔ aimg S α U)
    (hZ : aimg S α U ⊓ Q = aimg S α (U ⊓ Subgroup.centralizer (S : Set P)))
    (hE : ∀ (N : Subgroup E) [N.Normal], IsPGroup 2 (E ⧸ N) → N = ⊤)
    (hSyl : IsSylowTwoOf (S ⊓ E) E) : Q ⊓ E ≤ U := by
  classical
  have hUQ : U ≤ Q := hU ▸ Subgroup.commutator_le_left Q E
  have hUE : U ≤ E := hU ▸ Subgroup.commutator_le_right Q E
  have hQE : ∀ q ∈ Q, ∀ e ∈ E, ⁅q, e⁆ ∈ U := fun q hq e he =>
    hU ▸ Subgroup.commutator_mem_commutator hq he
  have hQR := eq_sup_inf_centralizer_of_aimg α hQS hUQ hUc hSα hZ
  have hU'ab := aimg_commutative α hUQ hUc
  have hRc : ∀ r ∈ Q ⊓ Subgroup.centralizer ((aimg S α U : Subgroup P) : Set P),
      ∀ x ∈ aimg S α U, r * x = x * r := fun r hr x hx =>
    (Subgroup.mem_centralizer_iff.mp hr.2 x hx).symm
  have hcomm := commutator_inf_le_of_decomp hSα hUE hQR hU'ab hRc hQE
  refine le_of_central_mod_of_commutative_mod_sylow (E := E) (U := U) (QE := Q ⊓ E)
    (SE := S ⊓ E) hE (fun e _ u hu => (inferInstance : U.Normal).conj_mem u hu e) ?_
    inf_le_right (inf_le_inf_right E hQS) hSyl.2.1 hSyl.2.2 ?_ hcomm
  · exact le_inf (hUQ.trans hQS) hUE
  · intro q hq e he
    exact hQE q hq.1 e he

end CFSG.CGT.PushingUpLit.BHS7

module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreDatum
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBender

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant
  isoInvariant_card_quotient_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace QSporadic

@[expose] def QFree (s : TauCeti.SporadicName) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → NativeSporadic.IsSporadic D s →
    ∀ (n : ℕ) (α : MulAut D) (J : Subgroup D), ¬ QFixedRootDatum D n α J

section Datum

variable {D : Type} [Group D] {n : ℕ} {α : MulAut D} {J : Subgroup D}

theorem false_of_comps (d : QFixedRootDatum D n α J) {Q : (Y : Type) → [Group Y] → Prop}
    (hQ : IsoInvariant Q) (hQJ : ¬ Q J)
    (hC : CompsSatisfy (α.toMonoidHom.eqLocus (MonoidHom.id D)) Q) : False :=
  hQJ (hQ _ _ (Subgroup.subgroupOfEquivOfLe d.le_fixed).symm (hC _ d.isComponent))

theorem false_of_inner_comps (hD : IsSimpleGroup D) (d : QFixedRootDatum D n α J)
    (hin : α ∈ inner D) {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (hQJ : ¬ Q J)
    (hC : ∀ t : D, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set D)) Q) : False := by
  obtain ⟨t, ht, rfl⟩ := Sporadic.exists_involution_of_mem_inner
    (SporadicBender.center_eq_bot_of_subgroup_nonabelian hD d.nonabelian) d.orderOf_eq hin
  exact false_of_comps d hQ hQJ
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (Sporadic.eqLocus_conj t)) (hC t ht))

theorem false_of_outer_comps (d : QFixedRootDatum D n α J) (hout : α ∉ inner D)
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (hQJ : ¬ Q J)
    (hC : ∀ β : MulAut D, orderOf β = 2 → β ∉ inner D →
      CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Q) : False :=
  false_of_comps d hQ hQJ (CompsSatisfy.of_mulEquiv hQ
    (MulEquiv.subgroupCongr (Sporadic.eqLocus_eq_fixSub α)) (hC α d.orderOf_eq hout))

end Datum

theorem qFree_of_comps {s : TauCeti.SporadicName} {Qi Qo : (Y : Type) → [Group Y] → Prop}
    (hQi : IsoInvariant Qi) (hQo : IsoInvariant Qo)
    (hT : ∀ (n : ℕ) (X : Type) [Group X], CFSG.Open.IsQuasisimple X →
      LieModel (X ⧸ center X) .PSU 3 2 n → ¬ Qi X ∧ ¬ Qo X)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set G)) Qi)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Qo) :
    QFree s := by
  intro D _ _ hD hs n α J d
  obtain ⟨hi, ho⟩ := hT n J d.quasisimple d.model
  by_cases hα : α ∈ inner D
  · exact false_of_inner_comps hD d hα hQi hi (hin D hD hs)
  · exact false_of_outer_comps d hα hQo ho (hout D hD hs)

theorem qFree_of_card_quotient_center {s : TauCeti.SporadicName} {Ni No : Set ℕ}
    (hT : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], T_U3 n X →
      Nat.card X ∉ Ni ∧ Nat.card X ∉ No)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nat.card (Y ⧸ center Y) ∈ Ni)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) fun Y _ => Nat.card (Y ⧸ center Y) ∈ No) :
    QFree s :=
  qFree_of_comps (isoInvariant_card_quotient_center Ni) (isoInvariant_card_quotient_center No)
    (fun n X _ _ hm => by
      have : Finite (X ⧸ center X) := finite_of_lieModel_PSU3 hm
      exact hT n (X ⧸ center X) ⟨two_le_of_lieModel_PSU3 hm, hm⟩)
    hin hout

theorem qFree_of_card {s : TauCeti.SporadicName} {N : ℕ}
    (hN : Nat.card (NativeSporadic.Carrier s) = N)
    (hT : ∀ (n : ℕ) (X : Type) [Group X], T_U3 n X → ¬ Nat.card X ∣ N) : QFree s := by
  intro D _ _ _ ⟨e⟩ n α J d
  refine hT n (J ⧸ center J) ⟨d.two_le, d.model⟩ ?_
  rw [← hN, ← Nat.card_congr e.toEquiv]
  exact d.card_quotient_center_dvd.trans (Subgroup.card_subgroup_dvd_card J)

theorem qFree_of_check {s : TauCeti.SporadicName} {N e h : ℕ}
    (hs : Nat.card (NativeSporadic.Carrier s) = N) (hN : N = 2 ^ e * h) (hh : Odd h)
    (hU : ∀ m ≤ e / 3, 2 ≤ m → ¬ SporadicBender.u3Order m ∣ N) : QFree s :=
  qFree_of_card hs fun _ _ _ hX => SporadicBender.not_dvd_of_check_U3 hX hN hh hU

theorem m11_qFree : QFree .M11 :=
  qFree_of_check CFSG.Sporadic.Mathieu.card_M11 (e := 4) (h := 495) (by norm_num) (by decide)
    (by decide)

theorem m12_qFree : QFree .M12 :=
  qFree_of_check CFSG.Sporadic.Mathieu.card_M12 (e := 6) (h := 1485) (by norm_num) (by decide)
    (by decide)

theorem j4_qFree : QFree .J4 :=
  qFree_of_check CFSG.Sporadic.J4.card_J4 (e := 21) (h := 41377816699065) (by norm_num)
    (by decide) (by decide)

theorem m22_qFree : QFree .M22 :=
  qFree_of_check CFSG.Sporadic.Mathieu.card_M22 (e := 7) (h := 3465) (by norm_num) (by decide)
    (by decide)

theorem m23_qFree :
    QFree .M23 :=
  qFree_of_check CFSG.EvenSmallLie.CatalogOrders.card_M23 (e := 7) (h := 79695) (by norm_num)
    (by decide) (by decide)

theorem m24_qFree : QFree .M24 :=
  qFree_of_check CFSG.Sporadic.Mathieu.card_M24 (e := 10) (h := 239085) (by norm_num)
    (by decide) (by decide)

theorem j1_qFree : QFree .J1 :=
  qFree_of_check CFSG.Sporadic.J1.card_J1 (e := 3) (h := 21945) (by norm_num) (by decide)
    (by decide)

theorem j2_qFree : QFree .J2 :=
  qFree_of_check CFSG.Sporadic.J2.card_J2 (e := 7) (h := 4725) (by norm_num) (by decide)
    (by decide)

theorem j3_qFree : QFree .J3 :=
  qFree_of_check CFSG.Sporadic.J3.card_J3 (e := 7) (h := 392445) (by norm_num) (by decide)
    (by decide)

theorem hs_qFree : QFree .HS :=
  qFree_of_check CFSG.Sporadic.HS.card_HS (e := 9) (h := 86625) (by norm_num) (by decide)
    (by decide)

theorem mcl_qFree : QFree .McL :=
  qFree_of_check CFSG.Sporadic.McL.card_McL (e := 7) (h := 7016625) (by norm_num) (by decide)
    (by decide)

theorem he_qFree : QFree .He :=
  qFree_of_check CFSG.Sporadic.He.fam_he_order.1 (e := 10) (h := 3935925) (by norm_num)
    (by decide) (by decide)

theorem co2_qFree : QFree .Co2 :=
  qFree_of_check CFSG.Sporadic.Co2.card_Co2 (e := 18) (h := 161382375) (by norm_num)
    (by decide) (by decide)

theorem co3_qFree : QFree .Co3 :=
  qFree_of_check CFSG.Sporadic.Co3.card_Co3 (e := 10) (h := 484147125) (by norm_num)
    (by decide) (by decide)

theorem ly_qFree : QFree .Ly :=
  qFree_of_check CFSG.Sporadic.Ly.card_Ly (e := 8) (h := 202207730484375) (by norm_num)
    (by decide) (by decide)

end QSporadic

end CFSG.LocalAnalysis.EvenBN.GMSK

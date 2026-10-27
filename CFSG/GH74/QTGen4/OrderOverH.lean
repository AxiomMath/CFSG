module

public import CFSG.GH74.QTGen4.CharTwoQuotient
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Open

theorem isCharacteristicP_of_charTwo {G : Type} [Group G] {H : Subgroup G}
    (h : CFSG.QuasithinUnique.CharTwo H) : CFSG.IsCharacteristicP 2 ↥H := by
  intro x hx
  have hx' : (x : G) ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    have := Subgroup.mem_centralizer_iff.1 hx y (by assumption)
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := h hx'
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem modO2_dvd_of_inH {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {H K : Subgroup G}
    (hH : CFSG.Quasithin.InH (T : Subgroup G) H) (hKH : K ≤ H) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 20160 := by
  have hchar := CFSG.Quasithin.charTwo_of_inH hEven T hH
  have hOH := card_quotient_pCore_dvd_20160 (isCharacteristicP_of_charTwo hchar)
    (Gen4.subgroup H hG)
  let f : ↥K →* ↥H ⧸ CFSG.pCore 2 ↥H := (QuotientGroup.mk' _).comp (Subgroup.inclusion hKH)
  have hker : f.ker ≤ CFSG.pCore 2 ↥K := by
    have hn : f.ker.Normal := MonoidHom.normal_ker f
    have hp : IsPGroup 2 f.ker := by
      have h2 : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
      let g : f.ker →* ↥(CFSG.pCore 2 ↥H) :=
        { toFun := fun k => ⟨Subgroup.inclusion hKH k.1, (QuotientGroup.eq_one_iff _).1 k.2⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      refine IsPGroup.of_injective h2 g (fun a b hab => ?_)
      have h1 : Subgroup.inclusion hKH a.1 = Subgroup.inclusion hKH b.1 :=
        congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => (z : ↥H)) hab
      have h2 : (a.1 : G) = b.1 := congrArg (fun z : ↥H => (z : G)) h1
      exact Subtype.ext (Subtype.ext h2)
    exact le_sSup ⟨hn, hp⟩
  have hdiv1 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card (↥K ⧸ f.ker) := by
    exact Subgroup.card_dvd_of_surjective (f := QuotientGroup.map f.ker (CFSG.pCore 2 ↥K)
      (MonoidHom.id _) hker) (fun x => by
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨QuotientGroup.mk k, rfl⟩)
  have hdiv2 : Nat.card (↥K ⧸ f.ker) ∣ Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_subgroup_dvd_card f.range
  exact hdiv1.trans (hdiv2.trans hOH)

theorem le_of_isSubnormal {X : Type*} [Group X] {A B : Subgroup X} (h : IsSubnormal A B) :
    A ≤ B :=
  h.le

theorem modO2_dvd_of_cComp_of_le {G : Type} [Group G] [Finite G]
    (hG : Gen4 G) (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M₁ K₁ : Subgroup G}
    (hM₁ : IsTwoLocal M₁) (hTM : (T : Subgroup G) ≤ M₁)
    (hK₁ : K₁ ∈ CFSG.Quasithin.cComp M₁) :
    Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∣ 20160 :=
  modO2_dvd_of_inH hG hEven T ⟨hTM, CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hM₁⟩
    (le_of_isSubnormal hK₁.2.2.1)

theorem modO2_dvd_of_cComp_maxTwoLocal {G : Type} [Group G] [Finite G]
    (hG : Gen4 G) (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M₁ K₁ : Subgroup G}
    (hM₁ : quasithinIsMaxTwoLocal M₁)
    (hC : Subgroup.centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤ M₁)
    (hK₁ : K₁ ∈ CFSG.Quasithin.cComp M₁) :
    Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∣ 20160 :=
  modO2_dvd_of_cComp_of_le hG hEven T hM₁.1
    ((CFSG.Quasithin.le_centralizer_quasithinOmegaOneCenter _).trans hC) hK₁

end CFSG.GH74.QTGen4

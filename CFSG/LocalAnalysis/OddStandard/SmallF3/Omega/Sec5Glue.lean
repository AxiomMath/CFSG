module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82Sec5FactB5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
      ∀ r : G, orderOf r = 2 → (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
        ∃ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) ∧ IsElemAb2 B 5 ∧ t ∈ B ∧
          zpowers t ⊓ layerCent L r = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L r)

theorem sec5_exists_rctx [Finite G] (h52b : Asc82Lemma52b) (h56 : Asc82Lemma56)
    (hZ : Asc82ZExists) (hB : Asc82Sec5FactB5) {t : G} {L : Subgroup G} (h : Sec5Setting G t L) :
    ∃ (S : Subgroup G) (z r : G) (B A : Subgroup G), Sec5RCtx G t L S z r B A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_isSylow2Of (centralizer ({t} : Set G))
  obtain ⟨z₀, hz₀⟩ := hZ G t L h.toSec3SettingLB S₀ hS₀
  obtain ⟨r, ⟨g, hg⟩, hrtype⟩ :=
    h56 G t L S₀ z₀ { toSec5Setting := h, toAsc82Notation := hz₀ }
  have hr2 : orderOf r = 2 := by
    rw [← hg]
    exact (orderOf_conjugate_eq t g).trans h.involution
  obtain ⟨B, hBle, hBE, htB, hinf, hBeq⟩ :=
    hB G L h.isOm6Z2 t (sec5_t_mem_centerIn h52b h) h.involution r hr2 hrtype
  have htr : t * r = r * t := Subgroup.mem_centralizer_singleton_iff.mp (hBle htB).2
  have hrC : r ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htr.symm
  have hAC : zpowers r ⊔ B ≤ centralizer ({t} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hrC) ((hBle.trans inf_le_left).trans h.component.le)
  have hrB : ∀ a ∈ zpowers r, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbr : Commute b r := Subgroup.mem_centralizer_singleton_iff.mp (hBle hb).2
    exact (hbr.symm.zpow_left k)
  have h2r : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2]; norm_num)
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 5) hBE.2
  have hA2 : IsPGroup 2 ↥(zpowers r ⊔ B) :=
    CFSG.OddStandard.SmallF3.HarrisU33.isPGroup_sup_of_commute hrB h2r hB2
  obtain ⟨S, hS, hAS⟩ := exists_isSylow2Of_ge hA2 hAC
  obtain ⟨z, hz⟩ := hZ G t L h.toSec3SettingLB S hS
  exact ⟨S, z, r, B, zpowers r ⊔ B,
    { toSec5Ctx := { toSec5Setting := h, toAsc82Notation := hz }
      conj_r := ⟨g, hg⟩
      type_r := hrtype
      B_le := hBle
      B_E32 := hBE
      B_split := ⟨htB, hinf, hBeq⟩
      A_eq := rfl
      A_le := hAS }⟩

end CFSG.OddStandard.SmallF3.Omega

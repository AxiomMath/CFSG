module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Layer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

theorem sec128_quot_solvable {Y : Type} [Group Y] [Finite Y] (Z O : Subgroup Y) [Z.Normal]
    [O.Normal] (hO : Group.IsSolvable ↥O) (hidx : (Z ⊔ O).index = 2) :
    Group.IsSolvable (Y ⧸ Z) := by
  have hle : Z ≤ Z ⊔ O := le_sup_left
  let f : ↥O →* Y ⧸ Z := (QuotientGroup.mk' Z).comp O.subtype
  let g : Y ⧸ Z →* Y ⧸ (Z ⊔ O) := QuotientGroup.map Z (Z ⊔ O) (MonoidHom.id Y) hle
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (Y ⧸ (Z ⊔ O)) := isCyclic_of_prime_card (p := 2) hidx
  haveI : Group.IsSolvable (Y ⧸ (Z ⊔ O)) := inferInstance
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H y =>
    have hy : y ∈ Z ⊔ O := (QuotientGroup.eq_one_iff y).mp (MonoidHom.mem_ker.mp hx)
    have hy' : y ∈ ((Z : Set Y) * (O : Set Y)) := by
      rw [← Subgroup.normal_mul]
      exact hy
    obtain ⟨z, hz, o, ho, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨⟨o, ho⟩, ?_⟩
    show ((o : Y) : Y ⧸ Z) = ((z * o : Y) : Y ⧸ Z)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, one_mul]

theorem sec128_card_join {Y : Type} [Group Y] [Finite Y] (Z O : Subgroup Y) [Z.Normal]
    (hZO : Z ⊓ O = ⊥) : Nat.card ↥(Z ⊔ O) = Nat.card ↥O * Nat.card ↥Z := by
  have h1 := Subgroup.relIndex_mul_card Z (Z ⊔ O)
  have h2 := Subgroup.relIndex_mul_card Z O
  rw [inf_sup_self, Subgroup.relIndex_sup_left] at h1
  rw [hZO, Subgroup.card_bot, mul_one] at h2
  rw [← h1, h2]

theorem sec128_odd_dvd_six {n : ℕ} (hodd : Odd n) (hdvd : n ∣ 6) : n = 1 ∨ n = 3 := by
  have hn6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;>
    first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert hodd hdvd; decide)

theorem sec128_alt2 {G : Type} [Group G] [Finite G] {V : Subgroup G}
    {Y Xt Z : Subgroup (MulAut ↥V)} (hZY : Z ≤ Y) (hXZ : Xt ≤ Z)
    (hDc : Nat.card ↥(Subgroup.centralizer (Xt : Set (MulAut ↥V))) ∣ 6)
    (hZn : (Z.subgroupOf Y).Normal)
    (hZc : ∀ z ∈ Z, ∀ o ∈ oddCore ↥Y, z * (o : MulAut ↥V) = (o : MulAut ↥V) * z)
    (hZO : Z ⊓ (oddCore ↥Y).map Y.subtype = ⊥)
    (hidx : (Z.subgroupOf Y ⊔ oddCore ↥Y).index = 2)
    (hZe : Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))))
    (hΩ : IsNatOmega4Plus V Z) :
    IsNatOmega4Plus V ((CFSG.layer ↥Y).map Y.subtype) ∧
      (Nat.card ↥Y = 2 * Nat.card ↥((CFSG.layer ↥Y).map Y.subtype) ∨
        Nat.card ↥Y = 6 * Nat.card ↥((CFSG.layer ↥Y).map Y.subtype)) := by
  set O : Subgroup ↥Y := oddCore ↥Y with hOdef
  set Zy : Subgroup ↥Y := Z.subgroupOf Y with hZydef
  haveI : Zy.Normal := hZn
  have hZyO : Zy ⊓ O = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    have h1 : (y : MulAut ↥V) ∈ Z ⊓ O.map Y.subtype :=
      ⟨Subgroup.mem_subgroupOf.mp hy.1, ⟨y, hy.2, rfl⟩⟩
    rw [hZO, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hOle : O.map Y.subtype ≤ Subgroup.centralizer (Xt : Set (MulAut ↥V)) := by
    rintro _ ⟨o, ho, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hZc x (hXZ hx) o ho
  have hOdvd : Nat.card ↥O ∣ 6 := by
    have h1 : Nat.card ↥(O.map Y.subtype) = Nat.card ↥O :=
      Subgroup.card_map_of_injective Y.subtype_injective
    rw [← h1]
    exact (Subgroup.card_dvd_of_le hOle).trans hDc
  have hOodd : Odd (Nat.card ↥O) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hOcard := sec128_odd_dvd_six hOodd hOdvd
  have hOsol : Group.IsSolvable ↥O := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpg : IsPGroup 3 ↥O := by
      rcases hOcard with h | h
      · exact IsPGroup.of_card (n := 0) (by simpa using h)
      · exact IsPGroup.of_card (n := 1) (by simpa using h)
    haveI : Group.IsNilpotent ↥O := hpg.isNilpotent
    infer_instance
  have hsol : Group.IsSolvable (↥Y ⧸ Zy) := sec128_quot_solvable Zy O hOsol hidx
  have hZy : Nonempty (↥Zy ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) :=
    hZe.map fun e => (Subgroup.subgroupOfEquivOfLe hZY).trans e
  have hlayer : CFSG.layer ↥Y = Zy := sec128_layer_eq Zy hZy hsol
  have hmap : (CFSG.layer ↥Y).map Y.subtype = Z := by
    rw [hlayer, hZydef, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hZY
  rw [hmap]
  refine ⟨hΩ, ?_⟩
  have hY : Nat.card ↥Y = 2 * Nat.card ↥(Zy ⊔ O) := by
    have h1 := Subgroup.index_mul_card (Zy ⊔ O)
    rw [hidx] at h1
    exact h1.symm
  have hZcard : Nat.card ↥Zy = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  have hcard : Nat.card ↥Y = 2 * (Nat.card ↥O * Nat.card ↥Z) := by
    rw [hY, sec128_card_join Zy O hZyO, hZcard]
  rcases hOcard with h | h
  · left
    rw [hcard, h]
    ring
  · right
    rw [hcard, h]
    ring

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4O82
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoLeviCover
public import CFSG.LieType.Chevalley.CLSTwistedE6FieldTwoCoverLifts
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFacts
public import CFSG.Monster.B.GSide.HInnerFusionI3
public import CFSG.Monster.B.GSide.EdgeHom
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4U62

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Chevalley.C2E6Std
open CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide

theorem card_dvd_two_mul_card_inf {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    (hH : H.index = 2) (K : Subgroup G) : Nat.card K ∣ 2 * Nat.card (H.subgroupOf K) := by
  have h1 := (H.subgroupOf K).card_mul_index
  have h2 : (H.subgroupOf K).index ∣ 2 := by
    rw [← hH]
    exact Subgroup.relIndex_dvd_index_of_normal H K
  rw [← h1, mul_comm 2]
  exact Nat.mul_dvd_mul_left _ h2

theorem card_dvd_two_mul_card_map {G G' : Type*} [Group G] [Group G'] [Finite G] (π : G →* G')
    (hπ : Nat.card π.ker ∣ 2) (D : Subgroup G) : Nat.card D ∣ 2 * Nat.card (D.map π) := by
  have h1 := Subgroup.card_ker_mul_card_range (π.comp D.subtype)
  have hrange : (π.comp D.subtype).range = D.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card (π.comp D.subtype).ker ∣ Nat.card π.ker := by
    have hle : (π.comp D.subtype).ker.map D.subtype ≤ π.ker := by
      rintro _ ⟨d, hd, rfl⟩
      exact hd
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  rw [hrange] at h1
  rw [← h1]
  exact Nat.mul_dvd_mul_right (hker.trans hπ) _

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [_root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective, ← _root_.commutator_def]

theorem pow_dvd_card_centralizer_of_double_cover {S A H : Type*} [Group S] [Group A] [Group H]
    [Finite A] {k : ℕ} (εE : commutator A ⧸ center (commutator A) ≃* S)
    (hE2 : Nat.card (center (commutator A)) = 2)
    (hsq : ∀ a : commutator A, a ^ 2 ∈ center (commutator A) → a ^ 2 = 1) (φ : H ≃* A)
    (hidx : (commutator H).index = 2)
    (hcent : ∀ u : H, u ∈ commutator H → u * u = 1 → u ≠ 1 →
      2 ^ (k + 2) ∣ Nat.card (centralizer ({u} : Set H)))
    {x : S} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    2 ^ k ∣ Nat.card (centralizer ({x} : Set S)) := by
  have : Finite H := Finite.of_equiv _ φ.symm.toEquiv
  set E' := commutator A with hE'
  let π : E' →* S := εE.toMonoidHom.comp (QuotientGroup.mk' (center E'))
  have hπ : Function.Surjective π := εE.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = center E' := by
    ext y
    rw [MonoidHom.mem_ker]
    change εE (QuotientGroup.mk y) = 1 ↔ _
    rw [map_eq_one_iff εE εE.injective, QuotientGroup.eq_one_iff]
  obtain ⟨a, rfl⟩ := hπ x
  have ha2 : a ^ 2 = 1 := hsq a (by
    rw [← hπker, MonoidHom.mem_ker, map_pow, pow_two, hx2])
  have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have huH : φ.symm (a : A) ∈ commutator H := by
    rw [← map_commutator_mulEquiv φ.symm]
    exact ⟨a, a.2, rfl⟩
  have ha2' : (a : A) * (a : A) = 1 := by
    have := congrArg Subtype.val ha2
    rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one] at this
    exact this
  have hu2 : φ.symm (a : A) * φ.symm (a : A) = 1 := by rw [← map_mul, ha2', map_one]
  have hu1 : φ.symm (a : A) ≠ 1 := fun h => by
    apply ha1
    apply Subtype.ext
    have h' : φ.symm (a : A) = φ.symm 1 := by rw [h, map_one]
    exact φ.symm.injective h'
  have hk := hcent _ huH hu2 hu1
  rw [card_centralizer_mulEquiv φ, MulEquiv.apply_symm_apply] at hk
  have hidx' : E'.index = 2 := by
    rw [hE', ← hidx, ← map_commutator_mulEquiv φ, Subgroup.index_map_of_bijective φ.bijective]
  have hC := card_dvd_two_mul_card_inf hidx' (centralizer ({(a : A)} : Set A))
  have hCE : Nat.card (E'.subgroupOf (centralizer ({(a : A)} : Set A))) =
      Nat.card (centralizer ({a} : Set E')) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1.1, y.2⟩, ?_⟩
        invFun := fun y => ⟨⟨y.1.1, ?_⟩, y.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h := mem_centralizer_singleton_iff.mp y.1.2
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext h)
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2))
  rw [hCE] at hC
  have hD := card_dvd_two_mul_card_map π (by rw [hπker, hE2]) (centralizer ({a} : Set E'))
  have hle : (centralizer ({a} : Set E')).map π ≤ centralizer ({π a} : Set S) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy])
  have hfin := (hk.trans hC).trans (Nat.mul_dvd_mul_left 2 hD)
  rw [← mul_assoc, show (2 : ℕ) * 2 = 2 ^ 2 by norm_num, pow_add, mul_comm (2 ^ k)] at hfin
  exact (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hfin).trans (Subgroup.card_dvd_of_le hle)

theorem pow_dvd_card_centralizer_stdGroup
    {x : stdGroup} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    2 ^ 25 ∣ Nat.card (centralizer ({x} : Set stdGroup)) := by
  obtain ⟨-, hEfin, hE2, ⟨εE⟩⟩ := EvenSmallLie.TwoE6.derived_Eam_facts
  have : Finite Eam := Finite.of_equiv _ vStabEam.toEquiv
  exact pow_dvd_card_centralizer_of_double_cover εE hE2
    (fun a ha => EvenSmallLie.TwoE6.sq_eq_one_of_sq_mem_center a ha) vStabEam
    index_commutator_H (fun u hu hu2 hu1 => inner_involution_centralizer_two_pow hu hu2 hu1)
    hx2 hx1

theorem exists_noncentral_involution_of_twistedE6
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (e : Q ⧸ center Q ≃* stdGroup)
    {u v : Q} (hu : u ∈ center Q) (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) : ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q := by
  obtain ⟨N, _, -, hN2, -, h2, ⟨e'⟩, -⟩ := exists_twoCover_quotient hQ hu hv hu2 hv2 hu1 hv1 huv
  let η : Q ⧸ N →* stdGroup := (e'.trans e).toMonoidHom.comp (QuotientGroup.mk' _)
  have hη : Function.Surjective η := (e'.trans e).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center (Q ⧸ N) := by
    ext y
    rw [MonoidHom.mem_ker]
    change (e'.trans e) (QuotientGroup.mk y) = 1 ↔ _
    rw [map_eq_one_iff _ (e'.trans e).injective, QuotientGroup.eq_one_iff]
  have hr := CFSG.Blueprint.Chevalley.isRoot_single CFSG.Blueprint.Chevalley.Tag.F4 ⟨0, by decide⟩
  obtain ⟨F, hFmap, hFker, -⟩ :=
    TwistedE6LeviCover.exists_split_relRootGroup η hη hker.le (hker ▸ h2) hr
  have hcard : 1 < Nat.card (F.map η) := by
    rw [hFmap]
    change 1 < Nat.card (LieType.Chevalley.TwistedE6FieldTwoCover.relG _)
    rw [LieType.Chevalley.TwistedE6FieldTwoCover.card_relG, RelativeRoots.card_relRootGroup hr]
    split_ifs <;> norm_num
  have := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨ρ, hρ⟩, hρ1⟩ := exists_ne (1 : ↥(F.map η))
  have hρ1' : ρ ≠ 1 := fun h => hρ1 (Subtype.ext h)
  have hρR : ρ ∈ (RelativeRoots.relRootGroup (Pi.single ⟨0, by decide⟩ 1)).comap
      stdGroup.subtype := hFmap ▸ hρ
  obtain ⟨f, hfF, hfρ⟩ := hρ
  have hρ2 : ρ * ρ = 1 := Subtype.ext ((RelativeRoots.relRootGroup_elementary hr).2 _ hρR)
  have hf2 : f * f = 1 := by
    have hmem : f * f ∈ F ⊓ η.ker :=
      ⟨mul_mem hfF hfF, MonoidHom.mem_ker.mpr (by rw [map_mul, hfρ, hρ2])⟩
    rw [hFker] at hmem
    exact hmem
  have hfZ : f ∉ center (Q ⧸ N) := by
    rw [← hker, MonoidHom.mem_ker, hfρ]
    exact hρ1'
  exact exists_noncentral_involution_of_quotient hN2 hf2 hfZ

theorem centralFour_twistedE6
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hL : LieModel (Q ⧸ center Q) .twistedE6 0 2 1) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q) (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  obtain ⟨e⟩ := (EvenSmallLie.TwoE6.lieModel_twistedE6_two_iff _).1 hL
  have hrow : GriessAll.GriessRow (Q ⧸ center Q) .twistedE6 0 2 1 :=
    GriessTwistedE6Two.row_of_multiplier (TwistedE6TwoCover.twistedE6TwoMultiplier _ hL)
  have hodd : (¬ 2 ∣ (genericOrders .twistedE6 0 2 1).1 ∧
      ¬ 2 ∣ (genericOrders .twistedE6 0 2 1).2) ∨
      (¬ 2 ∣ (exceptionalOrders .twistedE6 0 2 1).1 ∧
        ¬ 2 ∣ (exceptionalOrders .twistedE6 0 2 1).2) :=
    Or.inl (by decide)
  refine ⟨exists_noncentral_involution_of_twistedE6 hQ e huZ hvZ hu2 hv2 hu1 hv1 huv,
    fun x hx hxZ => ?_⟩
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  refine clause_two_of_griessRow hQ hrow hodd huZ hvZ hu2 hv2 hu1 hv1 huv hx2 ?_
  have hxb2 : e (x : Q ⧸ center Q) * e (x : Q ⧸ center Q) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hx2]
    exact map_one e
  have hxb1 : e (x : Q ⧸ center Q) ≠ 1 := by
    intro h
    apply hxZ
    rw [← QuotientGroup.eq_one_iff]
    exact e.injective (by rw [h, map_one])
  have h25 := pow_dvd_card_centralizer_stdGroup hxb2 hxb1
  rw [← card_centralizer_mulEquiv e] at h25
  have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h25
  omega

end CFSG.ComponentClassification.Sol76T13.Hq4

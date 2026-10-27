module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

theorem hasElemAbelianEight_of_e8Check_rep {n : ℕ} {A B C : Table}
    {a b c : Equiv.Perm (Fin n)} (rA : Rep n A a) (rB : Rep n B b) (rC : Rep n C c)
    (h : e8Check n A B C = true) {K : Subgroup (Equiv.Perm (Fin n))} (ha : a ∈ K) (hb : b ∈ K)
    (hc : c ∈ K) : HasElemAbelianEight K := by
  simp only [e8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha2⟩, hb2⟩, hc2⟩, hab2⟩, hac2⟩, hbc2⟩, habc2⟩ := h
  have order2 : ∀ {T : Table} {g : Equiv.Perm (Fin n)}, Rep n T g → ordTest n 2 T = true →
      orderOf g = 2 := fun hT hT2 => (ordTest_iff perm_faithful hT (by norm_num)).1 hT2
  obtain ⟨E, hE, hEe, hEc⟩ := exists_elemAbelian_eight a b c
    ((commT_iff rA rB).1 hab) ((commT_iff rA rC).1 hac) ((commT_iff rB rC).1 hbc)
    (order2 rA ha2) (order2 rB hb2) (order2 rC hc2)
    (order2 (Rep.compT rA rB) hab2) (order2 (Rep.compT rA rC) hac2)
    (order2 (Rep.compT rB rC) hbc2) (order2 (Rep.compT (Rep.compT rA rB) rC) habc2)
  refine HasElemAbelianEight.of_le (hE.trans ?_) hEe hEc
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb))
    (Subgroup.zpowers_le.mpr hc)

theorem hypothesisOne_of_innerModel {Y : Type*} [Group Y] {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))} (e : Y ≃* P) (hc : center Y = ⊥)
    (hsurj : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g)
    (hodd : ∀ v ∈ P, orderOf v = 2 → CFSG.oddCore ↥(centralizerIn P v) = ⊥)
    (hfour : ∀ v ∈ P, orderOf v = 2 → FourClassesLarge (centralizerIn P v)) :
    HypothesisOne Y := by
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hc) hsurj fun y hy => ?_
  have hv : orderOf ((e y : P) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hy
  have h1 : SmallNormalFree ↥(centralizerIn P ((e y : P) : Equiv.Perm (Fin n))) :=
    SmallNormalFree.of_fourClassesLarge (hodd _ (e y).2 hv) (hfour _ (e y).2 hv)
  exact SmallNormalFree.of_mulEquiv
    ((centralizerEquiv e y).trans (centralizerSubgroupEquiv P (e y))).symm h1

theorem card_centralizerIn_eq_two_mul {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (hPR : P ≤ R) (hidx : ∀ x ∈ R, x ∉ P → ∀ y ∈ R, y ∉ P → x⁻¹ * y ∈ P) (r z : M)
    (hz : z ∈ centralizerIn R r) (hzP : z ∉ P) :
    Nat.card ↥(centralizerIn R r) = 2 * Nat.card ↥(centralizerIn P r) := by
  set H := centralizerIn R r
  set N := centralizerIn P r
  have hNH : N ≤ H := fun g hg => mem_centralizerIn.2
    ⟨hPR (mem_centralizerIn.1 hg).1, (mem_centralizerIn.1 hg).2⟩
  have h2 : (N.subgroupOf H).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨z, hz⟩, ?_, fun b => ?_⟩
    · rw [mem_subgroupOf]
      exact fun h => hzP (mem_centralizerIn.1 h).1
    · by_cases hbP : (b : M) ∈ P
      · right
        rw [mem_subgroupOf]
        exact mem_centralizerIn.2 ⟨hbP, (mem_centralizerIn.1 b.2).2⟩
      · left
        rw [mem_subgroupOf]
        have hb := mem_centralizerIn.1 b.2
        have hz' := mem_centralizerIn.1 hz
        refine mem_centralizerIn.2 ⟨?_, ?_⟩
        · have := hidx _ (R.inv_mem hb.1) (fun h => hbP (by simpa using P.inv_mem h)) z hz'.1 hzP
          simpa using this
        · simp only [Subgroup.coe_mul]
          calc (b : M) * z * r = b * (z * r) := by group
            _ = b * (r * z) := by rw [hz'.2]
            _ = (b * r) * z := by group
            _ = (r * b) * z := by rw [hb.2]
            _ = r * (b * z) := by group
  have h := (N.subgroupOf H).card_mul_index
  rw [h2, Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv] at h
  omega

theorem hypothesisOne_of_outTwo {Y : Type*} [Group Y] {n : ℕ}
    {P R : Subgroup (Equiv.Perm (Fin n))} (eY : Y ≃* P) (hc : center P = ⊥)
    (hA : CFSG.Sporadic.SmallOddCore.AutModel P R) (e : R ≃* MulAut P)
    (hidx : Nat.card R ≤ 2 * Nat.card P)
    (hodd : ∀ τ ∈ R, orderOf τ = 2 →
      CFSG.oddCore ↥(P ⊓ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n)))) = ⊥)
    (hfourP : ∀ τ ∈ P, orderOf τ = 2 → FourClassesLarge (centralizerIn P τ))
    (hfourR : ∀ τ ∈ R, orderOf τ = 2 → FourClassesLarge (centralizerIn R τ)) :
    HypothesisOne Y := by
  have hinj := conj_injective_of_center_eq_bot hc
  have hcard : Nat.card (MulAut P) ≤ 2 * Nat.card P := by
    rw [← Nat.card_congr e.toEquiv]
    exact hidx
  have hI : HypothesisOne P := by
    refine hypothesisOne_of_index_two hinj (index_dvd_two_of_card_le hinj hcard) ?_ ?_
    · intro y hy
      have hv : orderOf (y : Equiv.Perm (Fin n)) = 2 := by
        rw [← Subgroup.orderOf_coe] at hy
        exact hy
      have h1 : SmallNormalFree ↥(centralizerIn P (y : Equiv.Perm (Fin n))) :=
        SmallNormalFree.of_fourClassesLarge (hodd _ (hA.le y.2) hv) (hfourP _ y.2 hv)
      exact SmallNormalFree.of_mulEquiv (centralizerSubgroupEquiv P y).symm h1
    · intro x hx
      obtain ⟨r, rfl⟩ := e.surjective x
      have hrR : orderOf r = 2 := by
        rw [← MulEquiv.orderOf_eq e]
        exact hx
      have hr : orderOf (r : Equiv.Perm (Fin n)) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact hrR
      have hS : (P.subgroupOf R).Normal := ⟨fun s hs g => by
        rw [mem_subgroupOf] at hs ⊢
        simpa using hA.conj_mem g g.2 s hs⟩
      have hC : Subgroup.centralizer ((P.subgroupOf R : Subgroup R) : Set R) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx'
        rw [Subgroup.mem_centralizer_iff] at hx'
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        refine hA.inj x x.2 fun p hp => ?_
        have := hx' ⟨p, hA.le hp⟩ (mem_subgroupOf.2 hp)
        exact congrArg Subtype.val this.symm
      have hO : CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ :=
        CFSG.Sporadic.SmallOddCore.oddCore_centralizer_eq_bot hA hidx hodd (P.subgroupOf R)
          (subgroupOfEquivOfLe hA.le) hC r hrR
      have hF : FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R)) :=
        FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv R r) (hfourR _ r.2 hr)
      exact SmallNormalFree.of_mulEquiv (centralizerEquiv e r)
        (SmallNormalFree.of_fourClassesLarge hO hF)
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv eY.symm hI

theorem foursGroupCondition_of_outTwo {Y : Type*} [Group Y] {n : ℕ}
    {P R : Subgroup (Equiv.Perm (Fin n))} (eY : Y ≃* P) (hc : center P = ⊥) (hPR : P ≤ R)
    (e : R ≃* MulAut P)
    (he : ∀ (x : R) (p : P),
      ((e x p : P) : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) * p * (x : _)⁻¹)
    (reps : List R)
    (hcover : ∀ τ : R, orderOf (τ : Equiv.Perm (Fin n)) = 2 → (τ : Equiv.Perm (Fin n)) ∉ P →
      ∃ ρ ∈ reps, ∃ g ∈ P, (τ : Equiv.Perm (Fin n)) = g * ρ * g⁻¹)
    (hwit : ∀ ρ ∈ reps, ∃ l ∈ P,
      orderOf (l * (ρ : Equiv.Perm (Fin n)) * l⁻¹ * (ρ : Equiv.Perm (Fin n))⁻¹) = 2) :
    CFSG.EvenSmallLie.FoursGroupCondition Y := by
  refine CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv eY.symm ?_
  refine foursGroupCondition_of_reps (reps.map e) ?_ ?_
  · intro φ hφ hout
    obtain ⟨a, rfl⟩ := e.surjective φ
    have haa : a * a = 1 := e.injective (by rw [map_mul, hφ, map_one])
    have haP : (a : Equiv.Perm (Fin n)) ∉ P := fun ham => hout ⟨a, ham⟩ (by
      refine MulEquiv.ext fun p => Subtype.ext ?_
      rw [he]
      simp [MulAut.conj_apply])
    have ha2 : orderOf (a : Equiv.Perm (Fin n)) = 2 :=
      orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, haa, Subgroup.coe_one])
        (fun h1 => haP (h1 ▸ P.one_mem))
    obtain ⟨ρ, hρ, g, hg, hag⟩ := hcover a ha2 haP
    refine ⟨e ρ, List.mem_map_of_mem hρ, e ⟨g, hPR hg⟩, ?_⟩
    have : a = ⟨g, hPR hg⟩ * ρ * ⟨g, hPR hg⟩⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hag)
    rw [this, map_mul, map_mul, map_inv]
  · intro ρ' hρ'
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hρ'
    obtain ⟨l, hl, h2⟩ := hwit ρ hρ
    have hv : (((⟨l, hl⟩ : P) * (e ρ ⟨l, hl⟩)⁻¹ : P) : Equiv.Perm (Fin n)) =
        l * (ρ : Equiv.Perm (Fin n)) * l⁻¹ * (ρ : Equiv.Perm (Fin n))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, he]
      show l * (↑ρ * l * (ρ : Equiv.Perm (Fin n))⁻¹)⁻¹ = _
      group
    refine ⟨⟨l, hl⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [SubgroupClass.coe_pow, hv, OneMemClass.coe_one, ← h2]
      exact pow_orderOf_eq_one _
    · rw [hc, Subgroup.mem_bot]
      intro h1
      have := congrArg Subtype.val h1
      rw [hv, OneMemClass.coe_one] at this
      rw [this, orderOf_one] at h2
      omega

end CFSG.EvenSporadicStandard.HypOne

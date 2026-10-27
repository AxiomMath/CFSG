module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Gen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1J2
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.J2FiveStrong
public import Certificates.Certificate17324
public import CFSG.Sporadic.Schreier.Co1OuterImage

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA CFSG.Open
  CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section FiveA


theorem fiveA_data :
    MRep repD0 (kG ext 88) ∧ kG ext 88 ^ 5 = 1 ∧ kG ext 88 ≠ 1 ∧
    kG ext 88 * kG ext 89 = kG ext 89 * kG ext 88 ∧
    kG ext 88 * kG ext 90 = kG ext 90 * kG ext 88 ∧ kG ext 89 ≠ 1 ∧
    wordG [kG ext 89, kG ext 90] rel1 = 1 ∧ wordG [kG ext 89, kG ext 90] rel2 = 1 ∧
    wordG [kG ext 89, kG ext 90] rel3 = 1 ∧
    Nat.card ↥(Subgroup.centralizer ({kG ext 88} : Set GL24) ⊓ GA) ≤ 3024000 := by
  have h := (Certificates.certificate17324 : fiveACheck () = true)
  simp only [fiveACheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hD, hwk, hwu, hw1, hkrep, hk5, hk1, hku, hkv, hu1, hr1, hr2, hr3, hbnd, hprod⟩ := h
  have rk := rep_nd (ext := ext) hD 88
  have ru := rep_nd (ext := ext) hD 89
  have rv := rep_nd (ext := ext) hD 90
  have hrel : ∀ w : List ℤ, Native.word [nd (kDag ext) 89, nd (kDag ext) 90]
      [ndI (kDag ext) 89, ndI (kDag ext) 90] w = Native.one () →
        wordG [kG ext 89, kG ext 90] w = 1 :=
    fun w hw => eq_one_of_rep (rep_evalW (ext := ext) hD [89, 90] w) hw
  have hcard := card_centralizer_le_of_powBound rk hbnd
  exact ⟨hkrep ▸ rk, eq_one_of_rep (rk.pow 5) hk5, ne_one_of_rep rk hwk hw1 hk1,
    (rk.mul ru).eq (by rw [hku]; exact ru.mul rk), (rk.mul rv).eq (by rw [hkv]; exact rv.mul rk),
    ne_one_of_rep ru hwu hw1 hu1, hrel _ hr1, hrel _ hr2, hrel _ hr3, hcard.trans hprod⟩

theorem card_cent_fiveA_le (x : ↥GA) (hx : MRep repD0 (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) ≤ 3024000 := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, hbd⟩ := fiveA_data
  have hxk : (x : GL24) = kG ext 88 := hx.eq hk
  rw [← Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective,
    map_centralizer_subtype' GA x, hxk]
  exact hbd

end FiveA

section Shape


theorem shapeRkAt_J2_of_data (hOut : SporadicOuterLeTwo) {G : Type} [Group G] (P : Subgroup G)
    [Finite P] (x : ↥P) (k u v : G) (hxk : (x : G) = k) (hu : u ∈ P) (hv : v ∈ P)
    (hk5 : k ^ 5 = 1) (hk1 : k ≠ 1) (hku : k * u = u * k) (hkv : k * v = v * k) (hu1 : u ≠ 1)
    (h1 : u * v * u * v⁻¹ * u⁻¹ * v⁻¹ = 1)
    (h2 : u * v * v * u * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ = 1)
    (h3 : (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) * (u * u * u * u * u * u * u) = 1)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G) ⊓ P) ≤ 3024000) :
    ShapeRkAt 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) x := by
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = Subgroup.closure ({u, v} : Set G) := ⟨_, rfl⟩
  obtain ⟨eL⟩ := nonempty_mulEquiv_J2_of_relators u v L hL h1 h2
    (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) rfl h3 hu1
  obtain ⟨hs, hcard, hnab⟩ := J2_facts_of_equiv eL
  have hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
    rw [hL]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      have hc := Subgroup.mem_centralizer_singleton_iff.2
        (show u * (x : G) = (x : G) * u by rw [hxk]; exact hku.symm)
      exact Subgroup.mem_inf.2 ⟨hc, hu⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hc := Subgroup.mem_centralizer_singleton_iff.2
        (show v * (x : G) = (x : G) * v by rw [hxk]; exact hkv.symm)
      exact Subgroup.mem_inf.2 ⟨hc, hv⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → GoodSpor 5 [.J2] T →
      GoodSpor 5 [.J2] T' := fun _ _ _ _ e h => GoodSpor.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → RkSpor 5 [.J2] T →
      RkSpor 5 [.J2] T' := fun _ _ _ _ e h => RkSpor.of_equiv e h
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* (TauCeti.CFSGIndex.sporadic .J2).Group := b
  have hG : GoodSpor 5 [.J2] ↥L := Or.inr (Or.inr ⟨.J2, by simp, ⟨eL.trans b₀⟩⟩)
  have hR : RkSpor 5 [.J2] ↥L := fun _ => rkAut_J2_five hOut eL
  refine shapeRkAt_of_bound (by norm_num) hGood hRk P x L hLC hs hnab
    (by rw [hcard]; norm_num) (by rw [hxk]; exact hk1) (by rw [hxk]; exact hk5) ?_ hG hR
  rw [hxk, hcard]
  exact hbound

end Shape

section Rel

theorem relators_of_wordG {u v : GL24} (hw1 : wordG [u, v] rel1 = 1) (hw2 : wordG [u, v] rel2 = 1)
    (hw3 : wordG [u, v] rel3 = 1) :
    u * v * u * v⁻¹ * u⁻¹ * v⁻¹ = 1 ∧ u * v * v * u * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ = 1 ∧
    (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) * (u * u * u * u * u * u * u) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [wordG, letterG, rel1, mul_assoc] using hw1
  · simpa [wordG, letterG, rel2, mul_assoc] using hw2
  · simpa [wordG, letterG, rel3, relW, mul_assoc] using hw3

end Rel

section Final


theorem tabCo1_fiveA (hOut : SporadicOuterLeTwo) (x : ↥GA) (hx : MRep repD0 (x : GL24)) :
    ShapeRkAt 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) x := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨hrep, hk5, hk1, hku, hkv, hu1, hw1, hw2, hw3, hbound⟩ := fiveA_data
  obtain ⟨h1, h2, h3⟩ := relators_of_wordG hw1 hw2 hw3
  exact shapeRkAt_J2_of_data hOut GA x _ _ _ (hx.eq hrep) (kG_mem ext 89) (kG_mem ext 90) hk5 hk1
    hku hkv hu1 h1 h2 h3 hbound

end Final


end CFSG.HardMathSupport.Dickson.I271.TabCo1

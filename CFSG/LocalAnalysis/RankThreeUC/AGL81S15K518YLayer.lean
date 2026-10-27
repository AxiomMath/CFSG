module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LieType.SeitzGeneration.ExcPlanePair
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open

section General

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.RankThree.PartOne.Sec12Three (dvd_card_center_of_mem)

theorem two_le_pRank_of_mem_centralizer {B L : Subgroup Y} {q : ℕ} (hq : q.Prime)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥L)) (hB : q ∣ Nat.card ↥(B ⊓ L)) {u : Y}
    (huB : u ∈ B) (huC : u ∈ Subgroup.centralizer (L : Set Y)) (hu : orderOf u = q) :
    2 ≤ CFSG.Open.pRank q B := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ L)) q hB
  have hao : orderOf (a : Y) = q := by rw [Subgroup.orderOf_coe, ha]
  have haB : (a : Y) ∈ B := (Subgroup.mem_inf.1 a.2).1
  have haL : (a : Y) ∈ L := (Subgroup.mem_inf.1 a.2).2
  have hcomm : Commute u (a : Y) := ((Subgroup.mem_centralizer_iff.1 huC) _ haL).symm
  have hind : (a : Y) ∉ Subgroup.zpowers u := fun h =>
    hZ (dvd_card_center_of_mem haL (fun l hl =>
      (Subgroup.mem_centralizer_iff.1 ((Subgroup.zpowers_le.2 huC) h) l hl).symm) hao)
  have hup : u ^ q = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hap : (a : Y) ^ q = 1 := by rw [← hao]; exact pow_orderOf_eq_one _
  have hE := CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair (p := q) hcomm hup hap
  have hcard := CFSG.LieType.SeitzGeneration.card_closure_pair_sq hq hcomm hu hao hind
  have hEB : Subgroup.closure ({u, (a : Y)} : Set Y) ≤ B := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact huB
    · exact haB
  exact CFSG.SectionRank.le_pRank hq.one_lt hEB hE hcard

theorem not_dvd_card_centralizer_inf_layer {L : Subgroup Y} (hL : IsComponentOf L ⊤) {q : ℕ}
    (hq : q.Prime) (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥L))
    (hI : ∀ I, IsComponentOf I ⊤ → I ≠ L → ¬ q ∣ Nat.card ↥I) :
    ¬ q ∣ Nat.card ↥(Subgroup.centralizer (L : Set Y) ⊓ CFSG.Open.rankThreeLayer ⊤) := by
  classical
  have hcom : ∀ I J : Subgroup Y, IsComponentOf I ⊤ → IsComponentOf J ⊤ → I ≠ J →
      ∀ x y : Y, x ∈ I → y ∈ J → Commute x y := by
    intro I J hI' hJ' hne x y hx hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [kComp_holds.1 _ I J hI' hJ' hne, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  let ι := {I : Subgroup Y // IsComponentOf I ⊤ ∧ I ≠ L}
  haveI : Finite ι := inferInstance
  let F : Option ι → Subgroup Y := fun o =>
    o.elim (L ⊓ Subgroup.centralizer (L : Set Y)) fun i => i.1
  have hF : ∀ o, ¬ q ∣ Nat.card ↥(F o) := by
    rintro (_ | i)
    · intro hd
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ Subgroup.centralizer
        (L : Set Y))) q hd
      have hzC := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 z.2).2
      exact hZ (dvd_card_center_of_mem (Subgroup.mem_inf.1 z.2).1 (fun l hl => (hzC l hl).symm)
        (by rw [Subgroup.orderOf_coe, hz]))
    · exact hI i.1 i.2.1 i.2.2
  have hFc : Pairwise fun o o' : Option ι => ∀ x y : Y, x ∈ F o → y ∈ F o' → Commute x y := by
    rintro (_ | i) (_ | j) hij x y hx hy
    · exact absurd rfl hij
    · exact hcom L j.1 hL j.2.1 (Ne.symm j.2.2) x y (Subgroup.mem_inf.1 hx).1 hy
    · exact hcom i.1 L i.2.1 hL i.2.2 x y hx (Subgroup.mem_inf.1 hy).1
    · exact hcom i.1 j.1 i.2.1 j.2.1 (fun h => hij (congrArg some (Subtype.ext h))) x y hx hy
  set W : Subgroup Y := ⨆ i : ι, i.1 with hW
  have hWC : W ≤ Subgroup.centralizer (L : Set Y) := by
    refine iSup_le fun i z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hcom L i.1 hL i.2.1 (Ne.symm i.2.2) g z hg hz
  have hLW : L ≤ Subgroup.normalizer (W : Set Y) :=
    (Subgroup.le_centralizer_iff.1 hWC).trans (Subgroup.centralizer_le_normalizer _)
  have hEW : CFSG.Open.rankThreeLayer (⊤ : Subgroup Y) ≤ L ⊔ W := by
    refine sSup_le fun I hI' => ?_
    by_cases h : I = L
    · exact h ▸ le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun i : ι => i.1) ⟨I, hI', h⟩)
  have hle : Subgroup.centralizer (L : Set Y) ⊓ CFSG.Open.rankThreeLayer ⊤ ≤ ⨆ o, F o := by
    intro x hx
    have hxLW : x ∈ ((L ⊔ W : Subgroup Y) : Set Y) := hEW (Subgroup.mem_inf.1 hx).2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L W hLW] at hxLW
    obtain ⟨l, hl, w, hw, rfl⟩ := hxLW
    have hlC : l ∈ Subgroup.centralizer (L : Set Y) := by
      have h1 : l = l * w * w⁻¹ := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_inf.1 hx).1 (Subgroup.inv_mem _ (hWC hw))
    rw [iSup_option]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hl, hlC⟩) hw
  intro hd
  exact not_dvd_card_iSup_of_commute F hFc hq hF (hd.trans (Subgroup.card_dvd_of_le hle))

end General

variable {X : Type} [Group X] [Finite X]

theorem dvd_card_gnA_of_mS {T Ti : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {p : ℕ}
    (hp : p.Prime) (hm : mS T Ti p Ls = 1) : p ∣ Nat.card (gnA T Ti Ls) :=
  (one_le_pRank_iff_dvd _ hp).1 hm.ge

theorem orderOf_ne_of_mem_centralizer {T Ti : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥Ls))
    (hA : p ∣ Nat.card (gnA T Ti Ls)) (hN : mN Ti p ≤ 1) {u : X ⧸ gnC T}
    (huN : u ∈ gnImg T (Subgroup.normalizer (Ti : Set X)))
    (huC : u ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) : orderOf u ≠ p := by
  intro hu
  have h2 : 2 ≤ CFSG.Open.pRank p
      ((Subgroup.normalizer (Ti : Set X)).map (QuotientGroup.mk' (gnC T))) :=
    two_le_pRank_of_mem_centralizer (B := gnImg T (Subgroup.normalizer (Ti : Set X))) (L := Ls)
      hp hZ hA huN huC hu
  have h3 := two_le_pRank_of_map (QuotientGroup.mk' (gnC T)) hp hp2
    (Subgroup.normalizer (Ti : Set X)) h2
  have hN' : CFSG.Open.pRank p (Subgroup.normalizer (Ti : Set X)) ≤ 1 := hN
  omega

theorem not_dvd_card_center_of_mS {T T₁ T₂ : Subgroup X} (hc : GNCentre T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T))) {p : ℕ} (hp : p.Prime)
    (m1 : mS T T₁ p Ls = 1) (m2 : mS T T₂ p Ls = 1) :
    ¬ p ∣ Nat.card (Subgroup.center ↥Ls) := fun h => by
  have m1' : CFSG.Open.pRank p (gnA T T₁ Ls) = 1 := m1
  have m2' : CFSG.Open.pRank p (gnA T T₂ Ls) = 1 := m2
  rcases hc Ls hLs hinv p hp h with h' | h' <;> omega

theorem not_dvd_card_of_isComponentOf_ne {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : IsComponentOf Ls ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥Ls)) (hA₁ : p ∣ Nat.card (gnA T T₁ Ls))
    (hA₂ : p ∣ Nat.card (gnA T T₂ Ls)) (hN₁ : mN T₁ p ≤ 1) (hN₂ : mN T₂ p ≤ 1)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is)
    {Is : Subgroup (X ⧸ gnC T)} (hIs : IsComponentOf Is ⊤) (hne : Is ≠ Ls) :
    ¬ p ∣ Nat.card ↥Is := by
  by_cases hY : GNYComponent T T₁ T₂ Is
  · exact hoth Is hY hne
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Is) p hd
  have huo : orderOf (u : X ⧸ gnC T) = p := by rw [Subgroup.orderOf_coe, hu]
  have huC : (u : X ⧸ gnC T) ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := Subgroup.commutator_mem_commutator hg u.2
    rw [kComp_holds.1 _ Ls Is hLs hIs (Ne.symm hne), Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hcov : Is ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      Is ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
    by_contra h
    rw [not_or] at h
    exact hY ⟨hIs, h.1, h.2⟩
  rcases hcov with h | h
  · have huN : (u : X ⧸ gnC T) ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
      Subgroup.map_mono (Subgroup.centralizer_le_normalizer (T₁ : Set X)) (h u.2)
    exact orderOf_ne_of_mem_centralizer hp hp2 hZ hA₁ hN₁ huN huC huo
  · exact orderOf_ne_of_mem_centralizer hp hp2 hZ hA₂ hN₂ (h u.2) huC huo

theorem not_dvd_card_centralizer_inf_layer_of_k518Y {T T₁ T₂ : Subgroup X}
    (hc : GNCentre T T₁ T₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m1 : mS T T₁ p Ls = 1) (m2 : mS T T₂ p Ls = 1) (n1 : mN T₁ p = 1) (n2 : mN T₂ p = 1)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) :
    ¬ p ∣ Nat.card ↥(Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) ⊓
      CFSG.Open.rankThreeLayer ⊤) := by
  have hZ := not_dvd_card_center_of_mS hc hLs hinv hp m1 m2
  exact not_dvd_card_centralizer_inf_layer hLs.1 hp hZ fun I hI hne =>
    not_dvd_card_of_isComponentOf_ne hLs.1 hp hp2 hZ (dvd_card_gnA_of_mS hp m1)
      (dvd_card_gnA_of_mS hp m2) n1.le n2.le hoth hI hne

end CFSG.LocalAnalysis.RankThreeUC.S15

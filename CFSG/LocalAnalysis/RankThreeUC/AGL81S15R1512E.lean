module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

section Interface1510

variable {X : Type} [Group X] [Finite X]

theorem one_le_pRank_iff_dvd {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) {q : ℕ}
    (hq : q.Prime) : 1 ≤ CFSG.Open.pRank q A ↔ q ∣ Nat.card A := by
  refine ⟨fun h => ?_, one_le_pRank_of_dvd A hq⟩
  obtain ⟨E, hEA, -, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have h1 : q ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self q (by omega)
  exact h1.trans (Subgroup.card_dvd_of_le hEA)

theorem mem_normalizer_of_map_conj_eq_s15 {Y : Type*} [Group Y] {A : Subgroup Y} {g : Y}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

theorem lift_normal_of_two_le_pRank {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hL : LiftOf T L Ls) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hX3 : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 3) (hL2 : 2 ≤ CFSG.Open.pRank q L)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥(barO2 L))) : L.Normal ∧ Ls.Normal := by
  have hLn : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    by_contra hcon
    have hC2 : IsC2 (L.map (MulAut.conj g).toMonoidHom) := liftOf_conj_aux4 hL.1 g
    have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := by
      intro h
      apply hcon
      have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨n, hn, by simp [MulAut.conj_apply]⟩
      rw [← h] at hmem
      exact hmem
    have hs : CFSG.Open.pRank q ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ 0 := by
      by_contra hlt
      push Not at hlt
      have h1 := (one_le_pRank_iff_dvd _ hq).1 hlt
      rw [Subgroup.card_map_of_injective (barO2 L).subtype_injective] at h1
      exact hZ h1
    have hsum := pRank_add_le_pRank_sup hL.1 hC2 hne hq hq2 hs
    have hmono : CFSG.Open.pRank q L ≤ CFSG.Open.pRank q (L.map (MulAut.conj g).toMonoidHom) :=
      CFSG.SectionRank.pRank_le_map hq.one_lt _ (fun a b h => (MulAut.conj g).injective h) L
    have hle : CFSG.Open.pRank q (L ⊔ L.map (MulAut.conj g).toMonoidHom) ≤ 3 :=
      (CFSG.SectionRank.pRank_mono hq.one_lt le_top).trans hX3
    omega
  refine ⟨hLn, ?_⟩
  rw [← hL.2]
  exact Subgroup.Normal.map hLn (toStar T) (QuotientGroup.mk'_surjective _)

theorem gnImg_le_normalizer_of_normal {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (h : Ls.Normal) :
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
  haveI := h
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem two_le_pRank_of_two_components' {Y : Type} [Group Y] [Finite Y] {B Ls Is : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤) (hIs : IsComponentOf Is ⊤) (hne : Ls ≠ Is) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls))
    (hB : q ∣ Nat.card ↥(B ⊓ Ls)) (hB' : q ∣ Nat.card ↥(B ⊓ Is)) :
    2 ≤ CFSG.Open.pRank q B := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ Ls)) q hB
  obtain ⟨b', hb'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ Is)) q hB'
  have hai : orderOf (a' : Y) = q ^ 1 := by rw [Subgroup.orderOf_coe, ha', pow_one]
  have hbj : orderOf (b' : Y) = q ^ 1 := by rw [Subgroup.orderOf_coe, hb', pow_one]
  have haM : (a' : Y) ∈ B ⊓ Ls := a'.2
  have hbM : (b' : Y) ∈ B ⊓ Is := b'.2
  have haB : (a' : Y) ∈ B := (Subgroup.mem_inf.1 haM).1
  have haL : (a' : Y) ∈ Ls := (Subgroup.mem_inf.1 haM).2
  have hbB : (b' : Y) ∈ B := (Subgroup.mem_inf.1 hbM).1
  have hbI : (b' : Y) ∈ Is := (Subgroup.mem_inf.1 hbM).2
  have hcomm : ⁅Ls, Is⁆ = ⊥ := kComp_holds.1 Y Ls Is hLs hIs hne
  have hcom : ∀ x ∈ Ls, ∀ y ∈ Is, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hab : Commute (a' : Y) (b' : Y) := hcom _ haL _ hbI
  have hpa : IsPGroup q (Subgroup.zpowers (a' : Y)) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hai]⟩
  have hpb : IsPGroup q (Subgroup.zpowers (b' : Y)) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hbj]⟩
  have hnorm : Subgroup.zpowers (a' : Y) ≤ Subgroup.normalizer (Subgroup.zpowers (b' : Y) : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers (b' : Y) : Set Y))
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hab.zpow_right n).symm.eq
  have hE : IsPGroup q (Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y) : Subgroup Y) :=
    hpa.to_sup_of_normal_right' hpb hnorm
  have hEB : (Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y) : Subgroup Y) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 haB) (Subgroup.zpowers_le.2 hbB)
  by_contra hlt
  have hcyc : IsCyclic (Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y) : Subgroup Y) := by
    by_contra hnc
    have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hq hq2 hE hnc
    exact hlt (h2.trans (CFSG.SectionRank.pRank_mono hq.one_lt hEB))
  have haE : (a' : Y) ∈ (Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y) : Subgroup Y) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbE : (b' : Y) ∈ (Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y) : Subgroup Y) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h1 : (a' : Y) ∈ Subgroup.zpowers (b' : Y) :=
    mem_zpowers_of_isCyclic_of_orderOf hcyc hq haE hbE hai hbj le_rfl
  have haI : (a' : Y) ∈ Is := Subgroup.zpowers_le.2 hbI h1
  have hcL : (a' : Y) ∈ (Subgroup.center ↥Ls).map Ls.subtype := by
    refine ⟨⟨(a' : Y), haL⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    exact Subtype.ext (hcom g g.2 _ haI)
  obtain ⟨z, hz, hza⟩ := hcL
  apply hZ
  have hzo : orderOf z = q := by
    have h2 : orderOf (z : Y) = orderOf z := Subgroup.orderOf_coe z
    have h3 : (z : Y) = (a' : Y) := hza
    rw [← h2, h3, hai, pow_one]
  rw [← hzo, ← Subgroup.orderOf_mk z hz]
  exact orderOf_dvd_natCard _

theorem not_dvd_card_gnA_of_ne {T Ti : Subgroup X} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hN : CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) ≤ 1)
    {Ls Is : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤) (hIs : IsComponentOf Is ⊤)
    (hne : Ls ≠ Is) (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls))
    (hA : q ∣ Nat.card (gnA T Ti Ls)) : ¬ q ∣ Nat.card (gnA T Ti Is) := by
  intro hA'
  have h2 := two_le_pRank_of_two_components' (B := gnImg T (Subgroup.normalizer (Ti : Set X)))
    hLs hIs hne hq hq2 hZ hA hA'
  have h3 := two_le_pRank_of_map (QuotientGroup.mk' (gnC T)) hq hq2
    (Subgroup.normalizer (Ti : Set X)) h2
  omega

theorem gnImg_le_normalizer_of_dvd_gnA {T Ti : Subgroup X}
    (hT : T ≤ Subgroup.normalizer (Ti : Set X)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hN : CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls)) (hA : q ∣ Nat.card (gnA T Ti Ls)) :
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := hg
  apply mem_normalizer_of_map_conj_eq_s15
  by_contra hne
  have hKmap : (Subgroup.normalizer (Ti : Set X)).map (MulAut.conj t).toMonoidHom =
      Subgroup.normalizer (Ti : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    have hTi : Subgroup.map (MulAut.conj t).toMonoidHom Ti = Ti :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT ht)
    rw [hTi]
  have hNimg : (gnImg T (Subgroup.normalizer (Ti : Set X))).map
      (MulAut.conj (toStar T t)).toMonoidHom =
        gnImg T (Subgroup.normalizer (Ti : Set X)) :=
    gnImg_map_conj_eq hKmap
  have hAeq : gnA T Ti (Ls.map (MulAut.conj (toStar T t)).toMonoidHom) =
      (gnA T Ti Ls).map (MulAut.conj (toStar T t)).toMonoidHom := by
    unfold gnA
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (toStar T t)).injective, hNimg]
  have hA' : q ∣ Nat.card (gnA T Ti (Ls.map (MulAut.conj (toStar T t)).toMonoidHom)) := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj (toStar T t)).injective]
    exact hA
  have hLs' : IsComponentOf (Ls.map (MulAut.conj (toStar T t)).toMonoidHom) ⊤ :=
    isComponentOf_conj_aux hLs _
  have hZ' : ¬ q ∣ Nat.card
      (Subgroup.center ↥(Ls.map (MulAut.conj (toStar T t)).toMonoidHom)) := by
    rw [Nat.card_congr (Subgroup.centerCongr
      (Ls.equivMapOfInjective (MulAut.conj (toStar T t)).toMonoidHom
        (MulAut.conj (toStar T t)).injective)).toEquiv.symm]
    exact hZ
  exact (not_dvd_card_gnA_of_ne hq hq2 hN hLs' hLs hne hZ' hA') hA

theorem not_dvd_card_iSup_of_commute {Y : Type} [Group Y] [Finite Y] {ι : Type} [Finite ι]
    (H : ι → Subgroup Y)
    (hcomm : Pairwise fun i j : ι => ∀ x y : Y, x ∈ H i → y ∈ H j → Commute x y) {q : ℕ}
    (hq : q.Prime) (h : ∀ i, ¬ q ∣ Nat.card (H i)) : ¬ q ∣ Nat.card (⨆ i, H i : Subgroup Y) := by
  haveI := Fintype.ofFinite ι
  intro hdvd
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hdvd
  have h1 : Nat.card (Subgroup.noncommPiCoprod hcomm).range ∣ Nat.card (∀ i, H i) :=
    Subgroup.card_range_dvd _
  have h2 : Nat.card (∀ i, H i) = ∏ i, Nat.card (H i) := Nat.card_pi
  have h3 := hdvd.trans h1
  rw [h2] at h3
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 h3
  exact h i hi

theorem pElementSubgroup_ystar_le_of_others {T T₁ T₂ : Subgroup X} {q : ℕ} (hq : q.Prime)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ q ∣ Nat.card Is) :
    pElementSubgroup q (Ystar T T₁ T₂) ≤ Ls := by
  classical
  let ι := {I : Subgroup (X ⧸ gnC T) // GNYComponent T T₁ T₂ I ∧ I ≠ Ls}
  haveI : Finite ι := inferInstance
  let H : ι → Subgroup (X ⧸ gnC T) := fun i => i.1
  have hcomm : ∀ i j : ι, i ≠ j → ∀ x y : X ⧸ gnC T, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [kComp_holds.1 _ i.1 j.1 i.2.1.1 j.2.1.1 hne, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hW : ¬ q ∣ Nat.card (⨆ i, H i : Subgroup (X ⧸ gnC T)) :=
    not_dvd_card_iSup_of_commute H (fun i j hij => hcomm i j hij) hq
      (fun i => hoth i.1 i.2.1 i.2.2)
  set W : Subgroup (X ⧸ gnC T) := ⨆ i, H i with hWdef
  have hcen : ∀ x ∈ Ls, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ (⨆ i, H i : Subgroup (X ⧸ gnC T)) := hy
    have hle : ∀ i : ι, H i ≤ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
      intro i z hz
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := Subgroup.commutator_mem_commutator hg hz
      rw [kComp_holds.1 _ Ls i.1 hLs.1 i.2.1.1 (Ne.symm i.2.2), Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have := (iSup_le hle : (⨆ i, H i) ≤ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) hy'
    exact (Subgroup.mem_centralizer_iff.1 this) x hx
  have hLE : Ls ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have hc : x * w = w * x := hcen x hx w hw
      have h2 : x * w * x⁻¹ = w := by rw [hc]; group
      rw [h2]; exact hw
    · intro hw
      have hc : x * (x * w * x⁻¹) = (x * w * x⁻¹) * x := hcen x hx _ hw
      have h3 : x * w * x⁻¹ = w := by
        calc x * w * x⁻¹ = x⁻¹ * (x * (x * w * x⁻¹)) := by group
          _ = x⁻¹ * ((x * w * x⁻¹) * x) := by rw [hc]
          _ = w := by group
      exact h3 ▸ hw
  have hYle : Ystar T T₁ T₂ ≤ Ls ⊔ W := by
    unfold Ystar
    refine iSup₂_le fun L hL => ?_
    by_cases h : L = Ls
    · exact h ▸ le_sup_left
    · exact le_sup_of_le_right (le_iSup H (⟨L, hL, h⟩ : ι))
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxY, k, hk⟩
  have hx := hYle hxY
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Ls W hLE] at hx
  obtain ⟨l, hl, w, hw, rfl⟩ := hx
  have hc : Commute l w := hcen l hl w hw
  have hwm : w ^ Nat.card W = 1 := by
    have h1 : (⟨w, hw⟩ : ↥W) ^ Nat.card W = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hlm : (l * w) ^ Nat.card W ∈ Ls := by
    rw [hc.mul_pow, hwm, mul_one]
    exact Subgroup.pow_mem _ hl _
  have hcop : Nat.Coprime (Nat.card W) (orderOf (l * w)) := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).2 hW).symm.pow_right k
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hfin : l * w ∈ Ls := by
    rw [← hj]
    exact Subgroup.pow_mem _ hlm j
  exact hfin

theorem pElement_le_comap_of_others {T T₁ T₂ : Subgroup X} {q : ℕ} (hq : q.Prime)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ q ∣ Nat.card Is)
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Y0 T T₁ T₂) :
    pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨-, k, hk⟩
  have hx : x ∈ Y0 T T₁ T₂ := hle (Subgroup.subset_closure ⟨Subgroup.mem_top x, k, hk⟩)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1
    (hk ▸ orderOf_map_dvd (toStar T) x : orderOf (toStar T x) ∣ q ^ k)
  have h1 : toStar T x ∈ pElementSubgroup q (Ystar T T₁ T₂) :=
    Subgroup.subset_closure ⟨hx, j, hj⟩
  exact pElementSubgroup_ystar_le_of_others hq hLs hoth h1

theorem gnYComponent_unique_of_forall_dvd {T T₁ T₂ : Subgroup X} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h₁ : CFSG.Open.pRank q (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls))
    (hall : ∀ I, GNYComponent T T₁ T₂ I → q ∣ Nat.card (gnA T T₁ I)) :
    ∀ I, GNYComponent T T₁ T₂ I → I = Ls := by
  intro I hI
  by_contra hne
  exact not_dvd_card_gnA_of_ne hq hq2 h₁ hLs.1 hI.1 (Ne.symm hne) hZ (hall Ls hLs) (hall I hI)

theorem mS_mN_eq_one_of_dvd {T Ti : Subgroup X} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hN : CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) ≤ 1) (Ls : Subgroup (X ⧸ gnC T))
    (hA : q ∣ Nat.card (gnA T Ti Ls)) : mS T Ti q Ls = 1 ∧ mN Ti q = 1 := by
  have h1 : 1 ≤ CFSG.Open.pRank q (gnA T Ti Ls) := one_le_pRank_of_dvd _ hq hA
  have h2 : CFSG.Open.pRank q (gnA T Ti Ls) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have := two_le_pRank_normalizer_of_gnA T Ti Ls hq hq2 hlt
    omega
  have h3 : 1 ≤ CFSG.Open.pRank q (Subgroup.normalizer (Ti : Set X)) := by
    have := dvd_card_normalizer_of_dvd_gnA T Ti Ls hq hA
    exact one_le_pRank_of_dvd _ hq (this.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact ⟨le_antisymm h2 h1, le_antisymm hN h3⟩

theorem not_pElementSubgroup_le_centre {Y : Type} [Group Y] [Finite Y] {A Ls : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (hA : A ≤ Ls) (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls))
    (hd : q ∣ Nat.card A) :
    ¬ pElementSubgroup q Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) q hd
  intro hle
  have hxL : (x : Y) ∈ Ls := hA x.2
  have hord : orderOf (x : Y) = q := by rw [Subgroup.orderOf_coe]; exact hx
  have hmem : (x : Y) ∈ pElementSubgroup q Ls :=
    Subgroup.subset_closure ⟨hxL, 1, by rw [hord, pow_one]⟩
  obtain ⟨z, hz, hzx⟩ := hle hmem
  apply hZ
  have h1 : orderOf z = q := by
    have h2 : orderOf (z : Y) = orderOf z := Subgroup.orderOf_coe z
    have h3 : (z : Y) = (x : Y) := hzx
    rw [← h2, h3, hord]
  rw [← h1, ← Subgroup.orderOf_mk z hz]
  exact orderOf_dvd_natCard _

theorem pRank_le_of_pElementSubgroup_le {L : Subgroup X} {q : ℕ}
    (hq : q.Prime) (h : pElementSubgroup q (⊤ : Subgroup X) ≤ L) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ CFSG.Open.pRank q L := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup X)
  have hEL : E ≤ L := by
    intro x hx
    apply h
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top x, ?_⟩
    have h3 : orderOf x ∣ q ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 h3
    exact ⟨m, hm⟩
  exact CFSG.SectionRank.le_pRank hq.one_lt hEL hE hcard

end Interface1510

end CFSG.LocalAnalysis.RankThreeUC.S15

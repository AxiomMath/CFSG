module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem exists_pElement_not_mem {Y : Type} [Group Y] (p : ℕ) (A Z : Subgroup Y)
    (h : ¬ pElementSubgroup p A ≤ Z) :
    ∃ y ∈ A, y ∉ Z ∧ ∃ k : ℕ, orderOf y = p ^ k := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold pElementSubgroup
  refine (Subgroup.closure_le Z).2 ?_
  rintro x ⟨hxA, k, hk⟩
  by_contra hxZ
  exact hcon x hxA hxZ k hk

theorem eq_of_card_eq_of_isCyclic_aux {G : Type*} [Group G] [Finite G] {Q Y Y' : Subgroup G}
    (hQ : IsCyclic Q) (hY : Y ≤ Q) (hY' : Y' ≤ Q) (h : Nat.card Y = Nat.card Y') : Y = Y' := by
  have h1 : Y.subgroupOf Q = Y'.subgroupOf Q := by
    refine (IsCyclic.subgroup_eq_iff_card_eq (H := Y.subgroupOf Q) (K := Y'.subgroupOf Q)).2 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY').toEquiv]
    exact h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hY, inf_of_le_left hY'] at h1
  exact h1

theorem mem_zpowers_of_isCyclic_of_orderOf {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : IsCyclic E) {q : ℕ} (hq : q.Prime) {a b : Y} (ha : a ∈ E) (hb : b ∈ E) {i j : ℕ}
    (hi : orderOf a = q ^ i) (hj : orderOf b = q ^ j) (hij : i ≤ j) : a ∈ Subgroup.zpowers b := by
  have hdvd : q ^ (j - i) ∣ orderOf b := hj ▸ pow_dvd_pow q (Nat.sub_le j i)
  have hc : orderOf (b ^ q ^ (j - i)) = q ^ i := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hq.ne_zero) hdvd, hj, Nat.pow_div (Nat.sub_le j i) hq.pos]
    congr 1
    omega
  have hle1 : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.2 ha
  have hle2 : Subgroup.zpowers (b ^ q ^ (j - i)) ≤ E := Subgroup.zpowers_le.2 (E.pow_mem hb _)
  have heq : Subgroup.zpowers a = Subgroup.zpowers (b ^ q ^ (j - i)) :=
    eq_of_card_eq_of_isCyclic_aux hE hle1 hle2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hi, hc])
  have hmem : a ∈ Subgroup.zpowers (b ^ q ^ (j - i)) := heq ▸ Subgroup.mem_zpowers a
  exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _) hmem

theorem two_le_pRank_of_two_components {Y : Type} [Group Y] [Finite Y] {B Ls Is : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤) (hIs : IsComponentOf Is ⊤) (hne : Ls ≠ Is) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hy : ¬ pElementSubgroup q (B ⊓ Ls) ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hy' : ¬ pElementSubgroup q (B ⊓ Is) ≤ (Subgroup.center ↥Is).map Is.subtype) :
    2 ≤ CFSG.Open.pRank q B := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, haM, haZ, i, hi⟩ := exists_pElement_not_mem q _ _ hy
  obtain ⟨b, hbM, hbZ, j, hj⟩ := exists_pElement_not_mem q _ _ hy'
  have haB : a ∈ B := (Subgroup.mem_inf.1 haM).1
  have haL : a ∈ Ls := (Subgroup.mem_inf.1 haM).2
  have hbB : b ∈ B := (Subgroup.mem_inf.1 hbM).1
  have hbI : b ∈ Is := (Subgroup.mem_inf.1 hbM).2
  have hcomm : ⁅Ls, Is⁆ = ⊥ := kComp_holds.1 Y Ls Is hLs hIs hne
  have hcom : ∀ x ∈ Ls, ∀ y ∈ Is, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hcL : ∀ x ∈ Ls, x ∈ Is → x ∈ (Subgroup.center ↥Ls).map Ls.subtype := by
    intro x hxL hxI
    refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    exact Subtype.ext (hcom g g.2 x hxI)
  have hcI : ∀ x ∈ Ls, x ∈ Is → x ∈ (Subgroup.center ↥Is).map Is.subtype := by
    intro x hxL hxI
    refine ⟨⟨x, hxI⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    exact Subtype.ext (hcom x hxL g g.2).symm
  have hab : Commute a b := hcom a haL b hbI
  have hpa : IsPGroup q (Subgroup.zpowers a) :=
    IsPGroup.iff_card.2 ⟨i, by rw [Nat.card_zpowers, hi]⟩
  have hpb : IsPGroup q (Subgroup.zpowers b) :=
    IsPGroup.iff_card.2 ⟨j, by rw [Nat.card_zpowers, hj]⟩
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set Y))
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hab.zpow_right n).symm.eq
  have hE : IsPGroup q (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) :=
    hpa.to_sup_of_normal_right' hpb hnorm
  have hEB : (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 haB) (Subgroup.zpowers_le.2 hbB)
  by_contra hlt
  have hcyc : IsCyclic (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) := by
    by_contra hnc
    have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hq hq2 hE hnc
    exact hlt (h2.trans (CFSG.SectionRank.pRank_mono hq.one_lt hEB))
  have haE : a ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbE : b ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  rcases le_total i j with hij | hji
  · have h1 : a ∈ Subgroup.zpowers b :=
      mem_zpowers_of_isCyclic_of_orderOf hcyc hq haE hbE hi hj hij
    exact haZ (hcL a haL (Subgroup.zpowers_le.2 hbI h1))
  · have h1 : b ∈ Subgroup.zpowers a :=
      mem_zpowers_of_isCyclic_of_orderOf hcyc hq hbE haE hj hi hji
    exact hbZ (hcI b (Subgroup.zpowers_le.2 haL h1) hbI)

theorem gnYComponent_unique {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    (h₁ : CFSG.Open.pRank 3 (normalizer (T₁ : Set X)) ≤ 1) {Ls Is : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) (hIs : GNYComponent T T₁ T₂ Is) : Ls = Is := by
  by_contra hne
  have h2 := two_le_pRank_of_two_components (B := gnImg T (normalizer (T₁ : Set X))) hLs.1 hIs.1
    hne Nat.prime_three (by norm_num) (hthree Ls hLs).1 (hthree Is hIs).1
  have h3 := two_le_pRank_of_map (QuotientGroup.mk' (gnC T)) Nat.prime_three (by norm_num)
    (normalizer (T₁ : Set X)) h2
  omega

theorem IsGNPair.le_normalizer₁ {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂) :
    T ≤ normalizer (T₁ : Set X) := by
  have hle : T₁ ≤ T := h.le_center.trans (omegaOneCenterOf_le_subgroup T)
  haveI := h.char₁
  have hn : (T₁.subgroupOf T).Normal := inferInstance
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := (Subgroup.normal_subgroupOf_iff hle).1 hn
  constructor
  · intro hx
    exact h1 x t hx ht
  · intro hx
    have := h1 (t * x * t⁻¹) t⁻¹ hx (T.inv_mem ht)
    simpa [mul_assoc] using this

theorem IsGNPair.le_normalizer₂ {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂) :
    T ≤ normalizer (T₂ : Set X) := by
  have hle : T₂ ≤ T := h.le₂
  haveI := h.char₂
  have hn : (T₂.subgroupOf T).Normal := inferInstance
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := (Subgroup.normal_subgroupOf_iff hle).1 hn
  constructor
  · intro hx
    exact h1 x t hx ht
  · intro hx
    have := h1 (t * x * t⁻¹) t⁻¹ hx (T.inv_mem ht)
    simpa [mul_assoc] using this

theorem isComponentOf_conj_aux {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (g : Y) :
    CFSG.Open.IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL

theorem map_conj_eq_of_conj_mem {K : Subgroup X} {t : X} (h1 : ∀ x ∈ K, t * x * t⁻¹ ∈ K)
    (h2 : ∀ x ∈ K, t⁻¹ * x * t ∈ K) : K.map (MulAut.conj t).toMonoidHom = K := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro y hy
    refine ⟨t⁻¹ * y * t, h2 y hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup X} {t : X}
    (ht : t ∈ normalizer (S : Set X)) : ∀ x ∈ centralizer (S : Set X), t * x * t⁻¹ ∈ centralizer (S : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hn : t⁻¹ * h * t ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 ht (t⁻¹ * h * t)).2
    apply this
    simpa [mul_assoc] using hh
  have h1 := hx _ hn
  calc h * (t * x * t⁻¹) = t * ((t⁻¹ * h * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * h * t)) * t⁻¹ := by rw [h1]
    _ = t * x * t⁻¹ * h := by group

theorem gnImg_map_conj_eq {T K : Subgroup X} {t : X}
    (hK : K.map (MulAut.conj t).toMonoidHom = K) :
    (gnImg T K).map (MulAut.conj (toStar T t)).toMonoidHom = gnImg T K := by
  unfold gnImg
  rw [Subgroup.map_map]
  have hcomm : (MulAut.conj (toStar T t)).toMonoidHom.comp (QuotientGroup.mk' (gnC T)) =
      (QuotientGroup.mk' (gnC T)).comp (MulAut.conj t).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [hcomm, ← Subgroup.map_map, hK]

theorem gnYComponent_conj {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) {t : X} (ht : t ∈ T) :
    GNYComponent T T₁ T₂ (Ls.map (MulAut.conj (toStar T t)).toMonoidHom) := by
  obtain ⟨hcomp, hC, hN⟩ := hLs
  have hT1 : t ∈ normalizer (T₁ : Set X) := IsGNPair.le_normalizer₁ h ht
  have hT2 : t ∈ normalizer (T₂ : Set X) := IsGNPair.le_normalizer₂ h ht
  have hCmap : (centralizer (T₁ : Set X)).map (MulAut.conj t).toMonoidHom =
      centralizer (T₁ : Set X) :=
    map_conj_eq_of_conj_mem (conj_mem_centralizer_of_mem_normalizer hT1)
      (conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hT1) (t := t⁻¹)
        |> fun h' => by simpa using h')
  have hNmap : (normalizer (T₂ : Set X)).map (MulAut.conj t).toMonoidHom =
      normalizer (T₂ : Set X) :=
    map_conj_eq_of_conj_mem (fun x hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ hT2 hx)
        (Subgroup.inv_mem _ hT2))
      (fun x hx => by
        simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hT2) hx) hT2)
  refine ⟨isComponentOf_conj_aux hcomp _, ?_, ?_⟩
  · intro hle
    apply hC
    rw [← gnImg_map_conj_eq (T := T) hCmap] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (toStar T t)).injective).1 hle
  · intro hle
    apply hN
    rw [← gnImg_map_conj_eq (T := T) hNmap] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (toStar T t)).injective).1 hle

theorem gnImg_le_normalizer_of_unique {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls) :
    gnImg T T ≤ normalizer (Ls : Set (X ⧸ gnC T)) := by
  rintro _ ⟨t, ht, rfl⟩
  have h1 := huniq _ (gnYComponent_conj h hLs ht)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h1] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => (toStar T t)⁻¹ * z * (toStar T t)) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

theorem gnShape_classical {T T₁ T₂ : Subgroup X} (halt7 : GNAlt7 T T₁ T₂)
    (haltBig : GNAltBig T T₁ T₂) (hshape : GNShape T T₁ T₂)
    (h₁ : CFSG.Open.pRank 3 (normalizer (T₁ : Set X)) ≤ 1) (h₂ : CFSG.Open.pRank 3 (normalizer (T₂ : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ normalizer (Ls : Set (X ⧸ gnC T))) :
    IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls) ∧
      ¬ RankOneChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
  obtain ⟨-, hcl | ⟨n, hn, ⟨e⟩⟩⟩ := hshape Ls hLs
  · exact hcl
  · exfalso
    have hrk : 1 < CFSG.Open.pRank 3 (gnA T T₁ Ls) ∨ 1 < CFSG.Open.pRank 3 (gnA T T₂ Ls) := by
      rcases hn with rfl | ⟨h8, -⟩
      · exact halt7 Ls hLs.1 hinv ⟨e⟩
      · exact haltBig Ls hLs.1 n h8 ⟨e⟩
    rcases hrk with h | h
    · have := two_le_pRank_normalizer_of_gnA T T₁ Ls Nat.prime_three (by norm_num) h
      omega
    · have := two_le_pRank_normalizer_of_gnA T T₂ Ls Nat.prime_three (by norm_num) h
      omega

theorem exists_pPow_lift {Y Z : Type} [Group Y] [Group Z] [Finite Y] [Finite Z] (f : Y →* Z)
    (hf : Function.Surjective f) {q : ℕ} (hq : q.Prime) {z : Z} (hz : ∃ k : ℕ, orderOf z = q ^ k) :
    ∃ y : Y, f y = z ∧ ∃ k : ℕ, orderOf y = q ^ k := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hz
  let U : Subgroup Y := (Subgroup.zpowers z).comap f
  let g : U →* Subgroup.zpowers z := (f.comp U.subtype).codRestrict _ (fun u => u.2)
  have hg : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := hf w
    exact ⟨⟨y, hw⟩, rfl⟩
  have hpg : IsPGroup q (Subgroup.zpowers z) :=
    IsPGroup.iff_card.2 ⟨k, by rw [Nat.card_zpowers, hk]⟩
  obtain ⟨S, hSp, hSt⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.exists_isPGroup_map_eq_top hq g hg hpg
  have hz' : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈ S.map g := by
    rw [hSt]
    exact Subgroup.mem_top _
  obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.1 hz'
  obtain ⟨k', hk'⟩ := hSp ⟨u, huS⟩
  have h1 : (u : Y) ^ q ^ k' = 1 := by
    have := congrArg (fun x : S => ((x : U) : Y)) hk'
    simpa using this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨u.1, congrArg Subtype.val hu, m, hm⟩

theorem one_le_pRank_of_dvd {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Nat.card A) : 1 ≤ CFSG.Open.pRank q A := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) q h
  have hxq : (x.1 : Y) ^ q = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hel : IsElemAbelian q (Subgroup.zpowers x.1) := by
    refine ⟨inferInstance, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxq, one_zpow]
  exact CFSG.SectionRank.le_pRank hq.one_lt ((Subgroup.zpowers_le).2 x.2) hel
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])

theorem mS_mN_eq_one {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    (h₁ : CFSG.Open.pRank 3 (normalizer (T₁ : Set X)) ≤ 1) (h₂ : CFSG.Open.pRank 3 (normalizer (T₂ : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hcl : IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls)) :
    mS T T₁ 3 Ls = 1 ∧ mS T T₂ 3 Ls = 1 ∧ mN T₁ 3 = 1 ∧ mN T₂ 3 = 1 := by
  have key : ∀ Ti : Subgroup X,
      (¬ pElementSubgroup 3 (gnA T Ti Ls) ≤ (Subgroup.center ↥Ls).map Ls.subtype) →
      CFSG.Open.pRank 3 (normalizer (Ti : Set X)) ≤ 1 → mS T Ti 3 Ls = 1 ∧ mN Ti 3 = 1 := by
    intro Ti hne hle
    obtain ⟨y, hyA, hyZ, k, hk⟩ := exists_pElement_not_mem 3 _ _ hne
    have hy1 : y ≠ 1 := fun h => hyZ (h ▸ one_mem _)
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hy1 (orderOf_eq_one_iff.1 (by simpa using hk))
    have hdvd : 3 ∣ Nat.card (gnA T Ti Ls) := by
      have h1 : orderOf y ∣ Nat.card (gnA T Ti Ls) := by
        rw [← Subgroup.orderOf_mk y hyA]
        exact orderOf_dvd_natCard _
      rw [hk] at h1
      exact (dvd_pow_self 3 hk1).trans h1
    have h1 : 1 ≤ CFSG.Open.pRank 3 (gnA T Ti Ls) := one_le_pRank_of_dvd _ Nat.prime_three hdvd
    have h2 : CFSG.Open.pRank 3 (gnA T Ti Ls) ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have := two_le_pRank_normalizer_of_gnA T Ti Ls Nat.prime_three (by norm_num) hlt
      omega
    have h3 : 1 ≤ CFSG.Open.pRank 3 (normalizer (Ti : Set X)) := by
      have := dvd_card_normalizer_of_dvd_gnA T Ti Ls Nat.prime_three hdvd
      exact one_le_pRank_of_dvd _ Nat.prime_three
        (this.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact ⟨le_antisymm h2 h1, le_antisymm hle h3⟩
  obtain ⟨a1, a2⟩ := key T₁ (hthree Ls hLs).1 h₁
  obtain ⟨b1, b2⟩ := key T₂ ((hthree Ls hLs).2 (Or.inl hcl)) h₂
  exact ⟨a1, b1, a2, b2⟩

theorem Y0_eq_comap_of_unique {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) (huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls) :
    Y0 T T₁ T₂ = Ls.comap (toStar T) := by
  have h : Ystar T T₁ T₂ = Ls := by
    apply le_antisymm
    · exact iSup₂_le fun L hL => (huniq L hL).le
    · exact le_iSup₂_of_le (f := fun L (_ : L ∈ {L : Subgroup (X ⧸ gnC T) | GNYComponent T T₁ T₂ L}) => L) Ls hLs le_rfl
  unfold Y0
  rw [h]

theorem three_le_pRank_of_le_comap {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hC : ¬ 3 ∣ Nat.card (gnC T)) (hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : 3 ≤ CFSG.Open.pRank 3 Ls := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup X)
  have hEle : E ≤ Ls.comap (toStar T) := by
    intro x hx
    apply hle
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top x, ?_⟩
    have h3 : orderOf x ∣ 3 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
    exact ⟨m, hm⟩
  have hinj : Function.Injective ((toStar T).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : (x : X) ∈ gnC T := (QuotientGroup.eq_one_iff (x : X)).1 hx
    have h3 : orderOf (x : X) ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 x x.2)
    have h4 : orderOf (x : X) ∣ Nat.card (gnC T) := by
      rw [← Subgroup.orderOf_mk (x : X) hxC]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact Subtype.ext (orderOf_eq_one_iff.1 h)
    · exact absurd (h ▸ h4) hC
  have := hE.1
  have hle' := CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hEcard ((toStar T).comp E.subtype) hinj
    (by rintro _ ⟨x, rfl⟩; exact hEle x.2)
  exact hX.trans hle'

theorem normal_of_pElement_le_comap {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : IsComponentOf Ls ⊤) (hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype) : Ls.Normal := by
  obtain ⟨y, hyL, hyZ, k, hk⟩ := exists_pElement_not_mem 3 Ls _ hy
  have hconj : ∀ g : X ⧸ gnC T, Ls.map (MulAut.conj g).toMonoidHom = Ls := by
    intro g
    by_contra hne
    set Ls' := Ls.map (MulAut.conj g).toMonoidHom with hLs'
    have hL' : IsComponentOf Ls' ⊤ := isComponentOf_conj_aux hLs g
    have hcomm : ⁅Ls, Ls'⁆ = ⊥ := kComp_holds.1 _ Ls Ls' hLs hL' (Ne.symm hne)
    have hcom : ∀ a ∈ Ls, ∀ b ∈ Ls', a * b = b * a := by
      intro a ha b hb
      have h1 := Subgroup.commutator_mem_commutator ha hb
      rw [hcomm, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hy'L' : g * y * g⁻¹ ∈ Ls' := ⟨y, hyL, by simp [MulAut.conj_apply]⟩
    have hord : ∃ m : ℕ, orderOf (g * y * g⁻¹) = 3 ^ m := by
      refine ⟨k, ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      simpa [MulAut.conj_apply, hk] using this
    obtain ⟨u, hu, m, hm⟩ := exists_pPow_lift (toStar T) (QuotientGroup.mk'_surjective _)
      Nat.prime_three hord
    have huL : u ∈ Ls.comap (toStar T) := by
      apply hle
      apply Subgroup.subset_closure
      exact ⟨Subgroup.mem_top u, m, hm⟩
    have hy'L : g * y * g⁻¹ ∈ Ls := by
      rw [← hu]
      exact huL
    apply hyZ
    refine ⟨⟨y, hyL⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro l
    have h1 := hcom _ hy'L (g * (l : X ⧸ gnC T) * g⁻¹) ⟨l, l.2, by simp [MulAut.conj_apply]⟩
    have h2 : g * ((l : X ⧸ gnC T) * y) * g⁻¹ = g * (y * (l : X ⧸ gnC T)) * g⁻¹ := by
      calc g * ((l : X ⧸ gnC T) * y) * g⁻¹
          = (g * (l : X ⧸ gnC T) * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * (l : X ⧸ gnC T) * g⁻¹) := h1.symm
        _ = g * (y * (l : X ⧸ gnC T)) * g⁻¹ := by group
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  refine ⟨fun n hn g => ?_⟩
  have : (MulAut.conj (g : X ⧸ gnC T)) n ∈ Ls.map (MulAut.conj (g : X ⧸ gnC T)).toMonoidHom :=
    ⟨n, hn, rfl⟩
  rw [hconj] at this
  simpa [MulAut.conj_apply] using this

theorem pElementSubgroup_eq_of_isComponent {Y : Type} [Group Y] [Finite Y] {Ls : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤)
    (hy : ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype) :
    pElementSubgroup 3 Ls = Ls := by
  obtain ⟨-, -, hperf, hsimp⟩ := hLs
  have hOle : pElementSubgroup 3 Ls ≤ Ls := pElementSubgroup_le Ls
  set O : Subgroup ↥Ls := (pElementSubgroup 3 Ls).subgroupOf Ls with hO
  have hOn : O.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Y) ∈ pElementSubgroup 3 Ls := hn
    have key : ∀ x ∈ pElementSubgroup 3 Ls, (g : Y) * x * (g : Y)⁻¹ ∈ pElementSubgroup 3 Ls := by
      intro x hx
      unfold pElementSubgroup at hx ⊢
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        apply Subgroup.subset_closure
        refine ⟨Ls.mul_mem (Ls.mul_mem g.2 hx.1) (Ls.inv_mem g.2), ?_⟩
        obtain ⟨k, hk⟩ := hx.2
        refine ⟨k, ?_⟩
        have := orderOf_injective (MulAut.conj (g : Y)).toMonoidHom (MulAut.conj (g : Y)).injective x
        simpa [MulAut.conj_apply, hk] using this
      | one => simpa using Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        have : (g : Y) * (x * y) * (g : Y)⁻¹ = ((g : Y) * x * (g : Y)⁻¹) * ((g : Y) * y * (g : Y)⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have : (g : Y) * x⁻¹ * (g : Y)⁻¹ = ((g : Y) * x * (g : Y)⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hx
    show ((g * n * g⁻¹ : ↥Ls) : Y) ∈ pElementSubgroup 3 Ls
    simpa using key _ hn'
  haveI := hOn
  haveI : (O.map (QuotientGroup.mk' (Subgroup.center ↥Ls))).Normal :=
    hOn.map _ (QuotientGroup.mk'_surjective _)
  have hbt := hsimp.eq_bot_or_eq_top_of_normal (O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)))
  rcases hbt with hbot | htop
  · exfalso
    apply hy
    intro x hx
    have hxO : (⟨x, hOle hx⟩ : ↥Ls) ∈ O := hx
    have h1 : QuotientGroup.mk' (Subgroup.center ↥Ls) ⟨x, hOle hx⟩ ∈
        O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)) := ⟨_, hxO, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hOle hx⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  ·
    have hsplit : ∀ a : ↥Ls, ∃ o ∈ O, ∃ z ∈ Subgroup.center ↥Ls, a = o * z := by
      intro a
      have h1 : QuotientGroup.mk' (Subgroup.center ↥Ls) a ∈
          O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, hoa⟩ := h1
      refine ⟨o, ho, o⁻¹ * a, ?_, by simp⟩
      have : QuotientGroup.mk' (Subgroup.center ↥Ls) (o⁻¹ * a) = 1 := by
        rw [map_mul, map_inv, hoa, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcomm : ∀ a b : ↥Ls, ⁅a, b⁆ ∈ O := by
      intro a b
      obtain ⟨o, ho, z, hz, rfl⟩ := hsplit a
      obtain ⟨o', ho', z', hz', rfl⟩ := hsplit b
      have hπ : ∀ x ∈ O, QuotientGroup.mk' O x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).2 hx
      have hzz : ⁅z, z'⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz' z)
      apply (QuotientGroup.eq_one_iff _).1
      change (QuotientGroup.mk' O) ⁅o * z, o' * z'⁆ = 1
      rw [map_commutatorElement, map_mul, map_mul, hπ o ho, hπ o' ho', one_mul, one_mul,
        ← map_commutatorElement, hzz, map_one]
    have hbtop : (⊤ : Subgroup ↥Ls) ≤ O := by
      rw [← hperf, _root_.commutator_def]
      exact (Subgroup.commutator_le).2 (fun a _ b _ => hcomm a b)
    apply le_antisymm hOle
    intro x hx
    exact hbtop (Subgroup.mem_top ⟨x, hx⟩)

open KFactsPair in
theorem xlevel_three_branch_gen (hK518 : K518) (hK517 : K517_6) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    (h₁ : CFSG.Open.pRank 3 (normalizer (T₁ : Set X)) ≤ 1) (h₂ : CFSG.Open.pRank 3 (normalizer (T₂ : Set X)) ≤ 1)
    (hX3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {Ls₀ : Subgroup (X ⧸ gnC T)}
    (hLs₀ : GNYComponent T T₁ T₂ Ls₀) {L : Subgroup X} (hL : LiftOf T L Ls₀) :
    ∃ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls ∧ Ls.Normal ∧
      ¬ 3 ∣ Nat.card (gnC T) ∧ pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T) ∧
      ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype ∧ 3 ≤ CFSG.Open.pRank 3 Ls ∧
      (IsUFourOdd ↥Ls ∨
        (CFSG.Open.pRank 3 Ls = 3 ∧ (HasLThreeCore (gnA T T₁ Ls) ∨ HasLThreeCore (gnA T T₂ Ls)))) := by
  have huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls₀ := fun Is hIs =>
    gnYComponent_unique hg.three h₁ hIs hLs₀
  have hinv := gnImg_le_normalizer_of_unique hg.pair hLs₀ huniq
  obtain ⟨hcl, -⟩ := gnShape_classical hg.alt7 hg.altBig hg.shape h₁ h₂ hLs₀ hinv
  obtain ⟨m1, m2, n1, n2⟩ := mS_mN_eq_one hg.three h₁ h₂ hLs₀ hcl
  obtain ⟨hC, hY⟩ := hK518 X T T₁ T₂ hX hg 3 Nat.prime_three (by norm_num) Ls₀ L hLs₀ hL hinv
    m1 m2 n1 n2
  have hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls₀.comap (toStar T) :=
    hY fun Is hIs hne => absurd (huniq Is hIs) hne
  have hy : ¬ pElementSubgroup 3 Ls₀ ≤ (Subgroup.center ↥Ls₀).map Ls₀.subtype := by
    intro h
    apply (hg.three Ls₀ hLs₀).1
    have hA : gnA T T₁ Ls₀ ≤ Ls₀ := inf_le_right
    have hmono : pElementSubgroup 3 (gnA T T₁ Ls₀) ≤ pElementSubgroup 3 Ls₀ := by
      unfold pElementSubgroup
      exact Subgroup.closure_mono (fun x hx => ⟨hA hx.1, hx.2⟩)
    exact hmono.trans h
  have hnorm : Ls₀.Normal := normal_of_pElement_le_comap hLs₀.1 hle hy
  have h3 : 3 ≤ CFSG.Open.pRank 3 Ls₀ := three_le_pRank_of_le_comap hC hle hX3
  refine ⟨Ls₀, hLs₀, hnorm, hC, hle, hy, h3, ?_⟩
  exact hK517 X T T₁ T₂ hX hg Ls₀ hLs₀ hinv (isChevTwo_of_classicalTwoOrG2 hcl) (by omega) m1 m2

open KFactsPair in
theorem xlevel_three_branch (hK518 : K518) (hK517 : K517_6) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    (h₁ : CFSG.Open.pRank 3 (normalizer (T₁ : Set X)) ≤ 1) (h₂ : CFSG.Open.pRank 3 (normalizer (T₂ : Set X)) ≤ 1)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) {Ls₀ : Subgroup (X ⧸ gnC T)}
    (hLs₀ : GNYComponent T T₁ T₂ Ls₀) {L : Subgroup X} (hL : LiftOf T L Ls₀) :
    ∃ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls ∧ Ls.Normal ∧
      ¬ 3 ∣ Nat.card (gnC T) ∧ pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T) ∧
      ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype ∧ 3 ≤ CFSG.Open.pRank 3 Ls ∧
      (IsUFourOdd ↥Ls ∨
        (CFSG.Open.pRank 3 Ls = 3 ∧ (HasLThreeCore (gnA T T₁ Ls) ∨ HasLThreeCore (gnA T T₂ Ls)))) :=
  xlevel_three_branch_gen hK518 hK517 hX hg h₁ h₂ hX3.ge hLs₀ hL

end XLevel
end CFSG.LocalAnalysis.RankThreeUC.S15

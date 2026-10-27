module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.StronglyEmbeddedInvolution
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.StronglyEmbedded.SteinbergBKSylowInheritance
public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCentralizer
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped Pointwise

section General

variable {X : Type*} [Group X] [Finite X]

private theorem exists_involution_of_even_card {L : Subgroup X} (hL : Even (Nat.card L)) :
    ∃ t ∈ L, orderOf t = 2 := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (even_iff_two_dvd.mp hL)
  exact ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩

private theorem le_of_conj_commute_of_mem_stronglyEmbedded {H' L : Subgroup X}
    (hH' : fusionStronglyEmbedded H') {t : X} (htH' : t ∈ H') (htL : t ∈ L)
    (ht : orderOf t = 2) (hL : Even (Nat.card L)) {g0 : X}
    (hg0 : L.map (MulAut.conj g0).toMonoidHom ≠ L)
    (hcomm : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : L ≤ H' := by
  have hLg0even : Even (Nat.card (L.map (MulAut.conj g0).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g0).injective]
    exact hL
  obtain ⟨u, huLg, huord⟩ := exists_involution_of_even_card hLg0even
  have hLC : L ≤ Subgroup.centralizer ((L.map (MulAut.conj g0).toMonoidHom : Subgroup X) : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm g0 hg0)
  have hLgC : L.map (MulAut.conj g0).toMonoidHom ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp hLC
  have hCt : Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact htL)
  have huH' : u ∈ H' :=
    (CFSG.strong_embedding_involution_centralizers (show CFSG.IsStronglyEmbedded H' from hH')
      htH' ht) (hCt (hLgC huLg))
  have hLleCu : L ≤ Subgroup.centralizer ({u} : Set X) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((Subgroup.mem_centralizer_iff.mp (hLC hy)) u huLg).symm)
  exact hLleCu.trans (CFSG.strong_embedding_involution_centralizers
    (show CFSG.IsStronglyEmbedded H' from hH') huH' huord)

private theorem exists_stronglyEmbedded_conj_le {H L : Subgroup X}
    (hH : fusionStronglyEmbedded H) (hL : Even (Nat.card L))
    (hcomm : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {g0 : X} (hg0 : L.map (MulAut.conj g0).toMonoidHom ≠ L) :
    ∃ H' : Subgroup X, fusionStronglyEmbedded H' ∧ ∃ t : X, t ∈ H' ∧ t ∈ L ∧
      orderOf t = 2 ∧ L ≤ H' := by
  obtain ⟨t, htL, ht⟩ := exists_involution_of_even_card hL
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨P, hP⟩ := (CFSG.StronglyEmbedded.SteinbergBK.strongly_embedded_sylow_inheritance
    (show CFSG.IsStronglyEmbedded H from hH)).1 S
  have hPle : (P : Subgroup X) ≤ H := by
    rw [hP]
    exact Subgroup.map_subtype_le _
  obtain ⟨member, hconj⟩ :=
    CFSG.TwoRankLowerBound.Helpers.two_element_isConj_sylow P t ⟨1, by simpa using ht⟩
  obtain ⟨x, hx⟩ := isConj_iff.mp hconj
  have hxP : x * t * x⁻¹ ∈ (P : Subgroup X) := by
    rw [hx]
    exact member.2
  let H' : Subgroup X := H.map (MulAut.conj x⁻¹).toMonoidHom
  have hH' : fusionStronglyEmbedded H' := hH.map_mulEquiv (MulAut.conj x⁻¹)
  have htH' : t ∈ H' := by
    refine Subgroup.mem_map.mpr ⟨x * t * x⁻¹, hPle hxP, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact ⟨H', hH', t, htH', htL, ht,
    le_of_conj_commute_of_mem_stronglyEmbedded hH' htH' htL ht hL hg0 hcomm⟩

omit [Finite X] in
private theorem normalClosure_le_of_conj_le {H L : Subgroup X}
    (h : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≤ H) :
    Subgroup.normalClosure (L : Set X) ≤ H := by
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro y hy
  rw [Group.mem_conjugatesOfSet_iff] at hy
  obtain ⟨a, haL, hay⟩ := hy
  obtain ⟨c, hc⟩ := isConj_iff.mp hay
  exact h c (Subgroup.mem_map.mpr ⟨a, haL, by simpa [MulAut.conj_apply] using hc⟩)

private theorem all_conj_le_of_conj_commute {H' L : Subgroup X}
    (hH' : fusionStronglyEmbedded H') {t : X} (htH' : t ∈ H') (htL : t ∈ L)
    (ht : orderOf t = 2) (hLleH' : L ≤ H')
    (hcomm : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≤ H' := by
  intro g
  by_cases hg : L.map (MulAut.conj g).toMonoidHom = L
  · rw [hg]
    exact hLleH'
  · have hLgC : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (L : Set X) :=
      Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm g hg))
    have hCt : Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer ({t} : Set X) :=
      Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact htL)
    exact (hLgC.trans hCt).trans (CFSG.strong_embedding_involution_centralizers
      (show CFSG.IsStronglyEmbedded H' from hH') htH' ht)

theorem normal_of_commute_conj_of_fusionStronglyEmbedded {H L : Subgroup X}
    (hH : fusionStronglyEmbedded H) (hL : Even (Nat.card L))
    (hcomm : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : L.Normal := by
  classical
  by_contra hnorm
  have hex : ∃ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L := by
    by_contra h
    push Not at h
    exact hnorm ⟨fun n hn g => by
      have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨n, hn, by simp [MulAut.conj_apply]⟩
      rwa [h g] at hmem⟩
  obtain ⟨g0, hg0⟩ := hex
  obtain ⟨H', hH', t, htH', htL, ht, hLleH'⟩ :=
    exists_stronglyEmbedded_conj_le hH hL hcomm hg0
  have hall := all_conj_le_of_conj_commute hH' htH' htL ht hLleH' hcomm
  have hNle : Subgroup.normalClosure (L : Set X) ≤ H' := normalClosure_le_of_conj_le hall
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ H' := by
    by_contra h
    push Not at h
    exact hH'.1 (le_antisymm le_top (fun y _ => h y))
  have hNmap : (Subgroup.normalClosure (L : Set X)).map (MulAut.conj z⁻¹).toMonoidHom =
      Subgroup.normalClosure (L : Set X) := by
    apply le_antisymm
    · rintro y ⟨n, hn, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem n hn z⁻¹
    · intro y hy
      refine ⟨z * y * z⁻¹, (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem y hy z, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hNle2 : Subgroup.normalClosure (L : Set X) ≤
      H'.map (MulAut.conj z⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj z⁻¹).toMonoidHom) hNle
    rwa [hNmap] at h
  have hNleInf : Subgroup.normalClosure (L : Set X) ≤
      H' ⊓ H'.map (MulAut.conj z⁻¹).toMonoidHom := le_inf hNle hNle2
  have hLleInf : L ≤ H' ⊓ H'.map (MulAut.conj z⁻¹).toMonoidHom :=
    Subgroup.le_normalClosure.trans hNleInf
  have hdvd : Nat.card L ∣ Nat.card ↥(H' ⊓ H'.map (MulAut.conj z⁻¹).toMonoidHom) := by
    have h := Subgroup.card_subgroup_dvd_card
      (L.subgroupOf (H' ⊓ H'.map (MulAut.conj z⁻¹).toMonoidHom))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLleInf).toEquiv] at h
    exact h
  have hevenInf : Even (Nat.card ↥(H' ⊓ H'.map (MulAut.conj z⁻¹).toMonoidHom)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hL).trans hdvd)
  exact (Nat.not_even_iff_odd.mpr (hH'.2.2 z hz)) hevenInf

private theorem center_eq_bot_of_card_eq_six {L : Subgroup X} (h6 : Nat.card L = 6)
    (hnc : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc
  have hcenterP : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    decide
  have hmap := Subgroup.map_center_eq e
  rw [hcenterP] at hmap
  rwa [Subgroup.map_eq_bot_iff_of_injective (Subgroup.center L) e.injective] at hmap

private theorem centralizer_eq_bot_of_normal_card_eq_six {L : Subgroup X} [L.Normal]
    (h6 : Nat.card L = 6) (hnc : ∃ a b : L, a * b ≠ b * a) (hq : IsPGroup 2 (X ⧸ L))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥) :
    Subgroup.centralizer (L : Set X) = ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := center_eq_bot_of_card_eq_six h6 hnc
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  have hCnormal : C.Normal := Subgroup.normal_centralizer
  have hCinter : C ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.mp hx
    have hxZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) (y : X) y.2)
    exact Subgroup.mem_bot.mpr (by simpa [hZ] using hxZ)
  let f : C →* X ⧸ L := (QuotientGroup.mk' L).comp C.subtype
  have hfker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcL : (c : X) ∈ L := by
      have hc' : (c : X) ∈ (QuotientGroup.mk' L).ker := by
        rw [MonoidHom.mem_ker]
        exact hc
      rwa [QuotientGroup.ker_mk'] at hc'
    have hinf : (c : X) ∈ C ⊓ L := Subgroup.mem_inf.mpr ⟨c.2, hcL⟩
    rw [hCinter] at hinf
    exact Subtype.ext (Subgroup.mem_bot.mp hinf)
  have hC2 : IsPGroup 2 C := by
    have htop : IsPGroup 2 (⊤ : Subgroup (X ⧸ L)) :=
      IsPGroup.of_equiv hq Subgroup.topEquiv.symm
    have hrange : IsPGroup 2 f.range := htop.to_le le_top
    let iso : C ≃* f.range :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
          (QuotientGroup.quotientKerEquivRange f))
    exact IsPGroup.of_equiv hrange iso.symm
  exact hO C hCnormal hC2

private theorem card_le_six_of_centralizer_eq_bot {L : Subgroup X} [L.Normal]
    (h6 : Nat.card L = 6) (hnc : ∃ a b : L, a * b ≠ b * a)
    (hCbot : Subgroup.centralizer (L : Set X) = ⊥) : Nat.card X ≤ 6 := by
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc
  have hinj : Function.Injective (MulAut.conjNormal (H := L)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := congrArg (fun a : MulAut L => ((a ⟨l, hl⟩ : L) : X)) hx
      have h2 : x * l * x⁻¹ = l := by
        simpa only [MulAut.conjNormal_apply, map_one, MulAut.one_apply] using h
      have h3 : l * x = x * l := by
        have := congrArg (fun t => t * x) h2
        simpa [mul_assoc] using this.symm
      exact h3
    rw [hCbot] at hxC
    simpa using (Subgroup.mem_bot.mp hxC)
  have hcardAut : Nat.card (MulAut L) = 6 := by
    have h1 : Nat.card (MulAut L) = Nat.card (MulAut (Equiv.Perm (Fin 3))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h2 : Nat.card (MulAut (Equiv.Perm (Fin 3))) = Nat.card (Equiv.Perm (Fin 3)) :=
      Nat.card_congr CFSG.Quasithin.SBd.conjEquivPerm3.symm.toEquiv
    rw [h1, h2, Nat.card_perm]
    norm_num
  have h := Nat.card_le_card_of_injective (MulAut.conjNormal (H := L)) hinj
  rwa [hcardAut] at h

theorem eq_top_of_normal_of_card_eq_six {L : Subgroup X} [L.Normal] (h6 : Nat.card L = 6)
    (hnc : ∃ a b : L, a * b ≠ b * a) (hq : IsPGroup 2 (X ⧸ L))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥) : L = ⊤ := by
  have hCbot := centralizer_eq_bot_of_normal_card_eq_six h6 hnc hq hO
  have hle := card_le_six_of_centralizer_eq_bot h6 hnc hCbot
  have hLX : Nat.card L ≤ Nat.card X := Subgroup.card_le_card_group L
  have hXcard : Nat.card X = 6 := le_antisymm hle (by omega)
  exact Subgroup.eq_top_of_card_eq L (by rw [h6, hXcard])

private theorem exists_two_involutions_of_four_group {A : Subgroup X}
    (hAel : IsElemAbelian 2 A) (hAcard : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ orderOf a = 2 ∧ orderOf b = 2 := by
  have hA2 : ∀ a : A, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    simpa using hAel.2 (a : X) a.2
  have hfinA : Fintype A := Fintype.ofFinite A
  have hfinT : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have hAcard' : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card]; exact hAcard
  have hcardT : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    rw [Fintype.card_subtype_eq]
    simp [hAcard']
  have hcard4 : 1 < Fintype.card A := by rw [hAcard']; norm_num
  obtain ⟨a, ha1⟩ := Fintype.exists_ne_of_one_lt_card hcard4 (1 : A)
  have hcardT1 : 1 < Fintype.card {a : A // a ≠ 1} := by rw [hcardT]; norm_num
  let aT : {a : A // a ≠ 1} := ⟨a, ha1⟩
  obtain ⟨bT, hba⟩ := Fintype.exists_ne_of_one_lt_card hcardT1 aT
  let b : A := bT.1
  have hb1 : b ≠ 1 := bT.2
  have hbane : b ≠ a := fun h => hba (Subtype.ext h)
  refine ⟨a, b, ha1, hb1, hbane.symm, ?_, ?_⟩
  · exact orderOf_eq_prime (by simpa [pow_two] using hA2 a) ha1
  · exact orderOf_eq_prime (by simpa [pow_two] using hA2 b) hb1

private theorem eq_of_orderOf_eq_two_of_isCyclic {S : Type*} [Group S] [Finite S] [IsCyclic S]
    {x y : S} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  let Hx : Subgroup S := Subgroup.zpowers x
  let Hy : Subgroup S := Subgroup.zpowers y
  have hcardx : Nat.card Hx = 2 := by rw [Nat.card_zpowers, hx]
  have hcardy : Nat.card Hy = 2 := by rw [Nat.card_zpowers, hy]
  have heq : Hx = Hy := (IsCyclic.subgroup_eq_iff_card_eq).mpr (hcardx.trans hcardy.symm)
  have hxmem : x ∈ Hy := by rw [← heq]; exact Subgroup.mem_zpowers x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hy).mp hxmem with h | h
  · exact absurd h hx1
  · exact h

private theorem eq_of_orderOf_eq_two_of_quaternion {n : ℕ} [NeZero n]
    {x y : QuaternionGroup n} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  rw [CFSG.BrauerSuzuki.Helpers.quat_unique_order_two hx,
    CFSG.BrauerSuzuki.Helpers.quat_unique_order_two hy]

private theorem false_of_sylow_cyclic_or_quaternion {S : Sylow 2 X}
    (hS : IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    {x y : S} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) : False := by
  rcases hS with hcyc | ⟨r, -, ⟨eQ⟩⟩
  · have : IsCyclic (S : Subgroup X) := hcyc
    exact hxy (eq_of_orderOf_eq_two_of_isCyclic hx hy)
  · have hN0 : 2 ^ (r - 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have : NeZero (2 ^ (r - 2)) := ⟨hN0⟩
    have hx' : orderOf (eQ x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
    have hy' : orderOf (eQ y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy
    exact hxy (eQ.injective (eq_of_orderOf_eq_two_of_quaternion hx' hy'))

theorem false_of_isQuasisimple_of_sylow_cyclic_or_quaternion {L : Subgroup X}
    (hL : CFSG.IsQuasisimple L) (hZ : Odd (Nat.card (Subgroup.center L)))
    (hS : ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) : False := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ≤ CFSG.pRank 2 L :=
    CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hL hZ
  obtain ⟨A, hAel, hAcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  obtain ⟨a, b, ha1, hb1, hbane, haord, hbord⟩ :=
    exists_two_involutions_of_four_group hAel hAcard
  have haordX : orderOf (((a : A) : L) : X) = 2 :=
    (Subgroup.orderOf_coe ((a : A) : L)).trans ((Subgroup.orderOf_coe a).trans haord)
  have hbordX : orderOf (((b : A) : L) : X) = 2 :=
    (Subgroup.orderOf_coe ((b : A) : L)).trans ((Subgroup.orderOf_coe b).trans hbord)
  have hAabne : (((a : A) : L) : X) ≠ (((b : A) : L) : X) := by
    intro h
    exact hbane (Subtype.ext (Subtype.ext h))
  have hAp : IsPGroup 2 (A.map L.subtype) := hAel.isPGroup.map L.subtype
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have haS : (((a : A) : L) : X) ∈ (S : Subgroup X) :=
    hAS (Subgroup.mem_map_of_mem L.subtype (a : A).2)
  have hbS : (((b : A) : L) : X) ∈ (S : Subgroup X) :=
    hAS (Subgroup.mem_map_of_mem L.subtype (b : A).2)
  let xS : S := ⟨(((a : A) : L) : X), haS⟩
  let yS : S := ⟨(((b : A) : L) : X), hbS⟩
  have hxord : orderOf xS = 2 := by rw [← Subgroup.orderOf_coe xS]; exact haordX
  have hyord : orderOf yS = 2 := by rw [← Subgroup.orderOf_coe yS]; exact hbordX
  have hxyne : xS ≠ yS := by
    intro h
    exact hAabne (congrArg (fun z : S => (z : X)) h)
  exact false_of_sylow_cyclic_or_quaternion (hS S) hxord hyord hxyne

private def twoElements {X : Type*} [Group X] (L : Subgroup X) : Subgroup L :=
  Subgroup.closure {x : L | ∃ k : ℕ, x ^ (2 ^ k) = 1}

omit [Finite X] in
private theorem twoElements_normal (L : Subgroup X) : (twoElements L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ twoElements L) ?_ ?_ ?_ ?_ hn
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    rw [← MulAut.conj_apply g x, ← map_pow, hk, map_one]
  · simp
  · intro x y hx hy ihx ihy
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact (twoElements L).mul_mem ihx ihy
  · intro x hx ih
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact (twoElements L).inv_mem ih

private theorem twoElements_not_le_center {L : Subgroup X} [L.Normal]
    (_hL : CFSG.IsQuasisimple L) (hLeven : Even (Nat.card L))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥)
    (hle : twoElements L ≤ Subgroup.center L) : False := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨tX, htXL, htXord⟩ := exists_involution_of_even_card hLeven
  let t : ↥L := ⟨tX, htXL⟩
  have htord : orderOf t = 2 := by
    change orderOf (⟨tX, htXL⟩ : ↥L) = 2
    rw [← Subgroup.orderOf_coe]
    exact htXord
  have htE : t ∈ twoElements L := Subgroup.subset_closure
    ⟨1, by rw [pow_one, ← htord]; exact pow_orderOf_eq_one t⟩
  have htcenter : t ∈ Subgroup.center L := hle htE
  have hzpNormal : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htcenter)
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord]; norm_num)
  have htpcore : t ∈ CFSG.pCore 2 L :=
    Subgroup.mem_sSup_of_mem (S := CFSG.normalPSubgroups 2 L)
      (s := Subgroup.zpowers t) ⟨hzpNormal, hzp2⟩ (Subgroup.mem_zpowers t)
  have hmapnormal : ((CFSG.pCore 2 L).map L.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := L) (K := CFSG.pCore 2 L)
  have hmapbot : (CFSG.pCore 2 L).map L.subtype = ⊥ :=
    hO _ hmapnormal (CFSG.pCore_isPGroup.map L.subtype)
  have htm : (t : X) ∈ (CFSG.pCore 2 L).map L.subtype := ⟨t, htpcore, rfl⟩
  rw [hmapbot] at htm
  have htne : (t : X) ≠ 1 := by
    intro h
    have ht1 : t = 1 := Subtype.ext h
    rw [ht1, orderOf_one] at htord
    omega
  exact htne (Subgroup.mem_bot.mp htm)

private theorem twoElements_eq_top_of_isQuasisimple {L : Subgroup X} [L.Normal]
    (hL : CFSG.IsQuasisimple L) (hLeven : Even (Nat.card L))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥) : twoElements L = ⊤ := by
  have hLopen : CFSG.Open.IsQuasisimple L :=
    ⟨@Group.IsPerfect.commutator_eq_top L _ hL.1, hL.2.1⟩
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab.normal_eq_top_or_le_center
    hLopen (twoElements_normal L) with htop | hle
  · exact htop
  · exact False.elim (twoElements_not_le_center hL hLeven hO hle)

private theorem le_of_odd_index_of_isPGroup_two {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    [K.Normal] (hH : IsPGroup 2 H) (hK : Odd K.index) : H ≤ K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (H.map (QuotientGroup.mk' K)) := hH.map (QuotientGroup.mk' K)
  have hodd : Odd (Nat.card (H.map (QuotientGroup.mk' K))) := by
    refine hK.of_dvd_nat ?_
    rw [Subgroup.index_eq_card K]
    exact Subgroup.card_subgroup_dvd_card (H.map (QuotientGroup.mk' K))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hbot : H.map (QuotientGroup.mk' K) = ⊥ := by
    refine Subgroup.card_eq_one.mp ?_
    rw [hk, hk0, pow_zero]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

private theorem le_of_twoElements_eq_top {L N : Subgroup X} [N.Normal]
    (hgen : twoElements L = ⊤) (hN : Odd N.index) : L ≤ N := by
  intro x hx
  have hxE : (⟨x, hx⟩ : ↥L) ∈ twoElements L := by rw [hgen]; exact Subgroup.mem_top _
  have hxE' : (⟨x, hx⟩ : ↥L) ∈
      Subgroup.closure {y : ↥L | ∃ k : ℕ, y ^ (2 ^ k) = 1} := hxE
  refine Subgroup.closure_induction (G := ↥L)
    (k := {y : ↥L | ∃ k : ℕ, y ^ (2 ^ k) = 1}) (p := fun y _ => (y : X) ∈ N)
    ?_ ?_ ?_ ?_ hxE'
  · intro y hy
    obtain ⟨k, hk⟩ := hy
    have hdiv : orderOf y ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    have hP2 : IsPGroup 2 (Subgroup.zpowers y) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hP2X : IsPGroup 2 ((Subgroup.zpowers y).map L.subtype) := hP2.map L.subtype
    obtain ⟨P, hyP⟩ := hP2X.exists_le_sylow
    exact (le_of_odd_index_of_isPGroup_two (K := N) P.isPGroup' hN)
      (hyP (Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_zpowers y)))
  · simp
  · intro a b _ _ iha ihb
    simpa using N.mul_mem iha ihb
  · intro a _ iha
    simpa using N.inv_mem iha

private theorem eq_top_of_le_of_isPGroup_quotient {L N : Subgroup X} [L.Normal] [N.Normal]
    (hLN : L ≤ N) (hq : IsPGroup 2 (X ⧸ L)) (hN : Odd N.index) : N = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : X ⧸ L →* X ⧸ N :=
    QuotientGroup.map L N (MonoidHom.id X) (by intro x hx; exact hLN hx)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨QuotientGroup.mk' L x, by
      simpa [φ] using QuotientGroup.map_mk' L N (MonoidHom.id X) _ x⟩
  have h2N : IsPGroup 2 (X ⧸ N) := hq.of_surjective φ hφsurj
  have hoddN : Odd (Nat.card (X ⧸ N)) := by
    simpa [Subgroup.index_eq_card] using hN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2N
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [hk] at hoddN
    exact (Nat.not_even_iff_odd.mpr hoddN) heven
  have hcard1 : Nat.card (X ⧸ N) = 1 := by rw [hk, hk0, pow_zero]
  have hsub : Subsingleton (X ⧸ N) := (Nat.card_eq_one_iff_unique.mp hcard1).1
  exact QuotientGroup.subsingleton_iff.mp hsub

omit [Finite X] in
private theorem fusionIsBenderGroup_quotient_of_top {M N : Subgroup X} [M.Normal] [N.Normal]
    (hMN : M ≤ N) (hNtop : N = ⊤)
    (hB : fusionIsBenderGroup (N ⧸ M.subgroupOf N)) :
    fusionIsBenderGroup (X ⧸ M) := by
  let eN : ↥N ≃* ↥(⊤ : Subgroup X) := MulEquiv.subgroupCongr hNtop
  have hmapN : Subgroup.map eN.toMonoidHom (M.subgroupOf N) =
      M.subgroupOf (⊤ : Subgroup X) := by
    apply Subgroup.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        simpa [eN, MulEquiv.subgroupCongr_apply] using (Subgroup.mem_subgroupOf.mp hx))
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      exact ⟨⟨(y : X), hMN hy⟩, Subgroup.mem_subgroupOf.mpr hy, Subtype.ext rfl⟩
  have hquotN : (↥N ⧸ M.subgroupOf N) ≃*
      (↥(⊤ : Subgroup X) ⧸ M.subgroupOf (⊤ : Subgroup X)) :=
    QuotientGroup.congr (M.subgroupOf N) (M.subgroupOf ⊤) eN hmapN
  have hBtop : fusionIsBenderGroup (↥(⊤ : Subgroup X) ⧸ M.subgroupOf (⊤ : Subgroup X)) :=
    CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv hquotN hB
  have hquotEquiv : (↥(⊤ : Subgroup X) ⧸ M.subgroupOf (⊤ : Subgroup X)) ≃* (X ⧸ M) :=
    QuotientGroup.congr (M.subgroupOf ⊤) M Subgroup.topEquiv (by
      change Subgroup.map (⊤ : Subgroup X).subtype (M.subgroupOf ⊤) = M
      exact Subgroup.map_subgroupOf_eq_of_le (H := M) (K := (⊤ : Subgroup X)) le_top)
  exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv hquotEquiv hBtop

private theorem sup_eq_top_of_fusionIsBenderGroup {L M : Subgroup X} [L.Normal] [M.Normal]
    (hB : fusionIsBenderGroup (X ⧸ M)) (hLnotleM : ¬ L ≤ M) : L ⊔ M = ⊤ := by
  have hsimple : IsSimpleGroup (X ⧸ M) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  let π : X →* X ⧸ M := QuotientGroup.mk' M
  have hnormal : (L.map π).Normal :=
    (inferInstance : L.Normal).map π (QuotientGroup.mk'_surjective M)
  have hne : L.map π ≠ ⊥ := by
    intro hbot
    apply hLnotleM
    intro x hx
    have hx' : π x ∈ L.map π := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hx')
  have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.map π)).resolve_left hne
  have hcomap := Subgroup.comap_map_eq π (L ⊔ M)
  rw [Subgroup.map_sup, htop, QuotientGroup.map_mk'_self, sup_bot_eq,
    Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
  rw [sup_assoc, sup_idem] at hcomap
  exact hcomap.symm

omit [Finite X] in
private theorem center_map_le_centralizer {L : Subgroup X} :
    (Subgroup.center L).map L.subtype ≤ Subgroup.centralizer (L : Set X) := by
  rintro x ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg (fun w : ↥L => (w : X)) ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)

omit [Finite X] in
private theorem inf_le_center_map_of_normal {L M : Subgroup X} [L.Normal] [M.Normal]
    (hLopen : CFSG.Open.IsQuasisimple L) (hLnotleM : ¬ L ≤ M) :
    L ⊓ M ≤ (Subgroup.center L).map L.subtype := by
  have hnormal : (M.subgroupOf L).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : M.Normal) L
  have hcase : M.subgroupOf L = ⊤ ∨ M.subgroupOf L ≤ Subgroup.center L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab.normal_eq_top_or_le_center
      hLopen hnormal
  have hmaple : (M.subgroupOf L).map L.subtype ≤ (Subgroup.center L).map L.subtype := by
    rcases hcase with htop | hle
    · exfalso
      apply hLnotleM
      have hLM : (M.subgroupOf L).map L.subtype = L := by
        rw [htop, Subgroup.map_top, Subgroup.range_subtype]
      intro x hx
      have hx' : x ∈ (M.subgroupOf L).map L.subtype := by rw [hLM]; exact hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      rw [← hyx]
      exact Subgroup.mem_subgroupOf.mp hy
    · exact Subgroup.map_mono hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_comm] at hmaple

omit [Finite X] in
private theorem commutator_eq_bot_of_inf_le_center {L M : Subgroup X} [L.Normal] [M.Normal]
    (hperf : Group.IsPerfect L) (hMcapL : L ⊓ M ≤ (Subgroup.center L).map L.subtype) :
    ⁅L, M⁆ = ⊥ := by
  have hcenterLeC := center_map_le_centralizer (L := L)
  have h1 : ⁅⁅L, M⁆, L⁆ = ⊥ := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_
    exact ((Subgroup.commutator_le_inf L M).trans hMcapL).trans hcenterLeC
  have h2 : ⁅⁅M, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm M L]
    exact h1
  have hperf' : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L,
      @Group.IsPerfect.commutator_eq_top L _ hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := L) (H₂ := L) (H₃ := M) h1 h2
  rwa [hperf'] at hrot

omit [Finite X] in
private theorem le_center_of_le_centralizer_of_eq_top {L M : Subgroup X}
    (hMleC : M ≤ Subgroup.centralizer (L : Set X)) (hMleL : M ≤ L) (hLtop : L = ⊤) :
    M ≤ Subgroup.center X := by
  have hMleZmap : M ≤ (Subgroup.center L).map L.subtype := by
    intro m hm
    have hmC : m ∈ Subgroup.centralizer (L : Set X) := hMleC hm
    have hmL : m ∈ L := hMleL hm
    refine Subgroup.mem_map.mpr ⟨⟨m, hmL⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hmC) (y : X) y.2)
  rw [hLtop] at hMleZmap
  have hmap : (Subgroup.center (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype =
      Subgroup.center X := by
    change Subgroup.map (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom
      (Subgroup.center (⊤ : Subgroup X)) = Subgroup.center X
    exact Subgroup.map_center_eq (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  rwa [hmap] at hMleZmap

private theorem exists_not_commute_of_perfect {G : Type*} [Group G] [Nontrivial G]
    (hperf : Group.IsPerfect G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let : IsMulCommutative G := ⟨⟨fun a b => h a b⟩⟩
  have : Group.IsPerfect G := hperf
  exact (Group.IsPerfect.not_isMulCommutative G) inferInstance

private theorem center_le_of_fusionIsBenderGroup {M : Subgroup X} [M.Normal]
    (hB : fusionIsBenderGroup (X ⧸ M)) (hperf : Group.IsPerfect (X ⧸ M)) :
    Subgroup.center X ≤ M := by
  have hsimple : IsSimpleGroup (X ⧸ M) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hnc : ∃ a b : X ⧸ M, a * b ≠ b * a :=
    exists_not_commute_of_perfect hperf
  have hcenterbot : Subgroup.center (X ⧸ M) = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
  have hmaple : Subgroup.map (QuotientGroup.mk' M) (Subgroup.center X) ≤
      Subgroup.center (X ⧸ M) := by
    rintro y ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M w
    simpa [map_mul] using congrArg (QuotientGroup.mk' M)
      ((Subgroup.mem_center_iff.mp hz) x)
  rw [hcenterbot] at hmaple
  have hmapbot : Subgroup.map (QuotientGroup.mk' M) (Subgroup.center X) = ⊥ :=
    le_bot_iff.mp hmaple
  have h := (Subgroup.map_eq_bot_iff (Subgroup.center X) (f := QuotientGroup.mk' M)).mp hmapbot
  rwa [QuotientGroup.ker_mk'] at h

private theorem even_card_of_isQuasisimple_of_odd_center {L : Subgroup X}
    (hL : CFSG.IsQuasisimple L) (hZ : Odd (Nat.card (Subgroup.center L))) :
    Even (Nat.card L) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hZeven : Even (Nat.card (Subgroup.center L))
  · exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hZeven).trans
      (Subgroup.card_subgroup_dvd_card (Subgroup.center L)))
  · have h2 : 2 ≤ CFSG.pRank 2 L :=
      CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hL hZ
    obtain ⟨A, -, hAcard⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
    exact even_iff_two_dvd.mpr (dvd_trans (by rw [hAcard]; norm_num)
      (Subgroup.card_subgroup_dvd_card A))

private theorem map_eq_bot_of_odd_card {G Y : Type*} [Group G] [Group Y] [Finite Y]
    {H : Subgroup G} (f : G →* Y) (hodd : Odd (Nat.card H)) (hY : IsPGroup 2 Y) :
    H.map f = ⊥ := by
  have htop : IsPGroup 2 (⊤ : Subgroup Y) := IsPGroup.of_equiv hY Subgroup.topEquiv.symm
  have h2 : IsPGroup 2 (H.map f) := htop.to_le le_top
  have hodd' : Odd (Nat.card (H.map f)) := hodd.of_dvd_nat (Subgroup.card_map_dvd H f)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [hk] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') heven
  have hcard : Nat.card (H.map f) = 1 := by rw [hk, hk0, pow_zero]
  exact Subgroup.card_eq_one.mp hcard

private theorem le_of_odd_card_of_isPGroup_quotient {M L : Subgroup X} [L.Normal]
    (hM : Odd (Nat.card M)) (hq : IsPGroup 2 (X ⧸ L)) : M ≤ L := by
  have hbot : M.map (QuotientGroup.mk' L) = ⊥ :=
    map_eq_bot_of_odd_card (QuotientGroup.mk' L) hM hq
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

omit [Finite X] in
private theorem isPerfect_quotient_of_map_eq_top {L M : Subgroup X} [M.Normal]
    (hmap : L.map (QuotientGroup.mk' M) = ⊤) (hperf : Group.IsPerfect L) :
    Group.IsPerfect (X ⧸ M) := by
  have : Group.IsPerfect L := hperf
  refine Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' M).comp L.subtype) ?_
  intro y
  have hy : y ∈ L.map (QuotientGroup.mk' M) := by rw [hmap]; exact Subgroup.mem_top y
  obtain ⟨x, hxL, hx⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hxL⟩, hx⟩

theorem eq_top_of_normal_of_fusionIsBenderGroup {L M N : Subgroup X} [L.Normal] [M.Normal]
    [N.Normal] (hL : CFSG.IsQuasisimple L) (hq : IsPGroup 2 (X ⧸ L))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥) (hMN : M ≤ N)
    (hM : Odd (Nat.card M)) (hN : Odd N.index) (hB : fusionIsBenderGroup (N ⧸ M.subgroupOf N)) :
    L = ⊤ ∧ fusionIsBenderGroup (X ⧸ Subgroup.center X) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLopen : CFSG.Open.IsQuasisimple L :=
    ⟨@Group.IsPerfect.commutator_eq_top L _ hL.1, hL.2.1⟩
  have hLeven : Even (Nat.card L) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center L)) with hZeven | hZodd
    · exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hZeven).trans
        (Subgroup.card_subgroup_dvd_card (Subgroup.center L)))
    · exact even_card_of_isQuasisimple_of_odd_center hL hZodd
  have hgen := twoElements_eq_top_of_isQuasisimple hL hLeven hO
  have hLleN : L ≤ N := le_of_twoElements_eq_top hgen hN
  have hNtop : N = ⊤ := eq_top_of_le_of_isPGroup_quotient hLleN hq hN
  have hBquot : fusionIsBenderGroup (X ⧸ M) :=
    fusionIsBenderGroup_quotient_of_top hMN hNtop hB
  have hLnotleM : ¬ L ≤ M := by
    intro hLM
    have hdvd : 2 ∣ Nat.card M :=
      (even_iff_two_dvd.mp hLeven).trans (Subgroup.card_dvd_of_le hLM)
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr hdvd)
  have hLsupM : L ⊔ M = ⊤ := sup_eq_top_of_fusionIsBenderGroup hBquot hLnotleM
  have hMcapL : L ⊓ M ≤ (Subgroup.center L).map L.subtype :=
    inf_le_center_map_of_normal hLopen hLnotleM
  have hcommLM : ⁅L, M⁆ = ⊥ := commutator_eq_bot_of_inf_le_center hL.1 hMcapL
  have hMleC : M ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLM)
  have hMleL : M ≤ L := le_of_odd_card_of_isPGroup_quotient hM hq
  have hLtop : L = ⊤ := by
    have h := hLsupM
    rwa [sup_eq_left.mpr hMleL] at h
  have hMleZ : M ≤ Subgroup.center X :=
    le_center_of_le_centralizer_of_eq_top hMleC hMleL hLtop
  have hmapLtop : L.map (QuotientGroup.mk' M) = ⊤ := by
    rw [hLtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)
  have hperfX : Group.IsPerfect (X ⧸ M) :=
    isPerfect_quotient_of_map_eq_top hmapLtop hL.1
  have hZleM : Subgroup.center X ≤ M := center_le_of_fusionIsBenderGroup hBquot hperfX
  have hMZ : M = Subgroup.center X := le_antisymm hMleZ hZleM
  exact ⟨hLtop, CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq hMZ) hBquot⟩

private theorem not_isQuasisimple_of_card_eq_six {L : Subgroup X} (h6 : Nat.card L = 6)
    (hnc : ∃ a b : L, a * b ≠ b * a) : ¬ CFSG.IsQuasisimple L := by
  intro hLq
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc
  have : Group.IsPerfect L := hLq.1
  have hperf : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have : Group.IsPerfect (Equiv.Perm (Fin 3)) := hperf
  exact (Group.IsPerfect.not_isSolvable (Equiv.Perm (Fin 3)))
    (Equiv.Perm.isSolvable (α := Fin 3) (by simp))

end General

section Final

variable {X : Type} [Group X] [Finite X]

theorem eq_top_of_isPIsolatedOver (hB : GomiBender) {L : Subgroup X}
    (hX : IsPIsolatedOver 2 (⊤ : Subgroup X) ⊥)
    (hcomm : ∀ g : X, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hq : IsPGroup 2 (X ⧸ Subgroup.normalClosure (L : Set X)))
    (hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥)
    (hL : (Nat.card L = 6 ∧ ∃ a b : L, a * b ≠ b * a) ∨
      (CFSG.IsQuasisimple L ∧ Odd (Nat.card (Subgroup.center L)))) :
    L = ⊤ ∧ (CFSG.IsQuasisimple L → fusionIsBenderGroup (X ⧸ Subgroup.center X)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ := isPIsolatedOver_two_iff_fusionStronglyEmbedded.mp hX
  rcases hL with ⟨h6, hnc⟩ | ⟨hLq, hZ⟩
  · have hLeven : Even (Nat.card L) := by rw [h6]; norm_num
    have hLnormal : L.Normal :=
      normal_of_commute_conj_of_fusionStronglyEmbedded hH hLeven hcomm
    have : L.Normal := hLnormal
    have hq' : IsPGroup 2 (X ⧸ L) :=
      IsPGroup.of_equiv hq
        (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalClosure_eq_self L))
    have hLtop : L = ⊤ := eq_top_of_normal_of_card_eq_six h6 hnc hq' hO
    exact ⟨hLtop, fun hLq => False.elim (not_isQuasisimple_of_card_eq_six h6 hnc hLq)⟩
  · have hLeven : Even (Nat.card L) := even_card_of_isQuasisimple_of_odd_center hLq hZ
    have hLnormal : L.Normal :=
      normal_of_commute_conj_of_fusionStronglyEmbedded hH hLeven hcomm
    have : L.Normal := hLnormal
    have hq' : IsPGroup 2 (X ⧸ L) :=
      IsPGroup.of_equiv hq
        (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalClosure_eq_self L))
    rcases hB X H hH with hlow | hMB
    · exact False.elim (false_of_isQuasisimple_of_sylow_cyclic_or_quaternion hLq hZ hlow)
    · obtain ⟨M, N, hMnormal, hNnormal, _, hMN, hMcard, hNindex, hB'⟩ := hMB
      have : M.Normal := hMnormal
      have : N.Normal := hNnormal
      obtain ⟨hLtop, hBZ⟩ :=
        eq_top_of_normal_of_fusionIsBenderGroup hLq hq' hO hMN hMcard hNindex hB'
      exact ⟨hLtop, fun _ => hBZ⟩

end Final

end CFSG.GroupTheory

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Core
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
open scoped commutatorElement

section Row

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_sup {p : ℕ} {P Q : Subgroup G} (hP : IsElemAbelian p P)
    (hQ : IsElemAbelian p Q) (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    IsElemAbelian p (P ⊔ Q) := by
  set S : Set G := (P : Set G) ∪ (Q : Set G) with hSdef
  have hSS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact isElemAbelian_commute hP hs ht
    · exact hPQ s hs t ht
    · exact (hPQ t ht s hs).symm
    · exact isElemAbelian_commute hQ hs ht
  have hcentS : ∀ s ∈ S, s ∈ Subgroup.centralizer S := fun s hs =>
    Subgroup.mem_centralizer_iff.2 (fun t ht => hSS t ht s hs)
  have hclC : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 hcentS
  have hcommC : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.closure_le_centralizer_centralizer S ha) b
      (hclC hb)).symm
  rw [Subgroup.sup_eq_closure]
  refine ⟨⟨⟨fun a b => Subtype.ext (hcommC a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | hs
    · exact hP.2 s hs
    · exact hQ.2 s hs
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (hcommC a ha b hb)), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hk, ← hl]
    exact (Commute.zpow_zpow_self x k l)
  · intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem mem_of_center_card_three {p : ℕ} (hp : p.Prime) {x : G} {L : Subgroup G}
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hp3 : p = 3)
    (hZ : Nat.card (Subgroup.center (PQuot p L)) = 3)
    (hr1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p) : x ∈ L := by
  by_contra hxL
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hLC : L ≤ cx x := hL.1
  have hxLc : ∀ l ∈ L, x * l = l * x := fun l hl => ((Subgroup.mem_centralizer_singleton_iff).1 (hLC hl)).symm
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => (hxLc h hh).symm)
  have hEb : IsElemAbelian 3 (Subgroup.center (PQuot 3 L)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a.1)⟩⟩, fun z hz => ?_⟩
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center (PQuot 3 L))) (x := ⟨z, hz⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hNcop : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    have h1 : Nat.card ((GLAPPrimeCore 3 ↥L).map L.subtype) = Nat.card (GLAPPrimeCore 3 ↥L) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have h2 : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := by
      rw [← h1]
      exact CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp L
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h2
  obtain ⟨S, hS, hSmap, hSc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift
    (GLAPPrimeCore 3 ↥L) hNcop hEb
  have hSc3 : Nat.card S = 3 := hSc.trans hZ
  have hSne : S ≠ ⊥ := fun h => by
    have h1 : Nat.card S = 1 := (Subgroup.card_eq_one).2 h
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
  set z : ↥L := a.1 with hzdef
  have hz3 : z ^ 3 = 1 := hS.2 z a.2
  have hzne : z ≠ 1 := fun h => ha (Subtype.ext h)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hzne
  have hcentz : (QuotientGroup.mk z : PQuot 3 L) ∈ Subgroup.center (PQuot 3 L) := by
    have : (QuotientGroup.mk z : PQuot 3 L) ∈ S.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) :=
      Subgroup.mem_map_of_mem _ a.2
    rw [hSmap] at this
    exact this
  set zG : G := (z : G) with hzGdef
  have hzL : zG ∈ L := z.2
  have hzG3 : orderOf zG = 3 := by
    rw [hzGdef, Subgroup.orderOf_coe]
    exact hord
  have hxz : x * zG = zG * x := ((Subgroup.mem_centralizer_singleton_iff).1 (hLC hzL)).symm
  have hzC : zG ∈ centModSubgroup 3 L := by
    rw [mem_centModSubgroup]
    refine ⟨Subgroup.le_normalizer hzL, fun l hl => ?_⟩
    have hcomm := Subgroup.mem_center_iff.1 hcentz (QuotientGroup.mk (⟨l, hl⟩ : ↥L))
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) ⁅(⟨l, hl⟩ : ↥L), z⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    have hN : ⁅(⟨l, hl⟩ : ↥L), z⁆ ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have hval : (⁅(⟨l, hl⟩ : ↥L), z⁆ : ↥L).1 = ⁅l, zG⁆ := by
      simp [commutatorElement_def, hzGdef]
    rw [← hval]
    exact Subgroup.mem_map.2 ⟨_, hN, rfl⟩
  set A : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers zG with hAdef
  have hxE : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hAab : IsElemAbelian 3 A :=
    isElemAbelian_sup (isElemAbelian_zpowers hxE)
      (isElemAbelian_zpowers (by rw [← hzG3]; exact pow_orderOf_eq_one zG))
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact Commute.zpow_zpow (show Commute x zG from hxz) k l)
  have hAle : A ≤ cx x :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
      (Subgroup.zpowers_le.2 (hLC hzL))
  have hAcM : ∀ a ∈ A, CentMod 3 L a := by
    intro a ha
    have hx' : Subgroup.zpowers x ≤ centModSubgroup 3 L :=
      Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer hxC))
    have hz' : Subgroup.zpowers zG ≤ centModSubgroup 3 L := Subgroup.zpowers_le.2 hzC
    exact centMod_iff.2 ((sup_le hx' hz') ha)
  have hcardA : Nat.card A = 9 := by
    have hzN : Subgroup.zpowers zG ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      apply Subgroup.zpowers_le.2
      apply Subgroup.centralizer_le_normalizer
      apply Subgroup.mem_centralizer_iff.2
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute x zG from hxz) k).eq
    have h1 := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [Nat.card_zpowers, Nat.card_zpowers, hx, hzG3, ← hAdef] at h1
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers zG : Subgroup G) ∣
        Nat.card (Subgroup.zpowers x) := Subgroup.card_dvd_of_le inf_le_left
    rw [Nat.card_zpowers, hx] at hdvd
    have hinf : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers zG : Subgroup G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3'
      · exact h1'
      · exfalso
        have hEq : Subgroup.zpowers x ⊓ Subgroup.zpowers zG = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hx, h3'])
        have hxmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers zG := by
          rw [hEq]
          exact Subgroup.mem_zpowers x
        exact hxL ((Subgroup.zpowers_le.2 hzL) hxmem.2)
    rw [hinf, mul_one] at h1
    omega
  have hbound := hr1 A hAab hAle hAcM
  omega

theorem isPGroup_subgroupOf_of {p : ℕ} {L V : Subgroup G} (hV : IsPGroup p V) :
    IsPGroup p (V.subgroupOf L) := by
  intro g
  obtain ⟨k, hk⟩ := hV ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem i1016Row_of_facts {p : ℕ} (hF : I1016RowFacts) : I1016RowAt G p := by
  intro x L row hx hxp hL hK hrow hr1 E V hE hEab hVL hV2 hVN hEN
  obtain ⟨hpr, hK', hZ⟩ := hrow
  subst hpr
  have hpp : (Row.prime row).Prime := by cases row <;> norm_num [S8.Row.prime]
  have hp2 : Row.prime row ≠ 2 := by cases row <;> simp [S8.Row.prime]
  have hTLR : GLATwoLocalRank (Row.prime row) (PSimple (Row.prime row) L) ≤ row.rank - 1 :=
    hF row (PSimple (Row.prime row) L) hK'
  have hrank : 1 ≤ row.rank := by cases row <;> simp [S8.Row.rank]
  have hcen : Nat.card (Subgroup.center (PQuot (Row.prime row) L)) = 1 ∨
      (Nat.card (Subgroup.center (PQuot (Row.prime row) L)) = 3 ∧ Row.prime row = 3) := by
    rw [hZ]
    cases row <;> simp [S8.Row.center, S8.Row.prime]
  have hxLc : ∀ l ∈ L, x * l = l * x := fun l hl =>
    ((Subgroup.mem_centralizer_singleton_iff).1 (hL.1 hl)).symm
  have hidx : Nat.card E ≤ Row.prime row * Nat.card (L ⊓ E : Subgroup G) :=
    card_le_mul_card_inf hxp hxLc hE
  have hcore : Nat.card (L ⊓ E : Subgroup G) ≤
      Nat.card (Subgroup.center (PQuot (Row.prime row) L)) *
        Row.prime row ^ GLATwoLocalRank (Row.prime row) (PSimple (Row.prime row) L) := by
    have hA : IsElemAbelian (Row.prime row) ((L ⊓ E).subgroupOf L) :=
      isElemAbelian_subgroupOf' (isElemAbelian_mono hEab inf_le_right)
    have hW : IsPGroup 2 (V.subgroupOf L) := isPGroup_subgroupOf_of hV2
    have hW1 : V.subgroupOf L ≠ ⊥ := by
      intro h
      apply hVN
      intro v hv
      have hvL : (⟨v, hVL hv⟩ : ↥L) ∈ V.subgroupOf L := Subgroup.mem_subgroupOf.2 hv
      rw [h, Subgroup.mem_bot] at hvL
      have hv1 : v = 1 := congrArg Subtype.val hvL
      rw [hv1]
      exact Subgroup.one_mem _
    have hWN : ¬ (V.subgroupOf L) ≤ GLAPPrimeCore (Row.prime row) ↥L := by
      intro hle
      apply hVN
      intro v hv
      have hvL : (⟨v, hVL hv⟩ : ↥L) ∈ V.subgroupOf L := Subgroup.mem_subgroupOf.2 hv
      exact Subgroup.mem_map.2 ⟨_, hle hvL, rfl⟩
    have hAW : (L ⊓ E).subgroupOf L ≤
        Subgroup.normalizer ((V.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      intro a ha
      have haE : ((a : ↥L) : G) ∈ E := (inf_le_right : L ⊓ E ≤ E) (Subgroup.mem_subgroupOf.1 ha)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hn := Subgroup.mem_normalizer_iff.1 (hEN haE) (h : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hn
    have hc := card_le_center_mul_pow hpp hp2 hA hW hW1 hWN hAW
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ E ≤ L)).toEquiv] at hc
  rcases hcen with h1 | ⟨h3, hp3⟩
  ·
    calc Nat.card E ≤ Row.prime row * Nat.card (L ⊓ E : Subgroup G) := hidx
      _ ≤ Row.prime row * (Nat.card (Subgroup.center (PQuot (Row.prime row) L)) *
            Row.prime row ^ GLATwoLocalRank (Row.prime row) (PSimple (Row.prime row) L)) :=
          Nat.mul_le_mul_left _ hcore
      _ = Row.prime row ^ (GLATwoLocalRank (Row.prime row) (PSimple (Row.prime row) L) + 1) := by
          rw [h1, one_mul, pow_succ, mul_comm]
      _ ≤ Row.prime row ^ row.rank :=
          Nat.pow_le_pow_right hpp.pos (by omega)
  ·
    have hxL : x ∈ L := mem_of_center_card_three hpp hxp hL hp3 h3 hr1
    have hEq : L ⊓ E = E :=
      inf_eq_right.2 (hE.trans (sup_eq_left.2 (Subgroup.zpowers_le.2 hxL)).le)
    rw [hEq, h3, hp3] at hcore
    rw [hp3] at hTLR
    rw [hp3]
    calc Nat.card E ≤ 3 * 3 ^ GLATwoLocalRank 3 (PSimple 3 L) := hcore
      _ = 3 ^ (GLATwoLocalRank 3 (PSimple 3 L) + 1) := by rw [pow_succ, mul_comm]
      _ ≤ 3 ^ row.rank := Nat.pow_le_pow_right (by norm_num) (by omega)

end Row

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

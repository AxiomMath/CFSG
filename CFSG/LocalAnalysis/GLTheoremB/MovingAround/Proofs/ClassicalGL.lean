module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1211b
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalGL

open scoped commutatorElement

section RankGL4Part

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

section Orbit

variable {G : Type} [Group G]

theorem relIndex_centralizer_le [Finite G] {X N : Subgroup G} {v : G}
    (hv : ∀ x ∈ X, ⁅x, v⁆ ∈ N) :
    (Subgroup.centralizer ({v} : Set G)).relIndex X ≤ Nat.card N := by
  set C := Subgroup.centralizer ({v} : Set G) with hC
  have key : ∀ a b : ↥X, (⁅(a : G), v⁆ = ⁅(b : G), v⁆ ↔ a⁻¹ * b ∈ C.subgroupOf X) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_singleton_iff]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      have h1 : (a : G) * v * (a : G)⁻¹ = (b : G) * v * (b : G)⁻¹ := mul_right_cancel h
      calc (a : G)⁻¹ * b * v = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * b := by rw [h1]
        _ = v * ((a : G)⁻¹ * b) := by group
    · intro h
      calc (a : G) * v * (a : G)⁻¹ * v⁻¹ = (a : G) * (v * ((a : G)⁻¹ * b)) * (b : G)⁻¹ * v⁻¹ := by
            group
        _ = (a : G) * ((a : G)⁻¹ * b * v) * (b : G)⁻¹ * v⁻¹ := by rw [h]
        _ = (b : G) * v * (b : G)⁻¹ * v⁻¹ := by group
  let f : ↥X ⧸ C.subgroupOf X → ↥N :=
    Quotient.lift (fun x : ↥X => (⟨⁅(x : G), v⁆, hv x x.2⟩ : ↥N)) (fun a b hab =>
      Subtype.ext ((key a b).2 (QuotientGroup.leftRel_apply.1 hab)))
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 ((key a b).1 (congrArg Subtype.val h))
  exact Nat.card_le_card_of_injective f hf

theorem centralizer_sup (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (fun a ha => Subgroup.mem_sup_left ha))
      (Subgroup.centralizer_le (fun b hb => Subgroup.mem_sup_right hb))
  · intro x hx
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1 a ha
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem sup_le_centralizer_sup {A B : Subgroup G} (hA : A ≤ Subgroup.centralizer (A : Set G))
    (hB : B ≤ Subgroup.centralizer (B : Set G)) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [centralizer_sup]
  exact le_inf (sup_le hA (Subgroup.le_centralizer_iff.1 hAB)) (sup_le hAB hB)

theorem mem_centralizer_sup_zpowers {U : Subgroup G} {v x : G}
    (hU : x ∈ Subgroup.centralizer (U : Set G)) (hv : x ∈ Subgroup.centralizer ({v} : Set G)) :
    x ∈ Subgroup.centralizer ((U ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hle : U ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hU u hu
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hv).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem centralizer_sup_zpowers (U : Subgroup G) (v : G) :
    Subgroup.centralizer ((U ⊔ Subgroup.zpowers v : Subgroup G) : Set G) =
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({v} : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (fun u hu => Subgroup.mem_sup_left hu))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))))
  · exact fun x hx => mem_centralizer_sup_zpowers hx.1 hx.2

theorem exists_gen_bound [Finite G] {p : ℕ} [Fact p.Prime] {X A N : Subgroup G}
    (hA : IsPGroup p A) (hXA : ∀ x ∈ X, ∀ a ∈ A, ⁅x, a⁆ ∈ N) :
    ∀ H : Subgroup G, H ≤ A → ∃ (U : Subgroup G) (t : ℕ), U ≤ A ∧ A ≤ U ⊔ H ∧
      p ^ t * Nat.card H ≤ Nat.card A ∧
      (Subgroup.centralizer (U : Set G)).relIndex X ≤ Nat.card N ^ t := by
  intro H
  induction hn : Nat.card A - Nat.card H using Nat.strong_induction_on generalizing H with
  | _ n ih =>
  intro hHA
  by_cases hAH : A ≤ H
  · refine ⟨⊥, 0, bot_le, le_sup_of_le_right hAH, ?_, ?_⟩
    · rw [pow_zero, one_mul]
      exact Subgroup.card_le_of_le hHA
    · rw [pow_zero, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2
        (by simp [Subgroup.one_mem]), Subgroup.relIndex_top_left]
  · obtain ⟨v, hvA, hvH⟩ := Set.not_subset.1 hAH
    set H' := H ⊔ Subgroup.zpowers v with hH'
    have hH'A : H' ≤ A := sup_le hHA (Subgroup.zpowers_le.2 hvA)
    have hlt : H < H' := lt_of_le_of_ne le_sup_left (fun h => hvH (by
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
    have hcardlt : Nat.card H < Nat.card H' := Subgroup.card_lt_of_lt hlt
    have hpH : p * Nat.card H ≤ Nat.card H' := by
      obtain ⟨i, hi⟩ := (hA.to_le hHA).exists_card_eq
      obtain ⟨j, hj⟩ := (hA.to_le hH'A).exists_card_eq
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      rw [hi, hj] at hcardlt ⊢
      have hij : i < j := (Nat.pow_lt_pow_iff_right (by omega)).1 hcardlt
      calc p * p ^ i = p ^ (i + 1) := by ring
        _ ≤ p ^ j := Nat.pow_le_pow_right (by omega) hij
    have hH'le : Nat.card H' ≤ Nat.card A := Subgroup.card_le_of_le hH'A
    obtain ⟨U, t, hUA, hAU, hcard, hidx⟩ := ih (Nat.card A - Nat.card H') (by omega) H' rfl hH'A
    refine ⟨U ⊔ Subgroup.zpowers v, t + 1, sup_le hUA (Subgroup.zpowers_le.2 hvA), ?_, ?_, ?_⟩
    · calc A ≤ U ⊔ H' := hAU
        _ = U ⊔ Subgroup.zpowers v ⊔ H := by
          rw [hH', sup_comm H, ← sup_assoc]
    · calc p ^ (t + 1) * Nat.card H = p ^ t * (p * Nat.card H) := by ring
        _ ≤ p ^ t * Nat.card H' := Nat.mul_le_mul_left _ hpH
        _ ≤ Nat.card A := hcard
    · rw [centralizer_sup_zpowers]
      calc (Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({v} : Set G)).relIndex X
          ≤ (Subgroup.centralizer (U : Set G)).relIndex X *
            (Subgroup.centralizer ({v} : Set G)).relIndex X := Subgroup.relIndex_inf_le
        _ ≤ Nat.card N ^ t * Nat.card N :=
          Nat.mul_le_mul hidx (relIndex_centralizer_le (fun x hx => hXA x hx v hvA))
        _ = Nat.card N ^ (t + 1) := by ring

end Orbit

section Nakayama

variable {G : Type} [Group G]

theorem commutatorElement_mul_of_abelian {V : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {e a b : G} (he : ∀ v ∈ V, e * v * e⁻¹ ∈ V)
    (ha : a ∈ V) (hb : b ∈ V) : ⁅e, a * b⁆ = ⁅e, a⁆ * ⁅e, b⁆ := by
  have h1 := hVc _ (V.inv_mem ha) _ (he b hb)
  have h2 := hVc _ (V.inv_mem ha) _ (V.inv_mem hb)
  simp only [commutatorElement_def]
  calc e * (a * b) * e⁻¹ * (a * b)⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) * (b⁻¹ * a⁻¹) := by group
    _ = (e * a * e⁻¹) * (e * b * e⁻¹) * (a⁻¹ * b⁻¹) := by rw [h2]
    _ = (e * a * e⁻¹) * ((e * b * e⁻¹) * a⁻¹) * b⁻¹ := by group
    _ = (e * a * e⁻¹) * (a⁻¹ * (e * b * e⁻¹)) * b⁻¹ := by rw [h1]
    _ = e * a * e⁻¹ * a⁻¹ * (e * b * e⁻¹ * b⁻¹) := by group

theorem commutatorElement_inv_of_abelian {V : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {e a : G} (he : ∀ v ∈ V, e * v * e⁻¹ ∈ V)
    (ha : a ∈ V) : ⁅e, a⁻¹⁆ = ⁅e, a⁆⁻¹ := by
  have h1 := hVc _ ha _ (V.inv_mem (he a ha))
  simp only [commutatorElement_def]
  calc e * a⁻¹ * e⁻¹ * a⁻¹⁻¹ = (e * a * e⁻¹)⁻¹ * a := by group
    _ = a * (e * a * e⁻¹)⁻¹ := h1.symm
    _ = (e * a * e⁻¹ * a⁻¹)⁻¹ := by group

@[expose] def commPre (V T : Subgroup G) (e : G) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (he : ∀ v ∈ V, e * v * e⁻¹ ∈ V) : Subgroup G where
  carrier := {v | v ∈ V ∧ ⁅e, v⁆ ∈ T}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    rw [commutatorElement_mul_of_abelian hVc he ha hb]
    exact T.mul_mem ha' hb'
  one_mem' := ⟨V.one_mem, by rw [commutatorElement_one_right]; exact T.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨V.inv_mem ha, ?_⟩
    rw [commutatorElement_inv_of_abelian hVc he ha]
    exact T.inv_mem ha'

theorem le_of_le_sup_commutator [Finite G] {p : ℕ} [Fact p.Prime] {P V M : Subgroup G}
    (hP : IsPGroup p P) (hV : IsPGroup p V) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hMV : M ≤ V)
    (hPM : ∀ e ∈ P, ∀ m ∈ M, e * m * e⁻¹ ∈ M) (hle : V ≤ M ⊔ ⁅P, V⁆) : V ≤ M := by
  set Q := P ⊔ V with hQ
  have hQp : IsPGroup p Q := hP.to_sup_of_normal_right' hV hPV
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Q).1 hQp.isNilpotent
  have hconj : ∀ e ∈ P, ∀ v ∈ V, e * v * e⁻¹ ∈ V := fun e he v hv =>
    (Subgroup.mem_normalizer_iff.1 (hPV he) v).1 hv
  have key : ∀ k, V ≤ M ⊔ (V ⊓ Q.lowerCentralSeries k) := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (le_inf le_rfl le_sup_right)
    | succ k ih =>
      refine hle.trans (sup_le le_sup_left ?_)
      rw [Subgroup.commutator_le]
      intro e he v hv
      set T := M ⊔ (V ⊓ Q.lowerCentralSeries (k + 1)) with hT
      have hS : M ⊔ (V ⊓ Q.lowerCentralSeries k) ≤ commPre V T e hVc (hconj e he) := by
        refine sup_le (fun m hm => ?_) (fun l hl => ?_)
        · refine ⟨hMV hm, ?_⟩
          · refine Subgroup.mem_sup_left ?_
            rw [commutatorElement_def]
            exact M.mul_mem (hPM e he m hm) (M.inv_mem hm)
        · refine ⟨hl.1, Subgroup.mem_sup_right ⟨?_, ?_⟩⟩
          · rw [commutatorElement_def]
            exact V.mul_mem (hconj e he l hl.1) (V.inv_mem hl.1)
          · rw [Subgroup.lowerCentralSeries_succ, ← commutatorElement_inv]
            exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hl.2
              (Subgroup.mem_sup_left he))
      exact (hS (ih hv)).2
  have h := key n
  rw [hn, inf_bot_eq, sup_bot_eq] at h
  exact h

end Nakayama

section RankGL4

variable {G : Type} [Group G]

theorem mul_le_four_of_add_le {a t : ℕ} (h : a + t ≤ 4) : a * t ≤ 4 := by
  have ha : a ≤ 4 := by omega
  interval_cases a <;> omega

theorem relIndex_centralizer_le_pow_four [Finite G] {p : ℕ} [Fact p.Prime] {P V : Subgroup G}
    (hP : IsPGroup p P) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hV : IsPGroup p V) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hV4 : Nat.card V ≤ p ^ 4) :
    (Subgroup.centralizer (V : Set G)).relIndex P ≤ p ^ 4 := by
  have hconj : ∀ e ∈ P, ∀ v ∈ V, e * v * e⁻¹ ∈ V := fun e he v hv =>
    (Subgroup.mem_normalizer_iff.1 (hPV he) v).1 hv
  set N := ⁅P, V⁆ with hN
  have hNV : N ≤ V := by
    rw [hN, Subgroup.commutator_le]
    intro e he v hv
    rw [commutatorElement_def]
    exact V.mul_mem (hconj e he v hv) (V.inv_mem hv)
  have hXA : ∀ x ∈ P, ∀ a ∈ V, ⁅x, a⁆ ∈ N := fun x hx a ha =>
    Subgroup.commutator_mem_commutator hx ha
  obtain ⟨U, t, hUV, hVU, hcard, hidx⟩ := exists_gen_bound hV hXA N hNV
  set F := P ⊓ Subgroup.centralizer (U : Set G) with hF
  set M := V ⊓ Subgroup.centralizer (F : Set G) with hM
  have hUM : U ≤ M := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hUV hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_centralizer_iff.1 hf.2 u hu).symm
  have hPM : ∀ e ∈ P, ∀ m ∈ M, e * m * e⁻¹ ∈ M := by
    intro e he m hm
    refine Subgroup.mem_inf.2 ⟨hconj e he m hm.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 : f * m = m * f := Subgroup.mem_centralizer_iff.1 hm.2 f hf
    have h2 : f * e = e * f := hPc f hf.1 e he
    calc f * (e * m * e⁻¹) = (f * e) * m * e⁻¹ := by group
      _ = e * (f * m) * e⁻¹ := by rw [h2]; group
      _ = e * (m * f) * e⁻¹ := by rw [h1]
      _ = e * m * (f * e⁻¹) := by group
      _ = e * m * e⁻¹ * f := by
        have h3 : f * e⁻¹ = e⁻¹ * f := hPc f hf.1 e⁻¹ (P.inv_mem he)
        rw [h3]; group
  have hVM : V ≤ M :=
    le_of_le_sup_commutator hP hV hVc hPV inf_le_left hPM (hVU.trans (sup_le_sup_right hUM N))
  have hFV : F ≤ P ⊓ Subgroup.centralizer (V : Set G) := by
    intro f hf
    refine Subgroup.mem_inf.2 ⟨hf.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hVM hv).2 f hf).symm
  have hne : F.relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (Subgroup.centralizer (V : Set G)).relIndex P ≤
      (Subgroup.centralizer (U : Set G)).relIndex P := by
    rw [← Subgroup.inf_relIndex_left P (Subgroup.centralizer (V : Set G)),
      ← Subgroup.inf_relIndex_left P (Subgroup.centralizer (U : Set G))]
    exact Subgroup.relIndex_le_of_le_left hFV hne
  obtain ⟨a, ha⟩ := (hV.to_le hNV).exists_card_eq
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hat : a + t ≤ 4 := by
    have h2 : p ^ (t + a) ≤ p ^ 4 := by
      rw [pow_add, ← ha]
      exact hcard.trans hV4
    exact (by have := (Nat.pow_le_pow_iff_right (by omega : 1 < p)).1 h2; omega)
  calc (Subgroup.centralizer (V : Set G)).relIndex P
      ≤ Nat.card N ^ t := h1.trans hidx
    _ = p ^ (a * t) := by rw [ha, ← pow_mul]
    _ ≤ p ^ 4 := Nat.pow_le_pow_right (by omega) (mul_le_four_of_add_le hat)

end RankGL4

section ClassTwo

variable {G : Type} [Group G]

theorem card_le_pow_four_mul_card_commutator [Finite G] {p : ℕ} [Fact p.Prime] {W : Subgroup G}
    (hexp : ∀ w ∈ W, w ^ p = 1) (hcl : ⁅W, W⁆ ≤ centerOf W)
    (hab : ∀ U : Subgroup G, U ≤ W → IsElemAbelian p U → Nat.card ↥U ≤ p ^ 3) :
    Nat.card W ≤ p ^ 4 * Nat.card ↥⁅W, W⁆ := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hWp : IsPGroup p W := fun w => ⟨1, Subtype.ext (by simpa using hexp w w.2)⟩
  set Z := centerOf W with hZdef
  have hZW : Z ≤ W := Subgroup.map_subtype_le _
  have hZc : ∀ z ∈ Z, ∀ w ∈ W, w * z = z * w := fun z hz =>
    ((Lemma1211.mem_centerOf_iff' W z).1 hz).2
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hZPr : Z ≤ W ∧ Z ≤ Subgroup.centralizer (Z : Set G) := by
    refine ⟨hZW, fun z hz => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hZc z hz y (hZW hy))
  obtain ⟨A, hZA, ⟨hAW, hAc⟩, hAmax⟩ := Finite.exists_le_maximal
    (p := fun A : Subgroup G => A ≤ W ∧ A ≤ Subgroup.centralizer (A : Set G)) hZPr
  have hself : W ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
    intro x hx
    have hxW := (Subgroup.mem_inf.1 hx).1
    have hxA := (Subgroup.mem_inf.1 hx).2
    have hzc : Subgroup.zpowers x ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    have hAx : A ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.2 hxA
    have hPr : A ⊔ Subgroup.zpowers x ≤ W ∧ A ⊔ Subgroup.zpowers x ≤
        Subgroup.centralizer ((A ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
      ⟨sup_le hAW (Subgroup.zpowers_le.2 hxW), sup_le_centralizer_sup hAc hzc hAx⟩
    exact hAmax hPr le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hXA : ∀ x ∈ W, ∀ a ∈ A, ⁅x, a⁆ ∈ ⁅W, W⁆ := fun x hx a ha =>
    Subgroup.commutator_mem_commutator hx (hAW ha)
  obtain ⟨U, t, hUA, hAU, hcard, hidx⟩ := exists_gen_bound (hWp.to_le hAW) hXA Z hZA
  have hCU : W ⊓ Subgroup.centralizer (U : Set G) ≤ A := by
    intro x hx
    apply hself
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, ?_⟩
    have hxZ : x ∈ Subgroup.centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hZc z hz x (Subgroup.mem_inf.1 hx).1).symm
    have hxUZ : x ∈ Subgroup.centralizer ((U ⊔ Z : Subgroup G) : Set G) := by
      rw [centralizer_sup]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, hxZ⟩
    exact Subgroup.centralizer_le hAU hxUZ
  have hidxA : A.relIndex W ≤ Nat.card ↥⁅W, W⁆ ^ t := by
    calc A.relIndex W ≤ (W ⊓ Subgroup.centralizer (U : Set G)).relIndex W :=
          Subgroup.relIndex_le_of_le_left hCU Subgroup.index_ne_zero_of_finite
      _ = (Subgroup.centralizer (U : Set G)).relIndex W := Subgroup.inf_relIndex_left _ _
      _ ≤ _ := hidx
  have hWA : A.relIndex W * Nat.card A = Nat.card W := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := W)
    rwa [inf_of_le_left hAW] at h
  obtain ⟨a, ha⟩ := (hWp.to_le hAW).exists_card_eq
  obtain ⟨z, hz⟩ := (hWp.to_le hZW).exists_card_eq
  obtain ⟨d, hd⟩ := (hWp.to_le (Subgroup.commutator_le_self W)).exists_card_eq
  have ha3 : a ≤ 3 := by
    have h := hab A hAW ⟨Subgroup.le_centralizer_iff_isMulCommutative.1 hAc,
      fun x hx => hexp x (hAW hx)⟩
    rw [ha] at h
    exact (Nat.pow_le_pow_iff_right hp1).1 h
  have hdz : d ≤ z := by
    have h := Subgroup.card_le_of_le hcl
    rw [hd, hz] at h
    exact (Nat.pow_le_pow_iff_right hp1).1 h
  have htz : t + z ≤ a := by
    rw [hz, ha, ← pow_add] at hcard
    exact (Nat.pow_le_pow_iff_right hp1).1 hcard
  have hexpo : d * t + a ≤ 4 + d := by
    have ht3 : t ≤ 3 := by omega
    interval_cases t <;> omega
  calc Nat.card W = A.relIndex W * Nat.card A := hWA.symm
    _ ≤ Nat.card ↥⁅W, W⁆ ^ t * Nat.card A := Nat.mul_le_mul_right _ hidxA
    _ = p ^ (d * t + a) := by rw [hd, ha, ← pow_mul, ← pow_add]
    _ ≤ p ^ (4 + d) := Nat.pow_le_pow_right (by omega) hexpo
    _ = p ^ 4 * Nat.card ↥⁅W, W⁆ := by rw [hd, pow_add]

end ClassTwo

section Assembly

theorem input_rankGL4_holds : Claims1211b.Input_rankGL4 := by
  intro p hp _hp5 Y _ _ W hWn hexp hcl hab hker E hE
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hWn
  set D := ⁅W, W⁆ with hD
  set π : Y →* Y ⧸ D := QuotientGroup.mk' D with hπ
  set V := W.map π with hV
  set P := E.map π with hP
  have hWp : IsPGroup p W := fun w => ⟨1, Subtype.ext (by simpa using hexp w w.2)⟩
  have hEp : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  have hVn : V.Normal := hWn.map π (QuotientGroup.mk'_surjective D)
  have hVp : IsPGroup p V := hWp.map π
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h : π ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.commutator_mem_commutator ha hb)
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  have hV4 : Nat.card V ≤ p ^ 4 := by
    have h1 : D.relIndex W = Nat.card V := by
      have h := Subgroup.relIndex_ker W π
      rwa [hπ, QuotientGroup.ker_mk'] at h
    have h2 := Subgroup.relIndex_mul_card (H := D) (K := W)
    rw [inf_of_le_left (Subgroup.commutator_le_self W), h1] at h2
    have h3 := card_le_pow_four_mul_card_commutator hexp hcl hab
    have hDpos : 0 < Nat.card D := Nat.card_pos
    rw [← h2] at h3
    exact Nat.le_of_mul_le_mul_right h3 hDpos
  have hPp : IsPGroup p P := hEp.map π
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    have := hE.1
    exact congrArg π (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩))
  have hPV : P ≤ Subgroup.normalizer (V : Set (Y ⧸ D)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hVn]
    exact le_top
  have hCL := relIndex_centralizer_le_pow_four hPp hPc hVp hVc hPV hV4
  set K₀ := (Subgroup.centralizer (V : Set (Y ⧸ D))).comap π with hK₀
  have hK₀n : K₀.Normal := by
    haveI : V.Normal := hVn
    exact Subgroup.Normal.comap inferInstance π
  have hK₀p : IsPGroup p K₀ := by
    intro k
    have hk : π k ∈ Subgroup.centralizer (V : Set (Y ⧸ D)) := k.2
    obtain ⟨n, hn⟩ := hker k (fun w hw => by
      have h1 : π w * π k = π k * π w :=
        Subgroup.mem_centralizer_iff.1 hk (π w) ⟨w, hw, rfl⟩
      rw [← QuotientGroup.eq_one_iff]
      change π ⁅(k : Y), w⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hK₀O : K₀ ≤ CFSG.pCore p Y := le_sSup ⟨hK₀n, hK₀p⟩
  have h1 : K₀.relIndex E = (Subgroup.centralizer (V : Set (Y ⧸ D))).relIndex P :=
    Subgroup.relIndex_comap _ π E
  have h2 : (CFSG.pCore p Y).relIndex E ≤ K₀.relIndex E := by
    rw [← Subgroup.inf_relIndex_left E (CFSG.pCore p Y), ← Subgroup.inf_relIndex_left E K₀]
    exact Subgroup.relIndex_le_of_le_left (inf_le_inf_left E hK₀O)
      Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (H := CFSG.pCore p Y) (K := E)
  rw [inf_comm] at h3
  calc Nat.card E = (CFSG.pCore p Y).relIndex E * Nat.card ↥(E ⊓ CFSG.pCore p Y) := h3.symm
    _ ≤ p ^ 4 * Nat.card ↥(E ⊓ CFSG.pCore p Y) :=
      Nat.mul_le_mul_right _ (h2.trans (h1 ▸ hCL))

end Assembly

end RankGL4Part

section GL3Part

open Matrix

abbrev G33 := GL (Fin 3) (ZMod 3)

abbrev V3 := Fin 3 → ZMod 3

abbrev SL33 : Subgroup G33 := (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).ker

theorem card_G33 : Nat.card G33 = 11232 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem card_units_zmod3 : Nat.card (ZMod 3)ˣ = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

theorem det_neg_one : Matrix.GeneralLinearGroup.det (-1 : G33) = -1 := by
  ext
  simp [Matrix.det_neg]

theorem neg_one_ne_one : (-1 : G33) ≠ 1 := by
  intro h
  have := congrArg Matrix.GeneralLinearGroup.det h
  rw [det_neg_one, map_one] at this
  exact absurd (congrArg Units.val this) (by decide)

theorem card_SL33 : Nat.card SL33 = 5616 := by
  have h : Nat.card SL33 * Nat.card (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).range =
      Nat.card G33 :=
    Subgroup.card_ker_mul_card_range (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ)
  have hr : (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u = 1 ∨ u = -1 := by
      have : ∀ v : ZMod 3, IsUnit v → v = 1 ∨ v = -1 := by decide
      rcases this u.val u.isUnit with h1 | h1
      · exact Or.inl (Units.ext h1)
      · exact Or.inr (Units.ext h1)
    rcases hu with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨-1, det_neg_one⟩
  rw [hr, Subgroup.card_top, card_units_zmod3, card_G33] at h
  omega

section Thirteen

variable {P : Subgroup G33}

theorem card_V3 : Nat.card V3 = 27 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_V3_ne_zero : Nat.card {v : V3 // v ≠ 0} = 26 := by
  rw [Nat.card_eq_fintype_card]
  rfl

@[expose] def fixSub (P : Subgroup G33) : AddSubgroup V3 where
  carrier := {v | ∀ g ∈ P, g • v = v}
  add_mem' := by
    intro a b ha hb g hg
    rw [smul_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => smul_zero g
  neg_mem' := by
    intro a ha g hg
    rw [smul_neg, ha g hg]

theorem card_addSubgroup_V3 (U : AddSubgroup V3) :
    Nat.card U = 1 ∨ Nat.card U = 3 ∨ Nat.card U = 9 ∨ Nat.card U = 27 := by
  have h := AddSubgroup.card_addSubgroup_dvd_card U
  rw [card_V3, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
  obtain ⟨i, hi, hU⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h
  interval_cases i <;> simp [hU]

theorem card_modEq_fix (hP : IsPGroup 13 P) (U : AddSubgroup V3)
    (hU : ∀ g ∈ P, ∀ u ∈ U, g • u ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ fixSub P) [MOD 13] := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let A : SubMulAction ↥P V3 :=
    { carrier := U
      smul_mem' := fun g u hu => hU g g.2 u hu }
  have h := hP.card_modEq_card_fixedPoints ↥A
  have e : MulAction.fixedPoints ↥P ↥A ≃ ↥(U ⊓ fixSub P) :=
    { toFun := fun a => ⟨a.1.1, AddSubgroup.mem_inf.2 ⟨a.1.2,
        fun g hg => congrArg Subtype.val (a.2 ⟨g, hg⟩)⟩⟩
      invFun := fun v => ⟨⟨v.1, (AddSubgroup.mem_inf.1 v.2).1⟩,
        fun g => Subtype.ext ((AddSubgroup.mem_inf.1 v.2).2 g g.2)⟩
      left_inv := fun a => rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr e] at h
  exact h

theorem isPGroup_of_card_13 (hP : Nat.card P = 13) : IsPGroup 13 P :=
  IsPGroup.of_card (n := 1) (by rw [hP, pow_one])

theorem eq_one_of_forall_smul {g : G33} (h : ∀ v : V3, g • v = v) : g = 1 := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [Units.val_one, Matrix.one_mulVec]
  exact h v

theorem fixSub_eq_bot (hP : Nat.card P = 13) : fixSub P = ⊥ := by
  have h := card_modEq_fix (isPGroup_of_card_13 hP) ⊤ (fun _ _ _ _ => AddSubgroup.mem_top _)
  rw [top_inf_eq, AddSubgroup.card_top, card_V3] at h
  rcases card_addSubgroup_V3 (fixSub P) with h1 | h1 | h1 | h1
  · exact AddSubgroup.eq_bot_of_card_eq _ h1
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · exfalso
    have htop : fixSub P = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [h1, card_V3])
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact eq_one_of_forall_smul fun v =>
        (show v ∈ fixSub P from htop ▸ AddSubgroup.mem_top v) g hg
    rw [hPbot, Subgroup.card_bot] at hP
    norm_num at hP

theorem eq_top_of_invariant (hP : Nat.card P = 13) (U : AddSubgroup V3)
    (hU : ∀ g ∈ P, ∀ u ∈ U, g • u ∈ U) {u : V3} (hu : u ∈ U) (hu0 : u ≠ 0) : U = ⊤ := by
  have h := card_modEq_fix (isPGroup_of_card_13 hP) U hU
  rw [fixSub_eq_bot hP, inf_bot_eq, AddSubgroup.card_bot] at h
  rcases card_addSubgroup_V3 U with h1 | h1 | h1 | h1
  · exfalso
    have hb := AddSubgroup.eq_bot_of_card_eq U h1
    rw [hb, AddSubgroup.mem_bot] at hu
    exact hu0 hu
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · exact AddSubgroup.eq_top_of_card_eq _ (by rw [h1, card_V3])

theorem card_centralizer_le (hP : Nat.card P = 13) :
    Nat.card (Subgroup.centralizer (P : Set G33)) ≤ 26 := by
  set v₀ : V3 := Pi.single 0 1 with hv₀def
  have hv₀ : v₀ ≠ 0 := by decide
  let f : ↥(Subgroup.centralizer (P : Set G33)) → {v : V3 // v ≠ 0} := fun c =>
    ⟨(c : G33) • v₀, fun h => hv₀ (by
      have h2 := congrArg (fun w => (c : G33)⁻¹ • w) h
      simpa using h2)⟩
  have hf : Function.Injective f := by
    intro c c' h
    have hcc : (c : G33) • v₀ = (c' : G33) • v₀ := congrArg Subtype.val h
    set d := (c : G33)⁻¹ * c' with hd
    have h1 : d • v₀ = v₀ := by
      rw [hd, mul_smul, ← hcc, inv_smul_smul]
    have hdC : d ∈ Subgroup.centralizer (P : Set G33) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ c.2) c'.2
    let U : AddSubgroup V3 :=
      { carrier := {u | d • u = u}
        add_mem' := by
          intro a b ha hb
          show d • (a + b) = a + b
          rw [smul_add, ha, hb]
        zero_mem' := smul_zero d
        neg_mem' := by
          intro a ha
          show d • (-a) = -a
          rw [smul_neg, ha] }
    have hU : ∀ g ∈ P, ∀ u ∈ U, g • u ∈ U := by
      intro g hg u hu
      show d • (g • u) = g • u
      rw [← mul_smul, ← Subgroup.mem_centralizer_iff.1 hdC g hg, mul_smul]
      rw [show d • u = u from hu]
    have htop := eq_top_of_invariant hP U hU (show v₀ ∈ U from h1) hv₀
    have hd1 : d = 1 := eq_one_of_forall_smul fun v =>
      (show v ∈ U from htop ▸ AddSubgroup.mem_top v)
    apply Subtype.ext
    rw [hd, inv_mul_eq_one] at hd1
    exact hd1
  calc Nat.card ↥(Subgroup.centralizer (P : Set G33)) ≤ Nat.card {v : V3 // v ≠ 0} :=
        Nat.card_le_card_of_injective f hf
    _ = 26 := card_V3_ne_zero

end Thirteen

section Thirteen2

variable {P : Subgroup G33}

theorem neg_one_mem_centralizer (s : Set G33) : (-1 : G33) ∈ Subgroup.centralizer s := by
  rw [Subgroup.mem_centralizer_iff]
  intro h _
  rw [mul_neg_one, neg_one_mul]

theorem le_centralizer_of_card_13 (hP : Nat.card P = 13) :
    P ≤ Subgroup.centralizer (P : Set G33) := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : IsCyclic P := isCyclic_of_prime_card hP
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : P) ⟨x, hx⟩)

theorem card_centralizer_13 (hP : Nat.card P = 13) :
    Nat.card (Subgroup.centralizer (P : Set G33)) = 26 := by
  have hle := card_centralizer_le hP
  have h13 : 13 ∣ Nat.card (Subgroup.centralizer (P : Set G33)) :=
    hP ▸ Subgroup.card_dvd_of_le (le_centralizer_of_card_13 hP)
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (P : Set G33)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hm := neg_one_mem_centralizer (P : Set G33)
    have hord : orderOf (⟨-1, hm⟩ : Subgroup.centralizer (P : Set G33)) = 2 := by
      apply orderOf_eq_prime
      · exact Subtype.ext (by simp)
      · intro h
        exact neg_one_ne_one (congrArg Subtype.val h)
    exact hord ▸ orderOf_dvd_natCard _
  have h26 : 26 ∣ Nat.card (Subgroup.centralizer (P : Set G33)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h13
  have hpos : 0 < Nat.card (Subgroup.centralizer (P : Set G33)) := Nat.card_pos
  obtain ⟨k, hk⟩ := h26
  rw [hk] at hle hpos ⊢
  have : k = 1 := by omega
  rw [this]

theorem factorization_G33_13 : (Nat.card G33).factorization 13 = 1 := by
  rw [card_G33, show (11232 : ℕ) = 13 * 864 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_normalizer_13 (hP : Nat.card P = 13) :
    Nat.card (Subgroup.normalizer (P : Set G33)) = 78 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h1 := Subgroup.card_ker_mul_card_range (Subgroup.normalizerMonoidHom P)
  rw [Subgroup.normalizerMonoidHom_ker] at h1
  have hCN : Subgroup.centralizer (P : Set G33) ≤ Subgroup.normalizer (P : Set G33) :=
    Subgroup.centralizer_le_normalizer _
  have hk : Nat.card ((Subgroup.centralizer (P : Set G33)).subgroupOf
      (Subgroup.normalizer (P : Set G33))) = 26 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, card_centralizer_13 hP]
  rw [hk] at h1
  have hAut : Nat.card (MulAut P) = 12 := by
    haveI : IsCyclic P := isCyclic_of_prime_card hP
    rw [IsCyclic.card_mulAut, hP]
    decide
  have hr : Nat.card (Subgroup.normalizerMonoidHom P).range ∣ 12 :=
    hAut ▸ Subgroup.card_subgroup_dvd_card _
  let S : Sylow 13 G33 := Sylow.ofCard P (by rw [factorization_G33_13, pow_one, hP])
  have hS := card_sylow_modEq_one 13 G33
  rw [Sylow.card_eq_index_normalizer S] at hS
  have hidx := Subgroup.index_mul_card (Subgroup.normalizer ((S : Subgroup G33) : Set G33))
  rw [card_G33] at hidx
  change (Subgroup.normalizer (P : Set G33)).index ≡ 1 [MOD 13] at hS
  change (Subgroup.normalizer (P : Set G33)).index *
    Nat.card (Subgroup.normalizer (P : Set G33)) = 11232 at hidx
  rw [← h1] at hidx ⊢
  generalize Nat.card (Subgroup.normalizerMonoidHom P).range = m at hr hidx ⊢
  generalize (Subgroup.normalizer (P : Set G33)).index = n at hS hidx
  have hm : m ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hr, by norm_num⟩
  have hd : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hd] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  unfold Nat.ModEq at hS
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end Thirteen2

section Counting

variable {P K : Subgroup G33}

theorem card_SL_inf_normalizer_13 (hP : Nat.card P = 13) :
    Nat.card ↥(SL33 ⊓ Subgroup.normalizer (P : Set G33)) = 39 := by
  set N := Subgroup.normalizer (P : Set G33) with hN
  let f : ↥N →* (ZMod 3)ˣ := (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).comp N.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hm : (-1 : G33) ∈ N := Subgroup.centralizer_le_normalizer _ (neg_one_mem_centralizer _)
  have hr : f.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u = 1 ∨ u = -1 := by
      have : ∀ v : ZMod 3, IsUnit v → v = 1 ∨ v = -1 := by decide
      rcases this u.val u.isUnit with h1 | h1
      · exact Or.inl (Units.ext h1)
      · exact Or.inr (Units.ext h1)
    rcases hu with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨⟨-1, hm⟩, det_neg_one⟩
  have hker : Nat.card f.ker = Nat.card ↥(SL33 ⊓ N) := by
    have h2 : f.ker = SL33.subgroupOf N := rfl
    rw [h2, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  rw [hr, Subgroup.card_top, card_units_zmod3, card_normalizer_13 hP, hker] at h1
  omega

theorem eq_of_dvd_432 {n : ℕ} (hn : n ∣ 432) (h1 : n % 13 = 1) : n = 1 ∨ n = 27 ∨ n = 144 := by
  have h : n ∣ 2 ^ 4 * 3 ^ 3 := by norm_num; exact hn
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hb
  interval_cases i <;> interval_cases j <;> simp_all

theorem factorization_13_of_dvd {n : ℕ} (hn0 : n ≠ 0) (h13 : 13 ∣ n) (hn : n ∣ 5616) :
    n.factorization 13 = 1 := by
  obtain ⟨k, rfl⟩ := h13
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hn0 (mul_zero 13)
  have hk13 : ¬ 13 ∣ k := by
    rintro ⟨l, rfl⟩
    have h169 : 169 ∣ 5616 := (Dvd.intro l (by ring)).trans hn
    norm_num at h169
  rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd hk13]

theorem card_cases (hKSL : K ≤ SL33) (hPK : P ≤ K) (hP : Nat.card P = 13) :
    (Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G33)) = 13 ∧
      (Nat.card K = 13 ∨ Nat.card K = 351 ∨ Nat.card K = 1872)) ∨
    (Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G33)) = 39 ∧
      (Nat.card K = 39 ∨ Nat.card K = 5616)) := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (P : Set G33) with hN
  have hm1 : Nat.card ↥(K ⊓ N) ∣ 39 := by
    rw [← card_SL_inf_normalizer_13 hP]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right N hKSL)
  have hm2 : 13 ∣ Nat.card ↥(K ⊓ N) := by
    rw [← hP]
    exact Subgroup.card_dvd_of_le (le_inf hPK Subgroup.le_normalizer)
  have hK : Nat.card K ∣ 5616 := card_SL33 ▸ Subgroup.card_dvd_of_le hKSL
  set P' : Subgroup ↥K := P.subgroupOf K with hP'def
  have hP' : Nat.card P' = 13 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hP]
  have h13K : 13 ∣ Nat.card K := hP ▸ Subgroup.card_dvd_of_le hPK
  have hfac : (Nat.card ↥K).factorization 13 = 1 :=
    factorization_13_of_dvd Nat.card_pos.ne' h13K hK
  let S : Sylow 13 ↥K := Sylow.ofCard P' (by rw [hfac, pow_one, hP'])
  have hS := card_sylow_modEq_one 13 ↥K
  rw [Sylow.card_eq_index_normalizer S] at hS
  have hidx := Subgroup.index_mul_card (Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K))
  have hNcard : Nat.card (Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K)) =
      Nat.card ↥(K ⊓ N) := by
    change Nat.card (Subgroup.normalizer (P' : Set ↥K)) = _
    rw [hP'def, ← Subgroup.subgroupOf_normalizer_eq hPK, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
  rw [hNcard] at hidx
  generalize (Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K)).index = n at hS hidx
  generalize Nat.card ↥(K ⊓ N) = m at hm1 hm2 hidx ⊢
  unfold Nat.ModEq at hS
  have hm : m = 13 ∨ m = 39 := by
    have : m ∈ Nat.divisors 39 := Nat.mem_divisors.2 ⟨hm1, by norm_num⟩
    have hd : Nat.divisors 39 = {1, 3, 13, 39} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rw [← hidx] at hK ⊢
  rcases hm with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hn : n ∣ 432 := by
      have h' : n * 13 ∣ 432 * 13 := by simpa using hK
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
    rcases eq_of_dvd_432 hn (by omega) with rfl | rfl | rfl <;> simp
  · right
    refine ⟨rfl, ?_⟩
    have hn : n ∣ 144 := by
      have h' : n * 39 ∣ 144 * 39 := by simpa using hK
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
    have hn' : n ∣ 432 := hn.trans (by norm_num)
    rcases eq_of_dvd_432 hn' (by omega) with rfl | rfl | rfl
    · simp
    · norm_num at hn
    · simp

end Counting

section Classification

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5 (isSolvable_of_card_eq_pow_mul_pow)

theorem isSolvable_of_card_dvd_432 {H : Type} [Group H] [Finite H]
    (hn : Nat.card H ∣ 432) : Group.IsSolvable H := by
  have h : Nat.card H ∣ 2 ^ 4 * 3 ^ 3 := by norm_num; exact hn
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hb
  exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hab.symm

theorem isSolvable_of_selfNormalizing {K P : Subgroup G33} (hPK : P ≤ K) (hP : Nat.card P = 13)
    (hm : Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G33)) = 13) (hK : Nat.card K ∣ 5616) :
    Group.IsSolvable K := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set P' : Subgroup ↥K := P.subgroupOf K with hP'def
  have hP' : Nat.card P' = 13 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hP]
  have h13K : 13 ∣ Nat.card K := hP ▸ Subgroup.card_dvd_of_le hPK
  let S : Sylow 13 ↥K := Sylow.ofCard P'
    (by rw [factorization_13_of_dvd Nat.card_pos.ne' h13K hK, pow_one, hP'])
  have hSP : (S : Subgroup ↥K) = P' := rfl
  have hNcard : Nat.card (Subgroup.normalizer (P' : Set ↥K)) = 13 := by
    rw [hP'def, ← Subgroup.subgroupOf_normalizer_eq hPK, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, hm]
  have heq : Subgroup.normalizer (P' : Set ↥K) = P' :=
    (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hNcard, hP'])).symm
  haveI : IsCyclic P' := isCyclic_of_prime_card hP'
  have hNS : Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) ≤
      Subgroup.centralizer ((S : Subgroup ↥K) : Set ↥K) := by
    rw [hSP, heq]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : P') ⟨x, hx⟩)
  have hcompl := MonoidHom.ker_transferSylow_isComplement' S hNS
  have hcard := hcompl.card_mul_card
  have hSc : Nat.card (S : Subgroup ↥K) = 13 := hP'
  rw [hSc] at hcard
  haveI : Group.IsSolvable (MonoidHom.transferSylow S hNS).ker := by
    apply isSolvable_of_card_dvd_432
    have h' : Nat.card (MonoidHom.transferSylow S hNS).ker * 13 ∣ 432 * 13 := by
      rw [hcard]; simpa using hK
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
  haveI : Group.IsSolvable ↥(S : Subgroup ↥K) := by
    rw [hSP]
    exact Group.isSolvable_of_comm fun a b => mul_comm' a b
  exact Group.isSolvable_of_ker_le_range (MonoidHom.transferSylow S hNS).ker.subtype
    (MonoidHom.transferSylow S hNS) (by rw [Subgroup.range_subtype])

theorem eq_SL33_of_not_isSolvable {X₀ : Subgroup G33} (hX₀ : X₀ ≤ SL33)
    (hns : ¬ Group.IsSolvable X₀) : X₀ = SL33 := by
  have hX₀d : Nat.card X₀ ∣ 5616 := card_SL33 ▸ Subgroup.card_dvd_of_le hX₀
  by_cases h13 : 13 ∣ Nat.card X₀
  · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X₀) 13 h13
    set P := Subgroup.zpowers (x : G33) with hPdef
    have hP : Nat.card P = 13 := by rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hPK : P ≤ X₀ := Subgroup.zpowers_le.2 x.2
    rcases card_cases hX₀ hPK hP with ⟨hm, -⟩ | ⟨-, hK⟩
    · exact absurd (isSolvable_of_selfNormalizing hPK hP hm hX₀d) hns
    · rcases hK with hK | hK
      · exact absurd (isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) Nat.prime_three
          (by norm_num : Nat.Prime 13) (by norm_num) (by rw [hK]; norm_num)) hns
      · exact Subgroup.eq_of_le_of_card_ge hX₀ (by rw [hK, card_SL33])
  · refine absurd (isSolvable_of_card_dvd_432 ?_) hns
    have hcop : Nat.Coprime (Nat.card X₀) 13 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h13)
    exact hcop.dvd_of_dvd_mul_right (by simpa using hX₀d)

end Classification

section NotPSolvable

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5 (isPSolvable_of_isSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_normal)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)

theorem SL33_le_of_not_isPSolvable {X : Subgroup G33}
    (hX : ¬ CFSG.HallHigman.IsPSolvable 3 X) : SL33 ≤ X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hns : ¬ Group.IsSolvable ↥(SL33 ⊓ X) := by
    intro hsol
    apply hX
    let f : ↥X →* (ZMod 3)ˣ := (Matrix.GeneralLinearGroup.det : G33 →* (ZMod 3)ˣ).comp X.subtype
    have hker : f.ker = SL33.subgroupOf X := rfl
    have e : ↥(SL33 ⊓ X) ≃* ↥f.ker := by
      rw [hker, ← Subgroup.inf_subgroupOf_right]
      exact (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hkerS : CFSG.HallHigman.IsPSolvable 3 f.ker :=
      isPSolvable_of_mulEquiv e (isPSolvable_of_isSolvable Nat.prime_three hsol)
    have hrange : CFSG.HallHigman.IsPSolvable 3 f.range :=
      isPSolvable_of_isSolvable Nat.prime_three
        (Group.isSolvable_of_comm fun a b => Subtype.ext (mul_comm (a : (ZMod 3)ˣ) b))
    exact isPSolvable_of_normal f.ker hkerS
      (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange f).symm hrange)
  have h := eq_SL33_of_not_isSolvable inf_le_left hns
  rw [← h]
  exact inf_le_right

end NotPSolvable

section Unitriangular

@[expose] def uMat (x y z : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, x, z; 0, 1, y; 0, 0, 1]

theorem uMat_mul (x y z x' y' z' : ZMod 3) :
    uMat x y z * uMat x' y' z' = uMat (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uMat_zero : uMat 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem uMat_mul_inv (x y z : ZMod 3) : uMat x y z * uMat (-x) (-y) (x * y - z) = 1 := by
  rw [uMat_mul, ← uMat_zero]
  congr 1 <;> ring

theorem uMat_inv_mul (x y z : ZMod 3) : uMat (-x) (-y) (x * y - z) * uMat x y z = 1 := by
  rw [uMat_mul, ← uMat_zero]
  congr 1 <;> ring

@[expose] def uGL (x y z : ZMod 3) : G33 :=
  ⟨uMat x y z, uMat (-x) (-y) (x * y - z), uMat_mul_inv x y z, uMat_inv_mul x y z⟩

theorem uGL_mul (x y z x' y' z' : ZMod 3) :
    uGL x y z * uGL x' y' z' = uGL (x + x') (y + y') (z + z' + x * y') :=
  Units.ext (uMat_mul x y z x' y' z')

theorem uGL_inv (x y z : ZMod 3) : (uGL x y z)⁻¹ = uGL (-x) (-y) (x * y - z) := Units.ext rfl

theorem uGL_zero : uGL 0 0 0 = 1 := Units.ext uMat_zero

theorem uGL_injective {x y z x' y' z' : ZMod 3} (h : uGL x y z = uGL x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have h1 : uMat x y z = uMat x' y' z' := congrArg Units.val h
  refine ⟨?_, ?_, ?_⟩
  · simpa [uMat] using congrFun (congrFun h1 0) 1
  · simpa [uMat] using congrFun (congrFun h1 1) 2
  · simpa [uMat] using congrFun (congrFun h1 0) 2

theorem det_uGL (x y z : ZMod 3) : uGL x y z ∈ SL33 := by
  rw [MonoidHom.mem_ker]
  ext
  simp [uGL, uMat, Matrix.det_fin_three]

@[expose] def U3 : Subgroup G33 where
  carrier := {g | ∃ x y z, g = uGL x y z}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, rfl⟩ ⟨x', y', z', rfl⟩
    exact ⟨_, _, _, uGL_mul x y z x' y' z'⟩
  one_mem' := ⟨0, 0, 0, uGL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, rfl⟩
    exact ⟨_, _, _, uGL_inv x y z⟩

@[expose] def R1 : Subgroup G33 where
  carrier := {g | ∃ x z, g = uGL x 0 z}
  mul_mem' := by
    rintro _ _ ⟨x, z, rfl⟩ ⟨x', z', rfl⟩
    exact ⟨x + x', z + z', by rw [uGL_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, 0, uGL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨x, z, rfl⟩
    exact ⟨-x, -z, by rw [uGL_inv]; congr 1 <;> ring⟩

@[expose] def R2 : Subgroup G33 where
  carrier := {g | ∃ y z, g = uGL 0 y z}
  mul_mem' := by
    rintro _ _ ⟨y, z, rfl⟩ ⟨y', z', rfl⟩
    exact ⟨y + y', z + z', by rw [uGL_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, 0, uGL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨y, z, rfl⟩
    exact ⟨-y, -z, by rw [uGL_inv]; congr 1 <;> ring⟩

theorem card_U3 : Nat.card U3 = 27 := by
  let f : ZMod 3 × ZMod 3 × ZMod 3 → U3 := fun t => ⟨uGL t.1 t.2.1 t.2.2, _, _, _, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uGL_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨x, y, z, hg⟩ := g.2
      exact ⟨(x, y, z), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod, ZMod.card]

theorem card_R1 : Nat.card R1 = 9 := by
  let f : ZMod 3 × ZMod 3 → R1 := fun t => ⟨uGL t.1 0 t.2, _, _, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ?_, fun g => ?_⟩
    · obtain ⟨h1, -, h3⟩ := uGL_injective (congrArg Subtype.val h)
      exact Prod.ext h1 h3
    · obtain ⟨x, z, hg⟩ := g.2
      exact ⟨(x, z), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod, ZMod.card]

theorem card_R2 : Nat.card R2 = 9 := by
  let f : ZMod 3 × ZMod 3 → R2 := fun t => ⟨uGL 0 t.1 t.2, _, _, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ?_, fun g => ?_⟩
    · obtain ⟨-, h2, h3⟩ := uGL_injective (congrArg Subtype.val h)
      exact Prod.ext h2 h3
    · obtain ⟨y, z, hg⟩ := g.2
      exact ⟨(y, z), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod, ZMod.card]

theorem R1_le_U3 : R1 ≤ U3 := by
  rintro _ ⟨x, z, rfl⟩
  exact ⟨x, 0, z, rfl⟩

theorem R2_le_U3 : R2 ≤ U3 := by
  rintro _ ⟨y, z, rfl⟩
  exact ⟨0, y, z, rfl⟩

theorem U3_le_SL33 : U3 ≤ SL33 := by
  rintro _ ⟨x, y, z, rfl⟩
  exact det_uGL x y z

end Unitriangular

section Weyl

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {R : Subgroup G} {g : G}
    (h : ∀ r ∈ R, g * r * g⁻¹ ∈ R) : g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let φ : R → R := fun r => ⟨g * r * g⁻¹, h r r.2⟩
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab)))
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨_, hx⟩
  have hrx : (r : G) = x := mul_left_cancel (mul_right_cancel (congrArg Subtype.val hr))
  exact hrx ▸ r.2

@[expose] def s1Mat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 1, 0; -1, 0, 0; 0, 0, 1]
@[expose] def s1iMat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, -1, 0; 1, 0, 0; 0, 0, 1]
@[expose] def s2Mat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 0, 0; 0, 0, 1; 0, -1, 0]
@[expose] def s2iMat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 0, 0; 0, 0, -1; 0, 1, 0]
@[expose] def bMat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![-1, 0, -1; 0, -1, 0; 0, 0, 1]

@[expose] def s1 : G33 := ⟨s1Mat, s1iMat, by decide, by decide⟩
@[expose] def s2 : G33 := ⟨s2Mat, s2iMat, by decide, by decide⟩
@[expose] def bG : G33 := ⟨bMat, bMat, by decide, by decide⟩

theorem s1_mem : s1 ∈ SL33 := by
  rw [MonoidHom.mem_ker]
  ext
  simp [s1, s1Mat, Matrix.det_fin_three]

theorem s2_mem : s2 ∈ SL33 := by
  rw [MonoidHom.mem_ker]
  ext
  simp [s2, s2Mat, Matrix.det_fin_three]

theorem bG_mem : bG ∈ SL33 := by
  rw [MonoidHom.mem_ker]
  ext
  simp [bG, bMat, Matrix.det_fin_three]

theorem s2_conj (x z : ZMod 3) : s2 * uGL x 0 z * s2⁻¹ = uGL z 0 (-x) := by
  apply Units.ext
  show s2Mat * uMat x 0 z * s2iMat = uMat z 0 (-x)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s2Mat, s2iMat, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem bG_conj (x z : ZMod 3) : bG * uGL x 0 z * bG⁻¹ = uGL x 0 (-z) := by
  apply Units.ext
  show bMat * uMat x 0 z * bMat = uMat x 0 (-z)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem s1_conj (y z : ZMod 3) : s1 * uGL 0 y z * s1⁻¹ = uGL 0 (-z) y := by
  apply Units.ext
  show s1Mat * uMat 0 y z * s1iMat = uMat 0 (-z) y
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s1Mat, s1iMat, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s2_mem_normalizer : s2 ∈ Subgroup.normalizer (R1 : Set G33) :=
  mem_normalizer_of_conj_mem (by rintro _ ⟨x, z, rfl⟩; exact ⟨z, -x, s2_conj x z⟩)

theorem bG_mem_normalizer : bG ∈ Subgroup.normalizer (R1 : Set G33) :=
  mem_normalizer_of_conj_mem (by rintro _ ⟨x, z, rfl⟩; exact ⟨x, -z, bG_conj x z⟩)

theorem s1_mem_normalizer : s1 ∈ Subgroup.normalizer (R2 : Set G33) :=
  mem_normalizer_of_conj_mem (by rintro _ ⟨y, z, rfl⟩; exact ⟨-z, y, s1_conj y z⟩)

theorem U3_le_normalizer_R1 : U3 ≤ Subgroup.normalizer (R1 : Set G33) := by
  rintro _ ⟨x, y, z, rfl⟩
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨a, c, rfl⟩
  refine ⟨a, c - a * y, ?_⟩
  rw [uGL_inv, uGL_mul, uGL_mul]
  congr 1 <;> ring

theorem orderOf_c : orderOf (s1 * s2 * bG) = 13 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (s1Mat * s2Mat * bMat) ^ 13 = 1
    decide
  · intro h
    have h1 := congrArg Units.val h
    rw [Units.val_one] at h1
    exact absurd (h1 : s1Mat * s2Mat * bMat = 1) (by decide)

theorem orderOf_bG : orderOf bG = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show bMat ^ 2 = 1
    decide
  · intro h
    have h1 := congrArg Units.val h
    rw [Units.val_one] at h1
    exact absurd (h1 : bMat = 1) (by decide)

end Weyl

section Generation

@[expose] def GenProp (Z : Type) [Group Z] : Prop :=
  ∀ S : Sylow 3 Z, (⊤ : Subgroup Z) =
    ⨆ (Q : Subgroup Z) (_ : Q ≤ S ∧ Q.relIndex S = 3), Subgroup.normalizer (Q : Set Z)

theorem SL33_le_sup (X : Subgroup G33) (hX : SL33 ≤ X) :
    SL33 ≤ (Subgroup.normalizer (R1 : Set G33) ⊓ X) ⊔ (Subgroup.normalizer (R2 : Set G33) ⊓ X) := by
  set K := (Subgroup.normalizer (R1 : Set G33) ⊓ X) ⊔ (Subgroup.normalizer (R2 : Set G33) ⊓ X)
    with hK
  set K₀ := K ⊓ SL33 with hK₀
  have hU : U3 ≤ K₀ :=
    le_inf (le_sup_of_le_left (le_inf U3_le_normalizer_R1 (U3_le_SL33.trans hX))) U3_le_SL33
  have hb : bG ∈ K₀ := Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left
    (Subgroup.mem_inf.2 ⟨bG_mem_normalizer, hX bG_mem⟩), bG_mem⟩
  have hs2 : s2 ∈ K₀ := Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left
    (Subgroup.mem_inf.2 ⟨s2_mem_normalizer, hX s2_mem⟩), s2_mem⟩
  have hs1 : s1 ∈ K₀ := Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right
    (Subgroup.mem_inf.2 ⟨s1_mem_normalizer, hX s1_mem⟩), s1_mem⟩
  have hc : s1 * s2 * bG ∈ K₀ := K₀.mul_mem (K₀.mul_mem hs1 hs2) hb
  have hP : Nat.card (Subgroup.zpowers (s1 * s2 * bG)) = 13 := by
    rw [Nat.card_zpowers, orderOf_c]
  have hPK : Subgroup.zpowers (s1 * s2 * bG) ≤ K₀ := Subgroup.zpowers_le.2 hc
  have h27 : 27 ∣ Nat.card K₀ := card_U3 ▸ Subgroup.card_dvd_of_le hU
  have h2 : 2 ∣ Nat.card K₀ := by
    have h := orderOf_dvd_natCard (⟨bG, hb⟩ : K₀)
    rwa [← Subgroup.orderOf_coe, orderOf_bG] at h
  rcases card_cases inf_le_right hPK hP with ⟨-, hc'⟩ | ⟨-, hc'⟩
  · exfalso
    rcases hc' with hc' | hc' | hc' <;> rw [hc'] at h27 h2 <;> omega
  · rcases hc' with hc' | hc'
    · exfalso
      rw [hc'] at h2
      norm_num at h2
    · have heq : K₀ = SL33 :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc', card_SL33])
      rw [← heq]
      exact inf_le_left

theorem det_eq_one_or_neg_one (g : G33) :
    Matrix.GeneralLinearGroup.det g = 1 ∨ Matrix.GeneralLinearGroup.det g = -1 := by
  have : ∀ v : ZMod 3, IsUnit v → v = 1 ∨ v = -1 := by decide
  rcases this _ (Matrix.GeneralLinearGroup.det g).isUnit with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext h1)

theorem le_sup_normalizers (X : Subgroup G33) (hX : SL33 ≤ X) :
    X ≤ (Subgroup.normalizer (R1 : Set G33) ⊓ X) ⊔ (Subgroup.normalizer (R2 : Set G33) ⊓ X) := by
  intro x hx
  by_cases hxs : x ∈ SL33
  · exact SL33_le_sup X hX hxs
  · have hdet : Matrix.GeneralLinearGroup.det x = -1 :=
      (det_eq_one_or_neg_one x).resolve_left (fun h => hxs (MonoidHom.mem_ker.2 h))
    have hnx : -x ∈ SL33 := by
      rw [MonoidHom.mem_ker, ← neg_one_mul, map_mul, det_neg_one, hdet]
      simp
    have hm1 : (-1 : G33) ∈ X := by
      have h := X.mul_mem (hX hnx) (X.inv_mem hx)
      rwa [← neg_one_mul, mul_assoc, mul_inv_cancel, mul_one] at h
    have hm1N : (-1 : G33) ∈ Subgroup.normalizer (R1 : Set G33) :=
      Subgroup.centralizer_le_normalizer _ (neg_one_mem_centralizer _)
    have hx' : x = (-1) * (-x) := by rw [neg_one_mul, neg_neg]
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hm1N, hm1⟩))
      (SL33_le_sup X hX hnx)

theorem genProp_of_one {Z : Type} [Group Z] [Finite Z] (S₀ : Sylow 3 Z)
    (h : (⊤ : Subgroup Z) ≤
      ⨆ (Q : Subgroup Z) (_ : Q ≤ S₀ ∧ Q.relIndex S₀ = 3), Subgroup.normalizer (Q : Set Z)) :
    GenProp Z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Z S₀ S
  refine le_antisymm ?_ le_top
  set φ : Z →* Z := (MulAut.conj g).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.conj g).injective
  have hS : ((g • S₀ : Sylow 3 Z) : Subgroup Z) = (S₀ : Subgroup Z).map φ := by
    rw [Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  calc (⊤ : Subgroup Z) = (⊤ : Subgroup Z).map φ :=
        (Subgroup.map_top_of_surjective φ (MulAut.conj g).surjective).symm
    _ ≤ (⨆ (Q : Subgroup Z) (_ : Q ≤ S₀ ∧ Q.relIndex S₀ = 3),
          Subgroup.normalizer (Q : Set Z)).map φ := Subgroup.map_mono h
    _ ≤ _ := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun Q => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hQ => ?_
      refine le_iSup₂_of_le (Q.map φ) ⟨?_, ?_⟩ ?_
      · rw [hS]
        exact Subgroup.map_mono hQ.1
      · rw [hS, Subgroup.relIndex_map_map_of_injective _ _ hφi]
        exact hQ.2
      · rw [hφ, Subgroup.map_equiv_normalizer_eq]

theorem genProp_of_SL33_le (X : Subgroup G33) (hX : SL33 ≤ X) : GenProp X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU3X : U3 ≤ X := U3_le_SL33.trans hX
  have hXc : Nat.card X = 5616 ∨ Nat.card X = 11232 := by
    have h1 : Nat.card X ∣ 11232 := card_G33 ▸ Subgroup.card_subgroup_dvd_card X
    have h2 : 5616 ∣ Nat.card X := card_SL33 ▸ Subgroup.card_dvd_of_le hX
    obtain ⟨k, hk⟩ := h2
    rw [hk] at h1 ⊢
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5616)
      (show 5616 * k ∣ 5616 * 2 by norm_num; exact h1)
    rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl <;> simp
  have hfac : (Nat.card X).factorization 3 = 3 := by
    rcases hXc with h | h <;> rw [h]
    · rw [show (5616 : ℕ) = 3 ^ 3 * 208 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    · rw [show (11232 : ℕ) = 3 ^ 3 * 416 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hUc : Nat.card (U3.subgroupOf X) = 3 ^ (Nat.card X).factorization 3 := by
    rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU3X).toEquiv, card_U3]
    norm_num
  set S₀ : Sylow 3 X := Sylow.ofCard (U3.subgroupOf X) hUc with hS₀
  have hSc : (S₀ : Subgroup X) = U3.subgroupOf X := rfl
  have hidx : ∀ {R : Subgroup G33}, R ≤ U3 → Nat.card R = 9 →
      R.subgroupOf X ≤ S₀ ∧ (R.subgroupOf X).relIndex S₀ = 3 := by
    intro R hRU hR
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hSc, Subgroup.mem_subgroupOf]
      exact hRU (Subgroup.mem_subgroupOf.1 hx)
    · rw [hSc, Subgroup.relIndex_subgroupOf hU3X]
      have h := Subgroup.relIndex_mul_card (H := R) (K := U3)
      rw [inf_of_le_left hRU, hR, card_U3] at h
      omega
  refine genProp_of_one S₀ ?_
  intro y _
  have hy : (y : G33) ∈ (Subgroup.normalizer (R1 : Set G33) ⊓ X) ⊔
      (Subgroup.normalizer (R2 : Set G33) ⊓ X) := le_sup_normalizers X hX y.2
  have hmap : ((Subgroup.normalizer (R1 : Set G33)).subgroupOf X ⊔
      (Subgroup.normalizer (R2 : Set G33)).subgroupOf X).map X.subtype =
      (Subgroup.normalizer (R1 : Set G33) ⊓ X) ⊔ (Subgroup.normalizer (R2 : Set G33) ⊓ X) := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
  rw [← hmap] at hy
  have hy' := (Subgroup.mem_map_iff_mem X.subtype_injective).1 hy
  have hle : (Subgroup.normalizer (R1 : Set G33)).subgroupOf X ⊔
      (Subgroup.normalizer (R2 : Set G33)).subgroupOf X ≤
      ⨆ (Q : Subgroup X) (_ : Q ≤ S₀ ∧ Q.relIndex S₀ = 3), Subgroup.normalizer (Q : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.subgroupOf_normalizer_eq (R1_le_U3.trans hU3X)]
      exact le_iSup₂_of_le (R1.subgroupOf X) (hidx R1_le_U3 card_R1) le_rfl
    · rw [Subgroup.subgroupOf_normalizer_eq (R2_le_U3.trans hU3X)]
      exact le_iSup₂_of_le (R2.subgroupOf X) (hidx R2_le_U3 card_R2) le_rfl
  exact hle hy'

end Generation

section Lift

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5 (isPSolvable_of_isSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_normal)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)

theorem genProp_of_surjective {Y Z : Type} [Group Y] [Group Z] [Finite Y] (f : Y →* Z)
    (hf : Function.Surjective f) (hker : IsPGroup 3 f.ker) (hZ : GenProp Z) [Nontrivial Z] :
    GenProp Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Z := Finite.of_surjective f hf
  intro S
  set S' : Sylow 3 Z := S.mapSurjective hf with hS'def
  have hS' := hZ S'
  have hkS : f.ker ≤ S := hker.le_sylow_of_normal S
  have hcomapS : (S' : Subgroup Z).comap f = S := by
    rw [hS'def, Sylow.coe_mapSurjective, Subgroup.comap_map_eq, sup_eq_left.2 hkS]
  set J := ⨆ (Q : Subgroup Y) (_ : Q ≤ S ∧ Q.relIndex S = 3), Subgroup.normalizer (Q : Set Y)
    with hJ
  have hmem : ∀ Q' : Subgroup Z, Q' ≤ S' ∧ Q'.relIndex S' = 3 →
      Q'.comap f ≤ S ∧ (Q'.comap f).relIndex S = 3 := by
    intro Q' hQ'
    refine ⟨?_, ?_⟩
    · rw [← hcomapS]
      exact Subgroup.comap_mono hQ'.1
    · rw [Subgroup.relIndex_comap, ← Sylow.coe_mapSurjective hf]
      exact hQ'.2
  have hstep : ∀ Q' : Subgroup Z, Q' ≤ S' ∧ Q'.relIndex S' = 3 →
      (Subgroup.normalizer (Q' : Set Z)).comap f ≤ J := fun Q' hQ' =>
    le_trans (Subgroup.le_normalizer_comap f) (le_iSup₂_of_le (Q'.comap f) (hmem Q' hQ') le_rfl)
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q' : Subgroup Z, Q' ≤ S' ∧ Q'.relIndex S' = 3 := by
    by_contra hnone
    have hbot : (⨆ (Q : Subgroup Z) (_ : Q ≤ S' ∧ Q.relIndex S' = 3),
        Subgroup.normalizer (Q : Set Z)) = ⊥ := by
      refine iSup₂_eq_bot.2 fun Q hQ => absurd ⟨Q, hQ⟩ hnone
    rw [hbot] at hS'
    exact bot_ne_top hS'.symm
  have hkJ : f.ker ≤ J := by
    have h1 : f.ker ≤ Q₀.comap f := fun k hk => by
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hk]
      exact Q₀.one_mem
    exact h1.trans (Subgroup.le_normalizer.trans (le_iSup₂_of_le (Q₀.comap f) (hmem Q₀ hQ₀) le_rfl))
  have hmap : J.map f = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [hS']
    refine iSup₂_le fun Q' hQ' => ?_
    calc Subgroup.normalizer (Q' : Set Z)
        = ((Subgroup.normalizer (Q' : Set Z)).comap f).map f :=
          (Subgroup.map_comap_eq_self_of_surjective hf _).symm
      _ ≤ J.map f := Subgroup.map_mono (hstep Q' hQ')
  rw [← Subgroup.comap_map_eq_self hkJ, hmap, Subgroup.comap_top]

end Lift

section InputGL3

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5 (isPSolvable_of_isSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_normal)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)

theorem card_GL_dvd_432 {n : ℕ} (hn : n ≤ 2) : Nat.card (GL (Fin n) (ZMod 3)) ∣ 432 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> simp [Fin.prod_univ_two] <;> norm_num

theorem genProp_of_hom {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : n ≤ 3)
    (ρ : Y →* GL (Fin n) (ZMod 3)) (hker : IsPGroup 3 ρ.ker)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 Y) : GenProp Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange : ¬ CFSG.HallHigman.IsPSolvable 3 ρ.range := by
    intro h
    apply hns
    haveI := hker.isNilpotent
    exact isPSolvable_of_normal ρ.ker (isPSolvable_of_isSolvable Nat.prime_three inferInstance)
      (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange ρ).symm h)
  have hsmall : n ≤ 2 → False := fun h2 =>
    hrange (isPSolvable_of_isSolvable Nat.prime_three (isSolvable_of_card_dvd_432
      ((Subgroup.card_subgroup_dvd_card _).trans (card_GL_dvd_432 h2))))
  have hn3 : n = 3 := by
    by_contra h
    exact hsmall (by omega)
  subst hn3
  haveI : Nontrivial ρ.range := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hrange (isPSolvable_of_isSolvable Nat.prime_three inferInstance)
  exact genProp_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) (genProp_of_SL33_le _ (SL33_le_of_not_isPSolvable hrange))

theorem input_GL3_holds : Claims1211b.Input_GL3 := by
  intro Y _ _ W hWn hexp hcard hker hns
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hWn
  set D := ⁅W, W⁆ with hD
  set π : Y →* Y ⧸ D := QuotientGroup.mk' D with hπ
  set V := W.map π with hV
  haveI hVn : V.Normal := hWn.map π (QuotientGroup.mk'_surjective D)
  set ρ : Y →* MulAut ↥V := (MulAut.conjNormal (H := V)).comp π with hρ
  have hkerρ : IsPGroup 3 ρ.ker := by
    intro k
    have hk : ρ k = 1 := k.2
    obtain ⟨m, hm⟩ := hker k (fun w hw => by
      have h1 : π k * π w * (π k)⁻¹ = π w := by
        have := congrArg (fun α : MulAut ↥V => ((α ⟨π w, w, hw, rfl⟩ : ↥V) : Y ⧸ D)) hk
        simpa [hρ, MulAut.conjNormal_apply] using this
      rw [← QuotientGroup.eq_one_iff]
      change π ⁅(k : Y), w⁆ = 1
      rw [map_commutatorElement, commutatorElement_def, h1, mul_inv_cancel])
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  have hVc : ∀ a b : ↥V, a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have h : π ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.commutator_mem_commutator ha hb)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hVe : ∀ a : ↥V, a ^ 3 = 1 := by
    rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hexp a ha, map_one]
  have hVp : IsPGroup 3 ↥V := fun a => ⟨1, by rw [pow_one]; exact hVe a⟩
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hV27 : Nat.card V ≤ 27 := by
    have h1 : D.relIndex W = Nat.card V := by
      have h := Subgroup.relIndex_ker W π
      rwa [hπ, QuotientGroup.ker_mk'] at h
    have h2 := Subgroup.relIndex_mul_card (H := D) (K := W)
    rw [inf_of_le_left (Subgroup.commutator_le_self W), h1] at h2
    have hDpos : 0 < Nat.card D := Nat.card_pos
    rw [← h2] at hcard
    exact Nat.le_of_mul_le_mul_right (by linarith) hDpos
  have hn3 : n ≤ 3 := by
    rw [hn] at hV27
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hVc hVe hn
  set ρ' : Y →* GL (Fin n) (ZMod 3) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ with hρ'
  have hker' : ρ'.ker = ρ.ker := by
    ext y
    simp only [MonoidHom.mem_ker, hρ', MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact genProp_of_hom hn3 ρ' (hker' ▸ hkerρ) hns

end InputGL3

end GL3Part

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalGL

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711c2
public import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711d

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Bar

variable {X : Type} [Group X] [Finite X] {p : ℕ}

@[expose] noncomputable def kOf {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (b : ↥B) : ↥L :=
  ⟨Classical.choose (hin b b.2), (Classical.choose_spec (hin b b.2)).1⟩

theorem kOf_spec {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (b : ↥B) :
    ((kOf hin b : ↥L) : X)⁻¹ * (b : X) ∈ Subgroup.centralizer (L : Set X) :=
  (Classical.choose_spec (hin b b.2)).2

theorem mem_center_of_mem_centralizer {L : Subgroup X} {k : ↥L}
    (hk : (k : X) ∈ Subgroup.centralizer (L : Set X)) : k ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hk y y.2)

theorem mem_centralizer_of_mem_center {L : Subgroup X} {k : ↥L}
    (hk : k ∈ Subgroup.center ↥L) : (k : X) ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hk ⟨y, hy⟩)

theorem mk_eq_of_inner {L : Subgroup X} {k k' : ↥L} {b : X}
    (hk : (k : X)⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hk' : (k' : X)⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) :
    (QuotientGroup.mk k : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk k' := by
  rw [QuotientGroup.eq]
  apply mem_center_of_mem_centralizer
  have e : ((k⁻¹ * k' : ↥L) : X) = ((k : X)⁻¹ * b) * ((k' : X)⁻¹ * b)⁻¹ := by
    push_cast
    group
  rw [e]
  exact Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hk')

theorem mul_inner_mem {L : Subgroup X} {k k' a b : X} (hk' : k' ∈ L)
    (ha : k⁻¹ * a ∈ Subgroup.centralizer (L : Set X))
    (hb : k'⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) :
    (k * k')⁻¹ * (a * b) ∈ Subgroup.centralizer (L : Set X) := by
  have hc : k' * (k⁻¹ * a) = (k⁻¹ * a) * k' := Subgroup.mem_centralizer_iff.1 ha k' hk'
  have e : (k * k')⁻¹ * (a * b) = (k⁻¹ * a) * (k'⁻¹ * b) := by
    calc (k * k')⁻¹ * (a * b) = k'⁻¹ * ((k⁻¹ * a) * k') * (k'⁻¹ * b) := by group
      _ = k'⁻¹ * (k' * (k⁻¹ * a)) * (k'⁻¹ * b) := by rw [hc]
      _ = (k⁻¹ * a) * (k'⁻¹ * b) := by group
  rw [e]
  exact Subgroup.mul_mem _ ha hb

@[expose] noncomputable def barHom {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) :
    ↥B →* ↥L ⧸ Subgroup.center ↥L where
  toFun b := QuotientGroup.mk (kOf hin b)
  map_one' := by
    have h1 : ((1 : ↥L) : X)⁻¹ * ((1 : ↥B) : X) ∈ Subgroup.centralizer (L : Set X) := by
      simp only [OneMemClass.coe_one, inv_one, mul_one]
      exact Subgroup.one_mem _
    rw [mk_eq_of_inner (kOf_spec hin 1) h1]
    rfl
  map_mul' a b := by
    have h1 : (((kOf hin a * kOf hin b : ↥L) : X))⁻¹ * ((a * b : ↥B) : X) ∈
        Subgroup.centralizer (L : Set X) := by
      push_cast
      exact mul_inner_mem (kOf hin b).2 (kOf_spec hin a) (kOf_spec hin b)
    rw [mk_eq_of_inner (kOf_spec hin (a * b)) h1]
    rfl

theorem barHom_apply {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (b : ↥B) :
    barHom hin b = QuotientGroup.mk (kOf hin b) := rfl

theorem barHom_eq_one_iff {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (b : ↥B) :
    barHom hin b = 1 ↔ (b : X) ∈ Subgroup.centralizer (L : Set X) := by
  rw [barHom_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have h1 := mem_centralizer_of_mem_center h
    have e : (b : X) = ((kOf hin b : ↥L) : X) * (((kOf hin b : ↥L) : X)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (kOf_spec hin b)
  · intro h
    apply mem_center_of_mem_centralizer
    have e : ((kOf hin b : ↥L) : X) = ((((kOf hin b : ↥L) : X))⁻¹ * b * (b : X)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (kOf_spec hin b) (Subgroup.inv_mem _ h))

theorem card_range_barHom_mul {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) :
    Nat.card (barHom hin).range * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) =
      Nat.card B := by
  have hker : (barHom hin).ker = (B ⊓ Subgroup.centralizer (L : Set X)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, barHom_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_mul_index (barHom hin).ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card (barHom hin).ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  rw [mul_comm]
  exact h1

theorem isElemAbelian_range_barHom {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) :
    IsElemAbelian p (barHom hin).range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun t ht => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : ↥L ⧸ Subgroup.center ↥L) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB a.2 b.2)
  · obtain ⟨a, rfl⟩ := ht
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using hB.2 a a.2)
    rw [this, map_one]

theorem range_barHom_le_centralizer {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (e : ↥B) :
    (barHom hin).range ≤ Subgroup.centralizer ({barHom hin e} : Set (↥L ⧸ Subgroup.center ↥L)) := by
  rintro _ ⟨b, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (isElemAbelian_commute hB b.2 e.2)

theorem exists_glaPComponent_barHom (hp : p.Prime) {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (e : ↥B)
    (hl : GLAPLayer p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) ≠ ⊥) :
    ∃ I : Subgroup (↥L ⧸ Subgroup.center ↥L),
      GLAPComponent p (Subgroup.centralizer ({barHom hin e} : Set (↥L ⧸ Subgroup.center ↥L))) I :=
  Inputs2711b.exists_glaPComponent_quot_of_inner hp (kOf hin e).2 (kOf_spec hin e) hl

end Bar

section Rank

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pow_pRank_mul_le (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) :
    p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≤
      Nat.card B := by
  obtain ⟨A₀, -, hA₀, hA₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥L)
  set A : Subgroup X := A₀.map L.subtype with hAdef
  have hA : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA₀ L.subtype
  have hAc : Nat.card A = p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    rw [hAdef, Subgroup.card_map_of_injective L.subtype_injective, hA₀c]
  have hAL : A ≤ L := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  set B₀ := B ⊓ Subgroup.centralizer (L : Set X) with hB₀
  have hB₀el : IsElemAbelian p B₀ := CFSG.Open.IsElemAbelian.mono hB inf_le_left
  have hAC : ∀ a ∈ A, ∀ c ∈ B₀, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a (hAL ha))
  have hdisj : ∀ x ∈ A, x ∈ B₀ → x = 1 := by
    intro x hxA hxB
    have hxZ : (⟨x, hAL hxA⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxB).2 y y.2
    have hxp : (⟨⟨x, hAL hxA⟩, hxZ⟩ : ↥(Subgroup.center ↥L)) ^ p = 1 :=
      Subtype.ext (Subtype.ext (hA.2 x hxA))
    have hord : orderOf (⟨⟨x, hAL hxA⟩, hxZ⟩ : ↥(Subgroup.center ↥L)) = 1 := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
      · exact h
      · exfalso
        apply hZL
        rw [← h]
        exact orderOf_dvd_natCard _
    have := orderOf_eq_one_iff.1 hord
    exact congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : X)) this
  obtain ⟨hPel, hPc⟩ := Inputs2711c.card_prodHom_range hA hB₀el hAC hdisj
  have hPle : (Inputs2711c.prodHom hAC).range ≤ B ⊔ L := by
    rintro _ ⟨x, rfl⟩
    rw [Inputs2711c.prodHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAL x.1.2))
      (Subgroup.mem_sup_left (Subgroup.mem_inf.1 x.2.2).1)
  have h1 := hmax _ hPle hPel
  rw [hPc, hAc] at h1
  exact h1

theorem exists_full_comp_quot (hp : p.Prime) {L B E : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1)
    (hle : ∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥)
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) :
    ∃ t : ↥L ⧸ Subgroup.center ↥L, t ≠ 1 ∧ t ^ p = 1 ∧
      p ^ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ∣
        Nat.card (Subgroup.centralizer ({t} : Set (↥L ⧸ Subgroup.center ↥L))) ∧
      ∃ I : Subgroup (↥L ⧸ Subgroup.center ↥L),
        GLAPComponent p (Subgroup.centralizer ({t} : Set (↥L ⧸ Subgroup.center ↥L))) I := by
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  set b : ↥B := ⟨e, hEB he⟩ with hb
  set R := (barHom hin).range with hR
  have hRel : IsElemAbelian p R := isElemAbelian_range_barHom hB hin
  refine ⟨barHom hin b, fun h => heC ((barHom_eq_one_iff hin b).1 h), ?_, ?_,
    exists_glaPComponent_barHom hp hin b (hle e he)⟩
  · exact hRel.2 _ ⟨b, rfl⟩
  · have hRB := card_range_barHom_mul hin
    have hle' := pow_pRank_mul_le hp hB hmax hZL
    have hB₀pos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := Nat.card_pos
    have h1 : p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ Nat.card R := by
      rw [← hRB] at hle'
      exact Nat.le_of_mul_le_mul_right hle' hB₀pos
    have h2 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd hp hZL
    have h3 : Nat.card R = p ^ CFSG.Open.pRank p R := Inputs27.card_eq_pow_pRank hp hRel
    have h4 : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ CFSG.Open.pRank p R := by
      have := (Nat.pow_le_pow_iff_right hp.one_lt).1 (h3 ▸ h1)
      omega
    have h5 : p ^ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ∣ Nat.card R :=
      h3 ▸ Nat.pow_dvd_pow p h4
    exact h5.trans (Subgroup.card_dvd_of_le (range_barHom_le_centralizer hB hin b))

theorem exists_full_comp (hp : p.Prime) {L B E : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1)
    (hle : ∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥)
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {Q : Type} [Group Q] [Finite Q]
    (σ : (↥L ⧸ Subgroup.center ↥L) ≃* Q) :
    ∃ x : Q, x ≠ 1 ∧ x ^ p = 1 ∧
      p ^ CFSG.Open.pRank p (⊤ : Subgroup Q) ∣ Nat.card (Subgroup.centralizer ({x} : Set Q)) ∧
      ∃ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) I := by
  obtain ⟨t, ht1, htp, hdvd, I, hI⟩ := exists_full_comp_quot hp hB hmax hin hEB hE2 hC1 hle hZL
  have hmap := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton σ t
  refine ⟨σ t, fun h => ht1 (σ.injective (h.trans (map_one σ).symm)), ?_, ?_, ?_⟩
  · rw [← map_pow, htp, map_one]
  · rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt σ, ← hmap,
      Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
    exact hdvd
  · refine ⟨I.map σ.toMonoidHom, ?_⟩
    rw [← hmap]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ hI

end Rank

section Multiplier

theorem not_dvd_card_center
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) {K : Type}
    [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {s : TauCeti.SporadicName}
    (hs : IsSporType s (K ⧸ Subgroup.center K)) {p : ℕ}
    (hp : ¬ p ∣ CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.sporadicMultiplierOrder s) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨e⟩ := hs
  exact fun h => hp (h.trans (CFSG.HardMathSupport.Dickson.I271.card_center_dvd_multiplier hSpM hq s e))

end Multiplier

section Conj

theorem centralizer_conj_pow {P : Type} [Group P] {c : P} (hc : c ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (k : P) :
    Subgroup.centralizer ({k * c ^ e * k⁻¹} : Set P) =
      (Subgroup.centralizer ({c} : Set P)).map (MulAut.conj k).toMonoidHom := by
  rw [← CFSG.Quasithin.Kleidman.centralizer_pow_eq hc he,
    CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton]
  rfl

end Conj

section Graded

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def DownStep (p : ℕ) (P P' : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → P S →
    ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S,
      GLAPComponent p (fixSubgroup α) I → P' (PSimple p I)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem typeQ_step_graded (hp : p.Prime) {P P' : ∀ (T : Type) [Group T], Prop}
    (hD : DownStep p P P') (hinv : Inputs2711c.IsoInv P') {X K : Subgroup G}
    (hK : GLAPComponent p X K) (hP : P (PSimple p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) {L : Subgroup G}
    (hL : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L) :
    P' (PSimple p L) := by
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hap' : IsPGroup p (Subgroup.zpowers a) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hap
  have hα : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha hap
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp ha hap' hL
  exact hinv _ _ e.symm
    (hD (PSimple p K) hsimple hnonab hP _ hα _ (glaPComponent_chevTransfer hp ha hap' hL))

theorem graded_mono {P : ℕ → ∀ (T : Type) [Group T], Prop} {k : ℕ}
    (hmono : ∀ n < k, ∀ (T : Type) [Group T], P n T → P (n + 1) T) {m n : ℕ} (hmn : m ≤ n)
    (hnk : n ≤ k) {T : Type} [Group T] (h : P m T) : P n T := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact h
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact hmono n (by omega) T (ih (by omega) (by omega))
    · have : m = n + 1 := by omega
      subst this
      exact h

theorem typeQ_core_graded (hp : p.Prime) (hp2 : p ≠ 2) {P : ℕ → ∀ (T : Type) [Group T], Prop}
    {k : ℕ} (hmono : ∀ n < k, ∀ (T : Type) [Group T], P n T → P (n + 1) T)
    (hstep : ∀ n < k, DownStep p (P n) (P (n + 1))) (hinv : ∀ n, Inputs2711c.IsoInv (P n))
    (h183 : Input18_3_4) {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K A : Subgroup Y} (hK : GLAPComponent p K K) (hP : P 0 (PSimple p K))
    (hA : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set Y)) (hKA : K ⊔ A = ⊤) :
    ∀ n ≤ k, ∀ (B : Subgroup Y), B ≤ A → Nat.card B ≤ p ^ n → ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer (B : Set Y)) J → P n (PSimple p J) := by
  have hbot : ∀ n ≤ k, ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer ((⊥ : Subgroup Y) : Set Y)) J →
        P n (PSimple p J) := by
    intro n hnk J hJ
    have e : K ⊓ Subgroup.centralizer (((⊥ : Subgroup Y) : Subgroup Y) : Set Y) = K := by
      refine inf_eq_left.2 fun k _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have : c = 1 := by simpa using hc
      rw [this, one_mul, mul_one]
    rw [e] at hJ
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
    obtain ⟨-, hall, -⟩ := glaPLayer_of_isQuasisimple (Y := K) hq
    have hJK : J = K := (hall J hJ).trans (hall K hK).symm
    exact hJK ▸ graded_mono hmono (Nat.zero_le n) hnk hP
  intro n
  induction n with
  | zero =>
    intro _ B _ hcard J hJ
    have hB1 : B = ⊥ := by
      rw [pow_zero] at hcard
      exact Subgroup.eq_bot_of_card_le B hcard
    subst hB1
    exact hbot 0 (Nat.zero_le k) J hJ
  | succ n ih =>
  intro hnk B hBA hcard J hJ
  by_cases hB1 : B = ⊥
  · subst hB1
    exact hbot (n + 1) hnk J hJ
  · obtain ⟨B₁, hB₁B, hidx, d, hdB, hdB₁⟩ :=
      Inputs2711c.exists_hyperplane' hp (isElemAbelian_mono hA hBA) hB1
    have hBel : IsElemAbelian p B := isElemAbelian_mono hA hBA
    have hB₁A : B₁ ≤ A := hB₁B.trans hBA
    have hcard₁ : Nat.card B₁ ≤ p ^ n := by
      have h1 := (B₁.subgroupOf B).card_mul_index
      rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁B).toEquiv] at h1
      rw [← h1, pow_succ] at hcard
      exact Nat.le_of_mul_le_mul_right hcard hp.pos
    have hX₁K : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (B₁ : Set Y)) :=
      hY.of_injective _ (Subgroup.centralizer (B₁ : Set Y)).subtype_injective
    have hBX₁ : B ≤ Subgroup.centralizer (B₁ : Set Y) := Inputs2711c.le_centralizer_of_elem hBel hB₁B
    have hCB : Subgroup.centralizer (B : Set Y) ≤ Subgroup.centralizer (B₁ : Set Y) :=
      Subgroup.centralizer_le hB₁B
    have hJC : GLAPComponent p (Subgroup.centralizer (B : Set Y)) J :=
      glaPComponent_of_isSubnormal' hp (Inputs2711c.centralizer_facts' hA hAK hKA hBA).2.2 hJ
    have hJ' : GLAPComponent p (Subgroup.centralizer (B₁ : Set Y) ⊓
        Subgroup.centralizer (B : Set Y)) J := by
      rwa [inf_eq_right.2 hCB]
    obtain ⟨𝒞, hcomp, hsup, hinv', htrans⟩ := h183 Y _ hX₁K p hp B hBX₁ hBel J hJ'
    have hCP : ∀ C ∈ 𝒞, P n (PSimple p C) := fun C hC =>
      ih (by omega) B₁ hB₁A hcard₁ C
        (Inputs2711c.pcomp_of_centralizer' hp hA hAK hKA hB₁A (hcomp C hC))
    have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
      rw [hsup]
      exact (gLBConj_one J).symm.le.trans (le_iSup₂
        (f := fun g (_ : g ∈ GLAPLayer p (Subgroup.centralizer (B₁ : Set Y))) => GLBConj g J)
        (1 : Y) (Subgroup.one_mem _))
    by_cases hdiag : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
    · have hcov := i183DiagAt_holds Y p hp hp2 B₁ B J 𝒞 hBel hB₁B hidx hX₁K hJC hcomp hsup hinv'
        htrans hdiag
      obtain ⟨C₁, hC₁, -⟩ := hdiag
      have hJC' : J ≤ C₁ ⊔ centModSubgroup p C₁ := hJle.trans (iSup₂_le fun C hC => by
        by_cases hCC : C = C₁
        · exact hCC ▸ le_sup_left
        · exact (le_centModSubgroup_of_ne hp (hcomp C hC) (hcomp C₁ hC₁) hCC).trans le_sup_right)
      obtain ⟨e⟩ := pSimple_equiv_of_diag hp (hcomp C₁ hC₁) hJC hJC' (hcov C₁ hC₁)
      exact hinv (n + 1) _ _ e.symm (hmono n (by omega) _ (hCP C₁ hC₁))
    · push Not at hdiag
      obtain ⟨C, hC⟩ : ∃ C, C ∈ 𝒞 := by
        by_contra h
        push Not at h
        have h0 : (⨆ C ∈ 𝒞, C) = ⊥ := by simp [h]
        rw [h0, le_bot_iff] at hJle
        exact glaPComponent_ne_bot' hJC hJle
      have hall : ∀ C' ∈ 𝒞, C' = C := fun C' hC' => hdiag C' hC' C hC
      have hJCC : J ≤ C := hJle.trans (iSup₂_le fun C' hC' => (hall C' hC').le)
      have hdN : d ∈ Subgroup.normalizer (C : Set Y) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        exact hall _ (hinv' C hC d hdB)
      have hBeq := Inputs2711c.eq_sup_zpowers' hp hB₁B hidx hdB hdB₁
      have hCeq : C ⊓ Subgroup.centralizer (B : Set Y) =
          C ⊓ Subgroup.centralizer ({d} : Set Y) := by
        refine le_antisymm (inf_le_inf_left C (Subgroup.centralizer_le (by simpa using hdB))) ?_
        intro y hy
        refine ⟨hy.1, ?_⟩
        have hyB₁ : y ∈ Subgroup.centralizer (B₁ : Set Y) := (hcomp C hC).1 hy.1
        have hle : B ≤ Subgroup.centralizer ({y} : Set Y) := by
          rw [← hBeq]
          refine sup_le (fun b hb => ?_) ?_
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hyB₁ b hb
          · rw [Subgroup.zpowers_le]
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm
        show y ∈ Subgroup.centralizer (B : Set Y)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
      have hJd : GLAPComponent p (C ⊓ Subgroup.centralizer ({d} : Set Y)) J := by
        have h1 : GLAPComponent p (C ⊓ Subgroup.centralizer (B : Set Y)) J :=
          glaPComponent_of_le hp hJC (le_inf hJCC hJC.1) inf_le_right
        rwa [hCeq] at h1
      exact typeQ_step_graded hp (hstep n (by omega)) (hinv (n + 1)) (hcomp C hC) (hCP C hC) hdN
        (hBel.2 d hdB) hJd

theorem typeClosure_graded (hp : p.Prime) (hp2 : p ≠ 2) {P : ℕ → ∀ (T : Type) [Group T], Prop}
    {k : ℕ} (hmono : ∀ n < k, ∀ (T : Type) [Group T], P n T → P (n + 1) T)
    (hstep : ∀ n < k, DownStep p (P n) (P (n + 1))) (hinv : ∀ n, Inputs2711c.IsoInv (P n))
    (h183 : Input18_3_4) {X K A : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hK : GLAPComponent p X K) (hP : P 0 (PSimple p K)) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hnk : n ≤ k) (hAn : Nat.card A ≤ p ^ n)
    {J : Subgroup G} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) :
    P n (PSimple p J) := by
  classical
  set H : Subgroup G := K ⊔ A with hH
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hHK : CFSG.Open.IsKGroup ↥H :=
    chevTools_isKGroup_sup hp hKX hAK (isPGroup_of_isElemAbelian hA)
  have hKK : GLAPComponent p K K := glaPComponent_of_le hp hK le_rfl hK.1
  have hK' : GLAPComponent p (K.subgroupOf H) (K.subgroupOf H) :=
    glaPComponent_subgroupOf hp hKH hKK
  obtain ⟨eK⟩ := Inputs2711c.pSimple_equiv_subgroupOf' p hKH
  have hP' : P 0 (PSimple p (K.subgroupOf H)) := hinv 0 _ _ eK hP
  have hA' : IsElemAbelian p (A.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (isElemAbelian_commute hA a.2 b.2))
    · exact Subtype.ext (by simpa using hA.2 (x : G) hx)
  have hAK' : A.subgroupOf H ≤ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hAK hx) (h : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hKA' : K.subgroupOf H ⊔ A.subgroupOf H = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup K A)
  have hJle : K ⊓ Subgroup.centralizer (A : Set G) ≤ H := inf_le_left.trans hKH
  have hJ1 := glaPComponent_subgroupOf hp hJle hJ
  have hcen : (Subgroup.centralizer (A : Set G)).subgroupOf H =
      Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_subgroupOf_inf_centralizer hAH,
      Subgroup.inf_subgroupOf_left]
  have hinf : (K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H =
      K.subgroupOf H ⊓ Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← hcen]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hinf] at hJ1
  have hAn' : Nat.card (A.subgroupOf H) ≤ p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
    exact hAn
  have hres := typeQ_core_graded hp hp2 hmono hstep hinv h183 (Y := ↥H) hHK hK' hP' hA' hAK' hKA'
    n hnk (A.subgroupOf H) le_rfl hAn' (J.subgroupOf H) hJ1
  obtain ⟨eJ⟩ := Inputs2711c.pSimple_equiv_subgroupOf' p (hJ.1.trans hJle)
  exact hinv n _ _ eJ.symm hres

end Graded

section BalanceSub

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem glaPComponent_le_glaPLayer_centralizer_sub (hp : p.Prime) (h183 : Input18_3_4)
    {K A D : Subgroup G} (hK : CFSG.Open.IsKGroup ↥K) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hDA : D ≤ A) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) :
    J ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (D : Set G)) := by
  have hApg : IsPGroup p A := isPGroup_of_isElemAbelian hA
  set H : Subgroup G := K ⊔ A with hH
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hAK
  have hHK : CFSG.Open.IsKGroup ↥H := chevTools_isKGroup_sup hp hK hAK hApg
  set X₁ : Subgroup G := H ⊓ Subgroup.centralizer (D : Set G) with hX₁
  have hX₁K : CFSG.Open.IsKGroup ↥X₁ := CFSG.Open.IsKGroup.of_le hHK inf_le_left
  have hAX₁ : A ≤ X₁ := le_inf le_sup_right (Inputs2711c.le_centralizer_of_elem hA hDA)
  have heq : X₁ ⊓ Subgroup.centralizer (A : Set G) = H ⊓ Subgroup.centralizer (A : Set G) := by
    rw [hX₁, inf_assoc, inf_eq_right.2 (Subgroup.centralizer_le hDA)]
  have hSX : K ⊓ Subgroup.centralizer (A : Set G) ≤ H ⊓ Subgroup.centralizer (A : Set G) :=
    inf_le_inf_right _ le_sup_left
  have hsub : IsSubnormal (K ⊓ Subgroup.centralizer (A : Set G))
      (H ⊓ Subgroup.centralizer (A : Set G)) :=
    IsSubnormal.step hSX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSX).2
        (chev_inf_centralizer_le_normalizer hHN A)) (IsSubnormal.refl _)
  have hJ' : GLAPComponent p (X₁ ⊓ Subgroup.centralizer (A : Set G)) J := by
    rw [heq]
    exact glaPComponent_of_isSubnormal' hp hsub hJ
  obtain ⟨𝒞, hcomp, hsup, -, -⟩ := h183 G X₁ hX₁K p hp A hAX₁ hA J hJ'
  have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
    rw [hsup]
    exact (gLBConj_one J).symm.le.trans (le_iSup₂
      (f := fun g (_ : g ∈ GLAPLayer p X₁) => GLBConj g J) (1 : G) (Subgroup.one_mem _))
  refine hJle.trans (iSup₂_le fun C hC => ?_)
  have hCK : C ≤ K := chevTools_perfect_le_of_sup hp hAK hApg ((hcomp C hC).1.trans inf_le_left)
    (glaPComponent_perfect (hcomp C hC))
  exact le_sSup (glaPComponent_of_le hp (hcomp C hC) (le_inf hCK ((hcomp C hC).1.trans inf_le_right))
    (inf_le_inf_right _ le_sup_left))

end BalanceSub

section TransferBar

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem subgroupOf_inf_centralizer_eq {L : Subgroup X} {k : X} (hk : k ∈ L) :
    (L ⊓ Subgroup.centralizer ({k} : Set X)).subgroupOf L =
      fixSubgroup (MulAut.conj (⟨k, hk⟩ : ↥L)) := by
  rw [Inputs1415.fixSubgroup_conj]
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨y.2, congrArg Subtype.val h⟩

theorem transfer_barHom (hp : p.Prime) {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (e : ↥B) {J : Subgroup X}
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J) :
    GLAPComponent p (Subgroup.centralizer ({barHom hin e} : Set (↥L ⧸ Subgroup.center ↥L)))
        ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      Nonempty (PSimple p J ≃*
        PSimple p ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) := by
  set k : ↥L := kOf hin e with hkdef
  rw [Inputs2711b.inf_centralizer_eq_of_inner (kOf_spec hin e)] at hJ
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJ' := glaPComponent_subgroupOf hp
    (inf_le_left : L ⊓ Subgroup.centralizer ({(k : X)} : Set X) ≤ L) hJ
  rw [subgroupOf_inf_centralizer_eq k.2] at hJ'
  obtain ⟨hI, ⟨eI⟩⟩ := Inputs1415.center_transfer hp _ hJ'
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj, Inputs1415.fixSubgroup_conj] at hI
  obtain ⟨e0⟩ := Inputs2711c.pSimple_equiv_subgroupOf' p hJL
  exact ⟨hI, ⟨e0.trans eI⟩⟩

theorem eq_of_transfer_barHom (hp : p.Prime) {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (e : ↥B)
    {J₁ J₂ : Subgroup X}
    (hJ₁ : GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J₁)
    (hJ₂ : GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J₂)
    (h : (J₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
      (J₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) : J₁ = J₂ := by
  have hJ₁L : J₁ ≤ L := hJ₁.1.trans inf_le_left
  have hJ₂L : J₂ ≤ L := hJ₂.1.trans inf_le_left
  have h₁ := glaPComponent_subgroupOf hp
    (inf_le_left : L ⊓ Subgroup.centralizer ({(e : X)} : Set X) ≤ L) hJ₁
  have h₂ := glaPComponent_subgroupOf hp
    (inf_le_left : L ⊓ Subgroup.centralizer ({(e : X)} : Set X) ≤ L) hJ₂
  have h3 : J₁.subgroupOf L = J₂.subgroupOf L :=
    glaPComponent_eq_of_map_eq_of_ker_le_center (QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.ker_mk' _).le h₁ h₂ h
  rw [← Subgroup.map_subgroupOf_eq_of_le hJ₁L, ← Subgroup.map_subgroupOf_eq_of_le hJ₂L, h3]

theorem pow_pRank_dvd_card_centralizer (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (b : ↥B) :
    p ^ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ∣
      Nat.card (Subgroup.centralizer ({barHom hin b} : Set (↥L ⧸ Subgroup.center ↥L))) := by
  set R := (barHom hin).range with hR
  have hRel : IsElemAbelian p R := isElemAbelian_range_barHom hB hin
  have hRB := card_range_barHom_mul hin
  have hle' := pow_pRank_mul_le hp hB hmax hZL
  have hB₀pos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := Nat.card_pos
  have h1 : p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ Nat.card R := by
    rw [← hRB] at hle'
    exact Nat.le_of_mul_le_mul_right hle' hB₀pos
  have h2 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd hp hZL
  have h3 : Nat.card R = p ^ CFSG.Open.pRank p R := Inputs27.card_eq_pow_pRank hp hRel
  have h4 : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ CFSG.Open.pRank p R := by
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 (h3 ▸ h1)
    omega
  have h5 : p ^ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ∣ Nat.card R :=
    h3 ▸ Nat.pow_dvd_pow p h4
  exact h5.trans (Subgroup.card_dvd_of_le (range_barHom_le_centralizer hB hin b))

theorem census_barHom (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {Q : Type} [Group Q] [Finite Q]
    (σ : (↥L ⧸ Subgroup.center ↥L) ≃* Q) {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : Inputs2711c.IsoInv Good)
    (hcen : ∀ x : Q, x ≠ 1 → x ^ p = 1 →
      p ^ CFSG.Open.pRank p (⊤ : Subgroup Q) ∣ Nat.card (Subgroup.centralizer ({x} : Set Q)) →
      (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) I →
        Good (PSimple p I)) ∧
      (∀ I I' : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) I →
        GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) I' → I = I'))
    (e : ↥B) (he : (e : X) ∉ Subgroup.centralizer (L : Set X)) :
    (∀ J : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J →
      Good (PSimple p J)) ∧
    (∀ J J' : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J →
      GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J' → J = J') := by
  set t := barHom hin e with ht
  have ht1 : σ t ≠ 1 := fun h =>
    he ((barHom_eq_one_iff hin e).1 (σ.injective (h.trans (map_one σ).symm)))
  have htp : σ t ^ p = 1 := by
    rw [← map_pow, (isElemAbelian_range_barHom hB hin).2 _ ⟨e, rfl⟩, map_one]
  have hmap := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton σ t
  have hdvd : p ^ CFSG.Open.pRank p (⊤ : Subgroup Q) ∣
      Nat.card (Subgroup.centralizer ({σ t} : Set Q)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt σ, ← hmap,
      Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
    exact pow_pRank_dvd_card_centralizer hp hB hmax hin hZL e
  obtain ⟨hG, hU⟩ := hcen (σ t) ht1 htp hdvd
  refine ⟨fun J hJ => ?_, fun J J' hJ hJ' => ?_⟩
  · obtain ⟨h1, ⟨e1⟩⟩ := transfer_barHom hp hin e hJ
    obtain ⟨h2, ⟨e2⟩⟩ := Inputs1415.comp_transport hp σ h1
    exact hGood _ _ (e1.trans e2).symm (hG _ h2)
  · obtain ⟨h1, -⟩ := transfer_barHom hp hin e hJ
    obtain ⟨h1', -⟩ := transfer_barHom hp hin e hJ'
    obtain ⟨h2, -⟩ := Inputs1415.comp_transport hp σ h1
    obtain ⟨h2', -⟩ := Inputs1415.comp_transport hp σ h1'
    have h3 := hU _ _ h2 h2'
    have h4 := Subgroup.map_injective (f := σ.toMonoidHom) σ.injective h3
    exact eq_of_transfer_barHom hp hin e hJ hJ' h4

end TransferBar

section UniqueClosure

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem typeClosure_of_unique (hp : p.Prime) (hp2 : p ≠ 2) {P : ∀ (T : Type) [Group T], Prop}
    (hD : Inputs2711c.DownClosed p P) (hinv : Inputs2711c.IsoInv P) (h183 : Input18_3_4)
    {L E : Subgroup G} (hLK : CFSG.Open.IsKGroup ↥L) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) {e : G} (he : e ∈ E)
    (hP : ∀ C : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C →
      P (PSimple p C))
    (huniq : ∀ C C' : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C →
      GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C' → C = C')
    {J : Subgroup G} (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J) :
    P (PSimple p J) := by
  have hEpg : IsPGroup p E := isPGroup_of_isElemAbelian hE
  set H : Subgroup G := L ⊔ E with hH
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hEN
  have hHK : CFSG.Open.IsKGroup ↥H := chevTools_isKGroup_sup hp hLK hEN hEpg
  set X₁ : Subgroup G := H ⊓ Subgroup.centralizer ({e} : Set G) with hX₁
  have hX₁K : CFSG.Open.IsKGroup ↥X₁ := CFSG.Open.IsKGroup.of_le hHK inf_le_left
  have heE : ({e} : Set G) ⊆ E := Set.singleton_subset_iff.2 he
  have hEX₁ : E ≤ X₁ := le_inf le_sup_right
    (Inputs2711c.le_centralizer_of_elem hE (Subgroup.zpowers_le.2 he) |>.trans
      (Subgroup.centralizer_le (by
        rw [Set.singleton_subset_iff]
        exact Subgroup.mem_zpowers e)))
  have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le heE
  have heq : X₁ ⊓ Subgroup.centralizer (E : Set G) = H ⊓ Subgroup.centralizer (E : Set G) := by
    rw [hX₁, inf_assoc, inf_eq_right.2 hCE]
  have hSX : L ⊓ Subgroup.centralizer (E : Set G) ≤ H ⊓ Subgroup.centralizer (E : Set G) :=
    inf_le_inf_right _ le_sup_left
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (E : Set G))
      (H ⊓ Subgroup.centralizer (E : Set G)) :=
    IsSubnormal.step hSX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSX).2
        (chev_inf_centralizer_le_normalizer hHN E)) (IsSubnormal.refl _)
  have hJ' : GLAPComponent p (X₁ ⊓ Subgroup.centralizer (E : Set G)) J := by
    rw [heq]
    exact glaPComponent_of_isSubnormal' hp hsub hJ
  obtain ⟨𝒞, hcomp, hsup, hinv', -⟩ := h183 G X₁ hX₁K p hp E hEX₁ hE J hJ'
  have hcompL : ∀ C ∈ 𝒞, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C := by
    intro C hC
    have hCL : C ≤ L := chevTools_perfect_le_of_sup hp hEN hEpg ((hcomp C hC).1.trans inf_le_left)
      (glaPComponent_perfect (hcomp C hC))
    exact glaPComponent_of_le hp (hcomp C hC) (le_inf hCL ((hcomp C hC).1.trans inf_le_right))
      (inf_le_inf_right _ le_sup_left)
  have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
    rw [hsup]
    exact (gLBConj_one J).symm.le.trans (le_iSup₂
      (f := fun g (_ : g ∈ GLAPLayer p X₁) => GLBConj g J) (1 : G) (Subgroup.one_mem _))
  obtain ⟨C, hC⟩ : ∃ C, C ∈ 𝒞 := by
    by_contra h
    push Not at h
    have h0 : (⨆ C ∈ 𝒞, C) = ⊥ := by simp [h]
    rw [h0, le_bot_iff] at hJle
    exact glaPComponent_ne_bot' hJ hJle
  have hall : ∀ C' ∈ 𝒞, C' = C := fun C' hC' => huniq C' C (hcompL C' hC') (hcompL C hC)
  have hJC : J ≤ C := hJle.trans (iSup₂_le fun C' hC' => (hall C' hC').le)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := by
    intro d hd
    rw [mem_normalizer_iff_gLBConj_eq]
    exact hall _ (hinv' C hC d hd)
  have hCL : C ≤ L := (hcompL C hC).1.trans inf_le_left
  have hJCE : GLAPComponent p (C ⊓ Subgroup.centralizer (E : Set G)) J :=
    glaPComponent_of_le hp hJ (le_inf hJC (hJ.1.trans inf_le_right)) (inf_le_inf_right _ hCL)
  have hXK : CFSG.Open.IsKGroup ↥(L ⊓ Subgroup.centralizer ({e} : Set G)) :=
    CFSG.Open.IsKGroup.of_le hLK inf_le_left
  exact Inputs2711c.typeClosure hp hp2 hD hinv h183 hXK (hcompL C hC) (hP C (hcompL C hC)) hE hEC
    hJCE

end UniqueClosure

section SieveD

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_card_sq (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) {x : X} (hx : x ∈ E) :
    ∃ D : Subgroup X, D ≤ E ∧ x ∈ D ∧ Nat.card D = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hE.2 x hx
  have h1 : Nat.card (Subgroup.zpowers x) ∣ p ^ 2 := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one hxp).trans (dvd_pow_self p (by norm_num))
  have h2 : p ^ 2 ∣ Nat.card E := by
    rw [Inputs27.card_eq_pow_pRank hp hE]
    exact Nat.pow_dvd_pow p hE2
  obtain ⟨D, hD, hxD, hDE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp h1 h2
    (Subgroup.zpowers_le.2 hx)
  exact ⟨D, hDE, hxD (Subgroup.mem_zpowers x), hD⟩


theorem exists_jD (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p 2)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) {name : TauCeti.SporadicName} (hpS : p ∣ sporOrd name)
    (h12 : ¬ sporOrd name ∣ Nat.factorial 12)
    {L B J0 E D : Subgroup X} (hLK : CFSG.IsKGroup ↥L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L))
    (hJ0 : CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X))) (hJt : Inputs2711c.J0Type p ↥J0) (hEB : E ≤ B)
    (hEl : GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥)
    (hDE : D ≤ E) (hD2r : 2 ≤ CFSG.Open.pRank p D)
    (hDC : ¬ D ≤ Subgroup.centralizer (L : Set X)) :
    ∃ J : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set X)) J ∧
      ((Inputs2711c.AltOrChevTwo (PSimple p J) ∧ ¬ sporOrd name ∣ Nat.card (PSimple p J)) ∨
        (Nat.card (PSimple p J) ∣ 720 ∨ Nat.card (PSimple p J) ∣ 20160 ∨
          Nat.card (PSimple p J) ∣ 25920 ∨ Nat.card (PSimple p J) ∣ 60)) := by
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    L ⊓ Subgroup.normalizer (U : Set X) with hΓ
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hEl
  have hΓL : Γ ≤ L := iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hJ0L : J0 ≤ L := hJ0.1.trans hΓL
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hJ0K : CFSG.Open.IsKGroup ↥J0 := CFSG.Open.IsKGroup.of_le hLK' hJ0L
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB hEB
  have hDel : IsElemAbelian p D := isElemAbelian_mono hEel hDE
  have hEN : E ≤ Subgroup.normalizer (J0 : Set X) :=
    Inputs2711c.le_normalizer_of_component hp hB hBN hJ0 hEB hJ
  have hJle := glaPComponent_le_glaPLayer_centralizer_sub hp h183 hJ0K hEel hEN hDE hJ
  have hlay : GLAPLayer p (J0 ⊓ Subgroup.centralizer (D : Set X)) ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hJle
    exact glaPComponent_ne_bot' hJ hJle
  obtain ⟨JD, hJD⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hlay
  have hJDL : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set X)) JD :=
    Inputs2711.glaPComponent_of_J0 hp (hDE.trans hEB) hD2r hJ0 hJD
  refine ⟨JD, hJDL, ?_⟩
  have hJDJ0 : JD ≤ J0 := hJD.1.trans inf_le_left
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hp.two_le
      obtain ⟨k, hk⟩ := h
      omega
  have hq0 : CFSG.Open.IsQuasisimple ↥J0 := hJ0.2.2
  have hdvd0 : Nat.card (PSimple p JD) ∣ Nat.card J0 :=
    (Inputs2711c.card_pSimple_dvd p JD).trans (Subgroup.card_dvd_of_le hJDJ0)
  rcases Inputs2711c.j0_trichotomy hp3 hq0 hJt with ⟨hZ, hA0⟩ | h720 | h20160 | h25920 | h60
  · left
    have eZ : (↥J0 ⧸ Subgroup.center ↥J0) ≃* ↥J0 :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    haveI hs0 : IsSimpleGroup ↥J0 := eZ.isSimpleGroup_congr.1 hq0.2
    have hnab0 : ∃ a b : ↥J0, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq0
      exact ⟨eZ a, eZ b, fun h => hab (eZ.injective (by rw [map_mul, map_mul, h]))⟩
    have hpJ0 : p ∣ Nat.card ↥J0 :=
      (Inputs2711c.dvd_card_pSimple hp hJD).trans hdvd0
    have hpJ0Z : p ∣ Nat.card (↥J0 ⧸ Subgroup.center ↥J0) := by
      rw [Nat.card_congr eZ.toEquiv]; exact hpJ0
    have hJ0J0 : GLAPComponent p J0 J0 :=
      S10.glaPComponent_of_quasisimple hp (IsSubnormal.refl J0) hq0 hpJ0Z
    obtain ⟨eP0⟩ := pSimple_equiv_of_surjective_simple hp hJ0J0 hnab0
      (Inputs2711c.glaPPrimeCore_eq_bot_of_simple hp hpJ0) (MonoidHom.id ↥J0) Function.surjective_id
    have hPJ0 : Inputs2711c.AltOrChevTwo (PSimple p J0) :=
      Inputs2711c.isoInv_altOrChevTwo _ _ eP0.symm hA0
    have hAJ : Inputs2711c.AltOrChevTwo (PSimple p JD) :=
      Inputs2711c.typeClosure hp hp2 (Inputs2711c.downClosed_altOrChevTwo hp hp2 hD2)
        Inputs2711c.isoInv_altOrChevTwo h183 hJ0K hJ0J0 hPJ0 hDel (hDE.trans hEN) hJD
    obtain ⟨eS⟩ := hname
    have hZ12 :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hLq name eS
    have hcardS : Nat.card (↥L ⧸ Subgroup.center ↥L) = sporOrd name :=
      (Nat.card_congr eS.toEquiv).trans (hOrd name)
    have hnotS : ¬ sporOrd name ∣ Nat.card (PSimple p JD) := by
      rw [← hcardS]
      exact Inputs2711c.not_dvd_card_pSimple_of_centralizer hLq hZ12 (by rw [hcardS]; exact h12)
        hDC hJDL
    exact ⟨hAJ, hnotS⟩
  · exact Or.inr (Or.inl (hdvd0.trans h720))
  · exact Or.inr (Or.inr (Or.inl (h20160 ▸ hdvd0)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h25920 ▸ hdvd0))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h60 ▸ hdvd0))))

end SieveD

section PairCo3

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.Sporadic.Schreier.Co3 (co3P co3PermEquiv)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (SporadicMultipliers)


theorem co3_constrained_XA (hXA : XA ∈ co3P) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({(⟨XA, hXA⟩ : ↥co3P)} : Set ↥co3P)) := by
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem co3_constrained_XB (hXB : XB ∈ co3P) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({(⟨XB, hXB⟩ : ↥co3P)} : Set ↥co3P)) := by
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem co3_card_centralizer_y :
    Nat.card (Subgroup.centralizer ({(⟨yPerm, yPerm_mem⟩ : ↥co3P)} : Set ↥co3P)) = 4536 := by
  obtain ⟨⟨hC, hCcard⟩, -⟩ := caseC_spec
  have h1 : Nat.card ↥(Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) = 4536 :=
    hC ▸ hCcard
  rw [← Subgroup.card_map_of_injective co3P.subtype_injective, map_centralizer_subtype']
  exact h1

theorem five_le_pRank_co3P : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥co3P) := by
  refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top (E := Dg.subgroupOf co3P) ?_ ?_
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (Dg_comm _ a.2 _ b.2))⟩⟩, fun x hx => ?_⟩
    exact Subtype.ext (by simpa using Dg_pow_three _ hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dg_le).toEquiv, card_Dg]
    norm_num

theorem false_of_co3P {x : ↥co3P} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hdvd : 3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set ↥co3P)))
    {I : Subgroup ↥co3P} (hI : GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co3P)) I) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : orderOf (x : Equiv.Perm (Fin 276)) = 3 := by
    have h1 : (x : Equiv.Perm (Fin 276)) ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    have h2 : (x : Equiv.Perm (Fin 276)) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨k, hk, c, hc, e, he, hcon⟩ := exists_conj_classes x.2 hs3
  obtain ⟨hXA3, -, hXAm, -⟩ := caseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := caseB_spec
  have key : ∀ (c' : ↥co3P), (c' : Equiv.Perm (Fin 276)) = c → c' ^ 3 = 1 →
      Subgroup.centralizer ({x} : Set ↥co3P) =
        (Subgroup.centralizer ({c'} : Set ↥co3P)).map (MulAut.conj (⟨k, hk⟩ : ↥co3P)).toMonoidHom := by
    intro c' hc' hc'3
    have hx : x = (⟨k, hk⟩ : ↥co3P) * c' ^ e * (⟨k, hk⟩ : ↥co3P)⁻¹ := by
      apply Subtype.ext
      rw [← hcon, ← hc']
      simp
    rw [hx]
    exact centralizer_conj_pow hc'3 he _
  rcases hc with rfl | rfl | rfl
  · have hcon' := pConstrainedShape_map (MulAut.conj (⟨k, hk⟩ : ↥co3P)) (co3_constrained_XA hXAm)
    rw [← key ⟨XA, hXAm⟩ rfl (Subtype.ext (by simpa using hXA3))] at hcon'
    exact no_glaPComponent_of_pConstrainedShape Nat.prime_three hcon' hI
  · have hcon' := pConstrainedShape_map (MulAut.conj (⟨k, hk⟩ : ↥co3P)) (co3_constrained_XB hXBm)
    rw [← key ⟨XB, hXBm⟩ rfl (Subtype.ext (by simpa using hXB3))] at hcon'
    exact no_glaPComponent_of_pConstrainedShape Nat.prime_three hcon' hI
  · rw [key ⟨yPerm, yPerm_mem⟩ rfl (Subtype.ext (by simpa using yPerm_pow)),
      Subgroup.card_map_of_injective (f := (MulAut.conj (⟨k, hk⟩ : ↥co3P)).toMonoidHom)
        (MulAut.conj (⟨k, hk⟩ : ↥co3P)).injective,
      co3_card_centralizer_y] at hdvd
    norm_num at hdvd

theorem sporPairCase_Co3_three (hSpM : SporadicMultipliers) (hBr : SporadicBridges) :
    Inputs2711c.SporPairCase .Co3 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hname hin J0 hJ0 hJt hJ5 E hEB hEC
    hEi hEl hE2 hlE hle
  exfalso
  have hZL : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
    not_dvd_card_center hSpM hLq hname (by decide)
  obtain ⟨eS⟩ := hname
  obtain ⟨bC⟩ := hBr .Co3
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥co3P :=
    (eS.trans bC.symm).trans (co3PermEquiv : CFSG.Blueprint.NativeSporadic.Co3 ≃* co3P)
  obtain ⟨x, hx1, hx3, hdvd, I, hI⟩ :=
    exists_full_comp hp hB hmax hin hEB hE2 hC1 hle hZL σ
  have h5 : 3 ^ 5 ∣ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥co3P) :=
    Nat.pow_dvd_pow 3 five_le_pRank_co3P
  exact false_of_co3P hx1 hx3 (h5.trans hdvd) hI

end PairCo3

section Orders

open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)

theorem not_altOrChevTwo_of_card (hb : LieOrderBridge) {T : Type} [Group T] [Finite T] {N : ℕ}
    (hT : Nat.card T = N) (a m m₀ : ℕ) (hN : N = 2 ^ a * m) (hm : Odd m) (h4 : 4 ^ a ≤ m)
    (hamb : N ≠ 60 ∧ N ≠ 168 ∧ N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 6048 ∧ N ≠ 20160 ∧ N ≠ 25920)
    (hm₀ : 2 ≤ m₀) (hM : ¬ m₀.factorial / 2 ∣ N) (hA : ∀ k < m₀, 2 ≤ k → k.factorial / 2 ≠ N) :
    ¬ Inputs2711c.AltOrChevTwo T := by
  rintro (h | h)
  · exact Inputs2711c.not_alt_of_card hT hm₀ hM hA h
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (hT.trans hN) hm h4
      (hN ▸ hamb) h

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem selfComp (hp : p.Prime) (hOrd : SporadicOrdersTable) {name : TauCeti.SporadicName}
    (hpS : p ∣ sporOrd name) {L : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L)) :
    GLAPComponent p L L ∧ Nonempty (PSimple p L ≃* (TauCeti.CFSGIndex.sporadic name).Group) := by
  obtain ⟨eS⟩ := hname
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  have hcardS : Nat.card (↥L ⧸ Subgroup.center ↥L) = sporOrd name :=
    (Nat.card_congr eS.toEquiv).trans (hOrd name)
  have hpLZ : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := hcardS ▸ hpS
  have hLL : GLAPComponent p L L :=
    S10.glaPComponent_of_quasisimple hp (IsSubnormal.refl L) hLq hpLZ
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq
  obtain ⟨ePL⟩ := pSimple_equiv_of_surjective_simple hp hLL hnab
    (Inputs2711c.glaPPrimeCore_eq_bot_of_simple hp hpLZ) (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _)
  exact ⟨hLL, ⟨ePL.trans eS⟩⟩

theorem pRank_eq_two (hp : p.Prime) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hc : Nat.card D = p ^ 2) : CFSG.Open.pRank p D = 2 := by
  have h := Inputs27.card_eq_pow_pRank hp hD
  rw [hc] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

end Orders

section PairM3

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)

@[expose] def FiGood (T : Type) [Group T] : Prop :=
  Nat.card T = 4952179814400 ∨ Nat.card T = 4245696

theorem fiGood_iso : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → FiGood T → FiGood T' := by
  intro T T' _ _ e h
  rw [FiGood, ← Nat.card_congr e.toEquiv]
  exact h

theorem centShapeRk_fi24_fiGood :
    CentShapeRk 3 FiGood (fun _ _ => True) (NativeSporadic.Carrier .Fi24Prime) := by
  haveI : Finite ↥CFSG.Sporadic.Fi24.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have e : NativeSporadic.Fi24prime ≃* ↥CFSG.Sporadic.Fi24.J := CFSG.Sporadic.Fi24.fi24EquivJ
  haveI : Finite NativeSporadic.Fi24prime := Finite.of_equiv _ e.symm.toEquiv
  have hN : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → Nat.card T = 4952179814400 →
      FiGood T := fun _ _ _ _ h => Or.inl h
  have hG2 : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → Nat.card T = 4245696 →
      FiGood T := fun _ _ _ _ h => Or.inr h
  have hJ := TabFi24.centShapeRk_J_good (Good := FiGood) fiGood_iso hN hG2
  exact CentShapeRk.of_equiv (Q := ↥CFSG.Sporadic.Fi24.J) (Q' := NativeSporadic.Fi24prime)
    Nat.prime_three fiGood_iso (fun _ _ _ _ _ h => h) e.symm hJ

@[expose] def PMZero (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .M).Group)

@[expose] def PMOne (T : Type) [Group T] : Prop :=
  PMZero T ∨ Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) ∨
    Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Th).Group)

@[expose] def PMTwo (T : Type) [Group T] : Prop :=
  PMOne T ∨ Inputs2711c.PTh T ∨ FiGood T

@[expose] def PMLevel : ℕ → ∀ (T : Type) [Group T], Prop
  | 0 => PMZero
  | 1 => PMOne
  | _ => PMTwo

theorem isoInv_PMZero : Inputs2711c.IsoInv PMZero := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isoInv_PMOne : Inputs2711c.IsoInv PMOne := by
  intro T T' _ _ e h
  rcases h with h | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl (isoInv_PMZero T T' e h)
  · exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr ⟨e.symm.trans f⟩)

theorem isoInv_PMTwo : Inputs2711c.IsoInv PMTwo := by
  intro T T' _ _ e h
  rcases h with h | h | h
  · exact Or.inl (isoInv_PMOne T T' e h)
  · exact Or.inr (Or.inl (Inputs2711c.isoInv_PTh T T' e h))
  · exact Or.inr (Or.inr (fiGood_iso T T' e h))

theorem isoInv_PMLevel : ∀ n, Inputs2711c.IsoInv (PMLevel n)
  | 0 => isoInv_PMZero
  | 1 => isoInv_PMOne
  | _ + 2 => isoInv_PMTwo

theorem mono_PMLevel : ∀ n < 2, ∀ (T : Type) [Group T], PMLevel n T → PMLevel (n + 1) T := by
  intro n hn T _ h
  interval_cases n
  · exact Or.inl h
  · exact Or.inl h

theorem downStep_M (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hcen : PCompCensus 3 (NativeSporadic.Carrier .M)
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    {P : ∀ (T : Type) [Group T], Prop} (hinv : Inputs2711c.IsoInv P)
    (hPM : P (TauCeti.CFSGIndex.sporadic .M).Group) (hPO : ∀ (T : Type) [Group T], PMOne T → P T)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hS : PMZero S) (α : MulAut S) (hα : α ^ 3 = 1) (I : Subgroup S)
    (hI : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I) :
    P (PSimple 3 I) := by
  obtain ⟨bM⟩ := hBr .M
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv _ (hS.some.trans bM.symm).toEquiv
  exact Inputs2711c.pSimple_of_sporCensus Nat.prime_three (by norm_num) hOut bM
    (Good := fun T _ => CFSG.Yardstones.Md0ec50421ce4.catalogIs T
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e h) hcen hinv
    hPM (fun T _ ⟨i, hi, hf⟩ => hPO T (by
      rcases hi with rfl | rfl
      · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr hf))) hnab hS α hα I hI

theorem downStep_PMZero (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hcen : PCompCensus 3 (NativeSporadic.Carrier .M)
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th)) :
    DownStep 3 PMZero PMOne := by
  intro S _ _ hs hnab hP α hα I hI
  exact downStep_M hOut hBr hcen isoInv_PMOne (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ h => h) hnab hP
    α hα I hI


theorem downStep_PMOne (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3)
    (hcen : PCompCensus 3 (NativeSporadic.Carrier .M)
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (hFi : CentShapeRk 3 FiGood (fun _ _ => True) (NativeSporadic.Carrier .Fi24Prime)) :
    DownStep 3 PMOne PMTwo := by
  intro S _ _ hs hnab hP α hα I hI
  rcases hP with hM | hF | hT
  · exact downStep_M hOut hBr hcen isoInv_PMTwo (Or.inl (Or.inl ⟨MulEquiv.refl _⟩))
      (fun _ _ h => Or.inl h) hnab hM α hα I hI
  · obtain ⟨bF⟩ := hBr .Fi24Prime
    haveI : Finite (NativeSporadic.Carrier .Fi24Prime) :=
      Finite.of_equiv _ (hF.some.trans bF.symm).toEquiv
    exact Inputs2711c.pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bF fiGood_iso
      (fun _ _ _ _ _ h => h) hFi isoInv_PMTwo (Or.inl (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)))
      (fun _ _ h => Or.inr (Or.inr h)) hnab hF α hα I hI
  · exact Or.inr (Or.inl (Inputs2711c.downClosed_PTh hOut hBr hKD S hs hnab (Or.inl hT) α hα I hI))

theorem dvd_card_of_PMTwo (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PMTwo T) : 4245696 ∣ Nat.card T := by
  rcases h with ((⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩) | h | h | h)
  · rw [Nat.card_congr f.toEquiv, hOrd .M]
    simp only [sporOrd, CFSG.Open.orderMonster]
    norm_num
  · rw [Nat.card_congr f.toEquiv, hOrd .Fi24Prime]
    simp only [sporOrd, CFSG.Open.orderFi24Prime]
    norm_num
  · rw [Nat.card_congr f.toEquiv, hOrd .Th]
    simp only [sporOrd, CFSG.Open.orderTh]
    norm_num
  · exact Inputs2711c.dvd_card_of_PTh hOrd h
  · rw [h]; norm_num
  · rw [h]

theorem disj_PMTwo (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {T : Type} [Group T]
    [Finite T] (hP : PMTwo T) (hA : Inputs2711c.AltOrChevTwo T) (hnd : ¬ sporOrd .M ∣ Nat.card T) :
    False := by
  have hFi : ∀ {T : Type} [Group T] [Finite T], Nat.card T = 1255205709190661721292800 →
      ¬ Inputs2711c.AltOrChevTwo T := fun hT =>
    not_altOrChevTwo_of_card hb hT 21 598528723330813275 25 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide)
  have hTh : ∀ {T : Type} [Group T] [Finite T], Nat.card T = 90745943887872000 →
      ¬ Inputs2711c.AltOrChevTwo T := fun hT =>
    not_altOrChevTwo_of_card hb hT 15 2769346432125 20 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide)
  have hN : ∀ {T : Type} [Group T] [Finite T], Nat.card T = 4952179814400 →
      ¬ Inputs2711c.AltOrChevTwo T := fun hT =>
    not_altOrChevTwo_of_card hb hT 12 1209028275 16 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide)
  have hG : ∀ {T : Type} [Group T] [Finite T], Nat.card T = 4245696 →
      ¬ Inputs2711c.AltOrChevTwo T := fun hT =>
    not_altOrChevTwo_of_card hb hT 6 66339 11 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide)
  rcases hP with ((⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩) | (⟨⟨f⟩⟩ | ⟨⟨f⟩⟩) | h | h)
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .M])
  · exact hFi (by rw [Nat.card_congr f.toEquiv, hOrd .Fi24Prime]; rfl) hA
  · exact hTh (by rw [Nat.card_congr f.toEquiv, hOrd .Th]; rfl) hA
  · exact hTh (by rw [Nat.card_congr f.toEquiv, hOrd .Th]; rfl) hA
  · exact hG (leafType_three_of_equiv_adjointG2 f).2.2.2 hA
  · exact hN h hA
  · exact hG h hA


theorem sporPairCase_M_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hcen : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M) →
      PCompCensus 3 (NativeSporadic.Carrier .M)
        (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (hFi : CentShapeRk 3 FiGood (fun _ _ => True) (NativeSporadic.Carrier .Fi24Prime)) :
    Inputs2711c.SporPairCase .M 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ hC1 hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exfalso
  have hc := hcen (Inputs2711c.isKGroup_carrier hLK hname hBr)
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
  obtain ⟨D, hDE, heD, hDc⟩ := exists_card_sq hp hEel hE2 he
  have hDel : IsElemAbelian 3 D := isElemAbelian_mono hEel hDE
  have hD2r : 2 ≤ CFSG.Open.pRank 3 D := (pRank_eq_two hp hDel hDc).ge
  have hDC : ¬ D ≤ Subgroup.centralizer (L : Set X) := fun h => heC (h heD)
  have hpS : 3 ∣ sporOrd .M := by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num
  have h12 : ¬ sporOrd .M ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEl hDE hD2r hDC
  obtain ⟨hLL, ⟨ePL⟩⟩ := selfComp hp hOrd hpS hLq hname
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hT : PMLevel 2 (PSimple 3 J) :=
    typeClosure_graded hp hp2 (k := 2) mono_PMLevel
      (fun n hn => by
        interval_cases n
        · exact downStep_PMZero hOut hBr hc
        · exact downStep_PMOne hOut hBr hKD hc hFi)
      isoInv_PMLevel h183 hLK' hLL ⟨ePL⟩ hDel (hDE.trans (hEB.trans hBN)) le_rfl hDc.le hJL
  rcases hJ with ⟨hA, hnS⟩ | hsmall
  · exact disj_PMTwo hOrd hb hT hA hnS
  · have h1 := dvd_card_of_PMTwo hOrd hT
    rcases hsmall with h | h | h | h
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)

end PairM3

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711d

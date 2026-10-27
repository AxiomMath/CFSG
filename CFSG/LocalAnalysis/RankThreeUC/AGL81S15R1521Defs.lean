module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21c
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section Row1523

theorem normalizer_lift_eq_comap {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) :
    Subgroup.normalizer (L : Set X) = Subgroup.normalizer ((Ls.comap (toStar T) : Subgroup X) : Set X) := by
  have hcomap : Ls.comap (toStar T) = L ⊔ gnC T := (liftOf_central_ext hX hLs hL).2
  have key : ∀ (g : X) (A : Subgroup X), A.map (MulAut.conj g).toMonoidHom = A →
      g ∈ Subgroup.normalizer (A : Set X) := by
    intro g A h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have : y = x := by simpa using hyx'
      rwa [← this]
  ext t
  constructor
  · intro ht
    rw [hcomap]
    apply key
    rw [Subgroup.map_sup, liftOf_conj_aux1 ht]
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (gnC_normal T).conj_mem a ha t
    · intro hz
      exact ⟨t⁻¹ * z * t, by simpa [mul_assoc] using (gnC_normal T).conj_mem z hz t⁻¹, by
        show t * (t⁻¹ * z * t) * t⁻¹ = z; group⟩
  · intro ht
    have hφt : toStar T t ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 := Subgroup.mem_normalizer_iff.1 ht x
      have e1 : x ∈ Ls.comap (toStar T) ↔ (toStar T x) ∈ Ls := Iff.rfl
      have e2 : t * x * t⁻¹ ∈ Ls.comap (toStar T) ↔ toStar T t * toStar T x * (toStar T t)⁻¹ ∈ Ls := by
        show toStar T (t * x * t⁻¹) ∈ Ls ↔ _
        simp
      exact e1.symm.trans (h1.trans e2)
    exact key t L (liftOf_conj hX hLs hL t hφt)

end Row1523

section Row1521Defs

open KFactsSmall

structure AConfig {X : Type} [Group X] [Finite X] (T R A : Subgroup X) : Prop where
  elemAbelian : IsElemAbelian 3 A
  card_eq : Nat.card A = 9
  perm : Permutable A T
  core : R = pCoreOf 2 (A ⊔ T)
  maximal : IsMaxInvariantTwo A R
  solvable : Group.IsSolvable ↥(Subgroup.normalizer (R : Set X))
  quaternion : HasQ8 (autInduced T A)
  transitive : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    ∃ t ∈ T ⊓ Subgroup.normalizer (A : Set X), t * a * t⁻¹ = b

end Row1521Defs

section Row1521X

open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem AConfig.inf_eq_bot_or_le {T R A : Subgroup X} (hA : AConfig T R A) {K : Subgroup X}
    (hK : T ≤ Subgroup.normalizer (K : Set X)) : A ⊓ K = ⊥ ∨ A ≤ K := by
  by_cases h : A ⊓ K = ⊥
  · exact Or.inl h
  · right
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    have haA : (a : X) ∈ A := (Subgroup.mem_inf.1 a.2).1
    have haK : (a : X) ∈ K := (Subgroup.mem_inf.1 a.2).2
    have ha1 : (a : X) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]; exact K.one_mem
    · obtain ⟨t, ht, htab⟩ := hA.transitive a haA ha1 b hb hb1
      have htT : t ∈ T := (Subgroup.mem_inf.1 ht).1
      have := (Subgroup.mem_normalizer_iff.1 (hK htT) a).1 haK
      rw [← htab]
      exact this

structure LiftCtx (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X)
    (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X) : Prop where
  gn : GNSetting X T
  good : GNGood T T₁ T₂
  rank_odd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3
  comp : GNYComponent T T₁ T₂ Ls
  lift : LiftOf T L Ls

structure LiftCtxGen (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X)
    (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X) : Prop where
  gn : GNSetting X T
  good : GNGood T T₁ T₂
  rank_three : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3
  rank_L : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3
  comp : GNYComponent T T₁ T₂ Ls
  lift : LiftOf T L Ls

theorem LiftCtx.toGen {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) :
    LiftCtxGen X T T₁ T₂ Ls L :=
  ⟨hl.gn, hl.good, hl.rank_odd 3 Nat.prime_three (by norm_num),
    fun r hr hr2 => (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (hl.rank_odd r hr hr2),
    hl.comp, hl.lift⟩

@[expose] def LiftRankBound (G : Type) [Group G] [Finite G] (M T : Subgroup G)
    (T₁ T₂ : Subgroup ↥M) : Prop :=
  CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 ∧
    ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3

theorem LiftRankBound.liftCtxGen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hR : LiftRankBound G M T T₁ T₂)
    (hgn : GNSetting ↥M (T.subgroupOf M)) (hg : GNGood (T.subgroupOf M) T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls) :
    LiftCtxGen ↥M (T.subgroupOf M) T₁ T₂ Ls L :=
  ⟨hgn, hg, hR.1, fun r hr hr2 => hR.2 Ls L hLs hL r hr hr2, hLs, hL⟩

theorem liftRankBound_of_ctx2 {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : LiftRankBound G M T T₁ T₂ :=
  ⟨ctx.rank_odd 3 Nat.prime_three (by norm_num),
    fun _ _ _ _ r hr hr2 =>
      (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (ctx.rank_odd r hr hr2)⟩

@[expose] def Shape1515 (L : Subgroup X) : Prop :=
  L = Subgroup.normalClosure (L : Set X) ∨
    IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))) ∨
    (IsLThreeOfExp 1 ↥(barO2 L) ∧
      Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3)

structure AutData (J : Type) [Group J] (E T' : Subgroup (MulAut J)) : Prop where
  elemAbelian : IsElemAbelian 3 E
  card_eq : Nat.card E = 9
  pgroup : IsPGroup 2 T'
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut J) (innAut J)
  perm : Permutable E T'
  quaternion : HasQ8 (autInduced T' E)
  conj : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → IsConj x y

theorem permutable_map {N P : Type} [Group N] [Group P] (ρ : N →* P) {A T : Subgroup N}
    (h : Permutable A T) : Permutable (A.map ρ) (T.map ρ) := by
  unfold Permutable at h ⊢
  rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, h]

theorem map_inf_innAut_eq_bot {Y : Type} [Group Y] [Finite Y] (π : X →* Y) {Jn : Subgroup X}
    [hN : (Jn.map π).Normal] {A : Subgroup X}
    (h : A ⊓ (Jn ⊔ ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π).ker) = ⊥) :
    A.map ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π) ⊓ innAut ↥(Jn.map π) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨a, haA, rfl⟩, k, hk⟩
  obtain ⟨j, hj, hjk⟩ := k.2
  have hρj : ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π) j = MulAut.conj k := by
    ext n
    simp [MulAut.conjNormal_apply, MulAut.conj_apply, hjk]
  have hker : a * j⁻¹ ∈ ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρj, hk, mul_inv_cancel]
  have haJ : a ∈ Jn ⊔ ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π).ker := by
    have : a = (a * j⁻¹) * j := by group
    rw [this]
    exact Subgroup.mul_mem_sup hker hj |> fun h' => by simpa [sup_comm] using h'
  have : a ∈ A ⊓ (Jn ⊔ ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π).ker) := ⟨haA, haJ⟩
  rw [h, Subgroup.mem_bot] at this
  rw [this]
  simp

theorem ker_conjNormal_comp {Y : Type} [Group Y] (π : X →* Y) {K : Subgroup Y} [hN : K.Normal] :
    ((MulAut.conjNormal : Y →* MulAut ↥K).comp π).ker =
      (Subgroup.centralizer (K : Set Y)).comap π := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    MonoidHom.comp_apply]
  constructor
  · intro h k hk
    have := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : Y)) h
    simp [MulAut.conjNormal_apply] at this
    calc k * π x = (π x * k * (π x)⁻¹) * π x := by rw [this]
       _ = π x * k := by group
  · intro h
    ext ⟨k, hk⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    show π x * k * (π x)⁻¹ = k
    rw [mul_inv_eq_iff_eq_mul]
    exact (h k hk).symm

theorem false_of_autData_k21ab (k21b : K21b) {J : Type} [Group J] [Finite J]
    (hJ : CFSG.Open.IsQuasisimple J)
    (hty : Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 6)) ∨
      IsLThreeTwo (J ⧸ Subgroup.center J) ∨ IsLThreeTwoPower (J ⧸ Subgroup.center J))
    {E T' : Subgroup (MulAut J)} (h : AutData J E T') : False := by
  rcases hty with h6 | h3 | hp
  · exact K21a_holds J hJ (Or.inl h6) E T' h.card_eq h.sylow h.perm
  · exact K21a_holds J hJ (Or.inr h3) E T' h.card_eq h.sylow h.perm
  · exact k21b J hJ hp E T' h.elemAbelian h.card_eq h.pgroup h.sylow h.perm h.quaternion

theorem false_of_autData_k21c {J : Type} [Group J] [Finite J]
    (hty : Nonempty (J ≃* alternatingGroup (Fin 7)) ∨ IsLThreeTwoProd 2 J ∨ IsLThreeTwoProd 3 J)
    {E T' : Subgroup (MulAut J)} (h : AutData J E T') : False := by
  obtain ⟨x, hx, y, hy, hxo, hyo, hnc⟩ := K21c_holds J hty E h.elemAbelian h.card_eq
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxo; omega
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; omega
  exact hnc (h.conj x hx y hy hx1 hy1)

theorem commute_star_of_commute_barO2 {T : Subgroup X} (hX : GNSetting X T) {K A : Subgroup X}
    (h : ⁅barO2 K, barO2 A⁆ = ⊥) : ⁅gnImg T K, gnImg T A⁆ = ⊥ := by
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφ : ∀ B : Subgroup X, (barO2 B).map φ = gnImg T B := by
    intro B
    unfold barO2 gnImg
    rw [Subgroup.map_map]
    congr 1
  have h1 := congrArg (Subgroup.map φ) h
  rw [Subgroup.map_commutator, hφ, hφ, Subgroup.map_bot] at h1
  exact h1

structure K21dData (S : Type) [Group S] (N T' R E : Subgroup (MulAut S)) : Prop where
  inn_le : innAut S ≤ N
  le_N : T' ≤ N
  pgroup : IsPGroup 2 T'
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut S) (innAut S)
  R_le : R ≤ T'
  T_normalizes : T' ≤ Subgroup.normalizer (R : Set (MulAut S))
  core : R = CFSG.Open.pCoreOf 2 (N ⊓ Subgroup.normalizer (R : Set (MulAut S)))
  solvable : Group.IsSolvable ↥(N ⊓ Subgroup.normalizer (R : Set (MulAut S)))
  E_le : E ≤ N ⊓ Subgroup.normalizer (R : Set (MulAut S))
  elemAbelian : CFSG.Open.IsElemAbelian 3 E
  card_eq : Nat.card E = 9
  quaternion : HasQ8 (autInduced T' E)

theorem false_of_k21dData (k21d : K21d) {S : Type} [Group S] [Finite S] (hS : IsK21dGroup S)
    {N T' R E : Subgroup (MulAut S)} (h : K21dData S N T' R E) : False :=
  k21d S hS N T' R E h.inn_le h.le_N h.pgroup h.sylow h.R_le h.T_normalizes h.core h.solvable
    h.E_le h.elemAbelian h.card_eq h.quaternion

theorem primePower_p_eq_two_of_card {q : TauCeti.PrimePower} {n : ℕ} (hn : n = 2 ∨ n = 4)
    (hq : q.card = n) : q.p = 2 := by
  have h1 : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hp : q.p.Prime := q.prime_p
  have h2 : q.p ∣ n := by
    rw [← hq, h1]
    exact dvd_pow_self _ (by have := q.exponent_pos; omega)
  rcases hn with rfl | rfl
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  · have h4 : q.p ∣ 2 ^ 2 := by simpa using h2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)

theorem isClassicalTwoOrG2_of_isK21dGroup {S : Type} [Group S] (h : IsK21dGroup S) :
    IsClassicalTwoOrG2 S := by
  rcases h with ⟨d, Q, hcase, he⟩ | h5 | hU | ⟨n, hn, he⟩
  · rcases hcase with ⟨hQ, hd4⟩ | ⟨hc4, hd⟩
    · refine Or.inl ⟨d, ?_, he⟩
      rcases hd4 with hd | hd | hd | hd <;> (rw [hd]; exact hQ)
    · refine Or.inl ⟨d, ?_, he⟩
      rw [hd]
      exact primePower_p_eq_two_of_card (Or.inr rfl) hc4
  · obtain ⟨d, ⟨q, hq, hd⟩, e⟩ := h5
    refine Or.inl ⟨d, ?_, e⟩
    rw [hd]
    exact primePower_p_eq_two_of_card (Or.inl rfl) hq
  · obtain ⟨d, ⟨q, hq, hd⟩, e⟩ := hU
    exact Or.inr (Or.inr ⟨d, Or.inr ⟨q, hq, hd⟩, e⟩)
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), he⟩)
    · exact Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), he⟩)

theorem isClassicalTwoOrG2_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsClassicalTwoOrG2 Y') : IsClassicalTwoOrG2 Y := by
  rcases h with ⟨d, hd, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.trans e'⟩⟩)

theorem isClassicalTwoOrG2_quot_of_isK21dGroup {S : Type} [Group S] (h : IsK21dGroup S)
    (hZ : Subgroup.center S = ⊥) : IsClassicalTwoOrG2 (S ⧸ Subgroup.center S) :=
  isClassicalTwoOrG2_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    (isClassicalTwoOrG2_of_isK21dGroup h)

theorem isLThreeTwo_iff_isLThreeOfExp_one {S : Type} [Group S] :
    IsLThreeTwo S ↔ IsLThreeOfExp 1 S := by
  constructor
  · rintro ⟨d, ⟨q, hq, hd⟩, e⟩
    exact Or.inl ⟨rfl, d, q, hq, hd, e⟩
  · rintro (⟨-, d, q, hq, hd, e⟩ | ⟨h, -⟩)
    · exact ⟨d, ⟨q, hq, hd⟩, e⟩
    · omega

@[expose] def Case21 (T : Subgroup X) (L : Subgroup X) : Prop :=
  (L.Normal ∧ (Nonempty ((↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* alternatingGroup (Fin 6)) ∨
      IsLThreeTwo (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ∨
      IsLThreeTwoPower (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)))) ∨
    IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))) ∨
    (Nonempty (↥(gnImg T (Subgroup.normalClosure (L : Set X))) ≃* alternatingGroup (Fin 7)) ∨
      IsLThreeTwoProd 2 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) ∨
      IsLThreeTwoProd 3 ↥(gnImg T (Subgroup.normalClosure (L : Set X)))) ∨
    (L.Normal ∧ IsK21dGroup ↥(barO2 L) ∧ Subgroup.center ↥(barO2 L) = ⊥ ∧
      2 ≤ CFSG.Open.pRank 3 L)

end Row1521X

section Row1524

variable {X : Type} [Group X] [Finite X]

@[expose] def Small1522 (S : Type) [Group S] : Prop :=
  IsLThreeOfExp 1 S ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 8)) ∨ IsLinTwo 5 S ∨ IsUThreeThree S

theorem gnV_comm_exp_two {T : Subgroup X} (hX : GNSetting X T) :
    (∀ a ∈ gnV T, ∀ b ∈ gnV T, a * b = b * a) ∧ (∀ v ∈ gnV T, v ^ 2 = 1) := by
  have h := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  haveI := h.1
  refine ⟨fun a ha b hb => ?_, fun v hv => h.2 v hv⟩
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(gnV T)) ⟨b, hb⟩)

end Row1524

section Shared

theorem exists_elemAbelian_sq {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {H : Subgroup Y} (h : 2 ≤ CFSG.Open.pRank p H) :
    ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E₀, hE₀H, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ 2 ∣ Nat.card E₀ := by rw [hcard]; exact pow_dvd_pow p h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p hdvd
  haveI := hE₀.1
  have hcomm : ∀ a b : E₀, a * b = b * a := fun a b => mul_comm' a b
  have hKe : IsElemAbelian p K := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (hcomm _ _)
    · exact Subtype.ext (by simpa using hE₀.2 _ x.2)
  refine ⟨K.map E₀.subtype, (Subgroup.map_subtype_le K).trans hE₀H,
    CFSG.SectionRank.isElemAbelian_map hKe E₀.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]

theorem exists_maxTwoLocal_normalizer_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hTM : T ≤ M) (hT : IsPGroup 2 T) (hnot : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic) :
    ∃ H₀ : Subgroup G, rankThreeIsMaxTwoLocal H₀ ∧
      Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G) ≤ H₀ ∧ H₀ ≠ M := by
  obtain ⟨hTi'T, hchar'⟩ := map_subtype_characteristic hTM hle hchar
  have hne' : Ti.map M.subtype ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective Ti M.subtype_injective).mp h)
  have hN : IsTwoLocal (Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G)) :=
    ⟨Ti.map M.subtype, hne', hT.to_le hTi'T, rfl⟩
  obtain ⟨H₀, ⟨hH₀, hNH₀⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | IsTwoLocal K ∧
      Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G) ≤ K}
    (fun K => Nat.card K) (Set.toFinite _) ⟨_, hN, le_rfl⟩
  refine ⟨H₀, ⟨hH₀, fun H hH hH₀H => ?_⟩, hNH₀, ?_⟩
  · exact (Subgroup.eq_of_le_of_card_ge hH₀H (hmax H ⟨hH, hNH₀.trans hH₀H⟩)).symm
  · intro hEq
    apply hnot
    intro g hg
    have h1 := normalizer_le_normalizer_of_characteristic hTi'T hchar' hg
    rw [← hEq]
    exact hNH₀ h1

theorem map_subtype_normalizer_le {G : Type} [Group G] {M : Subgroup G} (Ti : Subgroup ↥M) :
    (Subgroup.normalizer (Ti : Set ↥M)).map M.subtype ≤
      Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx t).1 ht, by simp⟩
  · rintro ⟨t, ht, hth⟩
    have hinv := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Ti : Set ↥M)).inv_mem hx) t).1 ht
    refine ⟨x⁻¹ * t * x, by simpa [mul_assoc] using hinv, ?_⟩
    have : (x : G) * h * (x : G)⁻¹ = (t : G) := hth.symm
    show (x : G)⁻¹ * (t : G) * (x : G) = h
    rw [← this]
    group

end Shared

section Row1522

open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem gnC_le_normalizer_one {T T₁ T₂ : Subgroup X} (hg : GNGood T T₁ T₂) :
    gnC T ≤ Subgroup.normalizer (T₁ : Set X) := by
  intro c hc
  have h1 : T₁ ≤ gnV T := fun x hx => Subgroup.le_normalClosure (hg.pair.le_center hx)
  have h2 : gnC T ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.centralizer_le (fun x hx => h1 hx)
  exact Subgroup.centralizer_le_normalizer (T₁ : Set X) (h2 hc)

theorem gnA_le_map_normalizer_one {T T₁ T₂ : Subgroup X} (hg : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls) :
    gnA T T₁ Ls ≤ (Subgroup.normalizer (T₁ : Set X) ⊓ L).map (toStar T) := by
  rintro y ⟨⟨n, hn, rfl⟩, hyLs⟩
  have hyL : (QuotientGroup.mk' (gnC T)) n ∈ L.map (toStar T) := by rw [hL.2]; exact hyLs
  obtain ⟨l, hl, hln⟩ := hyL
  refine ⟨l, ⟨?_, hl⟩, hln⟩
  have hc : n⁻¹ * l ∈ gnC T := by
    have : (QuotientGroup.mk' (gnC T)) n = (toStar T) l := hln.symm
    exact QuotientGroup.eq.1 this
  have hcN := gnC_le_normalizer_one hg hc
  have : l = n * (n⁻¹ * l) := by group
  rw [this]
  exact Subgroup.mul_mem _ hn hcN

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem primes_of_isAltSixCoverThree {S : Type} [Group S] [Finite S] (h : IsAltSixCoverThree S)
    {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S) : p = 2 ∨ p = 3 ∨ p = 5 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have h1080 : Nat.card S = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S),
      Nat.card_congr e.toEquiv, card_alternatingGroup_six, hZ]
  rw [h1080] at hpS
  have h2 : (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 := by norm_num
  rw [h2] at hpS
  rcases (Nat.Prime.dvd_mul hp).1 hpS with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
  · right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h

def piFinTwoMulEquiv (S : Type) [Group S] : (Fin 2 → S) ≃* S × S where
  toFun f := (f 0, f 1)
  invFun p := ![p.1, p.2]
  left_inv f := by ext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

def piFinThreeMulEquiv (S : Type) [Group S] : (Fin 3 → S) ≃* S × S × S where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by ext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

theorem isLThreeTwoSq_or_cube_of_prod {J : Type} [Group J]
    (h : IsLThreeTwoProd 2 J ∨ IsLThreeTwoProd 3 J) : IsLThreeTwoSq J ∨ IsLThreeTwoCube J := by
  rcases h with ⟨S, hS, hL, ⟨e⟩⟩ | ⟨S, hS, hL, ⟨e⟩⟩
  · exact Or.inl ⟨S, hS, isLThreeTwo_iff_isLThreeOfExp_one.1 hL, ⟨e.trans (piFinTwoMulEquiv S)⟩⟩
  · exact Or.inr ⟨S, hS, isLThreeTwo_iff_isLThreeOfExp_one.1 hL, ⟨e.trans (piFinThreeMulEquiv S)⟩⟩

end Row1522

section Row1525

@[expose] def Big1525 (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* alternatingGroup (Fin 8)) ∨
    IsLinTwo 5 S ∨ IsUThreeThree S

theorem isL5Two_iff_isLinTwo_five {S : Type} [Group S] : IsL5Two S ↔ IsLinTwo 5 S := by
  constructor
  · rintro ⟨d, ⟨q, hq, hd⟩, e⟩
    have hq2 : q.p = 2 := by
      have h1 : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
      have hp : q.p.Prime := q.prime_p
      have h2 : q.p ∣ 2 := by
        rw [← hq, h1]
        exact dvd_pow_self _ (by have := q.exponent_pos; omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    exact ⟨q, hq2, hq, d, hd, e⟩
  · rintro ⟨Q, hp, hc, d, hd, e⟩
    exact ⟨d, ⟨Q, hc, hd⟩, e⟩

end Row1525

end CFSG.LocalAnalysis.RankThreeUC.S15

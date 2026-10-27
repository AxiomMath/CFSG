module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift7
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barAut_mem_inner_of_pPrimePerfect {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L Q : Subgroup G} (hout : Nat.card (Outer (PQuot p L)) ≤ 2) (hQ : S10.PPrimePerfect p Q)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G)) {q : G} (hq : q ∈ Q) :
    barAut p L ⟨q, hQN hq⟩ ∈ inner (PQuot p L) := by
  haveI : Finite (MulAut (PQuot p L)) := finite_mulAut
  set f : ↥Q →* Outer (PQuot p L) :=
    (QuotientGroup.mk' (inner (PQuot p L))).comp ((barAut p L).comp (Subgroup.inclusion hQN))
    with hf
  have hidx : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have hrange : Nat.card f.range ≤ 2 := (Subgroup.card_le_card_group _).trans hout
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hcop : Nat.Coprime f.ker.index p := by
    rw [hidx]
    interval_cases h : Nat.card f.range
    · exact Nat.coprime_one_left p
    · exact (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp2)
  set M : Subgroup G := f.ker.map Q.subtype with hM
  have hMQ : M ≤ Q := Subgroup.map_subtype_le _
  have hMsub : M.subgroupOf Q = f.ker :=
    Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
  have hMn : (M.subgroupOf Q).Normal := by
    rw [hMsub]
    exact f.normal_ker
  have hMidx : Nat.Coprime (M.relIndex Q) p := by
    show Nat.Coprime (M.subgroupOf Q).index p
    rw [hMsub]
    exact hcop
  have hMeq : M = Q := hQ M hMQ hMn hMidx
  have hqM : q ∈ M := hMeq ▸ hq
  obtain ⟨q', hq'k, hq'q⟩ := hqM
  have hq'eq : q' = ⟨q, hq⟩ := Subtype.ext hq'q
  rw [hq'eq] at hq'k
  exact (QuotientGroup.eq_one_iff _).1 hq'k

private theorem eq_bot_of_perfect_of_isPGroup' {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    [Finite Q] {R : Subgroup Q} (hR : IsPGroup p R) (hperf : ⁅R, R⁆ = R) : R = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries R).1 hR.isNilpotent
  have h : ∀ k, R.lowerCentralSeries k = R := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  rw [← h n, hn]

private theorem le_of_perfect_of_pow_mem {p : ℕ} [Fact p.Prime] {X N A Q : Subgroup G} (hNX : N ≤ X)
    (hn : (N.subgroupOf X).Normal) (hAX : A ≤ X) (hQA : Q ≤ A) (hQ : ⁅Q, Q⁆ = Q)
    (hA : ∀ a ∈ A, ∃ k : ℕ, a ^ (p ^ k) ∈ N) : Q ≤ N := by
  set mk : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' (N.subgroupOf X) with hmk
  set R : Subgroup (↥X ⧸ N.subgroupOf X) := (Q.subgroupOf X).map mk with hR
  have hRp : IsPGroup p R := by
    rintro ⟨_, ⟨q, hq, rfl⟩⟩
    obtain ⟨k, hk⟩ := hA q (hQA hq)
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hmk, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hk
  have hQX : Q ≤ X := hQA.trans hAX
  have hQsub : ⁅Q.subgroupOf X, Q.subgroupOf X⁆ = Q.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQX, hQ]
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hQsub]
  have hRbot : R = ⊥ := eq_bot_of_perfect_of_isPGroup' hRp hRperf
  intro q hq
  have h1 : mk ⟨q, hQX hq⟩ ∈ R := ⟨⟨q, hQX hq⟩, hq, rfl⟩
  rw [hRbot, Subgroup.mem_bot, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

private theorem exists_pow_eq_mul {L : Subgroup G} {c l : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) (n : ℕ) :
    ∃ l' ∈ L, (c * l) ^ n = c ^ n * l' := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hconj : c⁻¹ * l' * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcL) l').1 hl'
      simpa using this
    refine ⟨(c⁻¹ * l' * c) * l, L.mul_mem hconj hl, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem le_of_glaPComponent_of_le_cx {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    {L : Subgroup G} (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hout : Nat.card (Outer (PQuot p L)) ≤ 2)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (hLn : cx x ≤ Subgroup.normalizer (L : Set G)) {W Q : Subgroup G} (hW : W ≤ cx x)
    (hQ : GLAPComponent p W Q) : Q ≤ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQX : Q ≤ cx x := hQ.1.trans hW
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQX.trans hLn
  have hpp : S10.PPrimePerfect p Q := S10.pPrimePerfect_of_glaPComponent hQ
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hO
  set C : Subgroup G := centModSubgroup p L ⊓ cx x with hC
  have hLx : L ≤ cx x := hL.1
  have hQT : Q ≤ L ⊔ C := by
    intro q hq
    have hin := barAut_mem_inner_of_pPrimePerfect hp2 hout hpp hQN hq
    obtain ⟨k, hk⟩ := hin
    obtain ⟨l, rfl⟩ := pQuotHom_surjective p L k
    have hl : (l : G) ∈ L := l.2
    have hβl : barAut p L ⟨l, Subgroup.le_normalizer hl⟩ = barAut p L ⟨q, hQN hq⟩ := by
      rw [barAut_of_mem hl]
      exact hk
    have hgN : (l : G)⁻¹ * q ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hl)) (hQN hq)
    have hβ : barAut p L ⟨(l : G)⁻¹ * q, hgN⟩ = 1 := by
      have e : (⟨(l : G)⁻¹ * q, hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨l, Subgroup.le_normalizer hl⟩)⁻¹ * ⟨q, hQN hq⟩ := rfl
      rw [e, map_mul, map_inv, hβl, inv_mul_cancel]
    have hcm : CentMod p L ((l : G)⁻¹ * q) := (chev_barAut_eq_one_iff_centMod hgN).1 hβ
    have hgC : (l : G)⁻¹ * q ∈ C :=
      ⟨centMod_iff.1 hcm, (cx x).mul_mem ((cx x).inv_mem (hLx hl)) (hQX hq)⟩
    rw [show q = (l : G) * ((l : G)⁻¹ * q) by group]
    exact Subgroup.mul_mem_sup hl hgC
  have hOn : cx x ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p (cx x)
  have hOX : O ≤ cx x := Subgroup.map_subtype_le _
  have hNX : L ⊔ O ≤ cx x := sup_le hLx hOX
  have hNn : ((L ⊔ O).subgroupOf (cx x)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
    exact S8.L89.le_normalizer_sup' hLn hOn
  have hCX : C ≤ cx x := inf_le_right
  have hpow : ∀ a ∈ L ⊔ C, ∃ k : ℕ, a ^ (p ^ k) ∈ L ⊔ O := by
    intro a ha
    have ha' : a ∈ ((C ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C L (hCX.trans hLn)] at ha'
    obtain ⟨c, hc, l, hl, rfl⟩ := Set.mem_mul.1 ha'
    have hcC : c ∈ C := hc
    obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCoreOf_of_centMod hp hp2 hx hL hrk1 hcC.2
      (centMod_iff.2 hcC.1)
    obtain ⟨l', hl', he⟩ := exists_pow_eq_mul (hLn hcC.2) hl (p ^ k)
    refine ⟨k, ?_⟩
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hl')
  have hQLO : Q ≤ L ⊔ O :=
    le_of_perfect_of_pow_mem hNX hNn (sup_le hLx hCX) hQT (glaPComponent_perfect hQ) hpow
  have hOcop : Nat.Coprime (Nat.card O) p := by
    have h1 : Nat.card O = Nat.card (GLAPPrimeCore p ↥(cx x)) :=
      Subgroup.card_map_of_injective (cx x).subtype_injective
    rw [h1]
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(cx x))).symm
  exact le_of_pPrimePerfect_of_le_sup hpp hQN (hLx.trans hOn) hOcop hQLO

theorem card_outer_le_two
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {p : ℕ}
    (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {row : Row}
    (hrow : RowL row p L) (hc : row.center = 1) : Nat.card (Outer (PQuot p L)) ≤ 2 := by
  obtain ⟨-, hcat, hZ1⟩ := hrow
  have hZ : Subgroup.center (PQuot p L) = ⊥ := Subgroup.card_eq_one.1 (hZ1.trans hc)
  let eK : PQuot p L ≃* PSimple p L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  obtain ⟨hsimple, a, b, hab⟩ := chev_pSimple_simple_nonabelian hp hL
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  have hi' : i = .sporadic row.name := hi
  subst hi'
  haveI : IsSimpleGroup (PQuot p L) := eK.isSimpleGroup_congr.mpr hsimple
  refine hOut (PQuot p L) inferInstance ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩ row.name
    ⟨eK.trans f⟩
  have := congrArg eK h
  simpa using this

theorem SporCfgCore.hK6_sandwich
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {p : ℕ}
    {row : Row} (hc : row.center = 1) {x : G} {L : Subgroup G} (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (c : SporCfgCore G p x L row) :
    row = .ly ∨ (cfgK p x L c.D c.R ≤ GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ∧
      GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ≤
          cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p (cx x)) := by
  rcases c.hK6L with h | ⟨hKE, himg⟩
  · exact Or.inl h
  right
  have hp : p.Prime := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  have hp2 : p ≠ 2 := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  haveI : Fact p.Prime := ⟨hp⟩
  have hout := card_outer_le_two hOut hp hL hrow hc
  set W : Subgroup G := Subgroup.centralizer (c.D : Set G) ⊓
    Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G) with hWdef
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hO
  have hWX : W ≤ cx x := inf_le_left.trans (S8.L89.centralizer_le_cx_of_mem c.hD.2.2.2)
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := hWX.trans c.hLn
  have hWLn : ((L ⊓ W).subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro w hw
    exact S10.mem_normalizer_inf_of (hWL hw) (Subgroup.le_normalizer hw)
  have hEW : GLAPLayer p (L ⊓ W) ≤ GLAPLayer p W := by
    unfold GLAPLayer
    exact sSup_le fun J hJ => le_sSup
      (CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp inf_le_right
        hWLn hJ)
  have hEK : GLAPLayer p (L ⊓ W) ≤ cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p L := by
    intro e he
    have heL : e ∈ L := ((glaPLayer_le_self' _).trans inf_le_left) he
    have hmem : pQuotHom p L ⟨e, heL⟩ ∈ lImg p L (GLAPLayer p (L ⊓ W)) :=
      ⟨⟨e, heL⟩, he, rfl⟩
    rw [himg] at hmem
    obtain ⟨k, hk, hke⟩ := hmem
    have hk' : (k : G) ∈ cfgK p x L c.D c.R := hk
    have hko : (k : G)⁻¹ * e ∈ GLAPPrimeCoreOf p L := (pQuot_mk_eq_mk_iff k ⟨e, heL⟩).1 hke
    rw [show e = (k : G) * ((k : G)⁻¹ * e) by group]
    exact Subgroup.mul_mem_sup hk' hko
  have hOL : GLAPPrimeCoreOf p L ≤ O :=
    HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hL.2.1
  have hWK : GLAPLayer p W ≤ cfgK p x L c.D c.R ⊔ O := by
    have hle : GLAPLayer p W ≤ GLAPLayer p (L ⊓ W) := by
      unfold GLAPLayer
      refine sSup_le fun Q hQ => le_sSup ?_
      have hQL : Q ≤ L := le_of_glaPComponent_of_le_cx hp hp2 hx hL hout hrk1 c.hLn hWX hQ
      exact glaPComponent_of_le hp hQ (le_inf hQL hQ.1) inf_le_right
    exact hle.trans (hEK.trans (sup_le_sup_left hOL _))
  exact ⟨hKE.trans hEW, hWK⟩

theorem SporCfgCore.hK6_layer
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {p : ℕ}
    {row : Row} (hc : row.center = 1) {x : G} {L : Subgroup G} (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (c : SporCfgCore G p x L row) :
    row = .ly ∨ (cfgK p x L c.D c.R ≤ GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ∧
      GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ≤
          cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p (GLAPLayer p
            (Subgroup.centralizer (c.D : Set G) ⊓
              Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)))) := by
  rcases c.hK6_sandwich hOut hc hx hL hrow hrk1 with h | ⟨hKΛ, hΛKO⟩
  · exact Or.inl h
  right
  refine ⟨hKΛ, ?_⟩
  have hp : p.Prime := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  haveI : Fact p.Prime := ⟨hp⟩
  set Λ : Subgroup G := GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
    Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) with hΛdef
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hO
  have hΛX : Λ ≤ cx x :=
    (glaPLayer_le_self' _).trans (inf_le_left.trans (S8.L89.centralizer_le_cx_of_mem c.hD.2.2.2))
  have hON : cx x ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p (cx x)
  have hOcop : Nat.Coprime (Nat.card O) p := by
    have h1 : Nat.card O = Nat.card (GLAPPrimeCore p ↥(cx x)) :=
      Subgroup.card_map_of_injective (cx x).subtype_injective
    rw [h1]
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(cx x))).symm
  have hcore : Λ ⊓ O ≤ GLAPPrimeCoreOf p Λ := S10.inf_le_glaPPrimeCoreOf (hΛX.trans hON) hOcop
  intro y hy
  have hy' : y ∈ ((cfgK p x L c.D c.R ⊔ O : Subgroup G) : Set G) := hΛKO hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ O ((hKΛ.trans hΛX).trans hON)] at hy'
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hy'
  have hoΛ : o ∈ Λ := by
    have e : o = k⁻¹ * (k * o) := by group
    rw [e]
    exact Λ.mul_mem (Λ.inv_mem (hKΛ hk)) hy
  exact Subgroup.mul_mem_sup hk (hcore ⟨hoΛ, ho⟩)

end CFSG.LocalAnalysis.GLTheoremA.H301

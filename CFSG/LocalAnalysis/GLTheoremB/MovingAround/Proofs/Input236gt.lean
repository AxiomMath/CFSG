module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma116

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input236gt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section AltAut

theorem card_mulAut_alt {n : ℕ} (h5 : 5 ≤ n) (h6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6),
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem dvd_card_mulAut_six : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
  have hinj :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have h1 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h2 : Nat.card (Equiv.Perm (Fin 6)) =
      Nat.card (MulAut.conjNormal (H := alternatingGroup (Fin 6))).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← h1, h2]
  exact Subgroup.card_subgroup_dvd_card _

theorem mulAut_alt_eq_one {n p : ℕ} (hp : p.Prime) (h5 : 5 ≤ n) (hnp : n < p)
    (φ : MulAut (alternatingGroup (Fin n))) (hφ : φ ^ p = 1) : φ = 1 := by
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hφ) with h1 | hpo
  · exact orderOf_eq_one_iff.1 h1
  · exfalso
    have hc : p ∣ Nat.card (MulAut (alternatingGroup (Fin n))) := hpo ▸ orderOf_dvd_natCard φ
    by_cases h6 : n = 6
    · subst h6
      haveI := finite_mulAut (alternatingGroup (Fin 6))
      have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
      have hle :=
        CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
      obtain ⟨k, hk⟩ := dvd_card_mulAut_six
      rw [hk] at hc hle hpos
      rcases (Nat.Prime.dvd_mul hp).1 hc with h | h
      · have h720 : (720 : ℕ) = Nat.factorial 6 := by decide
        rw [h720, Nat.Prime.dvd_factorial hp] at h
        omega
      · have := Nat.le_of_dvd (by omega) h
        omega
    · rw [card_mulAut_alt h5 h6, Nat.Prime.dvd_factorial hp] at hc
      omega

variable {X : Type*} [Group X]

@[expose] def conjOn {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    MulAut K where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (x : K) : ((conjOn hg x : K) : X) = g * x * g⁻¹ :=
  rfl

theorem conjOn_pow {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) (m : ℕ)
    (x : K) : (((conjOn hg ^ m) x : K) : X) = g ^ m * x * (g ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, conjOn_apply, ih]
    group

theorem mem_centralizer_of_mem_normalizer {K : Subgroup X} {n p : ℕ} (hp : p.Prime) (h5 : 5 ≤ n)
    (hnp : n < p) (e : K ≃* alternatingGroup (Fin n)) {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) (hgp : g ^ p = 1) :
    g ∈ Subgroup.centralizer (K : Set X) := by
  have h1 : conjOn hg ^ p = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [conjOn_pow, hgp]
    simp
  have h2 : MulAut.congr e (conjOn hg) = 1 :=
    mulAut_alt_eq_one hp h5 hnp _ (by rw [← map_pow, h1, map_one])
  have h3 : conjOn hg = 1 := by
    have := congrArg (MulAut.congr e).symm h2
    rwa [MulEquiv.symm_apply_apply, map_one] at this
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h4 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) h3
  simp only [conjOn_apply, MulAut.one_apply] at h4
  calc k * g = g * k * g⁻¹ * g := by rw [h4]
    _ = g * k := by group

theorem five_le_of_isQuasisimple {K : Type*} [Group K] {n : ℕ} (hK : CFSG.Open.IsQuasisimple K)
    (e : K ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra h
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Nontrivial K := CFSG.ComponentClassification.Quasisimple.nontrivial hK
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial K
  rw [hK.1] at this
  exact lt_irrefl _ this

end AltAut

section Indep

variable {X : Type*} [Group X]

theorem mem_of_pow_mem {p : ℕ} (hp : p.Prime) {H : Subgroup X} {x : X} (hx : x ^ p = 1) {j : ℕ}
    (hj0 : 0 < j) (hjp : j < p) (hxj : x ^ j ∈ H) : x ∈ H := by
  have hcop : Nat.Coprime j p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := Nat.le_of_dvd hj0 h
      omega)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have h1 : x ^ (j * m) = x := by
    rw [← Nat.div_add_mod (j * m) p, hm, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  rw [← h1, pow_mul]
  exact Subgroup.pow_mem _ hxj m

theorem exists_indep [Finite X] {p : ℕ} (hp : p.Prime) {B S : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian p B) (hSB : S ≤ B) (hS : Nat.card S = p)
    (hB3 : p ^ 3 ≤ Nat.card B) :
    ∃ b1 ∈ B, ∃ b2 ∈ B, ∀ i j : ℕ, i < p → j < p → b1 ^ i * b2 ^ j ∈ S → i = 0 ∧ j = 0 := by
  have hp1 := hp.one_lt
  have hpp : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
  have hp2 : p * p < p ^ 3 := by
    calc p * p = p ^ 2 := (sq p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
  obtain ⟨b1, hb1B, hb1S⟩ : ∃ b1 ∈ B, b1 ∉ S := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show B ≤ S from hcon)
    omega
  have hcomm : S ≤ Subgroup.centralizer (Subgroup.zpowers b1 : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact elemAbelian_comm hB (Subgroup.zpow_mem _ hb1B z) (hSB hs)
  have hHcard : Nat.card ↥(S ⊔ Subgroup.zpowers b1) ≤ p * p := by
    have hsurj : Function.Surjective (fun q : S × Subgroup.zpowers b1 =>
        (⟨(q.1 : X) * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2)
          (Subgroup.mem_sup_right q.2.2)⟩ : ↥(S ⊔ Subgroup.zpowers b1))) := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm hx
      exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), rfl⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, hS, Nat.card_zpowers] at h1
    have h2 : orderOf b1 ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 b1 hb1B))
    calc Nat.card ↥(S ⊔ Subgroup.zpowers b1) ≤ p * orderOf b1 := h1
      _ ≤ p * p := Nat.mul_le_mul_left p h2
  obtain ⟨b2, hb2B, hb2H⟩ : ∃ b2 ∈ B, b2 ∉ S ⊔ Subgroup.zpowers b1 := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show B ≤ S ⊔ Subgroup.zpowers b1 from hcon)
    omega
  refine ⟨b1, hb1B, b2, hb2B, fun i j hi hj hmem => ?_⟩
  have hj0 : j = 0 := by
    by_contra hj0
    apply hb2H
    apply mem_of_pow_mem hp (hB.2 b2 hb2B) (Nat.pos_of_ne_zero hj0) hj
    have : b2 ^ j = (b1 ^ i)⁻¹ * (b1 ^ i * b2 ^ j) := by group
    rw [this]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers b1 i)))
      (Subgroup.mem_sup_left hmem)
  subst hj0
  refine ⟨?_, rfl⟩
  by_contra hi0
  apply hb1S
  rw [pow_zero, mul_one] at hmem
  exact mem_of_pow_mem hp (hB.2 b1 hb1B) (Nat.pos_of_ne_zero hi0) hi hmem

end Indep

section Diag

variable {X : Type*} [Group X]

def cj (b k : X) (i : ℕ) : X := (b ^ i)⁻¹ * k * b ^ i

def tail (b k : X) (m : ℕ) : X := ((List.range m).map fun i => cj b k (i + 1)).prod

def diag (b k : X) (m : ℕ) : X := k * tail b k m

theorem cj_mem {K : Subgroup X} {k : X} (hk : k ∈ K) (b : X) (i : ℕ) :
    cj b k i ∈ GLBConj (b ^ i) K := by
  rw [mem_gLBConj]
  simpa [cj, mul_assoc] using hk

theorem tail_succ (b k : X) (m : ℕ) : tail b k (m + 1) = tail b k m * cj b k (m + 1) := by
  simp [tail, List.range_succ]

theorem tail_succ' (b k : X) (m : ℕ) :
    tail b k (m + 1) = cj b k 1 * ((List.range m).map fun i => cj b k (i + 2)).prod := by
  rw [tail, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  rfl

theorem conj_tail (b k : X) (m : ℕ) :
    b⁻¹ * tail b k m * b = ((List.range m).map fun i => cj b k (i + 2)).prod := by
  have h : b⁻¹ * tail b k m * b = MulAut.conj b⁻¹ (tail b k m) := by
    rw [MulAut.conj_apply, inv_inv]
  rw [h, tail, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, MulAut.conj_apply, inv_inv, cj]
  group

theorem commute_diag {b k : X} {m : ℕ} (hb : b ^ (m + 1) = 1) (hk : Commute k (tail b k m)) :
    Commute b (diag b k m) := by
  have h1 : b⁻¹ * diag b k m * b = diag b k m := by
    calc b⁻¹ * diag b k m * b = (b⁻¹ * k * b) * (b⁻¹ * tail b k m * b) := by
          simp only [diag]
          group
      _ = cj b k 1 * ((List.range m).map fun i => cj b k (i + 2)).prod := by
          rw [conj_tail]
          simp [cj]
      _ = tail b k (m + 1) := (tail_succ' b k m).symm
      _ = tail b k m * k := by rw [tail_succ]; simp [cj, hb]
      _ = k * tail b k m := hk.eq.symm
      _ = diag b k m := rfl
  show b * diag b k m = diag b k m * b
  calc b * diag b k m = b * (b⁻¹ * diag b k m * b) := by rw [h1]
    _ = diag b k m * b := by group

theorem commute_tail_of_commute {s b k : X} (hb : Commute s b) (hk : Commute s k) (m : ℕ) :
    Commute s (tail b k m) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  exact ((hb.pow_right (i + 1)).inv_right.mul_right hk).mul_right (hb.pow_right (i + 1))

theorem commute_diag_of_commute {s b k : X} (hb : Commute s b) (hk : Commute s k) (m : ℕ) :
    Commute s (diag b k m) :=
  hk.mul_right (commute_tail_of_commute hb hk m)

theorem commutatorElement_mul_mul {k k' y1 y2 : X} (h1 : Commute y1 k') (h2 : Commute y1 y2)
    (h3 : Commute y2 k) : ⁅k * y1, k' * y2⁆ = ⁅k, k'⁆ := by
  have e1 : y1 * (k' * y2) = k' * y2 * y1 := (h1.mul_right h2).eq
  have e2 : y2 * k⁻¹ = k⁻¹ * y2 := h3.inv_right.eq
  rw [commutatorElement_def, commutatorElement_def]
  calc k * y1 * (k' * y2) * (k * y1)⁻¹ * (k' * y2)⁻¹
      = k * (y1 * (k' * y2)) * y1⁻¹ * k⁻¹ * y2⁻¹ * k'⁻¹ := by group
    _ = k * (k' * y2 * y1) * y1⁻¹ * k⁻¹ * y2⁻¹ * k'⁻¹ := by rw [e1]
    _ = k * k' * (y2 * k⁻¹) * y2⁻¹ * k'⁻¹ := by group
    _ = k * k' * (k⁻¹ * y2) * y2⁻¹ * k'⁻¹ := by rw [e2]
    _ = k * k' * k⁻¹ * k'⁻¹ := by group

theorem le_of_commutators {K H : Subgroup X} (hK : commutator K = ⊤)
    (h : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ H) : K ≤ H := by
  intro x hx
  have hx' : (⟨x, hx⟩ : K) ∈ commutator K := by
    rw [hK]
    exact Subgroup.mem_top _
  have hle : commutator K ≤ H.comap K.subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact h a a.2 b b.2
  exact hle hx'

end Diag

section Components

variable {X : Type*} [Group X]

theorem commute_of_mem_ne [Finite X] {L1 L2 : Subgroup X} (h1 : IsComponentOf L1 ⊤)
    (h2 : IsComponentOf L2 ⊤) (hne : L1 ≠ L2) {a c : X} (ha : a ∈ L1) (hc : c ∈ L2) :
    Commute a c := by
  have hbot := CFSG.ComponentClassification.LocalComponents.commute_of_ne L1 L2 h1 h2 hne
  have hmem : ⁅a, c⁆ ∈ ⁅L1, L2⁆ := Subgroup.commutator_mem_commutator ha hc
  rw [hbot, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

theorem isComponentOf_glbConj {K : Subgroup X} (hK : IsComponentOf K ⊤) (g : X) :
    IsComponentOf (GLBConj g K) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) K).2 hK

theorem glbConj_eq_of_eq {g h : X} {K : Subgroup X} (hgh : GLBConj g K = GLBConj h K) :
    GLBConj (h * g⁻¹) K = K := by
  have := congrArg (GLBConj g⁻¹) hgh
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
  exact this.symm

end Components

theorem input23_6gt_holds : Lemma116.Input23_6gt := by
  intro X _ _ p n hp _ hnp B K hB hB3 hK he hS
  obtain ⟨e⟩ := he
  have h5 : 5 ≤ n := five_le_of_isQuasisimple hK.2.2 e
  have hBel : CFSG.Open.IsElemAbelian p B := hB.2.1
  set S : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X)
  have hSB : S ≤ B := inf_le_left
  have hSC : S ≤ Subgroup.centralizer (K : Set X) := inf_le_right
  have hNS : ∀ g ∈ B, GLBConj g K = K → g ∈ S := by
    intro g hg hgK
    exact ⟨hg, mem_centralizer_of_mem_normalizer hp h5 hnp e
      (mem_normalizer_iff_gLBConj_eq.2 hgK) (hBel.2 g hg)⟩
  have hSK : ∀ s ∈ S, ∀ k ∈ K, Commute s k := by
    intro s hs k hk
    exact (Subgroup.mem_centralizer_iff.1 (hSC hs) k hk).symm
  by_cases hS2 : 2 ≤ CFSG.Open.pRank p S
  ·
    intro k hk
    refine normalizer_le_glbCore hSB hS2 ?_
    have h := Lemma116.mem_normalizer_closure_of_comm (S : Set X) k
      (fun s hs => (hSK s hs k hk).eq.symm)
    rwa [Subgroup.closure_eq] at h
  ·
    have hp1 : 1 < p := hp.one_lt
    have hSel : CFSG.Open.IsElemAbelian p S := isElemAbelian_mono hBel hSB
    have hScard : Nat.card S = p := by
      have h1 := Lemma116.card_eq_pow_pRank hp hSel
      have h2 : CFSG.Open.pRank p S ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at h1
        exact hS (Subgroup.eq_bot_of_card_eq S h1)
      have h3 : CFSG.Open.pRank p S = 1 := by omega
      rw [h1, h3, pow_one]
    have hBcard : p ^ 3 ≤ Nat.card B := by
      rw [Lemma116.card_eq_pow_pRank hp hBel]
      exact Nat.pow_le_pow_right hp.pos hB3
    obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
      obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS
      exact ⟨s, hs, fun h => hs1 (Subtype.ext h)⟩
    obtain ⟨b1, hb1B, b2, hb2B, hind⟩ := exists_indep hp hBel hSB hScard hBcard
    have hsp : s ^ p = 1 := hBel.2 s (hSB hsS)
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    have hpow1 : ∀ i, 0 < i → i < p → b1 ^ i ∉ S := fun i hi0 hi hmem =>
      absurd (hind i 0 hi (by omega) (by simpa using hmem)).1 (by omega)
    have hpow2 : ∀ j, 0 < j → j < p → b2 ^ j ∉ S := fun j hj0 hj hmem =>
      absurd (hind 0 j (by omega) hj (by simpa using hmem)).2 (by omega)
    have hKne : ∀ b ∈ B, (∀ i, 0 < i → i < p → b ^ i ∉ S) →
        ∀ i, 0 < i → i < p → GLBConj (b ^ i) K ≠ K := fun b hbB hbS i hi0 hi h =>
      hbS i hi0 hi (hNS _ (Subgroup.pow_mem _ hbB i) h)
    have hKne12 : ∀ i j, 0 < i → i < p → 0 < j → j < p →
        GLBConj (b1 ^ i) K ≠ GLBConj (b2 ^ j) K := by
      intro i j hi0 hi hj0 hj h
      have h1 := hNS _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hb2B j)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb1B i))) (glbConj_eq_of_eq h)
      have h2 : b2 ^ j * (b1 ^ i)⁻¹ = b1 ^ (p - i) * b2 ^ j := by
        have hinv : (b1 ^ i)⁻¹ = b1 ^ (p - i) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le hi.le, hBel.2 b1 hb1B]
        rw [hinv]
        exact elemAbelian_comm hBel (Subgroup.pow_mem _ hb2B j) (Subgroup.pow_mem _ hb1B _)
      rw [h2] at h1
      exact absurd (hind (p - i) j (by omega) hj h1).2 (by omega)
    have hfac : ∀ b k : X, k ∈ K → ∀ y ∈ (List.range m).map (fun i => cj b k (i + 1)),
        ∃ i, 0 < i ∧ i < p ∧ y ∈ GLBConj (b ^ i) K := by
      intro b k hk y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      rw [List.mem_range] at hi
      exact ⟨i + 1, by omega, by omega, cj_mem hk b (i + 1)⟩
    have hcommK : ∀ b : X, (∀ i, 0 < i → i < p → GLBConj (b ^ i) K ≠ K) →
        ∀ k ∈ K, ∀ k' ∈ K, Commute (tail b k m) k' := by
      intro b hb k hk k' hk'
      apply Commute.list_prod_left
      intro y hy
      obtain ⟨i, hi0, hi, hyK⟩ := hfac b k hk y hy
      exact commute_of_mem_ne (isComponentOf_glbConj hK _) hK (hb i hi0 hi) hyK hk'
    have hcomm12 : ∀ k ∈ K, ∀ k' ∈ K, Commute (tail b1 k m) (tail b2 k' m) := by
      intro k hk k' hk'
      apply Commute.list_prod_left
      intro y hy
      apply Commute.list_prod_right
      intro z hz
      obtain ⟨i, hi0, hi, hyK⟩ := hfac b1 k hk y hy
      obtain ⟨j, hj0, hj, hzK⟩ := hfac b2 k' hk' z hz
      exact commute_of_mem_ne (isComponentOf_glbConj hK _) (isComponentOf_glbConj hK _)
        (hKne12 i j hi0 hi hj0 hj) hyK hzK
    have hdiag : ∀ b ∈ B, (∀ i, 0 < i → i < p → b ^ i ∉ S) →
        ∀ k ∈ K, diag b k m ∈ CFSG.Open.GLBCore p 2 B := by
      intro b hbB hbS k hk
      have hbp : b ^ p = 1 := hBel.2 b hbB
      have hbp' : b ^ (m + 1) = 1 := by rw [← hm]; exact hbp
      have hb1 : b ≠ 1 := by
        intro h1
        apply hbS 1 (by omega) (by omega)
        rw [h1, one_pow]
        exact S.one_mem
      have hsb : Commute s b := elemAbelian_comm hBel (hSB hsS) hbB
      have hcd_b : Commute b (diag b k m) :=
        commute_diag hbp' (hcommK b (hKne b hbB hbS) k hk k hk).symm
      have hcd_s : Commute s (diag b k m) := commute_diag_of_commute hsb (hSK s hsS k hk) m
      have hD : Subgroup.closure ({s, b} : Set X) ≤ B := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h' | h'
        · rw [h']
          exact hSB hsS
        · rw [h']
          exact hbB
      have hDr : 2 ≤ CFSG.Open.pRank p (Subgroup.closure ({s, b} : Set X)) := by
        refine Lemma116.two_le_pRank_pair hp hsb.eq hsp hbp hs1 hb1 ?_
        intro i j hij
        have hbj : b ^ j = b ^ (j % p) := by
          conv_lhs => rw [← Nat.div_add_mod j p, pow_add, pow_mul, hbp, one_pow, one_mul]
        by_cases hj0 : j % p = 0
        · rw [hij, hbj, hj0, pow_zero]
        · exfalso
          apply hbS (j % p) (Nat.pos_of_ne_zero hj0) (Nat.mod_lt _ hp.pos)
          rw [← hbj, ← hij]
          exact Subgroup.pow_mem _ hsS i
      refine normalizer_le_glbCore hD hDr
        (Lemma116.mem_normalizer_closure_of_comm _ _ fun t ht => ?_)
      rcases ht with h' | h'
      · rw [h']
        exact hcd_s.eq.symm
      · rw [h']
        exact hcd_b.eq.symm
    have hΓ : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ CFSG.Open.GLBCore p 2 B := by
      intro k hk k' hk'
      have h1 := hdiag b1 hb1B hpow1 k hk
      have h2 := hdiag b2 hb2B hpow2 k' hk'
      have hc : ⁅diag b1 k m, diag b2 k' m⁆ = ⁅k, k'⁆ :=
        commutatorElement_mul_mul (hcommK b1 (hKne b1 hb1B hpow1) k hk k' hk')
          (hcomm12 k hk k' hk') (hcommK b2 (hKne b2 hb2B hpow2) k' hk' k hk)
      rw [← hc, commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    exact le_of_commutators hK.2.2.1 hΓ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input236gt

end

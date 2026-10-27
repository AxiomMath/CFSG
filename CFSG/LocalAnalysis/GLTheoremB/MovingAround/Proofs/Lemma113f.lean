module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped Pointwise

namespace Lemma113f

variable {G : Type} [Group G] [Finite G]

theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem card_mul_le_card_inf_mul {A B R : Subgroup G} (hA : A ≤ R) (hB : B ≤ R) :
    Nat.card A * Nat.card B ≤ Nat.card (A ⊓ B : Subgroup G) * Nat.card R := by
  have h1 : (A ⊓ B).relIndex R ≤ A.relIndex R * B.relIndex R := Subgroup.relIndex_inf_le
  have hA' : A.relIndex R * Nat.card A = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := A) (K := R)
    rwa [inf_eq_left.2 hA] at this
  have hB' : B.relIndex R * Nat.card B = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := B) (K := R)
    rwa [inf_eq_left.2 hB] at this
  have hAB' : (A ⊓ B).relIndex R * Nat.card (A ⊓ B : Subgroup G) = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := R)
    rwa [inf_eq_left.2 (inf_le_left.trans hA)] at this
  set i := A.relIndex R
  set j := B.relIndex R
  set k := (A ⊓ B).relIndex R
  set a := Nat.card A
  set b := Nat.card B
  set c := Nat.card (A ⊓ B : Subgroup G)
  set n := Nat.card R
  have hn : 0 < n := Nat.card_pos
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, zero_mul] at hAB'
      omega
    · exact h0
  have key : k * (a * b) ≤ k * (c * n) := by
    calc k * (a * b) ≤ (i * j) * (a * b) := Nat.mul_le_mul_right _ h1
      _ = (i * a) * (j * b) := by ring
      _ = n * n := by rw [hA', hB']
      _ = (k * c) * n := by rw [hAB']
      _ = k * (c * n) := by ring
  exact Nat.le_of_mul_le_mul_left key hkpos

theorem thompsonJ_eq_of_structure {R E Q0 R1 : Subgroup G}
    (hRcard : Nat.card R = 3 ^ 8) (hE : IsEkIn 3 4 R E)
    (hR1R : R1 ≤ R) (hR1card : Nat.card R1 = 3 ^ 6)
    (hΩ : ∀ x ∈ R1, x ^ 3 = 1 → x ∈ Q0)
    (hΩE : ∀ y ∈ R1 ⊔ E, y ^ 3 = 1 → y ∈ E)
    (hCQ0 : ∀ x ∈ R, (∀ q ∈ Q0, x * q = q * x) → x ∈ R1 ⊔ E)
    (hfix : ∀ x ∈ R, ∀ W : Subgroup G, W ≤ Q0 → 9 ≤ Nat.card W →
      (∀ w ∈ W, x * w = w * x) → ∀ q ∈ Q0, x * q = q * x) :
    thompsonJ 3 R = E ∧ CFSG.Open.pRank 3 R = 4 := by
  have key : ∀ E1 : Subgroup G, E1 ≤ R → IsElemAbelian 3 E1 → 3 ^ 4 ≤ Nat.card E1 → E1 ≤ E := by
    intro E1 hE1R hE1ab hE1card
    have hW9 : 9 ≤ Nat.card (E1 ⊓ R1 : Subgroup G) := by
      have hc := card_mul_le_card_inf_mul (A := E1) (B := R1) hE1R hR1R
      rw [hR1card, hRcard] at hc
      have h81 : 3 ^ 4 * 3 ^ 6 ≤ Nat.card E1 * 3 ^ 6 := Nat.mul_le_mul_right _ hE1card
      by_contra hlt
      push Not at hlt
      have hlt' : Nat.card (E1 ⊓ R1 : Subgroup G) ≤ 8 := by omega
      have : Nat.card (E1 ⊓ R1 : Subgroup G) * 3 ^ 8 ≤ 8 * 3 ^ 8 :=
        Nat.mul_le_mul_right _ hlt'
      norm_num at h81 this hc
      omega
    have hWQ0 : (E1 ⊓ R1 : Subgroup G) ≤ Q0 := fun w hw =>
      hΩ w (Subgroup.mem_inf.1 hw).2 (by
        have := hE1ab.2 w (Subgroup.mem_inf.1 hw).1
        exact this)
    intro x hx
    have hxR : x ∈ R := hE1R hx
    have hxc : ∀ q ∈ Q0, x * q = q * x := fun q hq =>
      hfix x hxR (E1 ⊓ R1 : Subgroup G) hWQ0 hW9
        (fun w hw => comm_of_isElemAbelian hE1ab hx (Subgroup.mem_inf.1 hw).1) q hq
    have hxRE : x ∈ R1 ⊔ E := hCQ0 x hxR hxc
    exact hΩE x hxRE (hE1ab.2 x hx)
  have hpR : CFSG.Open.pRank 3 R = 4 := by
    unfold CFSG.Open.pRank
    apply le_antisymm
    · apply csSup_le
      · exact ⟨4, E, hE.1, hE.2.1, hE.2.2⟩
      · rintro k ⟨E1, hE1R, hE1ab, hE1card⟩
        by_contra hk
        push Not at hk
        have h81 : 3 ^ 4 ≤ Nat.card E1 := by
          rw [hE1card]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : Nat.card E1 ≤ Nat.card E := Subgroup.card_le_of_le (key E1 hE1R hE1ab h81)
        rw [hE.2.2, hE1card] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
        omega
    · apply le_csSup
      · refine ⟨4, ?_⟩
        rintro k ⟨E1, hE1R, hE1ab, hE1card⟩
        by_contra hk
        push Not at hk
        have h81 : 3 ^ 4 ≤ Nat.card E1 := by
          rw [hE1card]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : Nat.card E1 ≤ Nat.card E := Subgroup.card_le_of_le (key E1 hE1R hE1ab h81)
        rw [hE.2.2, hE1card] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
        omega
      · exact ⟨E, hE.1, hE.2.1, hE.2.2⟩
  refine ⟨?_, hpR⟩
  unfold thompsonJ
  simp only [hpR]
  apply le_antisymm
  · refine iSup₂_le fun E' hE' => ?_
    exact key E' hE'.1 hE'.2.1 (le_of_eq hE'.2.2.symm)
  · exact le_iSup₂ (f := fun (E'' : Subgroup G) (_ : IsEkIn 3 4 R E'') => E'') E hE

theorem zmod3_pow_three_pow (y : ZMod 3) (m : ℕ) : y ^ (3 ^ m) = y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul, ih]
    exact ZMod.pow_card y

theorem mul_comm_of_normalizer_zpowers_three_pow {e x : G} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {m : ℕ} (hm : x ^ (3 ^ m) = 1) : x * e = e * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  obtain ⟨k, hk⟩ : ∃ k : ℤ, e ^ k = x * e * x⁻¹ :=
    Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_normalizer_iff.1 hx e).1 (Subgroup.mem_zpowers e))
  have hc : ∀ j : ℤ, x * e ^ j * x⁻¹ = (x * e * x⁻¹) ^ j := fun j => by
    have := map_zpow (MulAut.conj x) e j
    simpa [MulAut.conj_apply] using this
  have hpow : ∀ n : ℕ, x ^ n * e * (x ^ n)⁻¹ = e ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : x ^ (n + 1) * e * (x ^ (n + 1))⁻¹ = x * (x ^ n * e * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih, hc, ← hk, ← zpow_mul]
      congr 1
      rw [pow_succ']
  have hfix : e ^ (k ^ (3 ^ m)) = e := by
    have := hpow (3 ^ m)
    rw [hm] at this
    simpa using this.symm
  have hzp : e ^ (k ^ (3 ^ m) - 1) = 1 := by
    rw [zpow_sub, zpow_one, hfix, mul_inv_cancel]
  have hdvd1 : (3 : ℤ) ∣ k ^ (3 ^ m) - 1 := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := e)).2 hzp
    rw [hord] at h
    exact_mod_cast h
  have hk1 : (k : ZMod 3) = 1 := by
    have h0 : (((k ^ (3 ^ m) - 1 : ℤ)) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hdvd1)
    push_cast at h0
    rw [sub_eq_zero] at h0
    rw [zmod3_pow_three_pow] at h0
    exact h0
  have hdvd2 : (3 : ℤ) ∣ k - 1 := by
    have h0 : (((k - 1 : ℤ)) : ZMod 3) = 0 := by
      push_cast
      rw [hk1, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h0
  have hek : e ^ (k - 1) = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := e)).1 (by rw [hord]; exact_mod_cast hdvd2)
  have hek' : e ^ k = e := by
    have : k = (k - 1) + 1 := by ring
    rw [this, zpow_add, hek, one_mul, zpow_one]
  have hxe : x * e * x⁻¹ = e := by rw [← hk, hek']
  calc x * e = (x * e * x⁻¹) * x := by group
    _ = e * x := by rw [hxe]

theorem exists_sylow_three_eight_of_index {E Q : Subgroup G} {e : G}
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hQN : Q ≤ Subgroup.normalizer (E : Set G))
    (hQC : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q)
    (hQcard : Nat.card Q = 3 ^ 5)
    (hidx : Nat.card ↥(Subgroup.normalizer (E : Set G)) =
      27 * Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))) :
    ∃ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R ∧ Q ≤ R ∧
      Nat.card R = 3 ^ 8 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hN
  set S : Subgroup G := N ⊓ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)
    with hS
  set T : Subgroup G := N ⊓ Subgroup.centralizer ({e} : Set G) with hT
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    norm_num at hQcard
  have hQT : Q ≤ T := le_inf hQN hQC.1
  have hTS : T ≤ S := inf_le_inf_left _ (Lemma113b.centralizer_le_normalizer_zpowers' e)
  have hQT_syl : IsSylowIn 3 T Q :=
    ⟨hQT, hQC.2.1, fun R' hR'T hR'p hQR' => hQC.2.2 R' (hR'T.trans inf_le_right) hR'p hQR'⟩
  have hS3 : ∀ R' : Subgroup G, R' ≤ S → IsPGroup 3 ↥R' → R' ≤ T := by
    intro R' hR'S hR'p x hx
    obtain ⟨m, hm⟩ := hR'p ⟨x, hx⟩
    have hm' : x ^ (3 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hxS : x ∈ S := hR'S hx
    refine ⟨(Subgroup.mem_inf.1 hxS).1, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    rw [Set.mem_singleton_iff.1 hh]
    exact (mul_comm_of_normalizer_zpowers_three_pow he3 he1 (Subgroup.mem_inf.1 hxS).2 hm').symm
  have hQS : IsSylowIn 3 S Q :=
    ⟨hQT.trans hTS, hQC.2.1, fun R' hR'S hR'p hQR' =>
      hQT_syl.2.2 R' (hS3 R' hR'S hR'p) hR'p hQR'⟩
  obtain ⟨k1, hk1, hk1'⟩ := Lemma113c.isSylowIn_card_index hQS hQ0
  obtain ⟨R, hRsyl, hQR⟩ := Lemma113b.exists_sylowIn_above' hQN hQC.2.1
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hQ0
    rw [h] at hQR
    exact le_bot_iff.1 hQR
  obtain ⟨k2, hk2, hk2'⟩ := Lemma113c.isSylowIn_card_index hRsyl hR0
  have hN_eq : Nat.card N = 3 ^ 8 * k1 := by
    rw [hidx, hk1, hQcard]
    ring
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hRsyl.2.1
  have hj8 : j = 8 := by
    have h : 3 ^ j * k2 = 3 ^ 8 * k1 := by
      rw [← hj, ← hk2, hN_eq]
    exact Lemma113c.pow_three_eq_of_mul h hk2' hk1'
  exact ⟨R, hRsyl, hQR, by rw [hj, hj8]⟩

theorem mem_centBar_iff {p : ℕ} {X L : Subgroup G} {g : G} :
    g ∈ centBar p X L ↔ g ∈ X ∧ ∃ h : g ∈ Subgroup.normalizer (L : Set G),
      barAut p L ⟨g, h⟩ = 1 := by
  unfold centBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨n, hn, hng⟩, hX⟩
    subst hng
    exact ⟨hX, n.2, MonoidHom.mem_ker.1 hn⟩
  · rintro ⟨hX, h, hb⟩
    exact ⟨⟨⟨g, h⟩, MonoidHom.mem_ker.2 hb, rfl⟩, hX⟩

noncomputable def qBarHom {K Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (K : Set G)) :
    ↥Q →* MulAut (barOf 3 K) :=
  (barAut 3 K).comp
    { toFun := fun q => ⟨q.1, hQN q.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem card_le_mul_of_centBar {K Q : Subgroup G} (hKI : IsLTwoTwentySeven (barOf 3 K))
    (hQN : Q ≤ Subgroup.normalizer (K : Set G)) (hQ3 : IsPGroup 3 ↥Q) :
    Nat.card ↥Q ≤ Nat.card ↥(centBar 3 Q K) * 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hKI
  set f := qBarHom hQN with hf
  have hker : f.ker.map Q.subtype = centBar 3 Q K := by
    ext g
    rw [Subgroup.mem_map, mem_centBar_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hQN x.2, MonoidHom.mem_ker.1 hx⟩
    · rintro ⟨hX, h, hb⟩
      exact ⟨⟨g, hX⟩, MonoidHom.mem_ker.2 hb, rfl⟩
  have hkc : Nat.card ↥(centBar 3 Q K) = Nat.card ↥f.ker := by
    rw [← hker, Subgroup.card_map_of_injective Subtype.val_injective]
  have hfR : IsPGroup 3 ↥f.range := hQ3.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hP3 : IsPGroup 3 ↥(f.range.map (MulAut.congr e).toMonoidHom) := hfR.map _
  have hPc : Nat.card ↥(f.range.map (MulAut.congr e).toMonoidHom) = Nat.card ↥f.range :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have h81 := CFSG.RankThree.PartTwo.KFacts.card_le_of_isPGroup_three_mulAut_psl2_27 hP3
  have hR : Nat.card ↥f.range ≤ 81 := by
    rw [← hPc]
    exact h81
  rw [CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f, hkc]
  exact Nat.mul_le_mul_left _ hR

theorem three_pow_five_le_card_of_sup {M Q E A : Subgroup G} (hE : IsSCp 3 M E)
    (hA : IsSCp 3 M A) (hE4 : CFSG.Open.pRank 3 E = 4) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hEQ : E ≤ Q) (hAQ : A ≤ Q) (hQ3 : IsPGroup 3 ↥Q) : 3 ^ 5 ≤ Nat.card ↥Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA_le : E ⊔ A ≤ Q := sup_le hEQ hAQ
  have hAnot : ¬ A ≤ E := by
    intro hAE
    have hEA : E = A := hA.2.2 E hE.1 hE.2.1 hAE
    rw [hEA] at hE4
    omega
  have hne : E ⊔ A ≠ E := by
    intro h
    apply hAnot
    rw [← h]
    exact le_sup_right
  have hEcard : Nat.card E = 3 ^ 4 := by
    rw [l113_card_eq_pow_pRank hE.2.1, hE4]
  have hsup3 : IsPGroup 3 ↥(E ⊔ A) := hQ3.to_le hEA_le
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hsup3
  have hle : Nat.card ↥E ≤ Nat.card ↥(E ⊔ A) := Subgroup.card_le_of_le le_sup_left
  have hne' : Nat.card ↥E ≠ Nat.card ↥(E ⊔ A) := by
    intro hc
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hc.symm)).symm
  have hlt : 3 ^ 4 < 3 ^ j := by
    rw [← hEcard, ← hj]
    exact lt_of_le_of_ne hle hne'
  have h4 : 4 < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  calc 3 ^ 5 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card ↥(E ⊔ A) := hj.symm
    _ ≤ Nat.card ↥Q := Subgroup.card_le_of_le hEA_le

theorem card_Q_eq_of_centBar {M K Q E A : Subgroup G} (hE : IsSCp 3 M E) (hA : IsSCp 3 M A)
    (hE4 : CFSG.Open.pRank 3 E = 4) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hEQ : E ≤ Q) (hAQ : A ≤ Q) (hQ3 : IsPGroup 3 ↥Q)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) (hQN : Q ≤ Subgroup.normalizer (K : Set G))
    (hcent : Nat.card ↥(centBar 3 Q K) ≤ 3) : Nat.card ↥Q = 3 ^ 5 := by
  have h1 := card_le_mul_of_centBar hKI hQN hQ3
  have h2 := three_pow_five_le_card_of_sup hE hA hE4 hA3 hEQ hAQ hQ3
  have h3 : Nat.card ↥Q ≤ 3 ^ 5 := by
    calc Nat.card ↥Q ≤ Nat.card ↥(centBar 3 Q K) * 81 := h1
      _ ≤ 3 * 81 := Nat.mul_le_mul_right _ hcent
      _ = 3 ^ 5 := by norm_num
  exact le_antisymm h3 h2

theorem le_normalizer_of_eq_thompsonJ {E Q : Subgroup G} (hEJ : E = thompsonJ 3 Q) :
    Q ≤ Subgroup.normalizer (E : Set G) := by
  intro q hq
  have hqn : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
  apply mem_normalizer_of_GLBConj_eq
  rw [hEJ]
  exact GLBConj_thompsonJ_eq (p := 3) hqn

@[expose] def PieceC_Q1 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (_hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)),
    Nat.card ↥(centBar 3 Q K) ≤ 3

@[expose] def PieceC_SylCE : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (_hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)),
    IsSylowIn 3 (Subgroup.centralizer (E : Set G)) E

@[expose] def PieceC_Index : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (_hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)),
    Nat.card ↥(Subgroup.normalizer (E : Set G)) =
      27 * Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))

@[expose] def PieceC_R1 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (_hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    (R : Subgroup G), IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      Nat.card R = 3 ^ 8 →
      ∃ R1 : Subgroup G, R1 ≤ R ∧ Nat.card R1 = 3 ^ 6 ∧
        (∀ x ∈ R1, x ^ 3 = 1 → x ∈ Q ⊓ K) ∧
        (∀ y ∈ R1 ⊔ E, y ^ 3 = 1 → y ∈ E) ∧
        (∀ x ∈ R, (∀ q ∈ Q ⊓ K, x * q = q * x) → x ∈ R1 ⊔ E) ∧
        (∀ x ∈ R, ∀ W : Subgroup G, W ≤ Q ⊓ K → 9 ≤ Nat.card ↥W →
          (∀ w ∈ W, x * w = w * x) → ∀ q ∈ Q ⊓ K, x * q = q * x)

theorem pieceC_claims_of_inputs (hQ1 : PieceC_Q1) (hSyl : PieceC_SylCE) (hIdx : PieceC_Index)
    (hR1 : PieceC_R1) : Lemma113_ii_pieceC_Claims := by
  intro G _ _ m B M E A a e K Q h hA hB
  have hEJ : E = thompsonJ 3 Q := hA.2.2.2.2.2.1
  have hQC : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q := h.hQ.1
  have hQ3 : IsPGroup 3 ↥Q := hQC.2.1
  have hQN : Q ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_eq_thompsonJ hEJ
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQC.1.trans hA.2.2.1
  have hEQ : E ≤ Q := le_sup_left.trans h.hQ.2
  have hAQ : A ≤ Q := le_sup_right.trans h.hQ.2
  have hEsc : IsSCp 3 M E := h.pair.1.1.1.1
  have hAsc : IsSCp 3 M A := h.pair.1.2.1.1.1
  have he3 : e ^ 3 = 1 := hEsc.2.1.2 e (Subgroup.mem_inf.1 h.he.1).1
  have hG2 : Nat.card ↥Q = 3 ^ 5 :=
    card_Q_eq_of_centBar hEsc hAsc h.h4 h.h3 hEQ hAQ hQ3 h.hK.2 hQK (hQ1 h hA hB)
  refine ⟨hSyl h hA hB, hG2, exists_sylow_three_eight_of_index he3 h.he.2 hQN hQC hG2
    (hIdx h hA hB), ?_⟩
  intro R hR hQR hR8
  obtain ⟨R1, hR1R, hR1card, hΩ, hΩE, hCQ0, hfix⟩ := hR1 h hA hB R hR hQR hR8
  have hE : IsEkIn 3 4 R E := by
    refine ⟨hEQ.trans hQR, hEsc.2.1, ?_⟩
    rw [l113_card_eq_pow_pRank hEsc.2.1, h.h4]
  exact (thompsonJ_eq_of_structure hR8 hE hR1R hR1card hΩ hΩE hCQ0 hfix).1.symm

end Lemma113f

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

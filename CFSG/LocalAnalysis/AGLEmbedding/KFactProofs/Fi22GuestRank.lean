module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.Sporadic.Bridge.Fi22Surj
public import Certificates.Certificate9400

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Guest

open scoped Pointwise

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native

variable {G : Type*} [Group G]

theorem pow_eq_one_of_mem_closure {S : Set G} (hcomm : S.Pairwise Commute) {n : ℕ}
    (hS : ∀ s ∈ S, s ^ n = 1) : ∀ g ∈ Subgroup.closure S, g ^ n = 1 := by
  have := Subgroup.isMulCommutative_closure hcomm
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact one_pow n
  | mul x y hx hy hx' hy' =>
    rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, hx', hy', one_mul]
  | inv x hx hx' => rw [inv_pow, hx', inv_one]

theorem isElemAbelian_card_closure {e : Fin 4 → G} (hpow : ∀ i, e i ^ 3 = 1)
    (hcomm : ∀ i j, e i * e j = e j * e i)
    (hnt : ∀ v : Fin 4 → ZMod 3, v ≠ 0 →
      e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val * e 3 ^ (v 3).val ≠ 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure (Set.range e)) ∧
      Nat.card (Subgroup.closure (Set.range e)) = 3 ^ 4 := by
  have hrc : (Set.range e).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j
  have hcm : ∀ i j (m k : ℕ), Commute (e i ^ m) (e j ^ k) :=
    fun i j m k => Commute.pow_pow (hcomm i j) m k
  have hadd : ∀ i (a b : ZMod 3), e i ^ (a + b).val = e i ^ a.val * e i ^ b.val := by
    intro i a b
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hpow i), pow_add]
  let φ : (Fin 4 → ZMod 3) → G := fun v =>
    e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val * e 3 ^ (v 3).val
  have hφ : ∀ v w, φ (v + w) = φ v * φ w := by
    intro v w
    simp only [φ, Pi.add_apply, hadd]
    simp only [mul_assoc]
    rw [(hcm 3 0 _ _).left_comm, (hcm 2 0 _ _).left_comm, (hcm 1 0 _ _).left_comm,
      (hcm 3 1 _ _).left_comm, (hcm 2 1 _ _).left_comm, (hcm 3 2 _ _).left_comm]
  let Φ : Multiplicative (Fin 4 → ZMod 3) →* G :=
    MonoidHom.mk' (fun v => φ (Multiplicative.toAdd v)) fun v w => hφ _ _
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hne
    exact hnt (Multiplicative.toAdd v) (fun h => hne (by simpa using h)) hv
  have hrange : Φ.range = Subgroup.closure (Set.range e) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      show φ (Multiplicative.toAdd v) ∈ _
      simp only [φ]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_ <;>
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self _)) _
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
      show φ (Pi.single i 1) = e i
      have h1 : (1 : ZMod 3).val = 1 := rfl
      fin_cases i <;> simp [φ, h1]
  refine ⟨⟨?_, pow_eq_one_of_mem_closure hrc fun s ⟨i, hi⟩ => hi ▸ hpow i⟩, ?_⟩
  · exact Subgroup.isMulCommutative_closure hrc
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp

theorem one_le_pRank_zpowers [Finite G] {q : G} (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1) :
    1 ≤ CFSG.Open.pRank 5 (Subgroup.zpowers q) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf q = 5 := orderOf_eq_prime hq5 hq1
  have hmem : 1 ∈ {k | ∃ E : Subgroup G, E ≤ Subgroup.zpowers q ∧
      CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ k} := by
    refine ⟨Subgroup.zpowers q, le_rfl, ⟨inferInstance, ?_⟩, ?_⟩
    · rintro x ⟨k, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq5, one_zpow]
    · rw [Nat.card_zpowers, hord, pow_one]
  refine le_csSup ⟨Nat.card G, ?_⟩ hmem
  rintro k ⟨E, -, -, hE⟩
  have := E.card_le_card_group
  rw [hE] at this
  exact (Nat.lt_pow_self (by norm_num : 1 < 5)).le.trans this

structure GuestData {G : Type*} [Group G] (X Y : G) (q : ℕ → G) (e : Fin 4 → G) : Prop where
  X_pow : X ^ 5 = 1
  Y_pow : Y ^ 5 = 1
  XY_comm : X * Y = Y * X
  q_mem : ∀ j, q j ∈ Subgroup.closure ({X, Y} : Set G)
  e_mem : ∀ i, e i ∈ Subgroup.closure
    {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c}
  e_pow : ∀ i, e i ^ 3 = 1
  e_comm : ∀ i j, e i * e j = e j * e i
  e_ne : ∀ v : Fin 4 → ZMod 3, v ≠ 0 →
    e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val * e 3 ^ (v 3).val ≠ 1

theorem GuestData.map {H : Type*} [Group H] {X Y : G} {q : ℕ → G} {e : Fin 4 → G}
    (D : GuestData X Y q e) (ψ : G ≃* H) :
    GuestData (ψ X) (ψ Y) (fun j => ψ (q j)) (fun i => ψ (e i)) where
  X_pow := by rw [← map_pow, D.X_pow, map_one]
  Y_pow := by rw [← map_pow, D.Y_pow, map_one]
  XY_comm := by rw [← map_mul, ← map_mul, D.XY_comm]
  q_mem j := by
    have := Subgroup.mem_map_of_mem ψ.toMonoidHom (D.q_mem j)
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  e_mem i := by
    have := Subgroup.mem_map_of_mem ψ.toMonoidHom (D.e_mem i)
    rw [MonoidHom.map_closure] at this
    refine Subgroup.closure_mono ?_ this
    rintro _ ⟨m, ⟨j, c, hq, hm⟩, rfl⟩
    refine ⟨j, c, fun h => hq (ψ.injective (by simpa using h)), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hm, map_pow]
  e_pow i := by rw [← map_pow, D.e_pow, map_one]
  e_comm i j := by rw [← map_mul, ← map_mul, D.e_comm]
  e_ne v hv h := by
    refine D.e_ne v hv (ψ.injective ?_)
    rw [map_one, ← h]
    simp only [map_mul, map_pow]

theorem GuestData.pairwise_commute {X Y : G} (hXY : X * Y = Y * X) :
    ({X, Y} : Set G).Pairwise Commute := by
  rintro a (rfl | rfl) b (rfl | rfl) hab
  · exact absurd rfl hab
  · exact hXY
  · exact hXY.symm
  · exact absurd rfl hab

theorem GuestData.pow_five {X Y : G} {q : ℕ → G} {e : Fin 4 → G} (D : GuestData X Y q e) :
    ∀ g ∈ Subgroup.closure ({X, Y} : Set G), g ^ 5 = 1 :=
  pow_eq_one_of_mem_closure (GuestData.pairwise_commute D.XY_comm) <| by
    rintro s (rfl | rfl)
    exacts [D.X_pow, D.Y_pow]

theorem GuestData.exists_le_glbCore [Finite G] {X Y : G} {q : ℕ → G} {e : Fin 4 → G}
    (D : GuestData X Y q e) (T : Subgroup G) (hT : Subgroup.closure ({X, Y} : Set G) ≤ T) :
    ∃ E : Subgroup G, E ≤ CFSG.Open.GLBCore 5 1 T ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := by
  have hS : {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c} ⊆
      (CFSG.Open.GLBCore 5 1 T : Set G) := by
    rintro m ⟨j, c, hq1, hm⟩
    have hq5 : q j ^ 5 = 1 := D.pow_five _ (D.q_mem j)
    have hQ : Subgroup.zpowers (q j) ≤ T := (Subgroup.zpowers_le).2 (hT (D.q_mem j))
    have hN : m ∈ Subgroup.normalizer ((Subgroup.zpowers (q j) : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      refine Subgroup.mem_zpowers_iff.2 ⟨c * k, ?_⟩
      have h' : q j ^ (c : ℤ) = m * q j * m⁻¹ := by rw [zpow_natCast, hm]
      rw [zpow_mul, h', conj_zpow]
    have hmem : Subgroup.normalizer ((Subgroup.zpowers (q j) : Subgroup G) : Set G) ∈
        {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ T ∧ 1 ≤ CFSG.Open.pRank 5 Q ∧
          N = Subgroup.normalizer (Q : Set G)} :=
      ⟨Subgroup.zpowers (q j), hQ, one_le_pRank_zpowers hq5 hq1, rfl⟩
    exact le_sSup hmem hN
  refine ⟨Subgroup.closure (Set.range e), ?_, isElemAbelian_card_closure D.e_pow D.e_comm D.e_ne⟩
  exact ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 D.e_mem)).trans
    ((Subgroup.closure_le _).2 hS)

theorem GuestData.exists_of_sylow [Finite G] {X Y : G} {q : ℕ → G} {e : Fin 4 → G}
    (D : GuestData X Y q e) (T : Sylow 5 G) :
    ∃ E : Subgroup G, E ≤ CFSG.Open.GLBCore 5 1 (T : Subgroup G) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.closure ({X, Y} : Set G)) := fun g =>
    ⟨1, Subtype.ext (by simpa using D.pow_five g.1 g.2)⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  refine (D.map (MulAut.conj g)).exists_le_glbCore (T : Subgroup G) ?_
  rw [Subgroup.closure_le]
  have hT : (T : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  rintro _ (rfl | rfl)
  all_goals
    rw [hT]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS (Subgroup.subset_closure (by simp)))

section Soundness

variable {n : ℕ} [MulAction G (Fin n)]

theorem wordProd_append (g : ℕ → G) (u v : Word) :
    wordProd g (u ++ v) = wordProd g u * wordProd g v := by
  simp [wordProd]

theorem wordProd_wpow (g : ℕ → G) (w : Word) (k : ℕ) :
    wordProd g (wpow w k) = wordProd g w ^ k := by
  induction k with
  | zero => simp [wpow, wordProd]
  | succ k ih => rw [wpow, wordProd_append, ih, pow_succ']

theorem wordProd_winv (g : ℕ → G) (w : Word) : wordProd g (winv w) = (wordProd g w)⁻¹ := by
  induction w with
  | nil => simp [winv, wordProd]
  | cons l w ih =>
    have e : winv (l :: w) = winv w ++ [(l.1, !l.2)] := by simp [winv]
    rw [e, wordProd_append, ih]
    obtain ⟨i, s⟩ := l
    cases s <;> simp [wordProd]

theorem eq_of_rep [FaithfulSMul G (Fin n)] {T : Table} {g h : G} (hg : Rep n T g)
    (hh : Rep n T h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Fin n) fun i => ?_
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  rw [idx_of_lt g i.isLt] at h1
  rw [idx_of_lt h i.isLt] at h2
  exact h1.symm.trans h2

theorem ne_one_of_movesPt {T : Table} {g : G} (h : movesPt n T = true) (hT : Rep n T g) :
    g ≠ 1 := by
  rintro rfl
  have h1 : allIn 0 n (fun i => ap T i == i) = true := by
    rw [allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hT i hi, idx_one]
  simp [movesPt, h1] at h

theorem eChecks_spec [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {E : Fin 4 → Table}
    {e : Fin 4 → G} (hE : ∀ i, Rep n (E i) (e i))
    (h : eChecks n (E 0) (E 1) (E 2) (E 3) = true) :
    (∀ i, e i ^ 3 = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
      ∀ v : Fin 4 → ZMod 3, v ≠ 0 →
        e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val * e 3 ^ (v 3).val ≠ 1 := by
  unfold eChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨hc, hm⟩, hp⟩ := h
  have hmem : ∀ i : Fin 4, E i ∈ [E 0, E 1, E 2, E 3] := by
    intro i
    fin_cases i <;> simp
  refine ⟨fun i => ?_, fun i j => ?_, fun v hv => ?_⟩
  · have h1 := hc (E i) (hmem i)
    have h2 := Rep.powT hn (hE i) 3
    rw [h1] at h2
    exact eq_one_of_rep_idT hn h2
  · have h1 := hm (E i) (hmem i) (E j) (hmem j)
    have h2 := Rep.compT (hE i) (hE j)
    have h3 := Rep.compT (hE j) (hE i)
    rw [h1] at h2
    exact eq_of_rep h2 h3
  · have hlt : ∀ i : Fin 4, (v i).val ∈ [0, 1, 2] := by
      intro i
      have := ZMod.val_lt (v i)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    rcases hp _ (hlt 0) _ (hlt 1) _ (hlt 2) _ (hlt 3) with h1 | h1
    · exfalso
      obtain ⟨⟨⟨h0, h1'⟩, h2'⟩, h3'⟩ := h1
      apply hv
      funext i
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1'
      · exact (ZMod.val_eq_zero _).1 h2'
      · exact (ZMod.val_eq_zero _).1 h3'
    · have hr := Rep.compT (Rep.powT hn (hE 0) (v 0).val) (Rep.compT (Rep.powT hn (hE 1) (v 1).val)
        (Rep.compT (Rep.powT hn (hE 2) (v 2).val) (Rep.powT hn (hE 3) (v 3).val)))
      have := ne_one_of_movesPt h1 hr
      simpa [mul_assoc] using this

theorem rep_eTab (hn : n < 2 ^ 32) {x y : G} {α αi β βi : Table} (hx : Rep n α x)
    (hxi : Rep n αi x⁻¹) (hy : Rep n β y) (hyi : Rep n βi y⁻¹) (i : ℕ) :
    Rep n (eTab n α αi β βi i)
      ((eData.getD i []).map fun s => wordProd (img2 x y) (eLetterWord s)).prod := by
  unfold eTab
  generalize eData.getD i [] = l
  induction l with
  | nil => exact Rep.idT hn
  | cons s l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    exact Rep.compT (rep_wordTab hn hx hxi hy hyi _) ih

theorem guestData_of_check [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {x y : G}
    {α αi β βi : Table} (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y)
    (hyi : Rep n βi y⁻¹) (h : guestCheck n α αi β βi = true) :
    ∃ (X Y : G) (q : ℕ → G) (e : Fin 4 → G), GuestData X Y q e := by
  unfold guestCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hrels := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h1
  let g := img2 x y
  let q : ℕ → G := fun j => wordProd g (qWord j)
  let S : Set G := {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c}
  let F : ℤ → G := fun s => wordProd g (eLetterWord s)
  let e : Fin 4 → G := fun i => ((eData.getD (i : ℕ) []).map F).prod
  have hX : wordProd g wx ^ 5 = 1 := by
    have := hrels (wpow wx 5) (by simp [wordRels])
    rwa [wordProd_wpow] at this
  have hY : wordProd g wy ^ 5 = 1 := by
    have := hrels (wpow wy 5) (by simp [wordRels])
    rwa [wordProd_wpow] at this
  have hXY : wordProd g wx * wordProd g wy = wordProd g wy * wordProd g wx := by
    have := hrels (wx ++ wy ++ winv wx ++ winv wy) (by simp [wordRels])
    simp only [wordProd_append, wordProd_winv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hq : ∀ j, q j ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) := by
    have hXm : wordProd g wx ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hYm : wordProd g wy ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) :=
      Subgroup.subset_closure (by simp)
    intro j
    rcases j with _ | _ | k
    · exact hXm
    · exact hYm
    · show wordProd g (wx ++ wpow wy (k + 1)) ∈ _
      rw [wordProd_append, wordProd_wpow]
      exact Subgroup.mul_mem _ hXm (Subgroup.pow_mem _ hYm _)
  have hnt : ∀ t ∈ nData, q t.1 ≠ 1 := fun t ht =>
    ne_one_of_movesPt ((List.all_eq_true.1 h2) t ht) (rep_wordTab hn hx hxi hy hyi (qWord t.1))
  have hm : ∀ k, wordProd g (nWord k) ∈ Subgroup.closure S := by
    intro k
    by_cases hk : k < nData.length
    · have hd : nData.getD k (0, 0, []) = nData[k] := List.getD_eq_getElem _ _ hk
      have hnw : nWord k = nData[k].2.2 := by
        unfold nWord
        rw [hd]
      have hmem : nData[k] ∈ nData := List.getElem_mem hk
      have hrel := hrels (nRel nData[k]) (by
        simp only [wordRels, List.mem_append, List.mem_map]
        exact Or.inr ⟨_, hmem, rfl⟩)
      simp only [nRel, wordProd_append, wordProd_winv, wordProd_wpow] at hrel
      rw [hnw]
      exact Subgroup.subset_closure ⟨nData[k].1, nData[k].2.1, hnt _ hmem, mul_inv_eq_one.1 hrel⟩
    · have : nWord k = [] := by
        unfold nWord
        rw [List.getD_eq_default _ _ (not_lt.1 hk)]
      rw [this]
      exact Subgroup.one_mem _
  have hF : ∀ s, F s ∈ Subgroup.closure S := by
    intro s
    show wordProd g (eLetterWord s) ∈ _
    unfold eLetterWord
    split_ifs
    · exact hm _
    · rw [wordProd_winv]
      exact Subgroup.inv_mem _ (hm _)
  have hEi : ∀ i, e i ∈ Subgroup.closure S := fun i =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
      exact hF s
  have hrep : ∀ i : Fin 4, Rep n (eTab n α αi β βi i) (e i) := fun i =>
    rep_eTab hn hx hxi hy hyi i
  obtain ⟨hpow, hcomm, hne⟩ := eChecks_spec hn hrep h3
  exact ⟨_, _, q, e, ⟨hX, hY, hXY, hq, hEi, hpow, hcomm, hne⟩⟩

end Soundness

open CFSG.Sporadic.Fi22 (J rep_alpha rep_beta actionChecks_parts)

theorem guest_check : fi22GuestCheck = true :=
  Certificates.certificate9400

theorem guestData_J :
    ∃ (X Y : J) (q : ℕ → J) (e : Fin 4 → J), GuestData X Y q e :=
  guestData_of_check (n := 3510) (by norm_num) rep_alpha
    CFSG.Sporadic.Bridge.Fi22.rep_alpha_inv rep_beta
    (CFSG.Sporadic.Th.Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1) guest_check

end CFSG.AGLEmbedding.KFactProofs.Fi22Guest

namespace CFSG.AGLEmbedding

theorem kFactFi22GuestRank :
    KFactFi22GuestRank := by
  intro K _ _ hK T
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  obtain ⟨X, Y, q, e, D⟩ := KFactProofs.Fi22Guest.guestData_J
  exact (D.map ((CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans β).trans φ.symm)).exists_of_sylow T

end CFSG.AGLEmbedding

module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Tools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Comp
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Order3
public import CFSG.LocalAnalysis.GL83PartI.I_33

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

theorem mem_centralizerQuot_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {X J J' : Subgroup G}
    (hJ : GLAPComponent p X J) (hJ' : GLAPComponent p X J') (hne : J ≠ J') {g : G}
    (hg : g ∈ J') : g ∈ centralizerQuot J (GLAPPrimeCoreOf p J) := by
  have hN := mem_normalizer_of_ne hp hJ hJ' hne hg
  refine ⟨hN, ?_, fun y hy => ?_⟩
  swap
  · have := (GLAPPrimeCoreOf p J).inv_mem (commutator_mem_gLAPPrimeCoreOf_of_ne hp hJ hJ' hne hg hy)
    simpa [mul_assoc] using this
  rw [mem_normalizer_iff_gLBConj_eq] at hN ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hN]

theorem isElemAbelian_sup_zpowers {A : Subgroup G} {x : G} (hA : IsElemAbelian 3 A)
    (hx : x ^ 3 = 1) (hc : ∀ a ∈ A, a * x = x * a) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers x) := by
  have hcomm : ∀ (m : A) (n : Subgroup.zpowers x),
      Commute (A.subtype m) ((Subgroup.zpowers x).subtype n) := by
    intro m n
    obtain ⟨k, hk⟩ := n.2
    show (m : G) * (n : G) = (n : G) * m
    rw [← hk]
    exact ((Commute.zpow_right (hc m m.2 : (m : G) * x = x * m) k)).eq
  have hrange : (MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers x).subtype hcomm).range =
      A ⊔ Subgroup.zpowers x := by
    rw [MonoidHom.noncommCoprod_range]
    simp
  have hmem : ∀ z ∈ A ⊔ Subgroup.zpowers x, ∃ a ∈ A, ∃ n : ℤ, z = a * x ^ n := by
    intro z hz
    rw [← hrange] at hz
    obtain ⟨⟨m, n⟩, rfl⟩ := hz
    obtain ⟨k, hk⟩ := n.2
    exact ⟨m, m.2, k, by simp [hk]⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxc : ∀ a ∈ A, ∀ n : ℤ, a * x ^ n = x ^ n * a := fun a ha n =>
    (Commute.zpow_right (hc a ha : (a : G) * x = x * a) n).eq
  have hx3 : ∀ n : ℤ, (x ^ n) ^ 3 = 1 := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  refine ⟨⟨⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha, n, rfl⟩ := hmem u hu
    obtain ⟨b, hb, m, rfl⟩ := hmem v hv
    apply Subtype.ext
    show a * x ^ n * (b * x ^ m) = b * x ^ m * (a * x ^ n)
    have h1 : x ^ n * b = b * x ^ n := (hxc b hb n).symm
    have h2 : x ^ n * x ^ m = x ^ m * x ^ n := (Commute.zpow_zpow_self x n m).eq
    calc a * x ^ n * (b * x ^ m) = a * (x ^ n * b) * x ^ m := by group
      _ = a * (b * x ^ n) * x ^ m := by rw [h1]
      _ = (a * b) * (x ^ n * x ^ m) := by group
      _ = (b * a) * (x ^ m * x ^ n) := by rw [hAc a ha b hb, h2]
      _ = b * (a * x ^ m) * x ^ n := by group
      _ = b * (x ^ m * a) * x ^ n := by rw [hxc a ha m]
      _ = b * x ^ m * (a * x ^ n) := by group
  · obtain ⟨a, ha, n, rfl⟩ := hmem z hz
    have hcom : Commute a (x ^ n) := hxc a ha n
    rw [hcom.mul_pow, hA.2 a ha, hx3 n, one_mul]

theorem exists_extension [Finite G] {X : Subgroup G} (S : Finset (Subgroup G))
    (hS : ∀ J ∈ S, GLAPComponent 3 X J) {A₀ : Subgroup G} (hA₀ : IsElemAbelian 3 A₀)
    (hA₀X : A₀ ≤ X) (hA₀N : ∀ L, GLAPComponent 3 X L → A₀ ≤ Subgroup.normalizer (L : Set G))
    (hA₀c : ∀ J ∈ S, A₀ ≤ centralizerQuot J (GLAPPrimeCoreOf 3 J)) :
    ∃ B' : Subgroup G, A₀ ≤ B' ∧ B' ≤ X ∧ B' ≤ A₀ ⊔ ⨆ J ∈ S, J ∧ IsElemAbelian 3 B' ∧
      Nat.card B' = Nat.card A₀ * 3 ^ S.card ∧
      (∀ L, GLAPComponent 3 X L → B' ≤ Subgroup.normalizer (L : Set G)) ∧
      ∀ J ∈ S, ¬ B' ⊓ J ≤ oPrimePOf 3 J := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨A₀, le_rfl, hA₀X, le_sup_left, hA₀, by simp, hA₀N, by simp⟩
  | insert J S' hJS' ih =>
    have hJ : GLAPComponent 3 X J := hS J (Finset.mem_insert_self _ _)
    obtain ⟨B'', hAB, hBX, hBle, hBel, hBcard, hBN, hBnot⟩ :=
      ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
        (fun K hK => hA₀c K (Finset.mem_insert_of_mem hK))
    have hBc : B'' ≤ centralizerQuot J (GLAPPrimeCoreOf 3 J) := by
      refine hBle.trans (sup_le (hA₀c J (Finset.mem_insert_self _ _)) ?_)
      refine iSup₂_le fun J' hJ' g hg => ?_
      have hne : J ≠ J' := fun h => hJS' (h ▸ hJ')
      exact mem_centralizerQuot_of_ne Nat.prime_three hJ (hS J' (Finset.mem_insert_of_mem hJ'))
        hne hg
    obtain ⟨x, hxJ, hx3, hxnot, hxc⟩ :=
      exists_centralizing_order_three hJ (GL83.isPGroup_of_isElemAbelian hBel) hBc
    have hxB : x ∉ B'' := fun hx =>
      hxnot (mem_oPrimePOf_of_forall_commutator_mem Nat.prime_three hxJ fun y hy => by
        have := (GLAPPrimeCoreOf 3 J).inv_mem ((hBc hx).2.2 y hy)
        simpa [mul_assoc] using this)
    have hcard := card_sup_zpowers_of_pow_three_eq_one hx3 hxB (fun h hh => hxc h hh)
    refine ⟨B'' ⊔ Subgroup.zpowers x, hAB.trans le_sup_left,
      sup_le hBX (Subgroup.zpowers_le.2 (hJ.1 hxJ)), ?_,
      isElemAbelian_sup_zpowers hBel hx3 hxc, ?_, ?_, ?_⟩
    · refine sup_le (hBle.trans (sup_le_sup_left ?_ _)) ?_
      · exact iSup₂_mono' fun K hK => ⟨K, Finset.mem_insert_of_mem hK, le_rfl⟩
      · refine Subgroup.zpowers_le.2 ?_
        have hJle : J ≤ A₀ ⊔ ⨆ K ∈ insert J S', K :=
          le_sup_of_le_right (le_iSup₂_of_le J (Finset.mem_insert_self _ _) le_rfl)
        exact hJle hxJ
    · rw [hcard, hBcard, Finset.card_insert_of_notMem hJS']
      ring
    · intro L hL
      refine sup_le (hBN L hL) (Subgroup.zpowers_le.2 ?_)
      by_cases hLJ : L = J
      · subst hLJ
        exact Subgroup.le_normalizer hxJ
      · exact mem_normalizer_of_ne Nat.prime_three hL hJ hLJ hxJ
    · intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK'
      · intro h
        exact hxnot (h ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hxJ⟩)
      · intro h
        exact hBnot K hK' fun y hy => h ⟨Subgroup.mem_sup_left hy.1, hy.2⟩

end CFSG.HardMathSupport.Solomon.LocalBalance

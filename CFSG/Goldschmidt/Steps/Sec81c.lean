module

import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.G52
import CFSG.Walter.Bender1970.S5.Normalizer
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem fittingSubgroupOf_le (H : Subgroup G) : CFSG.fittingSubgroupOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem isNilpotent_fittingSubgroupOf (H : Subgroup G) :
    Group.IsNilpotent (CFSG.fittingSubgroupOf H) :=
  Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem le_normalizer_oddCoreOf_fitting (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreOf (CFSG.fittingSubgroupOf H) : Set G) :=
  le_normalizer_oddCoreOf_of_le_normalizer
    (GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.fittingSubgroupOf_isNormalIn H))

theorem qCoreOf_le_oddCoreOf_fitting (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GorensteinWalter.qCoreOf H p ≤ oddCoreOf (CFSG.fittingSubgroupOf H) := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_oddCoreOf (GorensteinWalter.qCoreOf_le_fittingSubgroupOf H p hp)
    ((fittingSubgroupOf_le H).trans (GorensteinWalter.le_normalizer_of_isNormalIn
      (GorensteinWalter.qCoreOf_normal_in H p))) ?_
  obtain ⟨k, hk⟩ := (GorensteinWalter.qCoreOf_isPGroup H p).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem false_of_le (h31 : S_G31) (h37 : S_G37) (h64 : S_G64) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) {V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hVF : V ≤ CFSG.fittingSubgroupOf H) (hVp : IsPGroup p V) (hVc : ¬ IsCyclic V)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) {M : Subgroup G}
    (hM : IsCoatom M) (hMH : M ≠ H) (hAM : A ≤ M) (hVM : V ≤ M) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have haM : a ∈ M := hAM ha
  have hVa : V ≤ Subgroup.centralizer ({a} : Set G) :=
    hHa ▸ hVF.trans (fittingSubgroupOf_le H)
  have hVC' : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := fun v hv hv1 => hHa ▸ hVC v hv hv1
  have hOa := oddCoreOf_le_centralizer hp hp2 (hset.elem.2 a ha) hVp hVc hVC' haM hVM hVa
  have hAV := not_le_centralizer h64 hset h4 ha ha1 hH hp hp2 hVp hVc hVC
  have hS := sstar_of_le hset hM.1 hAM
  obtain ⟨-, -, T, hT, -, hcl, -⟩ := id hS
  set Q := normalClosureIn M A with hQ
  have hQM : GorensteinWalter.IsNormalIn Q M :=
    ⟨normalClosureIn_le_self M A, fun h hh k hk =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn M A hh) k).mp hk⟩
  have hOFQ : oddCoreOf (CFSG.fittingSubgroupOf Q) ≤ oddCoreOf M :=
    le_oddCoreOf (((oddCoreOf_le _).trans (fittingSubgroupOf_le Q)).trans hQM.1)
      (le_normalizer_oddCoreOf_of_le_normalizer (GorensteinWalter.le_normalizer_of_isNormalIn
        (Walter.fittingSubgroupOf_isNormalIn_of_isNormalIn hQM))) (odd_card_oddCoreOf _)
  have haF : a ∈ GorensteinWalter.generalizedFittingSubgroupOf M := by
    refine (h31 G M A hS).2 ⟨le_normalClosureIn hAM ha, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hOa (hOFQ hy))
  have hMN2 :=
    GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.qCoreOf_normal_in M 2)
  have haFM : a ∉ CFSG.fittingSubgroupOf M := by
    intro haFM
    have hza : IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1, pow_one])
    have ha2M : a ∈ GorensteinWalter.qCoreOf M 2 :=
      Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two (Subgroup.zpowers_le.mpr haFM)
        hza (Subgroup.mem_zpowers a)
    have hO2T : GorensteinWalter.qCoreOf M 2 ≤ T := by
      have hsup : IsPGroup 2 (T ⊔ GorensteinWalter.qCoreOf M 2 : Subgroup G) :=
        IsPGroup.to_sup_of_normal_right' hT.2.1 (GorensteinWalter.qCoreOf_isPGroup M 2)
          (hT.1.trans hMN2)
      have heq := hT.2.2 _ (sup_le hT.1 (GorensteinWalter.qCoreOf_le M 2)) hsup le_sup_left
      exact heq ▸ le_sup_right
    by_cases hAO : A ≤ GorensteinWalter.qCoreOf M 2
    · refine hAV fun v hv => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hvp : v ∈ GorensteinWalter.qCoreOf H p :=
        Walter.le_qCoreOf_of_le_fittingSubgroupOf hp hVF hVp hv
      have hxH : x ∈ H := le_of_mem_benderM hset h4 ha hH (hset.le hx)
      have hc1 : x⁻¹ * (v⁻¹ * x * v) ∈ GorensteinWalter.qCoreOf M 2 := by
        refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAO hx)) ?_
        simpa using
          (GorensteinWalter.qCoreOf_normal_in M 2).2 v⁻¹ (M.inv_mem (hVM hv)) x (hAO hx)
      have hc2 : x⁻¹ * (v⁻¹ * x * v) ∈ GorensteinWalter.qCoreOf H p := by
        have h1 := (GorensteinWalter.qCoreOf_normal_in H p).2 x⁻¹ (H.inv_mem hxH) v⁻¹
          (Subgroup.inv_mem _ hvp)
        have h2 := Subgroup.mul_mem _ h1 hvp
        simpa [mul_assoc] using h2
      have hdisj := IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _
        (GorensteinWalter.qCoreOf_isPGroup M 2) (GorensteinWalter.qCoreOf_isPGroup H p)
      have h1 : x = v⁻¹ * x * v :=
        inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hdisj.le_bot ⟨hc1, hc2⟩))
      calc x * v = v * (v⁻¹ * x * v) := by group
        _ = v * x := by rw [← h1]
    · obtain ⟨b, hb, hbO⟩ := Set.not_subset.mp hAO
      have hb1 : b ≠ 1 := fun h => hbO (h ▸ Subgroup.one_mem _)
      have hab : a ≠ b := fun h => hbO (h ▸ ha2M)
      apply hMH
      have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := fun m hm => by
        have h1 : m⁻¹ * a * m ∈ GorensteinWalter.qCoreOf M 2 := by
          simpa using (GorensteinWalter.qCoreOf_normal_in M 2).2 m⁻¹ (M.inv_mem hm) a ha2M
        have h2 : m⁻¹ * a * m ∈ A := hcl a ha m hm (hO2T h1)
        rcases mem_four hset.elem h4 ha hb h2 ha1 hb1 hab with h | h | h | h
        · exact absurd h (by simpa using conj_ne_one (n := m⁻¹) ha1)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc m * a = m * (m⁻¹ * a * m) := by rw [h]
            _ = a * m := by group
        · exact absurd (h ▸ h1) hbO
        · refine absurd ?_ hbO
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha2M) (h ▸ h1)
          simpa using this
      rcases hM.le_iff.mp (hHa ▸ hMa) with h | h
      · exact absurd h (Walter.ne_top_of_mem_benderM hH)
      · exact h.symm
  have haE : a ∉ Subgroup.centralizer (GorensteinWalter.componentLayerOf M : Set G) :=
    fun h => haFM (Walter.generalizedFittingSubgroupOf_inf_centralizer_le M ⟨haF, h⟩)
  obtain ⟨L, hL, haL⟩ : ∃ L : Subgroup G, GorensteinWalter.IsComponentOf L M ∧
      a ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    refine haE (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have hle : GorensteinWalter.componentLayerOf M ≤ Subgroup.centralizer ({a} : Set G) :=
      sSup_le fun K hK k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hno K hK) k hk)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  set X := oddCoreOf (CFSG.fittingSubgroupOf H) ⊓ M with hX
  have hXM : X ≤ M := inf_le_right
  have hXn : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    fun y hy => mem_normalizer_inf (le_normalizer_oddCoreOf_fitting H (hHa ▸ hy.2))
      (Subgroup.le_normalizer hy.1)
  have hXodd : Odd (Nat.card X) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hXnil : Group.IsNilpotent X :=
    Walter.isNilpotent_of_le (isNilpotent_fittingSubgroupOf H)
      (inf_le_left.trans (oddCoreOf_le _))
  have hOFX : oddCoreOf (CFSG.fittingSubgroupOf X) = X := by
    rw [Walter.fittingSubgroupOf_eq_self_of_isNilpotent hXnil, G52.oddCoreOf_eq_self_of_odd hXodd]
  have hXeq : X = GorensteinWalter.componentLayerOf X ⊔
      oddCoreOf (CFSG.fittingSubgroupOf X) := by
    rw [Walter.componentLayerOf_eq_bot_of_isSolvable (by infer_instance), bot_sup_eq, hOFX]
  obtain ⟨-, -, -, h3⟩ := h37 G M A hS hset.elem a ha ha1 X hXM hXn hXeq
  rw [hOFX] at h3
  have hVX : V ≤ X := le_inf ((Walter.le_qCoreOf_of_le_fittingSubgroupOf hp hVF hVp).trans
    (qCoreOf_le_oddCoreOf_fitting H hp hp2)) hVM
  obtain ⟨v, hv, hv1, hvL⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (L : Set G) := by
    by_cases hXL : X ≤ Subgroup.centralizer (L : Set G)
    · obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (ne_bot_of_not_isCyclic hVc)
      exact ⟨v, hv, fun h => hv1 (Subtype.ext h), hXL (hVX hv)⟩
    · obtain ⟨-, -, hXLC, ⟨y, hyX, hy⟩, -⟩ := h3 L hL hXL
      have hyN : y ∈ Subgroup.normalizer
          ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        normalizer_le_normalizer_centralizer L ((sup_le Subgroup.le_normalizer
          (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) (hXLC hyX))
      by_contra hno
      simp only [not_exists, not_and] at hno
      refine hVc (isCyclic_of_le_zpowers_sup hyN (hVX.trans hy) ?_)
      refine eq_bot_iff.mpr fun v hv => Subgroup.mem_bot.mpr ?_
      by_contra hv1
      exact hno v hv.1 hv1 hv.2
  apply haL
  have hLv : L ≤ Subgroup.centralizer ({v} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hvL l hl)
  have hLa : L ≤ Subgroup.centralizer ({a} : Set G) := hHa ▸ hLv.trans (hVC v hv hv1)
  exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLa hl))

omit [Finite G] in
theorem mem_two [Finite G] {K : Subgroup G} (h2 : Nat.card K = 2) {a x : G} (ha : a ∈ K)
    (ha1 : a ≠ 1) (hx : x ∈ K) : x = 1 ∨ x = a := by
  classical
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hx1, hxa⟩ := hne
  have hsub : (({1, a, x} : Finset G) : Set G) ⊆ K := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact K.one_mem
    · exact ha
    · exact hx
  have hcard : ({1, a, x} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hxa
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hx1⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  change 3 ≤ Nat.card K at hle
  omega

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : conjSub g K = K := by
  ext x
  rw [mem_conjSub, ← Subgroup.mem_normalizer_iff.mp hg x]

theorem false_of_le_sup (h31 : S_G31) (h37 : S_G37) (h64 : S_G64) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) {V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hVF : V ≤ CFSG.fittingSubgroupOf H) (hVp : IsPGroup p V) (hVc : ¬ IsCyclic V)
    (hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) {M : Subgroup G}
    (hM : IsCoatom M) (hMH : M ≠ H) (haVM : Subgroup.zpowers a ⊔ V ≤ M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have haM : a ∈ M := haVM (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hVM : V ≤ M := le_sup_right.trans haVM
  have hVa : V ≤ Subgroup.centralizer ({a} : Set G) :=
    hHa ▸ hVF.trans (fittingSubgroupOf_le H)
  have hVC' : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := fun v hv hv1 => hHa ▸ hVC v hv hv1
  have hOa := oddCoreOf_le_centralizer hp hp2 (hset.elem.2 a ha) hVp hVc hVC' haM hVM hVa
  have hMH' : ¬ M ≤ Subgroup.centralizer ({a} : Set G) := fun hle => by
    rcases hM.le_iff.mp (hHa ▸ hle) with h | h
    · exact Walter.ne_top_of_mem_benderM hH h
    · exact hMH h.symm
  obtain ⟨g, hle, hS⟩ := hset.sstar M hM.1
  set A₁ := conjSub g A ⊓ M with hA₁
  have haA₁ : a ∈ A₁ := ⟨hle ⟨ha, haM⟩, haM⟩
  have hdvd : Nat.card A₁ ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4, ← card_conjSub g A]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases i
  · exact ha1 (Subgroup.mem_bot.mp ((Subgroup.card_eq_one.mp (by simpa using hcard)) ▸ haA₁))
  ·
    rw [pow_one] at hcard
    obtain ⟨-, -, T, hT, hA₁T, hcl, -⟩ := hS
    have hiso : ∀ m ∈ M, m⁻¹ * a * m ∈ T → m⁻¹ * a * m = a := fun m hm hmT => by
      rcases mem_two hcard haA₁ ha1 (hcl a haA₁ m hm hmT) with h | h
      · exact absurd h (by simpa using conj_ne_one (n := m⁻¹) ha1)
      · exact h
    have hTa : T ≤ Subgroup.centralizer ({a} : Set G) := fun t ht => by
      have h1 := hiso t (hT.1 ht) (T.mul_mem (T.mul_mem (T.inv_mem ht) (hA₁T haA₁)) ht)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * a = t * (t⁻¹ * a * t) := by rw [h1]
        _ = a * t := by group
    refine hMH' fun m hm => ?_
    have hz := commutator_mem_oddCoreOf hT (hA₁T haA₁) hTa (mul_self_eq_one hset.elem ha) ha1
      hiso hm
    obtain ⟨y, hy⟩ : ∃ y, m * a * m⁻¹ * a⁻¹ = y := ⟨_, rfl⟩
    rw [hy] at hz
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hOa hz)
    have e1 : m * a * m⁻¹ = y * a := by rw [← hy]; group
    have e2 : (y * a) * (y * a) = 1 := by
      rw [← e1]
      calc m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
        _ = 1 := by rw [mul_self_eq_one hset.elem ha]; group
    have hy2 : y ^ 2 = 1 := by
      calc y ^ 2 = y * y * (a * a) := by rw [mul_self_eq_one hset.elem ha, mul_one, sq]
        _ = y * (y * a) * a := by group
        _ = y * (a * y) * a := by rw [hya]
        _ = (y * a) * (y * a) := by group
        _ = 1 := e2
    have hy1 : y = 1 := eq_one_of_pow_two_of_odd (odd_card_oddCoreOf M) hz (k := 1) (by simpa)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * a = (m * a * m⁻¹ * a⁻¹) * a * m := by group
      _ = a * m := by rw [hy, hy1, one_mul]
  ·
    have hA₁eq : A₁ = conjSub g A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_conjSub, h4, hcard]; norm_num)
    have hA₁ab : IsMulCommutative A₁ := ⟨⟨fun x y => Subtype.ext (by
      have hx : (x : G) ∈ conjSub g A := x.2.1
      have hy : (y : G) ∈ conjSub g A := y.2.1
      rw [mem_conjSub] at hx hy
      have h := comm hset.elem hx hy
      have : g * (x * y : G) * g⁻¹ = g * (y * x : G) * g⁻¹ := by
        calc g * (x * y : G) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h
          _ = g * (y * x : G) * g⁻¹ := by group
      simpa using conj_injective this)⟩⟩
    have hA₁H : A₁ ≤ H := fun x hx => hHa ▸ Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA₁ab.is_comm.comm ⟨x, hx⟩ ⟨a, haA₁⟩))
    have hA₁2 : IsPGroup 2 A₁ := (S.isPGroup'.to_le hset.le).map (MulAut.conj g⁻¹).toMonoidHom
      |>.to_le inf_le_left
    obtain ⟨c, hcH, y, hy1, hy2⟩ := Quasithin.exists_conj_le_sylow_of_isPGroup S
      (le_of_mem_benderM hset h4 ha hH) hA₁H S.isPGroup' hA₁2
    have hyS : y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      have heq : Quasithin.conjSubgroup (S : Subgroup G) y = S :=
        Subgroup.eq_of_le_of_card_ge hy1 (by
          rw [Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective])
      exact Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp heq
    have hyA : y ∈ Subgroup.normalizer (A : Set G) :=
      N3a G S A S hset.le hset.closed S.isPGroup' hset.le hyS
    have h1 : conjSub (g * (c * y)) A ≤ S := by
      rw [conjSub_mul, ← hA₁eq]
      exact hy2
    have h2 : conjSub (g * (c * y)) A = A := conj_eq_of_conj_le hset.closed h1
    have hgc : conjSub (g * c) A = A := by
      have h3 := congrArg (conjSub y⁻¹) h2
      rw [conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ hyA), ← conjSub_mul] at h3
      rw [← h3]
      congr 1
      group
    have hcA₁ : conjSub c A₁ = A := by
      rw [hA₁eq, ← conjSub_mul]
      exact hgc
    have hcinv : c⁻¹ ∈ H := H.inv_mem hcH
    refine false_of_le h31 h37 h64 hset h4 ha ha1 hH hp hp2 (V := conjSub c V) ?_ (hVp.map _)
      ?_ ?_ (M := conjSub c M) (Walter.isCoatom_map_conj c⁻¹ hM) ?_ ?_ (Subgroup.map_mono hVM)
    · intro x hx
      rw [mem_conjSub] at hx
      have := (show GorensteinWalter.IsNormalIn (CFSG.fittingSubgroupOf H) H from
        GorensteinWalter.fittingSubgroupOf_isNormalIn H).2 c⁻¹ hcinv _ (hVF hx)
      simpa [mul_assoc] using this
    · intro hcyc
      have : IsCyclic (V.map (MulAut.conj c⁻¹).toMonoidHom) := hcyc
      exact hVc (isCyclic_of_injective
        (V.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
          (MulAut.conj c⁻¹).injective).toMonoidHom (MulEquiv.injective _))
    · intro v hv hv1 x hx
      rw [mem_conjSub] at hv
      have hx' : c * x * c⁻¹ ∈ Subgroup.centralizer ({c * v * c⁻¹} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        calc c * x * c⁻¹ * (c * v * c⁻¹) = c * (x * v) * c⁻¹ := by group
          _ = c * (v * x) * c⁻¹ := by rw [hx]
          _ = c * v * c⁻¹ * (c * x * c⁻¹) := by group
      have := H.mul_mem (H.mul_mem hcinv (hVC _ hv (conj_ne_one hv1) hx')) hcH
      simpa [mul_assoc] using this
    · intro h
      apply hMH
      have h3 := congrArg (conjSub c⁻¹) h
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one,
        conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hcinv)] at h3
      exact h3
    · rw [← hcA₁]
      exact Subgroup.map_mono inf_le_right

end CFSG.Goldschmidt.Sec8

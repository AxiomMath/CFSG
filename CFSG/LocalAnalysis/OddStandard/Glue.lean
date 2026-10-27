module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeCatalog
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.ComponentClassification.UnbalancedLayer

theorem coreActionKernel_eq_centralizer {G : Type*} [Group G] {L : Subgroup G}
    (hperf : Group.IsPerfect L) (hO : CFSG.pPrimeCore 2 L ≤ Subgroup.center L) :
    coreActionKernel L = Subgroup.centralizer (L : Set G) := by
  refine le_antisymm ?_ ?_
  · have hcomm : ⁅L, coreActionKernel L⁆ ≤ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl k hk
      have h1 := (mem_coreActionKernel.1 (inv_mem hk)).2 l⁻¹ (inv_mem hl)
      obtain ⟨z, hz, hzl⟩ := Subgroup.mem_map.1 h1
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hzc := Subgroup.mem_center_iff.1 (hO hz) ⟨h, hh⟩
      have hcomm' : (h : G) * (z : G) = (z : G) * h := congrArg Subtype.val hzc
      have hzl' : (z : G) = l * k * l⁻¹ * k⁻¹ := by simpa using hzl
      rw [hzl'] at hcomm'
      rw [commutatorElement_def]
      exact hcomm'
    have hdc : ⁅⁅L, coreActionKernel L⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcomm
    have hLK := LocalAnalysis.ComponentInitial.perfect_double_commutator
      (Subgroup.commutator_eq_self (H := L)) hdc
    exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLK)
  · intro g hg
    refine mem_coreActionKernel.2
      ⟨Subgroup.centralizer_le_normalizer (L : Set G) hg, fun j hj => ?_⟩
    have hjg : j * g = g * j := Subgroup.mem_centralizer_iff.1 hg j hj
    have h : j⁻¹ * g⁻¹ * j * g = 1 := by
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by rw [mul_assoc (j⁻¹ * g⁻¹)]
        _ = j⁻¹ * g⁻¹ * (g * j) := by rw [hjg]
        _ = 1 := by group
    rw [h]
    exact one_mem _

theorem isCyclic_sylow_of_eq {G : Type*} [Group G] {A B : Subgroup G} (h : A = B)
    (hB : ∀ Q : Sylow 2 B, IsCyclic (Q : Subgroup B)) :
    ∀ P : Sylow 2 A, IsCyclic (P : Subgroup A) := by
  subst h
  exact hB

theorem isCyclic_sylow_coreActionKernel {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hperf : Group.IsPerfect L) (hO : CFSG.pPrimeCore 2 L ≤ Subgroup.center L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G)))) :
    ∀ P : Sylow 2 (coreActionKernel L), IsCyclic (P : Subgroup (coreActionKernel L)) :=
  isCyclic_sylow_of_eq (coreActionKernel_eq_centralizer hperf hO) fun Q =>
    ((Sylow.equiv Q S).isCyclic).2 hS

theorem pPrimeCore_eq_center_of_odd_center {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (heven : 2 ∣ Nat.card L) : CFSG.pPrimeCore 2 L = Subgroup.center L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
        (CFSG.pPrimeCore_normal (p := 2) (G := L)) with htop | hle
    · exfalso
      have h1 := CFSG.pPrimeCore_coprime_card (p := 2) (G := L)
      rw [htop, Subgroup.card_top] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd h1 heven) (by norm_num)
    · exact hle
  · exact le_sSup (show Subgroup.center L ∈
      {K : Subgroup L | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩)

namespace StandardSetting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isStandardSubgroup (h : StandardSetting G L) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup L :=
  h.standard

theorem even_card_centralizer (h : StandardSetting G L) :
    Even (Nat.card (Subgroup.centralizer (L : Set G))) :=
  h.standard.2.1

theorem center_eq_bot (h : StandardSetting G L) : Subgroup.center G = ⊥ :=
  have := h.simple
  ComponentClassification.StandardRecognition.center_eq_bot_of_isSimpleGroup h.nonab

theorem ne_top (h : StandardSetting G L) : L ≠ ⊤ := by
  intro htop
  have heven := h.even_card_centralizer
  rw [htop, Subgroup.coe_top, Subgroup.centralizer_univ, h.center_eq_bot,
    Subgroup.card_bot] at heven
  exact Nat.not_even_one heven

theorem ne_bot (h : StandardSetting G L) : L ≠ ⊥ := by
  rintro rfl
  have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) :=
    h.standard.1.2
  exact not_nontrivial _ hs.toNontrivial

theorem not_normal (h : StandardSetting G L) : ¬ L.Normal := fun hN => by
  have := h.simple
  have := hN
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal L).elim h.ne_bot h.ne_top

theorem oddCore_eq_bot (h : StandardSetting G L) : standardComponentOddCore G = ⊥ := by
  have := h.simple
  refine sSup_eq_bot.2 fun N hN => ?_
  have := hN.1
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right fun htop => ?_
  have hGodd : Odd (Nat.card G) := by
    rw [← Subgroup.card_top (G := G), ← htop]
    exact hN.2
  have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (L : Set G))
  exact Nat.not_even_iff_odd.2 hGodd
    (even_iff_two_dvd.2 ((even_iff_two_dvd.1 h.even_card_centralizer).trans hdvd))

theorem normalClosure_eq_top (h : StandardSetting G L) :
    Subgroup.normalClosure (L : Set G) = ⊤ := by
  have := h.simple
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.normalClosure (L : Set G))).resolve_left fun hbot => h.ne_bot (le_bot_iff.1 ?_)
  rw [← hbot]
  exact Subgroup.le_normalClosure

end StandardSetting

theorem sixty_le_card_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    60 ≤ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
  have h5 : Nat.factorial 5 ≤ Nat.factorial n := Nat.factorial_le hn
  have h120 : Nat.factorial 5 = 120 := rfl
  omega

theorem two_dvd_card_alternatingGroup {n : ℕ} (hn : 4 ≤ n) :
    2 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
  have h4 : 4 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) hn
  omega

theorem sixty_le_card_of_quotient_alternating {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hn : 5 ≤ n) (θ : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)) : 60 ≤ Nat.card Q := by
  have h1 : Nat.card (Q ⧸ Subgroup.center Q) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [Nat.card_congr θ.toEquiv] at h1
  exact (sixty_le_card_alternatingGroup hn).trans h1

theorem two_dvd_card_of_quotient_alternating {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hn : 4 ≤ n) (θ : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)) : 2 ∣ Nat.card Q :=
  (two_dvd_card_alternatingGroup hn).trans (by
    rw [← Nat.card_congr θ.toEquiv]
    exact Subgroup.card_quotient_dvd_card _)

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_sylow_two_of_card_eq_eight_mul {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hm : ¬ 2 ∣ m) (h : Nat.card G = 8 * m) (P : Sylow 2 G) : Nat.card (P : Subgroup G) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Sylow.card_eq_multiplicity P, h, show (8 : ℕ) = 2 ^ 3 by norm_num,
    Nat.factorization_mul (by norm_num) hm0, Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd hm]

theorem exists_sylow_two_card_eight_of_alternating {n : ℕ} (hn : n = 6 ∨ n = 7) {Q : Type*}
    [Group Q] [Finite Q] (e : Q ≃* alternatingGroup (Fin n)) :
    ∃ P : Sylow 2 Q, Nat.card (P : Subgroup Q) = 8 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  refine ⟨P, ?_⟩
  rcases hn with rfl | rfl
  · exact card_sylow_two_of_card_eq_eight_mul (m := 45) (by norm_num)
      (by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]) P
  · exact card_sylow_two_of_card_eq_eight_mul (m := 315) (by norm_num)
      (by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven]) P

theorem two_le_open_pRank_of_commuting_involutions {X : Type*} [Group X] [Finite X] {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) : 2 ≤ Open.pRank 2 (⊤ : Subgroup X) := by
  classical
  have hba : b * a = a * b := hc.symm
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h5 : a * b * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b, hba, ← mul_assoc, ← mul_assoc, ha, one_mul, hb]
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h5
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have h' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h', hia])
  set V : Subgroup X := Subgroup.closure ({a, b} : Set X) with hV
  have hsub : (V : Set X) ⊆ {1, a, b, a * b} := by
    have h1 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
    have h2 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h3 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> simp
    | one => simp
    | mul x y _ _ hx hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [ha, hb, hba, h1, h2, h3, h4, h5, one_mul, mul_one, true_or, or_true]
    | inv x _ hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hia, hib, hiab, true_or, or_true]
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have hbV : b ∈ V := Subgroup.subset_closure (by simp)
  have hsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    rcases hsub hx with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
    · exact h5
  have hsup : ({1, a, b, a * b} : Set X) ⊆ V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact haV
    · exact hbV
    · exact mul_mem haV hbV
  have hcard : Nat.card V = 2 ^ 2 := by
    have h1 : Nat.card V = (V : Set X).ncard := Nat.card_coe_set_eq _
    have h2 : (V : Set X) = {1, a, b, a * b} := Set.Subset.antisymm hsub hsup
    have n1 : (1 : X) ∉ ({a, b, a * b} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have n2 : a ∉ ({b, a * b} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, fun h => hb1 (mul_eq_left.1 h.symm)⟩
    have n3 : b ∉ ({a * b} : Set X) := by
      simp only [Set.mem_singleton_iff]
      exact fun h => ha1 (mul_eq_right.1 h.symm)
    rw [h1, h2, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
    norm_num
  refine SectionRank.le_pRank (k := 2) (by norm_num) le_top
    ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩ hcard
  · have hxy : (x : X) * y * ((x : X) * y) = 1 := hsq _ (mul_mem x.2 y.2)
    have hxi : (x : X)⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x x.2)
    have hyi : (y : X)⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y y.2)
    apply Subtype.ext
    have := inv_eq_of_mul_eq_one_right hxy
    rw [mul_inv_rev, hxi, hyi] at this
    exact this.symm
  · rw [pow_two]
    exact hsq x hx

private def permX : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

private def permY : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem permX_mem : permX ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, permX, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  rfl

private theorem permY_mem : permY ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, permY, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  rfl

theorem two_le_open_pRank_alternatingGroup_six :
    2 ≤ Open.pRank 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
  refine two_le_open_pRank_of_commuting_involutions (a := ⟨permX, permX_mem⟩)
    (b := ⟨permY, permY_mem⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by change permX * permX = 1; decide)
  · exact Subtype.ext (by change permY * permY = 1; decide)
  · intro h
    have h1 : permX = 1 := congrArg Subtype.val h
    revert h1
    decide
  · intro h
    have h1 : permY = 1 := congrArg Subtype.val h
    revert h1
    decide
  · intro h
    have h1 : permX = permY := congrArg Subtype.val h
    revert h1
    decide
  · exact Subtype.ext (by change permX * permY = permY * permX; decide)

private noncomputable def alternatingSixToSeven :
    alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by norm_num : 6 ≤ 7))).comp
      (alternatingGroup (Fin 6)).subtype).codRestrict (alternatingGroup (Fin 7)) fun g => by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (Equiv.Perm.viaEmbedding (g : Equiv.Perm (Fin 6)) _) = 1
    rw [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.1 g.2

private theorem alternatingSixToSeven_injective : Function.Injective alternatingSixToSeven :=
  fun a b h => Subtype.ext
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by norm_num : 6 ≤ 7))
      (congrArg Subtype.val h))

theorem open_pRank_alternatingGroup_seven_le_two :
    Open.pRank 2 (⊤ : Subgroup (alternatingGroup (Fin 7))) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hE2 : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨P, hP⟩ := hE2.exists_le_sylow
  have hP8 : Nat.card (P : Subgroup (alternatingGroup (Fin 7))) = 8 :=
    card_sylow_two_of_card_eq_eight_mul (m := 315) (by norm_num)
      (by rw [card_alternatingGroup_seven]) P
  have hdvd : Nat.card E ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hP8]
    exact Subgroup.card_dvd_of_le hP
  obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hkE]
  by_cases hk2 : k ≤ 2
  · exact Nat.pow_le_pow_right (by norm_num) hk2
  exfalso
  have hk3 : k = 3 := by omega
  subst hk3
  have hEP : E = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hP8, hkE]; norm_num)
  obtain ⟨m, -, ⟨φ⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven P
  have hcard : 2 * 2 ^ m = 8 := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr φ.toEquiv, hP8]
  have hm : m = 2 := by
    have h4 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h4
  subst hm
  have := hE.1
  have hcomm : ∀ a b : DihedralGroup (2 ^ 2), a * b = b * a := by
    intro a b
    have ha : ((φ.symm a : P) : alternatingGroup (Fin 7)) ∈ E := by
      rw [hEP]
      exact (φ.symm a).2
    have hb : ((φ.symm b : P) : alternatingGroup (Fin 7)) ∈ E := by
      rw [hEP]
      exact (φ.symm b).2
    have h1 : ((φ.symm a : P) : alternatingGroup (Fin 7)) * (φ.symm b : P) =
        (φ.symm b : P) * (φ.symm a : P) := by
      have h2 := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : E) ⟨_, hb⟩)
      simpa using h2
    apply φ.symm.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h1
  exact absurd (hcomm (DihedralGroup.r 1) (DihedralGroup.sr 0)) (by decide)

theorem pRank_two_of_alternating_six_seven {n : ℕ} (hn : n = 6 ∨ n = 7) {Q : Type*} [Group Q]
    [Finite Q] (e : Q ≃* alternatingGroup (Fin n)) : CFSG.pRank 2 Q = 2 := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  have h67 : Open.pRank 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) ≤
      Open.pRank 2 (⊤ : Subgroup (alternatingGroup (Fin 7))) :=
    SectionRank.pRank_top_le_of_injective (by norm_num) alternatingSixToSeven
      alternatingSixToSeven_injective
  rcases hn with rfl | rfl
  · exact le_antisymm (h67.trans open_pRank_alternatingGroup_seven_le_two)
      two_le_open_pRank_alternatingGroup_six
  · exact le_antisymm open_pRank_alternatingGroup_seven_le_two
      (two_le_open_pRank_alternatingGroup_six.trans h67)

theorem card_le_forty_eight_of_isSporadic_M11
    {G : Type} [Group G] [Finite G]
    (hM : Blueprint.NativeSporadic.IsSporadic G .M11) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({t} : Set G)) : Nat.card H ≤ 48 := by
  obtain ⟨e⟩ := hM
  let e' : G ≃* Blueprint.NativeSporadic.M11 := e
  have hez : orderOf (e' t) = 2 := (orderOf_injective e'.toMonoidHom e'.injective t).trans ht
  obtain ⟨hc, hN⟩ :=
    Semidihedral.ProperSubgroupRegularity.m11_involution_centralizer_card_and_odd_core (e' t) hez
  obtain ⟨hc', -⟩ :=
    Semidihedral.ProperSubgroupRegularity.centralizer_card_and_core_of_equiv e' t hc hN
  rw [← hc']
  exact Subgroup.card_le_of_le hH

theorem false_of_isSporadic_M11_of_le_centralizer
    {G : Type} [Group G] [Finite G]
    (hM : Blueprint.NativeSporadic.IsSporadic G .M11) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({t} : Set G)) (h60 : 60 ≤ Nat.card H) :
    False := by
  have := card_le_forty_eight_of_isSporadic_M11 hM ht hH
  omega

theorem isPComponent_two_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (ht : t ∈ Subgroup.centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hev : 2 ∣ Nat.card L) :
    L ≤ Subgroup.centralizer ({t} : Set G) ∧
      CFSG.IsPComponent 2 (L.subgroupOf (Subgroup.centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLT, hnorm, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL ht ht2
  refine ⟨hLT, ?_⟩
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have e : (L.subgroupOf C) ≃* L := Subgroup.subgroupOfEquivOfLe hLT
  have hq : CFSG.IsQuasisimple (L.subgroupOf C) :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      (ComponentClassification.Components.quasisimple_of_equiv e hL.1)
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    ⟨hq, hnorm.isSubnormal⟩ ?_
  intro hle
  have h1 : Nat.card (L.subgroupOf C) ∣ Nat.card (CFSG.pPrimeCore 2 C) :=
    Subgroup.card_dvd_of_le hle
  have h2 := CFSG.pPrimeCore_coprime_card (p := 2) (G := C)
  have h3 : 2 ∣ Nat.card (L.subgroupOf C) := by
    rw [Nat.card_congr e.toEquiv]
    exact hev
  exact absurd (Nat.Coprime.eq_one_of_dvd h2 (h3.trans h1)) (by norm_num)

end CFSG.OddStandard

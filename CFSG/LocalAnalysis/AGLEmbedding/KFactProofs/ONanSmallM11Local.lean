module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.GH74.KGroups.M11Tables
public import Certificates.Certificate9623

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Certificates.ONanSmallM11 CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.Blueprint

section Model


theorem m11_facts :
    m11x ∈ NativeSporadic.M11 ∧ m11y ∈ NativeSporadic.M11 ∧
    m11s ∈ NativeSporadic.M11 ∧ m11E.Nodup ∧
    (∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) ∧ (∀ a ∈ m11E, a⁻¹ ∈ m11E) ∧
    m11x ^ 3 = 1 ∧ m11y ^ 3 = 1 ∧ m11x * m11y = m11y * m11x ∧ m11x ≠ 1 ∧
    m11y ∉ ([1, m11x, m11x ^ 2] : List (Equiv.Perm (Fin 11))) ∧
    (∀ g ∈ NativeSporadic.M11, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1) ∧
    (∀ g ∈ NativeSporadic.M11, (g * m11x * g⁻¹ ∈ m11E ∧ g * m11y * g⁻¹ ∈ m11E) ↔
      ((g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0))) ∧
    (∀ g ∈ NativeSporadic.M11, g * m11x = m11x * g → g * m11y = m11y * g → g ∈ m11E) ∧
    (∀ v ∈ m11E, v ≠ 1 → ∀ t ∈ m11E, t ≠ 1 → ∃ n ∈ NativeSporadic.M11,
      ((n 0 = 0 ∧ n 1 = 1) ∨ (n 0 = 1 ∧ n 1 = 0)) ∧ n * v * n⁻¹ = t) ∧
    (((m11s 0 = 0 ∧ m11s 1 = 1) ∨ (m11s 0 = 1 ∧ m11s 1 = 0)) ∧ m11s ^ 8 = 1 ∧ m11s ^ 4 ≠ 1 ∧
      ∀ t ∈ m11E, t ≠ 1 → m11s * t * m11s⁻¹ ≠ t) :=
  Certificates.certificate9623

@[expose] def m11Sub : Subgroup (Equiv.Perm (Fin 11)) := Subgroup.closure {m11x, m11y}

theorem mem_m11Sub_iff (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E)
    (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E) {g : Equiv.Perm (Fin 11)} : g ∈ m11Sub ↔ g ∈ m11E := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl <;> simp [m11E]
    | one => simp [m11E]
    | mul a b _ _ ha hb => exact hmul a ha b hb
    | inv a _ ha => exact hinv a ha
  · intro hg
    have hx : m11x ∈ m11Sub := Subgroup.subset_closure (Set.mem_insert _ _)
    have hy : m11y ∈ m11Sub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hx
    · exact pow_mem hx 2
    · exact hy
    · exact mul_mem hx hy
    · exact mul_mem (pow_mem hx 2) hy
    · exact pow_mem hy 2
    · exact mul_mem hx (pow_mem hy 2)
    · exact mul_mem (pow_mem hx 2) (pow_mem hy 2)

theorem card_m11Sub (hnodup : m11E.Nodup) (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E)
    (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E) : Nat.card m11Sub = 9 := by
  have h : (m11Sub : Set (Equiv.Perm (Fin 11))) = (m11E.toFinset : Set (Equiv.Perm (Fin 11))) := by
    ext g
    simp [mem_m11Sub_iff hmul hinv]
  have h1 : Nat.card m11Sub = (m11Sub : Set (Equiv.Perm (Fin 11))).ncard :=
    Nat.card_congr (Equiv.refl _)
  rw [h1, h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
  rfl

theorem exists_smul_four_of_card {G : Subgroup (Equiv.Perm (Fin 11))} (hcard : Nat.card G = 7920)
    (hfree : ∀ g ∈ G, g 0 = 0 → g 1 = 1 → g 2 = 2 → g 3 = 3 → g = 1) :
    ∀ u v w z : Fin 11, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : G, g • (0 : Fin 11) = u ∧ g • (1 : Fin 11) = v ∧ g • (2 : Fin 11) = w ∧
        g • (3 : Fin 11) = z := by
  classical
  let c : Fin 4 ↪ Fin 11 := Fin.castLEEmb (by norm_num)
  let f : G → (Fin 4 ↪ Fin 11) := fun g => c.trans (g : Equiv.Perm (Fin 11)).toEmbedding
  have hfinj : Function.Injective f := by
    intro g h hgh
    have h0 : (g : Equiv.Perm (Fin 11)) 0 = (h : Equiv.Perm (Fin 11)) 0 :=
      DFunLike.congr_fun hgh 0
    have h1 : (g : Equiv.Perm (Fin 11)) 1 = (h : Equiv.Perm (Fin 11)) 1 :=
      DFunLike.congr_fun hgh 1
    have h2 : (g : Equiv.Perm (Fin 11)) 2 = (h : Equiv.Perm (Fin 11)) 2 :=
      DFunLike.congr_fun hgh 2
    have h3 : (g : Equiv.Perm (Fin 11)) 3 = (h : Equiv.Perm (Fin 11)) 3 :=
      DFunLike.congr_fun hgh 3
    have hmem : (h : Equiv.Perm (Fin 11))⁻¹ * (g : Equiv.Perm (Fin 11)) ∈ G :=
      G.mul_mem (G.inv_mem h.2) g.2
    have key := hfree _ hmem
      (by rw [Equiv.Perm.mul_apply, h0]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h1]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h2]; exact Equiv.symm_apply_apply _ _)
      (by rw [Equiv.Perm.mul_apply, h3]; exact Equiv.symm_apply_apply _ _)
    apply Subtype.ext
    exact (inv_mul_eq_one.1 key).symm
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_embedding_eq]
    simp [Nat.descFactorial]
  intro u v w z huv huw huz hvw hvz hwz
  let t : Fin 4 ↪ Fin 11 := ⟨![u, v, w, z], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> tauto⟩
  obtain ⟨g, hg⟩ := hbij.2 t
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact DFunLike.congr_fun hg 0
  · exact DFunLike.congr_fun hg 1
  · exact DFunLike.congr_fun hg 2
  · exact DFunLike.congr_fun hg 3

theorem isPreprimitive_duads_of_four {G : Subgroup (Equiv.Perm (Fin 11))}
    (h4 : ∀ u v w z : Fin 11, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : G, g • (0 : Fin 11) = u ∧ g • (1 : Fin 11) = v ∧ g • (2 : Fin 11) = w ∧
        g • (3 : Fin 11) = z) :
    MulAction.IsPreprimitive G (Set.powersetCard (Fin 11) 2) := by
  have hext : ∀ a b : Fin 11, a ≠ b → ∃ c d : Fin 11, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
    decide
  have hext3 : ∀ a b c : Fin 11, a ≠ b → a ≠ c → b ≠ c → ∃ d : Fin 11, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    decide
  have h2 : MulAction.IsMultiplyPretransitive G (Fin 11) 2 := by
    refine MulAction.is_two_pretransitive_iff.2 fun {a b a' b'} hab hab' => ?_
    obtain ⟨c, d, hca, hcb, hda, hdb, hcd⟩ := hext a b hab
    obtain ⟨c', d', hca', hcb', hda', hdb', hcd'⟩ := hext a' b' hab'
    obtain ⟨g, g0, g1, -, -⟩ := h4 a b c d hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb)
      (Ne.symm hdb) hcd
    obtain ⟨g', g0', g1', -, -⟩ := h4 a' b' c' d' hab' (Ne.symm hca') (Ne.symm hda')
      (Ne.symm hcb') (Ne.symm hdb') hcd'
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · rw [mul_smul, inv_smul_eq_iff.2 g0.symm, g0']
    · rw [mul_smul, inv_smul_eq_iff.2 g1.symm, g1']
  have hpre := Set.powersetCard.isPretransitive_of_isMultiplyPretransitive G h2
  refine CFSG.Sporadic.Mathieu.isPreprimitive_duads (G := G) 0 1 2 3 4 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro u v w huv huw hvw
    obtain ⟨z, hzu, hzv, hzw⟩ := hext3 u v w huv huw hvw
    obtain ⟨g, g0, g1, g2, -⟩ := h4 u v w z huv huw (Ne.symm hzu) hvw (Ne.symm hzv) (Ne.symm hzw)
    exact ⟨g, g0, g1, g2⟩
  · intro u v w z huv huw huz hvw hvz hwz
    exact h4 u v w z huv huw huz hvw hvz hwz

end Model

section Local


@[expose] def m11T0 : Subgroup ↥NativeSporadic.M11 := m11Sub.subgroupOf NativeSporadic.M11

theorem mem_m11T0_iff {g : ↥NativeSporadic.M11} : g ∈ m11T0 ↔ (g : Equiv.Perm (Fin 11)) ∈ m11Sub :=
  Iff.rfl

theorem card_m11T0 : Nat.card m11T0 = 9 := by
  obtain ⟨-, -, -, hnodup, hmul, hinv, -⟩ := m11_facts
  have hx : m11x ∈ NativeSporadic.M11 := (m11_facts).1
  have hy : m11y ∈ NativeSporadic.M11 := (m11_facts).2.1
  have hle : m11Sub ≤ NativeSporadic.M11 := by
    rw [m11Sub, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hx, hy]
  rw [m11T0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact card_m11Sub hnodup hmul hinv

theorem exists_sylow_m11T0 :
    ∃ T : Sylow 3 ↥NativeSporadic.M11, (T : Subgroup ↥NativeSporadic.M11) = m11T0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card m11T0 = 3 ^ 2 := by rw [card_m11T0]; norm_num
  have hP : IsPGroup 3 m11T0 := IsPGroup.of_card hc
  have hM : Nat.card ↥NativeSporadic.M11 = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have hidx : ¬ 3 ∣ m11T0.index := by
    have h := m11T0.index_mul_card
    rw [hM, hc] at h
    have : m11T0.index = 880 := by omega
    rw [this]
    norm_num
  exact ⟨hP.toSylow hidx, rfl⟩

theorem mem_normalizer_m11T0_iff {g : ↥NativeSporadic.M11} :
    g ∈ Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ↔
      ((g : Equiv.Perm (Fin 11)) * m11x * (g : Equiv.Perm (Fin 11))⁻¹ ∈ m11E ∧
        (g : Equiv.Perm (Fin 11)) * m11y * (g : Equiv.Perm (Fin 11))⁻¹ ∈ m11E) := by
  obtain ⟨hx, hy, -, -, hmul, hinv, -⟩ := m11_facts
  have hxT : (⟨m11x, hx⟩ : ↥NativeSporadic.M11) ∈ m11T0 := by
    rw [mem_m11T0_iff]; exact (mem_m11Sub_iff hmul hinv).2 (by simp [m11E])
  have hyT : (⟨m11y, hy⟩ : ↥NativeSporadic.M11) ∈ m11T0 := by
    rw [mem_m11T0_iff]; exact (mem_m11Sub_iff hmul hinv).2 (by simp [m11E])
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hxT
    have h2 := (Subgroup.mem_normalizer_iff.1 hg _).1 hyT
    rw [mem_m11T0_iff, mem_m11Sub_iff hmul hinv] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ h ∈ m11Sub,
        (g : Equiv.Perm (Fin 11)) * h * (g : Equiv.Perm (Fin 11))⁻¹ ∈ m11Sub := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem s hs =>
        rcases hs with rfl | rfl
        · exact (mem_m11Sub_iff hmul hinv).2 h1
        · exact (mem_m11Sub_iff hmul hinv).2 h2
      | one => simp [one_mem]
      | mul a b _ _ ha hb =>
        have : (g : Equiv.Perm (Fin 11)) * (a * b) * (g : Equiv.Perm (Fin 11))⁻¹ =
            ((g : Equiv.Perm (Fin 11)) * a * (g : Equiv.Perm (Fin 11))⁻¹) *
              ((g : Equiv.Perm (Fin 11)) * b * (g : Equiv.Perm (Fin 11))⁻¹) := by group
        rw [this]
        exact mul_mem ha hb
      | inv a _ ha =>
        have : (g : Equiv.Perm (Fin 11)) * a⁻¹ * (g : Equiv.Perm (Fin 11))⁻¹ =
            ((g : Equiv.Perm (Fin 11)) * a * (g : Equiv.Perm (Fin 11))⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem ha
    have : Finite ((m11T0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) :=
      inferInstance
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [SetLike.mem_coe, mem_m11T0_iff] at hn ⊢
    simpa using key _ hn

theorem mem_stabilizer_duad_iff (g : ↥NativeSporadic.M11) (h01 : (0 : Fin 11) ≠ 1) :
    g ∈ MulAction.stabilizer ↥NativeSporadic.M11
        (CFSG.Sporadic.Mathieu.duad (0 : Fin 11) 1 h01) ↔
      (((g : Equiv.Perm (Fin 11)) 0 = 0 ∧ (g : Equiv.Perm (Fin 11)) 1 = 1) ∨
        ((g : Equiv.Perm (Fin 11)) 0 = 1 ∧ (g : Equiv.Perm (Fin 11)) 1 = 0)) := by
  rw [MulAction.mem_stabilizer_iff]
  have key := CFSG.Sporadic.Mathieu.smul_duad (G := ↥NativeSporadic.M11) g (0 : Fin 11) 1 h01
  constructor
  · intro h
    have h' := Subtype.ext_iff.1 (key.symm.trans h)
    change ({g • (0 : Fin 11), g • (1 : Fin 11)} : Finset (Fin 11)) = {0, 1} at h'
    have h'' := congrArg (fun s : Finset (Fin 11) => (s : Set (Fin 11))) h'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff] at h''
    exact h''
  · intro h
    apply key.trans
    apply Subtype.ext
    change ({g • (0 : Fin 11), g • (1 : Fin 11)} : Finset (Fin 11)) = {0, 1}
    rw [← Finset.coe_inj]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff]
    exact h

theorem m11x_mem_m11T0 : (⟨m11x, (m11_facts).1⟩ : ↥NativeSporadic.M11) ∈ m11T0 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m11y_mem_m11T0 : (⟨m11y, (m11_facts).2.1⟩ : ↥NativeSporadic.M11) ∈ m11T0 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_m11T0_iff_mem_m11E {g : ↥NativeSporadic.M11} :
    g ∈ m11T0 ↔ (g : Equiv.Perm (Fin 11)) ∈ m11E := by
  obtain ⟨-, -, -, -, hmul, hinv, -⟩ := m11_facts
  rw [mem_m11T0_iff, mem_m11Sub_iff hmul hinv]

theorem m11_isPreprimitive_duads :
    MulAction.IsPreprimitive ↥NativeSporadic.M11 (Set.powersetCard (Fin 11) 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfree, -⟩ := m11_facts
  exact isPreprimitive_duads_of_four
    (exists_smul_four_of_card CFSG.Sporadic.Mathieu.card_M11 hfree)

theorem nontrivial_duads : Nontrivial (Set.powersetCard (Fin 11) 2) :=
  ⟨CFSG.Sporadic.Mathieu.duad 0 1 (by decide), CFSG.Sporadic.Mathieu.duad 0 2 (by decide),
    fun h => absurd (congrArg Subtype.val h)
      (by change ({0, 1} : Finset (Fin 11)) ≠ {0, 2}; decide)⟩

theorem normalizer_m11T0 :
    Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) =
      MulAction.stabilizer ↥NativeSporadic.M11
        (CFSG.Sporadic.Mathieu.duad (0 : Fin 11) 1 (by decide)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnorm, -⟩ := m11_facts
  ext g
  rw [mem_normalizer_m11T0_iff, mem_stabilizer_duad_iff g (by decide)]
  exact hnorm g g.2

theorem isCoatom_normalizer_m11T0 :
    IsCoatom (Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) :
      Set ↥NativeSporadic.M11)) := by
  rw [normalizer_m11T0]
  have := m11_isPreprimitive_duads
  have := nontrivial_duads
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _

theorem card_normalizer_m11T0 :
    Nat.card (Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) :
      Set ↥NativeSporadic.M11)) = 144 := by
  rw [normalizer_m11T0]
  have := m11_isPreprimitive_duads
  have hidx := MulAction.index_stabilizer_of_transitive ↥NativeSporadic.M11
    (CFSG.Sporadic.Mathieu.duad (0 : Fin 11) 1 (by decide))
  rw [Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin] at hidx
  have h := Subgroup.index_mul_card
    (MulAction.stabilizer ↥NativeSporadic.M11
      (CFSG.Sporadic.Mathieu.duad (0 : Fin 11) 1 (by decide)))
  rw [hidx, CFSG.Sporadic.Mathieu.card_M11] at h
  rw [show Nat.choose 11 2 = 55 by decide] at h
  omega

theorem isSolvable_normalizer_m11T0 :
    Group.IsSolvable (Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) :
      Set ↥NativeSporadic.M11)) := by
  refine CFSG.GH74.KGroups.isSolvable_of_two_primes ?_
  rw [card_normalizer_m11T0]
  decide +kernel

theorem centralizer_le_m11T0 (g : ↥NativeSporadic.M11)
    (hg : ∀ t ∈ m11T0, g * t = t * g) : g ∈ m11T0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcent, -⟩ := m11_facts
  have h1 := congrArg Subtype.val (hg _ m11x_mem_m11T0)
  have h2 := congrArg Subtype.val (hg _ m11y_mem_m11T0)
  exact mem_m11T0_iff_mem_m11E.2 (hcent g g.2 h1 h2)

theorem center_m11 : Subgroup.center ↥NativeSporadic.M11 = ⊥ := by
  obtain ⟨hx, -, hs, -, -, -, -, -, -, hx1, -, -, -, -, -, -, -, -, hstor⟩ := m11_facts
  have hsimple : IsSimpleGroup ↥NativeSporadic.M11 :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hnab : ∃ a b : ↥NativeSporadic.M11, a * b ≠ b * a := by
    refine ⟨⟨m11s, hs⟩, ⟨m11x, hx⟩, fun h => ?_⟩
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
    change m11s * m11x = m11x * m11s at h1
    refine hstor m11x (mem_m11T0_iff_mem_m11E.1 m11x_mem_m11T0) hx1 ?_
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  exact center_eq_bot_of_isSimpleGroup_nonabelian (L := ↥NativeSporadic.M11) hnab

theorem torus_m11T0 : ∃ T₀ : Subgroup ↥NativeSporadic.M11,
    T₀ ≤ Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) ∧
    Nat.Coprime 3 (Nat.card T₀) ∧
      m11T0 ⊓ Subgroup.centralizer (T₀ : Set ↥NativeSporadic.M11) = ⊥ := by
  obtain ⟨-, -, hs, -, -, -, -, -, -, -, -, -, -, -, -, hst, hs8, hs4, hstor⟩ := m11_facts
  refine ⟨Subgroup.zpowers ⟨m11s, hs⟩, ?_, ?_, ?_⟩
  · rw [normalizer_m11T0, Subgroup.zpowers_le]
    exact (mem_stabilizer_duad_iff _ (by decide)).2 hst
  · rw [Nat.card_zpowers]
    have h4 : ¬ (⟨m11s, hs⟩ : ↥NativeSporadic.M11) ^ 4 = 1 := fun h => by
      have := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact hs4 this
    have h8 : (⟨m11s, hs⟩ : ↥NativeSporadic.M11) ^ 8 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs8)
    have : orderOf (⟨m11s, hs⟩ : ↥NativeSporadic.M11) = 2 ^ (2 + 1) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime_pow (n := 2) (by simpa using h4) (by simpa using h8)
    rw [this]
    norm_num
  · rw [eq_bot_iff]
    rintro g ⟨hgT, hgC⟩
    rw [Subgroup.mem_bot]
    have hcomm := Subgroup.mem_centralizer_iff.1 hgC ⟨m11s, hs⟩ (Subgroup.mem_zpowers _)
    have h1 : m11s * (g : Equiv.Perm (Fin 11)) = (g : Equiv.Perm (Fin 11)) * m11s :=
      congrArg Subtype.val hcomm
    by_contra hg1
    refine hstor g (mem_m11T0_iff_mem_m11E.1 hgT) (fun h => hg1 (Subtype.ext h)) ?_
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem eq_m11T0_of_normalizer_le (V : Subgroup ↥NativeSporadic.M11) (hVT : V ≤ m11T0)
    (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) :
      Set ↥NativeSporadic.M11) ≤ Subgroup.normalizer (V : Set ↥NativeSporadic.M11)) :
    V = m11T0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, htrans, -⟩ := m11_facts
  refine le_antisymm hVT fun t ht => ?_
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV
  have hvK : (v : ↥NativeSporadic.M11) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvP : ((v : ↥NativeSporadic.M11) : Equiv.Perm (Fin 11)) ≠ 1 := fun h =>
    hvK (Subtype.ext h)
  by_cases ht1 : t = 1
  · rw [ht1]
    exact one_mem V
  · have htP : (t : Equiv.Perm (Fin 11)) ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨n, hn, hnst, hnvt⟩ := htrans _ (mem_m11T0_iff_mem_m11E.1 (hVT v.2)) hvP _
      (mem_m11T0_iff_mem_m11E.1 ht) htP
    have hnN : (⟨n, hn⟩ : ↥NativeSporadic.M11) ∈ Subgroup.normalizer
        ((m11T0 : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) := by
      rw [normalizer_m11T0]
      exact (mem_stabilizer_duad_iff _ (by decide)).2 hnst
    have h1 := (Subgroup.mem_normalizer_iff.1 (hVN hnN) v).1 v.2
    have h2 : (⟨n, hn⟩ : ↥NativeSporadic.M11) * (v : ↥NativeSporadic.M11) *
        (⟨n, hn⟩ : ↥NativeSporadic.M11)⁻¹ = t := Subtype.ext hnvt
    rw [h2] at h1
    exact h1

theorem sporCore_m11T0 {T : Sylow 3 ↥NativeSporadic.M11}
    (hT : (T : Subgroup ↥NativeSporadic.M11) = m11T0) :
    SporCore 3 ↥NativeSporadic.M11 T := by
  refine ⟨?_, center_m11, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, card_m11T0]
    norm_num
  · rw [hT]
    exact centralizer_le_m11T0
  · rw [hT]
    exact isCoatom_normalizer_m11T0
  · rw [hT]
    exact isSolvable_normalizer_m11T0
  · rw [hT]
    exact torus_m11T0
  · intro V hVT hV hVN
    rw [hT] at hVT hVN ⊢
    exact Or.inl (eq_m11T0_of_normalizer_le V hVT hV hVN)

theorem sporCore_m11 {K : Type} [Group K] [Finite K] (hK : IsSporadicGroup .M11 K)
    (T : Sylow 3 K) : SporCore 3 K T := by
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  obtain ⟨T₀, hT₀⟩ := exists_sylow_m11T0
  exact SporCore.of_equiv_all Nat.prime_three e ⟨T₀, sporCore_m11T0 hT₀⟩ T

theorem autFixInner_m11 {K : Type} [Group K] [Finite K] (hK : IsSporadicGroup .M11 K)
    (T : Sylow 3 K) : AutFixInner 3 K T := by
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  rintro f -
  obtain ⟨k, hk⟩ := CFSG.GH74.KGroups.M11.out_trivial ⟨e⟩ f
  exact ⟨k, MulEquiv.ext fun x => (hk x).symm⟩

end Local

end CFSG.AGLEmbedding.KFactProofs.SmallIdent

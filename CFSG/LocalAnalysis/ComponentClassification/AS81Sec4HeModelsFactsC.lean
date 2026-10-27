module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsFacts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeBridge
import all CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa

theorem all_range_congr {N : ℕ} {f g : ℕ → Bool} (h : ∀ v < N, f v = g v) :
    (List.range N).all f = (List.range N).all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun v hv => by rw [h v (List.mem_range.1 hv)]

theorem stabW_congr {k : ℕ} (hk : 2 ^ k ≤ 32) {t u : Array ℕ} {x : Equiv.Perm (Fin 32)}
    (ht : Rep 32 t x) (hu : Rep 32 u x) : stabW k t = stabW k u := by
  unfold stabW
  exact all_range_congr fun v hv => by
    simp only [ht.apply (hv.trans_le hk), hu.apply (hv.trans_le hk)]

theorem unipW_congr {k : ℕ} (hk : 2 ^ k ≤ 32) {t u : Array ℕ} {x : Equiv.Perm (Fin 32)}
    (ht : Rep 32 t x) (hu : Rep 32 u x) : unipW k t = unipW k u := by
  have he : ∀ v < 32, t[v]! = u[v]! := fun v hv => by rw [ht.apply hv, hu.apply hv]
  unfold unipW
  congr 1
  · exact all_range_congr fun v hv => by simp only [he v (hv.trans_le hk)]
  · exact all_range_congr fun v hv => by simp only [he v hv]

theorem le_of_normal_of_card_two {G : Type*} [Group G] {X S P : Subgroup G} (hXP : X ≤ P)
    (hSP : S ≤ P) (hn : ∀ b ∈ P, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hX : Nat.card X = 64)
    (hS : Nat.card S = 1024) (hP : Nat.card P = 3072) : X ≤ S := by
  have hN : (X.subgroupOf P).Normal := ⟨fun x hx b => hn b b.2 x hx⟩
  have hcS : Nat.card (S.subgroupOf P) = 1024 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv, hS]
  have hpX : IsPGroup 2 (X.subgroupOf P) := IsPGroup.of_card (n := 6) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv, hX]
    norm_num)
  have hpS : IsPGroup 2 (S.subgroupOf P) := IsPGroup.of_card (n := 10) (by
    rw [hcS]
    norm_num)
  have hidx : (S.subgroupOf P).index = 3 := by
    have := (S.subgroupOf P).card_mul_index
    rw [hcS, hP] at this
    omega
  have hle := hpX.le_sylow_of_normal (hpS.toSylow (by rw [hidx]; decide))
  intro x hx
  exact hle (show (⟨x, hXP hx⟩ : P) ∈ X.subgroupOf P from hx)

section C

variable (h : heModelCheck = true)
include h

theorem enum_PC : enumCheckK 32 base32 hePCGens 21504 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.1
theorem enum_BC : enumCheckK 32 base32 heBCGens 1024 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.1
theorem enum_P0 : enumCheckK 32 base32 heP12CGens 3072 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.1
theorem enum_P1 : enumCheckK 32 base32 heP13CGens 3072 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.1
theorem enum_U0 : enumCheckK 32 base32 heECGens 64 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.2.1
theorem enum_U1 : enumCheckK 32 base32 heFCGens 64 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.2.2.1
theorem rep_TC : Rep 32 heTCArr heTC :=
  rep_of_validA (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem heCheckC_parts :
    inLN 32 (eltsK 32 base32 hePCGens 21504) heTCArr = true ∧
      (eltsK 32 base32 hePCGens 21504).all (fun x => !(hePCGens.all (commN 32 x)) ||
        eqA 32 x (idA 32) || eqA 32 x heTCArr) = true ∧
      heBCGens.all (inLN 32 (eltsK 32 base32 heP12CGens 3072)) = true ∧
      heBCGens.all (inLN 32 (eltsK 32 base32 heP13CGens 3072)) = true ∧
      heP12CGens.all (inLN 32 (eltsK 32 base32 hePCGens 21504)) = true ∧
      heP13CGens.all (inLN 32 (eltsK 32 base32 hePCGens 21504)) = true ∧
      heECGens.all (inLN 32 (eltsK 32 base32 heP12CGens 3072)) = true ∧
      heFCGens.all (inLN 32 (eltsK 32 base32 heP13CGens 3072)) = true ∧
      heECGens.all (inLN 32 (eltsK 32 base32 heBCGens 1024)) = true ∧
      heFCGens.all (inLN 32 (eltsK 32 base32 heBCGens 1024)) = true ∧
      (eltsK 32 base32 heECGens 64).all (fun x => eqA 32 (mulN 32 x x) (idA 32)) = true ∧
      (eltsK 32 base32 heFCGens 64).all (fun x => eqA 32 (mulN 32 x x) (idA 32)) = true ∧
      inLN 32 (eltsK 32 base32 heECGens 64) heTCArr = true ∧
      inLN 32 (eltsK 32 base32 heFCGens 64) heTCArr = true ∧
      uniqEN 32 (eltsK 32 base32 heBCGens 1024) (eltsK 32 base32 heECGens 64)
        (eltsK 32 base32 heFCGens 64) = true ∧
      heP12CGens.any (fun g => heFCGens.any fun f =>
        !(inLN 32 (eltsK 32 base32 heFCGens 64) (conjA 32 g f))) = true ∧
      heP13CGens.any (fun g => heECGens.any fun f =>
        !(inLN 32 (eltsK 32 base32 heECGens 64) (conjA 32 g f))) = true ∧
      (eltsK 32 base32 hePCGens 21504).all (fun x => !(heECGens.all (commN 32 x)) ||
        inLN 32 (eltsK 32 base32 heECGens 64) x) = true ∧
      (eltsK 32 base32 hePCGens 21504).all (fun x => !(heFCGens.all (commN 32 x)) ||
        inLN 32 (eltsK 32 base32 heFCGens 64) x) = true ∧
      heP12CGens.all (normsN 32 (eltsK 32 base32 heECGens 64) heECGens) = true ∧
      heP13CGens.all (normsN 32 (eltsK 32 base32 heFCGens 64) heFCGens) = true := by
  have h2 := (heModelCheck_parts h).2.2.2.2.2.1
  simp only [heCheckC, heCL_eq, heBCL_eq, heP0L_eq, heP1L_eq, heU0L_eq, heU1L_eq,
    Bool.and_eq_true, and_assoc] at h2
  exact h2

theorem heCheckCount_parts :
    ((eltsK 32 base32 hePCGens 21504).filter (stabW 2)).length = 3072 ∧
      ((eltsK 32 base32 hePCGens 21504).filter (stabW 3)).length = 3072 ∧
      (eltsK 32 base32 heP12CGens 3072).all (stabW 2) = true ∧
      (eltsK 32 base32 heP13CGens 3072).all (stabW 3) = true ∧
      ((eltsK 32 base32 heP12CGens 3072).filter (stabW 3)).length = 1024 ∧
      ((eltsK 32 base32 hePCGens 21504).filter (unipW 2)).length = 64 ∧
      ((eltsK 32 base32 hePCGens 21504).filter (unipW 3)).length = 64 ∧
      (eltsK 32 base32 heECGens 64).all (unipW 2) = true ∧
      (eltsK 32 base32 heFCGens 64).all (unipW 3) = true ∧
      ((eltsK 32 base32 hePCGens 21504).filter fun x =>
        heECGens.all fun f => unipW 2 (conjA 32 x f)).length = 3072 ∧
      ((eltsK 32 base32 hePCGens 21504).filter fun x =>
        heFCGens.all fun f => unipW 3 (conjA 32 x f)).length = 3072 := by
  have h2 := (heModelCheck_parts h).2.2.2.2.2.2
  simp only [heCheckCount, heCL_eq, heP0L_eq, heP1L_eq, heU0L_eq, heU1L_eq, Bool.and_eq_true,
    beq_iff_eq, and_assoc] at h2
  exact h2

theorem card_PC_of : Nat.card hePC = 21504 :=
  card_grpNK base32_lt (enum_PC h)

theorem TC_mem_of : heTC ∈ hePC :=
  mem_of_inLNK base32_lt (enum_PC h) (heCheckC_parts h).1 (rep_TC h)

theorem center_PC_of : ∀ x ∈ hePC, (∀ y ∈ hePC, x * y = y * x) → x = 1 ∨ x = heTC := by
  intro x hx hc
  obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base32_lt (enum_PC h) hx
  have hb := List.all_eq_true.1 (heCheckC_parts h).2.1 t ht
  have hall : hePCGens.all (commN 32 t) = true := List.all_eq_true.2 fun a ha =>
    (commN_iff hrt (rep_of_validA (validA_of_mem_gensK (enum_PC h) ha))).2
      (hc _ (gen_mem_grpN ha))
  rw [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hb
  exact hb.imp (eq_of_eqA hrt rep_idA) (eq_of_eqA hrt (rep_TC h))

theorem BC_le_P_of : ∀ s, heBC ≤ heP12C s := by
  obtain ⟨-, -, hb0, hb1, -⟩ := heCheckC_parts h
  intro s
  cases s
  · exact grpN_le_of_allK base32_lt (enum_P0 h)
      (fun _ ha => validA_of_mem_gensK (enum_BC h) ha) hb0
  · exact grpN_le_of_allK base32_lt (enum_P1 h)
      (fun _ ha => validA_of_mem_gensK (enum_BC h) ha) hb1

theorem P_le_PC_of : ∀ s, heP12C s ≤ hePC := by
  obtain ⟨-, -, -, -, hp0, hp1, -⟩ := heCheckC_parts h
  intro s
  cases s
  · exact grpN_le_of_allK base32_lt (enum_PC h)
      (fun _ ha => validA_of_mem_gensK (enum_P0 h) ha) hp0
  · exact grpN_le_of_allK base32_lt (enum_PC h)
      (fun _ ha => validA_of_mem_gensK (enum_P1 h) ha) hp1

theorem card_P12C_of : ∀ s, Nat.card (heP12C s) = 3072 := by
  intro s
  cases s
  · exact card_grpNK base32_lt (enum_P0 h)
  · exact card_grpNK base32_lt (enum_P1 h)

theorem P12C_inf_of : heP12C false ⊓ heP12C true = heBC := by
  obtain ⟨-, -, -, hP1, h1024, -⟩ := heCheckCount_parts h
  refine (Subgroup.eq_of_le_of_card_ge (le_inf (BC_le_P_of h false) (BC_le_P_of h true))
    ?_).symm
  rw [card_grpNK base32_lt (enum_BC h), ← h1024]
  refine card_le_length (S := ((heP12C false ⊓ heP12C true : Subgroup _) :
    Set (Equiv.Perm (Fin 32)))) ?_
  rintro x ⟨hx0, hx1⟩
  obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base32_lt (enum_P0 h) hx0
  obtain ⟨u, hu, hru, -⟩ := exists_rep_of_memK base32_lt (enum_P1 h) hx1
  refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, hrt⟩
  rw [stabW_congr (by norm_num) hrt hru]
  exact List.all_eq_true.1 hP1 u hu

theorem EC_le_of : ∀ s, heEC s ≤ heP12C s := by
  obtain ⟨-, -, -, -, -, -, hl0, hl1, -⟩ := heCheckC_parts h
  intro s
  cases s
  · exact grpN_le_of_allK base32_lt (enum_P0 h)
      (fun _ ha => validA_of_mem_gensK (enum_U0 h) ha) hl0
  · exact grpN_le_of_allK base32_lt (enum_P1 h)
      (fun _ ha => validA_of_mem_gensK (enum_U1 h) ha) hl1

theorem EC_le_BC_of : ∀ s, heEC s ≤ heBC := by
  obtain ⟨-, -, -, -, -, -, -, -, hl0, hl1, -⟩ := heCheckC_parts h
  intro s
  cases s
  · exact grpN_le_of_allK base32_lt (enum_BC h)
      (fun _ ha => validA_of_mem_gensK (enum_U0 h) ha) hl0
  · exact grpN_le_of_allK base32_lt (enum_BC h)
      (fun _ ha => validA_of_mem_gensK (enum_U1 h) ha) hl1

theorem EC_sq_of : ∀ s, ∀ x ∈ heEC s, x * x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hq0, hq1, -⟩ := heCheckC_parts h
  intro s x hx
  cases s
  · obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base32_lt (enum_U0 h) hx
    exact eq_of_eqA (rep_mulN hrt hrt) rep_idA (List.all_eq_true.1 hq0 t ht)
  · obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base32_lt (enum_U1 h) hx
    exact eq_of_eqA (rep_mulN hrt hrt) rep_idA (List.all_eq_true.1 hq1 t ht)

theorem card_EC_of : ∀ s, Nat.card (heEC s) = 64 := by
  intro s
  cases s
  · exact card_grpNK base32_lt (enum_U0 h)
  · exact card_grpNK base32_lt (enum_U1 h)

theorem TC_mem_EC_of : ∀ s, heTC ∈ heEC s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ht0, ht1, -⟩ := heCheckC_parts h
  intro s
  cases s
  · exact mem_of_inLNK base32_lt (enum_U0 h) ht0 (rep_TC h)
  · exact mem_of_inLNK base32_lt (enum_U1 h) ht1 (rep_TC h)

theorem normal_BC_of : ∀ X : Subgroup (Equiv.Perm (Fin 32)), X ≤ heBC →
    (∀ b ∈ heBC, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = heEC false ∨ X = heEC true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hu, -⟩ := heCheckC_parts h
  intro X hX _ hsq h64
  exact eq_or_eq_of_setIP (card_setIP_of_uniqENK base32_lt (enum_BC h) (enum_U0 h) (enum_U1 h)
    hu) (card_grpNK base32_lt (enum_U0 h)) (card_grpNK base32_lt (enum_U1 h)) X hX hsq h64

theorem cent_EC_of : ∀ s, hePC ⊓ centralizer (heEC s : Set (Equiv.Perm (Fin 32))) ≤ heEC s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc0, hc1, -⟩ := heCheckC_parts h
  rintro s x ⟨hxC, hxc⟩
  obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base32_lt (enum_PC h) hxC
  cases s
  · have hb := List.all_eq_true.1 hc0 t ht
    have hall : heECGens.all (commN 32 t) = true := List.all_eq_true.2 fun a ha =>
      (commN_iff hrt (rep_of_validA (validA_of_mem_gensK (enum_U0 h) ha))).2
        (mem_centralizer_iff.mp hxc _ (gen_mem_grpN ha)).symm
    rw [hall, Bool.not_true, Bool.false_or] at hb
    exact mem_of_inLNK base32_lt (enum_U0 h) hb hrt
  · have hb := List.all_eq_true.1 hc1 t ht
    have hall : heFCGens.all (commN 32 t) = true := List.all_eq_true.2 fun a ha =>
      (commN_iff hrt (rep_of_validA (validA_of_mem_gensK (enum_U1 h) ha))).2
        (mem_centralizer_iff.mp hxc _ (gen_mem_grpN ha)).symm
    rw [hall, Bool.not_true, Bool.false_or] at hb
    exact mem_of_inLNK base32_lt (enum_U1 h) hb hrt

theorem normal_EC_of : ∀ s, ∀ X : Subgroup (Equiv.Perm (Fin 32)), X ≤ heP12C s →
    (∀ b ∈ heP12C s, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = heEC s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm0, hm1, -⟩ := heCheckC_parts h
  intro s X hXP hn hsq h64
  have hXB : X ≤ heBC := le_of_normal_of_card_two hXP (BC_le_P_of h s) hn h64
    (card_grpNK base32_lt (enum_BC h)) (card_P12C_of h s)
  have hX := normal_BC_of h X hXB (fun b hb x hx => hn b (BC_le_P_of h s hb) x hx) hsq h64
  cases s
  · refine hX.resolve_right fun hXe => ?_
    obtain ⟨g, hg, hgf⟩ := List.any_eq_true.1 hm0
    obtain ⟨f, hf, hnot⟩ := List.any_eq_true.1 hgf
    have hfX : permOfArr 32 f ∈ X := by
      rw [hXe]
      exact gen_mem_grpN hf
    have hc := hn _ (gen_mem_grpN hg) _ hfX
    rw [hXe] at hc
    rw [inLN_of_memK base32_lt (enum_U1 h) hc (rep_conjA (validA_of_mem_gensK (enum_P0 h) hg)
      (rep_of_validA (validA_of_mem_gensK (enum_U1 h) hf)))] at hnot
    exact absurd hnot (by decide)
  · refine hX.resolve_left fun hXe => ?_
    obtain ⟨g, hg, hgf⟩ := List.any_eq_true.1 hm1
    obtain ⟨f, hf, hnot⟩ := List.any_eq_true.1 hgf
    have hfX : permOfArr 32 f ∈ X := by
      rw [hXe]
      exact gen_mem_grpN hf
    have hc := hn _ (gen_mem_grpN hg) _ hfX
    rw [hXe] at hc
    rw [inLN_of_memK base32_lt (enum_U0 h) hc (rep_conjA (validA_of_mem_gensK (enum_P1 h) hg)
      (rep_of_validA (validA_of_mem_gensK (enum_U0 h) hf)))] at hnot
    exact absurd hnot (by decide)

theorem P_le_normalizer_EC_of :
    ∀ s, heP12C s ≤ normalizer (heEC s : Set (Equiv.Perm (Fin 32))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hn0, hn1⟩ := heCheckC_parts h
  intro s
  cases s
  · exact grpN_le fun a ha => mem_normalizer_of_normsN base32_lt (enum_U0 h)
      (validA_of_mem_gensK (enum_P0 h) ha) (List.all_eq_true.1 hn0 a ha)
  · exact grpN_le fun a ha => mem_normalizer_of_normsN base32_lt (enum_U1 h)
      (validA_of_mem_gensK (enum_P1 h) ha) (List.all_eq_true.1 hn1 a ha)

theorem norm_EC_of : ∀ s, hePC ⊓ normalizer (heEC s : Set (Equiv.Perm (Fin 32))) = heP12C s := by
  obtain ⟨-, -, -, -, -, -, -, hu0, hu1, hc0, hc1⟩ := heCheckCount_parts h
  intro s
  refine (Subgroup.eq_of_le_of_card_ge (le_inf (P_le_PC_of h s) (P_le_normalizer_EC_of h s))
    ?_).symm
  rw [card_P12C_of h s]
  cases s
  · rw [← hc0]
    refine card_le_length (S := ((hePC ⊓ normalizer (heEC false : Set (Equiv.Perm (Fin 32))) :
      Subgroup _) : Set (Equiv.Perm (Fin 32)))) ?_
    rintro x ⟨hxC, hxN⟩
    obtain ⟨t, ht, hrt, hvt⟩ := exists_rep_of_memK base32_lt (enum_PC h) hxC
    refine ⟨t, List.mem_filter.2 ⟨ht, List.all_eq_true.2 fun f hf => ?_⟩, hrt⟩
    have hrc := rep_conjA hvt (rep_of_validA (validA_of_mem_gensK (enum_U0 h) hf))
    rw [permOfArr_eq_of_rep hrt] at hrc
    have hmem : x * permOfArr 32 f * x⁻¹ ∈ grpN 32 heECGens :=
      (mem_normalizer_iff.mp hxN _).mp (gen_mem_grpN hf)
    obtain ⟨u, hu, hru, -⟩ := exists_rep_of_memK base32_lt (enum_U0 h) hmem
    rw [unipW_congr (by norm_num) hrc hru]
    exact List.all_eq_true.1 hu0 u hu
  · rw [← hc1]
    refine card_le_length (S := ((hePC ⊓ normalizer (heEC true : Set (Equiv.Perm (Fin 32))) :
      Subgroup _) : Set (Equiv.Perm (Fin 32)))) ?_
    rintro x ⟨hxC, hxN⟩
    obtain ⟨t, ht, hrt, hvt⟩ := exists_rep_of_memK base32_lt (enum_PC h) hxC
    refine ⟨t, List.mem_filter.2 ⟨ht, List.all_eq_true.2 fun f hf => ?_⟩, hrt⟩
    have hrc := rep_conjA hvt (rep_of_validA (validA_of_mem_gensK (enum_U1 h) hf))
    rw [permOfArr_eq_of_rep hrt] at hrc
    have hmem : x * permOfArr 32 f * x⁻¹ ∈ grpN 32 heFCGens :=
      (mem_normalizer_iff.mp hxN _).mp (gen_mem_grpN hf)
    obtain ⟨u, hu, hru, -⟩ := exists_rep_of_memK base32_lt (enum_U1 h) hmem
    rw [unipW_congr (by norm_num) hrc hru]
    exact List.all_eq_true.1 hu1 u hu

end C

theorem heModelFacts_of (h : heModelCheck = true) (hF : HexaFacts) : HeModelFacts where
  T_inf_M := T_inf_M_of h
  zeta_mem := zeta_mem_of h
  zeta_pow := zeta_pow_of h
  zeta_ne := zeta_ne_of h
  zeta_fix := zeta_fix_of h
  zeta_normal := zeta_normal_of h
  orbit := orbit_of' h
  card_P12 := card_P12_of h hF
  B0_le := B0_le_of h hF
  card_B0 := card_grpNK base64_lt (hB h)
  T_le_B0 := T_le_B0_of h
  F0_le_B0 := F0_le_B0_of h
  F0_sq := F0_sq_of h
  card_F0 := card_grpNK base64_lt (hF0 h)
  F0_ne := F0_ne_of h
  normal_B0 := normal_B0_of h
  P23_eq := P23_eq_of h hF
  P23_gens := P23_gens_of h
  bridge := nonempty_centralizer_mulEquiv_hePC (card_PC_of h)
  card_PC := card_PC_of h
  TC_mem := TC_mem_of h
  center_PC := center_PC_of h
  BC_le := (BC_le_P_of h false).trans (P_le_PC_of h false)
  card_BC := card_grpNK base32_lt (enum_BC h)
  P12C_le s := ⟨BC_le_P_of h s, P_le_PC_of h s⟩
  card_P12C := card_P12C_of h
  P12C_inf := P12C_inf_of h
  EC_le_BC := EC_le_BC_of h
  normal_BC := normal_BC_of h
  EC_le := EC_le_of h
  EC_sq := EC_sq_of h
  card_EC := card_EC_of h
  normal_EC := normal_EC_of h
  TC_mem_EC := TC_mem_EC_of h
  cent_EC := cent_EC_of h
  norm_EC := norm_EC_of h

end CFSG.ComponentClassification.AS81.HeTri


module

public import Certificates.Data.Kernel.M12Loc
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalBase
public import CFSG.Certificates.Kernel.M12Cent

public section

namespace CFSG.KC.M12Loc

open CFSG.GH74.M12.Hyp CFSG.KC.M12Cent CFSG.RankThree.PartTwo.Toolkit.M12 Subgroup
open CFSG.RankThree.PartTwo.Toolkit (toP3 toP4 perms3 perms4 ptab)
open scoped commutatorElement

theorem card_mul_le_of_coset_keys {G : Type*} [Group G] [Finite G] (S : Subgroup G) {α : Type*}
    (F : G → α) (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) {N : ℕ} (c : ℕ → G)
    (hk : ∀ i < N, ∀ j < N, F (c i) = F (c j) → i = j) : N * Nat.card S ≤ Nat.card G := by
  let f : Fin N × S → G := fun p => c p.1 * p.2
  have hf : Function.Injective f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have h' : c i * s = c j * t := h
    have hij : i = j := Fin.ext (hk i i.2 j j.2 (by rw [← hF (c i) s s.2, h', hF (c j) t t.2]))
    subst hij
    have hst : s = t := Subtype.ext (mul_left_cancel h')
    rw [hst]
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h

abbrev Nz : Subgroup G12 := normalizer ((zpowers ⁅x, y⁆ : Subgroup G12) : Set G12)

abbrev Na : Subgroup G12 := normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)

@[expose] def eltI (k : Idx) : G12 := ⟨prodP k, prodP_mem k⟩

theorem tbl_eltI (k : Idx) : tbl (eltI k).1 = prodT k := tbl_prodP k

theorem prodR_trT : prodR trT = prodT := funext fun _ => rfl

theorem nodup_of_nodupB : ∀ {l : List ℕ}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodup_of_nodupB h.2⟩
    rw [List.contains_iff_mem.2 ha] at h
    exact Bool.noConfusion h.1

theorem listOK_spec {p : List ℕ → Bool} {TT : List (List (List ℕ))} {L : List Idx}
    {T : List (List ℕ)} (hTT : TT = trT) (h : listOK p TT L T = true) :
    L.map prodT = T ∧ (T.map keyT).Nodup ∧ ∀ t ∈ T, p t = true := by
  subst hTT
  unfold listOK at h
  rw [prodR_trT] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, nodup_of_nodupB h.1.2, h.2⟩

theorem exists_tbl_of_listOK {p : List ℕ → Bool} {TT : List (List (List ℕ))} {L : List Idx}
    {T : List (List ℕ)} (hTT : TT = trT) (h : listOK p TT L T = true) :
    ∀ t ∈ T, ∃ g : G12, tbl g.1 = t := by
  intro t ht
  rw [← (listOK_spec hTT h).1, List.mem_map] at ht
  obtain ⟨k, -, rfl⟩ := ht
  exact ⟨eltI k, tbl_eltI k⟩

theorem mem_tables_of_card_le {K : Subgroup G12} {p : List ℕ → Bool}
    {TT : List (List (List ℕ))} {L : List Idx} {T : List (List ℕ)} (hTT : TT = trT)
    (hl : listOK p TT L T = true) (hp : ∀ g : G12, p (tbl g.1) = true → g ∈ K)
    (hK : Nat.card K ≤ L.length) : ∀ g : G12, tbl g.1 ∈ T ↔ g ∈ K := by
  classical
  obtain ⟨hLT, hnd, hpT⟩ := listOK_spec hTT hl
  have hTnd : T.Nodup := hnd.of_map _
  have hLnd : (L.map eltI).Nodup := by
    have e : (L.map eltI).map (fun g : G12 => tbl g.1) = T := by
      rw [List.map_map, ← hLT]
      exact List.map_congr_left fun k _ => tbl_eltI k
    rw [← e] at hTnd
    exact hTnd.of_map _
  intro g
  refine ⟨fun hg => hp g (hpT _ hg), fun hg => ?_⟩
  have hsub : (((L.map eltI).toFinset : Finset G12) : Set G12) ⊆ (K : Set G12) := by
    intro u hu
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hu
    obtain ⟨k, hk, rfl⟩ := hu
    refine hp _ (hpT _ ?_)
    rw [tbl_eltI, ← hLT]
    exact List.mem_map_of_mem hk
  have hcK : Nat.card K = (K : Set G12).ncard := Nat.card_coe_set_eq _
  have hcard : (K : Set G12).ncard ≤ (((L.map eltI).toFinset : Finset G12) : Set G12).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hLnd, List.length_map, ← hcK]
    exact hK
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
  have hg' : g ∈ (((L.map eltI).toFinset : Finset G12) : Set G12) := by
    rw [heq]
    exact hg
  rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hg'
  obtain ⟨k, hk, rfl⟩ := hg'
  rw [tbl_eltI, ← hLT]
  exact List.mem_map_of_mem hk

theorem zc_cube : ⁅x, y⁆ ^ 3 = 1 := by
  rw [eq_iff_tbl, tblG_pow, tblG_one, tbl_z]
  decide +kernel

theorem mem_nzp_iff {u : G12} {uT : List ℕ} (hu : tbl u.1 = uT) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (g : G12) : g ∈ normalizer ((zpowers u : Subgroup G12) : Set G12) ↔
      g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u ^ 2 := by
  rw [mem_normalizer_zpowers_iff hu hu3 hu1, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
    eq_iff_tbl, eq_iff_tbl (g := g * u * g⁻¹), tblG_conj, tblG_pow, hu]

theorem mem_centralizer_of_conj {g u : G12} (h : g * u * g⁻¹ = u) :
    g ∈ centralizer ({u} : Set G12) := by
  rw [mem_centralizer_singleton_iff]
  calc g * u = g * u * g⁻¹ * g := by group
    _ = u * g := by rw [h]

theorem card_nz_le {c : G12} (hc : c * ⁅x, y⁆ * c⁻¹ = ⁅x, y⁆ ^ 2) :
    Nat.card Nz ≤ 2 * Nat.card (centralizer ({⁅x, y⁆} : Set G12)) := by
  classical
  have h2 : ∀ g : G12, g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ 2 → c⁻¹ * g ∈ centralizer ({⁅x, y⁆} : Set G12) := by
    intro g hg
    refine mem_centralizer_of_conj ?_
    calc c⁻¹ * g * ⁅x, y⁆ * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * ⁅x, y⁆ * g⁻¹) * c := by group
      _ = c⁻¹ * (c * ⁅x, y⁆ * c⁻¹) * c := by rw [hg, hc]
      _ = ⁅x, y⁆ := by group
  let f : Nz → Bool × centralizer ({⁅x, y⁆} : Set G12) := fun g =>
    if h : g.1 * ⁅x, y⁆ * g.1⁻¹ = ⁅x, y⁆ then (true, ⟨g.1, mem_centralizer_of_conj h⟩)
    else (false, ⟨c⁻¹ * g.1, h2 g.1 (((mem_nzp_iff tbl_z zc_cube z_ne_one g.1).1 g.2).resolve_left h)⟩)
  have hf : Function.Injective f := by
    intro g h he
    simp only [f] at he
    split_ifs at he with hg hh hh
    · exact Subtype.ext (congrArg (fun p => p.2.1) he)
    · exact absurd (congrArg Prod.fst he) Bool.noConfusion
    · exact absurd (congrArg Prod.fst he) Bool.noConfusion
    · exact Subtype.ext (mul_left_cancel (congrArg (fun p => p.2.1) he))
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h

theorem mem_nz_tables {TT : List (List (List ℕ))}
    {T : List (List ℕ)} {S W C R : List (List ℕ)} (hcent : centCheck zT S W C R = true)
    (hTT : TT = trT) (hl : listOK (predP zT) TT idxNP T = true)
    (hs : T.any (fun t => tconj t zT == tpow zT 2) = true) :
    ∀ g : G12, tbl g.1 ∈ T ↔ g ∈ normalizer ((zpowers ⁅x, y⁆ : Subgroup G12) : Set G12) := by
  refine mem_tables_of_card_le hTT hl
    (fun g hg => (mem_normalizer_zpowers_iff tbl_z zc_cube z_ne_one g).2 hg) ?_
  obtain ⟨t, ht, htz⟩ := List.any_eq_true.1 hs
  obtain ⟨c, rfl⟩ := exists_tbl_of_listOK hTT hl t ht
  rw [beq_iff_eq, ← tbl_z, ← tblG_conj, ← tblG_pow, ← eq_iff_tbl] at htz
  have hC := card_centralizer_self (g := ⁅x, y⁆) (by rw [tbl_z]; exact hcent)
  have hle := card_nz_le htz
  rw [hC] at hle
  exact hle

theorem z_mem_P0 : ⁅x, y⁆ ∈ P0 := by
  have hxP : x ∈ P0 := subset_closure (by simp)
  have hyP : y ∈ P0 := subset_closure (by simp)
  rw [commutatorElement_def]
  exact P0.mul_mem (P0.mul_mem (P0.mul_mem hxP hyP) (P0.inv_mem hxP)) (P0.inv_mem hyP)

theorem z_comm_P0 {p : G12} (hp : p ∈ P0) : ⁅x, y⁆ * p = p * ⁅x, y⁆ := by
  have hle : P0 ≤ centralizer ({⁅x, y⁆} : Set G12) := by
    rw [P0, closure_le]
    rintro s (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 z_comm_x.eq.symm
    · exact mem_centralizer_singleton_iff.2 z_comm_y.eq.symm
  exact (mem_centralizer_singleton_iff.1 (hle hp)).symm

theorem mem_nz_of_tbl {g : G12}
    (h : (tbl (g * ⁅x, y⁆ * g⁻¹).1 = tid ∨ tbl (g * ⁅x, y⁆ * g⁻¹).1 = zT) ∨
      tbl (g * ⁅x, y⁆ * g⁻¹).1 = tpow zT 2) : g ∈ Nz := by
  rw [mem_nzp_iff tbl_z zc_cube z_ne_one]
  rcases h with (h | h) | h
  · exfalso
    apply z_ne_one
    have h1 : g * ⁅x, y⁆ * g⁻¹ = 1 := by rw [eq_iff_tbl, h, tblG_one]
    calc ⁅x, y⁆ = g⁻¹ * (g * ⁅x, y⁆ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · left
    rw [eq_iff_tbl, h, tbl_z]
  · right
    rw [eq_iff_tbl, h, tblG_pow, tbl_z]

theorem normalizer_P0_le_nz (h : centerOK = true) : normalizer (P0 : Set G12) ≤ Nz := by
  intro g hg
  have hxP : x ∈ P0 := subset_closure (by simp)
  have hyP : y ∈ P0 := subset_closure (by simp)
  have hwP : g * ⁅x, y⁆ * g⁻¹ ∈ P0 := (mem_normalizer_iff.1 hg _).1 z_mem_P0
  have hcomm : ∀ p ∈ P0, g * ⁅x, y⁆ * g⁻¹ * p = p * (g * ⁅x, y⁆ * g⁻¹) := by
    intro p hp
    have hp' : g⁻¹ * p * g ∈ P0 := by
      refine (mem_normalizer_iff.1 hg _).2 ?_
      have e : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
      rw [e]
      exact hp
    calc g * ⁅x, y⁆ * g⁻¹ * p = g * (⁅x, y⁆ * (g⁻¹ * p * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * p * g) * ⁅x, y⁆) * g⁻¹ := by rw [z_comm_P0 hp']
      _ = p * (g * ⁅x, y⁆ * g⁻¹) := by group
  have hc := List.all_eq_true.1 h _ ((mem_P0_iff _).1 hwP)
  have h1 : tmul (tbl (g * ⁅x, y⁆ * g⁻¹).1) xT = tmul xT (tbl (g * ⁅x, y⁆ * g⁻¹).1) := by
    rw [← tbl_x, ← tblG_mul, ← tblG_mul, hcomm x hxP]
  have h2 : tmul (tbl (g * ⁅x, y⁆ * g⁻¹).1) yT = tmul yT (tbl (g * ⁅x, y⁆ * g⁻¹).1) := by
    rw [← tbl_y, ← tblG_mul, ← tblG_mul, hcomm y hyP]
  simp only [h1, h2, beq_self_eq_true, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, beq_iff_eq] at hc
  exact mem_nz_of_tbl hc

theorem fixN_tbl (σ : Equiv.Perm (Fin 12)) :
    fixN (tbl σ) = (Finset.univ.filter fun i : Fin 12 => σ i = i).card := by
  classical
  have hnd : ((List.range 12).filter fun i => (tbl σ).getD i 0 == i).Nodup :=
    List.nodup_range.filter _
  rw [fixN, ← List.toFinset_card_of_nodup hnd, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext n
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq, Finset.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨⟨n, hn⟩, Fin.ext ?_, rfl⟩
    rw [← tbl_getD_of_lt σ hn]
    exact h
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.2, ?_⟩
    rw [tbl_getD, hi]

theorem fixN_conj (g u : G12) : fixN (tbl (g * u * g⁻¹).1) = fixN (tbl u.1) := by
  classical
  rw [fixN_tbl, fixN_tbl]
  have hs := Equiv.Perm.card_support_conj (σ := g.1) (τ := u.1)
  have e : ∀ τ : Equiv.Perm (Fin 12), (Finset.univ.filter fun i : Fin 12 => τ i = i) = τ.supportᶜ := by
    intro τ
    ext i
    simp [Equiv.Perm.mem_support]
  have hm : (g * u * g⁻¹).1 = g.1 * u.1 * g.1⁻¹ := rfl
  rw [e, e, Finset.card_compl, Finset.card_compl, hm, hs]

theorem normalizer_A_le_nz (h : aFixOK = true) : normalizer (basisA.sub : Set G12) ≤ Nz := by
  intro g hg
  have hzA : ⁅x, y⁆ ∈ basisA.sub := subset_closure (Or.inl rfl)
  have hwA : g * ⁅x, y⁆ * g⁻¹ ∈ basisA.sub := (mem_normalizer_iff.1 hg _).1 hzA
  have hc := List.all_eq_true.1 h _ ((mem_A_iff _).1 hwA)
  have hf : fixN (tbl (g * ⁅x, y⁆ * g⁻¹).1) = fixN zT := by rw [fixN_conj, tbl_z]
  simp only [hf, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · exact mem_nz_of_tbl (Or.inl (Or.inr hc))
  · exact mem_nz_of_tbl (Or.inr hc)

theorem centralizer_le_nz (B : CFSG.RankThree.Asc83Table.E9Basis G12) (hB : B.a = ⁅x, y⁆) :
    centralizer (B.sub : Set G12) ≤ Nz := by
  intro g hg
  have hzB : ⁅x, y⁆ ∈ B.sub := by
    rw [← hB]
    exact subset_closure (by simp)
  have hc := mem_centralizer_iff.1 hg _ hzB
  rw [mem_nzp_iff tbl_z zc_cube z_ne_one]
  left
  rw [← hc]
  group

theorem card_eq_countOK {H : Subgroup G12} {q : List ℕ → Bool} {T : List (List ℕ)} {n : ℕ}
    (hH : H ≤ Nz) (hq : ∀ g, g ∈ H ↔ q (tbl g.1) = true) (hT : ∀ g, tbl g.1 ∈ T ↔ g ∈ Nz)
    (hs : ∀ t ∈ T, ∃ g : G12, tbl g.1 = t) (hnd : nodupB (T.map keyT) = true)
    (hc : countOK q T n = true) : Nat.card H = n := by
  have hTnd : (T.filter q).Nodup := ((nodup_of_nodupB hnd).of_map _).filter _
  let f : H → {t // t ∈ T.filter q} := fun g =>
    ⟨tbl g.1.1, List.mem_filter.2 ⟨(hT _).2 (hH g.2), (hq _).1 g.2⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g h he => Subtype.ext (eq_iff_tbl.2 (congrArg Subtype.val he)), fun t => ?_⟩
    obtain ⟨ht, hqt⟩ := List.mem_filter.1 t.2
    obtain ⟨g, hg⟩ := hs _ ht
    refine ⟨⟨g, (hq g).2 (by rw [hg]; exact hqt)⟩, Subtype.ext hg⟩
  rw [Nat.card_eq_of_bijective f hf, ← Nat.card_congr (List.Nodup.getEquiv _ hTnd),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold countOK at hc
  exact beq_iff_eq.1 hc

theorem np_of_npOK {T : List (List ℕ)} (hP : centerOK = true) (hT : ∀ g, tbl g.1 ∈ T ↔ g ∈ Nz)
    (h : npOK T = true) : ∀ g ∈ normalizer (P0 : Set G12), g ^ 2 ∈ P0 ∧
      g ∈ normalizer (basisE.sub : Set G12) ∧ g ∈ normalizer (basisF.sub : Set G12) := by
  intro g hg
  have hn := (mem_normalizer_pair_iff tbl_x tbl_y mem_P0_iff g).1 hg
  have hc := List.all_eq_true.1 h _ ((hT g).2 (normalizer_P0_le_nz hP hg))
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · exact Bool.noConfusion (hn.symm.trans hc)
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
  obtain ⟨⟨h2, hE⟩, hF⟩ := hc
  refine ⟨(mem_P0_iff _).2 (by rw [pow_two, tblG_mul]; exact h2),
    (mem_normalizer_pair_iff tbl_z tbl_x (mem_sub_iff basisE tbl_z tbl_x) g).2 hE,
    (mem_normalizer_pair_iff tbl_z tbl_y (mem_sub_iff basisF tbl_z tbl_y) g).2 hF⟩

theorem keyA_sq {v : G12} (hv : v ^ 3 = 1) : keyA (tbl (v * v).1) = keyA (tbl v.1) := by
  have h4 : v * v * (v * v) = v := by
    calc v * v * (v * v) = v ^ 3 * v := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = v := by rw [hv, one_mul]
  unfold keyA
  simp only [← tblG_mul, h4]
  exact min_comm _ _

theorem mem_na_tables {TT : List (List (List ℕ))}
    {T W : List (List ℕ)} (hTT : TT = trT) (hl : listOK (predP aT) TT idxNa T = true)
    (ho : orbOK W = true) : ∀ g : G12, tbl g.1 ∈ T ↔ g ∈ Na := by
  refine mem_tables_of_card_le hTT hl
    (fun g hg => (mem_normalizer_zpowers_iff tbl_a a_cube a_ne_one g).2 hg) ?_
  unfold orbOK at ho
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨hW, hWk⟩ := ho
  have hF : ∀ g : G12, ∀ s ∈ Na, keyA (tbl (g * s * (x * y) * (g * s)⁻¹).1) =
      keyA (tbl (g * (x * y) * g⁻¹).1) := by
    intro g s hs
    have e : g * s * (x * y) * (g * s)⁻¹ = g * (s * (x * y) * s⁻¹) * g⁻¹ := by group
    rw [e]
    rcases (mem_nzp_iff tbl_a a_cube a_ne_one s).1 hs with h | h
    · rw [h]
    · have e2 : g * (x * y) ^ 2 * g⁻¹ = g * (x * y) * g⁻¹ * (g * (x * y) * g⁻¹) := by
        rw [pow_two]
        group
      rw [h, e2]
      refine keyA_sq ?_
      rw [conj_pow, a_cube]
      group
  have hle := card_mul_le_of_coset_keys Na (fun g : G12 => keyA (tbl (g * (x * y) * g⁻¹).1))
    (fun g s hs => hF g s hs) (N := 1320) (fun j => wG (W.getD j [])) (fun i hi j hj he => by
      simp only [tbl_wG_conj, tbl_a] at he
      have hi' : i < (W.map fun w => keyA (conjN w aT)).length := by
        rw [List.length_map, hW]
        exact hi
      have hj' : j < (W.map fun w => keyA (conjN w aT)).length := by
        rw [List.length_map, hW]
        exact hj
      refine idx_eq_of_incr hWk hi' hj' ?_
      rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ [],
        ← List.getD_eq_getElem _ []]
      exact he)
  have hc : Nat.card G12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have hlen : idxNa.length = 72 := rfl
  rw [hc] at hle
  rw [hlen]
  omega

theorem ptab_injective {n : ℕ} : Function.Injective (ptab (n := n)) := by
  intro σ τ h
  have h' := List.ofFn_injective h
  exact Equiv.ext fun i => Fin.ext (congrFun h' i)

theorem ptab_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ptab (σ * τ) = tmul (ptab σ) (ptab τ) := by
  unfold ptab tmul
  rw [List.map_ofFn]
  congr 1
  funext i
  simp [Equiv.Perm.mul_apply, List.getD_eq_getElem?_getD]

theorem find_ptab {n : ℕ} {l : List (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ l) :
    (l.find? fun τ => ptab τ == ptab σ).getD 1 = σ := by
  cases h : l.find? (fun τ => ptab τ == ptab σ) with
  | none =>
    have := List.find?_eq_none.1 h σ hσ
    simp at this
  | some τ =>
    have := List.find?_some h
    rw [beq_iff_eq] at this
    exact ptab_injective this

theorem ptab_perms3 : perms3.map ptab = T3L := by decide +kernel

theorem ptab_perms4e : (perms4.filter fun σ => decide (Equiv.Perm.sign σ = 1)).map ptab = T4eL := by
  decide +kernel

theorem nodupB_perms4 : nodupB ((perms4.map ptab).map keyT) = true := by decide +kernel

theorem mem_perms3 (ρ : Equiv.Perm (Fin 3)) : ρ ∈ perms3 := by
  classical
  have hnd : perms3.Nodup := by
    have h : (perms3.map ptab).Nodup := by
      rw [ptab_perms3]
      decide +kernel
    exact h.of_map _
  have hc : perms3.toFinset.card = Fintype.card (Equiv.Perm (Fin 3)) := by
    rw [List.toFinset_card_of_nodup hnd, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [← List.mem_toFinset, Finset.eq_univ_of_card _ hc]
  exact Finset.mem_univ _

theorem mem_perms4 (ρ : Equiv.Perm (Fin 4)) : ρ ∈ perms4 := by
  classical
  have hnd : perms4.Nodup := ((nodup_of_nodupB nodupB_perms4).of_map _).of_map _
  have hc : perms4.toFinset.card = Fintype.card (Equiv.Perm (Fin 4)) := by
    rw [List.toFinset_card_of_nodup hnd, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [← List.mem_toFinset, Finset.eq_univ_of_card _ hc]
  exact Finset.mem_univ _

theorem toP3_ptab (ρ : Equiv.Perm (Fin 3)) : toP3 (ptab ρ) = ρ := find_ptab (mem_perms3 ρ)

theorem toP4_ptab (ρ : Equiv.Perm (Fin 4)) : toP4 (ptab ρ) = ρ := find_ptab (mem_perms4 ρ)

theorem ptab_toP3 {u : List ℕ} (hu : u ∈ T3L) : ptab (toP3 u) = u := by
  rw [← ptab_perms3, List.mem_map] at hu
  obtain ⟨σ, -, rfl⟩ := hu
  rw [toP3_ptab]

theorem ptab_toP4 {u : List ℕ} (hu : u ∈ T4eL) : ptab (toP4 u) = u := by
  rw [← ptab_perms4e, List.mem_map] at hu
  obtain ⟨σ, -, rfl⟩ := hu
  rw [toP4_ptab]

theorem toP3_mul {u v : List ℕ} (hu : u ∈ T3L) (hv : v ∈ T3L) :
    toP3 (tmul u v) = toP3 u * toP3 v := by
  rw [← ptab_toP3 hu, ← ptab_toP3 hv, ← ptab_mul, toP3_ptab, toP3_ptab, toP3_ptab]

theorem toP4_mul {u v : List ℕ} (hu : u ∈ T4eL) (hv : v ∈ T4eL) :
    toP4 (tmul u v) = toP4 u * toP4 v := by
  rw [← ptab_toP4 hu, ← ptab_toP4 hv, ← ptab_mul, toP4_ptab, toP4_ptab, toP4_ptab]

theorem sign_toP4 {u : List ℕ} (hu : u ∈ T4eL) : Equiv.Perm.sign (toP4 u) = 1 := by
  rw [← ptab_perms4e, List.mem_map] at hu
  obtain ⟨σ, hσ, rfl⟩ := hu
  rw [toP4_ptab]
  exact of_decide_eq_true (List.mem_filter.1 hσ).2

theorem psiRows_of_split {T : List (List ℕ)} (h0 : psiRows (T.take 24) T = true)
    (h1 : psiRows ((T.drop 24).take 24) T = true) (h2 : psiRows (T.drop 48) T = true) :
    psiRows T T = true := by
  have e : T = T.take 24 ++ ((T.drop 24).take 24 ++ T.drop 48) := by
    have h48 : (T.drop 24).drop 24 = T.drop 48 := by rw [List.drop_drop]
    rw [← h48, List.take_append_drop, List.take_append_drop]
  unfold psiRows at h0 h1 h2 ⊢
  rw [e, List.all_append, List.all_append, ← e, h0, h1, h2]
  rfl

theorem psi_of_rows {K : Subgroup G12} {T : List (List ℕ)} (hT : ∀ g : G12, tbl g.1 ∈ T ↔ g ∈ K)
    (hr : psiRows T T = true) (hv : psiValOK T = true) :
    (∀ g ∈ K, ∀ h ∈ K, psiT (tbl (g * h).1) = psiT (tbl g.1) * psiT (tbl h.1)) ∧
      (∀ g ∈ K, ∀ h ∈ K, psiT (tbl g.1) = psiT (tbl h.1) → g = h) ∧
      ∀ g ∈ K, Equiv.Perm.sign (psiT (tbl g.1)).2 = 1 := by
  have hrow : ∀ s ∈ T, ∀ t ∈ T, (rowTab (tmul s t) = tmul (rowTab s) (rowTab t) ∧
      colTab (tmul s t) = tmul (colTab s) (colTab t)) ∧
      (rowTab s = rowTab t → colTab s = colTab t → s = t) := by
    intro s hs t ht
    unfold psiRows at hr
    have := List.all_eq_true.1 (List.all_eq_true.1 hr s hs) t ht
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, bne_iff_ne] at this
    refine ⟨this.1, fun h1 h2 => ?_⟩
    rcases this.2 with (h | h) | h
    · exact absurd h1 (by simpa using h)
    · exact absurd h2 (by simpa using h)
    · exact h
  have hval : ∀ s ∈ T, rowTab s ∈ T3L ∧ colTab s ∈ T4eL := by
    intro s hs
    unfold psiValOK at hv
    have := List.all_eq_true.1 hv s hs
    simp only [Bool.and_eq_true, List.contains_iff_mem] at this
    exact this
  refine ⟨fun g hg h hh => ?_, fun g hg h hh he => ?_, fun g hg => ?_⟩
  · have hs := (hT g).2 hg
    have ht := (hT h).2 hh
    obtain ⟨⟨h1, h2⟩, -⟩ := hrow _ hs _ ht
    rw [tblG_mul, psiT, psiT, psiT, h1, h2, toP3_mul (hval _ hs).1 (hval _ ht).1,
      toP4_mul (hval _ hs).2 (hval _ ht).2]
    rfl
  · have hs := (hT g).2 hg
    have ht := (hT h).2 hh
    simp only [psiT, Prod.mk.injEq] at he
    have h1 : rowTab (tbl g.1) = rowTab (tbl h.1) := by
      rw [← ptab_toP3 (hval _ hs).1, ← ptab_toP3 (hval _ ht).1, he.1]
    have h2 : colTab (tbl g.1) = colTab (tbl h.1) := by
      rw [← ptab_toP4 (hval _ hs).2, ← ptab_toP4 (hval _ ht).2, he.2]
    exact eq_iff_tbl.2 ((hrow _ hs _ ht).2 h1 h2)
  · exact sign_toP4 (hval _ ((hT g).2 hg)).2

end CFSG.KC.M12Loc

end

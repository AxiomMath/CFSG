module

public import CFSG.CGT.PushingUpLit.SolK.GenFourA8
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Certificates.Certificate22100

public section

namespace CFSG.ComponentClassification.GSThmB.Cat81A8

open CFSG.GH74 CFSG.CGT.PushingUpLit Subgroup

theorem cert_facts :
    TList.length = 128 ∧ closedUnder gensT TList = true ∧ bigInv.length ≤ 3 ∧ lx ∈ TList ∧
      ly ∈ TList ∧ (tr * tw) * (tr * tw) = lq ∧ (bfs [lx, lq] 6).length = 16 ∧
      (bfs [ly, lq] 6).length = 16 ∧ (bfs [lx * ly, lq] 6).length = 16 :=
  Certificates.certificate22100

theorem bfs_nodup (gens : List (Equiv.Perm (Fin 8))) : ∀ k, (bfs gens k).Nodup
  | 0 => List.nodup_singleton 1
  | _ + 1 => List.nodup_dedup _

theorem one_mem_bfs (gens : List (Equiv.Perm (Fin 8))) :
    ∀ k, (1 : Equiv.Perm (Fin 8)) ∈ bfs gens k
  | 0 => List.mem_singleton_self 1
  | k + 1 => by
    simp only [bfs, bfsStep, List.mem_dedup, List.mem_append]
    exact Or.inl (one_mem_bfs gens k)

theorem mem_closure_of_mem_bfs (gens : List (Equiv.Perm (Fin 8))) :
    ∀ k, ∀ x ∈ bfs gens k, x ∈ closure {g | g ∈ gens}
  | 0, x, hx => by
    simp only [bfs, List.mem_singleton] at hx
    subst hx
    exact one_mem _
  | k + 1, x, hx => by
    simp only [bfs, bfsStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with hx | ⟨a, ha, g, hg, rfl⟩
    · exact mem_closure_of_mem_bfs gens k x hx
    · rw [ofTab_eq]
      exact mul_mem (mem_closure_of_mem_bfs gens k a ha) (subset_closure hg)

theorem mul_mem_of_closedUnder {gens L : List (Equiv.Perm (Fin 8))}
    (h : closedUnder gens L = true) {a g : Equiv.Perm (Fin 8)} (ha : a ∈ L) (hg : g ∈ gens) :
    a * g ∈ L := by
  simp only [closedUnder, List.all_eq_true, List.contains_iff_mem] at h
  exact h a ha g hg

theorem card_mem_list (L : List (Equiv.Perm (Fin 8))) :
    Nat.card {y // y ∈ L} = L.toFinset.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => List.mem_toFinset.symm)

theorem card_mem_list_le (L : List (Equiv.Perm (Fin 8))) : Nat.card {y // y ∈ L} ≤ L.length :=
  (card_mem_list L).trans_le (List.toFinset_card_le L)

@[expose] def T8 : Subgroup (Equiv.Perm (Fin 8)) := closure {g | g ∈ gensT}

theorem mem_T8_of_mem_gensT {g : Equiv.Perm (Fin 8)} (hg : g ∈ gensT) : g ∈ T8 :=
  subset_closure hg

theorem mem_TList_of_mem_T8 {y : Equiv.Perm (Fin 8)}
    (hy : y ∈ T8) : y ∈ TList := by
  classical
  have key : ∀ x ∈ TList, x * y ∈ TList := by
    refine closure_induction (p := fun y _ => ∀ x ∈ TList, x * y ∈ TList) ?_ ?_ ?_ ?_
      (show y ∈ closure {g | g ∈ gensT} from hy)
    · intro g hg x hx
      exact mul_mem_of_closedUnder cert_facts.2.1 hx hg
    · intro x hx
      simpa using hx
    · intro u v _ _ hu hv x hx
      rw [← mul_assoc]
      exact hv _ (hu x hx)
    · intro u _ hu x hx
      have hsub : TList.toFinset.image (· * u) ⊆ TList.toFinset := by
        intro w hw
        simp only [Finset.mem_image, List.mem_toFinset] at hw ⊢
        obtain ⟨v, hv, rfl⟩ := hw
        exact hu v hv
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_image_of_injective _ (mul_left_injective u)])
      have hx' : x ∈ TList.toFinset.image (· * u) := by
        rw [heq]
        exact List.mem_toFinset.2 hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx'
      simpa using List.mem_toFinset.1 hv
  simpa using key 1 (one_mem_bfs gensT 8)

theorem mem_T8_iff {y : Equiv.Perm (Fin 8)} :
    y ∈ T8 ↔ y ∈ TList :=
  ⟨mem_TList_of_mem_T8, mem_closure_of_mem_bfs gensT 8 y⟩

theorem card_T8 : Nat.card T8 = 128 := by
  have h : Nat.card T8 = Nat.card {y // y ∈ TList} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_T8_iff)
  have hnd : TList.Nodup := bfs_nodup gensT 8
  rw [h, card_mem_list, List.toFinset_card_of_nodup hnd, cert_facts.1]

theorem card_perm8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

noncomputable def sylowT8 : Sylow 2 (Equiv.Perm (Fin 8)) :=
  IsPGroup.toSylow (P := T8) (IsPGroup.of_card (n := 7) (by rw [card_T8]; norm_num)) (by
    have h := T8.card_mul_index
    rw [card_T8, card_perm8] at h
    have : T8.index = 315 := by omega
    rw [this]
    norm_num)

theorem mul_comm_of_mul_self {G : Type*} [Group G] {P : Subgroup G}
    (hsq : ∀ x ∈ P, x * x = 1) {u v : G} (hu : u ∈ P) (hv : v ∈ P) : u * v = v * u :=
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hu hv))).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by
      rw [inv_eq_of_mul_eq_one_right (hsq v hv), inv_eq_of_mul_eq_one_right (hsq u hu)]

theorem exists_mul_self_ne_one (P : Subgroup T8)
    (hP : Nat.card P = 32) : ∃ x ∈ P, x * x ≠ 1 := by
  classical
  by_contra! hsq
  have hbig : ∀ y ∈ P, y ≠ 1 → ((y : T8) : Equiv.Perm (Fin 8)) ∈ bigInv := by
    intro y hy hy1
    have hinv : ∀ w : P, ((w : T8) : Equiv.Perm (Fin 8)) ∈ invComm (y : Equiv.Perm (Fin 8)) := by
      intro w
      have h1 : (w : T8) * (w : T8) = 1 := hsq _ w.2
      have h2 : y * (w : T8) = (w : T8) * y := mul_comm_of_mul_self hsq hy w.2
      simp only [invComm, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨mem_TList_of_mem_T8 (w : T8).2, congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    have h32 : 32 ≤ (invComm (y : Equiv.Perm (Fin 8))).length := by
      have hle := Nat.card_le_card_of_injective
        (fun w : P => (⟨((w : T8) : Equiv.Perm (Fin 8)), hinv w⟩ :
          {u // u ∈ invComm (y : Equiv.Perm (Fin 8))}))
        (fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
      have := card_mem_list_le (invComm (y : Equiv.Perm (Fin 8)))
      omega
    simp only [bigInv, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨mem_TList_of_mem_T8 y.2, ⟨congrArg Subtype.val (hsq y hy),
      fun h => hy1 (Subtype.ext h)⟩, h32⟩
  have hmem : ∀ y : P, ((y : T8) : Equiv.Perm (Fin 8)) ∈ 1 :: bigInv := by
    intro y
    by_cases hy1 : (y : T8) = 1
    · rw [hy1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hbig _ y.2 hy1)
  have hle := Nat.card_le_card_of_injective
    (fun y : P => (⟨((y : T8) : Equiv.Perm (Fin 8)), hmem y⟩ : {u // u ∈ 1 :: bigInv}))
    (fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h'))
  have h1 := card_mem_list_le (1 :: bigInv)
  have h2 := cert_facts.2.2.1
  simp only [List.length_cons] at h1
  omega

theorem card_closure_pair (u v : T8)
    (h : (bfs [(u : Equiv.Perm (Fin 8)), v] 6).length = 16) :
    16 ≤ Nat.card (closure (({u, v} : Finset T8) : Set T8)) := by
  classical
  rw [← card_map_of_injective (K := closure (({u, v} : Finset T8) : Set T8))
    T8.subtype_injective, MonoidHom.map_closure]
  have hset : (T8.subtype '' (({u, v} : Finset T8) : Set T8)) =
      {g | g ∈ [(u : Equiv.Perm (Fin 8)), v]} := by
    ext g
    simp
  rw [hset]
  have hnd := bfs_nodup [(u : Equiv.Perm (Fin 8)), v] 6
  calc 16 = Nat.card {y // y ∈ bfs [(u : Equiv.Perm (Fin 8)), v] 6} := by
        rw [card_mem_list, List.toFinset_card_of_nodup hnd, h]
    _ ≤ _ := Nat.card_le_card_of_injective
        (fun y => ⟨y.1, mem_closure_of_mem_bfs _ 6 y.1 y.2⟩)
        (fun a b hab => by
          have h' := congrArg Subtype.val hab
          exact Subtype.ext h')

theorem gen4_T8 : SectionalTwoRankLE T8 4 := by
  classical
  intro P hP
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  have hm7 : m ≤ 7 := by
    have hd : Nat.card P ∣ Nat.card T8 := card_subgroup_dvd_card P
    rw [hm, card_T8, show (128 : ℕ) = 2 ^ 7 by norm_num] at hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  rcases Nat.lt_or_ge m 5 with h4 | h5
  ·
    obtain ⟨t, -, ht, hcard⟩ := SolK.exists_gen_of_start P ∅ (by simp) 0 (by simp)
    refine ⟨t, ?_, ht⟩
    rw [hm] at hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by simpa using hcard)
    omega
  rcases Nat.lt_or_ge m 6 with h5' | h6
  ·
    have hP32 : Nat.card P = 32 := by rw [hm, show m = 5 by omega]; norm_num
    obtain ⟨x, hxP, hx2⟩ := exists_mul_self_ne_one P hP32
    have hord : orderOf x ∣ 2 ^ 5 := by
      have h := orderOf_dvd_natCard (⟨x, hxP⟩ : P)
      rw [Subgroup.orderOf_mk, hP32] at h
      norm_num
      exact h
    have hx4 : 4 ≤ orderOf x := by
      obtain ⟨k, -, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      by_contra hlt
      have hk1 : k ≤ 1 := by
        by_contra hk2
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hx2' : x ^ 2 = 1 := by
        have : orderOf x ∣ 2 := by
          rw [hkx]
          interval_cases k <;> simp
        exact orderOf_dvd_iff_pow_eq_one.1 this
      exact hx2 (by rw [← pow_two]; exact hx2')
    have h4 : 2 ^ (1 + 1) ≤ Nat.card (closure (({x} : Finset T8) : Set T8)) := by
      rw [Finset.coe_singleton, ← zpowers_eq_closure, Nat.card_zpowers]
      simpa using hx4
    obtain ⟨t, -, ht, hcard⟩ := SolK.exists_gen_of_start P {x} (by simpa using hxP) 1 h4
    refine ⟨t, ?_, ht⟩
    rw [hP32] at hcard
    have : 2 ^ (t.card + 1) ≤ 2 ^ 5 := by simpa using hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    omega
  rcases Nat.lt_or_ge m 7 with h6' | h7
  ·
    have hidx : P.index = 2 := by
      have h := P.card_mul_index
      rw [hm, card_T8, show m = 6 by omega] at h
      omega
    let x₀ : T8 := ⟨lx, mem_T8_iff.2 cert_facts.2.2.2.1⟩
    let y₀ : T8 := ⟨ly, mem_T8_iff.2 cert_facts.2.2.2.2.1⟩
    let r : T8 := ⟨tr * tw, mul_mem (mem_T8_of_mem_gensT (by simp [gensT]))
      (mem_T8_of_mem_gensT (by simp [gensT]))⟩
    have hq : r * r ∈ P := mul_self_mem_of_index_two hidx r
    have hr : ((r * r : T8) : Equiv.Perm (Fin 8)) = lq := cert_facts.2.2.2.2.2.1
    obtain ⟨w, hwP, hw16⟩ : ∃ w : T8, w ∈ P ∧
        (bfs [(w : Equiv.Perm (Fin 8)), lq] 6).length = 16 := by
      by_cases hx : x₀ ∈ P
      · exact ⟨x₀, hx, cert_facts.2.2.2.2.2.2.1⟩
      by_cases hy : y₀ ∈ P
      · exact ⟨y₀, hy, cert_facts.2.2.2.2.2.2.2.1⟩
      · exact ⟨x₀ * y₀, (mul_mem_iff_of_index_two hidx).2 (iff_of_false hx hy),
          cert_facts.2.2.2.2.2.2.2.2⟩
    have h16 := card_closure_pair w (r * r) (by rw [hr]; exact hw16)
    obtain ⟨t, -, ht, hcard⟩ := SolK.exists_gen_of_start P {w, r * r} (by
      intro u hu
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      exacts [hwP, hq]) 2 (by
      have hc : ({w, r * r} : Finset T8).card ≤ 2 := Finset.card_le_two
      calc 2 ^ (({w, r * r} : Finset T8).card + 2) ≤ 2 ^ (2 + 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := h16)
    refine ⟨t, ?_, ht⟩
    rw [hm, show m = 6 by omega] at hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
    omega
  ·
    have hPtop : P = ⊤ := eq_top_of_card_eq P (by rw [hm, card_T8, show m = 7 by omega]; norm_num)
    subst hPtop
    refine ⟨{⟨tr, mem_T8_of_mem_gensT (by simp [gensT])⟩,
      ⟨ts, mem_T8_of_mem_gensT (by simp [gensT])⟩, ⟨tw, mem_T8_of_mem_gensT (by simp [gensT])⟩},
      Finset.card_le_three.trans (by norm_num), ?_⟩
    have hset : (({⟨tr, mem_T8_of_mem_gensT (by simp [gensT])⟩,
        ⟨ts, mem_T8_of_mem_gensT (by simp [gensT])⟩,
        ⟨tw, mem_T8_of_mem_gensT (by simp [gensT])⟩} : Finset T8) : Set T8) =
        Subtype.val ⁻¹' {g | g ∈ gensT} := by
      ext u
      simp [gensT, Subtype.ext_iff]
    rw [hset]
    exact closure_closure_coe_preimage

theorem gen4_perm8 : SectionalTwoRankLE (Equiv.Perm (Fin 8)) 4 :=
  SolK.SectionalTwoRankLE.of_sylow sylowT8 gen4_T8

noncomputable def mulAutEquivPerm8 {K₀ : Type*} [Group K₀] (e : K₀ ≃* alternatingGroup (Fin 8)) :
    MulAut K₀ ≃* Equiv.Perm (Fin 8) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
      (by norm_num))).symm

theorem gen4_mulAut {K₀ : Type*} [Group K₀]
    (e : K₀ ≃* alternatingGroup (Fin 8)) : SectionalTwoRankLE (MulAut K₀) 4 :=
  SectionalTwoRankLE.of_mulEquiv (mulAutEquivPerm8 e).symm gen4_perm8

theorem card_le_of_isPGroup {K₀ : Type*} [Group K₀] (e : K₀ ≃* alternatingGroup (Fin 8))
    {R : Subgroup (MulAut K₀)} (hR : IsPGroup 2 R) : Nat.card R ≤ 128 := by
  have hcard : Nat.card (MulAut K₀) = 40320 :=
    (Nat.card_congr (mulAutEquivPerm8 e).toEquiv).trans card_perm8
  have : Finite (MulAut K₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR
  have hd := card_subgroup_dvd_card R
  rw [hm, hcard, show (40320 : ℕ) = 2 ^ 7 * 315 by norm_num] at hd
  have h7 : 2 ^ m ∣ 2 ^ 7 :=
    (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 315)).dvd_of_dvd_mul_right hd
  rw [hm]
  exact (Nat.le_of_dvd (by norm_num) h7).trans (by norm_num)

end CFSG.ComponentClassification.GSThmB.Cat81A8

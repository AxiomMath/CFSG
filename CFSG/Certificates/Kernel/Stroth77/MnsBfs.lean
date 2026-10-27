module

public import CFSG.Certificates.Kernel.Stroth77.MnsSmall
public import Certificates.Data.Kernel.Stroth77.MnsBfsK

public section

namespace CFSG.KC.Stroth77MN

open CFSG.CGT.Stroth77
open CFSG.KC.Stroth77SP (mulK conjK rd l32)

section Transport

variable {G : Type*} [Group G] [DecidableEq G] {f : G → ℕ} {m : ℕ → ℕ → ℕ}

theorem expandList_map (hf : Function.Injective f) (hm : ∀ a b, f (a * b) = m (f a) (f b))
    (gens : List G) (s : G) (vis : List G) :
    (expandList gens s vis).map f = expandListK m (gens.map f) (f s) (vis.map f) := by
  unfold expandList expandListK
  induction gens generalizing vis with
  | nil => rfl
  | cons g l ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    by_cases h : s * g ∈ vis
    · have h' : m (f s) (f g) ∈ vis.map f := by
        rw [← hm]
        exact List.mem_map_of_mem h
      rw [if_pos h, if_pos h']
    · have h' : m (f s) (f g) ∉ vis.map f := by
        rw [← hm]
        intro hx
        obtain ⟨y, hy, hye⟩ := List.mem_map.1 hx
        exact h (hf hye ▸ hy)
      rw [if_neg h, if_neg h', List.map_append, List.map_singleton, hm]

theorem closeList_map (hf : Function.Injective f) (hm : ∀ a b, f (a * b) = m (f a) (f b))
    (gens : List G) : ∀ (fuel : ℕ) (vis : List G) (i : ℕ),
    (closeList gens fuel vis i).map f = closeListK m (gens.map f) fuel (vis.map f) i := by
  intro fuel
  induction fuel with
  | zero => intro vis i; rfl
  | succ fuel ih =>
    intro vis i
    simp only [closeList, closeListK, List.length_map]
    by_cases hi : i < vis.length
    · rw [dif_pos hi, dif_pos hi, ih, expandList_map hf hm, List.getElem_map]
    · rw [dif_neg hi, dif_neg hi]

end Transport

theorem encN_mulK (a b : Mns) : encN (a * b) = mulK (encN a) (encN b) := encN_mul a b

theorem encN_inj : Function.Injective encN := fun _ _ h => encN_injective h

theorem bfsList_map_encN (gens : List Mns) (n : ℕ) :
    (bfsList gens n).map encN = bfsListK (gens.map encN) n := by
  rw [bfsList, closeList_map (fun _ _ h => encN_injective h) encN_mulK]
  simp [bfsListK, encN_one]

theorem mem_map_encN {L : List Mns} {g : Mns} : encN g ∈ L.map encN ↔ g ∈ L := by
  constructor
  · intro h
    obtain ⟨y, hy, hye⟩ := List.mem_map.1 h
    exact encN_injective hye ▸ hy
  · exact List.mem_map_of_mem

theorem gensA_map : gensA.map encN = gensAK := by
  simp [gensA, gensAK, encN_mnsX1, encN_mnsY1, encN_mnsX, encN_mnsY, encN_mnsW]

theorem gensL_map : gensL.map encN = gensLK := by
  simp [gensL, gensLK, encN_mnsUV, encN_mnsT, encN_mnsU, encN_mnsRho]

theorem bfsA_map : (bfsList gensA 60).map encN = bfsListK gensAK 60 := by
  rw [bfsList_map_encN, gensA_map]

theorem bfsL_map : (bfsList gensL 40).map encN = bfsListK gensLK 40 := by
  rw [bfsList_map_encN, gensL_map]

theorem stableB_of_stableK {gens L : List Mns} (h : stableK (gens.map encN) (L.map encN) = true) :
    stableB gens L = true := by
  rw [stableB_iff]
  intro s hs g hg
  simp only [stableK, List.all_eq_true, List.contains_iff_mem] at h
  have := h _ (List.mem_map_of_mem hs) _ (List.mem_map_of_mem hg)
  rwa [← encN_mul, mem_map_encN] at this

theorem nodup_of_nodupK : ∀ {L : List ℕ}, nodupK L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupK, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      List.contains_iff_mem] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_nodupK h.2⟩

variable {D : Tabs}

theorem bfs_facts (h : bfsOK D = true) :
    stableK gensAK (bfsListK gensAK 60) = true ∧ stableK gensLK (bfsListK gensLK 40) = true ∧
    nodupK (bfsListK gensAK 60) = true ∧ nodupK (bfsListK gensLK 40) = true ∧
    (bfsListK gensLK 40).length = 24 ∧
    (∀ c ∈ bfsListK gensLK 40, c ∈ bfsListK gensAK 60 → c = oneK) ∧
    (∀ a ∈ gensAK, ∀ b ∈ gensAK, mulK a b = mulK b a) ∧
    (∀ g ∈ gensLK, ∀ a ∈ gensAK, conjK g a ∈ bfsListK gensAK 60) ∧
    (∀ c ∈ bfsListK gensAK 60, mulK (mulK (mulK c c) c) c = oneK) ∧
    ((bfsListK gensAK 60).filter fun c => mulK c c == oneK).length = 8 ∧
    (∀ r ∈ l32, rd 44 D.AF r ∈ bfsListK gensAK 60) ∧
    (∀ k ∈ l24, rd 44 D.LF k ∈ bfsListK gensLK 40) := by
  simp only [bfsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun c hc hA => ?_, h7, h8, h9, h10, h11, h12⟩
  rcases h6 c hc with h' | h'
  · exact absurd hA h'
  · exact h'

theorem stable_A_of (h : bfsOK D = true) : stableB gensA (bfsList gensA 60) = true :=
  stableB_of_stableK (by rw [gensA_map, bfsA_map]; exact (bfs_facts h).1)

theorem stable_L_of (h : bfsOK D = true) : stableB gensL (bfsList gensL 40) = true :=
  stableB_of_stableK (by rw [gensL_map, bfsL_map]; exact (bfs_facts h).2.1)

theorem mem_Ag_bfs (h : bfsOK D = true) (g : Mns) : g ∈ Ag ↔ g ∈ bfsList gensA 60 :=
  mem_closure_bfs _ _ (stable_A_of h) g

theorem mem_Lg_bfs (h : bfsOK D = true) (g : Mns) : g ∈ Lg ↔ g ∈ bfsList gensL 40 :=
  mem_closure_bfs _ _ (stable_L_of h) g

theorem mem_Ag_code (h : bfsOK D = true) {g : Mns} : g ∈ Ag ↔ encN g ∈ bfsListK gensAK 60 := by
  rw [mem_Ag_bfs h, ← bfsA_map, mem_map_encN]

theorem mem_Lg_code (h : bfsOK D = true) {g : Mns} : g ∈ Lg ↔ encN g ∈ bfsListK gensLK 40 := by
  rw [mem_Lg_bfs h, ← bfsL_map, mem_map_encN]

theorem nodup_bfsA (h : bfsOK D = true) : (bfsList gensA 60).Nodup :=
  List.Nodup.of_map encN (by rw [bfsA_map]; exact nodup_of_nodupK (bfs_facts h).2.2.1)

theorem nodup_bfsL (h : bfsOK D = true) : (bfsList gensL 40).Nodup :=
  List.Nodup.of_map encN (by rw [bfsL_map]; exact nodup_of_nodupK (bfs_facts h).2.2.2.1)

theorem card_Lg_of (h : bfsOK D = true) : Nat.card Lg = 24 := by
  rw [Lg, card_closure_bfs _ 40 (stable_L_of h), List.toFinset_card_of_nodup (nodup_bfsL h),
    ← List.length_map (f := encN), bfsL_map]
  exact (bfs_facts h).2.2.2.2.1

theorem Lg_inf_Ag_of (h : bfsOK D = true) : Lg ⊓ Ag = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  refine encN_injective ?_
  rw [encN_one]
  exact (bfs_facts h).2.2.2.2.2.1 _ ((mem_Lg_code h).1 hg.1) ((mem_Ag_code h).1 hg.2)

theorem Ag_commutative_of (h : bfsOK D = true) : IsMulCommutative Ag := by
  have hpair : ({g | g ∈ gensA} : Set Mns).Pairwise Commute := by
    intro a ha b hb _
    refine encN_injective ?_
    rw [encN_mul, encN_mul]
    exact (bfs_facts h).2.2.2.2.2.2.1 _ (gensA_map ▸ List.mem_map_of_mem ha) _
      (gensA_map ▸ List.mem_map_of_mem hb)
  letI : CommGroup Ag := Subgroup.closureCommGroupOfComm hpair
  exact ⟨⟨fun a b => mul_comm a b⟩⟩

theorem Ag_exponent_of (h : bfsOK D = true) : ∀ g ∈ Ag, g * g * g * g = 1 := by
  intro g hg
  refine encN_injective ?_
  rw [encN_mul, encN_mul, encN_mul, encN_one]
  exact (bfs_facts h).2.2.2.2.2.2.2.2.1 _ ((mem_Ag_code h).1 hg)

theorem Ag_involutions_of (h : bfsOK D = true) :
    Nat.card {g : Mns // g ∈ Ag ∧ g * g = 1} = 8 := by
  classical
  have hset : {g : Mns | g ∈ Ag ∧ g * g = 1} =
      ↑((bfsList gensA 60).filter fun g => decide (g * g = 1)).toFinset := by
    ext g
    simp [mem_Ag_bfs h]
  have hF : ((bfsListK gensAK 60).filter fun c => mulK c c == oneK) =
      ((bfsList gensA 60).filter fun g => decide (g * g = 1)).map encN := by
    rw [← bfsA_map, List.filter_map]
    congr 1
  have hlen : ((bfsList gensA 60).filter fun g => decide (g * g = 1)).length = 8 := by
    rw [← List.length_map (f := encN), ← hF]
    exact (bfs_facts h).2.2.2.2.2.2.2.2.2.1
  have hc : Nat.card {g : Mns // g ∈ Ag ∧ g * g = 1} =
      ({g : Mns | g ∈ Ag ∧ g * g = 1} : Set Mns).ncard := Nat.card_coe_set_eq _
  rw [hc, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((nodup_bfsA h).filter _), hlen]

theorem Lg_le_normalizer_of (h : bfsOK D = true) : Lg ≤ NAg := by
  rw [Lg, Subgroup.closure_le]
  intro l hl
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hle : Ag ≤ Ag.comap (MulAut.conj l).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    change l * a * l⁻¹ ∈ Ag
    rw [mem_Ag_code h, ← conjK_encN]
    exact (bfs_facts h).2.2.2.2.2.2.2.1 _ (gensL_map ▸ List.mem_map_of_mem hl) _
      (gensA_map ▸ List.mem_map_of_mem ha)
  exact hle hn

theorem AF_mem (h : bfsOK D = true) {r : ℕ} (hr : r < 32) : ∃ a ∈ Ag, encN a = rd 44 D.AF r := by
  have hc := (bfs_facts h).2.2.2.2.2.2.2.2.2.2.1 r (mem_l32 hr)
  rw [← bfsA_map] at hc
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hc
  exact ⟨a, (mem_Ag_bfs h a).2 ha, he⟩

theorem LF_mem (h : bfsOK D = true) {k : ℕ} (hk : k ∈ l24) : ∃ l ∈ Lg, encN l = rd 44 D.LF k := by
  have hc := (bfs_facts h).2.2.2.2.2.2.2.2.2.2.2 k hk
  rw [← bfsL_map] at hc
  obtain ⟨l, hl, he⟩ := List.mem_map.1 hc
  exact ⟨l, (mem_Lg_bfs h l).2 hl, he⟩

end CFSG.KC.Stroth77MN

module

public import CFSG.Fischer.Polar.Delta
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  hypEnum famIndex xiImg xiInv xiAdj

local notation "PT" => perpTab ()
local notation "HX" => hypSets 1 ++ hypSets 2 ++ hypSets 3
local notation "IM" => xiImg (hypSets 1 ++ hypSets 2 ++ hypSets 3)
  (famIndex (hypSets 1 ++ hypSets 2 ++ hypSets 3))
local notation "IV" => xiInv (hypSets 1 ++ hypSets 2 ++ hypSets 3)
  (xiImg (hypSets 1 ++ hypSets 2 ++ hypSets 3) (famIndex (hypSets 1 ++ hypSets 2 ++ hypSets 3)))
local notation "AD" => xiAdj (xiInv (hypSets 1 ++ hypSets 2 ++ hypSets 3)
  (xiImg (hypSets 1 ++ hypSets 2 ++ hypSets 3) (famIndex (hypSets 1 ++ hypSets 2 ++ hypSets 3))))

local notation "XI" => xiGraph (hypOrbit 0)

structure XiFacts : Prop where
  img : xiImgOK HX IM IV = true
  inter : xiInterOK HX AD = true
  perp₁ : perpCountOK PT (rootFlags 1) = true
  perp₂ : perpCountOK PT (rootFlags 2) = true
  perp₃ : perpCountOK PT (rootFlags 3) = true
  diam : xiDiamOK AD = true
  mu : xiMuOK AD = true

theorem xiFacts : XiFacts := by
  have h := xi_certificate
  unfold xiCertificate xiChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem HX_get {k : ℕ} (hk : k < 1408) : (HX)[k]! = (hypEnum 1).1[k]! := by
  have := HU_get (i := 0) hk
  simp only [Fin.val_zero, mul_zero, zero_add] at this
  rw [hypSets, hypSets, hypSets]
  exact this

theorem flagSet_HX {k : ℕ} (hk : k < 1408) : flagSet (HX)[k]! = hypSet 0 k := by
  rw [HX_get hk]
  rfl

@[expose] def xv
    (k : ℕ) (hk : k < 1408) : hypOrbit 0 := ⟨hypSet 0 k, hypSet_mem_hypOrbit 0 k hk⟩

theorem exists_xv
    (v : hypOrbit 0) : ∃ k, ∃ hk : k < 1408, v = xv k hk := by
  obtain ⟨k, hk, hkv⟩ := mem_hypList.1 (mem_hypOrbit_iff.1 v.2)
  exact ⟨k, hk, Subtype.ext hkv⟩

theorem xiRoot_eq :
    xiRoot = xv 0 (by norm_num) := by
  apply Subtype.ext
  show hypRoot 0 = hypSet 0 0
  rw [hypSet_zero]

theorem xv_inj
    {k i : ℕ} {hk : k < 1408} {hi : i < 1408} : xv k hk = xv i hi ↔ k = i := by
  constructor
  · intro h
    exact ((hypSet_eq_iff hk hi).1 (congrArg Subtype.val h)).2
  · rintro rfl
    rfl

theorem img_facts
    {k : ℕ} (hk : k < 1408) {f : Fin 693} (hf : f ∉ hypSet 0 k) :
    (IM[k]!)[f.val]! < 1408 ∧ (IM[k]!)[f.val]! ≠ k ∧ (IV[k]!)[(IM[k]!)[f.val]!]! = f.val ∧
      tvP f '' hypSet 0 k = hypSet 0 ((IM[k]!)[f.val]!) := by
  have h0 := xiFacts.img
  unfold xiImgOK at h0
  have h := (allIn_eq_true.1 h0) k (Nat.zero_le _) hk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, h1⟩, -⟩ := h
  have h2 := (allIn_eq_true.1 h1) f.val (Nat.zero_le _) f.2
  have hSf : ((HX)[k]!)[f.val]! = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hf (by rw [← flagSet_HX hk]; exact h')
  rw [hSf, Bool.false_or] at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true] at h2
  obtain ⟨⟨⟨hlt, hne⟩, hiv⟩, hsub⟩ := h2
  refine ⟨hlt, hne, hiv, ?_⟩
  have hsub' : tvP f '' hypSet 0 k ⊆ hypSet 0 ((IM[k]!)[f.val]!) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← flagSet_HX hlt]
    have hpm : p.val ∈ members (HX)[k]! := by
      rw [mem_members]
      exact ⟨p.2, by rw [← mem_flagSet, flagSet_HX hk]; exact hp⟩
    have := hsub p.val hpm
    rw [rep_tvP f p.val p.2, idx_of_lt _ p.2] at this
    exact this
  have hc1 : (tvP f '' hypSet 0 k).ncard = 126 := by
    rw [Set.ncard_image_of_injective _ (tvP f).injective]
    exact ncard_of_mem_hypOrbit (hypSet_mem_hypOrbit 0 k hk)
  have hc2 : (hypSet 0 ((IM[k]!)[f.val]!)).ncard = 126 :=
    ncard_of_mem_hypOrbit (hypSet_mem_hypOrbit 0 _ hlt)
  exact Set.eq_of_subset_of_ncard_le hsub' (by rw [hc1, hc2]) (Set.toFinite _)

theorem inv_facts {k i : ℕ} (hk : k < 1408) (hi : i < 1408) (h : (IV[k]!)[i]! ≠ 693) :
    ∃ f : Fin 693, f.val = (IV[k]!)[i]! ∧ f ∉ hypSet 0 k ∧ (IM[k]!)[f.val]! = i := by
  have h0 := xiFacts.img
  unfold xiImgOK at h0
  have h1 := (allIn_eq_true.1 h0) k (Nat.zero_le _) hk
  simp only [Bool.and_eq_true] at h1
  have h2 := (allIn_eq_true.1 h1.2) i (Nat.zero_le _) hi
  rw [Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at h2
    obtain ⟨⟨hf, hS⟩, hIm⟩ := h2
    refine ⟨⟨_, hf⟩, rfl, fun h' => ?_, hIm⟩
    rw [← flagSet_HX hk, mem_flagSet] at h'
    rw [h'] at hS
    exact Bool.noConfusion hS

theorem iv_size {k : ℕ} (hk : k < 1408) : (IV[k]!).size = 1408 := by
  have h0 := xiFacts.img
  unfold xiImgOK at h0
  have h := (allIn_eq_true.1 h0) k (Nat.zero_le _) hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem ad_get {k i : ℕ} (hk : k < 1408) (hi : i < 1408) :
    (AD[k]!)[i]! = ((IV[k]!)[i]! != 693) := by
  unfold xiAdj
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  simp only
  rw [getElem!_pos _ i (by rw [Array.size_map, iv_size hk]; exact hi), Array.getElem_map,
    getElem!_pos _ i (by rw [iv_size hk]; exact hi)]

theorem adj_xv
    {k i : ℕ} (hk : k < 1408) (hi : i < 1408) :
    (XI).Adj (xv k hk) (xv i hi) ↔ (AD[k]!)[i]! = true := by
  rw [xiGraph_adj, ad_get hk hi, bne_iff_ne]
  constructor
  · rintro ⟨hne, f, hf, hfi⟩
    obtain ⟨hlt, -, hiv, himg⟩ := img_facts hk hf
    have hi' : (IM[k]!)[f.val]! = i :=
      ((hypSet_eq_iff hlt hi).1 ((himg.symm.trans hfi))).2
    rw [← hi', hiv]
    exact Nat.ne_of_lt f.2
  · intro h
    obtain ⟨f, -, hf, hIm⟩ := inv_facts hk hi h
    obtain ⟨-, hne, -, himg⟩ := img_facts hk hf
    refine ⟨fun h' => hne ?_, f, hf, ?_⟩
    · rw [hIm]
      exact (((hypSet_eq_iff hk hi).1 (congrArg Subtype.val h')).2).symm
    · show tvP f '' hypSet 0 k = hypSet 0 i
      rw [himg, hIm]

theorem ncard_compl_of_mem_hypOrbit {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ hypOrbit i) :
    Oᶜ.ncard = 567 := by
  have h := Set.ncard_add_ncard_compl O
  rw [ncard_of_mem_hypOrbit hO, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

theorem injOn_tvP_image
    {O : Set (Fin 693)} (hO : O ∈ hypOrbit 0) :
    Set.InjOn (fun f => tvP f '' O) Oᶜ := by
  obtain ⟨k, hk, rfl⟩ := mem_hypList.1 (mem_hypOrbit_iff.1 hO)
  intro f hf f' hf' h
  obtain ⟨hlt, -, hiv, himg⟩ := img_facts hk hf
  obtain ⟨hlt', -, hiv', himg'⟩ := img_facts hk hf'
  have : (IM[k]!)[f.val]! = (IM[k]!)[f'.val]! :=
    ((hypSet_eq_iff hlt hlt').1 (himg.symm.trans (h.trans himg'))).2
  apply Fin.ext
  rw [← hiv, ← hiv', this]

theorem tvP_image_ne
    {O : Set (Fin 693)} (hO : O ∈ hypOrbit 0) {f : Fin 693} (hf : f ∉ O) :
    tvP f '' O ≠ O := by
  obtain ⟨k, hk, rfl⟩ := mem_hypList.1 (mem_hypOrbit_iff.1 hO)
  obtain ⟨hlt, hne, -, himg⟩ := img_facts hk hf
  rw [himg]
  intro h
  exact hne ((hypSet_eq_iff hlt hk).1 h).2

theorem perpCount_root
    (i : Fin 3) {f : Fin 693} (hf : f ∉ hypRoot i) :
    {x | x ∈ hypRoot i ∧ perp f x}.ncard = 30 := by
  have hc : perpCountOK PT (rootFlags (i.val + 1)) = true := by
    fin_cases i
    · exact xiFacts.perp₁
    · exact xiFacts.perp₂
    · exact xiFacts.perp₃
  unfold perpCountOK at hc
  have h := (allIn_eq_true.1 hc) f.val (Nat.zero_le _) f.2
  have hRf : (rootFlags (i.val + 1))[f.val]! = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hf (by rw [← flagSet_rootFlags]; exact h')
  simp only [hRf, Bool.false_or, beq_iff_eq] at h
  have hset : {x | x ∈ hypRoot i ∧ perp f x} =
      {x : Fin 693 | x.val ∈ (members (rootFlags (i.val + 1))).filter
        (fun q => (PT[f.val]!)[q]!)} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, List.mem_filter, mem_members, ← flagSet_rootFlags,
      mem_flagSet, perpTab_spec f x]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨x.2, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  rw [hset, ncard_setOf_mem_list ((nodup_members _).filter _)
    (fun j hj => (mem_members.1 (List.mem_filter.1 hj).1).1), h]

theorem ncard_perp_inter
    {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ hypOrbit i) {f : Fin 693}
    (hf : f ∉ O) : {x | x ∈ O ∧ perp f x}.ncard = 30 := by
  obtain ⟨g, hg, rfl⟩ := hO
  have ha := isPolarAut_of_mem hg
  have hf' : g⁻¹ f ∉ hypRoot i := fun h => hf ⟨g⁻¹ f, h, perm_apply_inv_self g f⟩
  have hset : {x | x ∈ ⇑g '' hypRoot i ∧ perp f x} =
      ⇑g '' {x | x ∈ hypRoot i ∧ perp (g⁻¹ f) x} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hp⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rw [← ha.map_perp, perm_apply_inv_self]
      exact hp
    · rintro ⟨y, ⟨hy, hp⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rw [← ha.map_perp, perm_apply_inv_self] at hp
      exact hp
  rw [hset, Set.ncard_image_of_injective _ g.injective, perpCount_root i hf']

theorem IsClosedHyperoval.exists_not_perp
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hne : O.Nonempty) {f : Fin 693} (hf : f ∉ O) : ∃ x ∈ O, ¬ perp f x := by
  obtain ⟨i, hi⟩ := hO.exists_mem_hypOrbit hne
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  have : {x | x ∈ O ∧ perp f x} = O := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, hc x h⟩⟩
  have h1 := ncard_perp_inter hi hf
  rw [this, ncard_of_mem_hypOrbit hi] at h1
  norm_num at h1

theorem image_adj_iff {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) {O Q : Set (Fin 693)} :
    (∃ f, f ∉ O ∧ tvP f '' O = Q) ↔ ∃ f, f ∉ ⇑g '' O ∧ tvP f '' (⇑g '' O) = ⇑g '' Q := by
  have key : ∀ (h : Equiv.Perm (Fin 693)), IsPolarAut h → ∀ O Q : Set (Fin 693),
      (∃ f, f ∉ O ∧ tvP f '' O = Q) → ∃ f, f ∉ ⇑h '' O ∧ tvP f '' (⇑h '' O) = ⇑h '' Q := by
    rintro h hh O Q ⟨f, hf, rfl⟩
    refine ⟨h f, fun ⟨y, hy, hyf⟩ => hf (h.injective hyf ▸ hy), ?_⟩
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun y _ => (hh.map_tvP f y).symm
  refine ⟨key g hg O Q, fun H => ?_⟩
  have := key g⁻¹ hg.inv _ _ H
  simpa [Set.image_image, perm_inv_apply_self] using this

theorem inter_root {i : ℕ} (hi : i < 1408) (hi0 : i ≠ 0) :
    (hypSet 0 0 ∩ hypSet 0 i).ncard = if (AD[0]!)[i]! then 30 else 18 := by
  have h := xiFacts.inter
  unfold xiInterOK at h
  have h1 := (allIn_eq_true.1 h) i (Nat.one_le_iff_ne_zero.2 hi0) hi
  dsimp only at h1
  have hset : hypSet 0 0 ∩ hypSet 0 i = {x : Fin 693 | x.val ∈ (members (HX)[0]!).filter
      (fun q => ((HX)[i]!)[q]!)} := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_filter, mem_members,
      ← flagSet_HX (by norm_num : 0 < 1408), ← flagSet_HX hi, mem_flagSet, mem_flagSet]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨x.2, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  rw [hset, ncard_setOf_mem_list ((nodup_members _).filter _)
    (fun j hj => (mem_members.1 (List.mem_filter.1 hj).1).1)]
  split at h1
  · rename_i hA
    rw [ite_eq_left hA]
    exact beq_iff_eq.1 h1
  · rename_i hA
    rw [ite_eq_right hA]
    exact beq_iff_eq.1 h1

theorem exists_root_pair
    (O Q : hypOrbit 0) : ∃ i, ∃ hi : i < 1408,
    ((O : Set (Fin 693)) ∩ Q).ncard = (hypSet 0 0 ∩ hypSet 0 i).ncard ∧
      ((XI).Adj O Q ↔ (XI).Adj (xv 0 (by norm_num)) (xv i hi)) ∧ (O = Q ↔ i = 0) := by
  obtain ⟨g, hg, hO⟩ := O.2
  have ha := isPolarAut_of_mem hg
  have hQ' : ⇑g⁻¹ '' (Q : Set (Fin 693)) ∈ hypOrbit 0 := image_mem_hypOrbit (T46.inv_mem hg) Q.2
  obtain ⟨i, hi, hQi⟩ := mem_hypList.1 (mem_hypOrbit_iff.1 hQ')
  have hQ : (Q : Set (Fin 693)) = ⇑g '' hypSet 0 i := by rw [← hQi, image_inv_image]
  have hO' : (O : Set (Fin 693)) = ⇑g '' hypSet 0 0 := by rw [hO, hypSet_zero]
  have hinj : Function.Injective (Set.image ⇑g) := Set.image_injective.2 g.injective
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · rw [hO', hQ, ← Set.image_inter g.injective, Set.ncard_image_of_injective _ g.injective]
  · rw [xiGraph_adj, xiGraph_adj]
    have e1 : O ≠ Q ↔ xv 0 (by norm_num) ≠ xv i hi := by
      rw [ne_eq, ne_eq, ← Subtype.coe_inj, ← Subtype.coe_inj]
      show ¬ (O : Set (Fin 693)) = Q ↔ ¬ hypSet 0 0 = hypSet 0 i
      rw [hO', hQ, hinj.eq_iff]
    have e2 : (∃ f, f ∉ (O : Set (Fin 693)) ∧ tvP f '' (O : Set (Fin 693)) = Q) ↔
        ∃ f, f ∉ hypSet 0 0 ∧ tvP f '' hypSet 0 0 = hypSet 0 i := by
      rw [hO', hQ, ← image_adj_iff ha]
    exact and_congr e1 e2
  · rw [← Subtype.coe_inj, hO', hQ, hinj.eq_iff, hypSet_eq_iff (by norm_num) hi]
    exact ⟨fun h => h.2.symm, fun h => ⟨rfl, h.symm⟩⟩

theorem ncard_inter_of_adj
    {O Q : hypOrbit 0} (h : (XI).Adj O Q) :
    ((O : Set (Fin 693)) ∩ Q).ncard = 30 := by
  obtain ⟨i, hi, hc, hadj, heq⟩ := exists_root_pair O Q
  have hA := (adj_xv (by norm_num) hi).1 (hadj.1 h)
  have hi0 : i ≠ 0 := fun h0 => h.ne (heq.2 h0)
  rw [hc, inter_root hi hi0, ite_eq_left hA]

theorem ncard_inter_of_not_adj
    {O Q : hypOrbit 0} (hne : O ≠ Q) (h : ¬ (XI).Adj O Q) :
    ((O : Set (Fin 693)) ∩ Q).ncard = 18 := by
  obtain ⟨i, hi, hc, hadj, heq⟩ := exists_root_pair O Q
  have hA : ¬ (AD[0]!)[i]! = true := fun hA => h (hadj.2 ((adj_xv (by norm_num) hi).2 hA))
  have hi0 : i ≠ 0 := fun h0 => hne (heq.2 h0)
  rw [hc, inter_root hi hi0, ite_eq_right hA]

theorem diam_facts {v : ℕ} (hv : v < 1408) (hv0 : v ≠ 0) (hA : (AD[0]!)[v]! = false) :
    (∃ x < 1408, (AD[0]!)[x]! = true ∧ (AD[x]!)[v]! = true) ∧
      ∀ w < 1408, w ≠ 0 → (AD[0]!)[w]! = false → (AD[v]!)[w]! = true →
        ∃ x < 1408, (AD[0]!)[x]! = true ∧ (AD[x]!)[v]! = true ∧ (AD[x]!)[w]! = true := by
  have h := xiFacts.diam
  unfold xiDiamOK at h
  have h1 := (allIn_eq_true.1 h) v (Nat.one_le_iff_ne_zero.2 hv0) hv
  rw [hA, Bool.false_or, Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨?_, fun w hw hw0 hAw hvw => ?_⟩
  · obtain ⟨x, hx, hxx⟩ := anyIn_eq_true.1 h2
    rw [Bool.and_eq_true] at hxx
    exact ⟨x, hx, hxx.1, hxx.2⟩
  · have h4 := (allIn_eq_true.1 h3) w (Nat.one_le_iff_ne_zero.2 hw0) hw
    rw [hAw, hvw, Bool.false_or, Bool.not_true, Bool.false_or] at h4
    obtain ⟨x, hx, hxx⟩ := anyIn_eq_true.1 h4
    simp only [Bool.and_eq_true] at hxx
    exact ⟨x, hx, hxx.1.1, hxx.1.2, hxx.2⟩

theorem ad_zero_false
    {v : ℕ} (hv : v < 1408) (h : ¬ (XI).Adj xiRoot (xv v hv)) :
    (AD[0]!)[v]! = false := by
  rw [xiRoot_eq, adj_xv] at h
  exact Bool.eq_false_iff.2 h

theorem ne_zero_of_ne_root
    {v : ℕ} (hv : v < 1408) (h : xv v hv ≠ xiRoot) : v ≠ 0 := by
  rintro rfl
  exact h xiRoot_eq.symm

theorem xi22_D2 :
    ∀ v, v ≠ xiRoot → ¬ (XI).Adj xiRoot v → ∃ x, (XI).Adj xiRoot x ∧ (XI).Adj x v := by
  intro v hv hnadj
  obtain ⟨k, hk, rfl⟩ := exists_xv v
  obtain ⟨⟨x, hx, h0x, hxk⟩, -⟩ :=
    diam_facts hk (ne_zero_of_ne_root hk hv) (ad_zero_false hk hnadj)
  refine ⟨xv x hx, ?_, (adj_xv hx hk).2 hxk⟩
  rw [xiRoot_eq]
  exact (adj_xv _ hx).2 h0x

theorem xi22_ED :
    ∀ v w, v ≠ xiRoot → ¬ (XI).Adj xiRoot v → w ≠ xiRoot → ¬ (XI).Adj xiRoot w →
    (XI).Adj v w → ∃ x, (XI).Adj xiRoot x ∧ (XI).Adj x v ∧ (XI).Adj x w := by
  intro v w hv hnv hw hnw hvw
  obtain ⟨k, hk, rfl⟩ := exists_xv v
  obtain ⟨m, hm, rfl⟩ := exists_xv w
  obtain ⟨-, h⟩ := diam_facts hk (ne_zero_of_ne_root hk hv) (ad_zero_false hk hnv)
  obtain ⟨x, hx, h0x, hxk, hxm⟩ := h m hm (ne_zero_of_ne_root hm hw) (ad_zero_false hm hnw)
    ((adj_xv hk hm).1 hvw)
  refine ⟨xv x hx, ?_, (adj_xv hx hk).2 hxk, (adj_xv hx hm).2 hxm⟩
  rw [xiRoot_eq]
  exact (adj_xv _ hx).2 h0x

theorem induce_connected_of_tree {V : Type*} (G : SimpleGraph V) (S : Set V) {n : ℕ}
    (f : ℕ → V) (hn : 0 < n) (hmem : ∀ i < n, f i ∈ S) (hcov : ∀ x ∈ S, ∃ i < n, f i = x)
    (hpar : ∀ i < n, 0 < i → ∃ j < i, G.Adj (f j) (f i)) : (G.induce S).Connected := by
  have hreach : ∀ i (hi : i < n),
      (G.induce S).Reachable ⟨f 0, hmem 0 hn⟩ ⟨f i, hmem i hi⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rfl
      · obtain ⟨j, hj, hadj⟩ := hpar i hi hi0
        exact (ih j hj (by omega)).trans (SimpleGraph.Adj.reachable
          (SimpleGraph.induce_adj.2 hadj))
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨f 0, hmem 0 hn⟩⟩⟩
  obtain ⟨i, hi, hia⟩ := hcov a.1 a.2
  obtain ⟨j, hj, hjb⟩ := hcov b.1 b.2
  have ha : a = ⟨f i, hmem i hi⟩ := Subtype.ext hia.symm
  have hb : b = ⟨f j, hmem j hj⟩ := Subtype.ext hjb.symm
  rw [ha, hb]
  exact (hreach i hi).symm.trans (hreach j hj)

theorem xi22_MU :
    ∀ v, v ≠ xiRoot → ¬ (XI).Adj xiRoot v →
    ((XI).induce {x | (XI).Adj xiRoot x ∧ (XI).Adj x v}).Connected := by
  intro v hv hnadj
  obtain ⟨k, hk, rfl⟩ := exists_xv v
  have hk0 := ne_zero_of_ne_root hk hv
  have h := xiFacts.mu
  unfold xiMuOK at h
  have h1 := (allIn_eq_true.1 h) k (Nat.one_le_iff_ne_zero.2 hk0) hk
  rw [ad_zero_false hk hnadj, Bool.false_or] at h1
  unfold muTreeOK at h1
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨hpos, hpar⟩, htree⟩, hcov⟩ := h1
  set t := muTree AD k
  set pts := t.1
  have hpt : ∀ i < pts.size, pts[i]! < 1408 ∧ (AD[0]!)[pts[i]!]! = true ∧
      (AD[pts[i]!]!)[k]! = true ∧
        (i = 0 ∨ (t.2.1[i]! < i ∧ (AD[pts[t.2.1[i]!]!]!)[pts[i]!]! = true)) := by
    intro i hi
    have := (allIn_eq_true.1 htree) i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  let f : ℕ → hypOrbit 0 := fun i => if h : pts[i]! < 1408 then xv _ h else xiRoot
  have hf : ∀ i (hi : i < pts.size), f i = xv pts[i]! (hpt i hi).1 :=
    fun i hi => dite_eq_left (hpt i hi).1
  refine induce_connected_of_tree XI _ f hpos (fun i hi => ?_) (fun x hx => ?_) (fun i hi hi0 => ?_)
  · rw [hf i hi, Set.mem_ofPred_eq, xiRoot_eq, adj_xv, adj_xv]
    exact ⟨(hpt i hi).2.1, (hpt i hi).2.2.1⟩
  · obtain ⟨m, hm, rfl⟩ := exists_xv x
    rw [Set.mem_ofPred_eq, xiRoot_eq, adj_xv, adj_xv] at hx
    have := (allIn_eq_true.1 hcov) m (Nat.zero_le _) hm
    rw [hx.1, hx.2, Bool.and_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at this
    refine ⟨_, this.1, ?_⟩
    rw [hf _ this.1]
    exact xv_inj.2 this.2
  · rcases (hpt i hi).2.2.2 with h0 | ⟨hj, hadj⟩
    · omega
    · refine ⟨_, hj, ?_⟩
      rw [hf _ (lt_trans hj hi), hf i hi]
      exact (adj_xv _ _).2 hadj

end CFSG.Fischer

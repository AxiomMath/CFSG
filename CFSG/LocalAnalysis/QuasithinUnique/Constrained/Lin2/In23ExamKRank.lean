module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique

namespace RankCert

@[expose] def ElemAbelianLt (X : Type) [Group X] (c : ℕ) : Prop :=
  ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E < c

theorem ElemAbelianLt.of_mulEquiv {X Y : Type} [Group X] [Group Y] {c : ℕ} (e : X ≃* Y)
    (h : ElemAbelianLt Y c) : ElemAbelianLt X c := by
  intro E hE
  have h1 := h (E.map e.toMonoidHom) (isElemAbelian_map' hE _)
  rwa [card_map_of_inf_ker_eq_bot E _ (fun x _ hx => (e.map_eq_one_iff).mp hx)] at h1

@[expose] def genIdx (g gi : ℕ) (par cl : Array ℕ) (i : ℕ) : ℕ :=
  ((List.range g).find? fun j => cl[par[i]! * (g + gi) + j]! == i).getD 0

@[expose] def mulIdx (g gi : ℕ) (par cl : Array ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | f + 1, i, k =>
    if i = 0 then k
    else cl[mulIdx g gi par cl f par[i]! k * (g + gi) + genIdx g gi par cl i]!

@[expose] def dfs (mul : ℕ → ℕ → ℕ) (invs : List ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | d + 1, L, S =>
    invs.any fun c => !S.contains c && L.all (fun l => mul c l == mul l c) &&
      dfs mul invs d (c :: L) (S ++ S.map (mul c))

@[expose] def rankCheck (N g gi : ℕ) (par cl : Array ℕ) (d : ℕ) : Bool :=
  let mul := mulIdx g gi par cl N
  let invs := (List.range N).filter fun i => i != 0 && mul i i == 0
  let cands := invs.filter fun z => (List.range N).all fun i => mul z i == mul i z
  cands.any fun z => !(dfs mul invs d [z] [0, z])

section Semantics

variable {Γ : Type} [Group Γ]

structure Cayley (N g gi : ℕ) (par cl : Array ℕ) (gens : List Γ) (ι : ℕ → Γ) : Prop where
  pos : 0 < N
  zero : ι 0 = 1
  inj : ∀ i < N, ∀ k < N, ι i = ι k → i = k
  step : ∀ i < N, ∀ j < g, cl[i * (g + gi) + j]! < N ∧
    ι (cl[i * (g + gi) + j]!) = gens.getD j 1 * ι i
  parent : ∀ i < N, 0 < i → par[i]! < i ∧ ∃ j < g, ι i = gens.getD j 1 * ι par[i]!

variable {N g gi : ℕ} {par cl : Array ℕ} {gens : List Γ} {ι : ℕ → Γ}

theorem Cayley.genIdx_spec (h : Cayley N g gi par cl gens ι) {i : ℕ} (hi : i < N) (hi0 : 0 < i) :
    genIdx g gi par cl i < g ∧
      ι i = gens.getD (genIdx g gi par cl i) 1 * ι par[i]! ∧
      cl[par[i]! * (g + gi) + genIdx g gi par cl i]! = i := by
  obtain ⟨hlt, j, hj, hij⟩ := h.parent i hi hi0
  obtain ⟨hcl1, hcl2⟩ := h.step par[i]! (hlt.trans hi) j hj
  have hcli : cl[par[i]! * (g + gi) + j]! = i := h.inj _ hcl1 i hi (by rw [hcl2, hij])
  have hex : ∃ j' ∈ List.range g, (cl[par[i]! * (g + gi) + j']! == i) = true :=
    ⟨j, List.mem_range.mpr hj, by simp [hcli]⟩
  have hfind : ((List.range g).find? fun j => cl[par[i]! * (g + gi) + j]! == i).isSome = true :=
    List.find?_isSome.mpr hex
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hfind
  have hgi : genIdx g gi par cl i = j' := by
    unfold genIdx
    rw [hj']
    rfl
  have hmem := List.find?_some hj'
  have hj'g : j' < g := List.mem_range.mp (List.mem_of_find?_eq_some hj')
  have hcli' : cl[par[i]! * (g + gi) + j']! = i := by simpa using hmem
  refine ⟨by rw [hgi]; exact hj'g, ?_, by rw [hgi]; exact hcli'⟩
  obtain ⟨-, hcl2'⟩ := h.step par[i]! (hlt.trans hi) j' hj'g
  rw [hgi, ← hcl2', hcli']

theorem Cayley.mulIdx_spec (h : Cayley N g gi par cl gens ι) :
    ∀ (f i k : ℕ), i ≤ f → i < N → k < N →
      mulIdx g gi par cl f i k < N ∧ ι (mulIdx g gi par cl f i k) = ι i * ι k := by
  intro f
  induction f with
  | zero =>
    intro i k hif hi hk
    obtain rfl : i = 0 := by omega
    simp [mulIdx, h.zero, hk]
  | succ f ih =>
    intro i k hif hi hk
    by_cases hi0 : i = 0
    · subst hi0
      simp [mulIdx, h.zero, hk]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hgi, hιi, -⟩ := h.genIdx_spec hi hpos
      obtain ⟨hlt, -⟩ := h.parent i hi hpos
      obtain ⟨h1, h2⟩ := ih par[i]! k (by omega) (hlt.trans hi) hk
      obtain ⟨h3, h4⟩ := h.step _ h1 _ hgi
      simp only [mulIdx, hi0, ite_false]
      refine ⟨h3, ?_⟩
      rw [h4, h2, hιi, mul_assoc]

end Semantics

section Complete

variable {Γ : Type} [Group Γ] {N g gi : ℕ} {par cl : Array ℕ} {gens : List Γ}
  {ι : ℕ → Γ}

theorem dfs_complete (h : Cayley N g gi par cl gens ι) (E : Subgroup Γ) (hE : IsElemAbelian 2 E)
    (hsurj : ∀ x ∈ E, ∃ i < N, ι i = x) :
    ∀ (d : ℕ) (L S : List ℕ), (∀ l ∈ L, l < N ∧ ι l ∈ E) → S.length = 2 ^ L.length → 0 ∈ S →
      2 ^ (L.length + d) ≤ Nat.card E →
      dfs (mulIdx g gi par cl N)
        ((List.range N).filter fun i => i != 0 && mulIdx g gi par cl N i i == 0) d L S = true := by
  classical
  intro d
  induction d with
  | zero =>
    intro L S _ _ _ _
    rfl
  | succ d ih =>
    intro L S hL hS hS0 hcard
    have hnot : ∃ e ∈ E, ∀ s ∈ S, ι s ≠ e := by
      by_contra hcon
      push Not at hcon
      have hsub : (E : Set Γ) ⊆ ↑(S.toFinset.image ι) := fun e he => by
        obtain ⟨s, hs, hse⟩ := hcon e he
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, List.mem_toFinset.mpr hs, hse⟩)
      have h1 : Nat.card E ≤ S.length := by
        have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at h2
        have h3 : Nat.card E = (E : Set Γ).ncard := Nat.card_coe_set_eq _
        rw [h3]
        exact h2.trans ((Finset.card_image_le).trans (List.toFinset_card_le S))
      have h4 : 2 ^ L.length < 2 ^ (L.length + (d + 1)) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨e, heE, heS⟩ := hnot
    obtain ⟨c, hcN, hce⟩ := hsurj e heE
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact heS 0 hS0 (by rw [hce])
    have hcS : c ∉ S := fun hc => heS c hc hce
    have hee : e * e = 1 := by
      have := hE.2 e heE
      rwa [sq] at this
    have hmul := h.mulIdx_spec N
    have hcc : mulIdx g gi par cl N c c = 0 := by
      obtain ⟨h1, h2⟩ := hmul c c (le_of_lt hcN) hcN hcN
      apply h.inj _ h1 0 h.pos
      rw [h2, h.zero, hce, hee]
    have hcomm : ∀ l ∈ L, mulIdx g gi par cl N c l = mulIdx g gi par cl N l c := by
      intro l hl
      obtain ⟨hlN, hlE⟩ := hL l hl
      obtain ⟨h1, h2⟩ := hmul c l (le_of_lt hcN) hcN hlN
      obtain ⟨h3, h4⟩ := hmul l c (le_of_lt hlN) hlN hcN
      apply h.inj _ h1 _ h3
      rw [h2, h4, hce]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨ι l, hlE⟩)
    simp only [dfs, List.any_eq_true]
    refine ⟨c, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨List.mem_range.mpr hcN, by simp [hc0, hcc]⟩
    · have hrec := ih (c :: L) (S ++ S.map (mulIdx g gi par cl N c)) ?_ ?_ ?_ ?_
      · simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
        refine ⟨⟨by simpa using hcS, hcomm⟩, hrec⟩
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact ⟨hcN, by rw [hce]; exact heE⟩
        · exact hL l hl
      · simp [hS, pow_succ]
        ring
      · exact List.mem_append_left _ hS0
      · simpa [add_assoc, add_comm, add_left_comm] using hcard

theorem isElemAbelian_sup_zpowers {E : Subgroup Γ} (hE : IsElemAbelian 2 E) {z : Γ}
    (hz : z * z = 1) (hc : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian 2 (E ⊔ Subgroup.zpowers z) := by
  set S : Set Γ := (E : Set Γ) ∪ {z} with hSdef
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact congrArg Subtype.val (hE.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hc s hs
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact (hc t ht).symm
    · rw [Set.mem_singleton_iff] at hs ht
      rw [hs, ht]
  have hsup : E ⊔ Subgroup.zpowers z = Subgroup.closure S := by
    rw [hSdef, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  rw [hsup]
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    refine (Subgroup.closure_le _).mpr fun s hs => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun t ht => hcomm t ht s hs
  have h2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer (Subgroup.closure S : Set Γ) := by
      rw [Subgroup.centralizer_closure]
      exact h1 hx
    exact ((Subgroup.mem_centralizer_iff.mp hx') y hy).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | hs
    · have := hE.2 s hs
      rw [sq] at this ⊢
      exact this
    · rw [Set.mem_singleton_iff] at hs
      rw [hs, sq]
      exact hz
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [sq] at ihx ihy ⊢
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [h2 y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [sq] at ihx ⊢
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ihx, inv_one]

theorem card_lt_of_rankCheck [Finite Γ] {Q : Subgroup Γ} (h : Cayley N g gi par cl gens ι)
    (hιQ : ∀ i < N, ι i ∈ Q) (hsurj : ∀ x ∈ Q, ∃ i < N, ι i = x) {d : ℕ}
    (hcheck : rankCheck N g gi par cl d = true) :
    ∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E < 2 ^ (d + 1) := by
  intro E hEQ hE
  by_contra hlt
  push Not at hlt
  simp only [rankCheck, List.any_eq_true, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq,
    beq_iff_eq, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hcheck
  obtain ⟨zi, ⟨⟨hzN, hz0, hzz⟩, hzc⟩, hdfs⟩ := hcheck
  have hmul := h.mulIdx_spec N
  set z := ι zi with hzdef
  have hz2 : z * z = 1 := by
    obtain ⟨h1, h2⟩ := hmul zi zi (le_of_lt hzN) hzN hzN
    rw [← h2, hzz, h.zero]
  have hzQ : z ∈ Q := hιQ zi hzN
  have hzcQ : ∀ q ∈ Q, q * z = z * q := by
    intro q hq
    obtain ⟨i, hiN, rfl⟩ := hsurj q hq
    obtain ⟨h1, h2⟩ := hmul zi i (le_of_lt hzN) hzN hiN
    obtain ⟨h3, h4⟩ := hmul i zi (le_of_lt hiN) hiN hzN
    rw [← h4, ← h2, hzc i hiN]
  have hE' : IsElemAbelian 2 (E ⊔ Subgroup.zpowers z) :=
    isElemAbelian_sup_zpowers hE hz2 (fun e he => hzcQ e (hEQ he))
  have hE'Q : E ⊔ Subgroup.zpowers z ≤ Q :=
    sup_le hEQ ((Subgroup.zpowers_le).mpr hzQ)
  have hcard : 2 ^ (1 + d) ≤ Nat.card ↥(E ⊔ Subgroup.zpowers z) := by
    have h1 : Nat.card E ≤ Nat.card ↥(E ⊔ Subgroup.zpowers z) :=
      Subgroup.card_le_of_le le_sup_left
    have h2 : 1 + d = d + 1 := by omega
    rw [h2]
    exact hlt.trans h1
  have hdone := dfs_complete h (E ⊔ Subgroup.zpowers z) hE' (fun x hx => hsurj x (hE'Q hx)) d
    [zi] [0, zi] (by
      intro l hl
      rw [List.mem_singleton] at hl
      subst hl
      exact ⟨hzN, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩)
    (by simp) (by simp) (by simpa using hcard)
  rw [hdone] at hdfs
  exact absurd hdfs (by simp)

end Complete

section FromEnum

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem exists_cayley_of_baseEnum {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List Γ) (Ts : Array (List ℕ))
    (par cl : Array ℕ)
    (hEnum : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl) :
    ∃ ι : ℕ → Γ, Cayley Ts.size gens.length gens.length par cl gens ι ∧
      (∀ i < Ts.size, ι i ∈ Subgroup.closure {x | x ∈ gens}) ∧
      (∀ x ∈ Subgroup.closure {x | x ∈ gens}, ∃ i < Ts.size, ι i = x) ∧
      (∀ i < Ts.size, rt n (ptsOf B (genTabs n gens)) (ι i) = Ts[i]!) := by
  have hP := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  have hinjrt : ∀ {x y : Γ}, rt n (ptsOf B (genTabs n gens)) x = rt n (ptsOf B (genTabs n gens)) y →
      x = y := fun h => rt_injective hB hBP hbase h
  have hreach := benum_reach hB gens Ts par cl hEnum
  have hclosed := benum_closed hB gens Ts par cl hEnum
  classical
  let ι : ℕ → Γ := fun i =>
    if h : i < Ts.size then Classical.choose (hreach i h) else 1
  have hι : ∀ i (h : i < Ts.size), ι i ∈ Subgroup.closure {x | x ∈ gens} ∧
      rt n (ptsOf B (genTabs n gens)) (ι i) = Ts[i]! := fun i h => by
    have := Classical.choose_spec (hreach i h)
    simp only [ι, h, ↓reduceDIte]
    exact this
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hEnum
  have hgl : (genTabs n gens).length = gens.length := by simp [genTabs]
  have hgil : (genTabsInv n gens).length = gens.length := by simp [genTabsInv]
  have hGj : ∀ j < gens.length, (genTabs n gens)[j]! = (tab n (gens.getD j 1)).toArray := by
    intro j hj
    have hjG : j < (genTabs n gens).length := by rw [hgl]; exact hj
    rw [getElem!_pos _ j hjG]
    simp [genTabs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  refine ⟨ι, ⟨h0, ?_, ?_, ?_, ?_⟩, fun i hi => (hι i hi).1, ?_, fun i hi => (hι i hi).2⟩
  ·
    have hz := (hι 0 h0).2
    apply hinjrt
    rw [hz, h1, rt_one hP]
  ·
    intro i hi k hk hik
    have e1 : Ts[i]! = Ts[k]! := by
      rw [← (hι i hi).2, ← (hι k hk).2, hik]
    have hnd : Ts.toList.Nodup := List.Nodup.of_map _ h4
    have e2 : Ts.toList[i]'(by simpa using hi) = Ts.toList[k]'(by simpa using hk) := by
      simp only [Array.getElem_toList]
      rw [getElem!_pos Ts i hi, getElem!_pos Ts k hk] at e1
      exact e1
    exact (hnd.getElem_inj_iff).mp e2
  ·
    intro i hi j hj
    rw [hgl, hgil] at h5
    obtain ⟨hlt, heq⟩ := h5 i hi j hj
    refine ⟨hlt, ?_⟩
    apply hinjrt
    rw [(hι _ hlt).2, heq, hGj j hj, rt_mul_left hP, (hι i hi).2]
  ·
    intro i hi hi0
    obtain ⟨hlt, s, hs, heq⟩ := h3 i hi hi0
    refine ⟨hlt, ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    refine ⟨j, hj, ?_⟩
    apply hinjrt
    have hjd : gens.getD j 1 = x := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjx]
    rw [(hι i hi).2, rt_mul_left hP, (hι _ (hlt.trans hi)).2, hjd]
    exact heq
  ·
    intro x hx
    have hmem := hclosed x hx
    obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hmem
    have hiT' : i < Ts.size := by simpa using hi
    refine ⟨i, hiT', ?_⟩
    apply hinjrt
    rw [(hι i hiT').2, getElem!_pos Ts i hiT']
    simpa using hiT

end FromEnum

section Group

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem card_lt_of_baseEnum {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List Γ) (Ts : Array (List ℕ))
    (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hEnum : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl)
    (hsize : Ts.size = 2 ^ k) {d : ℕ}
    (hcheck : rankCheck Ts.size gens.length gens.length par cl d = true) :
    ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card E < 2 ^ (d + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hcay, hιQ, hsurj, -⟩ := exists_cayley_of_baseEnum hB hbase gens Ts par cl hEnum
  set Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens} with hQ
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [hQ, benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hQp2 : IsPGroup 2 Q := IsPGroup.of_card hcardQ
  have hQindex : Q.index = m := by
    have h1 := Q.card_mul_index
    rw [hcardQ, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hQsyl : IsSylowTwoOf Q ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hQp2, by
    rw [hQindex]; exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)⟩
  have hbound := card_lt_of_rankCheck (Q := Q) hcay hιQ hsurj hcheck
  intro E hE
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 (x : Γ) x.2)⟩
  obtain ⟨S, hS, hES⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_top : E ≤ ⊤) hEp
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS hQsyl
  have hEQ : E.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [← hg]
    exact Subgroup.map_mono hES
  have h1 := hbound _ hEQ (isElemAbelian_map' hE _)
  rwa [card_map_of_inf_ker_eq_bot E _ (fun x _ hx => (MulAut.conj g).injective (by
    rw [map_one]; exact hx))] at h1

@[expose] def RankCertS (n : ℕ) (B : List ℕ) (T : Array (Array ℕ)) (qp : List (ℕ × ℕ))
    (d : ℕ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ) : Prop :=
  (∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size) ∧
  (∀ p ∈ qp, ∀ q < n, img T[p.2]! (img T[p.1]! q) = q) ∧
  BaseEnumOK n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) Ts par cl ∧
  Ts.size = 2 ^ k ∧ rankCheck Ts.size qp.length qp.length par cl d = true

instance (n : ℕ) (B : List ℕ) (T : Array (Array ℕ)) (qp : List (ℕ × ℕ)) (d : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ) :
    Decidable (RankCertS n B T qp d Ts par cl k) := by
  unfold RankCertS; infer_instance

theorem card_lt_of_baseEnumS {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (d : ℕ) (Ts : Array (List ℕ))
    (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : RankCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp d Ts par cl k) :
    ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card E < 2 ^ (d + 1) := by
  obtain ⟨hqp, hinvt, hEnum, hsize, hcheck⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  set gens : List Γ := qp.map fun p => (slpElts a b prog).getD p.1 1 with hgens
  have hG : genTabs n gens = qp.map fun p => T[p.1]! := by
    simp only [genTabs, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    exact hE' p.1 (hqp p hp).1
  have hGi : genTabsInv n gens = qp.map fun p => T[p.2]! := by
    simp only [genTabsInv, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    have h1 : (slpElts a b prog).getD p.2 1 = ((slpElts a b prog).getD p.1 1)⁻¹ := by
      apply hinv_of
      rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
      exact hinvt p hp
    rw [← h1]
    exact hE' p.2 (hqp p hp).2
  rw [← hG, ← hGi] at hEnum
  have hlen : gens.length = qp.length := by simp [hgens]
  rw [← hlen] at hcheck
  exact card_lt_of_baseEnum hB hbase gens Ts par cl k m hcard hm hEnum hsize hcheck

end Group

end RankCert

end CFSG.QuasithinUnique.Lin2

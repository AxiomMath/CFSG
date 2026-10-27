module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSimple
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelClosure
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelEA

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel Subgroup
open CFSG.OddStandard.ChengHeld.M1b (evalE)

variable {H : Type} [Group H]

namespace S4Aux

variable {M : RegModel}

theorem set_top (R : Rep M H) :
    R.set (Array.replicate M.N true) = ((⊤ : Subgroup H) : Set H) := by
  ext h
  rw [Rep.mem_set, getElem!_pos (Array.replicate M.N true) (R.pt h) (by simpa using R.pt_lt h)]
  simp

theorem mem_iff_of (R : Rep M H) {B : Array Bool} {K : Subgroup H} (hK : R.set B = K) (h : H) :
    h ∈ R.set B ↔ h ∈ K := by
  rw [hK, SetLike.mem_coe]

theorem set_closure_of (R : Rep M H) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < M.N) {S : Set H}
    (hS : ∀ h, R.pt h ∈ gs ↔ h ∈ S) : R.set (M.closure gs) = (closure S : Set H) := by
  rw [R.set_closure hgs, show {h : H | R.pt h ∈ gs} = S from Set.ext hS]

theorem set_cl1 (R : Rep M H) (a : H) :
    R.set (M.closure [R.pt a]) = (zpowers a : Set H) := by
  rw [zpowers_eq_closure]
  exact set_closure_of R (by simp [R.pt_lt]) (fun h => by simp [R.pt_inj.eq_iff])

theorem set_cl3 (R : Rep M H) (a b c : H) :
    R.set (M.closure [R.pt a, R.pt b, R.pt c]) = (closure {a, b, c} : Set H) :=
  set_closure_of R (by simp [R.pt_lt]) (fun h => by simp [R.pt_inj.eq_iff])

theorem set_cl5 (R : Rep M H) (a b c d e : H) :
    R.set (M.closure [R.pt a, R.pt b, R.pt c, R.pt d, R.pt e]) =
      (closure {a, b, c, d, e} : Set H) :=
  set_closure_of R (by simp [R.pt_lt]) (fun h => by simp [R.pt_inj.eq_iff])

theorem size_cl3 (R : Rep M H) (a b c : H) : (M.closure [R.pt a, R.pt b, R.pt c]).size = M.N :=
  R.closure_size (by simp [R.pt_lt])

theorem size_cl5 (R : Rep M H) (a b c d e : H) :
    (M.closure [R.pt a, R.pt b, R.pt c, R.pt d, R.pt e]).size = M.N :=
  R.closure_size (by simp [R.pt_lt])

theorem eq_of_bitmap (R : Rep M H) {A B : Array Bool} {K L : Subgroup H} (hA : R.set A = K)
    (hB : R.set B = L) (h : A = B) : K = L := by
  subst h
  exact SetLike.coe_injective (hA.symm.trans hB)

theorem card_of (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) {K : Subgroup H}
    (hK : R.set B = K) : card B = Nat.card K := by
  rw [R.card_eq_ncard hB, hK]
  exact (Nat.card_coe_set_eq (K : Set H)).symm

theorem set_inf (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) {K L : Subgroup H}
    (hK : R.set A = K) (hL : R.set B = L) :
    R.set (bInter A B) = ((K ⊓ L : Subgroup H) : Set H) := by
  rw [R.set_bInter hA, hK, hL, coe_inf]

theorem set_cent_of (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) {K : Subgroup H}
    (hK : R.set B = K) : R.set (M.cent B) = (centralizer (K : Set H) : Set H) := by
  rw [R.set_cent hB, hK]
  ext h
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_centralizer_iff]
  exact forall₂_congr fun b _ => eq_comm

open scoped commutatorElement in
theorem set_commSub_of (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) (hB : B.size = M.N)
    {K L : Subgroup H} (hK : R.set A = K) (hL : R.set B = L) :
    R.set (M.commSub A B) = ((⁅K, L⁆ : Subgroup H) : Set H) := by
  have hS : {c : H | ∃ a ∈ (K : Set H), ∃ b ∈ (L : Set H), c = a⁻¹ * b⁻¹ * a * b} =
      {g | ∃ g₁ ∈ K, ∃ g₂ ∈ L, ⁅g₁, g₂⁆ = g} := by
    ext c
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp [commutatorElement_def]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp [commutatorElement_def]⟩
  rw [R.set_commSub hA hB, hK, hL, hS, Subgroup.commutator_def]

theorem pt_mem_invols (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) (h : H) :
    R.pt h ∈ M.invols B ↔ h ∈ R.set B ∧ h ≠ 1 ∧ h * h = 1 := by
  rw [R.mem_invols hB]
  constructor
  · rintro ⟨h', hpt, hh⟩
    rwa [R.pt_inj hpt] at hh
  · intro hh
    exact ⟨h, rfl, hh⟩

theorem pt_mem_ord4 (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) (h : H) :
    R.pt h ∈ M.ord4 B ↔ h ∈ R.set B ∧ orderOf h = 4 := by
  rw [R.mem_ord4 hB]
  constructor
  · rintro ⟨h', hpt, hh⟩
    rwa [R.pt_inj hpt] at hh
  · intro hh
    exact ⟨h, rfl, hh⟩

theorem ncard_invols (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    (M.invols B).length = {a | a ∈ R.set B ∧ a ≠ 1 ∧ a * a = 1}.ncard :=
  R.length_eq_ncard (Rep.invols_nodup B) (R.invols_lt hB) (pt_mem_invols R hB)

theorem ncard_invols_top (R : Rep M H) :
    (M.invols (Array.replicate M.N true)).length = {a : H | a ≠ 1 ∧ a * a = 1}.ncard := by
  rw [ncard_invols R (Array.size_replicate ..), set_top]
  simp only [coe_top, Set.mem_univ, true_and]

theorem not_bit_iff (R : Rep M H) {Z : Array Bool} {L : Subgroup H} (hZ : R.set Z = L) (h : H) :
    (!Z[R.pt h]!) = true ↔ h ∉ L := by
  rw [← mem_iff_of R hZ h, Rep.mem_set]
  simp

theorem ncard_invols_filter (R : Rep M H) {B Z : Array Bool} (hB : B.size = M.N)
    {K L : Subgroup H} (hK : R.set B = K) (hZ : R.set Z = L) :
    (List.filter (fun a => !Z[a]!) (M.invols B)).length =
      {a | a ∈ K ∧ a ∉ L ∧ a * a = 1}.ncard := by
  refine R.length_eq_ncard ((Rep.invols_nodup B).filter _)
    (fun a ha => R.invols_lt hB a (List.mem_filter.1 ha).1) fun h => ?_
  rw [List.mem_filter, pt_mem_invols R hB, not_bit_iff R hZ, mem_iff_of R hK]
  constructor
  · rintro ⟨⟨hK', -, h2⟩, hL⟩
    exact ⟨hK', hL, h2⟩
  · rintro ⟨hK', hL, h2⟩
    exact ⟨⟨hK', fun h1 => hL (h1 ▸ L.one_mem), h2⟩, hL⟩

theorem ncard_ord4_filter (R : Rep M H) {B Z : Array Bool} (hB : B.size = M.N)
    {K L : Subgroup H} (hK : R.set B = K) (hZ : R.set Z = L) :
    (List.filter (fun a => !Z[a]!) (M.ord4 B)).length =
      {a | a ∈ K ∧ a ∉ L ∧ orderOf a = 4}.ncard := by
  refine R.length_eq_ncard ((Rep.ord4_nodup B).filter _)
    (fun a ha => R.ord4_lt hB a (List.mem_filter.1 ha).1) fun h => ?_
  rw [List.mem_filter, pt_mem_ord4 R hB, not_bit_iff R hZ, mem_iff_of R hK]
  constructor
  · rintro ⟨⟨hK', h4⟩, hL⟩
    exact ⟨hK', hL, h4⟩
  · rintro ⟨hK', hL, h4⟩
    exact ⟨⟨hK', h4⟩, hL⟩

theorem invol_mem_of (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) {K L : Subgroup H}
    (hK : R.set A = K) (hL : R.set B = L)
    (h12 : (M.invols (Array.replicate M.N true)).length = 55)
    (h13 : (M.invols (bUnion A B)).length = 55) : ∀ a : H, a * a = 1 → a ∈ K ∨ a ∈ L := by
  have := R.finite
  rw [ncard_invols_top R] at h12
  rw [ncard_invols R (by rw [Rep.bUnion_size, hA]), R.set_bUnion hA, hK, hL] at h13
  have heq : {a : H | a ∈ (K : Set H) ∪ L ∧ a ≠ 1 ∧ a * a = 1} = {a | a ≠ 1 ∧ a * a = 1} :=
    Set.eq_of_subset_of_ncard_le (fun a ha => ha.2) (by rw [h12, h13])
  intro a ha
  by_cases h1 : a = 1
  · exact Or.inl (h1 ▸ K.one_mem)
  · have : a ∈ {a : H | a ≠ 1 ∧ a * a = 1} := ⟨h1, ha⟩
    rw [← heq] at this
    exact this.1

theorem no_root_of (R : Rep M H) (t : H)
    (h18 : (List.filter (fun s => M.pw s 2 == R.pt t || M.pw s 2 == R.pt t⁻¹)
      (List.range M.N)).length = 0) : ∀ s : H, s ^ 2 ≠ t ∧ s ^ 2 ≠ t⁻¹ := by
  intro s
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h18
  have := h18 (R.pt s) (List.mem_range.2 (R.pt_lt s))
  simp only [← R.pt_pow, Bool.or_eq_true, beq_iff_eq, R.pt_inj.eq_iff] at this
  exact not_or.1 this

theorem elemAb_le_of (R : Rep M H) (hN : M.N = 256) (h4 : (eaL M 4).size = 0) (E : Subgroup H)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 8 := by
  have := R.finite
  have hdvd : Nat.card E ∣ 2 ^ 8 := by
    have := E.card_subgroup_dvd_card
    rwa [R.natCard, hN] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hlt
  have hk4 : 4 ≤ k := by
    by_contra hk'
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 4)
    (by rw [hk]; exact pow_dvd_pow 2 hk4)
  have hFE : K.map E.subtype ≤ E := map_subtype_le K
  obtain ⟨l, hl, -⟩ := R.eaL_complete 4 (by norm_num) (K.map E.subtype)
    (fun a ha b hb => hab a (hFE ha) b (hFE hb)) (fun a ha => h2 a (hFE ha))
    (by rw [card_map_of_injective E.subtype_injective, hK])
  rw [Array.eq_empty_of_size_eq_zero h4] at hl
  simp at hl

theorem comm_iff_of (R : Rep M H) {W : Array Bool} (hW : W.size = M.N) {KW : Subgroup H}
    (hWs : R.set W = KW) {α : ℕ} (h23 : M.isAbelian W = (α == 0)) :
    (∀ a ∈ KW, ∀ b ∈ KW, a * b = b * a) ↔ α = 0 := by
  have := R.isAbelian_iff hW
  rw [h23, hWs, beq_iff_eq] at this
  exact this.symm

theorem W_invol_of (R : Rep M H) {V W : Array Bool} (hW : W.size = M.N) {KV KW : Subgroup H}
    (hV : R.set V = KV) (hWs : R.set W = KW) (h24 : ((M.invols W).all fun a => V[a]!) = true) :
    ∀ a ∈ KW, a * a = 1 → a ∈ KV := by
  intro a ha ha2
  by_cases h1 : a = 1
  · exact h1 ▸ KV.one_mem
  · simp only [List.all_eq_true] at h24
    exact (mem_iff_of R hV a).1
      (h24 (R.pt a) ((pt_mem_invols R hW a).2 ⟨(mem_iff_of R hWs a).2 ha, h1, ha2⟩))

theorem W_ord8_of (R : Rep M H) {W : Array Bool} (hW : W.size = M.N) {KW : Subgroup H}
    (hWs : R.set W = KW) (h25 : ((elems W).all fun a => M.ord a != 8) = true) :
    ∀ a ∈ KW, orderOf a ≠ 8 := by
  intro a ha
  simp only [List.all_eq_true, bne_iff_ne] at h25
  rw [← R.ord_eq]
  exact h25 (R.pt a) ((R.mem_elems_iff_exists_pt hW).2 ⟨a, rfl, (mem_iff_of R hWs a).2 ha⟩)

theorem W_extra_of (R : Rep M H) {W C Q : Array Bool} (hW : W.size = M.N)
    {KW KC KQ : Subgroup H} (hWs : R.set W = KW) (hC : R.set C = KC) (hQ : R.set Q = KQ)
    {α : ℕ} (h26 : (α == 0 || (bInter W (M.cent W) == C && M.commSub W W == Q)) = true)
    (hα : α = 1) : KW ⊓ centralizer (KW : Set H) = KC ∧ ⁅KW, KW⁆ = KQ := by
  have h0 : (α == 0) = false := by subst hα; decide
  rw [h0, Bool.false_or, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h26
  exact ⟨eq_of_bitmap R (set_inf R hW hWs (set_cent_of R hW hWs)) hC h26.1,
    eq_of_bitmap R (set_commSub_of R hW hW hWs hWs) hQ h26.2⟩

theorem comm_of (R : Rep M H) (c : H) {α : ℕ} (h27 : (R.pt c == 0) = (α == 0)) :
    c = 1 ↔ α = 0 := by
  have h1 : c = 1 ↔ (R.pt c == 0) = true := by
    rw [beq_iff_eq, ← R.pt_one, R.pt_inj.eq_iff]
  rw [h1, h27, beq_iff_eq]

end S4Aux

open S4Aux in
theorem struct4_facts {α : ℕ} (hα : α ≤ 1) (h : struct4OK α = true) (x : Fin 7 → H)
    (R : Rep (mkReg α) H) (hx : ∀ j : Fin 7, R.pt (x j) = (mkReg α).g j.val) :
    Struct4Facts α H x := by
  let _ := hα
  unfold struct4OK at h
  generalize mkReg α = M at h R hx
  have hx0 : M.g 0 = R.pt (x 0) := (hx 0).symm
  have hx1 : M.g 1 = R.pt (x 1) := (hx 1).symm
  have hx2 : M.g 2 = R.pt (x 2) := (hx 2).symm
  have hx3 : M.g 3 = R.pt (x 3) := (hx 3).symm
  have hx4 : M.g 4 = R.pt (x 4) := (hx 4).symm
  have hx5 : M.g 5 = R.pt (x 5) := (hx 5).symm
  have hx6 : M.g 6 = R.pt (x 6) := (hx 6).symm
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, hx0, hx1, hx2, hx3, hx4, hx5, hx6,
    ← R.pt_pow, ← R.pt_mul, ← R.pt_inv, ← R.pt_cm] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  have nD := size_cl3 R (x 0) (x 1) (x 2)
  have nR1 := size_cl5 R (x 0) (x 1) (x 2) (x 3) (x 4)
  have nR2 := size_cl5 R (x 0) (x 1) (x 2) (x 5) (x 6)
  have nV := size_cl3 R (x 0 ^ 2) (x 1) (x 0 * x 2)
  have nW := Rep.cent_size (M := M) (M.closure [R.pt (x 0 ^ 2), R.pt (x 1), R.pt (x 0 * x 2)])
  have nT := Array.size_replicate (n := M.N) (v := true)
  have eZ := set_cl1 R (x 0)
  have eD : R.set (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2)]) = (sD x : Set H) :=
    set_cl3 R _ _ _
  have eR1 : R.set (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 3), R.pt (x 4)]) =
      (sR1 x : Set H) := set_cl5 R _ _ _ _ _
  have eR2 : R.set (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 5), R.pt (x 6)]) =
      (sR2 x : Set H) := set_cl5 R _ _ _ _ _
  have eV : R.set (M.closure [R.pt (x 0 ^ 2), R.pt (x 1), R.pt (x 0 * x 2)]) = (sV x : Set H) :=
    set_cl3 R _ _ _
  have eW : R.set (M.cent (M.closure [R.pt (x 0 ^ 2), R.pt (x 1), R.pt (x 0 * x 2)])) =
      (sW x : Set H) := set_cent_of R nV eV
  have hVab := (R.isElemAb_iff nV).1 h20
  rw [eV] at hVab
  rw [eaCounts_eq] at h19
  simp only [List.cons.injEq] at h19
  exact {
    ord_t := by rw [← R.ord_eq]; exact h2
    center := eq_of_bitmap R R.set_center eZ h3
    commutator := eq_of_bitmap R (set_commSub_of R nT nT (set_top R) (set_top R)) eD h5
    card_D := (card_of R nD eD).symm.trans h6
    card_R1 := (card_of R nR1 eR1).symm.trans h7
    card_R2 := (card_of R nR2 eR2).symm.trans h8
    inf_R := eq_of_bitmap R (set_inf R nR1 eR1 eR2) eD h9
    center_R1 := eq_of_bitmap R (set_inf R nR1 eR1 (set_cent_of R nR1 eR1)) eZ h10
    center_R2 := eq_of_bitmap R (set_inf R nR2 eR2 (set_cent_of R nR2 eR2)) eZ h11
    involutions := (ncard_invols_top R).symm.trans h12
    involutions_mem := invol_mem_of R nR1 eR1 eR2 h12 h13
    R1_invol := (ncard_invols_filter R nR1 eR1 eZ).symm.trans h14
    R1_ord4 := (ncard_ord4_filter R nR1 eR1 eZ).symm.trans h15
    R2_invol := (ncard_invols_filter R nR2 eR2 eZ).symm.trans h16
    R2_ord4 := (ncard_ord4_filter R nR2 eR2 eZ).symm.trans h17
    no_root := no_root_of R (x 0) h18
    elemAb_le := elemAb_le_of R h1 h19.2.2.2.1
    V_comm := hVab.1
    V_sq := hVab.2
    card_V := (card_of R nV eV).symm.trans h21
    card_W := (card_of R nW eW).symm.trans h22
    W_comm_iff := comm_iff_of R nW eW h23
    W_invol := W_invol_of R nW eV eW h24
    W_ord8 := W_ord8_of R nW eW h25
    W_center := fun h1 => (W_extra_of R nW eW (set_cl3 R _ _ _) (set_cl1 R _) h26 h1).1
    W_commutator := fun h1 => (W_extra_of R nW eW (set_cl3 R _ _ _) (set_cl1 R _) h26 h1).2
    sq_mlxt := R.pt_inj h28
    comm_mlx := comm_of R _ h27 }

end CFSG.OddStandard.ChengHeld.Model

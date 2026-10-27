module

public import Certificates.Data.Kernel.ChengHeldS2StructK
public import CFSG.Certificates.Kernel.ChengHeldS4Sound

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.KC.ChengHeldS2

theorem s2_comm_mem {H : Type} [Group H] (N : Subgroup H) (hN : ∀ x ∈ N, ∀ y : H, x * y = y * x)
    {Γ : Set H} (hΓ : Subgroup.closure Γ = ⊤) (hc : ∀ x ∈ Γ, ∀ y ∈ Γ, x⁻¹ * y⁻¹ * x * y ∈ N)
    (a b : H) : a⁻¹ * b⁻¹ * a * b ∈ N := by
  have hn : N.Normal := ⟨fun x hx y => by rw [← hN x hx y, mul_inv_cancel_right]; exact hx⟩
  have key : ∀ x y : H, x⁻¹ * y⁻¹ * x * y ∈ N ↔
      QuotientGroup.mk' N x * QuotientGroup.mk' N y =
        QuotientGroup.mk' N y * QuotientGroup.mk' N x := by
    intro x y
    have e : (y * x)⁻¹ * (x * y) = x⁻¹ * y⁻¹ * x * y := by group
    rw [← map_mul, ← map_mul, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, e]
  have all : ∀ c : H, (∀ y ∈ Γ, QuotientGroup.mk' N c * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N c) → ∀ z : H,
      QuotientGroup.mk' N c * QuotientGroup.mk' N z =
        QuotientGroup.mk' N z * QuotientGroup.mk' N c := by
    intro c hcy z
    have hle : Subgroup.closure Γ ≤
        Subgroup.comap (QuotientGroup.mk' N) (Subgroup.centralizer {QuotientGroup.mk' N c}) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hcy y hy
    have hz := hle (by rw [hΓ]; exact Subgroup.mem_top z)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hz
    exact hz _ rfl
  rw [key]
  refine all a (fun y hy => ?_) b
  exact (all y (fun x hx => (key y x).1 (hc y hy x hx)) a).symm

variable {M : RegModel} {n : ℕ} {m : ℕ → ℕ → ℕ} {inv g : ℕ → ℕ}

theorem s2_arr_ext {A B : Array Bool} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ z : ℕ, A[z]! = B[z]!) : A = B :=
  Array.ext (by rw [hA, hB]) fun i hi hi' => by
    rw [← getElem!_pos A i hi, ← getElem!_pos B i hi', h]

theorem s2_arr_eq {H : Type} [Group H] (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N)
    (hB : B.size = M.N) (h : R.set A = R.set B) : A = B := by
  refine Array.ext (by rw [hA, hB]) fun i hi hi' => ?_
  obtain ⟨x, rfl⟩ := R.pt_surj i (hA ▸ hi)
  have := Set.ext_iff.mp h x
  rw [R.mem_set, R.mem_set] at this
  rw [← getElem!_pos A _ hi, ← getElem!_pos B _ hi']
  exact Bool.eq_iff_iff.mpr this

theorem s2_set_full {H : Type} [Group H] (R : Rep M H) :
    R.set (Array.replicate M.N true) = Set.univ := by
  ext h
  rw [R.mem_set, getElem!_pos _ _ (by rw [Array.size_replicate]; exact R.pt_lt h),
    Array.getElem_replicate]
  simp

theorem s2_full_get (hN : M.N = n) (i : ℕ) : (Array.replicate M.N true)[i]! = decide (i < n) := by
  by_cases hi : i < n
  · rw [getElem!_pos _ _ (by rw [Array.size_replicate, hN]; exact hi), Array.getElem_replicate,
      decide_eq_true hi]
  · rw [getElem!_neg _ _ (by rw [Array.size_replicate, hN]; exact hi), decide_eq_false hi]
    rfl

theorem s2_bInter_get {A B : Array Bool} {f h : ℕ → Bool} (hA : A.size = n)
    (hf : ∀ i, A[i]! = f i) (hh : ∀ i, B[i]! = h i) (i : ℕ) :
    (bInter A B)[i]! = (decide (i < n) && (f i && h i)) := by
  unfold bInter
  by_cases hi : i < n
  · rw [getElem!_pos _ _ (by simp [hA, hi]), Array.getElem_map, Array.getElem_range, hf, hh,
      decide_eq_true hi, Bool.true_and]
  · rw [getElem!_neg _ _ (by simp [hA, hi]), decide_eq_false hi]
    rfl

theorem s2_bUnion_get {A B : Array Bool} {f h : ℕ → Bool} (hA : A.size = n)
    (hf : ∀ i, A[i]! = f i) (hh : ∀ i, B[i]! = h i) (i : ℕ) :
    (bUnion A B)[i]! = (decide (i < n) && (f i || h i)) := by
  unfold bUnion
  by_cases hi : i < n
  · rw [getElem!_pos _ _ (by simp [hA, hi]), Array.getElem_map, Array.getElem_range, hf, hh,
      decide_eq_true hi, Bool.true_and]
  · rw [getElem!_neg _ _ (by simp [hA, hi]), decide_eq_false hi]
    rfl

theorem s2_bInter_size {A B : Array Bool} (hA : A.size = n) : (bInter A B).size = n := by
  simp [bInter, hA]

theorem s2_bUnion_size {A B : Array Bool} (hA : A.size = n) : (bUnion A B).size = n := by
  simp [bUnion, hA]

theorem s2_center_size (hN : M.N = n) : M.center.size = n := by
  simp [RegModel.center, hN]

theorem s2_center_get (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (x : ℕ) :
    M.center[x]! = centralW n m x := by
  unfold RegModel.center centralW
  by_cases hx : x < n
  · rw [getElem!_pos _ _ (by simp [hN, hx]), Array.getElem_map, Array.getElem_range,
      decide_eq_true hx, Bool.true_and, hN]
    simp only [hm]
  · rw [getElem!_neg _ _ (by simp [hN, hx]), decide_eq_false hx]
    rfl

theorem s2_ord_eq (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (a : ℕ) :
    M.ord a = ordW n m a := by
  unfold RegModel.ord ordW
  simp only [hN, pw_eq hm]

theorem s2_isElemAb_eq (hm : ∀ a b, M.m a b = m a b) {B : Array Bool} {f : ℕ → Bool}
    (hs : B.size = n) (hf : ∀ i, B[i]! = f i) : M.isElemAb B = elemAbW n m f := by
  unfold RegModel.isElemAb RegModel.isAbelian elemAbW
  simp only [elems_eq hs hf, hm]

theorem s2_invols_eq (hm : ∀ a b, M.m a b = m a b) {B : Array Bool} {f : ℕ → Bool}
    (hs : B.size = n) (hf : ∀ i, B[i]! = f i) : M.invols B = involsW n m f := by
  unfold RegModel.invols involsW
  simp only [elems_eq hs hf, hm]

theorem s2_commSub {H : Type} [Group H] (R : Rep M H) (hT : TreeSpec M) (hN : M.N = n)
    (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a) (hg : ∀ j, M.g j = g j)
    (hn : 0 < n) (hmlt : ∀ x y, x < n → y < n → m x y < n) {K : ℕ}
    (hD : clW n m [g 0, g 1, g 2] K = true) (hc : s2CmW n m inv g K = true) :
    (M.center == M.closure [g 0, g 1, g 2]) = true ∧
      (M.commSub (Array.replicate M.N true) (Array.replicate M.N true) ==
        M.closure [g 0, g 1, g 2]) = true := by
  unfold s2CmW at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hcl, heq⟩, hglt⟩, hcen⟩ := hc
  obtain ⟨sD, gD⟩ := closure_bit hN hm hn hmlt hD
  obtain ⟨sG, gG⟩ := closure_bit hN hm hn hmlt hcl
  have hcenter : (M.center == M.closure [g 0, g 1, g 2]) = true := by
    rw [beq_bitmap (s2_center_size hN) sD (s2_center_get hN hm) gD, List.all_eq_true]
    exact fun x hx => hcen x (List.mem_range.1 hx)
  refine ⟨hcenter, ?_⟩
  have hGD : M.closure (genCmW m inv g) = M.closure [g 0, g 1, g 2] :=
    s2_arr_ext sG sD fun z => by rw [gG, gD, Nat.eq_of_beq_eq_true heq]
  have hDl : ∀ x ∈ [g 0, g 1, g 2], x < M.N := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hN]
    rcases hx with rfl | rfl | rfl
    exacts [hglt 0 (by norm_num), hglt 1 (by norm_num), hglt 2 (by norm_num)]
  have hGl : ∀ x ∈ genCmW m inv g, x < M.N := by
    unfold clW at hcl
    rw [Bool.and_eq_true, List.all_eq_true] at hcl
    intro x hx
    rw [hN]
    simpa [Nat.blt_eq] using hcl.1 x hx
  set SD := Subgroup.closure {h : H | R.pt h ∈ [g 0, g 1, g 2]} with hSD
  have hsD := R.set_closure hDl
  have hsG := R.set_closure hGl
  rw [hGD, hsD] at hsG
  have hcentral : ∀ x ∈ SD, ∀ y : H, x * y = y * x := by
    intro x hx y
    have hx' : x ∈ R.set (M.closure [g 0, g 1, g 2]) := by rw [hsD]; exact hx
    rw [R.mem_set, gD] at hx'
    have hxn : R.pt x < n := hN ▸ R.pt_lt x
    have hc := hcen (R.pt x) hxn
    rw [hx', beq_iff_eq] at hc
    unfold centralW at hc
    rw [Bool.and_eq_true, List.all_eq_true] at hc
    have := hc.2 (R.pt y) (List.mem_range.2 (hN ▸ R.pt_lt y))
    rw [beq_iff_eq, ← hm, ← hm, ← R.pt_mul, ← R.pt_mul] at this
    exact R.pt_inj this
  have hgN : ∀ j < 7, M.gpt[j]! < M.N := fun j hj => by
    change M.g j < M.N
    rw [hg, hN]
    exact hglt j hj
  have hΓ : Subgroup.closure {h : H | ∃ j < 7, R.pt h = M.gpt[j]!} = ⊤ := by
    rw [← top_closure R hT hgN]
    congr 1
    ext h
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨j, hj, e⟩
      rw [e]
      interval_cases j <;> simp [RegModel.g]
    · rintro (e | e | e | e | e | e | e)
      exacts [⟨0, by norm_num, e⟩, ⟨1, by norm_num, e⟩, ⟨2, by norm_num, e⟩,
        ⟨3, by norm_num, e⟩, ⟨4, by norm_num, e⟩, ⟨5, by norm_num, e⟩, ⟨6, by norm_num, e⟩]
  have hgc : ∀ x ∈ {h : H | ∃ j < 7, R.pt h = M.gpt[j]!}, ∀ y ∈ {h : H | ∃ j < 7,
      R.pt h = M.gpt[j]!}, x⁻¹ * y⁻¹ * x * y ∈ SD := by
    rintro x ⟨i, hi, hxi⟩ y ⟨j, hj, hyj⟩
    have hin : R.pt (x⁻¹ * y⁻¹ * x * y) ∈ genCmW m inv g := by
      rw [R.pt_cm, hxi, hyj]
      unfold genCmW
      rw [List.mem_flatMap]
      refine ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩
      change cmW m inv (g i) (g j) = M.cm (M.g i) (M.g j)
      unfold cmW RegModel.cm
      rw [hg, hg, hm, hm, hm, hinv, hinv]
    have : x⁻¹ * y⁻¹ * x * y ∈ (SD : Set H) := by
      rw [hsG]
      exact Subgroup.subset_closure hin
    exact this
  have eSD : SD = Subgroup.closure {h : H | R.pt h ∈ genCmW m inv g} := SetLike.coe_injective hsG
  have hfull : (Array.replicate M.N true).size = M.N := Array.size_replicate
  rw [beq_iff_eq]
  refine s2_arr_eq R (R.commSub_size hfull hfull) (by rw [sD, hN]) ?_
  rw [R.set_commSub hfull hfull, s2_set_full, hsD, SetLike.coe_set_eq]
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro c ⟨a, -, b, -, rfl⟩
    exact s2_comm_mem SD hcentral hΓ hgc a b
  · refine (le_of_eq eSD).trans ((Subgroup.closure_le _).2 ?_)
    intro h hh
    rw [Set.mem_setOf_eq] at hh
    unfold genCmW at hh
    rw [List.mem_flatMap] at hh
    obtain ⟨i, hi, hh⟩ := hh
    obtain ⟨j, hj, hij⟩ := List.mem_map.1 hh
    rw [List.mem_range] at hi hj
    obtain ⟨x, hx⟩ := R.pt_surj (g i) (by rw [hN]; exact hglt i hi)
    obtain ⟨y, hy⟩ := R.pt_surj (g j) (by rw [hN]; exact hglt j hj)
    have e : R.pt (x⁻¹ * y⁻¹ * x * y) = R.pt h := by
      rw [R.pt_cm, hx, hy, ← hij]
      unfold cmW RegModel.cm
      rw [hm, hm, hm, hinv, hinv]
    rw [← R.pt_inj e]
    exact Subgroup.subset_closure ⟨x, Set.mem_univ _, y, Set.mem_univ _, rfl⟩

theorem struct2OK_of {H : Type} [Group H] (R : Rep (mkReg 2) H) (hT : TreeSpec (mkReg 2))
    (hN : (mkReg 2).N = n) (hm : ∀ a b, (mkReg 2).m a b = m a b)
    (hinv : ∀ a, (mkReg 2).inv[a]! = inv a) (hg : ∀ j, (mkReg 2).g j = g j) (hn : 0 < n)
    (hmlt : ∀ x y, x < n → y < n → m x y < n) (h128 : (n == 128) = true) {K : ℕ}
    (hcl : (clW n m [g 0, g 1, g 2] K && clW n m [g 0, g 1, g 2, g 3, g 4] K &&
      clW n m [g 0, g 1, g 2, g 5, g 6] K) = true)
    (hc : s2CmW n m inv g K = true) (hea : (mkReg 2).eaCounts = [55, 303, 309, 62, 2, 0])
    (hr : s2RestW n m g K = true) : struct2OK = true := by
  simp only [Bool.and_eq_true] at hcl
  obtain ⟨⟨cD, c1⟩, c2⟩ := hcl
  obtain ⟨sD, gD⟩ := closure_bit hN hm hn hmlt cD
  obtain ⟨s1, g1⟩ := closure_bit hN hm hn hmlt c1
  obtain ⟨s2, g2⟩ := closure_bit hN hm hn hmlt c2
  obtain ⟨hcen, hcomm⟩ := s2_commSub R hT hN hm hinv hg hn hmlt cD hc
  have hfull : (Array.replicate (mkReg 2).N true).size = n := by
    rw [Array.size_replicate, hN]
  rw [← hr]
  unfold struct2OK s2RestW rootW
  simp only [hg, hcen, hcomm, hea, s2_invols_eq hm hfull (s2_full_get hN)]
  simp only [hN, h128, beq_self_eq_true, Bool.true_and, Bool.and_true,
    s2_ord_eq hN hm, pw_eq hm, hm, card_eq sD gD, card_eq s1 g1, card_eq s2 g2,
    s2_isElemAb_eq hm s1 g1, s2_isElemAb_eq hm s2 g2,
    beq_bitmap (s2_bInter_size s1) sD (s2_bInter_get s1 g1 g2) gD,
    s2_invols_eq hm (s2_bUnion_size s1) (s2_bUnion_get s1 g1 g2)]

end CFSG.KC.ChengHeldP

end

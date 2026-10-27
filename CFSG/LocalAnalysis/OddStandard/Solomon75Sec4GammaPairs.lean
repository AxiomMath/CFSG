module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaElem
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaJordan
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG.Open

section Pairs

variable {n m : ℕ} {hm : 2 * m ≤ n}

@[expose] noncomputable def pairSwap (n m : ℕ) (hm : 2 * m ≤ n) (i : Fin m) : Perm (Fin n) :=
  swap (pairEmb n m hm (i, 0)) (pairEmb n m hm (i, 1))

theorem pairEmb_zero_ne_one (i : Fin m) : pairEmb n m hm (i, 0) ≠ pairEmb n m hm (i, 1) := by
  intro h
  have := (pairEmb n m hm).injective h
  simp at this

theorem pairEmb_ne_of_ne {i j : Fin m} (hij : i ≠ j) (b b' : Fin 2) :
    pairEmb n m hm (i, b) ≠ pairEmb n m hm (j, b') := by
  intro h
  exact hij (by simpa using congrArg Prod.fst ((pairEmb n m hm).injective h))

theorem pairSwap_mem (i : Fin m) :
    pairSwap n m hm i ∈ invSwapGrp (stdInv n m hm) stdInv_mul_self :=
  swapPair_mem_invSwapGrp i

theorem card_support_pairSwap (i : Fin m) : (pairSwap n m hm i).support.card = 2 :=
  card_support_swap (pairEmb_zero_ne_one i)

theorem sign_pairSwap (i : Fin m) : sign (pairSwap n m hm i) = -1 :=
  sign_swap (pairEmb_zero_ne_one i)

theorem pairSwap_apply_of_ne {i : Fin m} {x : Fin n} (h0 : x ≠ pairEmb n m hm (i, 0))
    (h1 : x ≠ pairEmb n m hm (i, 1)) : pairSwap n m hm i x = x :=
  swap_apply_of_ne_of_ne h0 h1

theorem pairSwap_apply_of_ne_index {i j : Fin m} (hij : i ≠ j) (b : Fin 2) :
    pairSwap n m hm i (pairEmb n m hm (j, b)) = pairEmb n m hm (j, b) :=
  pairSwap_apply_of_ne (pairEmb_ne_of_ne hij.symm _ _) (pairEmb_ne_of_ne hij.symm _ _)

theorem disjoint_pairSwap {i j : Fin m} (hij : i ≠ j) :
    Perm.Disjoint (pairSwap n m hm i) (pairSwap n m hm j) := by
  intro x
  by_cases h0 : x = pairEmb n m hm (i, 0)
  · right
    rw [h0]
    exact pairSwap_apply_of_ne_index hij.symm 0
  by_cases h1 : x = pairEmb n m hm (i, 1)
  · right
    rw [h1]
    exact pairSwap_apply_of_ne_index hij.symm 1
  · left
    exact pairSwap_apply_of_ne h0 h1

@[expose] noncomputable def quadSwap (n m : ℕ) (hm : 2 * m ≤ n) (t : Fin 4 → Fin m) :
    Perm (Fin n) :=
  pairSwap n m hm (t 0) * pairSwap n m hm (t 1) * pairSwap n m hm (t 2) * pairSwap n m hm (t 3)

theorem quadSwap_mem (t : Fin 4 → Fin m) :
    quadSwap n m hm t ∈ invSwapGrp (stdInv n m hm) stdInv_mul_self :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (pairSwap_mem _) (pairSwap_mem _))
    (pairSwap_mem _)) (pairSwap_mem _)

theorem quadSwap_mul_self (t : Fin 4 → Fin m) : quadSwap n m hm t * quadSwap n m hm t = 1 :=
  invSwapGrp_mul_self stdInv_mul_self (quadSwap_mem t)

theorem sign_quadSwap (t : Fin 4 → Fin m) : sign (quadSwap n m hm t) = 1 := by
  simp only [quadSwap, Perm.sign_mul, sign_pairSwap]
  decide

theorem card_support_quadSwap {t : Fin 4 → Fin m} (ht : Function.Injective t) :
    (quadSwap n m hm t).support.card = 8 := by
  have hne : ∀ i j : Fin 4, i ≠ j → t i ≠ t j := fun i j h => ht.ne h
  have d01 := disjoint_pairSwap (n := n) (hm := hm) (hne 0 1 (by decide))
  have d02 := disjoint_pairSwap (n := n) (hm := hm) (hne 0 2 (by decide))
  have d03 := disjoint_pairSwap (n := n) (hm := hm) (hne 0 3 (by decide))
  have d12 := disjoint_pairSwap (n := n) (hm := hm) (hne 1 2 (by decide))
  have d13 := disjoint_pairSwap (n := n) (hm := hm) (hne 1 3 (by decide))
  have d23 := disjoint_pairSwap (n := n) (hm := hm) (hne 2 3 (by decide))
  unfold quadSwap
  rw [Perm.Disjoint.card_support_mul ((d03.mul_left d13).mul_left d23),
    Perm.Disjoint.card_support_mul (d02.mul_left d12), Perm.Disjoint.card_support_mul d01]
  simp only [card_support_pairSwap]

theorem quadSwap_apply_of_forall_ne {t : Fin 4 → Fin m} {x : Fin n}
    (hx : ∀ (k : Fin 4) (b : Fin 2), x ≠ pairEmb n m hm (t k, b)) : quadSwap n m hm t x = x := by
  simp only [quadSwap, Perm.mul_apply]
  rw [pairSwap_apply_of_ne (hx 3 0) (hx 3 1), pairSwap_apply_of_ne (hx 2 0) (hx 2 1),
    pairSwap_apply_of_ne (hx 1 0) (hx 1 1), pairSwap_apply_of_ne (hx 0 0) (hx 0 1)]

end Pairs

section Star

variable {n m : ℕ} {hm : 2 * m ≤ n}

@[expose] noncomputable def pairIdx (n m : ℕ) (hm : 2 * m ≤ n) (x : Fin n) : Finset (Fin m) :=
  open Classical in Finset.univ.filter fun i => ∃ b, x = pairEmb n m hm (i, b)

theorem card_pairIdx_le_one (x : Fin n) : (pairIdx n m hm x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [pairIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  obtain ⟨b, hb⟩ := hi
  obtain ⟨b', hb'⟩ := hj
  have := (pairEmb n m hm).injective (hb.symm.trans hb')
  simpa using congrArg Prod.fst this

theorem pairIdx_eq_empty (x : Fin n) (hx : 2 * m ≤ x.val) : pairIdx n m hm x = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  simp only [pairIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨b, hb⟩ := hi
  have h1 := congrArg Fin.val hb
  simp only [pairEmb, Function.Embedding.coeFn_mk] at h1
  have := i.2
  have := b.2
  omega

theorem notMem_of_notMem_pairIdx {x : Fin n} {i : Fin m} (hi : i ∉ pairIdx n m hm x) (b : Fin 2) :
    x ≠ pairEmb n m hm (i, b) := by
  intro h
  apply hi
  simp only [pairIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b, h⟩

theorem exists_quad_indices (A : Finset (Fin m)) (hA : A.card + 4 ≤ m) :
    ∃ t : Fin 4 → Fin m, Function.Injective t ∧ ∀ k, t k ∉ A := by
  have hc : Fintype.card (Fin 4) ≤ Fintype.card ↥(Aᶜ) := by
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_compl]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun k => (e k).1, fun a b h => e.injective (Subtype.ext h), fun k => ?_⟩
  exact Finset.mem_compl.1 (e k).2

theorem swap_mul_comm_of_fix {α : Type*} [DecidableEq α] {f : Perm α} {a b : α} (ha : f a = a)
    (hb : f b = b) : swap a b * f = f * swap a b := by
  have h := Equiv.swap_apply_apply f a b
  rw [ha, hb] at h
  calc swap a b * f = (f * swap a b * f⁻¹) * f := by rw [← h]
    _ = f * swap a b := by group

theorem three_cycle_comm_of_fix {α : Type*} [DecidableEq α] {f : Perm α} {a b c : α}
    (ha : f a = a) (hb : f b = b) (hc : f c = c) :
    (swap a b * swap a c) * f = f * (swap a b * swap a c) := by
  calc (swap a b * swap a c) * f = swap a b * (swap a c * f) := by group
    _ = swap a b * (f * swap a c) := by rw [swap_mul_comm_of_fix ha hc]
    _ = (swap a b * f) * swap a c := by group
    _ = (f * swap a b) * swap a c := by rw [swap_mul_comm_of_fix ha hb]
    _ = f * (swap a b * swap a c) := by group

end Star

section Main

variable {n : ℕ} {K : Type} [Group K] [Finite K]

theorem exists_sylow_gamma_eq_top_of_pairs (hn : 11 ≤ n) (C : CoverSetup n K) :
    ∃ S : Sylow 2 K, properTwoGenCoreGamma (S : Subgroup K) 2 = ⊤ := by
  have hn8 : 8 ≤ n := by omega
  set m := n / 2 with hmdef
  have hm : 2 * m ≤ n := Nat.mul_div_le n 2
  set T := invSwapGrp (stdInv n m hm) stdInv_mul_self with hT
  have hTp : IsPGroup 2 T := fun g => ⟨1, by
    have := invSwapGrp_mul_self stdInv_mul_self g.2
    apply Subtype.ext
    simpa [pow_two] using this⟩
  have hker : IsPGroup 2 C.ρ.ker := by
    refine IsPGroup.of_card (n := 1) ?_
    have : C.ρ.ker = center K := by
      ext x
      rw [MonoidHom.mem_ker, C.ρ_eq_one_iff]
    rw [this, C.center_card, pow_one]
  have hW : IsPGroup 2 (T.comap C.ρ) := hTp.comap_of_ker_isPGroup C.ρ hker
  obtain ⟨S, hWS⟩ := hW.exists_le_sylow
  let ι := {t : Fin 4 → Fin m // Function.Injective t}
  let u : ι → Perm (Fin n) := fun t => quadSwap n m hm t.1
  have hu2 : ∀ t : ι, u t * u t = 1 := fun t => quadSwap_mul_self t.1
  have hus : ∀ t : ι, sign (u t) = 1 := fun t => sign_quadSwap t.1
  have hucard : ∀ t : ι, (u t).support.card = 8 := fun t => card_support_quadSwap t.2
  have hu1 : ∀ t : ι, u t ≠ 1 := fun t h => by
    have := hucard t
    rw [h, Perm.support_one, Finset.card_empty] at this
    omega
  have h8 : ∀ t : ι, 8 ∣ (u t).support.card := fun t => by rw [hucard t]
  have hES : ∀ t : ι, ((pairSub (u t) (hu2 t)).comap C.ρ : Subgroup K) ≤ (S : Subgroup K) :=
    fun t => (Subgroup.comap_mono (pairSub_le_of_mem (hu2 t) (quadSwap_mem t.1))).trans hWS
  have hr : ∀ t : ι, 2 ≤ Open.pRank 2 ((pairSub (u t) (hu2 t)).comap C.ρ) := fun t =>
    C.two_le_pRank_comap_pairSub hn8 (hu2 t) (hu1 t) (hus t) (h8 t)
  set H := (properTwoGenCoreGamma (S : Subgroup K) 2).map C.ρ with hH
  have hN : ∀ (t : ι) (g : Perm (Fin n)), sign g = 1 → g * u t = u t * g → g ∈ H := by
    intro t g hg hgu
    obtain ⟨y, hy⟩ := C.exists_ρ_eq hg
    have hyN := C.mem_normalizer_comap_pairSub (hu2 t) (x := y) (by rw [hy]; exact hgu)
    exact ⟨y, normalizer_le_gamma (hES t) (hr t) hyN, hy⟩
  let F : ι → Finset (Fin n) := fun t => (u t).supportᶜ
  have hFmem : ∀ (t : ι) (x : Fin n), x ∈ F t ↔ u t x = x := fun t x => by
    simp [F, Perm.mem_support]
  have h3 : ∀ t : ι, 3 ≤ (F t).card := fun t => by
    simp only [F, Finset.card_compl, Fintype.card_fin, hucard t]
    omega
  have hHyp : ∀ (t : ι) (a b c : Fin n), a ∈ F t → b ∈ F t → c ∈ F t → a ≠ b → a ≠ c → b ≠ c →
      swap a b * swap a c ∈ H := by
    intro t a b c ha hb hc hab hac hbc
    have ha' := (hFmem t a).1 ha
    have hb' := (hFmem t b).1 hb
    have hc' := (hFmem t c).1 hc
    refine hN t _ ?_ (three_cycle_comm_of_fix ha' hb' hc')
    rw [Perm.sign_mul, sign_swap hab, sign_swap hac]
    decide
  set w₀ : Fin n := ⟨n - 1, by omega⟩ with hw₀
  have hstar : ∀ x : Fin n, ∃ t : ι, x ∈ F t ∧ w₀ ∈ F t := by
    intro x
    have hA : (pairIdx n m hm x ∪ pairIdx n m hm w₀).card + 4 ≤ m := by
      rcases Nat.even_or_odd n with hev | hod
      · have h1 := card_pairIdx_le_one (hm := hm) x
        have h2 := card_pairIdx_le_one (hm := hm) w₀
        have := Finset.card_union_le (pairIdx n m hm x) (pairIdx n m hm w₀)
        obtain ⟨r, hr⟩ := hev
        omega
      · have h1 := card_pairIdx_le_one (hm := hm) x
        have h2 : pairIdx n m hm w₀ = ∅ := by
          apply pairIdx_eq_empty
          obtain ⟨r, hr⟩ := hod
          simp only [hw₀]
          omega
        rw [h2, Finset.union_empty]
        obtain ⟨r, hr⟩ := hod
        omega
    obtain ⟨t, ht, htA⟩ := exists_quad_indices _ hA
    refine ⟨⟨t, ht⟩, (hFmem _ x).2 ?_, (hFmem _ w₀).2 ?_⟩
    · exact quadSwap_apply_of_forall_ne fun k b => notMem_of_notMem_pairIdx
        (fun h => htA k (Finset.mem_union_left _ h)) b
    · exact quadSwap_apply_of_forall_ne fun k b => notMem_of_notMem_pairIdx
        (fun h => htA k (Finset.mem_union_right _ h)) b
  have hAlt := alt_le_of_star H w₀ F h3 hHyp hstar
  refine ⟨S, ?_⟩
  obtain ⟨t₀, -, -⟩ := hstar w₀
  have hcen : center K ≤ properTwoGenCoreGamma (S : Subgroup K) 2 :=
    center_le_gamma (hES t₀) (hr t₀)
  rw [eq_top_iff]
  intro k _
  obtain ⟨γ, hγ, hγk⟩ := hAlt (Perm.mem_alternatingGroup.2 (C.sign_ρ k))
  have hkγ : k * γ⁻¹ ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hγk, mul_inv_cancel]
  have : k = (k * γ⁻¹) * γ := by group
  rw [this]
  exact Subgroup.mul_mem _ (hcen hkγ) hγ

end Main

end CFSG.OddStandard.Solomon75.AhatData

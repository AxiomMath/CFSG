module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootW12

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] {a : ℕ} [Finite K] [CharP K F4.prime]

theorem weylS_mem_normalizer_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylS K ∈ normalizer (radS K a : Set (ModGL F4.tag K)) := by
  rw [radS_eq_complement hK]
  exact rankOneGroupOne_le_normalizer_complement hK weylS_mem_leviN

theorem torusH_le_normalizer_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    torusH K a ≤ normalizer (radS K a : Set (ModGL F4.tag K)) := by
  rw [(radS_spec hK).1]
  exact torusH_le_normalizer_rootSpan_inf hK fun α hα => hα.1

theorem radS_le_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) : radS K a ≤ F4.reeGamma K a := by
  rw [(radS_spec hK).1]
  exact inf_le_right

theorem S1_le_centralizer_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S1 K a ≤ centralizer (radS K a : Set (ModGL F4.tag K)) := by
  have hc : ∀ {x y : ModGL F4.tag K}, ⁅x, y⁆ = 1 → x * y = y * x := fun h =>
    commutatorElement_eq_one_iff_mul_comm.1 h
  have key : ∀ k ∈ ({.i1, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx), ∀ l ∈
      ({.i11, .i12} : Finset Idx), ∀ c d : K,
      rootElt K a k c * rootElt K a l d = rootElt K a l d * rootElt K a k c := by
    intro k hk l hl c d
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
    rcases hl with rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc (rootElt_comm_1_11 hK c d)
    · exact hc (rootElt_comm_4_11 hK c d)
    · exact (hc (rootElt_comm_11_5 hK d c)).symm
    · exact hc (rootElt_comm_6_11 hK c d)
    · exact (hc (rootElt_comm_11_7 hK d c)).symm
    · exact (hc (rootElt_comm_11_9 hK d c)).symm
    · exact (hc (rootElt_comm_11_10 hK d c)).symm
    · exact hc (rootElt_comm_1_12 hK c d)
    · exact hc (rootElt_comm_4_12 hK c d)
    · exact hc (rootElt_comm_5_12 hK c d)
    · exact hc (rootElt_comm_6_12 hK c d)
    · exact (hc (rootElt_comm_12_7 hK d c)).symm
    · exact (hc (rootElt_comm_12_9 hK d c)).symm
    · exact (hc (rootElt_comm_12_10 hK d c)).symm
  have h1 : S1 K a ≤ centralizer (⋃ k ∈ ({.i1, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx),
      Set.range (rootElt K a k)) := by
    refine iSup₂_le fun l hl => ?_
    rw [rootV, closure_le]
    rintro _ ⟨d, rfl⟩
    refine mem_centralizer_iff.2 fun g hg => ?_
    simp only [Set.mem_iUnion, Set.mem_range] at hg
    obtain ⟨k, hk, c, rfl⟩ := hg
    exact key k hk l hl c d
  have e : radS K a = closure (⋃ k ∈ ({.i1, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx),
      Set.range (rootElt K a k)) := by
    rw [radS, rootJoin, Subgroup.closure_iUnion]
    refine iSup_congr fun k => ?_
    rw [Subgroup.closure_iUnion]
    rfl
  intro x hx
  rw [e, mem_centralizer_iff]
  intro g hg
  have hS : closure (⋃ k ∈ ({.i1, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx),
      Set.range (rootElt K a k)) ≤ centralizer ({x} : Set (ModGL F4.tag K)) := by
    rw [closure_le]
    intro y hy
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (h1 hx) y hy)
  exact mem_centralizer_singleton_iff.1 (hS hg)

theorem reeGamma_inf_centralizer_radS_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ centralizer (radS K a : Set (ModGL F4.tag K)) ≤ S1 K a := by
  intro g hg
  obtain ⟨hgΓ, hgc⟩ := mem_inf.1 hg
  obtain ⟨-, -, -, hS4R, -, hS2R1⟩ := S1_le_S2_le_S3_le_S4_le_radS (K := K) (a := a) hK
  have hfS : sylowL a K 1 ∈ radS K a := rootV_le_rootJoin (i := .i10) (by decide)
    (rootElt_mem_rootV .i10 1)
  have hgf : g ∈ F4.reeGamma K a ⊓ centralizer {sylowL a K 1} :=
    mem_inf.2 ⟨hgΓ, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgc _ hfS).symm⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hself, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  have hgS4 : g ∈ S4 K a := by
    rw [S4_eq_tKernel hK]
    have hmem : (⟨g, hgf⟩ : ↥(F4.reeGamma K a ⊓ centralizer {sylowL a K 1})) ∈
        centralizer ((tKernel K a).subgroupOf
          (F4.reeGamma K a ⊓ centralizer {sylowL a K 1}) : Set _) := by
      refine mem_centralizer_iff.2 fun y hy => Subtype.ext ?_
      have hy' : (y : ModGL F4.tag K) ∈ radS K a := by
        have hy2 : (y : ModGL F4.tag K) ∈ tKernel K a := hy
        rw [← S4_eq_tKernel hK] at hy2
        exact hS4R hy2
      exact mem_centralizer_iff.1 hgc _ hy'
    exact hself hmem
  have hgS2 : g ∈ S2 K a := mem_S2_of_commute_S4 hK hgS4 fun w hw =>
    mem_centralizer_iff.1 hgc w (hS4R hw)
  have hgR1 := hS2R1 hgS2
  have h8 : r1Coord a g .i8 = 0 := r1Coord_eq_zero_of_mem_rootJoin hK (by decide) hgS2 rfl
    (by decide)
  have h9 : r1Coord a g .i9 = 0 := r1Coord_eq_zero_of_mem_rootJoin hK (by decide) hgS2 rfl
    (by decide)
  set u := r1Coord a g with hu
  have hg : g = rootElt K a .i10 (u .i10) * (rootElt K a .i11 (u .i11) *
      rootElt K a .i12 (u .i12)) := by
    conv_lhs => rw [← r1Elt_r1Coord hK hgR1]
    rw [← hu, rootElt_eq_r1Elt (k := .i10) rfl, rootElt_eq_r1Elt (k := .i11) rfl,
      rootElt_eq_r1Elt (k := .i12) rfl, ← r1Elt_add hK, ← r1Elt_add hK, r1Elt_eq_iff hK]
    intro j hj
    cases j <;> simp_all [Idx.isR1]
  have hw : rootElt K a .i1 1 * (rootElt K a .i11 (u .i11) * rootElt K a .i12 (u .i12)) =
      (rootElt K a .i11 (u .i11) * rootElt K a .i12 (u .i12)) * rootElt K a .i1 1 := by
    have e1 := commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_1_11 hK 1 (u .i11))
    have e2 := commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_1_12 hK 1 (u .i12))
    rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]
  have h1Γ : rootElt K a .i1 1 ∈ radS K a := rootV_le_rootJoin (i := .i1) (by decide)
    (rootElt_mem_rootV .i1 1)
  have hcomm := (mem_centralizer_iff.1 hgc _ h1Γ)
  have e3 : rootElt K a .i1 1 * rootElt K a .i10 (u .i10) =
      rootElt K a .i11 (u .i10) * rootElt K a .i10 (u .i10) * rootElt K a .i1 1 := by
    rw [← rootElt_one_comm_ten hK]
    simp only [commutatorElement_def]
    group
  have h10 : rootElt K a .i11 (u .i10) = 1 := by
    rw [hg] at hcomm
    have e4 : rootElt K a .i1 1 * (rootElt K a .i10 (u .i10) * (rootElt K a .i11 (u .i11) *
        rootElt K a .i12 (u .i12))) = rootElt K a .i11 (u .i10) * (rootElt K a .i10 (u .i10) *
        (rootElt K a .i11 (u .i11) * rootElt K a .i12 (u .i12))) * rootElt K a .i1 1 := by
      rw [← mul_assoc, e3, mul_assoc, mul_assoc, hw]
      simp only [mul_assoc]
    rw [e4] at hcomm
    have := mul_right_cancel hcomm
    exact mul_eq_right.1 this
  have hu10 : u .i10 = 0 := rootElt_injective hK .i11 (h10.trans (rootElt_zero .i11).symm)
  rw [hg, hu10, rootElt_zero, one_mul]
  exact mul_mem (rootV_le_rootJoin (i := .i11) (by decide) (rootElt_mem_rootV _ _))
    (rootV_le_rootJoin (i := .i12) (by decide) (rootElt_mem_rootV _ _))

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem S_le_L : h.S ≤ h.L := h.pull_le_L _

theorem S₁_le_S : h.S₁ ≤ h.S := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h.S₁_le_S₂_le_S₃_le_S₄_le_S
  exact h1.trans (h2.trans (h3.trans h4))

theorem S_le_P : h.S ≤ h.P := h.R_le_P_and_S_le_P.2

theorem V_le_S {k : Idx} (hk : k ∈ ({.i1, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx)) :
    h.V k ≤ h.S := h.pull_mono (rootV_le_rootJoin hk)

theorem V11_le_S₁ : h.V .i11 ≤ h.S₁ := h.pull_mono (rootV_le_rootJoin (by decide))

theorem S₁_le_R₁ : h.S₁ ≤ h.R₁ := h.pull_mono (rootJoin_mono (by decide))

theorem S₁_le_centralizer_S : h.S₁ ≤ centralizer (h.S : Set G) := by
  have e := h.pull_mono (S1_le_centralizer_radS h.card_K)
  rw [h.pull_centralizer_subgroup (radS_le_reeGamma h.card_K)] at e
  exact e.trans inf_le_right

theorem C_inf_centralizer_S_le : h.C ⊓ centralizer (h.S : Set G) ≤ h.S₁ ⊔ zpowers h.t := by
  intro x hx
  obtain ⟨hxC, hxS⟩ := mem_inf.1 hx
  have hxV : x ∈ h.CE := mem_inf.2 ⟨hxC, centralizer_le (SetLike.coe_subset_coe.2
    ((h.V_center_le .i5).trans (h.V_le_S (by decide)))) hxS⟩
  obtain ⟨r, hr, m, hm, hxe | hxe⟩ := h.exists_of_mem_CE hxV
  all_goals
    have hlL : r * m ∈ h.L := mul_mem (h.R_le_L hr) (h.N_le_L _ hm)
    have htS : h.t ∈ centralizer (h.S : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.2 h.S_le_L) h.htL
    have hlS : r * m ∈ centralizer (h.S : Set G) := by
      first
        | rw [← hxe]; exact hxS
        | (have := mul_mem hxS (inv_mem htS); rwa [hxe, mul_inv_cancel_right] at this)
    have hl : r * m ∈ h.S₁ := by
      have hmem : r * m ∈ h.L ⊓ centralizer (h.pull (radS h.K h.a) : Set G) :=
        mem_inf.2 ⟨hlL, hlS⟩
      rw [← h.pull_centralizer_subgroup (radS_le_reeGamma h.card_K)] at hmem
      obtain ⟨g, hg, hgΓ, hge⟩ := h.mem_pull_iff_elt.1 hmem
      rw [← hge]
      exact (h.elt_mem_pull hgΓ).2
        (reeGamma_inf_centralizer_radS_le h.one_le_a h.card_K (mem_inf.2 ⟨hgΓ, hg⟩))
  · rw [hxe]
    exact mem_sup_left hl
  · rw [hxe]
    exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers _))

theorem S_inf_centralizer_S : h.S ⊓ centralizer (h.S : Set G) = h.S₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.S₁_le_S h.S₁_le_centralizer_S)
  have hxt := h.C_inf_centralizer_S_le (mem_inf.2 ⟨h.L_le_C (h.S_le_L hx.1), hx.2⟩)
  obtain ⟨m, hm, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.pull_le_L _) hxt
  · exact hm
  · exfalso
    apply h.t_not_mem_L
    have := mul_mem (inv_mem (h.pull_le_L _ hm)) (h.S_le_L hx.1)
    rwa [inv_mul_cancel_left] at this

theorem Kp_le_normalizer_S₁ : h.Kp ≤ normalizer (h.S₁ : Set G) := fun k hk => by
  rw [← h.S_inf_centralizer_S]
  exact mem_normalizer_inf (mem_inf.1 hk).2 (mem_normalizer_centralizer (mem_inf.1 hk).2)

theorem s_mem_L : h.s ∈ h.L := h.emb_mem _

theorem elt_weylS : h.elt (weylS h.K) = h.s := h.elt_of_mem weylS_mem_reeGamma

theorem s_inv : h.s⁻¹ = h.s := inv_eq_of_mul_eq_one_right h.r_mul_self_s_mul_self.2

theorem s_mem_Kp : h.s ∈ h.Kp := by
  refine mem_inf.2 ⟨h.L_le_C h.s_mem_L, ?_⟩
  rw [← h.elt_weylS]
  have hle := h.pull_le_normalizer (M := normalizer (radS h.K h.a : Set (ModGL F4.tag h.K)))
    (M' := radS h.K h.a) le_rfl
  exact hle ((h.elt_mem_pull weylS_mem_reeGamma).2 (weylS_mem_normalizer_radS h.card_K))

theorem H_le_Kp : h.H ≤ h.Kp := fun _ hb => mem_inf.2 ⟨h.L_le_C (h.H_le_L hb),
  h.pull_le_normalizer (torusH_le_normalizer_radS h.card_K) hb⟩

theorem conj_s_mem_V {i : Idx} (hi : i ≠ .i3) {v : G} (hv : v ∈ h.V i) :
    h.s * v * h.s⁻¹ ∈ h.V i.sPerm := by
  have e := h.pull_map_conj (rootV h.K h.a i) (weylS_mem_reeGamma (K := h.K) (a := h.a))
  rw [map_conj_weylS_rootV hi, h.elt_weylS] at e
  change h.s * v * h.s⁻¹ ∈ h.pull (rootV h.K h.a i.sPerm)
  rw [e]
  exact ⟨v, hv, rfl⟩

theorem s_mem_normalizer_H : h.s ∈ normalizer (h.H : Set G) := by
  rw [← h.elt_weylS]
  have := h.pull_le_normalizer (M := normalizer (torusH h.K h.a : Set (ModGL F4.tag h.K)))
    (M' := torusH h.K h.a) le_rfl
  exact this ((h.elt_mem_pull weylS_mem_reeGamma).2 (weylS_mem_normalizer_torusH h.card_K))

theorem mul_mem_iff_of_le_L {M : Subgroup G} (hM : M ≤ h.L) {x y : G}
    (hx : x ∈ M ⊔ zpowers h.t) (hy : y ∈ M ⊔ zpowers h.t) :
    x * y ∈ M ↔ (x ∈ M ↔ y ∈ M) := by
  have hnot : ∀ {m : G}, m ∈ M → m * h.t ∉ M := fun {m} hm hmt => h.t_not_mem_L (hM (by
    have := mul_mem (inv_mem hm) hmt
    rwa [inv_mul_cancel_left] at this))
  obtain ⟨a, ha, hxa⟩ := h.exists_mul_of_mem_sup_zpowers_t hM hx
  obtain ⟨b, hb, hyb⟩ := h.exists_mul_of_mem_sup_zpowers_t hM hy
  rcases hxa with rfl | rfl
  · rcases hyb with rfl | rfl
    · simp [mul_mem ha hb, ha, hb]
    · have hab : x * (b * h.t) ∉ M := by
        rw [← mul_assoc]
        exact hnot (mul_mem ha hb)
      simp [hab, ha, hnot hb]
  · rcases hyb with rfl | rfl
    · have hab : a * h.t * y ∉ M := by
        rw [mul_assoc, ← h.mul_t_comm (hM hb), ← mul_assoc]
        exact hnot (mul_mem ha hb)
      simp [hab, hb, hnot ha]
    · have e : a * h.t * (b * h.t) = a * b := by
        rw [mul_assoc a, ← mul_assoc h.t b, ← h.mul_t_comm (hM hb), mul_assoc b, h.t_mul_t,
          mul_one]
      rw [e]
      simp [mul_mem ha hb, hnot ha, hnot hb]

theorem exists_ne_zero_add_one_ne_zero : ∃ μ : h.K, μ ≠ 0 ∧ μ + 1 ≠ 0 := by
  obtain ⟨μ, hμ⟩ := exists_largeReeSigma_ne h.one_le_a h.card_K
  refine ⟨μ, fun h0 => hμ (by rw [h0, largeReeSigma_zero]), fun h1 => hμ ?_⟩
  rw [show μ = 1 by linear_combination h1 - CharTwo.add_self_eq_zero (1 : h.K),
    largeReeSigma_one]

theorem r1c_eq_zero_of_brace_ne' {i j : Idx} (hi : i.isCenter = false) {Ψ : h.K → G}
    (hadd : ∀ c d : h.K, ∀ k : Idx, k.isR1 = true →
      h.r1c (Ψ (c + d)) k = h.r1c (Ψ c) k + h.r1c (Ψ d) k)
    (hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a i → ∀ c : h.K,
      ∀ k : Idx, k.isR1 = true →
        h.r1c (Ψ ((rootChar h.K h.a j t : h.K) * c)) k =
          (rootChar h.K h.a k t : h.K) * h.r1c (Ψ c) k)
    {k : Idx} (hk : k.isR1 = true) (hb : Idx.brace i j ≠ Idx.brace i k) (c : h.K) :
    h.r1c (Ψ c) k = 0 := by
  classical
  let φ : h.K → Idx → h.K := fun c l => if l.isR1 = true then h.r1c (Ψ c) l else 0
  have hφ := miyamoto_2_1_pi (ρ := id) (φ := φ) h.one_le_a h.card_K hi
    (fun x y => funext fun l => by
      simp only [φ, Pi.add_apply]
      split_ifs with hl
      · exact hadd x y l hl
      · rw [add_zero])
    (fun t ht x l => by
      simp only [φ, id]
      split_ifs with hl
      · exact hequiv t ht x l hl
      · rw [mul_zero])
    (l := k) hb c
  simpa [φ, hk] using hφ

theorem exists_mul_of_mem_S₁ {x : G} (hx : x ∈ h.S₁) :
    ∃ v ∈ h.V .i11, ∃ w ∈ h.V .i12, x = v * w := by
  have hxR := h.S₁_le_R₁ hx
  have hS : ∀ l ∈ ({.i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have hx' : x ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := hx
  have h0 : ∀ k : Idx, k.isR1 = true → k ∉ ({.i11, .i12} : Finset Idx) → h.r1c x k = 0 :=
    fun k hk hkS => h.r1c_eq_zero_of_mem hS hx' hk hkS
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have e : r1Elt h.K h.a (h.r1c x) =
      rootElt h.K h.a .i11 (h.r1c x .i11) * rootElt h.K h.a .i12 (h.r1c x .i12) := by
    rw [rootElt_eq_r1Elt (k := .i11) rfl, rootElt_eq_r1Elt (k := .i12) rfl,
      ← r1Elt_add h.card_K, r1Elt_eq_iff h.card_K]
    intro j hj
    cases j <;> simp only [Idx.isR1, Bool.false_eq_true] at hj
    · rw [h0 .i8 rfl (by decide)]; simp
    · rw [h0 .i9 rfl (by decide)]; simp
    · rw [h0 .i10 rfl (by decide)]; simp
    · simp
    · simp
  refine ⟨h.elt (rootElt h.K h.a .i11 (h.r1c x .i11)), h.elt_rootElt_mem_V _ _,
    h.elt (rootElt h.K h.a .i12 (h.r1c x .i12)), h.elt_rootElt_mem_V _ _, ?_⟩
  calc x = h.elt (r1Elt h.K h.a (h.r1c x)) := (h.elt_r1Elt_r1c hxR).symm
    _ = h.elt (rootElt h.K h.a .i11 (h.r1c x .i11) * rootElt h.K h.a .i12 (h.r1c x .i12)) := by
        rw [e]
    _ = _ := h.elt_mul' (hΓ _ _) (hΓ _ _)

theorem eq_one_of_mem_V11_of_mem_V12 {v : G} (h11 : v ∈ h.V .i11) (h12 : v ∈ h.V .i12) :
    v = 1 := by
  have hvR := h.V12_le_R₁ h12
  refine h.eq_of_r1c_eq hvR (one_mem _) fun k hk => ?_
  rw [h.r1c_one hk]
  by_cases hk12 : k = .i12
  · subst hk12
    have hS : ∀ l ∈ ({.i11} : Finset Idx), l.isR1 = true := by decide
    have e : rootJoin h.K h.a {.i11} = rootV h.K h.a .i11 := by rw [rootJoin]; simp
    have hv : v ∈ h.pull (rootJoin h.K h.a {.i11}) := by rw [e]; exact h11
    have hn : Idx.i12 ∉ ({.i11} : Finset Idx) := by decide
    exact h.r1c_eq_zero_of_mem hS hv hk hn
  · exact h.r1c_eq_zero_of_mem_V12 h12 hk hk12

@[expose] def MS : Subgroup G where
  carrier := {x | x ∈ centralizer (h.S : Set G) ∧ ⁅x, h.t⁆ ∈ h.S₁}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [commutatorElement_mul_left_eq]
    have hc : x * ⁅y, h.t⁆ * x⁻¹ = ⁅y, h.t⁆ := by
      rw [← mem_centralizer_iff.1 hx.1 _ (h.S₁_le_S hy.2), mul_inv_cancel_right]
    rw [hc]
    exact mul_mem hy.2 hx.2⟩
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    have e : ⁅x⁻¹, h.t⁆ = x⁻¹ * ⁅x, h.t⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, inv_inv, mul_assoc, mem_centralizer_iff.1 hx.1 _ (inv_mem (h.S₁_le_S hx.2)),
      inv_mul_cancel_left]
    exact inv_mem hx.2⟩

theorem comm_t_mul {x y : G} (hx : x ∈ h.MS) (hy : y ∈ h.MS) :
    ⁅x * y, h.t⁆ = ⁅x, h.t⁆ * ⁅y, h.t⁆ := by
  rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hx.1 _ (h.S₁_le_S hy.2),
    mul_inv_cancel_right, h.R₁_comm (h.S₁_le_R₁ hy.2) (h.S₁_le_R₁ hx.2)]

theorem comm_t_inv {x : G} (hx : x ∈ h.MS) : ⁅x⁻¹, h.t⁆ = ⁅x, h.t⁆⁻¹ := by
  have e := h.comm_t_mul hx (inv_mem hx)
  rw [mul_inv_cancel, commutatorElement_one_left] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem conj_Kp_mem_MS {k : G} (hk : k ∈ h.Kp) {x : G} (hx : x ∈ h.MS) : k * x * k⁻¹ ∈ h.MS := by
  obtain ⟨hkC, hkS⟩ := mem_inf.1 hk
  refine ⟨(mem_normalizer_iff.1 (mem_normalizer_centralizer hkS) x).1 hx.1, ?_⟩
  have hkt : k * h.t * k⁻¹ = h.t := by
    rw [mem_centralizer_singleton_iff.1 hkC, mul_inv_cancel_right]
  have e : ⁅k * x * k⁻¹, h.t⁆ = k * ⁅x, h.t⁆ * k⁻¹ := by
    calc ⁅k * x * k⁻¹, h.t⁆ = ⁅k * x * k⁻¹, k * h.t * k⁻¹⁆ := by rw [hkt]
      _ = k * ⁅x, h.t⁆ * k⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact (mem_normalizer_iff.1 (h.Kp_le_normalizer_S₁ hk) _).1 hx.2

theorem mem_S₁_sup_of_mem_MS {x : G} (hx : x ∈ h.MS) (hxt : ⁅x, h.t⁆ = 1) :
    x ∈ h.S₁ ⊔ zpowers h.t :=
  h.C_inf_centralizer_S_le (mem_inf.2 ⟨mem_centralizer_singleton_iff.2
    (commutatorElement_eq_one_iff_mul_comm.1 hxt), hx.1⟩)

theorem s_conj_eq (x : G) : h.s * x * h.s⁻¹ = h.s⁻¹ * x * h.s := by rw [h.s_inv]

theorem s_comm_t : h.s * h.t = h.t * h.s := h.mul_t_comm h.s_mem_L

theorem s_conj_t : h.s⁻¹ * h.t * h.s = h.t := by
  rw [mul_assoc, ← h.s_comm_t, ← mul_assoc, inv_mul_cancel, one_mul]

theorem s_conj_t' : h.s * h.t * h.s⁻¹ = h.t := by rw [h.s_comm_t, mul_inv_cancel_right]

theorem conj_s_V12 {v : G} (hv : v ∈ h.V .i12) : h.s * v * h.s⁻¹ ∈ h.V .i11 :=
  h.conj_s_mem_V (i := .i12) (by decide) hv

theorem conj_s_V11 {v : G} (hv : v ∈ h.V .i11) : h.s * v * h.s⁻¹ ∈ h.V .i12 :=
  h.conj_s_mem_V (i := .i11) (by decide) hv

theorem comm_mem_S₁_sup {x y : G} (hx : x ∈ h.MS) (hy : y ∈ h.MS) :
    ⁅x, y⁆ ∈ h.S₁ ⊔ zpowers h.t := by
  have hxy : ⁅x, y⁆ ∈ h.MS := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  refine h.mem_S₁_sup_of_mem_MS hxy ?_
  rw [commutatorElement_def x y, h.comm_t_mul (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    h.comm_t_mul (mul_mem hx hy) (inv_mem hx), h.comm_t_mul hx hy, h.comm_t_inv hx,
    h.comm_t_inv hy, h.R₁_comm (h.S₁_le_R₁ hx.2) (h.S₁_le_R₁ hy.2)]
  group

theorem S₁_comm_sup {v w : G} (hv : v ∈ h.S₁) (hw : w ∈ h.S₁ ⊔ zpowers h.t) : v * w = w * v := by
  obtain ⟨m, hm, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.pull_le_L _) hw
  · exact h.R₁_comm (h.S₁_le_R₁ hv) (h.S₁_le_R₁ hm)
  · rw [← mul_assoc, h.R₁_comm (h.S₁_le_R₁ hv) (h.S₁_le_R₁ hm), mul_assoc,
      h.mul_t_comm (h.pull_le_L _ hv), mul_assoc]

theorem comm_S₁_mul_right {x : G} (hx : x ∈ h.MS) {v y : G} (hv : v ∈ h.S₁) (hy : y ∈ h.MS) :
    ⁅x, v * y⁆ = ⁅x, y⁆ := by
  have h1 : ⁅x, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 hx.1 v (h.S₁_le_S hv)).symm
  rw [commutatorElement_mul_right_eq, h1, one_mul, h.S₁_comm_sup hv (h.comm_mem_S₁_sup hx hy),
    mul_inv_cancel_right]

theorem comm_S₁_mul_left {v x y : G} (hv : v ∈ h.S₁) (hx : x ∈ h.MS) (hy : y ∈ h.MS) :
    ⁅v * x, y⁆ = ⁅x, y⁆ := by
  have h1 : ⁅v, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 hy.1 v (h.S₁_le_S hv))
  rw [commutatorElement_mul_left_eq, h1, mul_one, h.S₁_comm_sup hv (h.comm_mem_S₁_sup hx hy),
    mul_inv_cancel_right]

theorem conj_MS_sup {y : G} (hy : y ∈ h.MS) {w : G} (hw : w ∈ h.S₁ ⊔ zpowers h.t) :
    ⁅y, w⁆ ∈ h.S₁ := by
  obtain ⟨m, hm, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.pull_le_L _) hw
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hy.1 w (h.S₁_le_S hm)).symm]
    exact one_mem _
  · rw [commutatorElement_mul_right_eq,
      commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hy.1 m (h.S₁_le_S hm)).symm,
      one_mul, h.R₁_comm (h.S₁_le_R₁ hm) (h.S₁_le_R₁ hy.2), mul_inv_cancel_right]
    exact hy.2

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

@[expose] def W11 : Subgroup G := d.W12.map (MulAut.conj h.s).toMonoidHom

theorem mem_W11_iff {y : G} : y ∈ d.W11 ↔ h.s * y * h.s⁻¹ ∈ d.W12 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv]
    rw [show h.s * (h.s * z * h.s) * h.s = (h.s * h.s) * z * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]
    exact hz
  · intro hy
    refine ⟨h.s * y * h.s⁻¹, hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv,
      show h.s * (h.s * y * h.s) * h.s = (h.s * h.s) * y * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]

theorem conj_s_mem_W11 {z : G} (hz : z ∈ d.W12) : h.s * z * h.s⁻¹ ∈ d.W11 := ⟨z, hz, rfl⟩

theorem W12_le_centralizer_S : d.W12 ≤ centralizer (h.S : Set G) := fun _ hz =>
  centralizer_le (SetLike.coe_subset_coe.2 h.S_le_P) (d.W12_le_centralizer_P hz)

theorem W11_le_centralizer_S : d.W11 ≤ centralizer (h.S : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  have hsS := (mem_inf.1 h.s_mem_Kp).2
  have := (mem_normalizer_iff.1 (mem_normalizer_centralizer hsS) z).1
    (d.W12_le_centralizer_S hz)
  exact this

theorem W11_comm {y y' : G} (hy : y ∈ d.W11) (hy' : y' ∈ d.W11) : y * y' = y' * y := by
  have h1 := d.W12_comm ((d.mem_W11_iff).1 hy) ((d.mem_W11_iff).1 hy')
  have e : ∀ u : G, u = h.s⁻¹ * (h.s * u * h.s⁻¹) * h.s := fun u => by group
  rw [e (y * y'), e (y' * y), show h.s * (y * y') * h.s⁻¹ =
    (h.s * y * h.s⁻¹) * (h.s * y' * h.s⁻¹) by group, show h.s * (y' * y) * h.s⁻¹ =
    (h.s * y' * h.s⁻¹) * (h.s * y * h.s⁻¹) by group, h1]

theorem W11_mul_self {y : G} (hy : y ∈ d.W11) : y * y = 1 := by
  have h1 := d.W12_mul_self ((d.mem_W11_iff).1 hy)
  rw [show h.s * y * h.s⁻¹ * (h.s * y * h.s⁻¹) = h.s * (y * y) * h.s⁻¹ by group] at h1
  have h2 := congrArg (fun u => h.s⁻¹ * u * h.s) h1
  rwa [show h.s⁻¹ * (h.s * (y * y) * h.s⁻¹) * h.s = y * y by group,
    show h.s⁻¹ * 1 * h.s = 1 by group] at h2

theorem V11_le_W11 : h.V .i11 ≤ d.W11 := fun _ hv =>
  (d.mem_W11_iff).2 (d.V12_le_W12 (h.conj_s_V11 hv))

theorem conj_t_mem_W11 {y : G} (hy : y ∈ d.W11) : h.t⁻¹ * y * h.t ∈ d.W11 := by
  rw [d.mem_W11_iff]
  have h1 := d.conj_t_mem_W12 ((d.mem_W11_iff).1 hy)
  have ht' : h.s⁻¹ * h.t = h.t * h.s⁻¹ := by
    calc h.s⁻¹ * h.t = h.s⁻¹ * h.t * h.s * h.s⁻¹ := by group
      _ = h.t * h.s⁻¹ := by rw [h.s_conj_t]
  have e : h.s * (h.t⁻¹ * y * h.t) * h.s⁻¹ = h.t⁻¹ * (h.s * y * h.s⁻¹) * h.t := by
    calc h.s * (h.t⁻¹ * y * h.t) * h.s⁻¹ = (h.s * h.t) * y * (h.t * h.s⁻¹) := by
          rw [h.t_inv]; group
      _ = (h.t * h.s) * y * (h.s⁻¹ * h.t) := by rw [h.s_comm_t, ht']
      _ = h.t⁻¹ * (h.s * y * h.s⁻¹) * h.t := by rw [h.t_inv]; group
  rw [e]
  exact h1

theorem exists_V11_conj_t {y : G} (hy : y ∈ d.W11) : ∃ v ∈ h.V .i11, y * h.t * y⁻¹ = h.t * v := by
  have hz := (d.mem_W11_iff).1 hy
  refine ⟨h.s⁻¹ * ((h.s * y * h.s⁻¹)⁻¹ * (h.t⁻¹ * (h.s * y * h.s⁻¹) * h.t)) * h.s, ?_, ?_⟩
  · rw [← h.s_conj_eq]
    exact h.conj_s_V12 (d.kappa_mem hz)
  · have e := d.conj_t_eq hz
    have hst := h.s_comm_t
    have hts : h.s⁻¹ * h.t * h.s = h.t := by
      rw [h.s_inv, mul_assoc, ← hst, ← mul_assoc, h.r_mul_self_s_mul_self.2, one_mul]
    calc y * h.t * y⁻¹ = h.s⁻¹ * ((h.s * y * h.s⁻¹) * (h.s * h.t * h.s⁻¹) *
        (h.s * y * h.s⁻¹)⁻¹) * h.s := by group
      _ = h.s⁻¹ * ((h.s * y * h.s⁻¹) * h.t * (h.s * y * h.s⁻¹)⁻¹) * h.s := by
          rw [show h.s * h.t * h.s⁻¹ = h.t by rw [hst, mul_inv_cancel_right]]
      _ = h.s⁻¹ * (h.t * ((h.s * y * h.s⁻¹)⁻¹ * (h.t⁻¹ * (h.s * y * h.s⁻¹) * h.t))) * h.s := by
          rw [e]
      _ = (h.s⁻¹ * h.t * h.s) * (h.s⁻¹ * ((h.s * y * h.s⁻¹)⁻¹ *
          (h.t⁻¹ * (h.s * y * h.s⁻¹) * h.t)) * h.s) := by group
      _ = _ := by rw [hts]

theorem comm_t_W11_mem {y : G} (hy : y ∈ d.W11) : ⁅y, h.t⁆ ∈ h.V .i11 := by
  obtain ⟨v, hv, hyt⟩ := d.exists_V11_conj_t hy
  rw [commutatorElement_def, hyt, ← h.mul_t_comm (h.pull_le_L _ hv), mul_inv_cancel_right]
  exact hv

theorem comm_t_W12_mem {z : G} (hz : z ∈ d.W12) : ⁅z, h.t⁆ ∈ h.V .i12 := by
  rw [commutatorElement_def, d.conj_t_eq hz, ← h.mul_t_comm (h.V12_le_L (d.kappa_mem hz)),
    mul_inv_cancel_right]
  exact d.kappa_mem hz

theorem exists_W11_comm_t {v : G} (hv : v ∈ h.V .i11) : ∃ y ∈ d.W11, ⁅y, h.t⁆ = v := by
  obtain ⟨z, hz, hzt⟩ := d.exists_W12_conj (h.conj_s_V11 hv)
  refine ⟨h.s⁻¹ * z * h.s, by rw [← h.s_conj_eq]; exact d.conj_s_mem_W11 hz, ?_⟩
  have hst := h.s_comm_t
  have hts : h.s⁻¹ * h.t * h.s = h.t := by
    rw [h.s_inv, mul_assoc, ← hst, ← mul_assoc, h.r_mul_self_s_mul_self.2, one_mul]
  have hzt' : ⁅z, h.t⁆ = h.s * v * h.s⁻¹ := by
    rw [commutatorElement_def, hzt, ← h.mul_t_comm (h.V12_le_L (h.conj_s_V11 hv)),
      mul_inv_cancel_right]
  calc ⁅h.s⁻¹ * z * h.s, h.t⁆ = h.s⁻¹ * ⁅z, h.s * h.t * h.s⁻¹⁆ * h.s := by
        simp only [commutatorElement_def]; group
    _ = h.s⁻¹ * ⁅z, h.t⁆ * h.s := by
        rw [show h.s * h.t * h.s⁻¹ = h.t by rw [hst, mul_inv_cancel_right]]
    _ = v := by rw [hzt']; group

theorem mem_V11_of_comm_t {y : G} (hy : y ∈ d.W11) (hyt : ⁅y, h.t⁆ = 1) : y ∈ h.V .i11 := by
  have hz := (d.mem_W11_iff).1 hy
  have e := commutatorElement_eq_one_iff_mul_comm.1 hyt
  have hzt : (h.s * y * h.s⁻¹) * h.t = h.t * (h.s * y * h.s⁻¹) := by
    calc h.s * y * h.s⁻¹ * h.t = h.s * y * (h.s⁻¹ * h.t * h.s) * h.s⁻¹ := by group
      _ = h.s * (y * h.t) * h.s⁻¹ := by rw [h.s_conj_t]; group
      _ = h.s * (h.t * y) * h.s⁻¹ := by rw [e]
      _ = (h.s * h.t * h.s⁻¹) * (h.s * y * h.s⁻¹) := by group
      _ = h.t * (h.s * y * h.s⁻¹) := by rw [h.s_conj_t']
  have := h.conj_s_V12 (d.mem_V12_of_commute hz hzt)
  rwa [show h.s * (h.s * y * h.s⁻¹) * h.s⁻¹ = (h.s * h.s) * y * (h.s * h.s)⁻¹ by group,
    h.r_mul_self_s_mul_self.2, inv_one, one_mul, mul_one] at this

theorem conj_H_mem_W11 {b : G} (hb : b ∈ h.H) {y : G} (hy : y ∈ d.W11) :
    b * y * b⁻¹ ∈ d.W11 := by
  rw [d.mem_W11_iff]
  have hb' : h.s * b * h.s⁻¹ ∈ h.H := (mem_normalizer_iff.1 h.s_mem_normalizer_H b).1 hb
  have := d.conj_H_mem_W12 hb' ((d.mem_W11_iff).1 hy)
  rwa [show h.s * b * h.s⁻¹ * (h.s * y * h.s⁻¹) * (h.s * b * h.s⁻¹)⁻¹ =
    h.s * (b * y * b⁻¹) * h.s⁻¹ by group] at this

theorem W11_le_MS : d.W11 ≤ h.MS := fun _ hy =>
  ⟨d.W11_le_centralizer_S hy, h.V11_le_S₁ (d.comm_t_W11_mem hy)⟩

theorem W12_le_MS : d.W12 ≤ h.MS := fun _ hz =>
  ⟨d.W12_le_centralizer_S hz, h.V12_le_S₁ (d.comm_t_W12_mem hz)⟩

theorem mul_inv_mem_V11_of_comm_eq {y y' : G} (hy : y ∈ d.W11) (hy' : y' ∈ d.W11)
    (he : ⁅y, h.t⁆ = ⁅y', h.t⁆) : y * y'⁻¹ ∈ h.V .i11 := by
  refine d.mem_V11_of_comm_t (mul_mem hy (inv_mem hy')) ?_
  rw [h.comm_t_mul (d.W11_le_MS hy) (inv_mem (d.W11_le_MS hy')),
    h.comm_t_inv (d.W11_le_MS hy'), he, mul_inv_cancel]

theorem mul_inv_mem_V12_of_comm_eq {z z' : G} (hz : z ∈ d.W12) (hz' : z' ∈ d.W12)
    (he : ⁅z, h.t⁆ = ⁅z', h.t⁆) : z * z'⁻¹ ∈ h.V .i12 := by
  refine d.mem_V12_of_commute (mul_mem hz (inv_mem hz'))
    (commutatorElement_eq_one_iff_mul_comm.1 ?_)
  rw [h.comm_t_mul (d.W12_le_MS hz) (inv_mem (d.W12_le_MS hz')),
    h.comm_t_inv (d.W12_le_MS hz'), he, mul_inv_cancel]

@[expose] def zc11 (c : h.K) : G := (d.exists_W11_comm_t (h.elt_rootElt_mem_V .i11 c)).choose

theorem zc11_mem (c : h.K) : d.zc11 c ∈ d.W11 :=
  (d.exists_W11_comm_t (h.elt_rootElt_mem_V .i11 c)).choose_spec.1

theorem zc11_comm (c : h.K) : ⁅d.zc11 c, h.t⁆ = h.elt (rootElt h.K h.a .i11 c) :=
  (d.exists_W11_comm_t (h.elt_rootElt_mem_V .i11 c)).choose_spec.2

theorem zc_comm (c : h.K) : ⁅d.zc c, h.t⁆ = h.elt (rootElt h.K h.a .i12 c) := by
  rw [commutatorElement_def, d.zc_conj, ← h.mul_t_comm (h.V12_le_L (h.elt_rootElt_mem_V _ _)),
    mul_inv_cancel_right]

theorem zc11_add (c e : h.K) : d.zc11 (c + e) * (d.zc11 c * d.zc11 e)⁻¹ ∈ h.V .i11 := by
  refine d.mul_inv_mem_V11_of_comm_eq (d.zc11_mem _) (mul_mem (d.zc11_mem c) (d.zc11_mem e)) ?_
  have hΓ : ∀ c, rootElt h.K h.a .i11 c ∈ F4.reeGamma h.K h.a := fun c =>
    rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
  rw [h.comm_t_mul (d.W11_le_MS (d.zc11_mem c)) (d.W11_le_MS (d.zc11_mem e)), d.zc11_comm,
    d.zc11_comm, d.zc11_comm, rootElt_add h.card_K rfl, h.elt_mul' (hΓ _) (hΓ _)]

theorem zc11_torus (t : h.Kˣ × h.Kˣ) (c : h.K) :
    h.elt (torusPair h.a t) * d.zc11 c * (h.elt (torusPair h.a t))⁻¹ *
      (d.zc11 ((rootChar h.K h.a .i11 t : h.K) * c))⁻¹ ∈ h.V .i11 := by
  have hb := h.elt_torusPair_mem_H t
  refine d.mul_inv_mem_V11_of_comm_eq (d.conj_H_mem_W11 hb (d.zc11_mem c)) (d.zc11_mem _) ?_
  have hbt : h.elt (torusPair h.a t) * h.t * (h.elt (torusPair h.a t))⁻¹ = h.t := by
    rw [h.mul_t_comm (h.H_le_L hb), mul_inv_cancel_right]
  rw [d.zc11_comm, ← h.elt_torusPair_conj_rootElt, ← d.zc11_comm]
  calc ⁅h.elt (torusPair h.a t) * d.zc11 c * (h.elt (torusPair h.a t))⁻¹, h.t⁆ =
      ⁅h.elt (torusPair h.a t) * d.zc11 c * (h.elt (torusPair h.a t))⁻¹,
        h.elt (torusPair h.a t) * h.t * (h.elt (torusPair h.a t))⁻¹⁆ := by rw [hbt]
    _ = _ := by simp only [commutatorElement_def]; group

theorem comm_W12_W11_mem_S₁ {x : G} (hx : x ∈ d.W12) {y : G} (hy : y ∈ d.W11) :
    ⁅x, y⁆ ∈ h.S₁ := by
  classical
  have hxM := d.W12_le_MS hx
  have hmem : ∀ {y}, y ∈ d.W11 → ⁅x, y⁆ ∈ h.S₁ ⊔ zpowers h.t := fun hy =>
    h.comm_mem_S₁_sup hxM (d.W11_le_MS hy)
  have hmul : ∀ {y y'}, y ∈ d.W11 → y' ∈ d.W11 →
      (⁅x, y * y'⁆ ∈ h.S₁ ↔ (⁅x, y⁆ ∈ h.S₁ ↔ ⁅x, y'⁆ ∈ h.S₁)) := by
    intro y y' hy hy'
    have hc := h.conj_MS_sup (d.W11_le_MS hy) (hmem hy')
    have e : y * ⁅x, y'⁆ * y⁻¹ = ⁅y, ⁅x, y'⁆⁆ * ⁅x, y'⁆ := by
      simp only [commutatorElement_def]; group
    have hy2 : y * ⁅x, y'⁆ * y⁻¹ ∈ h.S₁ ⊔ zpowers h.t := by
      rw [e]; exact mul_mem (mem_sup_left hc) (hmem hy')
    rw [commutatorElement_mul_right_eq, h.mul_mem_iff_of_le_L (M := h.S₁) (h.pull_le_L _)
      (hmem hy) hy2, e]
    have : ⁅y, ⁅x, y'⁆⁆ * ⁅x, y'⁆ ∈ h.S₁ ↔ ⁅x, y'⁆ ∈ h.S₁ :=
      ⟨fun h1 => by
        have := mul_mem (inv_mem hc) h1
        rwa [inv_mul_cancel_left] at this, fun h1 => mul_mem hc h1⟩
    rw [this]
  let f : h.K → G := fun c => if ⁅x, d.zc11 c⁆ ∈ h.S₁ then 1 else h.t
  have hf1 : ∀ c, f c = 1 → ⁅x, d.zc11 c⁆ ∈ h.S₁ := fun c hc => by
    by_contra hn
    simp only [f, ite_eq_right hn] at hc
    exact h.t_ne_one hc
  obtain ⟨μ, hμ0, hμ1⟩ := h.exists_ne_zero_add_one_ne_zero
  have key := eq_one_of_add_of_const (f := f) hμ0 hμ1
    (fun c e => by
      have hv := d.zc11_add c e
      have e1 : d.zc11 (c + e) = (d.zc11 (c + e) * (d.zc11 c * d.zc11 e)⁻¹) *
          (d.zc11 c * d.zc11 e) := by group
      have h2 : ⁅x, d.zc11 (c + e)⁆ = ⁅x, d.zc11 c * d.zc11 e⁆ := by
        rw [e1, h.comm_S₁_mul_right hxM (h.V11_le_S₁ hv)
          (d.W11_le_MS (mul_mem (d.zc11_mem c) (d.zc11_mem e)))]
      have h3 := hmul (d.zc11_mem c) (d.zc11_mem e)
      simp only [f, h2]
      by_cases h4 : ⁅x, d.zc11 c⁆ ∈ h.S₁ <;> by_cases h5 : ⁅x, d.zc11 e⁆ ∈ h.S₁ <;>
        simp [h3, h4, h5, h.t_mul_t])
    (fun c e hc he => by
      obtain ⟨t, ht, hte⟩ := exists_torusHi_rootChar_mul_eq h.card_K (i := .i5) rfl
        (j := .i11) (by decide) hc he
      have hb : h.elt (torusPair h.a t) ∈ h.Ht .i5 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hv := d.zc11_torus t c
      rw [hte] at hv
      have e1 : d.zc11 e = (h.elt (torusPair h.a t) * d.zc11 c * (h.elt (torusPair h.a t))⁻¹ *
          (d.zc11 e)⁻¹)⁻¹ * (h.elt (torusPair h.a t) * d.zc11 c *
            (h.elt (torusPair h.a t))⁻¹) := by group
      have h2 : ⁅x, d.zc11 e⁆ = h.elt (torusPair h.a t) * ⁅x, d.zc11 c⁆ *
          (h.elt (torusPair h.a t))⁻¹ := by
        rw [e1, h.comm_S₁_mul_right hxM (h.V11_le_S₁ (inv_mem hv)) (d.W11_le_MS
          (d.conj_H_mem_W11 (h.Ht_le_H .i5 hb) (d.zc11_mem c))),
          commutatorElement_conj_of_commute (d.W12_comm_H5 hx hb)]
      have h3 : (h.elt (torusPair h.a t) * ⁅x, d.zc11 c⁆ * (h.elt (torusPair h.a t))⁻¹ ∈ h.S₁ ↔
          ⁅x, d.zc11 c⁆ ∈ h.S₁) :=
        (mem_normalizer_iff.1 (h.Kp_le_normalizer_S₁ (h.H_le_Kp (h.Ht_le_H .i5 hb))) _).symm
      simp only [f, h2, h3])
  obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i11) rfl (d.comm_t_W11_mem hy)
  have hyc : y * (d.zc11 c)⁻¹ ∈ h.V .i11 :=
    d.mul_inv_mem_V11_of_comm_eq hy (d.zc11_mem c) (by rw [hc, d.zc11_comm])
  have e1 : y = (y * (d.zc11 c)⁻¹) * d.zc11 c := by group
  rw [e1, h.comm_S₁_mul_right hxM (h.V11_le_S₁ hyc) (d.W11_le_MS (d.zc11_mem c))]
  exact hf1 c (key c)

theorem comm_W12_W11 {x : G} (hx : x ∈ d.W12) {y : G} (hy : y ∈ d.W11) : ⁅x, y⁆ = 1 := by
  have hS : ∀ {x y}, x ∈ d.W12 → y ∈ d.W11 → ⁅x, y⁆ ∈ h.S₁ := fun hx hy =>
    d.comm_W12_W11_mem_S₁ hx hy
  have hR : ∀ {x y}, x ∈ d.W12 → y ∈ d.W11 → ⁅x, y⁆ ∈ h.R₁ := fun hx hy =>
    h.S₁_le_R₁ (hS hx hy)
  have bil_left : ∀ {x x' y}, x ∈ d.W12 → x' ∈ d.W12 → y ∈ d.W11 →
      ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := fun hx hx' hy => by
    rw [commutatorElement_mul_left_eq,
      ← mem_centralizer_iff.1 (d.W12_le_centralizer_S hx) _ (h.S₁_le_S (hS hx' hy)),
      mul_inv_cancel_right, h.R₁_comm (hR hx' hy) (hR hx hy)]
  have bil_right : ∀ {x y y'}, x ∈ d.W12 → y ∈ d.W11 → y' ∈ d.W11 →
      ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := fun hx hy hy' => by
    rw [commutatorElement_mul_right_eq,
      ← mem_centralizer_iff.1 (d.W11_le_centralizer_S hy) _ (h.S₁_le_S (hS hx hy')),
      mul_inv_cancel_right]
  have hxM := d.W12_le_MS hx
  have hyM := d.W11_le_MS hy
  have h11 : h.r1c ⁅x, y⁆ .i11 = 0 := by
    obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl (d.comm_t_W12_mem hx)
    have hxc : x * (d.zc c)⁻¹ ∈ h.V .i12 :=
      d.mul_inv_mem_V12_of_comm_eq hx (d.zc_mem c) (by rw [hc, d.zc_comm])
    have e1 : x = (x * (d.zc c)⁻¹) * d.zc c := by group
    rw [e1, h.comm_S₁_mul_left (h.V12_le_S₁ hxc) (d.W12_le_MS (d.zc_mem c)) hyM]
    refine h.r1c_eq_zero_of_brace_ne (i := .i6) (j := .i12) rfl (Ψ := fun c => ⁅d.zc c, y⁆)
      (fun c e k hk hk12 => ?_) (fun t ht c k hk hk12 => ?_) rfl (by decide) (by decide) c
    · show h.r1c ⁅d.zc (c + e), y⁆ k = h.r1c ⁅d.zc c, y⁆ k + h.r1c ⁅d.zc e, y⁆ k
      have e2 : d.zc (c + e) = (d.zc (c + e) * (d.zc c * d.zc e)⁻¹) * (d.zc c * d.zc e) := by
        group
      rw [e2, h.comm_S₁_mul_left (h.V12_le_S₁ (d.zc_add c e))
        (d.W12_le_MS (mul_mem (d.zc_mem c) (d.zc_mem e))) hyM,
        bil_left (d.zc_mem c) (d.zc_mem e) hy, h.r1c_mul (hR (d.zc_mem c) hy)
          (hR (d.zc_mem e) hy) hk]
    · show h.r1c ⁅d.zc ((rootChar h.K h.a .i12 t : h.K) * c), y⁆ k =
        (rootChar h.K h.a k t : h.K) * h.r1c ⁅d.zc c, y⁆ k
      set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i6 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H .i6 hb
      have hby : y * (b * y * b⁻¹)⁻¹ ∈ h.V .i11 := by
        refine d.mul_inv_mem_V11_of_comm_eq hy (d.conj_H_mem_W11 hbH hy) ?_
        have hbt : b * h.t * b⁻¹ = h.t := by rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
        have hc : b * ⁅y, h.t⁆ = ⁅y, h.t⁆ * b := mem_centralizer_iff.1
          (h.V_le_centralizer_Ht (i := .i6) rfl (h.V_center_le .i6 (d.comm_t_W11_mem hy))) b hb
        calc ⁅y, h.t⁆ = b * ⁅y, h.t⁆ * b⁻¹ := by rw [hc, mul_inv_cancel_right]
          _ = ⁅b * y * b⁻¹, b * h.t * b⁻¹⁆ := by simp only [commutatorElement_def]; group
          _ = ⁅b * y * b⁻¹, h.t⁆ := by rw [hbt]
      have e2 : y = (y * (b * y * b⁻¹)⁻¹) * (b * y * b⁻¹) := by group
      have hzc := d.zc_torus t c
      have e3 : d.zc ((rootChar h.K h.a .i12 t : h.K) * c) = (b * d.zc c * b⁻¹ *
          (d.zc ((rootChar h.K h.a .i12 t : h.K) * c))⁻¹)⁻¹ * (b * d.zc c * b⁻¹) := by group
      have hbz := d.conj_H_mem_W12 hbH (d.zc_mem c)
      have hby' := d.conj_H_mem_W11 hbH hy
      rw [e3, h.comm_S₁_mul_left (h.V12_le_S₁ (inv_mem hzc)) (d.W12_le_MS hbz) hyM]
      conv_lhs => rw [e2]
      rw [h.comm_S₁_mul_right (d.W12_le_MS hbz) (h.V11_le_S₁ hby) (d.W11_le_MS hby')]
      rw [show ⁅b * d.zc c * b⁻¹, b * y * b⁻¹⁆ = b * ⁅d.zc c, y⁆ * b⁻¹ by
        simp only [commutatorElement_def]; group, h.r1c_torus (hR (d.zc_mem c) hy) t hk]
  have h12 : h.r1c ⁅x, y⁆ .i12 = 0 := by
    obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i11) rfl (d.comm_t_W11_mem hy)
    have hyc : y * (d.zc11 c)⁻¹ ∈ h.V .i11 :=
      d.mul_inv_mem_V11_of_comm_eq hy (d.zc11_mem c) (by rw [hc, d.zc11_comm])
    have e1 : y = (y * (d.zc11 c)⁻¹) * d.zc11 c := by group
    rw [e1, h.comm_S₁_mul_right hxM (h.V11_le_S₁ hyc) (d.W11_le_MS (d.zc11_mem c))]
    refine h.r1c_eq_zero_of_brace_ne' (i := .i5) (j := .i11) rfl (Ψ := fun c => ⁅x, d.zc11 c⁆)
      (fun c e k hk => ?_) (fun t ht c k hk => ?_) rfl (by decide) c
    · show h.r1c ⁅x, d.zc11 (c + e)⁆ k = h.r1c ⁅x, d.zc11 c⁆ k + h.r1c ⁅x, d.zc11 e⁆ k
      have e2 : d.zc11 (c + e) = (d.zc11 (c + e) * (d.zc11 c * d.zc11 e)⁻¹) *
          (d.zc11 c * d.zc11 e) := by group
      rw [e2, h.comm_S₁_mul_right hxM (h.V11_le_S₁ (d.zc11_add c e))
        (d.W11_le_MS (mul_mem (d.zc11_mem c) (d.zc11_mem e))),
        bil_right hx (d.zc11_mem c) (d.zc11_mem e), h.r1c_mul (hR hx (d.zc11_mem c))
          (hR hx (d.zc11_mem e)) hk]
    · show h.r1c ⁅x, d.zc11 ((rootChar h.K h.a .i11 t : h.K) * c)⁆ k =
        (rootChar h.K h.a k t : h.K) * h.r1c ⁅x, d.zc11 c⁆ k
      set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i5 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H .i5 hb
      have hzc := d.zc11_torus t c
      have e3 : d.zc11 ((rootChar h.K h.a .i11 t : h.K) * c) = (b * d.zc11 c * b⁻¹ *
          (d.zc11 ((rootChar h.K h.a .i11 t : h.K) * c))⁻¹)⁻¹ * (b * d.zc11 c * b⁻¹) := by
        group
      rw [e3, h.comm_S₁_mul_right hxM (h.V11_le_S₁ (inv_mem hzc))
        (d.W11_le_MS (d.conj_H_mem_W11 hbH (d.zc11_mem c))),
        commutatorElement_conj_of_commute (d.W12_comm_H5 hx hb),
        h.r1c_torus (hR hx (d.zc11_mem c)) t hk]
  have hS1 := hS hx hy
  have hSl : ∀ l ∈ ({.i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have hS1' : ⁅x, y⁆ ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := hS1
  refine h.eq_of_r1c_eq (h.S₁_le_R₁ hS1) (one_mem _) fun k hk => ?_
  rw [h.r1c_one hk]
  by_cases hk11 : k = .i11
  · subst hk11; exact h11
  by_cases hk12 : k = .i12
  · subst hk12; exact h12
  exact h.r1c_eq_zero_of_mem hSl hS1' hk (by simp [hk11, hk12])

@[expose] def B1 : Subgroup G := d.W11 ⊔ d.W12

theorem W12_le_centralizer_W11 : d.W12 ≤ centralizer (d.W11 : Set G) := fun _ hx =>
  mem_centralizer_iff.2 fun _ hy => (commutatorElement_eq_one_iff_mul_comm.1
    (d.comm_W12_W11 hx hy)).symm

theorem exists_mul_of_mem_B1 {b : G} (hb : b ∈ d.B1) : ∃ y ∈ d.W11, ∃ z ∈ d.W12, b = y * z :=
  exists_mul_of_mem_sup_of_le_centralizer d.W12_le_centralizer_W11 hb

theorem W11_le_B1 : d.W11 ≤ d.B1 := le_sup_left

theorem W12_le_B1 : d.W12 ≤ d.B1 := le_sup_right

theorem B1_le_MS : d.B1 ≤ h.MS := sup_le d.W11_le_MS d.W12_le_MS

theorem B1_le_centralizer_S : d.B1 ≤ centralizer (h.S : Set G) := fun _ hb => (d.B1_le_MS hb).1

theorem B1_comm {b b' : G} (hb : b ∈ d.B1) (hb' : b' ∈ d.B1) : b * b' = b' * b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := d.exists_mul_of_mem_B1 hb
  obtain ⟨y', hy', z', hz', rfl⟩ := d.exists_mul_of_mem_B1 hb'
  have c1 := (commutatorElement_eq_one_iff_mul_comm.1 (d.comm_W12_W11 hz hy'))
  have c2 := (commutatorElement_eq_one_iff_mul_comm.1 (d.comm_W12_W11 hz' hy))
  calc y * z * (y' * z') = y * (z * y') * z' := by group
    _ = y * (y' * z) * z' := by rw [c1]
    _ = (y * y') * (z * z') := by group
    _ = (y' * y) * (z' * z) := by rw [d.W11_comm hy hy', d.W12_comm hz hz']
    _ = y' * (y * z') * z := by group
    _ = y' * (z' * y) * z := by rw [c2]
    _ = y' * z' * (y * z) := by group

theorem B1_mul_self {b : G} (hb : b ∈ d.B1) : b * b = 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := d.exists_mul_of_mem_B1 hb
  have c1 := (commutatorElement_eq_one_iff_mul_comm.1 (d.comm_W12_W11 hz hy))
  calc y * z * (y * z) = y * (z * y) * z := by group
    _ = y * (y * z) * z := by rw [c1]
    _ = (y * y) * (z * z) := by group
    _ = 1 := by rw [d.W11_mul_self hy, d.W12_mul_self hz, one_mul]

theorem S₁_le_B1 : h.S₁ ≤ d.B1 := fun v hv => by
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h.exists_mul_of_mem_S₁ hv
  exact mul_mem (d.W11_le_B1 (d.V11_le_W11 hv₁)) (d.W12_le_B1 (d.V12_le_W12 hv₂))

theorem exists_B1_comm_t {v : G} (hv : v ∈ h.S₁) : ∃ b ∈ d.B1, ⁅b, h.t⁆ = v := by
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h.exists_mul_of_mem_S₁ hv
  obtain ⟨y, hy, hyt⟩ := d.exists_W11_comm_t hv₁
  obtain ⟨z, hz, hzt⟩ := d.exists_W12_conj hv₂
  refine ⟨y * z, mul_mem (d.W11_le_B1 hy) (d.W12_le_B1 hz), ?_⟩
  rw [h.comm_t_mul (d.W11_le_MS hy) (d.W12_le_MS hz), hyt, commutatorElement_def, hzt,
    ← h.mul_t_comm (h.V12_le_L hv₂), mul_inv_cancel_right]

theorem mem_S₁_of_mem_B1 {b : G} (hb : b ∈ d.B1) (hbt : ⁅b, h.t⁆ = 1) : b ∈ h.S₁ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := d.exists_mul_of_mem_B1 hb
  rw [h.comm_t_mul (d.W11_le_MS hy) (d.W12_le_MS hz)] at hbt
  have e : ⁅y, h.t⁆ = ⁅z, h.t⁆⁻¹ := eq_inv_of_mul_eq_one_left hbt
  have h1 : ⁅y, h.t⁆ = 1 := h.eq_one_of_mem_V11_of_mem_V12 (d.comm_t_W11_mem hy)
    (e ▸ inv_mem (d.comm_t_W12_mem hz))
  have h2 : ⁅z, h.t⁆ = 1 := by rw [h1] at e; exact inv_eq_one.1 e.symm
  exact mul_mem (h.V11_le_S₁ (d.mem_V11_of_comm_t hy h1)) (h.V12_le_S₁ (d.mem_V12_of_commute hz
    (commutatorElement_eq_one_iff_mul_comm.1 h2)))

theorem t_not_mem_B1 : h.t ∉ d.B1 := fun ht => h.t_not_mem_L (h.pull_le_L _
  (d.mem_S₁_of_mem_B1 ht (commutatorElement_self _)))

theorem MS_le_B1_sup : h.MS ≤ d.B1 ⊔ zpowers h.t := fun x hx => by
  obtain ⟨b, hb, hbt⟩ := d.exists_B1_comm_t hx.2
  have hbM := d.B1_le_MS hb
  have h1 : ⁅b⁻¹ * x, h.t⁆ = 1 := by
    rw [h.comm_t_mul (inv_mem hbM) hx, h.comm_t_inv hbM, hbt, inv_mul_cancel]
  have h2 := h.mem_S₁_sup_of_mem_MS (mul_mem (inv_mem hbM) hx) h1
  have e : x = b * (b⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_left hb) (sup_le_sup_right d.S₁_le_B1 _ h2)

theorem t_mem_normalizer_B1 : h.t ∈ normalizer (d.B1 : Set G) := by
  have key : ∀ b ∈ d.B1, h.t * b * h.t⁻¹ ∈ d.B1 := fun b hb => by
    obtain ⟨y, hy, z, hz, rfl⟩ := d.exists_mul_of_mem_B1 hb
    have e : h.t * (y * z) * h.t⁻¹ = (h.t⁻¹ * y * h.t) * (h.t⁻¹ * z * h.t) := by
      rw [h.t_inv, show h.t * y * h.t * (h.t * z * h.t) = h.t * y * (h.t * h.t) * z * h.t by group,
        h.t_mul_t]
      group
    rw [e]
    exact mul_mem (d.W11_le_B1 (d.conj_t_mem_W11 hy)) (d.W12_le_B1 (d.conj_t_mem_W12 hz))
  refine mem_normalizer_iff.2 fun b => ⟨key b, fun hb => ?_⟩
  have := key _ hb
  rwa [h.t_inv, show h.t * (h.t * b * h.t) * h.t = (h.t * h.t) * b * (h.t * h.t) by group,
    h.t_mul_t, one_mul, mul_one] at this

theorem conj_Kp_mem_B1 {k : G} (hk : k ∈ h.Kp) {b : G} (hb : b ∈ d.B1) : k * b * k⁻¹ ∈ d.B1 := by
  set x := k * b * k⁻¹ with hxdef
  have hxM : x ∈ h.MS := h.conj_Kp_mem_MS hk (d.B1_le_MS hb)
  have hx2 : x * x = 1 := by
    rw [hxdef, show k * b * k⁻¹ * (k * b * k⁻¹) = k * (b * b) * k⁻¹ by group, d.B1_mul_self hb]
    group
  obtain ⟨b', hb', hxb | hxb⟩ := exists_eq_or_eq_mul_of_mem_sup h.t_mul_t d.t_mem_normalizer_B1
    (d.MS_le_B1_sup hxM)
  · rw [hxb]; exact hb'
  · exfalso
    have hb't : ⁅b', h.t⁆ = 1 := by
      have e1 : b' * h.t * (b' * h.t) = 1 := by rw [← hxb]; exact hx2
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right (d.B1_mul_self hb'), h.t_inv]
      exact e1 |> fun e => by rw [← e]; group
    have hb'S := d.mem_S₁_of_mem_B1 hb' hb't
    have hkC := (mem_inf.1 hk).1
    have hkt : k⁻¹ * h.t * k = h.t := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hkC, ← mul_assoc, inv_mul_cancel, one_mul]
    have hv : k⁻¹ * b' * k ∈ h.S₁ := by
      have := (mem_normalizer_iff.1 (inv_mem (h.Kp_le_normalizer_S₁ hk)) b').1 hb'S
      rwa [inv_inv] at this
    apply d.t_not_mem_B1
    have e : h.t = (k⁻¹ * b' * k)⁻¹ * b := by
      have e2 : b = k⁻¹ * x * k := by rw [hxdef]; group
      rw [e2, hxb, show k⁻¹ * (b' * h.t) * k = (k⁻¹ * b' * k) * (k⁻¹ * h.t * k) by group, hkt]
      group
    rw [e]
    exact mul_mem (inv_mem (d.S₁_le_B1 hv)) hb

theorem Kp_le_normalizer_B1 : h.Kp ≤ normalizer (d.B1 : Set G) := fun k hk =>
  mem_normalizer_iff.2 fun b => ⟨d.conj_Kp_mem_B1 hk, fun hb => by
    have := d.conj_Kp_mem_B1 (inv_mem hk) hb
    rwa [show k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b by group] at this⟩

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

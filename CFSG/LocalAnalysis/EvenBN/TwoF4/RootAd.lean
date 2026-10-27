module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAc

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem radR_le_of_rootV_seven (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {N : Subgroup (ModGL F4.tag K)} (hR1 : R1 K a ≤ N) (h7 : rootV K a .i7 ≤ N)
    (h1 : rootElt K a .i1 1 ∈ normalizer (N : Set (ModGL F4.tag K)))
    (hr : weylR K ∈ normalizer (N : Set (ModGL F4.tag K)))
    (hH : ∀ τ : Kˣ × Kˣ, torusPair a τ ∈ normalizer (N : Set (ModGL F4.tag K))) :
    radR K a ≤ N := by
  have hconj : ∀ {g x : ModGL F4.tag K}, g ∈ normalizer (N : Set (ModGL F4.tag K)) → x ∈ N →
      g * x * g⁻¹ ∈ N := fun hg hx => (mem_normalizer_iff.1 hg _).1 hx
  have hV : ∀ i : Idx, (∀ c, rootElt K a i c ∈ N) → rootV K a i ≤ N := fun i hi =>
    (closure_le _).2 (by rintro _ ⟨c, rfl⟩; exact hi c)
  have hrV : ∀ i : Idx, i ≠ .i1 → i ≠ .i2 → rootV K a i ≤ N → rootV K a i.rPerm ≤ N :=
    fun i hi1 hi2 hiN => hV _ fun c => by
      rw [← weylR_conj_rootElt hi1 hi2]
      exact hconj hr (hiN (rootElt_mem_rootV _ _))
  have hR1' : ∀ k : Idx, k.isR1 = true → ∀ c, rootElt K a k c ∈ N := fun k hk c =>
    hR1 (rootElt_mem_R1 hk c)
  have h3 : rootV K a .i3 ≤ N := hrV .i7 (by decide) (by decide) h7
  have hu : ∀ s : K, rootElt K a .i4 s * rootElt K a .i5 (largeReeSigma a s) ∈ N := by
    intro s
    have h3s := h3 (rootElt_mem_rootV (a := a) .i3 s)
    have hc : ⁅rootElt K a .i3 s, rootElt K a .i1 1⁆ ∈ N := by
      have e : ⁅rootElt K a .i3 s, rootElt K a .i1 1⁆ = rootElt K a .i3 s *
          (rootElt K a .i1 1 * (rootElt K a .i3 s)⁻¹ * (rootElt K a .i1 1)⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem h3s (hconj h1 (inv_mem h3s))
    simp only [rootElt_comm_3_1 hK, largeReeSigma_one, mul_one, one_mul] at hc
    set z := rootElt K a .i11 (largeReeSigma a s * s) with hz
    set Y := rootElt K a .i9 (s * largeReeSigma a s) * rootElt K a .i10 (s * largeReeSigma a s) *
      rootElt K a .i12 (s * (s * largeReeSigma a s)) with hY
    have hYN : Y ∈ N := mul_mem (mul_mem (hR1' .i9 rfl _) (hR1' .i10 rfl _)) (hR1' .i12 rfl _)
    have e57 : z⁻¹ * rootElt K a .i5 (largeReeSigma a s) * rootElt K a .i7 s =
        rootElt K a .i7 s * rootElt K a .i5 (largeReeSigma a s) := by
      have hc57 := rootElt_comm_5_7 hK (a := a) (largeReeSigma a s) s
      rw [← hz, commutatorElement_def] at hc57
      rw [← hc57]
      group
    have hz4 : z * rootElt K a .i4 s * z⁻¹ = rootElt K a .i4 s := by
      have h411 := commutatorElement_eq_one_iff_mul_comm.1
        (rootElt_comm_4_11 hK (a := a) s (largeReeSigma a s * s))
      rw [← hz] at h411
      rw [← h411, mul_inv_cancel_right]
    have e : rootElt K a .i4 s * rootElt K a .i5 (largeReeSigma a s) =
        z * (rootElt K a .i4 s * rootElt K a .i7 s * rootElt K a .i5 (largeReeSigma a s) * Y) *
          Y⁻¹ * (rootElt K a .i7 s)⁻¹ := by
      calc rootElt K a .i4 s * rootElt K a .i5 (largeReeSigma a s) =
          (z * rootElt K a .i4 s * z⁻¹) * rootElt K a .i5 (largeReeSigma a s) := by rw [hz4]
        _ = z * rootElt K a .i4 s * (z⁻¹ * rootElt K a .i5 (largeReeSigma a s) *
            rootElt K a .i7 s) * (rootElt K a .i7 s)⁻¹ := by group
        _ = z * rootElt K a .i4 s * (rootElt K a .i7 s * rootElt K a .i5 (largeReeSigma a s)) *
            (rootElt K a .i7 s)⁻¹ := by rw [e57]
        _ = _ := by group
    rw [e]
    have hX : rootElt K a .i4 s * rootElt K a .i7 s * rootElt K a .i5 (largeReeSigma a s) * Y ∈
        N := by
      rw [hY]
      simpa only [mul_assoc] using hc
    exact mul_mem (mul_mem (mul_mem (hR1' .i11 rfl _) hX) (inv_mem hYN))
      (inv_mem (h7 (rootElt_mem_rootV _ _)))
  obtain ⟨l, hl⟩ := exists_largeReeSigma_ne ha hK
  have hl0 : l ≠ 0 := fun h0 => hl (by rw [h0, largeReeSigma_zero])
  have hl1 : l - 1 ≠ 0 := fun h1 => hl (by rw [sub_eq_zero.1 h1, largeReeSigma_one])
  obtain ⟨τ, hτ5, hτ4⟩ := exists_rootChar_mul_eq hK (i := .i5) rfl (j := .i4) (by decide)
    one_ne_zero hl0
  rw [mul_one] at hτ4
  have h4 : rootV K a .i4 ≤ N := hV _ fun d => by
    set c := d * (l - 1)⁻¹ with hcdef
    have hlc : l * c = d + c := by
      rw [hcdef]
      field_simp
      ring
    have hw := hu c
    have hw' := hconj (hH τ) hw
    have e1 : torusPair a τ * (rootElt K a .i4 c * rootElt K a .i5 (largeReeSigma a c)) *
        (torusPair a τ)⁻¹ = rootElt K a .i4 (d + c) * rootElt K a .i5 (largeReeSigma a c) := by
      rw [show torusPair a τ * (rootElt K a .i4 c * rootElt K a .i5 (largeReeSigma a c)) *
          (torusPair a τ)⁻¹ = (torusPair a τ * rootElt K a .i4 c * (torusPair a τ)⁻¹) *
            (torusPair a τ * rootElt K a .i5 (largeReeSigma a c) * (torusPair a τ)⁻¹) by group,
        torusPair_conj_rootElt hK, torusPair_conj_rootElt hK, hτ4, hτ5, Units.val_one, one_mul,
        hlc]
    rw [e1] at hw'
    have hm := rootElt_mul_rootElt_of_isSz (a := a) hK (k := .i4) rfl d c
    have h48 : rootElt K a .i4 c * rootElt K a .i8 (largeReeSigma a d * c) =
        rootElt K a .i8 (largeReeSigma a d * c) * rootElt K a .i4 c :=
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_4_8 hK _ _)
    have e2 : rootElt K a .i4 d =
        (rootElt K a .i4 (d + c) * rootElt K a .i5 (largeReeSigma a c) *
          (rootElt K a .i4 c * rootElt K a .i5 (largeReeSigma a c))⁻¹) *
        (rootElt K a .i4 c * rootElt K a .i8 (largeReeSigma a d * c) *
          (rootElt K a .i4 c)⁻¹) := by
      calc rootElt K a .i4 d = rootElt K a .i4 d * rootElt K a .i4 c * (rootElt K a .i4 c)⁻¹ := by
            group
        _ = rootElt K a .i4 (d + c) * rootElt K a .i8 (largeReeSigma a d * c) *
            (rootElt K a .i4 c)⁻¹ := by
          rw [hm]
          rfl
        _ = _ := by group
    rw [e2, h48, mul_inv_cancel_right]
    exact mul_mem (mul_mem hw' (inv_mem hw)) (hR1' .i8 rfl _)
  have h5 : rootV K a .i5 ≤ N := hV _ fun e => by
    obtain ⟨s, rfl⟩ := Finite.injective_iff_surjective.1 (largeReeSigma_injective hK) e
    have := mul_mem (inv_mem (h4 (rootElt_mem_rootV (a := a) .i4 s))) (hu s)
    rwa [inv_mul_cancel_left] at this
  have h6 : rootV K a .i6 ≤ N := hrV .i4 (by decide) (by decide) h4
  refine iSup₂_le fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact (rootV_le_rootJoin (by decide)).trans hR1
  · exact (rootV_le_rootJoin (by decide)).trans hR1

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem R_le_of_V7 {N : Subgroup G} (hR1 : h.R₁ ≤ N) (h7 : h.V .i7 ≤ N)
    (h1 : h.elt (rootElt h.K h.a .i1 1) ∈ normalizer (N : Set G))
    (hr : h.r ∈ normalizer (N : Set G)) (hH : h.H ≤ normalizer (N : Set G)) : h.R ≤ N := by
  have key := radR_le_of_rootV_seven h.one_le_a h.card_K (N := h.unpull (N ⊓ h.L))
    (h.le_unpull_inf h.R1_le_reeGamma hR1)
    (h.le_unpull_inf (rootV_le_reeGamma h.card_K _) h7)
    (h.mem_normalizer_unpull_inf (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)) h1)
    (h.mem_normalizer_unpull_inf weylR_mem_reeGamma (by rw [h.elt_weylR]; exact hr))
    (fun τ => h.mem_normalizer_unpull_inf (h.torusPair_mem_reeGamma τ)
      (hH (h.elt_torusPair_mem_H τ)))
  have := h.pull_mono key
  rw [h.pull_unpull inf_le_right] at this
  exact this.trans inf_le_left

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

@[expose] def imA : Subgroup G where
  carrier := {v | ∃ x ∈ d.A, ⁅x, h.t⁆⁻¹ * v ∈ d.A1}
  mul_mem' := fun {v v'} hv hv' => by
    obtain ⟨x, hx, hα⟩ := hv
    obtain ⟨x', hx', hα'⟩ := hv'
    refine ⟨x * x', mul_mem hx hx', ?_⟩
    set u := ⁅x, h.t⁆ with hu
    set w := ⁅x', h.t⁆ with hw
    set ε := ⁅x * x', h.t⁆ * (u * w)⁻¹ with hε
    have hεA : ε ∈ d.A1 := d.comm_t_mul_mem hx hx'
    have huN : u ∈ normalizer (d.A1 : Set G) := (d.RA1_le_A hx.2.2.2.2).1
    have hwN : w⁻¹ ∈ normalizer (d.A1 : Set G) := (d.RA1_le_A (inv_mem hx'.2.2.2.2)).1
    have e : ⁅x * x', h.t⁆⁻¹ * (v * v') =
        (w⁻¹ * (u⁻¹ * ε⁻¹ * u * (u⁻¹ * v)) * w⁻¹⁻¹) * (w⁻¹ * v') := by
      rw [hε]; group
    rw [e]
    refine mul_mem ((mem_normalizer_iff.1 hwN _).1 (mul_mem ?_ hα)) hα'
    have := (mem_normalizer_iff.1 (inv_mem huN) _).1 (inv_mem hεA)
    simpa [mul_assoc] using this
  one_mem' := ⟨1, one_mem _, by rw [commutatorElement_one_left, inv_one, one_mul]; exact one_mem _⟩
  inv_mem' := fun {v} hv => by
    obtain ⟨x, hx, hα⟩ := hv
    refine ⟨x⁻¹, inv_mem hx, ?_⟩
    set u := ⁅x, h.t⁆ with hu
    have huR : u ∈ d.RA1 := hx.2.2.2.2
    have hδ : ⁅x⁻¹, u⁻¹⁆ ∈ d.A1 := d.comm_A_RA1_mem (inv_mem hx) (inv_mem huR)
    have e : ⁅x⁻¹, h.t⁆⁻¹ * v⁻¹ = u * ((⁅x⁻¹, u⁻¹⁆)⁻¹ * (u⁻¹ * v)⁻¹) * u⁻¹ := by
      rw [hu]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (d.RA1_le_A huR).1 _).1 (mul_mem (inv_mem hδ) (inv_mem hα))

theorem J_le_normalizer_imA : h.J ≤ normalizer (d.imA : Set G) := by
  have key : ∀ {j : G}, j ∈ h.J → ∀ v ∈ d.imA, j * v * j⁻¹ ∈ d.imA := by
    intro j hj v hv
    obtain ⟨x, hx, hα⟩ := hv
    have hjt : j * h.t = h.t * j := mem_centralizer_singleton_iff.1 (mem_inf.1 hj).1
    refine ⟨j * x * j⁻¹, d.conj_J_mem_A hj hx, ?_⟩
    have e : ⁅j * x * j⁻¹, h.t⁆⁻¹ * (j * v * j⁻¹) = j * (⁅x, h.t⁆⁻¹ * v) * j⁻¹ := by
      have hjt' : j * h.t * j⁻¹ = h.t := by rw [hjt, mul_inv_cancel_right]
      simp only [commutatorElement_def]
      conv_lhs => rw [← hjt']
      group
    rw [e]
    exact (mem_normalizer_iff.1 (d.J_le_normalizer_A1 hj) _).1 hα
  intro j hj
  refine mem_normalizer_of_conj_mem (key hj) fun v hv => ?_
  have := key (inv_mem hj) v hv
  rwa [inv_inv] at this

theorem R_le_imA : h.R ≤ d.imA := by
  refine h.R_le_of_V7 (fun v hv => ⟨1, one_mem _, by
      rw [commutatorElement_one_left, inv_one, one_mul]; exact d.R₁_le_A1 hv⟩)
    (fun v hv => ?_) (d.J_le_normalizer_imA (h.N1_le_J (h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1))))
    (d.J_le_normalizer_imA h.r_mem_J) fun b hb => d.J_le_normalizer_imA (h.H_le_J hb)
  obtain ⟨w, hw, hwt⟩ := d.exists_W7_comm_t hv
  exact ⟨w, d.W7_le_A hw, by rw [hwt, inv_mul_cancel]; exact one_mem _⟩

theorem exists_A_comm_t {v : G} (hv : v ∈ h.R) : ∃ x ∈ d.A, ⁅x, h.t⁆⁻¹ * v ∈ d.A1 :=
  d.R_le_imA hv

theorem isPGroup_RA1 : IsPGroup 2 d.RA1 :=
  (h.isPGroup_P.to_le h.R_le_P).to_sup_of_normal_right' (d.isPGroup_B4.to_le d.A1_le_B4)
    d.R_le_normalizer_A1

theorem comm_pow_mem_A1 {x : G} (hx : x ∈ d.A) (k : ℕ) :
    ⁅x ^ k, h.t⁆ * (⁅x, h.t⁆ ^ k)⁻¹ ∈ d.A1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ⁅x ^ (k + 1), h.t⁆ * (⁅x, h.t⁆ ^ (k + 1))⁻¹ =
        (x * (⁅x ^ k, h.t⁆ * (⁅x, h.t⁆ ^ k)⁻¹) * x⁻¹) * ⁅x, ⁅x, h.t⁆ ^ k⁆ := by
      rw [pow_succ' x k, commutatorElement_mul_left_eq, pow_succ]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hx.1 _).1 ih)
      (d.comm_A_RA1_mem hx (pow_mem hx.2.2.2.2 k))

theorem isPGroup_A : IsPGroup 2 d.A := by
  intro x
  obtain ⟨m, hm⟩ := d.isPGroup_RA1 ⟨_, (x.2 : (x : G) ∈ d.A).2.2.2.2⟩
  have hm' : ⁅(x : G), h.t⁆ ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 := d.comm_pow_mem_A1 x.2 (2 ^ m)
  rw [hm', inv_one, mul_one] at h1
  have hQ := d.mem_RA1_of_comm_mem_A1 (pow_mem x.2 _) h1
  obtain ⟨m', hm''⟩ := d.isPGroup_RA1 ⟨_, hQ⟩
  refine ⟨m + m', Subtype.ext ?_⟩
  have := congrArg Subtype.val hm''
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul, this]

theorem mem_R_of_mem_A_of_comm {x : G} (hx : x ∈ d.A) (hxt : ⁅x, h.t⁆ = 1) : x ∈ h.R := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1
    (d.mem_RA1_of_comm_mem_A1 hx (by rw [hxt]; exact one_mem _))
  have hat : ⁅a, h.t⁆ = 1 := by
    have e : ⁅r * a, h.t⁆ = r * ⁅a, h.t⁆ * r⁻¹ := by
      rw [commutatorElement_mul_left_eq,
        commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R_le_L hr)), mul_one]
    rw [e] at hxt
    simpa using mul_inv_eq_one.1 hxt
  exact mul_mem hr (h.R₁_le_R (d.mem_R₁_of_mem_A1 ha hat))

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

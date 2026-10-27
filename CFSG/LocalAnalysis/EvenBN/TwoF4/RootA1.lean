module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB1

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X] [Finite X]

theorem exists_fixed_mul_of_odd {B N : Subgroup X} (hB : Odd (Nat.card B))
    (hN2 : ∀ n ∈ N, n * n = 1) (hNc : ∀ n ∈ N, ∀ m ∈ N, n * m = m * n)
    (hBN : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N) {y : X}
    (hy : ∀ b ∈ B, y⁻¹ * (b * y * b⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ b ∈ B, b * (y * n) * b⁻¹ = y * n := by
  classical
  let : CommGroup N := { (inferInstance : Group N) with
    mul_comm := fun a b => Subtype.ext (hNc a a.2 b b.2) }
  have : Fintype B := Fintype.ofFinite B
  let c : B → N := fun b => ⟨y⁻¹ * (b * y * b⁻¹), hy b b.2⟩
  let r : N := ∏ g : B, c g
  refine ⟨r, r.2, fun b hb => ?_⟩
  let φ : N →* N :=
    { toFun := fun n => ⟨b * n * b⁻¹, hBN b hb n n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun m n => Subtype.ext (by
        show b * ((m : X) * n) * b⁻¹ = b * m * b⁻¹ * (b * n * b⁻¹)
        group) }
  have hcoc : ∀ g : B, φ (c g) = (c ⟨b, hb⟩)⁻¹ * c (⟨b, hb⟩ * g) := by
    intro g
    apply Subtype.ext
    show b * (y⁻¹ * ((g : X) * y * (g : X)⁻¹)) * b⁻¹ =
      (y⁻¹ * (b * y * b⁻¹))⁻¹ * (y⁻¹ * ((b * g) * y * (b * g)⁻¹))
    group
  have hφr : φ r = (c ⟨b, hb⟩)⁻¹ ^ Fintype.card B * r := by
    have e1 : φ r = ∏ g : B, φ (c g) := map_prod φ c Finset.univ
    rw [e1, Finset.prod_congr rfl fun g _ => hcoc g, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨b, hb⟩) (fun g => c (⟨b, hb⟩ * g)) c (fun g => rfl)
  have hcb : c ⟨b, hb⟩ * c ⟨b, hb⟩ = 1 := Subtype.ext (hN2 _ (c ⟨b, hb⟩).2)
  have hinv : (c ⟨b, hb⟩)⁻¹ = c ⟨b, hb⟩ := inv_eq_of_mul_eq_one_right hcb
  have hodd : (c ⟨b, hb⟩)⁻¹ ^ Fintype.card B = c ⟨b, hb⟩ := by
    obtain ⟨k, hk⟩ := hB
    rw [Fintype.card_eq_nat_card, hk, hinv, pow_succ, pow_mul, sq, hcb, one_pow, one_mul]
  rw [hodd] at hφr
  have hr : b * (r : X) * b⁻¹ = c ⟨b, hb⟩ * r := congrArg Subtype.val hφr
  have hyc : b * y * b⁻¹ = y * c ⟨b, hb⟩ := by
    show b * y * b⁻¹ = y * (y⁻¹ * (b * y * b⁻¹))
    group
  have hcb' : (c ⟨b, hb⟩ : X) * c ⟨b, hb⟩ = 1 := congrArg Subtype.val hcb
  calc b * (y * r) * b⁻¹ = (b * y * b⁻¹) * (b * r * b⁻¹) := by group
    _ = y * ((c ⟨b, hb⟩ : X) * c ⟨b, hb⟩) * r := by rw [hyc, hr]; group
    _ = y * r := by rw [hcb', mul_one]

theorem eq_zero_of_alternating_equivariant {K : Type*} [Field K] [Finite K] [CharP K 2]
    (β : K → K → K) (hadd1 : ∀ c c' e, β (c + c') e = β c e + β c' e)
    (hadd2 : ∀ c e e', β c (e + e') = β c e + β c e') (halt : ∀ c, β c c = 0)
    (hequiv : ∀ l : K, l ≠ 0 → ∀ c e, β (l * c) (l * e) = l * β c e) (c e : K) : β c e = 0 := by
  have h0l : ∀ e, β 0 e = 0 := fun e => by
    have := hadd1 0 0 e
    rw [add_zero] at this
    exact left_eq_add.1 this
  have h0r : ∀ c, β c 0 = 0 := fun c => by
    have := hadd2 c 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hequiv' : ∀ l c e, β (l * c) (l * e) = l * β c e := fun l c e => by
    by_cases hl : l = 0
    · rw [hl, zero_mul, zero_mul, zero_mul, h0l]
    · exact hequiv l hl c e
  have hsymm : ∀ x y, β x y = β y x := fun x y => by
    have := halt (x + y)
    rw [hadd1, hadd2, hadd2, halt, halt, zero_add, add_zero] at this
    rw [← CharTwo.add_eq_zero (R := K)]
    exact this
  have hbal : ∀ l x y, β (l * x) y = β x (l * y) := fun l x y => by
    have h1 := hequiv' (l + 1) x y
    rw [add_mul, add_mul, one_mul, one_mul, hadd1, hadd2, hadd2, hequiv', add_mul, one_mul]
      at h1
    rw [← CharTwo.add_eq_zero (R := K)]
    linear_combination h1
  have hsq : ∀ l x y, β (l * l * x) y = l * β x y := fun l x y => by
    rw [mul_assoc, hbal, hequiv']
  by_cases hc : c = 0
  · rw [hc, h0l]
  · obtain ⟨l, hl⟩ := isSquare_of_charTwo' (e / c)
    have he : e = l * l * c := by rw [← hl, div_mul_cancel₀ e hc]
    rw [he, hsymm, hsq, halt, mul_zero]

end Generic

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem V5_le_centralizer_R₁ : h.V .i5 ≤ centralizer (h.R₁ : Set G) := by
  have := (le_sup_left : h.V .i5 ≤ h.V .i5 ⊔ h.R₁)
  rw [← h.R_inf_centralizer_R₁] at this
  exact this.trans inf_le_right

theorem V5_sup_R₁_le_R : h.V .i5 ⊔ h.R₁ ≤ h.R := sup_le h.V5_le_R h.R₁_le_R

theorem V5_sup_R₁_le_S : h.V .i5 ⊔ h.R₁ ≤ h.S :=
  sup_le (h.V_le_S (by decide)) (h.pull_mono (rootJoin_le_rootJoin h.card_K (by decide)))

theorem mem_R₁_of_mem_V5_sup_R₁ {x : G} (hx : x ∈ h.V .i5 ⊔ h.R₁)
    (hxc : x ∈ centralizer (h.V .i5 : Set G)) : x ∈ h.R₁ := by
  obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (le_centralizer_iff.1 h.V5_le_centralizer_R₁) hx
  have hwc : w ∈ centralizer (h.V .i5 : Set G) := le_centralizer_iff.1 h.V5_le_centralizer_R₁ hw
  have hvc : v ∈ centralizer (h.V .i5 : Set G) := by
    have := mul_mem hxc (inv_mem hwc)
    rwa [mul_inv_cancel_right] at this
  have hvZ : v ∈ zIn (h.V .i5) := mem_inf.2 ⟨hvc, hv⟩
  rw [h.zIn_V5] at hvZ
  exact mul_mem (h.V12_le_R₁ hvZ) hw

theorem eq_one_of_mem_N1_of_comm_mem_V12 {m : G} (hm : m ∈ h.N .i1)
    (hmx : ∀ x ∈ h.R₁, ⁅m, x⁆ ∈ h.V .i12) : m = 1 := by
  classical
  have hNR₁ : ∀ n ∈ h.N .i1, ∀ x ∈ h.R₁, n * x * n⁻¹ ∈ h.R₁ := fun n hn x hx => by
    have hn' : n ∈ normalizer (h.R₁ : Set G) := by
      rw [← h.commutator_R_R]
      exact mem_normalizer_commutator_of (h.N1_le_normalizer_R hn) (h.N1_le_normalizer_R hn)
    exact (mem_normalizer_iff.1 hn' x).1 hx
  have hNV : ∀ {n v : G}, n ∈ h.N .i1 → v ∈ h.V .i12 → n * v = v * n := fun {n v} hn hv =>
    (mem_centralizer_iff.1 (h.R_sup_N1_le_centralizer_V12 (mem_sup_right hn)) v hv).symm
  let D : Subgroup (h.N .i1) :=
    { carrier := {n | ∀ x ∈ h.R₁, ⁅(n : G), x⁆ ∈ h.V .i12}
      mul_mem' := fun {n n'} hn hn' x hx => by
        have e : ⁅(n : G) * n', x⁆ = n * ⁅(n' : G), x⁆ * (n : G)⁻¹ * ⁅(n : G), x⁆ :=
          commutatorElement_mul_left_eq _ _ _
        show ⁅((n * n' : h.N .i1) : G), x⁆ ∈ h.V .i12
        rw [Subgroup.coe_mul, e, hNV n.2 (hn' x hx), mul_inv_cancel_right]
        exact mul_mem (hn' x hx) (hn x hx)
      one_mem' := fun x _ => by
        show ⁅((1 : h.N .i1) : G), x⁆ ∈ h.V .i12
        rw [Subgroup.coe_one, commutatorElement_one_left]
        exact one_mem _
      inv_mem' := fun {n} hn x hx => by
        show ⁅((n⁻¹ : h.N .i1) : G), x⁆ ∈ h.V .i12
        have hx' : (n : G)⁻¹ * x * n ∈ h.R₁ := by
          have := hNR₁ _ (inv_mem n.2) x hx
          rwa [inv_inv] at this
        have e : ⁅(n : G)⁻¹, x⁆ = ⁅(n : G), (n : G)⁻¹ * x * n⁆⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [Subgroup.coe_inv, e]
        exact inv_mem (hn _ hx') }
  have hDn : D.Normal := ⟨fun n hn g x hx => by
    show ⁅((g * n * g⁻¹ : h.N .i1) : G), x⁆ ∈ h.V .i12
    have hx' : (g : G)⁻¹ * x * g ∈ h.R₁ := by
      have := hNR₁ _ (inv_mem g.2) x hx
      rwa [inv_inv] at this
    have e : ⁅((g * n * g⁻¹ : h.N .i1) : G), x⁆ =
        (g : G) * ⁅(n : G), (g : G)⁻¹ * x * g⁆ * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [e, hNV g.2 (hn _ hx'), mul_inv_cancel_right]
    exact hn _ hx'⟩
  have h1N : h.elt (rootElt h.K h.a .i1 1) ∈ h.N .i1 := h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1)
  have h1D : (⟨_, h1N⟩ : h.N .i1) ∉ D := by
    intro hD
    have hmem := hD _ (h.elt_rootElt_mem_R₁ (k := .i8) rfl 1)
    have hΓ1 : rootElt h.K h.a .i1 1 ∈ F4.reeGamma h.K h.a :=
      rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
    have hΓ8 : rootElt h.K h.a .i8 1 ∈ F4.reeGamma h.K h.a :=
      rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
    have e : ⁅h.elt (rootElt h.K h.a .i1 1), h.elt (rootElt h.K h.a .i8 1)⁆ =
        h.elt (r1Elt h.K h.a (Pi.single .i9 1 + Pi.single .i11 1 +
          Pi.single .i12 (largeReeSigma h.a 1))) := by
      rw [← rootElt_one_comm_eight h.card_K, h.elt_commutator hΓ1 hΓ8]
    rw [e] at hmem
    have h9 := h.r1c_eq_zero_of_mem_V12 hmem (k := .i9) rfl (by decide)
    rw [h.r1c_elt_r1Elt _ rfl] at h9
    simp at h9
  have := (h.isSimpleGroup_N .i1).1
  have := hDn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with hD | hD
  · have hmD : (⟨m, hm⟩ : h.N .i1) ∈ D := hmx
    rw [hD, mem_bot] at hmD
    exact congrArg Subtype.val hmD
  · exact absurd (hD ▸ mem_top _) h1D

theorem elt_rootElt_one_ne_one (k : Idx) : h.elt (rootElt h.K h.a k 1) ≠ 1 := fun e => by
  have hΓ : rootElt h.K h.a k 1 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
  have e2 : rootElt h.K h.a k 1 = 1 := h.elt_injOn hΓ (one_mem _) (by rw [e, h.elt_one'])
  exact one_ne_zero (rootElt_injective h.card_K k (e2.trans (rootElt_zero k).symm))

theorem C_inf_centralizer_V5R₁_le :
    h.C ⊓ centralizer ((h.V .i5 ⊔ h.R₁ : Subgroup G) : Set G) ≤ h.R₁ ⊔ zpowers h.t := by
  intro x hx
  obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
  have hxV : x ∈ h.CE := mem_inf.2 ⟨hxC, centralizer_le (SetLike.coe_subset_coe.2
    (h.V12_le_R₁.trans le_sup_right)) hxc⟩
  have htc : h.t ∈ centralizer ((h.V .i5 ⊔ h.R₁ : Subgroup G) : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (h.V5_sup_R₁_le_R.trans h.R_le_L)) h.htL
  obtain ⟨r, hr, m, hm, hxe | hxe⟩ := h.exists_of_mem_CE hxV
  all_goals
    have hrm : r * m ∈ centralizer ((h.V .i5 ⊔ h.R₁ : Subgroup G) : Set G) := by
      first
        | rw [← hxe]; exact hxc
        | (have := mul_mem hxc (inv_mem htc); rwa [hxe, mul_inv_cancel_right] at this)
    have hm1 : m = 1 := by
      refine h.eq_one_of_mem_N1_of_comm_mem_V12 hm fun y hy => ?_
      have hc : r * m * y = y * (r * m) :=
        (mem_centralizer_iff.1 hrm y (mem_sup_right hy)).symm
      have hry := h.comm_mem_V12 hr hy
      have e : ⁅m, y⁆ = r⁻¹ * ⁅r, y⁆⁻¹ * r := by
        have e1 : ⁅r * m, y⁆ = 1 := by
          rw [commutatorElement_def, hc]; group
        rw [commutatorElement_mul_left_eq] at e1
        have e2 : r * ⁅m, y⁆ * r⁻¹ = ⁅r, y⁆⁻¹ := eq_inv_of_mul_eq_one_left e1
        calc ⁅m, y⁆ = r⁻¹ * (r * ⁅m, y⁆ * r⁻¹) * r := by group
          _ = r⁻¹ * ⁅r, y⁆⁻¹ * r := by rw [e2]
      rw [e, mul_assoc, (mem_centralizer_iff.1 (h.R_sup_N1_le_centralizer_V12 (mem_sup_left hr)) _
        (inv_mem hry)), inv_mul_cancel_left]
      exact inv_mem hry
    subst hm1
    rw [mul_one] at hrm hxe
    have hrR₁ : r ∈ h.R₁ := by
      have hrV : r ∈ h.V .i5 ⊔ h.R₁ := by
        rw [← h.R_inf_centralizer_R₁]
        exact mem_inf.2 ⟨hr, centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hrm⟩
      exact h.mem_R₁_of_mem_V5_sup_R₁ hrV
        (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hrm)
  · rw [hxe]
    exact mem_sup_left hrR₁
  · rw [hxe]
    exact mul_mem (mem_sup_left hrR₁) (mem_sup_right (mem_zpowers _))

theorem J_le_normalizer_R₁ : h.J ≤ normalizer (h.R₁ : Set G) := fun j hj => by
  rw [← h.commutator_R_R]
  exact mem_normalizer_commutator_of (mem_inf.1 hj).2 (mem_inf.1 hj).2

theorem H_le_J : h.H ≤ h.J := fun _ hb => mem_inf.2 ⟨h.L_le_C (h.H_le_L hb), h.H_le_normalizer_R hb⟩

theorem N1_le_J : h.N .i1 ≤ h.J := fun _ hn => mem_inf.2 ⟨h.L_le_C (h.N_le_L _ hn),
  h.N1_le_normalizer_R hn⟩

theorem odd_card_Ht (i : Idx) : Odd (Nat.card (h.Ht i)) := by
  rw [Setup.Ht, h.card_pull ((torusHi_le_torusH i).trans (torusH_le_reeGamma h.card_K)),
    card_torusHi h.card_K]
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one

theorem pull_rootJoin_singleton (k : Idx) : h.pull (rootJoin h.K h.a {k}) = h.V k := by
  have e : rootJoin h.K h.a {k} = rootV h.K h.a k := by rw [rootJoin]; simp
  rw [e]
  rfl

theorem mem_V_of_mem_R₁_of_mem_CH {i k : Idx} (hi : i.isCenter = false)
    (hbr : ∀ l : Idx, l.isR1 = true → l ≠ k → Idx.brace i l ≠ 0) {x : G} (hx : x ∈ h.R₁)
    (hxc : x ∈ h.CH i) : x ∈ h.V k := by
  have h0 : ∀ l : Idx, l.isR1 = true → l ∉ ({k} : Finset Idx) → h.r1c x l = 0 := by
    intro l hl hlk
    refine eq_zero_of_forall_rootChar_mul_eq h.one_le_a h.card_K hi
      (hbr l hl (by simpa using hlk)) fun t ht => ?_
    have hb : h.elt (torusPair h.a t) ∈ h.Ht i :=
      (h.elt_torusPair_mem_Ht_iff t).2 ((mem_torusHi_iff h.card_K i t).2 ht)
    have hbx : h.elt (torusPair h.a t) * x * (h.elt (torusPair h.a t))⁻¹ = x := by
      rw [mem_centralizer_iff.1 hxc _ hb, mul_inv_cancel_right]
    rw [← h.r1c_torus hx t hl, hbx]
  have := h.mem_of_r1c_eq_zero hx h0
  rwa [h.pull_rootJoin_singleton] at this

theorem R₁_le_of_V_le {M : Subgroup G} (h8 : h.V .i8 ≤ M) (h9 : h.V .i9 ≤ M)
    (h10 : h.V .i10 ≤ M) (h11 : h.V .i11 ≤ M) (h12 : h.V .i12 ≤ M) : h.R₁ ≤ M := fun r hr => by
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  rw [← h.elt_r1Elt_r1c hr, r1Elt,
    h.elt_mul' (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]
  exact mul_mem (mul_mem (mul_mem (mul_mem (h8 (h.elt_rootElt_mem_V _ _))
    (h11 (h.elt_rootElt_mem_V _ _))) (h12 (h.elt_rootElt_mem_V _ _)))
    (h9 (h.elt_rootElt_mem_V _ _))) (h10 (h.elt_rootElt_mem_V _ _))

theorem Ht6_eq_map_conj_s : h.Ht .i6 = (h.Ht .i5).map (MulAut.conj h.s).toMonoidHom := by
  have e : (torusHi h.K h.a .i5).map (MulAut.conj (weylS h.K)).toMonoidHom =
      torusHi h.K h.a .i6 := map_conj_weylS_torusHi h.card_K (i := .i5) (by decide)
  rw [Setup.Ht, ← e, h.pull_map_conj _ weylS_mem_reeGamma, h.elt_weylS]
  rfl

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem t_not_mem_centralizer_W12 : h.t ∉ centralizer (d.W12 : Set G) := by
  intro ht
  obtain ⟨z, hz, hzt⟩ := d.exists_W12_conj (h.elt_rootElt_mem_V .i12 1)
  have hzt' : z * h.t * z⁻¹ = h.t := by
    rw [mem_centralizer_iff.1 ht z hz, mul_inv_cancel_right]
  rw [hzt'] at hzt
  exact h.elt_rootElt_one_ne_one .i12 (by
    have := congrArg (h.t⁻¹ * ·) hzt
    simpa using this.symm)

@[expose] def A1 : Subgroup G where
  carrier := {x | x ∈ centralizer ((h.V .i5 ⊔ h.R₁ : Subgroup G) : Set G) ∧
    x ∈ centralizer (d.W12 : Set G) ∧ ⁅x, h.t⁆ ∈ h.R₁}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, by
    rw [commutatorElement_mul_left_eq]
    have hc : x * ⁅y, h.t⁆ * x⁻¹ = ⁅y, h.t⁆ := by
      rw [← mem_centralizer_iff.1 hx.1 _ (mem_sup_right hy.2.2), mul_inv_cancel_right]
    rw [hc]
    exact mul_mem hy.2.2 hx.2.2⟩
  one_mem' := ⟨one_mem _, one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, inv_mem hx.2.1, by
    have e : ⁅x⁻¹, h.t⁆ = x⁻¹ * ⁅x, h.t⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, inv_inv, mul_assoc, mem_centralizer_iff.1 hx.1 _ (mem_sup_right (inv_mem hx.2.2)),
      inv_mul_cancel_left]
    exact inv_mem hx.2.2⟩

theorem A1_le_centralizer_R₁ : d.A1 ≤ centralizer (h.R₁ : Set G) := fun _ hx =>
  centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.1

theorem A1_le_centralizer_V5 : d.A1 ≤ centralizer (h.V .i5 : Set G) := fun _ hx =>
  centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.1

theorem comm_t_mul_A1 {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1) :
    ⁅x * y, h.t⁆ = ⁅x, h.t⁆ * ⁅y, h.t⁆ := by
  rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx) _ hy.2.2,
    mul_inv_cancel_right, h.R₁_comm hy.2.2 hx.2.2]

theorem comm_t_inv_A1 {x : G} (hx : x ∈ d.A1) : ⁅x⁻¹, h.t⁆ = ⁅x, h.t⁆⁻¹ := by
  have e := d.comm_t_mul_A1 hx (inv_mem hx)
  rw [mul_inv_cancel, commutatorElement_one_left] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem R₁_le_A1 : h.R₁ ≤ d.A1 := fun x hx => ⟨mem_centralizer_iff.2 fun y hy => by
    obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (le_centralizer_iff.1 h.V5_le_centralizer_R₁) hy
    have h1 : v * x = x * v :=
      (mem_centralizer_iff.1 (h.V5_le_centralizer_R₁ hv) x hx).symm
    calc v * w * x = v * (x * w) := by rw [mul_assoc, h.R₁_comm hw hx]
      _ = x * (v * w) := by rw [← mul_assoc, h1, mul_assoc],
  fun z hz => (mem_centralizer_iff.1 (d.W12_le_centralizer_R₁ hz) x hx).symm,
  by rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R₁_le_R.trans h.R_le_L hx))]
     exact one_mem _⟩

theorem B1_le_A1 : d.B1 ≤ d.A1 := fun _ hb => ⟨centralizer_le
    (SetLike.coe_subset_coe.2 h.V5_sup_R₁_le_S) (d.B1_le_centralizer_S hb),
  mem_centralizer_iff.2 fun _ hz => d.B1_comm (d.W12_le_B1 hz) hb,
  h.S₁_le_R₁ (d.B1_le_MS hb).2⟩

theorem W12_le_A1 : d.W12 ≤ d.A1 := d.W12_le_B1.trans d.B1_le_A1

theorem W11_le_A1 : d.W11 ≤ d.A1 := d.W11_le_B1.trans d.B1_le_A1

theorem mem_R₁_of_mem_A1 {x : G} (hx : x ∈ d.A1) (hxt : ⁅x, h.t⁆ = 1) : x ∈ h.R₁ := by
  have hxC : x ∈ h.C := mem_centralizer_singleton_iff.2
    (commutatorElement_eq_one_iff_mul_comm.1 hxt)
  obtain ⟨m, hm, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.R₁_le_R.trans h.R_le_L)
    (h.C_inf_centralizer_V5R₁_le (mem_inf.2 ⟨hxC, hx.1⟩))
  · exact hm
  · exfalso
    have hmc : m ∈ centralizer (d.W12 : Set G) := (d.R₁_le_A1 hm).2.1
    apply d.t_not_mem_centralizer_W12
    have := mul_mem (inv_mem hmc) hx.2.1
    rwa [inv_mul_cancel_left] at this

theorem conj_J_mem_A1 {j : G} (hj : j ∈ h.J) {x : G} (hx : x ∈ d.A1) : j * x * j⁻¹ ∈ d.A1 := by
  obtain ⟨hjC, hjR⟩ := mem_inf.1 hj
  have hjR₁ : j ∈ normalizer (h.R₁ : Set G) := by
    rw [← h.commutator_R_R]
    exact mem_normalizer_commutator_of hjR hjR
  have hjV : j ∈ normalizer ((h.V .i5 ⊔ h.R₁ : Subgroup G) : Set G) := by
    rw [← h.R_inf_centralizer_R₁]
    exact mem_normalizer_inf hjR (mem_normalizer_centralizer hjR₁)
  have hjt : j * h.t * j⁻¹ = h.t := by
    rw [mem_centralizer_singleton_iff.1 hjC, mul_inv_cancel_right]
  refine ⟨(mem_normalizer_iff.1 (mem_normalizer_centralizer hjV) x).1 hx.1,
    (mem_normalizer_iff.1 (mem_normalizer_centralizer (d.J_le_normalizer_W12 hj)) x).1 hx.2.1, ?_⟩
  have e : ⁅j * x * j⁻¹, h.t⁆ = j * ⁅x, h.t⁆ * j⁻¹ := by
    conv_lhs => rw [← hjt]
    simp only [commutatorElement_def]; group
  rw [e]
  exact (mem_normalizer_iff.1 hjR₁ _).1 hx.2.2

theorem J_le_normalizer_A1 : h.J ≤ normalizer (d.A1 : Set G) := fun j hj =>
  mem_normalizer_iff.2 fun x => ⟨d.conj_J_mem_A1 hj, fun hx => by
    have := d.conj_J_mem_A1 (inv_mem hj) hx
    rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this⟩

@[expose] def kA1 : Subgroup G where
  carrier := {v | ∃ x ∈ d.A1, ⁅x, h.t⁆ = v}
  mul_mem' := fun {_ _} ⟨x, hx, hxv⟩ ⟨y, hy, hyv⟩ =>
    ⟨x * y, mul_mem hx hy, by rw [d.comm_t_mul_A1 hx hy, hxv, hyv]⟩
  one_mem' := ⟨1, one_mem _, commutatorElement_one_left _⟩
  inv_mem' := fun {_} ⟨x, hx, hxv⟩ => ⟨x⁻¹, inv_mem hx, by rw [d.comm_t_inv_A1 hx, hxv]⟩

theorem kA1_eq : d.kA1 = h.R₁ := by
  have hle : d.kA1 ≤ h.R₁ := fun _ ⟨x, hx, hxv⟩ => hxv ▸ hx.2.2
  have hJ : ∀ j ∈ h.J, j ∈ normalizer (d.kA1 : Set G) := by
    have key : ∀ {j}, j ∈ h.J → ∀ v ∈ d.kA1, j * v * j⁻¹ ∈ d.kA1 := by
      rintro j hj _ ⟨x, hx, rfl⟩
      have hjt : j * h.t * j⁻¹ = h.t := by
        rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hj).1, mul_inv_cancel_right]
      refine ⟨j * x * j⁻¹, d.conj_J_mem_A1 hj hx, ?_⟩
      conv_lhs => rw [← hjt]
      simp only [commutatorElement_def]; group
    intro j hj
    exact mem_normalizer_iff.2 fun v => ⟨key hj v, fun hv => by
      have := key (inv_mem hj) _ hv
      rwa [show j⁻¹ * (j * v * j⁻¹) * j⁻¹⁻¹ = v by group] at this⟩
  have hHJ : h.H ≤ h.J := fun b hb => mem_inf.2 ⟨h.L_le_C (h.H_le_L hb), h.H_le_normalizer_R hb⟩
  have hNJ : h.N .i1 ≤ h.J := fun n hn => mem_inf.2 ⟨h.L_le_C (h.N_le_L _ hn),
    h.N1_le_normalizer_R hn⟩
  by_contra hne
  have h12 := h.le_V12_of_invariant hle (fun b hb => hJ b (hHJ hb))
    (hJ _ (hNJ (h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1))))
    (hJ _ (hNJ h.r_mem_N_s_mem_N.1)) hne
  have hv := h.elt_rootElt_mem_V .i11 1
  obtain ⟨b, hb, hbv⟩ := d.exists_B1_comm_t (h.V11_le_S₁ hv)
  have hv12 : h.elt (rootElt h.K h.a .i11 1) ∈ h.V .i12 := h12 ⟨b, d.B1_le_A1 hb, hbv⟩
  exact h.elt_rootElt_one_ne_one .i11 (h.eq_one_of_mem_V11_of_mem_V12 hv hv12)

theorem exists_A1_comm_t {v : G} (hv : v ∈ h.R₁) : ∃ x ∈ d.A1, ⁅x, h.t⁆ = v := by
  rw [← d.kA1_eq] at hv
  exact hv

theorem mul_inv_mem_R₁_of_comm_eq {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1)
    (hxy : ⁅x, h.t⁆ = ⁅y, h.t⁆) : x * y⁻¹ ∈ h.R₁ :=
  d.mem_R₁_of_mem_A1 (mul_mem hx (inv_mem hy)) (by
    rw [d.comm_t_mul_A1 hx (inv_mem hy), d.comm_t_inv_A1 hy, hxy, mul_inv_cancel])

theorem comm_mem_R₁ {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1) : ⁅x, y⁆ ∈ h.R₁ := by
  refine d.mem_R₁_of_mem_A1 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
  have e : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  rw [e, d.comm_t_mul_A1 (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    d.comm_t_mul_A1 (mul_mem hx hy) (inv_mem hx), d.comm_t_mul_A1 hx hy, d.comm_t_inv_A1 hx,
    d.comm_t_inv_A1 hy, h.R₁_comm hx.2.2 hy.2.2]
  group

@[expose] def WA (i : Idx) : Subgroup G := d.A1 ⊓ h.CH i

theorem comm_t_mem_V_of_mem_WA {i k : Idx} (hi : i.isCenter = false)
    (hbr : ∀ l : Idx, l.isR1 = true → l ≠ k → Idx.brace i l ≠ 0) {x : G} (hx : x ∈ d.WA i) :
    ⁅x, h.t⁆ ∈ h.V k :=
  h.mem_V_of_mem_R₁_of_mem_CH hi hbr hx.1.2.2 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 (h.t_mem_CH i)) (inv_mem hx.2))
      (inv_mem (h.t_mem_CH i)))

theorem mem_V_of_mem_WA {i k : Idx} (hi : i.isCenter = false)
    (hbr : ∀ l : Idx, l.isR1 = true → l ≠ k → Idx.brace i l ≠ 0) {x : G} (hx : x ∈ d.WA i)
    (hxt : ⁅x, h.t⁆ = 1) : x ∈ h.V k :=
  h.mem_V_of_mem_R₁_of_mem_CH hi hbr (d.mem_R₁_of_mem_A1 hx.1 hxt) hx.2

theorem V_le_WA {i k : Idx} (hVR : h.V k ≤ h.R₁) (hV : h.V k ≤ h.CH i) : h.V k ≤ d.WA i :=
  le_inf (hVR.trans d.R₁_le_A1) hV

theorem exists_WA_comm_t {i k : Idx} (hVR : h.V k ≤ h.R₁) (hV : h.V k ≤ h.CH i) {v : G}
    (hv : v ∈ h.V k) : ∃ x ∈ d.WA i, ⁅x, h.t⁆ = v := by
  obtain ⟨y, hy, hyv⟩ := d.exists_A1_comm_t (hVR hv)
  have hbA : ∀ b ∈ h.Ht i, b * y * b⁻¹ ∈ d.A1 := fun b hb =>
    d.conj_J_mem_A1 (h.H_le_J (h.Ht_le_H i hb)) hy
  have hbt : ∀ b ∈ h.Ht i, b * h.t * b⁻¹ = h.t := fun b hb => by
    rw [h.mul_t_comm (h.H_le_L (h.Ht_le_H i hb)), mul_inv_cancel_right]
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_of_odd (B := h.Ht i) (N := h.R₁) (h.odd_card_Ht i)
    (fun n hn => h.R₁_mul_self hn) (fun n hn m hm => h.R₁_comm hn hm)
    (fun b hb n hn => (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J
      (h.Ht_le_H i hb))) n).1 hn) (y := y) fun b hb => by
      refine d.mem_R₁_of_mem_A1 (mul_mem (inv_mem hy) (hbA b hb)) ?_
      have e : ⁅b * y * b⁻¹, h.t⁆ = b * ⁅y, h.t⁆ * b⁻¹ := by
        conv_lhs => rw [← hbt b hb]
        simp only [commutatorElement_def]; group
      rw [d.comm_t_mul_A1 (inv_mem hy) (hbA b hb), d.comm_t_inv_A1 hy, e, hyv,
        mem_centralizer_iff.1 (hV hv) b hb, mul_inv_cancel_right, inv_mul_cancel]
  refine ⟨y * n, ⟨mul_mem hy (d.R₁_le_A1 hn), mem_centralizer_iff.2 fun b hb => ?_⟩, ?_⟩
  · have := hfix b hb
    calc b * (y * n) = b * (y * n) * b⁻¹ * b := by group
      _ = y * n * b := by rw [this]
  · rw [d.comm_t_mul_A1 hy (d.R₁_le_A1 hn), hyv, commutatorElement_eq_one_iff_mul_comm.2
      (h.mul_t_comm (h.R₁_le_R.trans h.R_le_L hn)), mul_one]

theorem comm_mul_R₁_right {x z r : G} (hx : x ∈ d.A1) (hz : z ∈ d.A1) (hr : r ∈ h.R₁) :
    ⁅x, r * z⁆ = ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq, commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx) r hr).symm, one_mul,
    h.R₁_comm hr (d.comm_mem_R₁ hx hz), mul_inv_cancel_right]

theorem comm_mul_right_A1 {x z z' : G} (hx : x ∈ d.A1) (hz : z ∈ d.A1) (hz' : z' ∈ d.A1) :
    ⁅x, z * z'⁆ = ⁅x, z⁆ * ⁅x, z'⁆ := by
  rw [commutatorElement_mul_right_eq, ← mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hz) _
    (d.comm_mem_R₁ hx hz'), mul_inv_cancel_right]

theorem comm_mul_R₁_left {x z r : G} (hx : x ∈ d.A1) (hz : z ∈ d.A1) (hr : r ∈ h.R₁) :
    ⁅r * z, x⁆ = ⁅z, x⁆ := by
  rw [commutatorElement_mul_left_eq, commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx) r hr), mul_one,
    h.R₁_comm hr (d.comm_mem_R₁ hz hx), mul_inv_cancel_right]

theorem comm_mul_left_A1 {x z z' : G} (hx : x ∈ d.A1) (hz : z ∈ d.A1) (hz' : z' ∈ d.A1) :
    ⁅z * z', x⁆ = ⁅z, x⁆ * ⁅z', x⁆ := by
  rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hz) _
    (d.comm_mem_R₁ hz' hx), mul_inv_cancel_right, h.R₁_comm (d.comm_mem_R₁ hz' hx)
    (d.comm_mem_R₁ hz hx)]

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.conj_H_mem_CH (h : Setup G) {i : Idx}
    {b : G} (hb : b ∈ h.H) {x : G} (hx : x ∈ h.CH i) : b * x * b⁻¹ ∈ h.CH i :=
  mem_centralizer_iff.2 fun g hg => by
    have hgb : g * b = b * g := h.H_comm (h.Ht_le_H i hg) hb
    have hgx := mem_centralizer_iff.1 hx g hg
    calc g * (b * x * b⁻¹) = b * (g * x) * b⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, hgb]; group
      _ = b * x * b⁻¹ * g := by
          rw [hgx]
          calc b * (x * g) * b⁻¹ = b * x * b⁻¹ * (b * g * b⁻¹) := by group
            _ = b * x * b⁻¹ * g := by rw [← hgb, mul_inv_cancel_right]

theorem conj_H_mem_WA {i : Idx} {b : G} (hb : b ∈ h.H) {x : G} (hx : x ∈ d.WA i) :
    b * x * b⁻¹ ∈ d.WA i :=
  ⟨d.conj_J_mem_A1 (h.H_le_J hb) hx.1, h.conj_H_mem_CH hb hx.2⟩

theorem WA_comm {i k : Idx} (hi : i.isCenter = false) (hk : k.isR1 = true)
    (hbr : ∀ l : Idx, l.isR1 = true → l ≠ k → Idx.brace i l ≠ 0) (hVR : h.V k ≤ h.R₁)
    (hV : h.V k ≤ h.CH i) {j : Idx} (hj : j.isCenter = false) (hjk : Idx.brace j k ≠ 0)
    {x y : G} (hx : x ∈ d.WA i) (hy : y ∈ d.WA i) : x * y = y * x := by
  classical
  have hkS : k.isSz = false := by cases k <;> simp_all [Idx.isR1, Idx.isSz]
  have hex : ∀ c : h.K, ∃ z ∈ d.WA i, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a k c) := fun c =>
    d.exists_WA_comm_t hVR hV (h.elt_rootElt_mem_V k c)
  choose lam hlam hlamt using hex
  have hΓ : ∀ c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hcCH : ∀ {u w}, u ∈ h.CH i → w ∈ h.CH i → ⁅u, w⁆ ∈ h.CH i := fun hu hw => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hw) (inv_mem hu)) (inv_mem hw)
  have hcV : ∀ {u w}, u ∈ d.WA i → w ∈ d.WA i → ⁅u, w⁆ ∈ h.V k := fun hu hw =>
    h.mem_V_of_mem_R₁_of_mem_CH hi hbr (d.comm_mem_R₁ hu.1 hw.1) (hcCH hu.2 hw.2)
  have hred : ∀ {u}, u ∈ d.WA i → ∃ c, u * (lam c)⁻¹ ∈ h.R₁ := fun {u} hu => by
    obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt hkS
      (d.comm_t_mem_V_of_mem_WA hi hbr hu)
    exact ⟨c, d.mul_inv_mem_R₁_of_comm_eq hu.1 (hlam c).1 (by rw [hc, hlamt])⟩
  have hadd : ∀ c e, lam (c + e) * (lam c * lam e)⁻¹ ∈ h.R₁ := fun c e =>
    d.mul_inv_mem_R₁_of_comm_eq (hlam _).1 (mul_mem (hlam c).1 (hlam e).1) (by
      rw [hlamt, d.comm_t_mul_A1 (hlam c).1 (hlam e).1, hlamt, hlamt, rootElt_add h.card_K hkS,
        h.elt_mul' (hΓ c) (hΓ e)])
  let β : h.K → h.K → h.K := fun c e => h.r1c ⁅lam c, lam e⁆ k
  have hRc : ∀ c e, ⁅lam c, lam e⁆ ∈ h.R₁ := fun c e => d.comm_mem_R₁ (hlam c).1 (hlam e).1
  have hβ : ∀ c e, β c e = 0 := by
    refine eq_zero_of_alternating_equivariant β (fun c c' e => ?_) (fun c e e' => ?_)
      (fun c => ?_) (fun l hl c e => ?_)
    · show h.r1c ⁅lam (c + c'), lam e⁆ k = h.r1c ⁅lam c, lam e⁆ k + h.r1c ⁅lam c', lam e⁆ k
      have e1 : lam (c + c') = (lam (c + c') * (lam c * lam c')⁻¹) * (lam c * lam c') := by
        group
      rw [e1, d.comm_mul_R₁_left (hlam e).1 (mul_mem (hlam c).1 (hlam c').1) (hadd c c'),
        d.comm_mul_left_A1 (hlam e).1 (hlam c).1 (hlam c').1, h.r1c_mul (hRc c e) (hRc c' e) hk]
    · show h.r1c ⁅lam c, lam (e + e')⁆ k = h.r1c ⁅lam c, lam e⁆ k + h.r1c ⁅lam c, lam e'⁆ k
      have e1 : lam (e + e') = (lam (e + e') * (lam e * lam e')⁻¹) * (lam e * lam e') := by
        group
      rw [e1, d.comm_mul_R₁_right (hlam c).1 (mul_mem (hlam e).1 (hlam e').1) (hadd e e'),
        d.comm_mul_right_A1 (hlam c).1 (hlam e).1 (hlam e').1,
        h.r1c_mul (hRc c e) (hRc c e') hk]
    · show h.r1c ⁅lam c, lam c⁆ k = 0
      rw [commutatorElement_self, h.r1c_one hk]
    · obtain ⟨t, -, ht⟩ := exists_rootChar_mul_eq h.card_K hj hjk one_ne_zero hl
      rw [mul_one] at ht
      set b := h.elt (torusPair h.a t) with hbdef
      have hbH : b ∈ h.H := h.elt_torusPair_mem_H t
      have hbt : b * h.t * b⁻¹ = h.t := by
        rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
      have hconj : ∀ c, lam (l * c) * (b * lam c * b⁻¹)⁻¹ ∈ h.R₁ := fun c =>
        d.mul_inv_mem_R₁_of_comm_eq (hlam _).1 (d.conj_H_mem_WA hbH (hlam c)).1 (by
          rw [hlamt, ← ht, ← h.elt_torusPair_conj_rootElt, ← hlamt c, ← hbdef]
          conv_rhs => rw [← hbt]
          simp only [commutatorElement_def]; group)
      have hX : b * lam c * b⁻¹ ∈ d.A1 := (d.conj_H_mem_WA hbH (hlam c)).1
      have hY : b * lam e * b⁻¹ ∈ d.A1 := (d.conj_H_mem_WA hbH (hlam e)).1
      have key : ⁅lam (l * c), lam (l * e)⁆ = ⁅b * lam c * b⁻¹, b * lam e * b⁻¹⁆ := by
        have h1 := d.comm_mul_R₁_left (x := lam (l * e)) (z := b * lam c * b⁻¹) (hlam _).1 hX
          (hconj c)
        rw [inv_mul_cancel_right] at h1
        rw [h1]
        have h2 := d.comm_mul_R₁_right (x := b * lam c * b⁻¹) (z := b * lam e * b⁻¹) hX hY
          (hconj e)
        rw [inv_mul_cancel_right] at h2
        exact h2
      show h.r1c ⁅lam (l * c), lam (l * e)⁆ k = l * h.r1c ⁅lam c, lam e⁆ k
      rw [key, show ⁅b * lam c * b⁻¹, b * lam e * b⁻¹⁆ = b * ⁅lam c, lam e⁆ * b⁻¹ by
        simp only [commutatorElement_def]; group, hbdef, h.r1c_torus (hRc c e) t hk, ht]
  obtain ⟨cx, hcx⟩ := hred hx
  obtain ⟨cy, hcy⟩ := hred hy
  have e2 : ⁅x, y⁆ = ⁅lam cx, lam cy⁆ := by
    have h1 := d.comm_mul_R₁_left (x := y) (z := lam cx) hy.1 (hlam cx).1 hcx
    rw [inv_mul_cancel_right] at h1
    rw [h1]
    have h2 := d.comm_mul_R₁_right (x := lam cx) (z := lam cy) (hlam cx).1 (hlam cy).1 hcy
    rw [inv_mul_cancel_right] at h2
    exact h2
  have hV1 := hcV (hlam cx) (hlam cy)
  have h1 : ⁅x, y⁆ = 1 := by
    rw [e2]
    refine h.eq_of_r1c_eq (hVR hV1) (one_mem _) fun m hm => ?_
    rw [h.r1c_one hm]
    by_cases hmk : m = k
    · subst hmk
      exact hβ cx cy
    · rw [← h.pull_rootJoin_singleton] at hV1
      exact h.r1c_eq_zero_of_mem (by simpa using hk) hV1 hm (by simpa using hmk)
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem r1c_comm_eq_zero_of_brace_ne {i : Idx} (hi : i.isCenter = false) {x : G}
    (hx : x ∈ d.WA i) {k : Idx} (hk : k.isR1 = true) {y : G} (hy : y ∈ d.A1)
    (hyk : ⁅y, h.t⁆ ∈ h.V k) {m : Idx} (hm : m.isR1 = true)
    (hb : Idx.brace i k ≠ Idx.brace i m) : h.r1c ⁅x, y⁆ m = 0 := by
  classical
  have hkS : k.isSz = false := by cases k <;> simp_all [Idx.isR1, Idx.isSz]
  have hex : ∀ c : h.K, ∃ z ∈ d.A1, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a k c) := fun c =>
    d.exists_A1_comm_t (h.elt_rootElt_mem_R₁ hk c)
  choose lam hlam hlamt using hex
  have hΓ : ∀ c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  obtain ⟨c₀, hc₀⟩ := h.exists_eq_elt_rootElt hkS hyk
  have hyr : y * (lam c₀)⁻¹ ∈ h.R₁ :=
    d.mul_inv_mem_R₁_of_comm_eq hy (hlam c₀) (by rw [hc₀, hlamt])
  have e0 : ⁅x, y⁆ = ⁅x, lam c₀⁆ := by
    have : y = (y * (lam c₀)⁻¹) * lam c₀ := by group
    rw [this, d.comm_mul_R₁_right hx.1 (hlam c₀) hyr]
  rw [e0]
  refine h.r1c_eq_zero_of_brace_ne' hi (j := k) (Ψ := fun c => ⁅x, lam c⁆)
    (fun c e l hl => ?_) (fun t ht c l hl => ?_) hm hb c₀
  · have h1 : lam (c + e) * (lam c * lam e)⁻¹ ∈ h.R₁ :=
      d.mul_inv_mem_R₁_of_comm_eq (hlam _) (mul_mem (hlam c) (hlam e)) (by
        rw [hlamt, d.comm_t_mul_A1 (hlam c) (hlam e), hlamt, hlamt, rootElt_add h.card_K hkS,
          h.elt_mul' (hΓ c) (hΓ e)])
    have e1 : lam (c + e) = (lam (c + e) * (lam c * lam e)⁻¹) * (lam c * lam e) := by group
    show h.r1c ⁅x, lam (c + e)⁆ l = h.r1c ⁅x, lam c⁆ l + h.r1c ⁅x, lam e⁆ l
    rw [e1, d.comm_mul_R₁_right hx.1 (mul_mem (hlam c) (hlam e)) h1,
      d.comm_mul_right_A1 hx.1 (hlam c) (hlam e),
      h.r1c_mul (d.comm_mem_R₁ hx.1 (hlam c)) (d.comm_mem_R₁ hx.1 (hlam e)) hl]
  · set b := h.elt (torusPair h.a t) with hbdef
    have hb : b ∈ h.Ht i := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hbJ := h.H_le_J (h.Ht_le_H i hb)
    have hbt : b * h.t * b⁻¹ = h.t := by
      rw [h.mul_t_comm (h.H_le_L (h.Ht_le_H i hb)), mul_inv_cancel_right]
    have hbl := d.conj_J_mem_A1 hbJ (hlam c)
    have h1 : lam ((rootChar h.K h.a k t : h.K) * c) * (b * lam c * b⁻¹)⁻¹ ∈ h.R₁ :=
      d.mul_inv_mem_R₁_of_comm_eq (hlam _) hbl (by
        rw [hlamt, ← h.elt_torusPair_conj_rootElt, ← hlamt c, ← hbdef]
        conv_rhs => rw [← hbt]
        simp only [commutatorElement_def]; group)
    have e1 : lam ((rootChar h.K h.a k t : h.K) * c) =
        (lam ((rootChar h.K h.a k t : h.K) * c) * (b * lam c * b⁻¹)⁻¹) * (b * lam c * b⁻¹) := by
      group
    have hxb : x * b = b * x := (mem_centralizer_iff.1 hx.2 b hb).symm
    show h.r1c ⁅x, lam ((rootChar h.K h.a k t : h.K) * c)⁆ l =
      (rootChar h.K h.a l t : h.K) * h.r1c ⁅x, lam c⁆ l
    rw [e1, d.comm_mul_R₁_right hx.1 hbl h1, commutatorElement_conj_of_commute hxb,
      h.r1c_torus (d.comm_mem_R₁ hx.1 (hlam c)) t hl]

theorem comm_WA_mem {i j k l : Idx} (hi : i.isCenter = false) (hj : j.isCenter = false)
    (hk : k.isR1 = true) (hl : l.isR1 = true)
    (hbri : ∀ m : Idx, m.isR1 = true → m ≠ k → Idx.brace i m ≠ 0)
    (hbrj : ∀ m : Idx, m.isR1 = true → m ≠ l → Idx.brace j m ≠ 0) {S : Finset Idx}
    (hS : ∀ m : Idx, m.isR1 = true → m ∉ S →
      Idx.brace i l ≠ Idx.brace i m ∨ Idx.brace j k ≠ Idx.brace j m)
    {x y : G} (hx : x ∈ d.WA i) (hy : y ∈ d.WA j) : ⁅x, y⁆ ∈ h.pull (rootJoin h.K h.a S) := by
  refine h.mem_of_r1c_eq_zero (d.comm_mem_R₁ hx.1 hy.1) fun m hm hmS => ?_
  rcases hS m hm hmS with hb | hb
  · exact d.r1c_comm_eq_zero_of_brace_ne hi hx hl hy.1 (d.comm_t_mem_V_of_mem_WA hj hbrj hy) hm hb
  · have h0 := d.r1c_comm_eq_zero_of_brace_ne hj hy hk hx.1 (d.comm_t_mem_V_of_mem_WA hi hbri hx)
      hm hb
    rw [← commutatorElement_inv, h.r1c_inv (d.comm_mem_R₁ hy.1 hx.1) hm, h0]

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.V_le_R₁ (h : Setup G) {k : Idx}
    (hk : k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx)) : h.V k ≤ h.R₁ :=
  h.pull_mono (rootV_le_rootJoin hk)

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.V_le_CH (h : Setup G) {i k : Idx}
    (hi : i.isCenter = false) (hk : k = i ∨ k = i.center) : h.V k ≤ h.CH i := by
  rcases hk with rfl | rfl
  · exact h.V_le_centralizer_Ht hi
  · exact (h.V_center_le i).trans (h.V_le_centralizer_Ht hi)

theorem WA_five_eq : d.WA .i5 = d.W12 := by
  refine le_antisymm (fun x hx => ?_) (le_inf d.W12_le_A1 d.W12_le_CH)
  have hxt := d.comm_t_mem_V_of_mem_WA (k := .i12) rfl (by decide) hx
  obtain ⟨z, hz, hzt⟩ := d.exists_W12_conj hxt
  have hzt' : ⁅z, h.t⁆ = ⁅x, h.t⁆ := by
    rw [commutatorElement_def, hzt, ← h.mul_t_comm (h.V12_le_L hxt), mul_inv_cancel_right]
  have hr := d.mul_inv_mem_R₁_of_comm_eq hx.1 (d.W12_le_A1 hz) hzt'.symm
  have hv : x * z⁻¹ ∈ h.V .i12 := h.mem_V_of_mem_R₁_of_mem_CH (k := .i12) rfl (by decide) hr
    (mul_mem hx.2 (inv_mem (d.W12_le_CH hz)))
  have e : x = (x * z⁻¹) * z := by group
  rw [e]
  exact mul_mem (d.V12_le_W12 hv) hz

theorem W11_le_CH6 : d.W11 ≤ h.CH .i6 := fun y hy => by
  show y ∈ centralizer (h.Ht .i6 : Set G)
  rw [h.Ht6_eq_map_conj_s]
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have hz : h.s * y * h.s⁻¹ ∈ d.W12 := (d.mem_W11_iff).1 hy
  have hcz := mem_centralizer_iff.1 (d.W12_le_CH hz) c hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : h.s⁻¹ * y * h.s = h.s * y * h.s⁻¹ := by rw [h.s_inv]
  have hcz' : c * (h.s⁻¹ * y * h.s) = (h.s⁻¹ * y * h.s) * c := by rw [e1]; exact hcz
  calc h.s * c * h.s⁻¹ * y = h.s * (c * (h.s⁻¹ * y * h.s)) * h.s⁻¹ := by group
    _ = h.s * ((h.s⁻¹ * y * h.s) * c) * h.s⁻¹ := by rw [hcz']
    _ = y * (h.s * c * h.s⁻¹) := by group

theorem WA_six_eq : d.WA .i6 = d.W11 := by
  refine le_antisymm (fun x hx => ?_) (le_inf d.W11_le_A1 d.W11_le_CH6)
  have hxt := d.comm_t_mem_V_of_mem_WA (k := .i11) rfl (by decide) hx
  obtain ⟨y, hy, hyt⟩ := d.exists_W11_comm_t hxt
  have hr := d.mul_inv_mem_R₁_of_comm_eq hx.1 (d.W11_le_A1 hy) hyt.symm
  have hv : x * y⁻¹ ∈ h.V .i11 := h.mem_V_of_mem_R₁_of_mem_CH (k := .i11) rfl (by decide) hr
    (mul_mem hx.2 (inv_mem (d.W11_le_CH6 hy)))
  have e : x = (x * y⁻¹) * y := by group
  rw [e]
  exact mul_mem (d.V11_le_W11 hv) hy

theorem A1_le_sup : d.A1 ≤ d.WA .i4 ⊔ d.WA .i6 ⊔ d.WA .i5 ⊔ d.WA .i9 ⊔ d.WA .i10 := by
  classical
  set M := d.WA .i4 ⊔ d.WA .i6 ⊔ d.WA .i5 ⊔ d.WA .i9 ⊔ d.WA .i10 with hM
  have h4 : d.WA .i4 ≤ M := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have h6 : d.WA .i6 ≤ M :=
    le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have h5 : d.WA .i5 ≤ M := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have h9 : d.WA .i9 ≤ M := le_sup_right.trans le_sup_left
  have h10 : d.WA .i10 ≤ M := le_sup_right
  have hlift : ∀ (i k : Idx), i.isCenter = false → (k = i ∨ k = i.center) →
      k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) → d.WA i ≤ M → ∀ c : h.K,
      ∃ z ∈ M, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a k c) := fun i k hi hk hkR hiM c => by
    obtain ⟨z, hz, hzt⟩ := d.exists_WA_comm_t (h.V_le_R₁ hkR) (h.V_le_CH hi hk)
      (h.elt_rootElt_mem_V k c)
    exact ⟨z, hiM hz, hzt⟩
  have hMA : M ≤ d.A1 := sup_le (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
    inf_le_left) inf_le_left
  have hR₁M : h.R₁ ≤ M := h.R₁_le_of_V_le
    ((d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH (i := .i4) rfl (Or.inr rfl))).trans h4)
    ((d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH (i := .i9) rfl (Or.inl rfl))).trans h9)
    ((d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH (i := .i10) rfl (Or.inl rfl))).trans h10)
    ((d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH (i := .i6) rfl (Or.inr rfl))).trans h6)
    ((d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH (i := .i5) rfl (Or.inr rfl))).trans h5)
  intro x hx
  set u := h.r1c ⁅x, h.t⁆ with hu
  obtain ⟨z8, hz8, e8⟩ := hlift .i4 .i8 rfl (Or.inr rfl) (by decide) h4 (u .i8)
  obtain ⟨z11, hz11, e11⟩ := hlift .i6 .i11 rfl (Or.inr rfl) (by decide) h6 (u .i11)
  obtain ⟨z12, hz12, e12⟩ := hlift .i5 .i12 rfl (Or.inr rfl) (by decide) h5 (u .i12)
  obtain ⟨z9, hz9, e9⟩ := hlift .i9 .i9 rfl (Or.inl rfl) (by decide) h9 (u .i9)
  obtain ⟨z10, hz10, e10⟩ := hlift .i10 .i10 rfl (Or.inl rfl) (by decide) h10 (u .i10)
  set w := z8 * z11 * z12 * z9 * z10 with hw
  have hwM : w ∈ M := mul_mem (mul_mem (mul_mem (mul_mem hz8 hz11) hz12) hz9) hz10
  have hwA := hMA hwM
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hwt : ⁅w, h.t⁆ = ⁅x, h.t⁆ := by
    have hA := fun {z} (hz : z ∈ M) => hMA hz
    rw [hw, d.comm_t_mul_A1 (hA (mul_mem (mul_mem (mul_mem hz8 hz11) hz12) hz9)) (hA hz10),
      d.comm_t_mul_A1 (hA (mul_mem (mul_mem hz8 hz11) hz12)) (hA hz9),
      d.comm_t_mul_A1 (hA (mul_mem hz8 hz11)) (hA hz12), d.comm_t_mul_A1 (hA hz8) (hA hz11),
      e8, e11, e12, e9, e10, ← h.elt_r1Elt_r1c hx.2.2, r1Elt,
      h.elt_mul' (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
      h.elt_mul' (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
      h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]
  have hr := d.mul_inv_mem_R₁_of_comm_eq hx hwA hwt.symm
  have e : x = (x * w⁻¹) * w := by group
  rw [e]
  exact mul_mem (hR₁M hr) hwM

theorem comm_WA_five {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.WA .i5) : ⁅x, y⁆ = 1 := by
  rw [d.WA_five_eq] at hy
  exact commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 hx.2.1 y hy).symm

@[expose] def IsWPair (i k : Idx) : Prop :=
  (i = .i4 ∧ k = .i8) ∨ (i = .i9 ∧ k = .i9) ∨ (i = .i10 ∧ k = .i10) ∨ (i = .i6 ∧ k = .i11) ∨
    (i = .i5 ∧ k = .i12)

instance (i k : Idx) : Decidable (IsWPair i k) := by unfold IsWPair; infer_instance

theorem IsWPair.isCenter {i k : Idx} (hik : IsWPair i k) : i.isCenter = false := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem IsWPair.isR1 {i k : Idx} (hik : IsWPair i k) : k.isR1 = true := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem IsWPair.brace {i k : Idx} (hik : IsWPair i k) :
    ∀ m : Idx, m.isR1 = true → m ≠ k → Idx.brace i m ≠ 0 := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem IsWPair.mem {i k : Idx} (hik : IsWPair i k) :
    k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem IsWPair.eq {i k : Idx} (hik : IsWPair i k) : k = i ∨ k = i.center := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem IsWPair.transitive {i k : Idx} (hik : IsWPair i k) :
    ∃ j : Idx, j.isCenter = false ∧ Idx.brace j k ≠ 0 := by
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨.i9, rfl, by decide⟩
  · exact ⟨.i10, rfl, by decide⟩
  · exact ⟨.i9, rfl, by decide⟩
  · exact ⟨.i9, rfl, by decide⟩
  · exact ⟨.i9, rfl, by decide⟩

theorem WA_comm' {i k : Idx} (hik : IsWPair i k) {x y : G} (hx : x ∈ d.WA i)
    (hy : y ∈ d.WA i) : x * y = y * x := by
  obtain ⟨j, hj, hjk⟩ := hik.transitive
  exact d.WA_comm hik.isCenter hik.isR1 hik.brace (h.V_le_R₁ hik.mem)
    (h.V_le_CH hik.isCenter hik.eq) hj hjk hx hy

theorem comm_A1_mem_rootJoin {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1) :
    ⁅x, y⁆ ∈ h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) := by
  classical
  set D := h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) with hD
  have hpair : ∀ {i k j l : Idx}, IsWPair i k → IsWPair j l → ∀ {x y : G}, x ∈ d.WA i →
      y ∈ d.WA j → ⁅x, y⁆ ∈ D := by
    intro i k j l hik hjl x y hx hy
    by_cases hj5 : j = .i5
    · subst hj5
      rw [d.comm_WA_five hx.1 hy]
      exact one_mem _
    by_cases hi5 : i = .i5
    · subst hi5
      rw [← commutatorElement_inv, d.comm_WA_five hy.1 hx, inv_one]
      exact one_mem _
    by_cases hij : i = j
    · subst hij
      rw [commutatorElement_eq_one_iff_mul_comm.2 (d.WA_comm' hik hx hy)]
      exact one_mem _
    refine d.comm_WA_mem hik.isCenter hjl.isCenter hik.isR1 hjl.isR1 hik.brace hjl.brace ?_ hx hy
    rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hjl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first
        | exact absurd rfl hij
        | exact absurd rfl hj5
        | exact absurd rfl hi5
        | decide
  have hW : ∀ {i k : Idx}, IsWPair i k → d.WA i ≤ d.WA .i4 ⊔ d.WA .i6 ⊔ d.WA .i5 ⊔ d.WA .i9 ⊔
      d.WA .i10 := by
    intro i k hik
    rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
    · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hA : ∀ {M : Subgroup G}, d.WA .i4 ≤ M → d.WA .i6 ≤ M → d.WA .i5 ≤ M → d.WA .i9 ≤ M →
      d.WA .i10 ≤ M → d.A1 ≤ M := fun h4 h6 h5 h9 h10 =>
    d.A1_le_sup.trans (sup_le (sup_le (sup_le (sup_le h4 h6) h5) h9) h10)
  have hright : ∀ {i k : Idx}, IsWPair i k → ∀ {x : G}, x ∈ d.WA i → ∀ y ∈ d.A1, ⁅x, y⁆ ∈ D := by
    intro i k hik x hx
    let M : Subgroup G :=
      { carrier := {y | y ∈ d.A1 ∧ ⁅x, y⁆ ∈ D}
        mul_mem' := fun {y y'} hy hy' => ⟨mul_mem hy.1 hy'.1, by
          rw [d.comm_mul_right_A1 hx.1 hy.1 hy'.1]
          exact mul_mem hy.2 hy'.2⟩
        one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
        inv_mem' := fun {y} hy => ⟨inv_mem hy.1, by
          have e := d.comm_mul_right_A1 hx.1 hy.1 (inv_mem hy.1)
          rw [mul_inv_cancel, commutatorElement_one_right] at e
          rw [eq_inv_of_mul_eq_one_right e.symm]
          exact inv_mem hy.2⟩ }
    have hWM : ∀ {j l : Idx}, IsWPair j l → d.WA j ≤ M := fun hjl y hy =>
      ⟨hy.1, hpair hik hjl hx hy⟩
    intro y hy
    exact (hA (hWM (j := .i4) (Or.inl ⟨rfl, rfl⟩))
      (hWM (j := .i6) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
      (hWM (j := .i5) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
      (hWM (j := .i9) (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (hWM (j := .i10) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hy).2
  let M : Subgroup G :=
    { carrier := {x | x ∈ d.A1 ∧ ∀ y ∈ d.A1, ⁅x, y⁆ ∈ D}
      mul_mem' := fun {x x'} hx hx' => ⟨mul_mem hx.1 hx'.1, fun y hy => by
        rw [d.comm_mul_left_A1 hy hx.1 hx'.1]
        exact mul_mem (hx.2 y hy) (hx'.2 y hy)⟩
      one_mem' := ⟨one_mem _, fun y _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun y hy => by
        have e := d.comm_mul_left_A1 hy hx.1 (inv_mem hx.1)
        rw [mul_inv_cancel, commutatorElement_one_left] at e
        rw [eq_inv_of_mul_eq_one_right e.symm]
        exact inv_mem (hx.2 y hy)⟩ }
  have hWM : ∀ {i k : Idx}, IsWPair i k → d.WA i ≤ M := fun hik x hx =>
    ⟨hx.1, hright hik hx⟩
  exact (hA (hWM (i := .i4) (Or.inl ⟨rfl, rfl⟩))
    (hWM (i := .i6) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    (hWM (i := .i5) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    (hWM (i := .i9) (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (hWM (i := .i10) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hx).2 y hy

theorem commutator_A1_le : ⁅d.A1, d.A1⁆ ≤ h.V .i12 := by
  have hD : ⁅d.A1, d.A1⁆ ≤ h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) :=
    (commutator_le).2 fun x hx y hy => d.comm_A1_mem_rootJoin hx hy
  have hJ : ∀ j ∈ h.J, j ∈ normalizer ((⁅d.A1, d.A1⁆ : Subgroup G) : Set G) := fun j hj =>
    mem_normalizer_commutator_of (d.J_le_normalizer_A1 hj) (d.J_le_normalizer_A1 hj)
  refine h.le_V12_of_invariant ((commutator_le).2 fun x hx y hy => d.comm_mem_R₁ hx hy)
    (fun b hb => hJ b (h.H_le_J hb)) (hJ _ (h.N1_le_J (h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1))))
    (hJ _ (h.N1_le_J h.r_mem_N_s_mem_N.1)) fun heq => ?_
  have h9 := h.elt_rootElt_mem_R₁ (k := .i9) rfl 1
  rw [← heq] at h9
  have h0 := h.r1c_eq_zero_of_mem (by decide) (hD h9) (k := .i9) rfl (by decide)
  rw [show h.elt (rootElt h.K h.a .i9 1) = h.elt (r1Elt h.K h.a (Pi.single .i9 1)) by
    rw [← rootElt_eq_r1Elt rfl], h.r1c_elt_r1Elt _ rfl] at h0
  simp at h0

theorem comm_A1_mem_V12 {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1) : ⁅x, y⁆ ∈ h.V .i12 :=
  d.commutator_A1_le (commutator_mem_commutator hx hy)

theorem comm_WA_eq_one {i k j l : Idx} (hik : IsWPair i k) (hjl : IsWPair j l)
    (hkl : ¬ ((k = .i8 ∧ l = .i11) ∨ (k = .i11 ∧ l = .i8) ∨ (k = .i9 ∧ l = .i10) ∨
      (k = .i10 ∧ l = .i9))) {x y : G} (hx : x ∈ d.WA i) (hy : y ∈ d.WA j) : ⁅x, y⁆ = 1 := by
  classical
  by_cases hj5 : j = .i5
  · subst hj5; exact d.comm_WA_five hx.1 hy
  by_cases hi5 : i = .i5
  · subst hi5; rw [← commutatorElement_inv, d.comm_WA_five hy.1 hx, inv_one]
  by_cases hij : i = j
  · subst hij; exact commutatorElement_eq_one_iff_mul_comm.2 (d.WA_comm' hik hx hy)
  have hS : ⁅x, y⁆ ∈ h.pull (rootJoin h.K h.a {.i8, .i11}) := by
    refine d.comm_WA_mem hik.isCenter hjl.isCenter hik.isR1 hjl.isR1 hik.brace hjl.brace ?_ hx hy
    rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hjl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first
        | exact absurd rfl hij
        | exact absurd rfl hj5
        | exact absurd rfl hi5
        | exact absurd (by decide) hkl
        | decide
  have h12 := d.comm_A1_mem_V12 hx.1 hy.1
  refine h.eq_of_r1c_eq (d.comm_mem_R₁ hx.1 hy.1) (one_mem _) fun m hm => ?_
  rw [h.r1c_one hm]
  by_cases hm12 : m = .i12
  · subst hm12; exact h.r1c_eq_zero_of_mem (by decide) hS rfl (by decide)
  · exact h.r1c_eq_zero_of_mem_V12 h12 hm hm12

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf31Psi
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf4X

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


@[expose] def Frame203Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K', InnerOn K x → InnerOn K' x →
        x ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')

@[expose] def Frame203Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∀ w ∈ V, w * w ≠ 1 → ¬ InnerOn K w ∧ ¬ InnerOn K' w

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem innerOn_swap {g x : G} {K : Subgroup G} (h : InnerOn K (g⁻¹ * x * g)) :
    InnerOn (conjSub g K) x := by
  obtain ⟨k, hk, h⟩ := h
  refine ⟨g * k * g⁻¹, conj_mem_conjSub hk, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ K := mem_conjSub_iff.mp hy
  have := h _ hy'
  have e : g⁻¹ * ((x * y * x⁻¹) * ((g * k * g⁻¹) * y * (g * k * g⁻¹)⁻¹)⁻¹) * g =
      (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ *
        (k * (g⁻¹ * y * g) * k⁻¹)⁻¹ := by group
  rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff, e]
  exact this

section Main

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem frameX_le_N :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K : Set G) :=
  fun x hx => ((sec20X_le_normalizers_frame d) hx).1

theorem K_le_kerG {y : G} (hy : y ∈ K) : y ∈ kerG K :=
  mem_kerG.mpr ⟨Subgroup.le_normalizer hy, psiK_eq_one_of_mem K hy⟩

theorem K'_le_kerG {y : G} (hy : y ∈ K') : y ∈ kerG K :=
  mem_kerG.mpr ⟨(le_trivialOnQuot_K d hy).1,
    psiK_eq_one_of_mem_trivialOnQuot K (le_trivialOnQuot_K d hy)⟩

theorem oddCoreX_le_kerG {y : G} (hy : y ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K')) :
    y ∈ kerG K :=
  mem_kerG.mpr ⟨frameX_le_N d (oddCoreOf_le_self _ hy),
    psiK_eq_one_of_mem_oddCore K _ le_sec20X_left (frameX_le_N d) hy⟩

theorem epsK_eq_one_of_mem_kerG {y : G} (hy : y ∈ kerG K) : epsK K y = 1 := by
  obtain ⟨h, h1⟩ := mem_kerG.mp hy
  rw [epsK_of_mem K h, h1, map_one]

theorem exists_gen_V :
    ∃ v₀ ∈ V, (∀ w ∈ V, ∃ n : ℤ, w = v₀ ^ n) ∧ v₀ * v₀ ≠ 1 ∧ v₀ * v₀ = t := by
  obtain ⟨R₀, -, hVR₀, hcyc, -⟩ := d.hV
  obtain ⟨v, hv⟩ := hcyc.exists_generator
  have hcR := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ d.hV d.late_mem_K d.hR
  have hV4 : Nat.card V = 4 := by rw [d.card8] at hcR; omega
  have hord : orderOf (v : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv, hV4]
  have hv1 : (v : G) * (v : G) ≠ 1 := by
    rw [← pow_two]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  have hvv : ((v : G) * (v : G)) * ((v : G) * (v : G)) = 1 := by
    have : (v : G) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    calc ((v : G) * (v : G)) * ((v : G) * (v : G)) = (v : G) ^ 4 := by
          simp [pow_succ, mul_assoc]
      _ = 1 := this
  refine ⟨(v : G), v.2, fun w hw => ?_, hv1, ?_⟩
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hv ⟨w, hw⟩)
    exact ⟨n, by simpa using (congrArg Subtype.val hn).symm⟩
  · exact d.eq_t_of_invol_mem_V (V.mul_mem v.2 v.2) hvv hv1

theorem eps_conj_gen {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgK : conjSub g K = K') {c w : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    (hw : w ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    epsK K (c * w * c⁻¹) * epsK K (g⁻¹ * (c * w * c⁻¹) * g) =
      epsK K w * epsK K (g⁻¹ * w * g) := by
  have hXN := frameX_le_N d
  have hw1 : w ∈ Subgroup.normalizer (K : Set G) := hXN hw
  have hw2 : g⁻¹ * w * g ∈ Subgroup.normalizer (K : Set G) :=
    conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d) hw).2
  have hK'swap : conjSub g K' = K := conjSub_swap_K' d hg hgK
  rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) hc with hcK | hcK
  · have hcK' : conjSub c K' = K' := by
      rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
      · exact absurd ((conjSub_inj c).mp (hcK.trans h.symm)) d.K_ne_K'
      · exact h
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hcK
    have hcN' : c ∈ Subgroup.normalizer (K' : Set G) := mem_normalizer_iff_conjSub_eq.mpr hcK'
    have hgc : g⁻¹ * c * g ∈ Subgroup.normalizer (K : Set G) :=
      conj_swap_mem_normalizer d hg hgK hcN'
    have e : g⁻¹ * (c * w * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * w * g) * (g⁻¹ * c * g)⁻¹ := by
      group
    rw [e, epsK_conj K hcN hw1, epsK_conj K hgc hw2]
  · have hcK' : conjSub c K' = K := by
      rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
      · exact h
      · exact absurd ((conjSub_inj c).mp (hcK.trans h.symm)) d.K_ne_K'
    have hgK2 : conjSub g⁻¹ K = K' := by
      rw [← hK'swap]; exact conjSub_inv_conjSub g K'
    have hgK3 : conjSub g⁻¹ K' = K := by
      rw [← hgK]; exact conjSub_inv_conjSub g K
    have hhN : c * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hgK2, hcK']
    have hhN' : c * g⁻¹ ∈ Subgroup.normalizer (K' : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hgK3, hcK]
    have hw' : g * w * g⁻¹ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
      conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hg (conj_mem_conjSub hw)
    have hg2 : g * g ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hgK, hK'swap]
    have hconj : g⁻¹ * (c * g⁻¹) * g ∈ Subgroup.normalizer (K : Set G) :=
      conj_swap_mem_normalizer d hg hgK hhN'
    have e1 : c * w * c⁻¹ = (c * g⁻¹) * (g * w * g⁻¹) * (c * g⁻¹)⁻¹ := by group
    have e2 : g * w * g⁻¹ = (g * g) * (g⁻¹ * w * g) * (g * g)⁻¹ := by group
    have e3 : g⁻¹ * (c * w * c⁻¹) * g =
        (g⁻¹ * (c * g⁻¹) * g) * w * (g⁻¹ * (c * g⁻¹) * g)⁻¹ := by group
    have A1 : epsK K (c * w * c⁻¹) = epsK K (g⁻¹ * w * g) := by
      rw [e1, epsK_conj K hhN (hXN hw'), e2, epsK_conj K hg2 hw2]
    have A2 : epsK K (g⁻¹ * (c * w * c⁻¹) * g) = epsK K w := by
      rw [e3, epsK_conj K hconj hw1]
    rw [A1, A2, mul_comm]

theorem conj_swap_sup {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgK : conjSub g K = K') {x : G} (hx : x ∈ K ⊔ K') : g⁻¹ * x * g ∈ K ⊔ K' := by
  have h : K ⊔ K' ≤ Subgroup.comap (MulAut.conj g⁻¹).toMonoidHom (K ⊔ K') := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have := conj_swap_K d hg hgK hy
      exact (le_sup_right : K' ≤ K ⊔ K') (by simpa using this)
    · have := conj_swap_K' d hg hgK hy
      exact (le_sup_left : K ≤ K ⊔ K') (by simpa using this)
  simpa using h hx

theorem epsK_prod_eq_one {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgK : conjSub g K = K') (e : Kbar K ≃* Q8)
    (hO : ∀ w ∈ V, w * w ≠ 1 → ¬ InnerOn K w ∧ ¬ InnerOn K' w)
    {x : G} (hx : x ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    epsK K x * epsK K (g⁻¹ * x * g) = 1 := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hXN := frameX_le_N d
  have hXN2 : ∀ y ∈ X, g⁻¹ * y * g ∈ Subgroup.normalizer (K : Set G) := fun y hy =>
    conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d) hy).2
  have hc3 : Nat.card (Idx2 (Kbar K)) = 3 := card_idx2_of_equiv_q8 e
  have hKK' : K ⊔ K' ≤ kerG K := sup_le (fun y hy => K_le_kerG d hy) (fun y hy => K'_le_kerG d hy)
  obtain ⟨v₀, hv₀V, hgen, hv1, hvt⟩ := exists_gen_V d
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hv₀X : v₀ ∈ X := tw.hVX hv₀V
  obtain ⟨hout1, hout2⟩ := hO v₀ hv₀V hv1
  have hvvK : v₀ * v₀ ∈ kerG K := hKK' (by rw [hvt]; exact d.htKK)
  have hε1 : epsK K v₀ = -1 := by
    rw [epsK_of_mem K (hXN hv₀X)]
    refine sign_eq_neg_one_of_invol hc3 _ ?_ ?_
    · intro h1
      exact hout1 ((psiK_eq_one_iff K e ⟨v₀, hXN hv₀X⟩).mp h1)
    · obtain ⟨_, h2⟩ := mem_kerG.mp hvvK
      rw [← map_mul]
      exact h2
  have hu : g⁻¹ * v₀ * g ∈ Subgroup.normalizer (K : Set G) := hXN2 v₀ hv₀X
  have huu : (g⁻¹ * v₀ * g) * (g⁻¹ * v₀ * g) ∈ kerG K := by
    have h1 : g⁻¹ * (v₀ * v₀) * g ∈ kerG K := hKK' (conj_swap_sup d hg hgK (by rw [hvt]; exact d.htKK))
    have e1 : (g⁻¹ * v₀ * g) * (g⁻¹ * v₀ * g) = g⁻¹ * (v₀ * v₀) * g := by group
    rw [e1]; exact h1
  have hε2 : epsK K (g⁻¹ * v₀ * g) = -1 := by
    rw [epsK_of_mem K hu]
    refine sign_eq_neg_one_of_invol hc3 _ ?_ ?_
    · intro h1
      have h2 := (psiK_eq_one_iff K e ⟨_, hu⟩).mp h1
      have h3 := innerOn_swap h2
      rw [hgK] at h3
      exact hout2 h3
    · obtain ⟨_, h2⟩ := mem_kerG.mp huu
      rw [← map_mul]
      exact h2
  let B : Subgroup G :=
    { carrier := {y | y ∈ X ∧ epsK K y * epsK K (g⁻¹ * y * g) = 1}
      one_mem' := ⟨X.one_mem, by simp [epsK_one]⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨X.mul_mem ha hb, ?_⟩
        have e1 : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
        rw [e1, epsK_mul K (hXN ha) (hXN hb), epsK_mul K (hXN2 a ha) (hXN2 b hb),
          mul_mul_mul_comm, ha1, hb1, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨X.inv_mem ha, ?_⟩
        have e1 : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
        rw [e1, epsK_inv K (hXN ha), epsK_inv K (hXN2 a ha), ← mul_inv, ha1, inv_one] }
  have hXB : X ≤ B := by
    rw [hXdef, Std20Frame.sec20X_eq d]
    refine sup_le (iSup₂_le fun c hc => ?_) ?_
    · intro y hy
      have hw : c⁻¹ * y * c ∈ V := mem_conjSub_iff.mp hy
      obtain ⟨n, hn⟩ := hgen _ hw
      have hy' : y = (c * v₀ * c⁻¹) ^ n := by
        rw [conj_zpow, ← hn]; group
      have hcv : c * v₀ * c⁻¹ ∈ B := by
        have hcvX : c * v₀ * c⁻¹ ∈ X :=
          conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hc (conj_mem_conjSub hv₀X)
        refine ⟨hcvX, ?_⟩
        rw [eps_conj_gen d hg hgK hc hv₀X, hε1, hε2]
        decide
      rw [hy']
      exact B.zpow_mem hcv n
    · refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · refine ⟨le_sec20X_left hy, ?_⟩
        rw [epsK_eq_one_of_mem_kerG d (K_le_kerG d hy),
          epsK_eq_one_of_mem_kerG d (K'_le_kerG d (conj_swap_K d hg hgK hy)), one_mul]
      · refine ⟨le_sec20X_right hy, ?_⟩
        rw [epsK_eq_one_of_mem_kerG d (K'_le_kerG d hy),
          epsK_eq_one_of_mem_kerG d (K_le_kerG d (conj_swap_K' d hg hgK hy)), one_mul]
  exact (hXB hx).2

end Main

theorem frame203Psi_of (hC : Frame203Cent) (hO : Frame203Outer) : Frame203Psi := by
  intro G _ _ _ K K' J S R R' W V z t d
  obtain ⟨g, hg, hgK⟩ := d.swap
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := frameX_le_N d
  have hXN2 : ∀ y ∈ X, g⁻¹ * y * g ∈ Subgroup.normalizer (K : Set G) := fun y hy =>
    conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d) hy).2
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have hc3 : Nat.card (Idx2 (Kbar K)) = 3 := card_idx2_of_equiv_q8 e
  have hf : Fintype.card (Idx2 (Kbar K)) = 3 := by rw [← Nat.card_eq_fintype_card]; exact hc3
  let eT : Idx2 (Kbar K) ≃ Fin 3 := Fintype.equivFinOfCardEq hf
  let m : Equiv.Perm (Idx2 (Kbar K)) →* Equiv.Perm (Fin 3) := eT.permCongrHom.toMonoidHom
  have hm : ∀ σ, m σ = eT.permCongr σ := fun σ => rfl
  have hminj : ∀ σ, m σ = 1 → σ = 1 := fun σ h =>
    (map_eq_one_iff _ eT.permCongrHom.injective).mp h
  let ψ : ↥X →* P3 := (m.comp (psi1 K X hXN)).prod (m.comp (psi2 K X g hXN2))
  have key : ∀ x : ↥X, ψ x = 1 ↔ (psi1 K X hXN x = 1 ∧ psi2 K X g hXN2 x = 1) := by
    intro x
    constructor
    · intro h
      have h1 : m (psi1 K X hXN x) = 1 := congrArg Prod.fst h
      have h2 : m (psi2 K X g hXN2 x) = 1 := congrArg Prod.snd h
      exact ⟨hminj _ h1, hminj _ h2⟩
    · rintro ⟨h1, h2⟩
      apply Prod.ext
      · show m (psi1 K X hXN x) = 1
        rw [h1, map_one]
      · show m (psi2 K X g hXN2 x) = 1
        rw [h2, map_one]
  have hA : oddCoreOf X ⊔ (K ⊔ K') ≤ kerG K ⊓ conjSub g (kerG K) := by
    refine sup_le (fun y hy => ?_) (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · exact ⟨oddCoreX_le_kerG d hy,
        mem_conjSub_iff.mpr (oddCoreX_le_kerG d (conj_swap_oddCore d hg hgK hy))⟩
    · exact ⟨K_le_kerG d hy, mem_conjSub_iff.mpr (K'_le_kerG d (conj_swap_K d hg hgK hy))⟩
    · exact ⟨K'_le_kerG d hy, mem_conjSub_iff.mpr (K_le_kerG d (conj_swap_K' d hg hgK hy))⟩
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  refine ⟨ψ, ?_, ?_, tw.hVX, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, key, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      have i1 : InnerOn K x := (psiK_eq_one_iff K e ⟨x, hXN x.2⟩).mp h1
      have i2 : InnerOn K (g⁻¹ * x * g) := (psiK_eq_one_iff K e ⟨_, hXN2 x x.2⟩).mp h2
      have i3 : InnerOn K' x := by
        have := innerOn_swap i2
        rwa [hgK] at this
      exact hC G K K' J S R R' W V z t d x x.2 i1 i3
    · intro h
      refine ⟨?_, ?_⟩
      · obtain ⟨_, h1⟩ := mem_kerG.mp (hA h).1
        exact h1
      · obtain ⟨_, h1⟩ := mem_kerG.mp (mem_conjSub_iff.mp (hA h).2)
        exact h1
  · intro x
    have h := epsK_prod_eq_one d hg hgK e (hO G K K' J S R R' W V z t d) x.2
    rw [epsK_of_mem K (hXN x.2), epsK_of_mem K (hXN2 x x.2)] at h
    show Equiv.Perm.sign (m (psi1 K X hXN x)) = Equiv.Perm.sign (m (psi2 K X g hXN2 x))
    rw [hm, hm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_permCongr]
    change Equiv.Perm.sign (psiK K ⟨x, hXN x.2⟩) =
      Equiv.Perm.sign (psiK K ⟨g⁻¹ * x * g, hXN2 x x.2⟩)
    have h' := eq_inv_of_mul_eq_one_left h
    rw [h', Int.units_inv_eq_self]
  · obtain ⟨v₀, hv₀V, -, hv1, hvt⟩ := exists_gen_V d
    have hv₀X : v₀ ∈ X := tw.hVX hv₀V
    refine ⟨v₀, hv₀X, hv₀V, by rw [hvt]; exact d.htKK, fun h => ?_⟩
    obtain ⟨h1, -⟩ := (key ⟨v₀, hv₀X⟩).mp h
    exact (hO G K K' J S R R' W V z t d v₀ hv₀V hv1).1
      ((psiK_eq_one_iff K e ⟨v₀, hXN hv₀X⟩).mp h1)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

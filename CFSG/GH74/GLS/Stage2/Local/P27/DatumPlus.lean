module

public import CFSG.GH74.GLS.Stage2.Local.P27.Ps4Glue
public import CFSG.GH74.GLS.Stage2.Local.Prop27Br

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Extra (z x : G) (T D₁ D₂ U : Subgroup G) (t' : G) : Prop where
  fusion : ∀ s ∈ D₂, orderOf s = 2 → ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s
  shape : (T = D₁ ⊔ D₂ ∧ Nat.card ↥D₂ = 2 * Nat.card ↥U) ∨ (D₂ = U ∧ (D₁ ⊔ D₂).relIndex T = 2)
  D₂_le_J : D₂ ≤ Jx x
  T_inf_J : T ⊓ Jx x = D₂
  compl : ∃ T₁s : Subgroup G, T₁s ≤ T ∧ IsDihedral ↥T₁s ∧ D₁ ≤ T₁s ∧ T₁s ⊓ D₂ = ⊥ ∧ D₂ ⊔ T₁s = T

@[expose] def DatumPlus (z x : G) : Prop :=
  ∃ (T D₁ D₂ U T₁ : Subgroup G) (q n : ℕ) (t' : G),
    Cfg z x T q ∧ Syl z x T D₁ D₂ U n t' ∧ Tr z x T D₁ D₂ U T₁ ∧ Extra z x T D₁ D₂ U t'

@[expose] def DatumPlusQ (z x : G) (q : ℕ) : Prop :=
  ∃ (T D₁ D₂ U T₁ : Subgroup G) (n : ℕ) (t' : G),
    Cfg z x T q ∧ Syl z x T D₁ D₂ U n t' ∧ Tr z x T D₁ D₂ U T₁ ∧ Extra z x T D₁ D₂ U t'

omit [Finite G] in
theorem DatumPlusQ.toDatumPlus {z x : G} {q : ℕ} (h : DatumPlusQ z x q) : DatumPlus z x := by
  obtain ⟨T, D₁, D₂, U, T₁, n, t', h1, h2, h3, h4⟩ := h
  exact ⟨T, D₁, D₂, U, T₁, q, n, t', h1, h2, h3, h4⟩

@[expose] def DatumPlusQL4 (z x : G) (q : ℕ) : Prop :=
  ∃ (T D₁ D₂ U T₁ : Subgroup G) (n : ℕ) (t' : G),
    Cfg z x T q ∧ Syl z x T D₁ D₂ U n t' ∧ Tr z x T D₁ D₂ U T₁ ∧ Extra z x T D₁ D₂ U t' ∧
      T = D₁ ⊔ D₂ ∧ Nat.card ↥D₂ = 2 * Nat.card ↥U

omit [Finite G] in
theorem DatumPlusQL4.toDatumPlusQ {z x : G} {q : ℕ} (h : DatumPlusQL4 z x q) : DatumPlusQ z x q := by
  obtain ⟨T, D₁, D₂, U, T₁, n, t', h1, h2, h3, h4, -, -⟩ := h
  exact ⟨T, D₁, D₂, U, T₁, n, t', h1, h2, h3, h4⟩

omit [Finite G] in
theorem DatumPlus.datum {z x : G} (h : DatumPlus z x) : Datum z x := by
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hT, -⟩ := h
  exact ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hT⟩

theorem not_mem_Jx_of_parts {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁) : x ∉ Jx x := by
  have hT₁D₁ : T₁ ≤ D₁ := htr.T₁_le
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => hsyl.comm a (hT₁D₁ ha) b hb
  have hT₁c : ∀ a ∈ T₁, ∀ a' ∈ T₁, a * a' = a' * a := by
    intro a ha a' ha'
    have := htr.T₁_cyc
    let _ := IsCyclic.commGroup (α := ↥T₁)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥T₁) ⟨a', ha'⟩)
  have hint : T₁ ⊓ D₂ = ⊥ := le_bot_iff.1 ((inf_le_inf_right D₂ hT₁D₁).trans hsyl.inter.le)
  exact P27Br.x_not_mem_Jx hcfg.x_nc.1 hcfg.T_syl (hsyl.D₁_le hsyl.x_mem) hcomm hT₁c hint
    htr.x_mem_T₁ htr.S1

theorem T₁_inf_Jx_of_parts {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁) :
    T₁ ⊓ Jx x = ⊥ :=
  P27Br.T₁_inf_Jx hcfg.x_nc.1 (not_mem_Jx_of_parts hcfg hsyl htr) htr.T₁_cyc
    (hcfg.T_syl.isPGroup.to_le (htr.T₁_le.trans hsyl.D₁_le)) htr.x_mem_T₁

theorem Extra.of_parts {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁)
    (hfus : ∀ s ∈ D₂, orderOf s = 2 → ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s)
    (hshape : (T = D₁ ⊔ D₂ ∧ Nat.card ↥D₂ = 2 * Nat.card ↥U) ∨ (D₂ = U ∧ (D₁ ⊔ D₂).relIndex T = 2))
    (hcompl : ∃ T₁s : Subgroup G, T₁s ≤ T ∧ IsDihedral ↥T₁s ∧ D₁ ≤ T₁s ∧ T₁s ⊓ D₂ = ⊥ ∧ D₂ ⊔ T₁s = T) :
    Extra z x T D₁ D₂ U t' := by
  have ht'J : t' ∈ Jx x := htr.I_le_J (hsyl.U_syl.le hsyl.t'_U)
  have hD₂J : D₂ ≤ Jx x := by
    rcases hshape with ⟨-, -⟩ | ⟨hDU, -⟩
    · intro d hd
      refine (Subgroup.closure_le (Jx x)).2 (fun s hs => ?_) (le_closure_involutions hsyl.D₂_dih hd)
      obtain ⟨c, hc, hcs⟩ := hfus s hs.1 hs.2
      rw [← hcs]
      exact P34.Jx_normalized x c hc t' ht'J
    · intro d hd
      refine htr.I_le_J (hsyl.U_syl.le ?_)
      rw [← hDU]
      exact hd
  refine ⟨hfus, hshape, hD₂J, ?_, hcompl⟩
  have hT₁D₁ : T₁ ≤ D₁ := htr.T₁_le
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => hsyl.comm a (hT₁D₁ ha) b hb
  have hT₁J : T₁ ⊓ Jx x = ⊥ := T₁_inf_Jx_of_parts hcfg hsyl htr
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_comm hcomm).1 (htr.S1 g hg)
    have haJ : a ∈ Jx x := by
      have := (Jx x).mul_mem hg.2 ((Jx x).inv_mem (hD₂J hb))
      simpa using this
    have : a ∈ T₁ ⊓ Jx x := ⟨ha, haJ⟩
    rw [hT₁J, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact hb
  · exact le_inf hsyl.D₂_le hD₂J

theorem fusion_of_I_L2 {z x : G} {U : Subgroup G} {q : ℕ} (hq : Odd q)
    (hU : IsSylowOf 2 U (Ixz z x))
    (hI : IVK.IsL2 (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) (fun r => r = q))
    {s t : G} (hs : s ∈ U) (ht : t ∈ U) (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) :
    ∃ c ∈ Ixz z x, c * t * c⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Ixz z x with hH
  let s' : ↥H := ⟨s, hU.le hs⟩
  let t' : ↥H := ⟨t, hU.le ht⟩
  have hs'2 : orderOf s' = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨F₀, iF, fF, hF, ⟨e⟩⟩ := hI
  have hFodd : Odd (Nat.card F₀) := hF ▸ hq
  have hOP := isOddPrimePower_card_of_odd hFodd
  let φ : HBar H ≃* GorensteinWalter.PSL2 F₀ := e.trans (IVK.L2.equivPSL F₀)
  have h1 := P34.orderOf_mk_eq_two H hs'2
  have h2 := P34.orderOf_mk_eq_two H ht'2
  have hinv : ∀ {a : HBar H}, orderOf a = 2 →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (φ a) := by
    intro a ha
    refine ⟨?_, ?_⟩
    · intro h
      have : a = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at ha
      omega
    · rw [← map_pow]
      have : a ^ 2 = 1 := by
        have h' := pow_orderOf_eq_one a
        rwa [ha] at h'
      rw [this, map_one]
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F₀ hOP _ _
    (hinv h2) (hinv h1)
  have hconj : IsConj (P34.mkH H t') (P34.mkH H s') := by
    refine isConj_iff.2 ⟨φ.symm g, ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.map_inv, MulEquiv.apply_symm_apply]
    exact hg
  obtain ⟨c, hc⟩ := isConj_iff.1 (P34.isConj_of_mk_isConj H ht'2 hs'2 hconj)
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem datumPlusQL4_of_l4 {z t u x : G} {S US : Subgroup G} {a q : ℕ} {Z X : Set G}
    (pic : L4Pic z t u x S US q Z X)
    (A : L4Actual S z t a Z X US) (St : L4Std S z u a Z X) : DatumPlusQL4 z x q := by
  obtain ⟨T, D₁, D₂, T₁, t', o⟩ := l4_out pic A St
  have htr : Tr z x T D₁ D₂ US T₁ :=
    tr_of_l4 o.cfg o.syl o.T_le o.T₁_le o.T₁_cyc o.x_T₁ o.T₁_idx o.T₁_card o.refl o.sepc o.D₂_cl
      o.D₂_gen o.x_D o.Ω pic.I_le_J (pLayerOf_two_perfect_P27 _) (pLayerOf_le_P27 2 _)
  have hfus := fusion_of_extremal o.cfg o.syl o.D₂_cl o.x_D o.Ω
  have hT : T = D₁ ⊔ D₂ := le_antisymm o.T_le (sup_le o.syl.D₁_le o.syl.D₂_le)
  have hcompl : ∃ T₁s : Subgroup G, T₁s ≤ T ∧ IsDihedral ↥T₁s ∧ D₁ ≤ T₁s ∧ T₁s ⊓ D₂ = ⊥ ∧ D₂ ⊔ T₁s = T :=
    ⟨D₁, by rw [hT]; exact le_sup_left, ⟨2 ^ a, o.syl.D₁_dih.2⟩, le_rfl, o.syl.inter,
      by rw [hT, sup_comm]⟩
  exact ⟨T, D₁, D₂, US, T₁, a, t', o.cfg, o.syl, htr,
    Extra.of_parts o.cfg o.syl htr hfus (Or.inl ⟨hT, o.D₂_card⟩) hcompl, hT, o.D₂_card⟩

theorem datumPlusQ_of_ps4 {z t u x : G} {S US : Subgroup G} {a q : ℕ} {Z X : Set G}
    (pic : L4Pic z t u x S US q Z X)
    (A : Ps4Actual S z t a Z X US) (St : Ps4StdC S z u a Z X) : DatumPlusQ z x q := by
  obtain ⟨T, D₁, T₁, M, n, t', T₁s, o, hc⟩ := ps4_out pic A St
  have htr : Tr z x T D₁ US US T₁ :=
    CFSG.GH74.GLS.Stage2.Local.P27Br.tr_of_sep o.cfg o.syl o.I_le_J o.T₁_le o.x_T₁ o.T₁_cyc
      o.T₁_card o.CTz o.D₂_M o.M_T o.D₂_J o.sep o.cos o.Mcomm o.M_D₁ o.M_DD
  have hIC : Ixz z x ≤ centralizer ({x} : Set G) :=
    (pLayerOf_le_P27 2 (centralizer ({x, z} : Set G))).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hfus : ∀ s ∈ US, orderOf s = 2 → ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s := by
    intro s hs hs2
    obtain ⟨c, hc, hcs⟩ := fusion_of_I_L2 o.cfg.q_odd o.syl.U_syl o.cfg.I_L2 hs o.syl.t'_U hs2
      o.syl.t'_ord
    exact ⟨c, hIC hc, hcs⟩
  exact ⟨T, D₁, US, US, T₁, n, t', o.cfg, o.syl, htr,
    Extra.of_parts o.cfg o.syl htr hfus (Or.inr ⟨rfl, o.index_eq⟩)
      ⟨T₁s, hc.le, hc.dih, hc.D₁_le, hc.inf, hc.sup⟩⟩

end CFSG.GH74.GLS.Stage2.Local.P27

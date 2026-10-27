module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Bar
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnM12
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12CardZW

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section GLevel

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {a b y x : G}

structure BarImg (h : M12Data S a b y x) (S' : Subgroup (CentralizerBar (a ^ 2 * b ^ 2)))
    (a' b' y' x' : CentralizerBar (a ^ 2 * b ^ 2)) : Prop where
  data : M12Data S' a' b' y' x'
  sylow : Sylow2In S' ⊤
  hz : a' ^ 2 * b' ^ 2 = toBar (a ^ 2 * b ^ 2) ⟨a ^ 2 * b ^ 2, z_mem_Cen _⟩
  hnu : ∀ p : NF, toBar (a ^ 2 * b ^ 2) (νC h p) = nu a' b' y' x' p
  conc : Lemma14_3Conc (CentralizerBar (a ^ 2 * b ^ 2)) (a' ^ 2 * b' ^ 2) (Rsub S' a' b')
    (R1sub a' b' y')

variable {h : M12Data S a b y x} {S' : Subgroup (CentralizerBar (a ^ 2 * b ^ 2))}
  {a' b' y' x' : CentralizerBar (a ^ 2 * b ^ 2)}

theorem BarImg.summary (hb : BarImg h S' a' b' y' x') :
    ∃ A : Subgroup (CentralizerBar (a ^ 2 * b ^ 2)),
      LBar (a ^ 2 * b ^ 2) = Rsub S' a' b' ⊔ A ∧ WBar (a ^ 2 * b ^ 2) = Rsub S' a' b' ∧
      (∀ g ∈ Rsub S' a' b' ⊔ A, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ Rsub S' a' b') := by
  have hcen : ∀ g : CentralizerBar (a ^ 2 * b ^ 2),
      g * (a' ^ 2 * b' ^ 2) = (a' ^ 2 * b' ^ 2) * g := by
    intro g; rw [hb.hz]; exact zBar_central _ g
  have hRn : (Rsub S' a' b').Normal := normal_of_conc hcen hb.conc.R_normal
  have cfg := barCfg_of_conc hb.data hb.sylow hcen hb.conc
  have hO : pPrimeCore 2 (CentralizerBar (a ^ 2 * b ^ 2)) = ⊥ := pPrimeCore_quotient_eq_bot _
  obtain ⟨A, -, hOres, hFst, -, -, hpcore, htop, h2⟩ := cfg.summary hO
  have hI : oPrimePResidual 2 (CentralizerBar (a ^ 2 * b ^ 2)) ≤ InnerE (a ^ 2 * b ^ 2) := by
    rw [innerE_eq_top_of_fstar_solvable _ (fstar_solvable_of_pcore hFst hpcore)]
    exact le_top
  refine ⟨A, ?_, ?_, h2⟩
  · rw [LBar_eq_oResidual _ htop hI, hOres]
  · rw [WBar_eq, hpcore]

theorem RC_eq (hS : Sylow2In S ⊤) (hb : BarImg h S' a' b' y' x') :
    RC S (a ^ 2 * b ^ 2) = nfSub h pR closed_pR := by
  obtain ⟨A, hL, -, h2⟩ := hb.summary
  have hR' : Rsub S' a' b' = nfSub hb.data pR closed_pR := R_eq hb.data
  have hkey : ∀ p : NF, ∃ k : ℕ, (νC h p) ^ (2 ^ k) = 1 ∧
      (nu a' b' y' x' p) ^ (2 ^ k) = 1 := fun p => by
    obtain ⟨k, hk⟩ := hS.2.1 ⟨nu a b y x p, nu_mem h p⟩
    have hk1 : (νC h p) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
      exact this
    exact ⟨k, hk1, by rw [← hb.hnu, ← map_pow, hk1, map_one]⟩
  ext s
  constructor
  · rintro ⟨hsS, hsL⟩
    obtain ⟨p, rfl⟩ := exists_nf h hsS
    obtain ⟨k, hk1, hk2⟩ := hkey p
    have hmemL : toBar (a ^ 2 * b ^ 2) (νC h p) ∈ LBar (a ^ 2 * b ^ 2) :=
      (mem_LC_iff_of_pElt (a ^ 2 * b ^ 2) (νC h p) hk1).1 hsL
    rw [hL, hb.hnu] at hmemL
    have := h2 _ hmemL k hk2
    rw [hR'] at this
    exact (nu_mem_nfSub h closed_pR p).2 ((nu_mem_nfSub hb.data closed_pR p).1 this)
  · intro hs
    obtain ⟨p, hp, rfl⟩ := hs
    refine ⟨nu_mem h p, ?_⟩
    obtain ⟨k, hk1, hk2⟩ := hkey p
    refine (mem_LC_iff_of_pElt (a ^ 2 * b ^ 2) (νC h p) hk1).2 ?_
    rw [hL, hb.hnu]
    have : nu a' b' y' x' p ∈ Rsub S' a' b' := by
      rw [hR']; exact (nu_mem_nfSub hb.data closed_pR p).2 hp
    exact mem_sup_left this

theorem card_pU : Nat.card {p : NF // pU p} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide +kernel

theorem small_class_pU : ∀ p : NF, p ≠ (0, 0, 0, 0) → nfMul p p = (0, 0, 0, 0) →
    (Finset.univ.image (fun q : NF => nfMul (nfMul q p) (nfInv q))).card ≤ 3 → pU p := by
  decide +kernel

omit [Finite G] in
theorem pU_isFour (h : M12Data S a b y x) : IVK.IsFourSubgroup (nfSub h pU closed_pU) := by
  refine ⟨?_, ?_⟩
  · refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, p, hp, rfl⟩ ⟨_, q, hq, rfl⟩
      apply Subtype.ext
      show nu a b y x p * nu a b y x q = nu a b y x q * nu a b y x p
      rw [nu_mul h, nu_mul h]
      have : ∀ p q : NF, pU p → pU q → nfMul p q = nfMul q p := by decide +kernel
      rw [this p q hp hq]
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, p, hp, rfl⟩
      apply Subtype.ext
      show nu a b y x p ^ 2 = 1
      rw [pow_two, nu_mul h, pU_sq_one p hp, nu_zero]
  · rw [card_nfSub h, card_pU]

theorem four_unique (h : M12Data S a b y x) (U' : Subgroup G) (hU'S : U' ≤ S)
    (h4 : IVK.IsFourSubgroup U') (hn : ∀ s ∈ S, ∀ u ∈ U', s * u * s⁻¹ ∈ U') :
    U' = nfSub h pU closed_pU := by
  classical
  have hcard : Nat.card {p : NF // nu a b y x p ∈ U'} = 4 := by
    rw [← h4.2]
    refine Nat.card_congr (Equiv.ofBijective
      (fun p : {p : NF // nu a b y x p ∈ U'} => (⟨nu a b y x p.1, p.2⟩ : ↥U')) ⟨?_, ?_⟩)
    · intro p q hpq
      exact Subtype.ext (nu_injective h (congrArg Subtype.val hpq))
    · rintro ⟨g, hg⟩
      obtain ⟨p, rfl⟩ := exists_nf h (hU'S hg)
      exact ⟨⟨p, hg⟩, rfl⟩
  set Ufin : Finset NF := Finset.univ.filter (fun p : NF => nu a b y x p ∈ U') with hUfin
  have hUcard : Ufin.card = 4 := by
    rw [hUfin, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]; exact hcard
  have h0 : (0, 0, 0, 0) ∈ Ufin := by
    rw [hUfin, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [nu_zero]; exact U'.one_mem⟩
  have hkey : ∀ p ∈ Ufin, pU p := by
    intro p hp
    by_cases hp0 : p = (0, 0, 0, 0)
    · subst hp0; decide +kernel
    have hpU' : nu a b y x p ∈ U' := (Finset.mem_filter.1 hp).2
    have := h4.1
    apply small_class_pU p hp0
    · have h2 : nu a b y x p * nu a b y x p = 1 := by
        have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U') (nu a b y x p) hpU'
        rwa [pow_two] at this
      rw [nu_mul h] at h2
      exact nu_injective h (h2.trans nu_zero.symm)
    · have hsub : (Finset.univ.image (fun q : NF => nfMul (nfMul q p) (nfInv q))) ⊆ Ufin.erase (0, 0, 0, 0) := by
        intro r hr
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
        have hnu : nu a b y x (nfMul (nfMul q p) (nfInv q)) =
            nu a b y x q * nu a b y x p * (nu a b y x q)⁻¹ := by
          rw [← nu_mul h, ← nu_mul h, nu_inv h]
        refine Finset.mem_erase.2 ⟨?_, ?_⟩
        · intro e
          have : nu a b y x p = 1 := by
            have h1 : nu a b y x (nfMul (nfMul q p) (nfInv q)) = 1 := by rw [e, nu_zero]
            rw [hnu] at h1
            have := mul_inv_eq_one.1 h1
            simpa using this
          exact hp0 (nu_injective h (this.trans nu_zero.symm))
        · rw [hUfin, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hnu]
          exact hn _ (nu_mem h q) _ hpU'
      calc _ ≤ (Ufin.erase (0, 0, 0, 0)).card := Finset.card_le_card hsub
        _ = 3 := by rw [Finset.card_erase_of_mem h0, hUcard]
  have hle : U' ≤ nfSub h pU closed_pU := by
    intro u hu
    obtain ⟨p, rfl⟩ := exists_nf h (hU'S hu)
    have hp : p ∈ Ufin := by rw [hUfin, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu⟩
    exact ⟨p, hkey p hp, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_nfSub h, card_pU, h4.2])

theorem card_mulAut_le_six {U : Type*} [Group U] [Finite U] (hc : Nat.card U = 4) :
    Nat.card (MulAut U) ≤ 6 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hT : Fintype.card {u : U // u ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc]
  let φ : MulAut U → Equiv.Perm {u : U // u ≠ 1} := fun e =>
    Equiv.subtypeEquiv e.toEquiv (fun u => by simp)
  have hφ : Function.Injective φ := by
    intro e e' hee
    ext u
    by_cases hu : u = 1
    · simp [hu]
    · have := congrArg (fun σ => ((σ ⟨u, hu⟩ : {u : U // u ≠ 1}) : U)) hee
      simpa [φ] using this
  calc Nat.card (MulAut U) ≤ Nat.card (Equiv.Perm {u : U // u ≠ 1}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hT]; rfl

theorem autOrd_six {x' : G} {T V : Subgroup G} (o : Out13 G x' T V S a b y) :
    AutOrd (⊤ : Subgroup G) (nfSub o.data pU closed_pU) = 6 := by
  have h := o.data
  set U := nfSub h pU closed_pU with hU
  have hUc : Nat.card U = 4 := by rw [hU, card_nfSub h, card_pU]
  let α := U.normalizerMonoidHom
  have hcard : Nat.card α.range = AutOrd (⊤ : Subgroup G) U := by
    unfold AutOrd
    rw [inf_top_eq, inf_top_eq, ← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  have happ : ∀ (g : ↥(normalizer (U : Set G))) (u : ↥U), ((α g u : ↥U) : G) = g * u * (g : G)⁻¹ :=
    fun g u => rfl
  have hnormU : ∀ g : G, (∀ u ∈ U, g * u * g⁻¹ ∈ U) → (∀ u ∈ U, g⁻¹ * u * g ∈ U) →
      g ∈ normalizer (U : Set G) := by
    intro g h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact h1 u
    · intro hu
      have := h2 _ hu
      have e : u = g⁻¹ * (g * u * g⁻¹) * g := by group
      rw [e]; exact this
  have hyN : y ∈ normalizer (U : Set G) := by
    refine hnormU y (fun u hu => conj_mem_nfSub h closed_pU conj_pU y (y_mem h) u hu) (fun u hu => ?_)
    have := conj_mem_nfSub h closed_pU conj_pU y⁻¹ (S.inv_mem (y_mem h)) u hu
    simpa using this
  have hy2 : orderOf (α ⟨y, hyN⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← map_mul]
      have : (⟨y, hyN⟩ * ⟨y, hyN⟩ : ↥(normalizer (U : Set G))) = 1 := Subtype.ext h.hy
      rw [this, map_one]
    · intro e
      have hu : nu a b y x' (2, 0, 0, 0) ∈ U := (nu_mem_nfSub h closed_pU _).2 (by decide +kernel)
      have h1 := congrArg (fun σ : MulAut ↥U => ((σ ⟨_, hu⟩ : ↥U) : G)) e
      simp only [happ] at h1
      have hy' : nu a b y x' yNF = y := by simp [nu, yNF]
      have e2 : nu a b y x' yNF * nu a b y x' (2, 0, 0, 0) * (nu a b y x' yNF)⁻¹ =
          nu a b y x' (nfMul (nfMul yNF (2, 0, 0, 0)) (nfInv yNF)) := by
        rw [← nu_mul h, ← nu_mul h, nu_inv h]
      rw [U_swap_a, hy'] at e2
      have e3 : nu a b y x' (0, 2, 0, 0) = nu a b y x' (2, 0, 0, 0) := by
        rw [← e2]; exact h1
      have := nu_injective h e3
      revert this; decide +kernel
  obtain ⟨f, hf3, hfH, -, v, hv, hfv⟩ := o.f3
  have hvU : v ∈ U := by rw [hU, ← U_eq h, ← o.V_eq]; exact hv
  have hfinv : f⁻¹ ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hfH
  have hfN : f ∈ normalizer (U : Set G) :=
    hnormU f (fun u hu => f_norm_U o hfH hu)
      (fun u hu => by simpa using f_norm_U o hfinv hu)
  have hf3' : orderOf (α ⟨f, hfN⟩) ∣ 3 ^ (Classical.choose hf3) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨f, hfN⟩ : ↥(normalizer (U : Set G))) ^ (3 ^ (Classical.choose hf3)) = 1 :=
      Subtype.ext (by simpa using Classical.choose_spec hf3)
    rw [this, map_one]
  have hf1 : α ⟨f, hfN⟩ ≠ 1 := by
    intro e
    have h1 := congrArg (fun σ : MulAut ↥U => ((σ ⟨v, hvU⟩ : ↥U) : G)) e
    simp only [happ] at h1
    exact hfv h1
  have hrangeF : α ⟨f, hfN⟩ ∈ α.range := ⟨_, rfl⟩
  have hrangeY : α ⟨y, hyN⟩ ∈ α.range := ⟨_, rfl⟩
  have h3 : 3 ∣ Nat.card α.range := by
    have hdvd := Subgroup.orderOf_dvd_natCard α.range hrangeF
    obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hf3'
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hf1 (orderOf_eq_one_iff.1 (by simpa using hord))
    exact (dvd_pow_self 3 hj0).trans (hord ▸ hdvd)
  have h2 : 2 ∣ Nat.card α.range := hy2 ▸ Subgroup.orderOf_dvd_natCard α.range hrangeY
  have h6 : 6 ∣ Nat.card α.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hle : Nat.card α.range ≤ 6 :=
    (Subgroup.card_le_card_group α.range).trans (card_mulAut_le_six hUc)
  have hpos : 0 < Nat.card α.range := Nat.card_pos
  rw [← hcard]
  obtain ⟨k, hk⟩ := h6
  omega

theorem R_le_WC (hb : BarImg h S' a' b' y' x') : nfSub h pR closed_pR ≤ WC (a ^ 2 * b ^ 2) := by
  obtain ⟨A, -, hW, -⟩ := hb.summary
  rintro _ ⟨p, hp, rfl⟩
  refine (mem_WC_iff (a ^ 2 * b ^ 2) (νC h p)).2 ?_
  have hR' : Rsub S' a' b' = nfSub hb.data pR closed_pR := R_eq hb.data
  rw [hb.hnu, hW, hR']
  exact (nu_mem_nfSub hb.data closed_pR p).2 hp

theorem stage1Base_of (hS : Sylow2In S ⊤) (hb : BarImg h S' a' b' y' x') :
    Stage1Base G (a ^ 2 * b ^ 2) S := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hwc hord
    obtain ⟨p, rfl⟩ := exists_nf h hw
    have hcomm : ∀ q : NF, pR q → nfMul p q = nfMul q p := by
      intro q _
      have := hwc (nu a b y x q) (nu_mem h q)
      rw [nu_mul h, nu_mul h] at this
      exact (nu_injective h this).symm
    rcases centralizer_R p hcomm with rfl | rfl
    · exfalso
      rw [nu_zero, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · exact (zG_eq (y := y) (x := x)).symm
  · intro _
    refine ⟨nu a b y x ((1, 0, 0, 1) : NF), nu_mem h _, ?_, ?_⟩
    · rw [RC_eq hS hb]
      intro hm
      have := (nu_mem_nfSub h closed_pR _).1 hm
      revert this; decide +kernel
    · apply orderOf_eq_prime
      · rw [pow_two, nu_mul h]
        have : nfMul ((1, 0, 0, 1) : NF) (1, 0, 0, 1) = (0, 0, 0, 0) := by decide +kernel
        rw [this, nu_zero]
      · intro e
        have := nu_injective h (e.trans nu_zero.symm)
        revert this; decide +kernel
  · intro U hUS h4 hn
    rw [four_unique h U hUS h4 hn]
    calc nfSub h pU closed_pU ≤ nfSub h pR closed_pR := nfSub_le_nfSub h _ _ pR_of_pU
      _ = RC S (a ^ 2 * b ^ 2) := (RC_eq hS hb).symm
      _ ≤ LC (a ^ 2 * b ^ 2) := inf_le_right

theorem fourGroup_field {x' : G} {T V : Subgroup G} {xb : CentralizerBar (a ^ 2 * b ^ 2)}
    (o : Out13 G x' T V S a b y)
    (hb : BarImg o.data S' a' b' y' xb) :
    ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
      a ^ 2 * b ^ 2 ∈ U ∧ U ≤ WC (a ^ 2 * b ^ 2) ∧
      (∀ U' : Subgroup G, U' ≤ S → IVK.IsFourSubgroup U' →
        (∀ s ∈ S, ∀ u ∈ U', s * u * s⁻¹ ∈ U') → U' = U) ∧
      AutOrd (⊤ : Subgroup G) U = 6 := by
  have h := o.data
  refine ⟨nfSub h pU closed_pU, nfSub_le_S h closed_pU, pU_isFour h,
    conj_mem_nfSub h closed_pU conj_pU, ?_, ?_, fun U' hU'S h4 hn => four_unique h U' hU'S h4 hn,
    autOrd_six o⟩
  · rw [zG_eq (y := y) (x := x')]
    exact (nu_mem_nfSub h closed_pU _).2 (by decide +kernel)
  · exact (nfSub_le_nfSub h _ _ pR_of_pU).trans (R_le_WC hb)

theorem fuseOut_field {x' : G} {T V : Subgroup G} {xb : CentralizerBar (a ^ 2 * b ^ 2)}
    (o : Out13 G x' T V S a b y)
    (hb : BarImg o.data S' a' b' y' xb)
    (hfus : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
      IsConj (a ^ 2 * b ^ 2) (nu a b y x' (i, j, 0, 1))) :
    ∃ t ∈ S, t ∉ WC (a ^ 2 * b ^ 2) ∧ orderOf t = 2 ∧ IsConj (a ^ 2 * b ^ 2) t := by
  have h := o.data
  refine ⟨nu a b y x' ((1, 0, 0, 1) : NF), nu_mem h _, ?_, ?_, hfus 1 0 (by decide)⟩
  · intro hm
    obtain ⟨A, -, hW, -⟩ := hb.summary
    have h1 := (mem_WC_iff (a ^ 2 * b ^ 2) (νC h ((1, 0, 0, 1) : NF))).1 hm
    have hR' : Rsub S' a' b' = nfSub hb.data pR closed_pR := R_eq hb.data
    rw [hb.hnu, hW, hR'] at h1
    have h2 := (nu_mem_nfSub hb.data closed_pR _).1 h1
    revert h2; decide +kernel
  · apply orderOf_eq_prime
    · rw [pow_two, nu_mul h]
      have : nfMul ((1, 0, 0, 1) : NF) (1, 0, 0, 1) = (0, 0, 0, 0) := by decide +kernel
      rw [this, nu_zero]
    · intro e
      have := nu_injective h (e.trans nu_zero.symm)
      revert this; decide +kernel

theorem exists_conj_into_S (hS : Sylow2In S ⊤) {u : G} {k : ℕ} (hu : u ^ (2 ^ k) = 1) :
    ∃ g : G, g * u * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let S' : Sylow 2 G := hS.2.1.toSylow hidx
  have hP : IsPGroup 2 (zpowers u) := by
    obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hu)
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_zpowers, hord]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S'
  refine ⟨g, ?_⟩
  have hmem : g * u * g⁻¹ ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ (hQ (Subgroup.mem_zpowers u))
  rw [hg] at hmem
  exact hmem

theorem nf_inv_cases : ∀ p : NF, nfMul p p = (0, 0, 0, 0) → p ≠ (0, 0, 0, 0) →
    pU p ∨ ¬ pQ0 p ∨ (pQ0 p ∧ p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0) ∨
      (p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ ¬ (p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0)) := by
  decide +kernel

theorem twoClasses_field {x' : G} {T V : Subgroup G} (o : Out13 G x' T V S a b y)
    (hfus : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
      IsConj (a ^ 2 * b ^ 2) (nu a b y x' (i, j, 0, 1))) :
    ∃ x : G, orderOf x = 2 ∧ ¬ IsConj (a ^ 2 * b ^ 2) x ∧
      ∀ u : G, orderOf u = 2 → IsConj (a ^ 2 * b ^ 2) u ∨ IsConj x u := by
  have h := o.data
  have hS : Sylow2In S ⊤ := o.sylow
  refine ⟨x', orderOf_eq_prime (by rw [pow_two]; exact o.out12.x_sq) o.out12.x_ne, ?_, ?_⟩
  · rintro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    exact x_not_conj_z o g hg
  · intro u hu
    have hu2 : u ^ (2 ^ 1) = 1 := by rw [pow_one, ← hu]; exact pow_orderOf_eq_one u
    obtain ⟨g, hgS⟩ := exists_conj_into_S hS hu2
    obtain ⟨p, hp⟩ := exists_nf h hgS
    have hsq : nfMul p p = (0, 0, 0, 0) := by
      have : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
        have : u * u = 1 := by rw [← pow_two]; rw [← hu]; exact pow_orderOf_eq_one u
        calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
          _ = 1 := by rw [this]; group
      rw [hp, nu_mul h] at this
      exact nu_injective h (this.trans nu_zero.symm)
    have hne : p ≠ (0, 0, 0, 0) := by
      intro e
      rw [e, nu_zero] at hp
      have : u = 1 := by
        have h1 : g * u * g⁻¹ = 1 := hp
        simpa using h1
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    have hup : IsConj u (nu a b y x' p) := isConj_iff.2 ⟨g, hp⟩
    rcases nf_inv_cases p hsq hne with hU | hk | ⟨-, hk0, hl1, hi, hj⟩ | ⟨hk0, hl1, hij⟩
    ·
      left
      have hmemU : nu a b y x' p ∈ nfSub h pU closed_pU := (nu_mem_nfSub h closed_pU p).2 hU
      obtain ⟨f, hf3, hfN, -, v, hv, hfv⟩ := o.f3
      have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
      obtain ⟨n, -, hn⟩ := exists_conj_U_to_z o hf3 hfN hvU hfv hmemU (by
        intro e; exact hne (nu_injective h (e.trans nu_zero.symm)))
      exact (isConj_iff.2 ⟨n, hn⟩).symm.trans hup.symm
    ·
      right
      have hvP : nu a b y x' p ∉ nfSub h pQ0 closed_pQ0 := fun hm =>
        hk ((nu_mem_nfSub h closed_pQ0 p).1 hm)
      obtain ⟨c, hc⟩ := involutions_conj_x o (nu_mem h p) (by rw [nu_mul h, hsq, nu_zero]) hvP
      exact (isConj_iff.2 ⟨c, hc⟩).trans hup.symm
    ·
      right
      have key : ∀ p : NF, p.2.2.1 = 0 → p.2.2.2 = 1 → p.1.val % 2 = 0 → p.2.1.val % 2 = 0 →
          ∃ q : NF, nfMul (nfMul q xNF) (nfInv q) = p := by decide +kernel
      obtain ⟨q, hq⟩ := key p hk0 hl1 hi hj
      have hx' : nu a b y x' xNF = x' := by simp [nu, xNF]
      have e1 : nu a b y x' q * x' * (nu a b y x' q)⁻¹ = nu a b y x' p := by
        have h2 : nu a b y x' q * nu a b y x' xNF * (nu a b y x' q)⁻¹ =
            nu a b y x' (nfMul (nfMul q xNF) (nfInv q)) := by
          rw [← nu_mul h, ← nu_mul h, nu_inv h]
        rw [hx', hq] at h2
        exact h2
      exact (isConj_iff.2 ⟨nu a b y x' q, e1⟩).trans hup.symm
    ·
      left
      obtain ⟨i, j, k, l⟩ := p
      simp only at hk0 hl1
      subst hk0; subst hl1
      exact (hfus i j hij).trans hup.symm

theorem WC_iff_pR {x' : G} {T V : Subgroup G} {xb : CentralizerBar (a ^ 2 * b ^ 2)}
    (o : Out13 G x' T V S a b y) (hb : BarImg o.data S' a' b' y' xb) (p : NF) :
    nu a b y x' p ∈ WC (a ^ 2 * b ^ 2) ↔ pR p := by
  have h := o.data
  constructor
  · intro hm
    obtain ⟨A, -, hW, -⟩ := hb.summary
    have h1 := (mem_WC_iff (a ^ 2 * b ^ 2) (νC h p)).1 hm
    have hR' : Rsub S' a' b' = nfSub hb.data pR closed_pR := R_eq hb.data
    rw [hb.hnu, hW, hR'] at h1
    exact (nu_mem_nfSub hb.data closed_pR _).1 h1
  · intro hp
    exact R_le_WC hb ((nu_mem_nfSub h closed_pR p).2 hp)

theorem stage1M12_of_barImg {x' : G} {T V : Subgroup G} {xb : CentralizerBar (a ^ 2 * b ^ 2)}
    (o : Out13 G x' T V S a b y) (hb : BarImg o.data S' a' b' y' xb)
    (hfus : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
      IsConj (a ^ 2 * b ^ 2) (nu a b y x' (i, j, 0, 1))) :
    Stage1M12 G (a ^ 2 * b ^ 2) S := by
  obtain ⟨hW, hL, hq⟩ := stage1M12_Cfields hb.data hb.sylow hb.hz hb.conc
  exact ⟨stage1Base_of o.sylow hb, hW, hL, hq, twoClasses_field o hfus, fourGroup_field o hb,
    fuseOut_field o hb hfus, cardZW_field o (WC_iff_pR o hb) hfus⟩

theorem BarImg.solvable (hb : BarImg h S' a' b' y' x') :
    Group.IsSolvable (CentralizerBar (a ^ 2 * b ^ 2)) := by
  have hcen : ∀ g : CentralizerBar (a ^ 2 * b ^ 2),
      g * (a' ^ 2 * b' ^ 2) = (a' ^ 2 * b' ^ 2) * g := by
    intro g; rw [hb.hz]; exact zBar_central _ g
  have hRn : (Rsub S' a' b').Normal := normal_of_conc hcen hb.conc.R_normal
  exact (barCfg_of_conc hb.data hb.sylow hcen hb.conc).isSolvable

theorem not_isPCompIn_of_solvable (z : G) (hs : Group.IsSolvable (CentralizerBar z))
    (K : Subgroup G) : ¬ IsPCompIn 2 (Cen z) K := by
  rintro ⟨-, K', ⟨⟨hperf, -, a, b, hab⟩, -⟩, -, -, -⟩
  have hnt : Nontrivial ↥K' := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hab (Subsingleton.elim _ _)
  have : Group.IsPerfect ↥K' := hperf
  exact Group.IsPerfect.not_isSolvable K' inferInstance

end GLevel

end CFSG.GH74.GLS.Stage1.Thm6.Prod

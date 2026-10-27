module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSCheck
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSGrp
public import CFSG.Sporadic.SuzOddCore.CTIFirst

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.SuzCS

open CFSG CFSG.LocalCores CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Certificates Subgroup

theorem map_rho0_eq_suzD
    (B : Subgroup (invE 0)) (hB : IsComponent B) : B.map rho0 = suzD := by
  set ρ' : invE 0 →* rho0.range := rho0.rangeRestrict
  have hsurj : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective rho0
  have hker : Group.IsSolvable ρ'.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 rho0.ker := IsPGroup.of_card (n := 2) (by rw [card_ker_rho0]; norm_num)
    have : Group.IsNilpotent rho0.ker := hp.isNilpotent
    infer_instance
  have e : suzD.subgroupOf rho0.range ≃* suzD := Subgroup.subgroupOfEquivOfLe suzD_le
  have hs : IsSimpleGroup (suzD.subgroupOf rho0.range) := by
    have := suzD_simple
    exact e.isSimpleGroup
  have h := map_eq_of_component ρ' hsurj hker _ suzD_index hs hB
  ext d
  constructor
  · rintro ⟨b, hb, rfl⟩
    have : ρ' b ∈ B.map ρ' := ⟨b, hb, rfl⟩
    rw [h, Subgroup.mem_subgroupOf] at this
    exact this
  · intro hd
    have : (⟨d, suzD_le hd⟩ : rho0.range) ∈ suzD.subgroupOf rho0.range := hd
    rw [← h] at this
    obtain ⟨b, hb, hbd⟩ := this
    exact ⟨b, hb, congrArg Subtype.val hbd⟩

theorem normal_of_component_zero
    (B : Subgroup (invE 0)) (hB : IsComponent B) : B.Normal := by
  refine normal_of_component hB Nat.prime_seven ?_ ?_
  · rw [CTI_Suz_first_involution_local_component_simple_quotient_order B hB]
    norm_num
  · rw [card_invE (i := 0) (by norm_num)]
    decide

@[expose] noncomputable def betaPerm : Equiv.Perm (Fin 1782) :=
  (betaWord.map fun l => invInnerGen 0 (l - 1)).prod

theorem betaOK_parts :
    (betaWord.all fun h => decide (1 ≤ h ∧ h ≤ (invInnerGenArrs 0).size)) = true ∧
    (fixList 0).all (fun x => betaArr[x]! == x) = true ∧
    eqA 1782 betaArr (idA 1782) = false ∧ eqA 1782 betaArr (tArr 0) = false ∧
    allBelow (invInnerGenArrs 0).size (fun k => betaConjOK (invInnerGenArrs 0)[k]!) = true ∧
    eqA 1782 (compA 1782 (invInnerGenArrs 0)[4]! betaArr)
      (compA 1782 betaArr (invInnerGenArrs 0)[4]!) = false := by
  have h := suzCS_zero_check.1
  simp only [betaOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_betaPerm :
    Rep 1782 betaArr betaPerm :=
  (rep_innerWordArr (i := 0) (by norm_num) betaWord betaOK_parts.1).1

theorem betaPerm_mem :
    betaPerm ∈ invE 0 :=
  (rep_innerWordArr (i := 0) (by norm_num) betaWord betaOK_parts.1).2

theorem betaPerm_fix
    {x : Fin 1782} (hx : (x : ℕ) ∈ fixList 0) : betaPerm x = x := by
  have h := betaOK_parts.2.1
  rw [List.all_eq_true] at h
  have h1 := h _ hx
  rw [beq_iff_eq, rep_betaPerm x] at h1
  exact Fin.ext h1

theorem betaPerm_ne_one :
    betaPerm ≠ 1 := by
  intro h
  have := (eqA_iff rep_betaPerm rep_idA).2 h
  rw [betaOK_parts.2.2.1] at this
  exact Bool.false_ne_true this

theorem betaPerm_ne_t :
    betaPerm ≠ suzInv 0 := by
  intro h
  have := (eqA_iff rep_betaPerm (rep_suzInv (i := 0) (by norm_num))).2 h
  rw [betaOK_parts.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem invInnerGenArrs_size0' : (invInnerGenArrs 0).size = 22 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem e4_conj_beta :
    invInnerGen 0 4 * betaPerm = suzInv 0 * betaPerm * invInnerGen 0 4 := by
  have h4 : (4 : ℕ) < (invInnerGenArrs 0).size := by rw [invInnerGenArrs_size0']; norm_num
  have hrep := rep_invInnerGen (i := 0) (by norm_num) h4
  have hc := betaOK_parts.2.2.2.2.1
  rw [allBelow_eq_true] at hc
  have hc4 := hc 4 h4
  simp only [betaConjOK, Bool.or_eq_true] at hc4
  rcases hc4 with h | h
  · exfalso
    have h6 := betaOK_parts.2.2.2.2.2
    rw [h] at h6
    exact absurd h6 (by decide)
  · exact (eqA_iff (rep_compA hrep rep_betaPerm)
      (rep_compA (rep_compA (rep_suzInv (i := 0) (by norm_num)) rep_betaPerm) hrep)).1 h

theorem t0_mem_invE :
    suzInv 0 ∈ invE 0 :=
  suzInv_mem_invE (i := 0) (by norm_num)
    (CTUC_Suz_four_exact_involution_centralizers.2.2.2.2.2.1)

theorem comm_t0
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 0) : g * suzInv 0 = suzInv 0 * g := by
  rw [invE_eq_centM (i := 0) (by norm_num)] at hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 hg.1)

theorem mem_ker_rho0_of_fix
    (g : invE 0)
    (hg : ∀ x : Fin 1782, (x : ℕ) ∈ fixList 0 → (g : Equiv.Perm (Fin 1782)) x = x) :
    g ∈ rho0.ker := by
  rw [MonoidHom.mem_ker]
  exact ((fixList_points hm0).restrHom_eq_one_iff (invE 0)
    (invE_preserves (i := 0) (by norm_num)) g).2 hg

theorem tb_ne_one :
    suzInv 0 * betaPerm ≠ 1 := by
  intro h
  apply betaPerm_ne_t
  rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (suzInv_sq (i := 0) (by norm_num))]

theorem tb_ne_t :
    suzInv 0 * betaPerm ≠ suzInv 0 := by
  intro h
  apply betaPerm_ne_one
  calc betaPerm = (suzInv 0)⁻¹ * (suzInv 0 * betaPerm) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem tb_ne_b :
    suzInv 0 * betaPerm ≠ betaPerm := by
  intro h
  apply suzInv_ne_one (i := 0) (by norm_num)
  calc suzInv 0 = suzInv 0 * betaPerm * betaPerm⁻¹ := by group
    _ = 1 := by rw [h, mul_inv_cancel]

theorem mem_ker_rho0
    {g : invE 0} (hg : g ∈ rho0.ker) :
    (g : Equiv.Perm (Fin 1782)) = 1 ∨ (g : Equiv.Perm (Fin 1782)) = suzInv 0 ∨
      (g : Equiv.Perm (Fin 1782)) = betaPerm ∨
      (g : Equiv.Perm (Fin 1782)) = suzInv 0 * betaPerm := by
  have ht : (⟨suzInv 0, t0_mem_invE⟩ : invE 0) ∈ rho0.ker :=
    suzInv_mem_ker (i := 0) (by norm_num) hm0 t0_mem_invE
  have hb : (⟨betaPerm, betaPerm_mem⟩ : invE 0) ∈ rho0.ker :=
    mem_ker_rho0_of_fix _ fun x hx => betaPerm_fix hx
  have htb := rho0.ker.mul_mem ht hb
  have ht1 : suzInv 0 ≠ 1 := suzInv_ne_one (i := 0) (by norm_num)
  have h := eq_of_mem_of_card_eq_four card_ker_rho0 rho0.ker.one_mem ht hb htb
    (fun h => ht1 (congrArg Subtype.val h).symm)
    (fun h => betaPerm_ne_one (congrArg Subtype.val h).symm)
    (fun h => tb_ne_one (congrArg Subtype.val h).symm)
    (fun h => betaPerm_ne_t (congrArg Subtype.val h).symm)
    (fun h => tb_ne_t (congrArg Subtype.val h).symm)
    (fun h => tb_ne_b (congrArg Subtype.val h).symm)
    hg
  rcases h with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem conj_beta
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 0) :
    g * betaPerm * g⁻¹ = betaPerm ∨ g * betaPerm * g⁻¹ = suzInv 0 * betaPerm := by
  have hk : (⟨g, hg⟩ : invE 0) * ⟨betaPerm, betaPerm_mem⟩ * (⟨g, hg⟩ : invE 0)⁻¹ ∈ rho0.ker :=
    (rho0.normal_ker).conj_mem _ (mem_ker_rho0_of_fix _ fun x hx => betaPerm_fix hx) _
  rcases mem_ker_rho0 hk with h | h | h | h <;>
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  · exfalso
    apply betaPerm_ne_one
    calc betaPerm = g⁻¹ * (g * betaPerm * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply betaPerm_ne_t
    calc betaPerm = g⁻¹ * (g * betaPerm * g⁻¹) * g := by group
      _ = g⁻¹ * (suzInv 0 * g) := by rw [h, mul_assoc]
      _ = suzInv 0 := by rw [← comm_t0 hg]; group
  · exact Or.inl h
  · exact Or.inr h

theorem card_centralizer_beta :
    Nat.card (Subgroup.centralizer {betaPerm} ⊓ invE 0 : Subgroup (Equiv.Perm (Fin 1782))) =
      80640 := by
  set C : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.centralizer {betaPerm} ⊓ invE 0 with hC
  have h4 : (4 : ℕ) < (invInnerGenArrs 0).size := by rw [invInnerGenArrs_size0']; norm_num
  have hE := invInnerGen_mem (i := 0) (by norm_num) h4
  have key : ∀ y : invE 0, y ∈ C.subgroupOf (invE 0) ↔
      (y : Equiv.Perm (Fin 1782)) * betaPerm * (y : Equiv.Perm (Fin 1782))⁻¹ = betaPerm := by
    intro y
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h, -⟩
      rw [h, mul_inv_cancel_right]
    · intro h
      refine ⟨?_, y.2⟩
      calc (y : Equiv.Perm (Fin 1782)) * betaPerm =
          ((y : Equiv.Perm (Fin 1782)) * betaPerm * (y : Equiv.Perm (Fin 1782))⁻¹) * y := by
            group
        _ = betaPerm * y := by rw [h]
  have he : invInnerGen 0 4 * betaPerm * (invInnerGen 0 4)⁻¹ = suzInv 0 * betaPerm := by
    rw [e4_conj_beta]
    group
  have ht2 : suzInv 0 * suzInv 0 = 1 := suzInv_sq (i := 0) (by norm_num)
  have hidx : (C.subgroupOf (invE 0)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨invInnerGen 0 4, hE⟩, fun g => ?_⟩
    rw [key, key]
    simp only [Subgroup.coe_mul]
    have hg := g.2
    generalize (g : Equiv.Perm (Fin 1782)) = G at hg ⊢
    have hge : G * invInnerGen 0 4 * betaPerm * (G * invInnerGen 0 4)⁻¹ =
        suzInv 0 * (G * betaPerm * G⁻¹) := by
      calc G * invInnerGen 0 4 * betaPerm * (G * invInnerGen 0 4)⁻¹ =
          G * (invInnerGen 0 4 * betaPerm * (invInnerGen 0 4)⁻¹) * G⁻¹ := by group
        _ = (G * suzInv 0) * betaPerm * G⁻¹ := by rw [he]; group
        _ = suzInv 0 * (G * betaPerm * G⁻¹) := by rw [comm_t0 hg]; group
    rw [hge]
    rcases conj_beta hg with h | h
    · rw [h]
      exact Or.inr ⟨rfl, tb_ne_b⟩
    · rw [h, ← mul_assoc, ht2, one_mul]
      exact Or.inl ⟨rfl, fun h' => tb_ne_b h'⟩
  have h := (C.subgroupOf (invE 0)).card_mul_index
  rw [hidx, card_invE (i := 0) (by norm_num)] at h
  have hc : Nat.card (C.subgroupOf (invE 0)) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : C ≤ invE 0)).toEquiv
  have h' : Nat.card C * 2 = 161280 := by
    rw [← hc]
    simpa [invInnerOrders] using h
  omega

theorem pinOK_parts : pinWords.length = 42 ∧ ∀ p < 42,
    ((pinWords.getD p []).all fun w =>
        (w.all fun j => decide (j < dGens.size)) && (wordTab 42 dGens w)[p]! == p) = true ∧
      ∀ q < 42, (q == p || (pinWords.getD p []).any fun w => (wordTab 42 dGens w)[q]! != q) =
        true := by
  have h := suzCS_zero_check.2.2
  simp only [pinOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  exact ⟨h.1, fun p hp => ⟨(h.2 p hp).1, fun q hq => (h.2 p hp).2 q hq⟩⟩

theorem dperm_word_mem
    (w : List ℕ) (hw : ∀ j ∈ w, j < dGens.size) :
    (w.map dperm).prod ∈ suzD := by
  refine suzD.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have := hw j hj
  rw [dGens_size] at this
  exact Subgroup.subset_closure ⟨j, this, rfl⟩

theorem tabRep_dword
    (w : List ℕ) (hw : ∀ j ∈ w, j < dGens.size) :
    TabRep (wordTab 42 dGens w) ((w.map dperm).prod) :=
  tabRep_wordTab (fun j hj => tabRep_dperm (by rw [dGens_size] at hj; exact hj)) w hw

theorem eq_one_of_comm_suzD
    {σ : Equiv.Perm (Fin 42)} (hσ : ∀ d ∈ suzD, σ * d = d * σ) :
    σ = 1 := by
  obtain ⟨-, hpin⟩ := pinOK_parts
  ext p
  simp only [Equiv.Perm.coe_one, id_eq]
  by_contra hne
  have hq : ((σ p : Fin 42) : ℕ) ≠ p := fun h => hne (congrArg Fin.val (Fin.ext h))
  obtain ⟨hfix, hmove⟩ := hpin p p.2
  have hm := hmove (σ p) (σ p).2
  simp only [Bool.or_eq_true, beq_iff_eq, hq, false_or, List.any_eq_true] at hm
  obtain ⟨w, hw, hwq⟩ := hm
  rw [List.all_eq_true] at hfix
  have hw' := hfix w hw
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hw'
  obtain ⟨hwl, hwp⟩ := hw'
  have hrep := tabRep_dword w hwl
  set d := (w.map dperm).prod
  have hdp : d p = p := Fin.ext (by rw [← hrep.apply p]; exact hwp)
  have hdq : d (σ p) ≠ σ p := by
    intro h
    have h1 := hrep.apply (σ p)
    rw [h] at h1
    rw [h1] at hwq
    simp at hwq
  apply hdq
  have := congrArg (fun π : Equiv.Perm (Fin 42) => π p) (hσ d (dperm_word_mem w hwl))
  simp only [Equiv.Perm.mul_apply, hdp] at this
  exact this.symm

theorem outerOK_parts :
    6 < (invFullGenArrs 0).size ∧ inM outerArr = false ∧
    notInOK (enumOf 42 (kGens 0) 40320).tabs (restrictArr (fixList 0) outerArr) = true := by
  have h := suzCS_zero_check.2.1
  simp only [outerOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem zero_model
    {J : Subgroup (Equiv.Perm (Fin 1782))}
    (hJ : IsComponent (J.subgroupOf (invE 0))) :
    (J.subgroupOf (invE 0)).Normal ∧
    ∀ (τ : Equiv.Perm (Fin 1782)) (R : Subgroup (Equiv.Perm (Fin 1782))),
      τ ∈ suzT → τ * suzInv 0 = suzInv 0 * τ → (∀ j ∈ J, τ * j = j * τ) →
      R ≤ invE 0 → IsPGroup 2 R → 2 ^ 9 ≤ Nat.card R → (∀ r ∈ R, τ * r = r * τ) →
      τ = 1 ∨ τ = suzInv 0 := by
  refine ⟨normal_of_component_zero _ hJ, fun τ R hτT hτt hτJ hRE hR2 hR9 hτR => ?_⟩
  have hL := fixList_points hm0
  have hτF : ∀ x : Fin 1782, (x : ℕ) ∈ fixList 0 ↔ (τ x : ℕ) ∈ fixList 0 := by
    intro x
    rw [mem_fixList (i := 0) (by norm_num), mem_fixList (i := 0) (by norm_num)]
    have h := congrArg (fun π : Equiv.Perm (Fin 1782) => π x) hτt
    simp only [Equiv.Perm.mul_apply] at h
    constructor
    · intro hx
      rw [← h, hx]
    · intro hx
      exact τ.injective (h.trans hx)
  set σ := hL.restrPerm τ hτF with hσ
  have hσD : ∀ d ∈ suzD, σ * d = d * σ := by
    intro d hd
    rw [← map_rho0_eq_suzD _ hJ] at hd
    obtain ⟨j, hj, rfl⟩ := hd
    have hj' : (j : Equiv.Perm (Fin 1782)) ∈ J := hj
    ext i
    apply congrArg Fin.val
    apply hL.pt_injective
    simp only [Equiv.Perm.mul_apply]
    rw [hσ, hL.pt_restrPerm, show rho0 = hL.restrHom (invE 0) (invE_preserves (i := 0)
      (by norm_num)) from rfl, hL.pt_restrHom, hL.pt_restrHom, hL.pt_restrPerm]
    have := congrArg (fun π : Equiv.Perm (Fin 1782) => π (hL.pt i)) (hτJ _ hj')
    simpa only [Equiv.Perm.mul_apply] using this
  have hσ1 : σ = 1 := eq_one_of_comm_suzD hσD
  have hτfix : ∀ x : Fin 1782, (x : ℕ) ∈ fixList 0 → τ x = x := by
    intro x hx
    obtain ⟨i, rfl⟩ := hL.exists_pt hx
    rw [← hL.pt_restrPerm τ hτF i, ← hσ, hσ1, Equiv.Perm.coe_one, id_eq]
  obtain ⟨h6, hinM, hnot⟩ := outerOK_parts
  have h6' : 6 < (invFullChain 0).originalCount := h6
  set d := (invFullChain 0).original.get ⟨6, h6'⟩ with hd
  have hdrep : Rep 1782 outerArr d := (invFullChain_arrays (i := 0) (by norm_num)).orig ⟨6, h6'⟩
  have hdD : d ∈ invD 0 := Subgroup.subset_closure (schreier_vector_get_mem_toList _ _)
  have hdc := invD_le_centT (i := 0) (by norm_num) hdD
  have hdT : d ∈ suzT := hdc.2
  have hdt : d * suzInv 0 = suzInv 0 * d := Subgroup.mem_centralizer_singleton_iff.1 hdc.1
  have hdM : d ∉ suzM := fun h => by
    have := (inM_iff hdrep).2 h
    rw [hinM] at this
    exact Bool.false_ne_true this
  have hdF : ∀ x : Fin 1782, (x : ℕ) ∈ fixList 0 ↔ (d x : ℕ) ∈ fixList 0 := by
    intro x
    rw [mem_fixList (i := 0) (by norm_num), mem_fixList (i := 0) (by norm_num)]
    have h := congrArg (fun π : Equiv.Perm (Fin 1782) => π x) hdt
    simp only [Equiv.Perm.mul_apply] at h
    constructor
    · intro hx
      rw [← h, hx]
    · intro hx
      exact d.injective (h.trans hx)
  have hτM : τ ∈ suzM := by
    by_contra hτM
    have hx : τ⁻¹ * d ∈ suzM := by
      have h := (Subgroup.mul_mem_iff_of_index_two suzM_index_T
        (a := (⟨τ, hτT⟩ : suzT)⁻¹) (b := ⟨d, hdT⟩))
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_mem_iff] at h
      exact h.2 (iff_of_false hτM hdM)
    have h1 : τ⁻¹ * suzInv 0 = suzInv 0 * τ⁻¹ := (Commute.inv_left hτt).eq
    have hxE : τ⁻¹ * d ∈ invE 0 := by
      rw [invE_eq_centM (i := 0) (by norm_num)]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hx⟩
      rw [mul_assoc, hdt, ← mul_assoc, h1, mul_assoc]
    have hρx : rho0 ⟨τ⁻¹ * d, hxE⟩ = hL.restrPerm d hdF := by
      ext i
      apply congrArg Fin.val
      apply hL.pt_injective
      rw [show rho0 = hL.restrHom (invE 0) (invE_preserves (i := 0) (by norm_num)) from rfl,
        hL.pt_restrHom, hL.pt_restrPerm]
      simp only [Equiv.Perm.mul_apply]
      have hdx : ((d (hL.pt i) : Fin 1782) : ℕ) ∈ fixList 0 := (hdF _).1 (hL.pt_mem i)
      have := hτfix _ hdx
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact this.symm
    have hmem : hL.restrPerm d hdF ∈ rho0.range := ⟨_, hρx⟩
    exact not_mem_of_notInOK rho0_enumerates hnot (hL.tabRep_restrictArr hdrep hdF) hmem
  have hτE : τ ∈ invE 0 := by
    rw [invE_eq_centM (i := 0) (by norm_num)]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hτt, hτM⟩
  have hker : (⟨τ, hτE⟩ : invE 0) ∈ rho0.ker := mem_ker_rho0_of_fix _ hτfix
  have hRb : (∀ r ∈ R, betaPerm * r = r * betaPerm) → False := by
    intro hrb
    have hle : R ≤ Subgroup.centralizer {betaPerm} ⊓ invE 0 := fun r hr =>
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (hrb r hr).symm, hRE hr⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [card_centralizer_beta] at hdvd
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk] at hdvd hR9
    have hk9 : 9 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hR9
    have := (pow_dvd_pow 2 hk9).trans hdvd
    norm_num at this
  rcases mem_ker_rho0 hker with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply hRb
    intro r hr
    have := hτR r hr
    simp only at h
    rw [h] at this
    exact this
  · exfalso
    apply hRb
    intro r hr
    have h2 := hτR r hr
    simp only at h
    rw [h] at h2
    have h3 : r * suzInv 0 = suzInv 0 * r := comm_t0 (hRE hr)
    have ht2 : suzInv 0 * suzInv 0 = 1 := suzInv_sq (i := 0) (by norm_num)
    calc betaPerm * r = suzInv 0 * (suzInv 0 * betaPerm * r) := by
          rw [← mul_assoc, ← mul_assoc, ht2, one_mul]
      _ = suzInv 0 * (r * (suzInv 0 * betaPerm)) := by rw [h2]
      _ = suzInv 0 * (suzInv 0 * r * betaPerm) := by rw [← mul_assoc r, h3]
      _ = r * betaPerm := by rw [← mul_assoc, ← mul_assoc, ht2, one_mul]

end CFSG.ComponentClassification.CatFactsL4U4.SuzCS

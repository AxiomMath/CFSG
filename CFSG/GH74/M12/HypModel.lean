module

public import CFSG.GH74.M12.HypTbl
public import CFSG.GH74.M12.HypCore
public import CFSG.GH74.M12.Statements
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.GH74.M12.Hyp

open CFSG.Blueprint CFSG.GH74

abbrev G12 : Type := ↥NativeSporadic.M12

theorem lvl_five_card :
    Nat.card (CFSG.Sporadic.Mathieu.lvl CFSG.Sporadic.Mathieu.Native.m12Data
      CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b 5) = 1 := by
  have h := (CFSG.Sporadic.Mathieu.chain CFSG.Sporadic.Mathieu.m12_hyp).2.2 5 (by decide)
  rw [h]
  have : CFSG.Sporadic.Mathieu.Native.m12Data.base.size = 5 := rfl
  rw [this]
  simp

theorem m12_fix5
    (g : G12) (h : ∀ i : Fin 12, i.val < 5 → g.1 i = i) : g = 1 := by
  have hC := CFSG.Sporadic.Mathieu.chain CFSG.Sporadic.Mathieu.m12_hyp
  have hbase : CFSG.Sporadic.Mathieu.Native.m12Data.base = #[0, 1, 2, 3, 4] := rfl
  have step : ∀ i < 5, g ∈ CFSG.Sporadic.Mathieu.lvl CFSG.Sporadic.Mathieu.Native.m12Data
      CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b i →
      g ∈ CFSG.Sporadic.Mathieu.lvl CFSG.Sporadic.Mathieu.Native.m12Data
        CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b (i + 1) := by
    intro i hi hg
    have hib : i < CFSG.Sporadic.Mathieu.Native.m12Data.base.size := by
      rw [hbase]; simpa using hi
    refine (hC.2.1 i hib g hg).1 ?_
    have hb : CFSG.Sporadic.Mathieu.Native.m12Data.base[i]! = i := by
      interval_cases i <;> rfl
    rw [hb, CFSG.Sporadic.Th.idx_of_lt g (show i < 12 by omega)]
    have := h ⟨i, by omega⟩ hi
    exact congrArg Fin.val this
  have h0 : g ∈ CFSG.Sporadic.Mathieu.lvl CFSG.Sporadic.Mathieu.Native.m12Data
      CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b 0 := by
    rw [CFSG.Sporadic.Mathieu.lvl_zero CFSG.Sporadic.Mathieu.m12_hyp]; trivial
  have h5 : g ∈ CFSG.Sporadic.Mathieu.lvl CFSG.Sporadic.Mathieu.Native.m12Data
      CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b 5 := by
    have h1 := step 0 (by norm_num) h0
    have h2 := step 1 (by norm_num) h1
    have h3 := step 2 (by norm_num) h2
    have h4 := step 3 (by norm_num) h3
    exact step 4 (by norm_num) h4
  have := Subgroup.eq_bot_of_card_eq _ lvl_five_card
  rw [this] at h5
  simpa using h5

theorem tbl_m12gA : tbl CFSG.Sporadic.Mathieu.m12gA = tA := by decide +kernel

theorem tbl_m12gB : tbl CFSG.Sporadic.Mathieu.m12gB = tB := by decide +kernel

theorem tbl_bfE : tbl bfE = ET := by decide +kernel

theorem tbl_bfN : tbl bfN = NT := by decide +kernel

theorem tbl_bfF : tbl bfF = FT := by decide +kernel

theorem tbl_bfX : tbl bfX = XT := by
  unfold bfX XT
  rw [tbl_mul, tbl_mul, tbl_mul, tbl_inv, tbl_inv, tbl_bfE, tbl_bfF]

theorem tbl_bfJ : tbl bfJ = JT := by
  unfold bfJ
  rw [tbl_pow, tbl_bfF, JT_eq]

@[expose] def letterP (l : Int) : Equiv.Perm (Fin 12) :=
  if l = 1 then CFSG.Sporadic.Mathieu.m12gA else
    if l = -1 then (CFSG.Sporadic.Mathieu.m12gA)⁻¹ else
      if l = 2 then CFSG.Sporadic.Mathieu.m12gB else (CFSG.Sporadic.Mathieu.m12gB)⁻¹

@[expose] def wordP : List Int → Equiv.Perm (Fin 12)
  | [] => 1
  | l :: w => letterP l * wordP w

theorem tbl_letterP (l : Int) : tbl (letterP l) = letterT l := by
  unfold letterP letterT
  split_ifs
  · exact tbl_m12gA
  · rw [tbl_inv, tbl_m12gA]
  · exact tbl_m12gB
  · rw [tbl_inv, tbl_m12gB]

theorem tbl_wordP (w : List Int) : tbl (wordP w) = wordT w := by
  induction w with
  | nil => exact tbl_one
  | cons l w ih => rw [wordP, wordT, tbl_mul, tbl_letterP, ih]

theorem letterP_mem (l : Int) : letterP l ∈ NativeSporadic.M12 := by
  have ha : CFSG.Sporadic.Mathieu.m12gA ∈ NativeSporadic.M12 := CFSG.Sporadic.Mathieu.m12a.2
  have hb : CFSG.Sporadic.Mathieu.m12gB ∈ NativeSporadic.M12 := CFSG.Sporadic.Mathieu.m12b.2
  unfold letterP
  split_ifs
  · exact ha
  · exact Subgroup.inv_mem _ ha
  · exact hb
  · exact Subgroup.inv_mem _ hb

theorem wordP_mem (w : List Int) : wordP w ∈ NativeSporadic.M12 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih => exact Subgroup.mul_mem _ (letterP_mem l) ih

@[expose] def CJ : Subgroup G12 :=
  (Subgroup.centralizer ({bfJ} : Set (Equiv.Perm (Fin 12)))).comap NativeSporadic.M12.subtype

theorem mem_CJ {x : G12} : x ∈ CJ ↔ bfJ * x.1 = x.1 * bfJ := by
  rw [CJ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  simp

@[expose] def tauC (x : ↥CJ) : List Nat := tbl x.1.1

theorem tauC_injective : Function.Injective tauC := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact tbl_injective h

theorem tauC_mul (x y : ↥CJ) : tauC (x * y) = tmul (tauC x) (tauC y) :=
  tbl_mul x.1.1 y.1.1

theorem tauC_one : tauC (1 : ↥CJ) = tid := tbl_one

theorem tauC_inv (x : ↥CJ) : tauC x⁻¹ = tinv (tauC x) := tbl_inv x.1.1

theorem word_mem_CJ (w : List Int) (hw : tmul JT (wordT w) = tmul (wordT w) JT) :
    (⟨wordP w, wordP_mem w⟩ : G12) ∈ CJ := by
  rw [mem_CJ]
  apply tbl_injective
  show tbl (bfJ * wordP w) = tbl (wordP w * bfJ)
  rw [tbl_mul, tbl_mul, tbl_bfJ, tbl_wordP]
  exact hw

theorem gen1_mem : (⟨wordP wordG1, wordP_mem _⟩ : G12) ∈ CJ :=
  word_mem_CJ _ (by rw [wordG1_eq]; exact gensT_commute _ (by simp [gensT]))

theorem gen2_mem : (⟨wordP wordG2, wordP_mem _⟩ : G12) ∈ CJ :=
  word_mem_CJ _ (by rw [wordG2_eq]; exact gensT_commute _ (by simp [gensT]))

theorem gen3_mem : (⟨wordP wordG3, wordP_mem _⟩ : G12) ∈ CJ :=
  word_mem_CJ _ (by rw [wordG3_eq]; exact gensT_commute _ (by simp [gensT]))

@[expose] def genC : List ↥CJ :=
  [⟨_, gen1_mem⟩, ⟨_, gen2_mem⟩, ⟨_, gen3_mem⟩]

theorem tauC_genC : (genC.map tauC) = gensT := by
  simp only [genC, List.map_cons, List.map_nil, tauC]
  rw [tbl_wordP, tbl_wordP, tbl_wordP, wordG1_eq, wordG2_eq, wordG3_eq]
  rfl

theorem foldl_stepHT (R : List Nat → Prop) (hid : R tid) (hg : ∀ g ∈ gensT, R g)
    (hmul : ∀ s t, R s → R t → R (tmul s t)) :
    ∀ (c : List (Nat × Nat)) (L : List (List Nat)), (∀ t ∈ L, R t) →
      ∀ t ∈ c.foldl stepHT L, R t := by
  intro c
  induction c with
  | nil => intro L hL t ht; exact hL t ht
  | cons pg c ih =>
    intro L hL t ht
    refine ih (stepHT L pg) ?_ t ht
    intro u hu
    unfold stepHT at hu
    rw [List.mem_append] at hu
    rcases hu with hu | hu
    · exact hL u hu
    · rw [List.mem_singleton] at hu
      subst hu
      apply hmul
      · rw [List.getD_eq_getElem?_getD]
        cases hL' : L[pg.1]? with
        | none => exact hid
        | some a => exact hL a (List.mem_of_getElem? hL')
      · rw [List.getD_eq_getElem?_getD]
        cases hg' : gensT[pg.2]? with
        | none => exact hid
        | some a => exact hg a (List.mem_of_getElem? hg')

theorem tauC_real : ∀ t ∈ HT, ∃ x : ↥CJ, tauC x = t := by
  refine foldl_stepHT (fun t => ∃ x : ↥CJ, tauC x = t) ⟨1, tauC_one⟩ ?_ ?_ certHT [tid] ?_
  · intro g hg
    rw [← tauC_genC] at hg
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hg
    exact ⟨x, rfl⟩
  · rintro s t ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, tauC_mul x y⟩
  · intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨1, tauC_one⟩

theorem tbl_take_five_eq (σ : Equiv.Perm (Fin 12)) :
    (tbl σ).take 5 = [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val] := by
  simp [tbl, List.ofFn_succ]

theorem bfJ_fix : ∀ i : Fin 12, bfJ i = i ↔ i.val < 4 := by decide +kernel

theorem bfJ_four : bfJ 4 = 8 := by decide +kernel

theorem tauC_mem
    (x : ↥CJ) : tauC x ∈ HT := by
  obtain ⟨g, hg⟩ := x
  have hcomm : ∀ i : Fin 12, bfJ (g.1 i) = g.1 (bfJ i) := by
    intro i
    have := congrArg (fun p : Equiv.Perm (Fin 12) => p i) (mem_CJ.1 hg)
    simpa using this
  have hlt : ∀ i : Fin 12, i.val < 4 → (g.1 i).val < 4 := by
    intro i hi
    have h1 : bfJ i = i := (bfJ_fix i).2 hi
    have h2 : bfJ (g.1 i) = g.1 i := by rw [hcomm, h1]
    exact (bfJ_fix _).1 h2
  have hge : 4 ≤ (g.1 4).val := by
    by_contra hcon
    push Not at hcon
    have h2 : bfJ (g.1 4) = g.1 4 := (bfJ_fix _).2 hcon
    rw [hcomm, bfJ_four] at h2
    exact absurd (g.1.injective h2) (by decide)
  have hinj : ∀ i j : Fin 12, i ≠ j → g.1 i ≠ g.1 j := fun i j hij h => hij (g.1.injective h)
  have h0 := hlt 0 (by decide)
  have h1 := hlt 1 (by decide)
  have h2 := hlt 2 (by decide)
  have h3 := hlt 3 (by decide)
  obtain ⟨t, htHT, htake⟩ := HT_cover (g.1 0).val (List.mem_range.2 h0) (g.1 1).val
    (List.mem_range.2 h1) (g.1 2).val (List.mem_range.2 h2) (g.1 3).val (List.mem_range.2 h3)
    (g.1 4).val (List.mem_range.2 (g.1 4).isLt)
    (fun h => hinj 0 1 (by decide) (Fin.ext h)) (fun h => hinj 0 2 (by decide) (Fin.ext h))
    (fun h => hinj 0 3 (by decide) (Fin.ext h)) (fun h => hinj 1 2 (by decide) (Fin.ext h))
    (fun h => hinj 1 3 (by decide) (Fin.ext h)) (fun h => hinj 2 3 (by decide) (Fin.ext h)) hge
  obtain ⟨y, hy⟩ := tauC_real t htHT
  have hagree : (tbl y.1.1).take 5 = (tbl g.1).take 5 := by
    have e1 : (tbl y.1.1).take 5 = t.take 5 := by rw [← hy]; rfl
    rw [e1, htake, tbl_take_five_eq]
  have hfix : (y.1⁻¹ * g : G12) = 1 := by
    apply m12_fix5
    intro i hi
    have hyi : y.1.1 i = g.1 i := tbl_take_five (σ := y.1.1) (τ := g.1) hagree i hi
    show (y.1.1)⁻¹ (g.1 i) = i
    rw [← hyi]
    simp
  have hgy : y.1 = g := inv_mul_eq_one.1 hfix
  have : tauC ⟨g, hg⟩ = t := by
    rw [← hy]
    show tbl g.1 = tbl y.1.1
    rw [hgy]
  rw [this]
  exact htHT

theorem card_mem_list {α : Type*} [DecidableEq α] (L : List α) (h : L.Nodup) :
    Nat.card {x // x ∈ L} = L.length := by
  have := List.ncard_ofPred_mem (l := L)
  rw [h.dedup] at this
  rw [← this]
  exact Nat.card_coe_set_eq _

@[expose] def bfElt (i j k m : Nat) : Equiv.Perm (Fin 12) :=
  bfE ^ i * bfN ^ j * (bfX ^ k * bfF ^ m)

theorem tbl_bfElt (i j k m : Nat) : tbl (bfElt i j k m) = bfT i j k m := by
  unfold bfElt bfT
  rw [tbl_mul, tbl_mul, tbl_mul, tbl_pow, tbl_pow, tbl_pow, tbl_pow, tbl_bfE, tbl_bfN, tbl_bfX,
    tbl_bfF]

theorem bfE_mem : bfE ∈ bfS := Subgroup.subset_closure (by simp)

theorem bfN_mem : bfN ∈ bfS := Subgroup.subset_closure (by simp)

theorem bfF_mem : bfF ∈ bfS := Subgroup.subset_closure (by simp)

theorem bfX_mem : bfX ∈ bfS := by
  unfold bfX
  exact mul_mem (mul_mem (mul_mem (inv_mem bfE_mem) bfF_mem) bfE_mem) (inv_mem bfF_mem)

theorem bfJ_mem_bfS : bfJ ∈ bfS := bfF_pow_mem 4

theorem bfElt_mem (i j k m : Nat) : bfElt i j k m ∈ bfS :=
  mul_mem (mul_mem (pow_mem bfE_mem i) (pow_mem bfN_mem j))
    (mul_mem (pow_mem bfX_mem k) (pow_mem bfF_mem m))

@[expose] def BS : Subgroup (Equiv.Perm (Fin 12)) where
  carrier := {σ | tbl σ ∈ BT}
  mul_mem' := by
    intro a b ha hb
    show tbl (a * b) ∈ BT
    rw [tbl_mul]
    exact BT_mul _ ha _ hb
  one_mem' := by
    show tbl 1 ∈ BT
    rw [tbl_one]
    exact tid_mem_BT
  inv_mem' := by
    intro a ha
    show tbl a⁻¹ ∈ BT
    rw [tbl_inv]
    exact BT_inv _ ha

theorem mem_bfS_iff
    {σ : Equiv.Perm (Fin 12)} : σ ∈ bfS ↔ tbl σ ∈ BT := by
  constructor
  · intro hσ
    have hle : bfS ≤ BS := by
      unfold bfS
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · show tbl bfE ∈ BT
        rw [tbl_bfE]; exact ET_mem_BT
      · show tbl bfN ∈ BT
        rw [tbl_bfN]; exact NT_mem_BT
      · show tbl bfF ∈ BT
        rw [tbl_bfF]; exact FT_mem_BT
    exact hle hσ
  · intro h
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 h
    have : σ = bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) := by
      apply tbl_injective
      rw [tbl_bfElt]
      exact hn
    rw [this]
    exact bfElt_mem _ _ _ _

theorem card_bfS : Nat.card ↥bfS = 64 := by
  have e : ↥bfS ≃ {t // t ∈ BT} :=
    Equiv.ofBijective (fun σ => ⟨tbl σ.1, mem_bfS_iff.1 σ.2⟩)
      ⟨fun a b hab => Subtype.ext (tbl_injective (congrArg Subtype.val hab)), by
        rintro ⟨t, ht⟩
        obtain ⟨n, -, hn⟩ := mem_BT_iff.1 ht
        refine ⟨⟨bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8), bfElt_mem _ _ _ _⟩, ?_⟩
        apply Subtype.ext
        show tbl _ = t
        rw [tbl_bfElt]
        exact hn.symm⟩
  rw [Nat.card_congr e, card_mem_list BT BT_nodup, BT_length]

theorem bfS_le_M12 : bfS ≤ NativeSporadic.M12 := by
  intro σ hσ
  obtain ⟨x, hx⟩ := tauC_real (tbl σ) (BT_sub_HT _ (mem_bfS_iff.1 hσ))
  have : x.1.1 = σ := tbl_injective hx
  rw [← this]
  exact x.1.2

@[expose] def bfS' : Subgroup G12 := bfS.subgroupOf NativeSporadic.M12

theorem mem_bfS' {x : G12} : x ∈ bfS' ↔ x.1 ∈ bfS := Iff.rfl

theorem card_bfS' : Nat.card ↥bfS' = 64 := by
  show Nat.card ↥(bfS.subgroupOf NativeSporadic.M12) = 64
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe bfS_le_M12).toEquiv, card_bfS]

theorem card_G12 :
    Nat.card G12 = 95040 := CFSG.Sporadic.Mathieu.card_M12

theorem factorization_95040 : Nat.factorization 95040 2 = 6 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (95040 : ℕ) = 2 ^ 6 * 1485 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

@[expose] def bfSylow : Sylow 2 G12 :=
  Sylow.ofCard bfS' (by rw [card_bfS', card_G12, factorization_95040]; norm_num)

theorem coe_bfSylow
    : (bfSylow : Subgroup G12) = bfS' := Sylow.coe_ofCard _ _

@[expose] def Jelt : G12 := ⟨bfJ, bfS_le_M12 bfJ_mem_bfS⟩

@[expose] def Xelt : G12 := ⟨bfX, bfS_le_M12 bfX_mem⟩

@[expose] def Eelt : G12 := ⟨bfE, bfS_le_M12 bfE_mem⟩

@[expose] def Felt : G12 := ⟨bfF, bfS_le_M12 bfF_mem⟩

theorem Jelt_mem_CJ : Jelt ∈ CJ := by
  rw [mem_CJ]
  rfl

theorem Jelt_mul_self : Jelt * Jelt = 1 := by
  apply Subtype.ext
  apply tbl_injective
  show tbl (bfJ * bfJ) = tbl 1
  rw [tbl_mul, tbl_bfJ, tbl_one]
  decide +kernel

theorem Jelt_ne_one : Jelt ≠ 1 := by
  intro h
  have h0 : Jelt.1 = (1 : G12).1 := congrArg Subtype.val h
  have h1 : bfJ = 1 := h0
  have h2 : tbl bfJ = tbl 1 := congrArg tbl h1
  rw [tbl_bfJ, tbl_one] at h2
  exact absurd h2 (by decide +kernel)

theorem orderOf_Jelt : orderOf Jelt = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Jelt_mul_self) Jelt_ne_one

theorem exists_conj_of_central_involution
    (z : G12) (hz : IsCentralInvolution z) :
    ∃ g : G12, g * Jelt * g⁻¹ = z := by
  obtain ⟨ho, S, hzS, hcen⟩ := hz
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G12 bfSylow S
  have hconj : ∀ y : G12, y ∈ (S : Subgroup G12) ↔ g⁻¹ * y * g ∈ (bfSylow : Subgroup G12) := by
    intro y
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  have hsq : z * z = 1 := by
    rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [ho])
  have hne : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at ho; omega
  obtain ⟨y, hyd⟩ : ∃ y : G12, y = g⁻¹ * z * g := ⟨_, rfl⟩
  have hy : y ∈ (bfSylow : Subgroup G12) := by rw [hyd]; exact (hconj z).1 hzS
  have hcentral : ∀ s ∈ (bfSylow : Subgroup G12), s * y = y * s := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ (S : Subgroup G12) := by
      rw [hconj]
      have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [e]; exact hs
    have := hcen _ hs'
    rw [hyd]
    calc s * (g⁻¹ * z * g) = g⁻¹ * ((g * s * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * s * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * z * g) * s := by group
  have hysq : y * y = 1 := by
    rw [hyd]
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hsq]; group
  have hyne : y ≠ 1 := by
    intro h
    apply hne
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [hyd]
      _ = 1 := by rw [h]; group
  rw [coe_bfSylow] at hy hcentral
  have hty : tbl y.1 ∈ BT := mem_bfS_iff.1 hy
  have hcent' : ∀ t ∈ BT, tmul (tbl y.1) t = tmul t (tbl y.1) := by
    intro t ht
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 ht
    have hσ : bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) ∈ bfS := bfElt_mem _ _ _ _
    have hs : (⟨_, bfS_le_M12 hσ⟩ : G12) ∈ bfS' := hσ
    have h1 := hcentral _ hs
    have h2 : (bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8)) * y.1 =
        y.1 * (bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8)) := congrArg Subtype.val h1
    have h3 := congrArg tbl h2
    rw [tbl_mul, tbl_mul, tbl_bfElt, ← hn] at h3
    exact h3.symm
  have hsq' : tmul (tbl y.1) (tbl y.1) = tid := by
    rw [← tbl_mul, ← tbl_one]
    exact congrArg tbl (congrArg Subtype.val hysq)
  have hne' : tbl y.1 ≠ tid := by
    intro h
    rw [← tbl_one] at h
    exact hyne (Subtype.ext (tbl_injective h))
  have hJ := BT_central_involution _ hty hcent' hsq' hne'
  rw [← tbl_bfJ] at hJ
  have hyJ : y = Jelt := Subtype.ext (tbl_injective hJ)
  refine ⟨g, ?_⟩
  rw [← hyJ, hyd]
  group

theorem exists_conj_Jelt_Xelt :
    ∃ h : G12, h * Jelt * h⁻¹ = Xelt := by
  refine ⟨⟨wordP wordH, wordP_mem _⟩, ?_⟩
  apply Subtype.ext
  apply tbl_injective
  show tbl (wordP wordH * bfJ * (wordP wordH)⁻¹) = tbl bfX
  rw [tbl_mul, tbl_mul, tbl_inv, tbl_wordP, tbl_bfJ, tbl_bfX]
  exact wordH_conj

theorem Xelt_ne_Jelt : Xelt ≠ Jelt := by
  intro h
  have h0 : Xelt.1 = Jelt.1 := congrArg Subtype.val h
  have h1 : tbl bfX = tbl bfJ := congrArg tbl h0
  rw [tbl_bfX, tbl_bfJ] at h1
  exact XT_ne_JT h1

end CFSG.GH74.M12.Hyp

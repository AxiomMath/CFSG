module

public import Certificates.Data.Kernel.Co1M.ElevenFix
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Certificates.Kernel.Co1M.RankSound
public import CFSG.Certificates.Kernel.F2WordSound
public import CFSG.Sporadic.Co1Block.PointStab
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Schreier.Co1Lift
public import CFSG.Sporadic.Co1
public import CFSG.HardMathSupport.Dickson.BMRows.Co2Eleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.Co1ElevenGlue

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2 CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KD.Co1ElevenFix CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  Matrix

theorem getD_map_unpack (x : Nat) : ∀ (l : List Nat) (i : Nat),
    (l.map (unpackR 24)).getD i (unpackR 24 x) = unpackR 24 (getL x l i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map_unpack x l i

theorem powB_unpack (Y : Nat) : ∀ n,
    unpackR 24 (powB Y n) = CFSG.Sporadic.Co1Schreier.Native.pow (unpackR 24 Y) n
  | 0 => by
    change unpackR 24 oneK = CFSG.Sporadic.Co1Schreier.Native.one ()
    exact CFSG.KC.Co1B.one_eq.symm
  | n + 1 => by
    change unpackR 24 (mulK (powB Y n) Y) = CFSG.Sporadic.Co1Schreier.Native.mul
      (CFSG.Sporadic.Co1Schreier.Native.pow (unpackR 24 Y) n) (unpackR 24 Y)
    rw [← mul_unpack, powB_unpack Y n]

theorem mulVec_of_rep {M : Nat} {g : GL24} (h : MRep (unpackR 24 M) g) (w : Nat) :
    (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 w = toVecD 24 (vmF 24 (trK 24 M) w) := by
  unfold MRep at h
  rw [← h]
  exact CFSG.KC.Co1M.mulVec_unpack M w

theorem fixB_sound {M w : Nat} (h : fixB M w = true) :
    w < 2 ^ 24 ∧ vmF 24 (trK 24 M) w = w := by
  unfold fixB at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem nodupB_nodup : ∀ L : List Nat, nodupB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    rw [nodupB, Bool.and_eq_true, List.all_eq_true] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodupB_nodup t h.2⟩
    have h1 := h.1 a ha
    have e : Nat.beq a a = true := by simp
    rw [e] at h1
    exact absurd h1 (by decide)

theorem fix_le_of_piv {M : ℕ} {W : List ℕ} {k : ℕ} (hk : W.length = k)
    (hpiv : pivK 24 (W.map fun v => vmF 24 (trK 24 M) v ^^^ v) 0 = true) :
    {v : Fin 24 → ZMod 2 | rowsMatrix 24 (unpackR 24 M) *ᵥ v = v}.ncard ≤ 2 ^ (24 - k) := by
  obtain ⟨L, hL⟩ : ∃ L, L = W.map fun v => vmF 24 (trK 24 M) v ^^^ v := ⟨_, rfl⟩
  rw [← hL] at hpiv
  obtain ⟨hlow, hnd⟩ := CFSG.KC.Co1Fix.pivK_spec L 0 hpiv
  have hLl : L.length = k := by rw [hL, List.length_map, hk]
  have himg : ∀ i : Fin k, rowsMatrix 24 (unpackR 24 M) *ᵥ toVecD 24 (W.getD i 0) -
      toVecD 24 (W.getD i 0) = CFSG.KC.Co1Fix.vecOf (L.getD i 0) := by
    intro i
    have hi : i.val < W.length := by rw [hk]; exact i.isLt
    have e : L.getD i 0 = vmF 24 (trK 24 M) (W.getD i 0) ^^^ W.getD i 0 := by
      rw [hL, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
        List.getD_eq_getElem _ _ hi, List.getElem_map]
    rw [e, CFSG.KC.Co1M.mulVec_unpack, CFSG.KC.Co1Fix.vecOf, toVecD_xor,
      CFSG.KC.Co1M.sub_eq_add2]
  exact CFSG.KC.FixRank.ncard_fix_le_of_indep (k := k) _
    (fun g hg => CFSG.KC.Co1Fix.piv_indep (n := k) (by omega) (fun v hv => (hlow v hv).1) hnd g hg)
    fun i => ⟨_, himg i⟩

theorem elevenFix_sound
    {mem : Nat → Bool} {b0 b1 : Nat} {derivs : List (List Nat)} {RS RIS W NF : List Nat}
    {U iy ie p q k n : Nat} (h : elevenFixOK mem [b0, b1] derivs RS RIS W NF U iy ie p q k n = true)
    (hA : MRep (unpackR 24 b0) A₁) (hB : MRep (unpackR 24 b1) A₂)
    (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX) :
    ∃ Y E : GL24, Y ∈ GA ∧ E ∈ GA ∧ Y ^ p = 1 ∧ E ^ q = 1 ∧ E ≠ 1 ∧ E * Y = Y * E ∧
      {v : Vec24 | (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}.ncard ≤ 2 ^ (24 - k) ∧
      (∃ S : Finset Vec24, S.card = n ∧
        ∀ v ∈ S, (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧ v ∉ certX) ∧
      toVecD 24 U ∈ xFix Y := by
  unfold elevenFixOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdag, hpY⟩, hpE⟩, hmv⟩, hcomm⟩, hlen⟩, hpiv⟩, hnl⟩, hnd⟩, hall⟩, hU⟩,
    hmU⟩ := h
  set ds := derivs.map (List.map decL)
  have hd : CFSG.Sporadic.Co1Schreier.Native.dag [unpackR 24 b0, unpackR 24 b1] ds =
      (RS.map (unpackR 24), RIS.map (unpackR 24), true) := dag_sound hdag
  have hrep := dag_rep (.cons hA (.cons hB .nil)) ds (by rw [hd])
  rw [hd] at hrep
  have hGA : ∀ g ∈ dagG [A₁, A₂] ds, g ∈ GA := dagG_mem (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with e | e
    · rw [e]
      exact A₁_mem
    · rw [e]
      exact A₂_mem) ds
  have hrepAt : ∀ i, MRep (unpackR 24 (getL oneK RS i)) ((dagG [A₁, A₂] ds).getD i 1) := by
    intro i
    have h1 := getD_rep hrep MRep.one i
    rwa [CFSG.KC.Co1B.one_eq, getD_map_unpack] at h1
  set Y := (dagG [A₁, A₂] ds).getD iy 1
  set E := (dagG [A₁, A₂] ds).getD ie 1
  have hRY : MRep (unpackR 24 (getL oneK RS iy)) Y := hrepAt iy
  have hRE : MRep (unpackR 24 (getL oneK RS ie)) E := hrepAt ie
  have hpow : ∀ {X : Nat} {g : GL24} (e : Nat), MRep (unpackR 24 X) g →
      Nat.beq (powB X e) oneK = true → g ^ e = 1 := by
    intro X g e hX hb
    have h1 : MRep (unpackR 24 (powB X e)) (g ^ e) := by
      rw [powB_unpack]
      exact hX.pow e
    rw [Nat.eq_of_beq_eq_true hb, ← CFSG.KC.Co1B.one_eq] at h1
    exact h1.eq MRep.one
  have hfixY : ∀ {w : Nat}, fixB (getL oneK RS iy) w = true →
      w < 2 ^ 24 ∧ (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 w = toVecD 24 w := by
    intro w hw
    obtain ⟨h1, h2⟩ := fixB_sound hw
    exact ⟨h1, by rw [mulVec_of_rep hRY, h2]⟩
  refine ⟨Y, E, getD_mem_of_forall hGA iy, getD_mem_of_forall hGA ie, hpow p hRY hpY,
    hpow q hRE hpE, ?_, ?_, ?_, ?_, ?_⟩
  · intro hE1
    have h1 := mulVec_of_rep hRE 1
    rw [hE1, Units.val_one, one_mulVec] at h1
    have h2 := toVecD_injective (by norm_num) (CFSG.KC.F2W.vmF_lt 24 _ 1) h1
    unfold movesB at hmv
    rw [← h2] at hmv
    have e : Nat.beq 1 1 = true := rfl
    rw [e] at hmv
    exact absurd hmv (by decide)
  · have h1 := hRE.mul hRY
    have h2 := hRY.mul hRE
    rw [mul_unpack] at h1 h2
    rw [Nat.eq_of_beq_eq_true hcomm] at h1
    exact h1.eq h2
  · have hf := fix_le_of_piv (Nat.eq_of_beq_eq_true hlen) hpiv
    have hY' : rowsMatrix 24 (unpackR 24 (getL oneK RS iy)) =
        (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) := hRY
    rwa [hY'] at hf
  · rw [List.all_eq_true] at hall
    have hinj : ∀ x ∈ NF, ∀ y ∈ NF, toVecD 24 x = toVecD 24 y → x = y := fun x hx y hy e =>
      toVecD_injective (fixB_sound (Bool.and_eq_true _ _ ▸ hall x hx).1).1
        (fixB_sound (Bool.and_eq_true _ _ ▸ hall y hy).1).1 e
    refine ⟨(NF.map (toVecD 24)).toFinset, ?_, fun v hv => ?_⟩
    · rw [List.toFinset_card_of_nodup ((nodupB_nodup NF hnd).map_on hinj), List.length_map,
        Nat.eq_of_beq_eq_true hnl]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hv)
      have hw' := hall w hw
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hw'
      obtain ⟨hlt, hfw⟩ := hfixY hw'.1
      refine ⟨hfw, fun hX => ?_⟩
      rw [← hmem w hlt, hw'.2] at hX
      exact Bool.false_ne_true hX
  · obtain ⟨hlt, hfw⟩ := hfixY hU
    exact ⟨(hmem U hlt).1 hmU, hfw⟩

section Orbit

@[expose, instance_reducible] def glAct16954 : MulAction GL24 Vec24 where
  smul g v := ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v
  one_smul v := by
    change ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  mul_smul g h v := mulVec_mul' g h v

attribute [local instance] glAct16954

theorem smul_def16954 (g : GL24) (v : Vec24) :
    g • v = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := rfl


theorem card_cent_le_of_fix {Y : GL24} (hY : Y ∈ GA) (ho : orderOf Y = 11) {u : Vec24}
    (hu : u ∈ xFix Y) :
    Nat.card (GA ⊓ Subgroup.centralizer {Y} : Subgroup GL24) ≤ (xFix Y).ncard * 11 := by
  set C : Subgroup GL24 := GA ⊓ Subgroup.centralizer {Y}
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨g, hgA, hgu⟩ := (fam_co1_order_point_stabilizer).1 (certVec 0) ⟨0, by norm_num, rfl⟩ u hu1
  have horb : MulAction.orbit C u ⊆ xFix Y := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    beta_reduce
    rw [Subgroup.mk_smul, smul_def16954]
    obtain ⟨hcA, hcY⟩ := Subgroup.mem_inf.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcY
    refine ⟨mulVec_mem_certX hcA hu1, ?_⟩
    rw [← mulVec_mul', ← hcY, mulVec_mul', hu2]
  have hfix0 : ∀ s : GL24, ((s : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u = u →
      ((g⁻¹ * s * g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 = certVec 0 := by
    intro s hs
    rw [mulVec_mul', mulVec_mul', hgu, hs, ← hgu, ← mulVec_mul', inv_mul_cancel, mulVec_one']
  have hcA : ∀ s ∈ GA, g⁻¹ * s * g ∈ GA := fun s hs =>
    GA.mul_mem (GA.mul_mem (GA.inv_mem hgA) hs) hgA
  have hc0H : g⁻¹ * Y * g ∈ stabH := (fix_iff_stabH ⟨_, hcA Y hY⟩).1 (hfix0 Y hu2)
  set c0 : stabH := ⟨g⁻¹ * Y * g, hc0H⟩
  have hmemH : ∀ s : MulAction.stabilizer C u, g⁻¹ * ((s : C) : GL24) * g ∈ stabH := by
    intro s
    have h := s.2
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, smul_def16954] at h
    exact (fix_iff_stabH ⟨_, hcA _ (Subgroup.mem_inf.1 (s : C).2).1⟩).1
      (hfix0 ((s : C) : GL24) h)
  have hcomm : ∀ s : MulAction.stabilizer C u,
      (⟨_, hmemH s⟩ : stabH) ∈ Subgroup.centralizer ({c0} : Set stabH) := by
    intro s
    have h := (Subgroup.mem_inf.1 (s : C).2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc g⁻¹ * ((s : C) : GL24) * g * (g⁻¹ * Y * g) = g⁻¹ * (((s : C) : GL24) * Y) * g := by group
      _ = g⁻¹ * (Y * ((s : C) : GL24)) * g := by rw [h]
      _ = g⁻¹ * Y * g * (g⁻¹ * ((s : C) : GL24) * g) := by group
  have : Finite stabH := Nat.finite_of_card_ne_zero (by rw [card_stabH]; norm_num)
  have hstab : Nat.card (MulAction.stabilizer C u) ≤
      Nat.card (Subgroup.centralizer ({c0} : Set stabH)) := by
    refine Nat.card_le_card_of_injective (fun s => ⟨⟨_, hmemH s⟩, hcomm s⟩) ?_
    intro s s' e
    simp only [Subtype.mk.injEq] at e
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel e)))
  have hoc : orderOf c0 = 11 := by
    rw [Subgroup.orderOf_mk, show g⁻¹ * Y * g = MulAut.conj g⁻¹ Y by
      rw [MulAut.conj_apply, inv_inv], MulEquiv.orderOf_eq, ho]
  have h11 := CFSG.HardMathSupport.Dickson.BMRows.Co2Eleven.co2_eleven_card_centralizer
    (stabCo2Equiv c0) (by rw [MulEquiv.orderOf_eq, hoc])
  rw [card_centralizer_mulEquiv_apply] at h11
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer C u)
  rw [MulAction.index_stabilizer] at h1
  have h2 : (MulAction.orbit C u).ncard ≤ (xFix Y).ncard :=
    Set.ncard_le_ncard horb (Set.toFinite _)
  rw [← h1, Nat.mul_comm (xFix Y).ncard]
  exact Nat.mul_le_mul (hstab.trans h11.le) h2

end Orbit

theorem co1_of_GA {Y E : GL24} (hY : Y ∈ GA) (hE : E ∈ GA) (hoY : orderOf Y = 11)
    (hoE : orderOf E = 3) (hEY : E * Y = Y * E)
    (hC : Nat.card (GA ⊓ Subgroup.centralizer {Y} : Subgroup GL24) ≤ 66)
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≤ 66 ∧
      3 ∣ Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Finite CFSG.Blueprint.NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have : Finite GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have hy' : orderOf (co1MatEquiv.symm (⟨Y, hY⟩ : GA)) = 11 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hoY]
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.Co1).factorization 11 = 1 := by
    rw [CFSG.Sporadic.Co1.card_Co1,
      show (4157776806543360000 : ℕ) = 11 * 377979709685760000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one hfac hy' hx
  have hk1 : (co1MatEquiv.symm (⟨Y, hY⟩ : GA)) ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    norm_num at hx
  have hCx : Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) := by
    rw [hxk, card_centralizer_conj_eq, centralizer_pow_eq_of_prime hy' hk1,
      card_centralizer_mulEquiv_apply]
  rw [hCx]
  refine ⟨le_trans ?_ hC, ?_⟩
  · have hz : ∀ z : Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA),
        ((z : GA) : GL24) ∈ GA ⊓ Subgroup.centralizer {Y} := by
      intro z
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 z.2)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact Subgroup.mem_inf.2 ⟨(z : GA).2, Subgroup.mem_centralizer_singleton_iff.2 h1⟩
    refine Nat.card_le_card_of_injective (fun z => ⟨((z : GA) : GL24), hz z⟩) ?_
    intro a b e
    simp only [Subtype.mk.injEq] at e
    exact Subtype.ext (Subtype.ext e)
  · have hEc : (⟨E, hE⟩ : GA) ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hEY
    have he3 : orderOf (⟨⟨E, hE⟩, hEc⟩ :
        Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hoE]
    rw [← he3]
    exact orderOf_dvd_natCard _

theorem ne_one_of_fix_le {Y : GL24}
    (hfix : {v : Vec24 | (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}.ncard ≤ 2 ^ (24 - 20)) :
    Y ≠ 1 := by
  rintro rfl
  have huniv : {v : Vec24 | ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} =
      Set.univ := Set.eq_univ_of_forall fun v => mulVec_one' v
  rw [huniv, Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hfix
  norm_num at hfix

theorem ncard_xFix_le {Y : GL24}
    (hfix : {v : Vec24 | (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}.ncard ≤ 2 ^ (24 - 20))
    {S : Finset Vec24} (hS : S.card = 10)
    (hSf : ∀ v ∈ S, (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧ v ∉ certX) :
    (xFix Y).ncard ≤ 6 := by
  have hsub : xFix Y ⊆ {v : Vec24 | (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} \ ↑S :=
    fun v hv => ⟨hv.2, fun hvS => (hSf v hvS).2 hv.1⟩
  have hSF : (↑S : Set Vec24) ⊆ {v : Vec24 | (Y : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} :=
    fun v hv => (hSf v hv).1
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_diff hSF (Set.toFinite _), Set.ncard_coe_finset, hS] at h1
  have h2 : 2 ^ (24 - 20) = 16 := rfl
  omega

theorem co1_eleven_of_check {mem : Nat → Bool} {b0 b1 : Nat} {derivs : List (List Nat)}
    {RS RIS W NF : List Nat} {U : Nat}
    (h : elevenFixOK mem [b0, b1] derivs RS RIS W NF U 52 53 11 3 20 10 = true)
    (hA : MRep (unpackR 24 b0) A₁) (hB : MRep (unpackR 24 b1) A₂)
    (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX)
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≤ 66 ∧
      3 ∣ Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) := by
  obtain ⟨Y, E, hY, hE, hY11, hE3, hE1, hEY, hfix, ⟨S, hS, hSf⟩, hU⟩ :=
    elevenFix_sound h hA hB hmem
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hoY : orderOf Y = 11 := orderOf_eq_prime hY11 (ne_one_of_fix_le hfix)
  have hoE : orderOf E = 3 := orderOf_eq_prime hE3 hE1
  have hx6 := ncard_xFix_le hfix hS hSf
  have hC : Nat.card (GA ⊓ Subgroup.centralizer {Y} : Subgroup GL24) ≤ 66 :=
    (card_cent_le_of_fix hY hoY hU).trans (by omega)
  exact co1_of_GA hY hE hoY hoE hEY hC x hx

end CFSG.KC.Co1ElevenGlue

end


module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveLeaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import CFSG.Open.GLADefs
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  Timmesfeld.Co1Five Matrix

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

noncomputable def gElts : List GL24 := dagG [A₁, A₂] (dagWords.map Native.decWord)

theorem base_mem : ∀ g ∈ ([A₁, A₂] : List GL24), g ∈ GA := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h
  · rw [h]; exact A₁_mem
  · rw [h]; exact A₂_mem

theorem gElts_mem : ∀ g ∈ gElts, g ∈ GA := by
  unfold gElts
  exact dagG_mem base_mem _

noncomputable def gE (k : ℕ) : ↥GA := ⟨gElts.getD k 1, getD_mem_of_forall gElts_mem k⟩

abbrev gRows : List Rows := (gDag Native.aR Native.bR).1

section Rep

theorem rep_gE (hflag : (gDag Native.aR Native.bR).2.2 = true) (k : ℕ) :
    MRep (rowAt gRows k) ((gE k : ↥GA) : GL24) := by
  have hb : List.Forall₂ MRep [Native.aR, Native.bR] [A₁, A₂] :=
    List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)
  have h := dag_rep hb (dagWords.map Native.decWord) hflag
  exact getD_rep h MRep.one k

end Rep

theorem globalOK_parts {aR bR : Rows} (h : globalOK aR bR = true) :
    (gDag aR bR).2.2 = true ∧ qOK (gDag aR bR).1 = true ∧ a0OK (gDag aR bR).1 = true ∧
      fusOK (gDag aR bR).1 = true ∧ planeOK (gDag aR bR).1 = true := by
  unfold globalOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem a0OK_parts {rs : List Rows} (h : a0OK rs = true) :
    (∀ i < 3, validRows (rowAt rs (idxD.getD i 0)) = true ∧
      Native.pow (rowAt rs (idxD.getD i 0)) 5 = Native.one () ∧
      ∀ j < 3, Native.mul (rowAt rs (idxD.getD i 0)) (rowAt rs (idxD.getD j 0)) =
        Native.mul (rowAt rs (idxD.getD j 0)) (rowAt rs (idxD.getD i 0))) ∧
    distinctKeys ((List.range 125).map fun k => rowsKey (a0Row rs k)) = true := by
  unfold a0OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun i hi => by
    obtain ⟨⟨a, b⟩, c⟩ := h1 i hi
    exact ⟨a, b, c⟩, h2⟩

section Elts

noncomputable def dE (i : Fin 3) : ↥GA := gE (idxD.getD i.val 0)

abbrev GOK : Prop := globalOK Native.aR Native.bR = true

theorem dE_pow (hG : GOK) (i : Fin 3) : dE i ^ 5 = 1 := by
  obtain ⟨hv, hp, -⟩ := (a0OK_parts (globalOK_parts hG).2.2.1).1 i.val i.2
  have h := (rep_gE (globalOK_parts hG).1 (idxD.getD i.val 0)).pow 5
  rw [hp] at h
  have h1 : ((dE i : ↥GA) : GL24) ^ 5 = 1 := h.eq MRep.one
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h1

theorem dE_comm (hG : GOK) (i j : Fin 3) : dE i * dE j = dE j * dE i := by
  obtain ⟨-, -, hc⟩ := (a0OK_parts (globalOK_parts hG).2.2.1).1 i.val i.2
  have h := hc j.val j.2
  have r1 := (rep_gE (globalOK_parts hG).1 (idxD.getD i.val 0)).mul
    (rep_gE (globalOK_parts hG).1 (idxD.getD j.val 0))
  have r2 := (rep_gE (globalOK_parts hG).1 (idxD.getD j.val 0)).mul
    (rep_gE (globalOK_parts hG).1 (idxD.getD i.val 0))
  rw [h] at r1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact r1.eq r2

noncomputable def φ (hG : GOK) : Multiplicative (Fin 3 → ZMod 5) →* ↥GA :=
  Co3T.vecProdHom (p := 5) dE (fun i j => dE_comm hG i j) (dE_pow hG)

theorem φ_apply (hG : GOK) (a : Fin 3 → ZMod 5) :
    φ hG (Multiplicative.ofAdd a) = Co3T.vecProd dE a := rfl

theorem vecProd_eq (a : Fin 3 → ZMod 5) : Co3T.vecProd dE a =
    dE 0 ^ (a 0).val * (dE 1 ^ (a 1).val * dE 2 ^ (a 2).val) := by
  simp [Co3T.vecProd, List.finRange_succ]

def vec3 (k : ℕ) : Fin 3 → ZMod 5 :=
  ![((k % 5 : ℕ) : ZMod 5), (((k / 5) % 5 : ℕ) : ZMod 5), ((k / 25 : ℕ) : ZMod 5)]

def idx3 (a : Fin 3 → ZMod 5) : ℕ := (a 0).val + 5 * (a 1).val + 25 * (a 2).val

theorem idx3_lt (a : Fin 3 → ZMod 5) : idx3 a < 125 := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  unfold idx3
  omega

theorem vec3_idx3 (a : Fin 3 → ZMod 5) : vec3 (idx3 a) = a := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  funext i
  fin_cases i
  · show (((idx3 a) % 5 : ℕ) : ZMod 5) = a 0
    rw [show idx3 a % 5 = (a 0).val by unfold idx3; omega, ZMod.natCast_zmod_val]
  · show ((((idx3 a) / 5) % 5 : ℕ) : ZMod 5) = a 1
    rw [show idx3 a / 5 % 5 = (a 1).val by unfold idx3; omega, ZMod.natCast_zmod_val]
  · show (((idx3 a) / 25 : ℕ) : ZMod 5) = a 2
    rw [show idx3 a / 25 = (a 2).val by unfold idx3; omega, ZMod.natCast_zmod_val]

theorem rep_a0Row (hG : GOK) {k : ℕ} (hk : k < 125) :
    MRep (a0Row gRows k) ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) := by
  rw [φ_apply, vecProd_eq]
  have hd := fun i : Fin 3 => rep_gE (globalOK_parts hG).1 (idxD.getD i.val 0)
  have : MRep (a0Row gRows k) ((dE 0 : GL24) ^ (k % 5) * ((dE 1 : GL24) ^ ((k / 5) % 5) *
      (dE 2 : GL24) ^ (k / 25))) :=
    ((hd 0).pow _).mul (((hd 1).pow _).mul ((hd 2).pow _))
  have e3 : k / 25 % 5 = k / 25 := Nat.mod_eq_of_lt (by omega)
  convert this using 1
  show ((dE 0 ^ ((((k % 5 : ℕ) : ZMod 5)).val) * (dE 1 ^ ((((k / 5 % 5 : ℕ) : ZMod 5)).val) *
    dE 2 ^ ((((k / 25 : ℕ) : ZMod 5)).val)) : ↥GA) : GL24) = _
  rw [ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, e3]
  simp only [Nat.mod_mod, Subgroup.coe_mul, Subgroup.coe_pow]

theorem validRows_a0Row (hG : GOK) (k : ℕ) : validRows (a0Row gRows k) = true := by
  have hd := fun i : Fin 3 => ((a0OK_parts (globalOK_parts hG).2.2.1).1 i.val i.2).1
  exact validRows_mul' (validRows_pow (hd 0) _) (validRows_mul' (validRows_pow (hd 1) _)
    (validRows_pow (hd 2) _))

theorem φ_injective (hG : GOK) : Function.Injective (φ hG) := by
  intro a b hab
  have ha := rep_a0Row hG (idx3_lt a.toAdd)
  have hb := rep_a0Row hG (idx3_lt b.toAdd)
  rw [vec3_idx3, ofAdd_toAdd] at ha hb
  rw [← hab] at hb
  have hrows : a0Row gRows (idx3 a.toAdd) = a0Row gRows (idx3 b.toAdd) :=
    rows_eq_of_mrep (validRows_a0Row hG _) (validRows_a0Row hG _) ha hb
  have hnd := CFSG.Sporadic.Co1.Module.distinctKeys_nodup
    (a0OK_parts (globalOK_parts hG).2.2.1).2
  have hk : idx3 a.toAdd = idx3 b.toAdd :=
    List.inj_on_of_nodup_map hnd (List.mem_range.2 (idx3_lt _)) (List.mem_range.2 (idx3_lt _))
      (by rw [hrows])
  have := congrArg vec3 hk
  rw [vec3_idx3, vec3_idx3] at this
  exact Multiplicative.toAdd.injective this

noncomputable def A0 (hG : GOK) : Subgroup ↥GA := (φ hG).range

theorem card_A0 (hG : GOK) : Nat.card (A0 hG) = 125 := by
  rw [A0, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (φ_injective hG),
    Subgroup.card_top, Co3T.card_vec]
  norm_num

theorem A0_comm (hG : GOK) : ∀ x ∈ A0 hG, ∀ y ∈ A0 hG, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem A0_pow (hG : GOK) : ∀ x ∈ A0 hG, x ^ 5 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 5 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, show ((5 : ℕ) : ZMod 5) = 0 from rfl,
      zero_mul]
  rw [this, map_one]

theorem A0_elemAbelian (hG : GOK) : IsElemAbelian 5 (A0 hG) :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (A0_comm hG _ a.2 _ b.2),
    fun x hx => A0_pow hG x hx⟩

theorem qOK_parts {rs : List Rows} (h : qOK rs = true) :
    gtOK (qGens rs).toArray (qTree rs) = true ∧ (qTree rs).pts.size = 625 ∧
      ∀ x ∈ (qTree rs).pts.toList, Native.pow x 5 = Native.one () := by
  unfold qOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < (qTree rs).pts.size := by simpa using hi
  have := h3 i hi'
  simpa using this

noncomputable def qG (l : ℕ) : ↥GA := gE (idxQ.getD l 0)

theorem qGens_getElem (l : ℕ) (hl : l < (qGens gRows).toArray.size) :
    (qGens gRows).toArray[l]! = rowAt gRows (idxQ.getD l 0) := by
  have hl' : l < idxQ.length := by simpa [qGens] using hl
  rw [getElem!_pos _ l hl]
  simp [qGens, List.getD_eq_getElem?_getD, hl']

theorem qG_rep (hG : GOK) :
    ∀ l < (qGens gRows).toArray.size,
      μG (qG l) = rowsMatrix 24 (qGens gRows).toArray[l]! := by
  intro l hl
  rw [qGens_getElem l hl, μG_apply]
  exact (rep_gE (globalOK_parts hG).1 _).symm

noncomputable def Qsub : Subgroup ↥GA :=
  Subgroup.closure (qG '' {l | l < (qGens gRows).toArray.size})

theorem card_Qsub (hG : GOK) : Nat.card Qsub = 625 := by
  obtain ⟨hok, hsz, -⟩ := qOK_parts (globalOK_parts hG).2.1
  have := CFSG.Sporadic.Co1Block.prodTree_card μG μG_injective hok qG (qG_rep hG)
  rw [Qsub, this, hsz]

theorem factorization_card_GA_five :
    (Nat.card ↥GA).factorization 5 = 4 := by
  rw [card_GA_eq, show (4157776806543360000 : ℕ) = 5 ^ 4 * 6652442890469376 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem fusOK_parts {rs : List Rows} (h : fusOK rs = true) :
    (∀ q ∈ (qTree rs).pts.toList, q ∈ (List.range 125).map (a0Row rs) ∨
      q ∈ (List.range 20).flatMap (conjList rs)) ∧
    ∀ j < 20, Native.mul (rowAt rs (idxC.getD j 0)) (Native.inv (rowAt rs (idxC.getD j 0))) =
        Native.one () ∧
      Native.mul (Native.mul (rowAt rs (idxC.getD j 0)) (rowAt rs (idxR.getD j 0)))
        (Native.inv (rowAt rs (idxC.getD j 0))) ∈ (List.range 125).map (a0Row rs) := by
  unfold fusOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq, Bool.or_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun q hq => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    have hi' : i < (qTree rs).pts.size := by simpa using hi
    have := h1 i hi'
    simpa using this
  · exact h2 j hj

theorem fusion_exists (hG : GOK) (s : ↥GA) (hs : orderOf s = 5) :
    ∃ c : ↥GA, ∃ a : Fin 3 → ZMod 5, c * s * c⁻¹ = φ hG (Multiplicative.ofAdd a) := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hflag, hq, -, hf, -⟩ := globalOK_parts hG
  obtain ⟨hok, hsz, hord⟩ := qOK_parts hq
  have hQcard : Nat.card Qsub = 5 ^ (Nat.card (⊤ : Subgroup ↥GA)).factorization 5 := by
    rw [card_Qsub hG, Subgroup.card_top, factorization_card_GA_five]; norm_num
  obtain ⟨g, -, hgq⟩ := Co3T.exists_conj_mem_of_full (le_top : Qsub ≤ ⊤) hQcard
    (Subgroup.mem_top s) hs
  obtain ⟨f, hfrow, -, hfeq⟩ := CFSG.Sporadic.Co1Block.prodTree_closure_eq μG μG_injective hok qG
    (qG_rep hG)
  have hqmem : g⁻¹ * s * g ∈ (Subgroup.closure (qG '' {l | l < (qGens gRows).toArray.size}) :
      Set ↥GA) := hgq
  rw [hfeq] at hqmem
  obtain ⟨i, hi, hiq⟩ := hqmem
  have hirep : MRep (qTree gRows).pts[i]! ((g⁻¹ * s * g : ↥GA) : GL24) := by
    unfold MRep
    rw [← hiq, ← μG_apply, hfrow i hi]
  have hi2 : i < (qTree gRows).pts.size := hi
  have hpt : (qTree gRows).pts[i]! ∈ (qTree gRows).pts.toList := by
    rw [getElem!_pos _ i hi2]
    exact Array.getElem_mem_toList hi2
  have hfp := fusOK_parts hf
  rcases hfp.1 _ hpt with hA | hB
  ·
    obtain ⟨k, hk, hkrow⟩ := List.mem_map.1 hA
    have hk' : k < 125 := List.mem_range.1 hk
    rw [← hkrow] at hirep
    have hq : ((g⁻¹ * s * g : ↥GA) : GL24) = ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) :
        GL24) := hirep.eq (rep_a0Row hG hk')
    refine ⟨g⁻¹, vec3 k, ?_⟩
    rw [inv_inv]
    exact Subtype.ext hq
  ·
    obtain ⟨j, hj, hjm⟩ := List.mem_flatMap.1 hB
    have hj' : j < 20 := List.mem_range.1 hj
    obtain ⟨y, hy, hyrow⟩ := List.mem_map.1 hjm
    obtain ⟨i', hi', hyi⟩ := List.getElem_of_mem hy
    have hi'' : i' < (qTree gRows).pts.size := by simpa using hi'
    set yel := f i' with hyel
    have hyrep : MRep y ((yel : ↥GA) : GL24) := by
      unfold MRep
      rw [← hyi, ← μG_apply, hfrow i' hi'']
      simp [getElem!_pos (qTree gRows).pts i' hi'']
    have hy5 : yel ^ 5 = 1 := by
      have h := hyrep.pow 5
      rw [hord y hy] at h
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h.eq MRep.one
    have hy4 : yel ^ 4 = yel⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      simpa using hy5
    have hr := rep_gE hflag (idxR.getD j 0)
    have hconj : ((g⁻¹ * s * g : ↥GA) : GL24) =
        ((yel * gE (idxR.getD j 0) * yel ^ 4 : ↥GA) : GL24) := by
      have h := (hyrep.mul hr).mul (hyrep.pow 4)
      rw [← hyrow] at hirep
      have e : ((yel * gE (idxR.getD j 0) * yel ^ 4 : ↥GA) : GL24) =
          ((yel : ↥GA) : GL24) * ((gE (idxR.getD j 0) : ↥GA) : GL24) *
            ((yel : ↥GA) : GL24) ^ 4 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [e]
      exact hirep.eq h
    have hq : g⁻¹ * s * g = yel * gE (idxR.getD j 0) * yel⁻¹ := by
      rw [← hy4]
      exact Subtype.ext hconj
    have hc := rep_gE hflag (idxC.getD j 0)
    obtain ⟨hinv, hmemA⟩ := hfp.2 j hj'
    have hcinv : MRep (Native.inv (rowAt gRows (idxC.getD j 0)))
        (((gE (idxC.getD j 0) : ↥GA) : GL24)⁻¹) := hc.inv hinv
    obtain ⟨k, hk, hkrow⟩ := List.mem_map.1 hmemA
    have hk' : k < 125 := List.mem_range.1 hk
    have hcr := (hc.mul hr).mul hcinv
    rw [← hkrow] at hcr
    have hcj : ((gE (idxC.getD j 0) * gE (idxR.getD j 0) * (gE (idxC.getD j 0))⁻¹ : ↥GA) :
        GL24) = ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) := by
      have := (rep_a0Row hG hk').eq hcr
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact this.symm
    refine ⟨gE (idxC.getD j 0) * yel⁻¹ * g⁻¹, vec3 k, ?_⟩
    rw [← Subtype.ext hcj]
    calc gE (idxC.getD j 0) * yel⁻¹ * g⁻¹ * s * (gE (idxC.getD j 0) * yel⁻¹ * g⁻¹)⁻¹
        = gE (idxC.getD j 0) * yel⁻¹ * (g⁻¹ * s * g) * yel * (gE (idxC.getD j 0))⁻¹ := by group
      _ = gE (idxC.getD j 0) * gE (idxR.getD j 0) * (gE (idxC.getD j 0))⁻¹ := by
        rw [hq]; group

theorem planeOK_parts {rs : List Rows} (h : planeOK rs = true) :
    (∀ p < 31, planeT.getD p 0 < 3 ∧ planeA.getD p 0 < 125 ∧ planeB.getD p 0 < 125 ∧
      Native.mul (rowAt rs (idxPC.getD p 0)) (Native.inv (rowAt rs (idxPC.getD p 0))) =
        Native.one () ∧
      Native.mul (Native.mul (rowAt rs (idxPC.getD p 0)) (a0Row rs (repA.getD (planeT.getD p 0) 0)))
        (Native.inv (rowAt rs (idxPC.getD p 0))) = a0Row rs (planeA.getD p 0) ∧
      Native.mul (Native.mul (rowAt rs (idxPC.getD p 0)) (a0Row rs (repB.getD (planeT.getD p 0) 0)))
        (Native.inv (rowAt rs (idxPC.getD p 0))) = a0Row rs (planeB.getD p 0) ∧
      dot5 (planeF.getD p []) (digitsOf (planeA.getD p 0)) = 0 ∧
      dot5 (planeF.getD p []) (digitsOf (planeB.getD p 0)) = 0) ∧
    (∀ k < 125, k = 0 ∨ ∃ p < 31, ∃ c < 5, 1 ≤ c ∧
      digitsOf k = scale5 c ((planeF.getD p []).getD 0 0, (planeF.getD p []).getD 1 0,
        (planeF.getD p []).getD 2 0)) ∧
    (∀ τ < 3, repA.getD τ 0 < 125 ∧ repB.getD τ 0 < 125 ∧
      gtOK [a0Row rs (repA.getD τ 0), a0Row rs (repB.getD τ 0)].toArray
        (gtBFS [a0Row rs (repA.getD τ 0), a0Row rs (repB.getD τ 0)].toArray 100000) = true ∧
      (gtBFS [a0Row rs (repA.getD τ 0),
        a0Row rs (repB.getD τ 0)].toArray 100000).pts.size = 25) := by
  unfold planeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun p hp => ?_, fun k hk => ?_, fun τ hτ => ?_⟩
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩ := h1 p hp
    exact ⟨a, b, c, g, i, j, d, e⟩
  · rcases h2 k hk with h | ⟨p, hp, c, hc, hc1, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, c, hc, hc1, hd⟩
  · obtain ⟨⟨a, b⟩, c, d⟩ := h3 τ hτ
    exact ⟨a, b, c, d⟩

noncomputable def gensGL (hG : GOK) (τ : ℕ) : List GL24 :=
  [((φ hG (Multiplicative.ofAdd (vec3 (repA.getD τ 0))) : ↥GA) : GL24),
    ((φ hG (Multiplicative.ofAdd (vec3 (repB.getD τ 0))) : ↥GA) : GL24)] ++
    (idxH.getD τ []).map (fun k => gElts.getD k 1)

noncomputable def g1 (hG : GOK) (τ : ℕ) : ↥GA :=
  φ hG (Multiplicative.ofAdd (vec3 (repA.getD τ 0)))

noncomputable def g2 (hG : GOK) (τ : ℕ) : ↥GA :=
  φ hG (Multiplicative.ofAdd (vec3 (repB.getD τ 0)))

noncomputable def cP (p : ℕ) : ↥GA := gE (idxPC.getD p 0)

noncomputable def xP (hG : GOK) (p : ℕ) : ↥GA :=
  φ hG (Multiplicative.ofAdd (vec3 (planeA.getD p 0)))

noncomputable def yP (hG : GOK) (p : ℕ) : ↥GA :=
  φ hG (Multiplicative.ofAdd (vec3 (planeB.getD p 0)))

theorem xP_eq (hG : GOK) {p : ℕ} (hp : p < 31) :
    xP hG p = cP p * g1 hG (planeT.getD p 0) * (cP p)⁻¹ := by
  obtain ⟨hflag, -, -, -, hpl⟩ := globalOK_parts hG
  obtain ⟨hτ, hα, hβ, hinv, hx, hy, -, -⟩ := (planeOK_parts hpl).1 p hp
  have hlt := (planeOK_parts hpl).2.2 _ hτ
  have hc := rep_gE hflag (idxPC.getD p 0)
  have hcinv : MRep (Native.inv (rowAt gRows (idxPC.getD p 0))) ((cP p : ↥GA) : GL24)⁻¹ :=
    hc.inv hinv
  have h1 : MRep (a0Row gRows (repA.getD (planeT.getD p 0) 0))
      ((g1 hG (planeT.getD p 0) : ↥GA) : GL24) :=
    rep_a0Row hG hlt.1
  have h := (hc.mul h1).mul hcinv
  rw [hx] at h
  apply Subtype.ext
  have := (rep_a0Row hG hα).eq h
  simpa only [xP, cP, Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem yP_eq (hG : GOK) {p : ℕ} (hp : p < 31) :
    yP hG p = cP p * g2 hG (planeT.getD p 0) * (cP p)⁻¹ := by
  obtain ⟨hflag, -, -, -, hpl⟩ := globalOK_parts hG
  obtain ⟨hτ, hα, hβ, hinv, hx, hy, -, -⟩ := (planeOK_parts hpl).1 p hp
  have hlt := (planeOK_parts hpl).2.2 _ hτ
  have hc := rep_gE hflag (idxPC.getD p 0)
  have hcinv : MRep (Native.inv (rowAt gRows (idxPC.getD p 0))) ((cP p : ↥GA) : GL24)⁻¹ :=
    hc.inv hinv
  have h1 : MRep (a0Row gRows (repB.getD (planeT.getD p 0) 0))
      ((g2 hG (planeT.getD p 0) : ↥GA) : GL24) :=
    rep_a0Row hG hlt.2.1
  have h := (hc.mul h1).mul hcinv
  rw [hy] at h
  apply Subtype.ext
  have := (rep_a0Row hG hβ).eq h
  simpa only [yP, cP, Subgroup.coe_mul, Subgroup.coe_inv] using this

section Planes

theorem card_plane_rep (hG : GOK) {τ : ℕ} (hτ : τ < 3) :
    Nat.card (Subgroup.closure ({g1 hG τ, g2 hG τ} : Set ↥GA)) = 25 := by
  obtain ⟨hflag, -, -, -, hpl⟩ := globalOK_parts hG
  obtain ⟨h1, h2, hok, hsz⟩ := (planeOK_parts hpl).2.2 τ hτ
  set gg : ℕ → ↥GA := fun l => if l = 0 then g1 hG τ else g2 hG τ with hgg
  have hrep : ∀ l < ([a0Row gRows (repA.getD τ 0), a0Row gRows (repB.getD τ 0)] :
      List Rows).toArray.size,
      μG (gg l) = rowsMatrix 24 ([a0Row gRows (repA.getD τ 0),
        a0Row gRows (repB.getD τ 0)] : List Rows).toArray[l]! := by
    intro l hl
    have hl2 : l < 2 := by simpa using hl
    interval_cases l
    · simpa [hgg, g1, μG_apply] using (rep_a0Row hG h1).symm
    · simpa [hgg, g2, μG_apply] using (rep_a0Row hG h2).symm
  have hcard := CFSG.Sporadic.Co1Block.prodTree_card μG μG_injective hok gg hrep
  rw [hsz] at hcard
  have hset : gg '' {l | l < ([a0Row gRows (repA.getD τ 0), a0Row gRows (repB.getD τ 0)] :
      List Rows).toArray.size} = {g1 hG τ, g2 hG τ} := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.size_toArray, List.length_cons,
      List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have : l < 2 := by simpa using hl
      interval_cases l <;> simp [hgg]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, by simp [hgg]⟩
      · exact ⟨1, by simp, by simp [hgg]⟩
  rw [hset] at hcard
  exact hcard

theorem card_plane (hG : GOK) {p : ℕ} (hp : p < 31) :
    Nat.card (Subgroup.closure ({xP hG p, yP hG p} : Set ↥GA)) = 25 := by
  have hτ := ((planeOK_parts (globalOK_parts hG).2.2.2.2).1 p hp).1
  rw [xP_eq hG hp, yP_eq hG hp, card_closure_pair_conj, card_plane_rep hG hτ]

theorem digitsOf_idx3 (a : Fin 3 → ZMod 5) :
    digitsOf (idx3 a) = ((a 0).val, (a 1).val, (a 2).val) := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  unfold digitsOf idx3
  ext <;> simp <;> omega

theorem idx3_eq_zero {a : Fin 3 → ZMod 5} (h : idx3 a = 0) : a = 0 := by
  have := vec3_idx3 a
  rw [h] at this
  rw [← this]
  funext i
  fin_cases i <;> simp [vec3]

theorem sum_vec3 (f : Fin 3 → ZMod 5) (c : ℕ) (fl : List ℕ)
    (hf : ∀ i : Fin 3, f i = (c : ZMod 5) * ((fl.getD i.val 0 : ℕ) : ZMod 5)) (k : ℕ)
    (hdot : dot5 fl (digitsOf k) = 0) : ∑ i, f i * vec3 k i = 0 := by
  rw [Fin.sum_univ_three, hf 0, hf 1, hf 2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  have h : ((fl.getD 0 0 * (k % 5) + fl.getD 1 0 * (k / 5 % 5) + fl.getD 2 0 * (k / 25) : ℕ) :
      ZMod 5) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero hdot
  simp only [vec3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have h' : (c : ZMod 5) * (((fl.getD 0 0 * (k % 5) + fl.getD 1 0 * (k / 5 % 5) +
      fl.getD 2 0 * (k / 25) : ℕ) : ZMod 5)) = 0 := by rw [h, mul_zero]
  push_cast at h'
  linear_combination h'

theorem functional_coords {f : Fin 3 → ZMod 5} {c : ℕ} {fl : List ℕ}
    (hc : digitsOf (idx3 f) = (c * fl.getD 0 0 % 5, c * fl.getD 1 0 % 5, c * fl.getD 2 0 % 5)) :
    ∀ i : Fin 3, f i = (c : ZMod 5) * ((fl.getD i.val 0 : ℕ) : ZMod 5) := by
  rw [digitsOf_idx3] at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨d0, d1, d2⟩ := hc
  intro i
  fin_cases i
  · show f 0 = (c : ZMod 5) * ((fl.getD 0 0 : ℕ) : ZMod 5)
    rw [← ZMod.natCast_zmod_val (f 0), d0, ZMod.natCast_mod]
    push_cast; rfl
  · show f 1 = (c : ZMod 5) * ((fl.getD 1 0 : ℕ) : ZMod 5)
    rw [← ZMod.natCast_zmod_val (f 1), d1, ZMod.natCast_mod]
    push_cast; rfl
  · show f 2 = (c : ZMod 5) * ((fl.getD 2 0 : ℕ) : ZMod 5)
    rw [← ZMod.natCast_zmod_val (f 2), d2, ZMod.natCast_mod]
    push_cast; rfl

theorem plane_eq (hG : GOK) {B : Subgroup ↥GA} (hB : B ≤ A0 hG)
    (hidx : B.relIndex (A0 hG) = 5) :
    ∃ p < 31, B = Subgroup.closure ({xP hG p, yP hG p} : Set ↥GA) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, -, -, -, hpl⟩ := globalOK_parts hG
  obtain ⟨hplane, hcov, -⟩ := planeOK_parts hpl
  have hBcard : Nat.card B = 25 := by
    have h := Subgroup.relIndex_mul_card B (A0 hG)
    rw [inf_eq_left.2 hB, hidx, card_A0 hG] at h
    omega
  obtain ⟨f, hf0, hf⟩ := Co3T.exists_dot_eq_zero_imp_mem (φ hG) (φ_injective hG)
    (hB : B ≤ (φ hG).range) (by rw [hBcard]; norm_num)
  have hk0 : idx3 f ≠ 0 := fun h => hf0 (idx3_eq_zero h)
  obtain ⟨p, hp, c, hc, hc1, hdig⟩ := (hcov (idx3 f) (idx3_lt f)).resolve_left hk0
  have hfi := functional_coords (f := f) (c := c) (fl := planeF.getD p []) hdig
  obtain ⟨-, hα, hβ, -, -, -, hdα, hdβ⟩ := hplane p hp
  have hx : xP hG p ∈ B := hf _ (sum_vec3 f c _ hfi _ hdα)
  have hy : yP hG p ∈ B := hf _ (sum_vec3 f c _ hfi _ hdβ)
  have hle : Subgroup.closure ({xP hG p, yP hG p} : Set ↥GA) ≤ B := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  refine ⟨p, hp, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [card_plane hG hp, hBcard]

end Planes

end Elts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

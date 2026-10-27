module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22Cent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRank
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import Certificates.Certificate9462

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent

open scoped Pointwise

open CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native

variable {G : Type*} [Group G]

@[expose] def pairHomFin (U V : G) (hU : U ^ 3 = 1) (hV : V ^ 3 = 1)
    (hcomm : U * V = V * U) : Multiplicative (Fin 2 → ZMod 3) →* G where
  toFun v := U ^ (Multiplicative.toAdd v 0).val * V ^ (Multiplicative.toAdd v 1).val
  map_one' := by simp
  map_mul' v w := by
    have hcm : ∀ (m k : ℕ), Commute (U ^ m) (V ^ k) := fun m k => Commute.pow_pow hcomm m k
    have hUadd : ∀ a b : ZMod 3, U ^ (a + b).val = U ^ a.val * U ^ b.val := by
      intro a b
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hU, pow_add]
    have hVadd : ∀ a b : ZMod 3, V ^ (a + b).val = V ^ a.val * V ^ b.val := by
      intro a b
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hV, pow_add]
    simp only [toAdd_mul, Pi.add_apply, hUadd, hVadd]
    calc
      U ^ (Multiplicative.toAdd v 0).val * U ^ (Multiplicative.toAdd w 0).val *
          (V ^ (Multiplicative.toAdd v 1).val * V ^ (Multiplicative.toAdd w 1).val) =
          U ^ (Multiplicative.toAdd v 0).val *
            (U ^ (Multiplicative.toAdd w 0).val * V ^ (Multiplicative.toAdd v 1).val) *
            V ^ (Multiplicative.toAdd w 1).val := by
            simp only [mul_assoc]
      _ = U ^ (Multiplicative.toAdd v 0).val *
            (V ^ (Multiplicative.toAdd v 1).val * U ^ (Multiplicative.toAdd w 0).val) *
            V ^ (Multiplicative.toAdd w 1).val := by
            rw [(hcm _ _).eq]
      _ = (U ^ (Multiplicative.toAdd v 0).val * V ^ (Multiplicative.toAdd v 1).val) *
            (U ^ (Multiplicative.toAdd w 0).val * V ^ (Multiplicative.toAdd w 1).val) := by
            simp only [mul_assoc]

theorem pairHomFin_injective {U V : G} (hU : U ^ 3 = 1) (hV : V ^ 3 = 1)
    (hcomm : U * V = V * U)
    (hnt : ∀ a b : ZMod 3, (a, b) ≠ (0, 0) → U ^ a.val * V ^ b.val ≠ 1) :
    Function.Injective (pairHomFin U V hU hV hcomm) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  by_contra hne
  refine hnt (Multiplicative.toAdd v 0) (Multiplicative.toAdd v 1) ?_ ?_
  · intro h
    apply hne
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h
  · change U ^ (Multiplicative.toAdd v 0).val *
      V ^ (Multiplicative.toAdd v 1).val = 1 at hv
    exact hv

theorem pairHomFin_range {U V : G} (hU : U ^ 3 = 1) (hV : V ^ 3 = 1)
    (hcomm : U * V = V * U) :
    (pairHomFin U V hU hV hcomm).range = Subgroup.closure ({U, V} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    show U ^ (Multiplicative.toAdd v 0).val * V ^ (Multiplicative.toAdd v 1).val ∈ _
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · have hUmem : U ∈ (pairHomFin U V hU hV hcomm).range := by
      refine ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩
      show U ^ ((Pi.single 0 1 : Fin 2 → ZMod 3) 0).val *
        V ^ ((Pi.single 0 1 : Fin 2 → ZMod 3) 1).val = U
      have h1 : (1 : ZMod 3).val = 1 := rfl
      simp [Pi.single, h1]
    have hVmem : V ∈ (pairHomFin U V hU hV hcomm).range := by
      refine ⟨Multiplicative.ofAdd (Pi.single 1 1), ?_⟩
      show U ^ ((Pi.single 1 1 : Fin 2 → ZMod 3) 0).val *
        V ^ ((Pi.single 1 1 : Fin 2 → ZMod 3) 1).val = V
      have h1 : (1 : ZMod 3).val = 1 := rfl
      simp [Pi.single, h1]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hUmem, hVmem]

theorem isElemAbelian_card_closure_pair {U V : G} (hU : U ^ 3 = 1) (hV : V ^ 3 = 1)
    (hcomm : U * V = V * U)
    (hnt : ∀ a b : ZMod 3, (a, b) ≠ (0, 0) → U ^ a.val * V ^ b.val ≠ 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({U, V} : Set G)) ∧
      Nat.card (Subgroup.closure ({U, V} : Set G)) = 3 ^ 2 := by
  have hrange := pairHomFin_range hU hV hcomm
  have hinj := pairHomFin_injective hU hV hcomm hnt
  refine ⟨?_, ?_⟩
  · rw [← hrange]
    exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.isElemAbelian_range
      (pairHomFin U V hU hV hcomm)
  · rw [← hrange]
    exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_range_of_injective
      (pairHomFin U V hU hV hcomm) hinj

structure CentData (X Y Qi Qj U V : G) : Prop where
  X_pow : X ^ 5 = 1
  Y_pow : Y ^ 5 = 1
  XY_comm : X * Y = Y * X
  Qi_mem : Qi ∈ Subgroup.closure ({X, Y} : Set G)
  Qj_mem : Qj ∈ Subgroup.closure ({X, Y} : Set G)
  Qi_ne : Qi ≠ 1
  Qj_ne : Qj ≠ 1
  U_pow : U ^ 3 = 1
  V_pow : V ^ 3 = 1
  UV_comm : U * V = V * U
  U_Qi : U * Qi = Qi * U
  V_Qj : V * Qj = Qj * V
  prod_ne : ∀ a b : ZMod 3, (a, b) ≠ (0, 0) → U ^ a.val * V ^ b.val ≠ 1

theorem CentData.map {H : Type*} [Group H] {X Y Qi Qj U V : G}
    (D : CentData X Y Qi Qj U V) (ψ : G →* H) (hψ : Function.Injective ψ) :
    CentData (ψ X) (ψ Y) (ψ Qi) (ψ Qj) (ψ U) (ψ V) where
  X_pow := by rw [← map_pow, D.X_pow, map_one]
  Y_pow := by rw [← map_pow, D.Y_pow, map_one]
  XY_comm := by rw [← map_mul, ← map_mul, D.XY_comm]
  Qi_mem := by
    have := Subgroup.mem_map_of_mem ψ (D.Qi_mem)
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  Qj_mem := by
    have := Subgroup.mem_map_of_mem ψ (D.Qj_mem)
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  Qi_ne h := D.Qi_ne (hψ (by simpa using h))
  Qj_ne h := D.Qj_ne (hψ (by simpa using h))
  U_pow := by rw [← map_pow, D.U_pow, map_one]
  V_pow := by rw [← map_pow, D.V_pow, map_one]
  UV_comm := by rw [← map_mul, ← map_mul, D.UV_comm]
  U_Qi := by rw [← map_mul, ← map_mul, D.U_Qi]
  V_Qj := by rw [← map_mul, ← map_mul, D.V_Qj]
  prod_ne a b hab h :=
    D.prod_ne a b hab (hψ (by rw [map_mul, map_pow, map_pow, h, map_one]))

theorem CentData.pow_five {X Y Qi Qj U V : G} (D : CentData X Y Qi Qj U V) :
    ∀ g ∈ Subgroup.closure ({X, Y} : Set G), g ^ 5 = 1 :=
  pow_eq_one_of_mem_closure (GuestData.pairwise_commute D.XY_comm) <| by
    rintro s (rfl | rfl)
    exacts [D.X_pow, D.Y_pow]

theorem CentData.isElemAbelian {X Y Qi Qj U V : G} (D : CentData X Y Qi Qj U V) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({U, V} : Set G)) ∧
      Nat.card (Subgroup.closure ({U, V} : Set G)) = 3 ^ 2 :=
  isElemAbelian_card_closure_pair D.U_pow D.V_pow D.UV_comm D.prod_ne

theorem CentData.exists_of_sylow [Finite G] {X Y Qi Qj U V : G}
    (D : CentData X Y Qi Qj U V) (T : Sylow 5 G) :
    ∃ t ∈ (T : Subgroup G), ∃ t' ∈ (T : Subgroup G), t ≠ 1 ∧ t' ≠ 1 ∧
      ∃ x y : G, x * t = t * x ∧ y * t' = t' * y ∧
        CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({x, y} : Set G)) ∧
        Nat.card (Subgroup.closure ({x, y} : Set G)) = 3 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.closure ({X, Y} : Set G)) := fun g =>
    ⟨1, Subtype.ext (by simpa using D.pow_five g.1 g.2)⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let ψ : G ≃* G := MulAut.conj g
  let D' := D.map ψ.toMonoidHom ψ.injective
  have hT : (T : Subgroup G) = ψ • (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hQiT : ψ Qi ∈ (T : Subgroup G) := by
    rw [hT]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS D.Qi_mem)
  have hQjT : ψ Qj ∈ (T : Subgroup G) := by
    rw [hT]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS D.Qj_mem)
  have hQine : ψ Qi ≠ 1 := fun h => D.Qi_ne (ψ.injective (by simpa using h))
  have hQjne : ψ Qj ≠ 1 := fun h => D.Qj_ne (ψ.injective (by simpa using h))
  exact ⟨ψ Qi, hQiT, ψ Qj, hQjT, hQine, hQjne, ψ U, ψ V,
    D'.U_Qi, D'.V_Qj, D'.isElemAbelian⟩

section Soundness

variable {n : ℕ} [MulAction G (Fin n)]

theorem rep_signedTab (hn : n < 2 ^ 32) {x y : G} {α αi β βi : Table} (hx : Rep n α x)
    (hxi : Rep n αi x⁻¹) (hy : Rep n β y) (hyi : Rep n βi y⁻¹) (l : List Int) :
    Rep n (signedTab n α αi β βi l)
      ((l.map fun s => wordProd (img2 x y) (eLetterWord s)).prod) := by
  unfold signedTab
  induction l with
  | nil => exact Rep.idT hn
  | cons s l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    exact Rep.compT (rep_wordTab hn hx hxi hy hyi _) ih

theorem twoChecks_spec [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {U V Qi Qj : G}
    {Ut Vt Qit Qjt : Table}
    (hU : Rep n Ut U) (hV : Rep n Vt V) (hQi : Rep n Qit Qi) (hQj : Rep n Qjt Qj)
    (h : twoChecks n Ut Vt Qit Qjt = true) :
    U ^ 3 = 1 ∧ V ^ 3 = 1 ∧ U * V = V * U ∧ U * Qi = Qi * U ∧ V * Qj = Qj * V ∧
      ∀ a b : ZMod 3, (a, b) ≠ (0, 0) → U ^ a.val * V ^ b.val ≠ 1 := by
  unfold twoChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hU3, hV3⟩, hUV⟩, hUQi⟩, hVQj⟩, hprods⟩ := h
  have hpow : U ^ 3 = 1 := by
    have h2 := Rep.powT hn hU 3
    rw [hU3] at h2
    exact eq_one_of_rep_idT hn h2
  have hpowV : V ^ 3 = 1 := by
    have h2 := Rep.powT hn hV 3
    rw [hV3] at h2
    exact eq_one_of_rep_idT hn h2
  have hcomm : U * V = V * U := by
    have h2 := Rep.compT hU hV
    have h3 := Rep.compT hV hU
    rw [hUV] at h2
    exact eq_of_rep h2 h3
  have hcommQi : U * Qi = Qi * U := by
    have h2 := Rep.compT hU hQi
    have h3 := Rep.compT hQi hU
    rw [hUQi] at h2
    exact eq_of_rep h2 h3
  have hcommQj : V * Qj = Qj * V := by
    have h2 := Rep.compT hV hQj
    have h3 := Rep.compT hQj hV
    rw [hVQj] at h2
    exact eq_of_rep h2 h3
  refine ⟨hpow, hpowV, hcomm, hcommQi, hcommQj, fun a b hab => ?_⟩
  have ha : a.val ∈ [0, 1, 2] := by
    have := ZMod.val_lt a
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hb : b.val ∈ [0, 1, 2] := by
    have := ZMod.val_lt b
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hprods a.val ha b.val hb with hzero | hmoves
  · exfalso
    have hzero' : a.val = 0 ∧ b.val = 0 := by simpa using hzero
    obtain ⟨ha0, hb0⟩ := hzero'
    apply hab
    have ha' : a = 0 := (ZMod.val_eq_zero a).1 ha0
    have hb' : b = 0 := (ZMod.val_eq_zero b).1 hb0
    simp [ha', hb']
  · have hr := Rep.compT (Rep.powT hn hU a.val) (Rep.powT hn hV b.val)
    exact ne_one_of_movesPt hmoves hr

theorem centData_of_check [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {x y : G}
    {α αi β βi : Table} (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y)
    (hyi : Rep n βi y⁻¹) (h : centCheck n α αi β βi = true) :
    ∃ X Y Qi Qj U V : G, CentData X Y Qi Qj U V := by
  unfold centCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, hq1⟩, hq2⟩, h2⟩ := h
  have hrels := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h1
  let g := img2 x y
  let X := wordProd g wx
  let Y := wordProd g wy
  let Qi := wordProd g (qWord iC)
  let Qj := wordProd g (qWord jC)
  let U := (uData.map fun s => wordProd g (eLetterWord s)).prod
  let V := (vData.map fun s => wordProd g (eLetterWord s)).prod
  have hX : X ^ 5 = 1 := by
    have := hrels (wpow wx 5) (by simp)
    rwa [wordProd_wpow] at this
  have hY : Y ^ 5 = 1 := by
    have := hrels (wpow wy 5) (by simp)
    rwa [wordProd_wpow] at this
  have hXY : X * Y = Y * X := by
    have := hrels (wx ++ wy ++ winv wx ++ winv wy) (by simp)
    simp only [wordProd_append, wordProd_winv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hq : ∀ j, wordProd g (qWord j) ∈ Subgroup.closure ({X, Y} : Set G) := by
    have hXm : X ∈ Subgroup.closure ({X, Y} : Set G) := Subgroup.subset_closure (by simp)
    have hYm : Y ∈ Subgroup.closure ({X, Y} : Set G) := Subgroup.subset_closure (by simp)
    intro j
    rcases j with _ | _ | k
    · exact hXm
    · exact hYm
    · show wordProd g (wx ++ wpow wy (k + 1)) ∈ _
      rw [wordProd_append, wordProd_wpow]
      exact Subgroup.mul_mem _ hXm (Subgroup.pow_mem _ hYm _)
  have hQine : Qi ≠ 1 :=
    ne_one_of_movesPt hq1 (rep_wordTab hn hx hxi hy hyi (qWord iC))
  have hQjne : Qj ≠ 1 :=
    ne_one_of_movesPt hq2 (rep_wordTab hn hx hxi hy hyi (qWord jC))
  have hUrep : Rep n (signedTab n α αi β βi uData) U :=
    rep_signedTab hn hx hxi hy hyi uData
  have hVrep : Rep n (signedTab n α αi β βi vData) V :=
    rep_signedTab hn hx hxi hy hyi vData
  obtain ⟨hU3, hV3, hUV, hUQi, hVQj, hprods⟩ :=
    twoChecks_spec hn hUrep hVrep
      (rep_wordTab hn hx hxi hy hyi (qWord iC))
      (rep_wordTab hn hx hxi hy hyi (qWord jC)) h2
  exact ⟨X, Y, Qi, Qj, U, V,
    ⟨hX, hY, hXY, hq iC, hq jC, hQine, hQjne, hU3, hV3, hUV, hUQi, hVQj, hprods⟩⟩

end Soundness

open CFSG.Sporadic.Fi22 (J rep_alpha rep_beta actionChecks_parts)

theorem cent_check : fi22CentCheck = true :=
  Certificates.certificate9462

theorem centData_J :
    ∃ X Y Qi Qj U V : J, CentData X Y Qi Qj U V :=
  centData_of_check (n := 3510) (by norm_num) rep_alpha
    CFSG.Sporadic.Bridge.Fi22.rep_alpha_inv rep_beta
    (CFSG.Sporadic.Th.Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1) cent_check

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactFi22CentThreeRank_holds :
    KFactFi22CentThreeRank := by
  intro K _ _ hK T
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  obtain ⟨X, Y, Qi, Qj, U, V, D⟩ := Fi22Cent.centData_J
  let e : CFSG.Sporadic.Fi22.J ≃* K :=
    (CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans β).trans φ.symm
  have hD : Fi22Cent.CentData (e X) (e Y) (e Qi) (e Qj) (e U) (e V) :=
    Fi22Cent.CentData.map (H := K) (X := X) (Y := Y) (Qi := Qi) (Qj := Qj)
      (U := U) (V := V) D (e : CFSG.Sporadic.Fi22.J →* K) e.injective
  exact Fi22Cent.CentData.exists_of_sylow (G := K) hD T

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

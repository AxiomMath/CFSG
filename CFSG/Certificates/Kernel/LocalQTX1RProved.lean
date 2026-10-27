module

public import CFSG.Certificates.Kernel.LocalQTX1HProved

public section

namespace CFSG.KC.LQT.XR.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.XH
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.RF.Pf CFSG.KC.LQT.BS.Pf
open CFSG.KC.LQT.XH.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem nodes_eqn {n w : Nat} (prog : List (Nat × Nat)) (TF : Nat → Nat) (K m : Nat)
    (hKm : Nat.ble (Nat.add (lenA prog) 2) (Nat.mul K m) = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true) :
    ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
  intro q hq
  have hKm' := Nat.le_of_ble_eq_true hKm
  rw [lenA_eq, Nat.add_eq, Nat.mul_eq] at hKm'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hKm'
      omega
    · exact h0
  have hc : (2 + q) / m < K := by
    rw [Nat.div_lt_iff_lt_mul hm0]
    omega
  have := allR_true (hnd _ hc) ((2 + q) % m) (Nat.mod_lt _ hm0)
  rw [Nat.div_add_mod'] at this
  dsimp only at this
  have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q) (Nat.add (lenA prog) 2)) = true := by
    rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
    constructor <;> omega
  have := impB_true this h2
  rw [P.beq_iff, nthP_eq, show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
  exact this

theorem nodes_rep {n w : Nat} (prog : List (Nat × Nat)) (TF : Nat → Nat) (K m : Nat)
    (a b : Array Nat) (h0 : Rep n w (TF 0) a) (h1 : Rep n w (TF 1) b)
    (hso : slpOKK prog 2 = true) (hKm : Nat.ble (Nat.add (lenA prog) 2) (Nat.mul K m) = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true) :
    (slpTabsA a b prog).size = prog.length + 2 ∧
    ∀ j < (slpTabsA a b prog).size, Rep n w (TF j) (slpTabsA a b prog)[j]! := by
  refine ⟨?_, ?_⟩
  · rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  · rw [slpTabsA]
    apply slpTF_rep prog #[a, b]
    · intro j hj
      rcases j with _ | _ | j
      · exact h0
      · exact h1
      · simp at hj
    · exact slpOKK_spec' prog 2 hso
    · exact nodes_eqn prog TF K m hKm hnd

theorem nodes_hb {n w : Nat} (prog : List (Nat × Nat)) (TF : Nat → Nat)
    (h0 : ∀ p, w * n ≤ p → (TF 0).testBit p = false)
    (h1 : ∀ p, w * n ≤ p → (TF 1).testBit p = false)
    (heq : ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2)) :
    ∀ j < prog.length + 2, ∀ p, w * n ≤ p → (TF j).testBit p = false := by
  intro j hj
  rcases j with _ | _ | j
  · exact h0
  · exact h1
  · have := heq j (by omega)
    rw [show j + 1 + 1 = 2 + j by omega, this]
    intro p hp
    exact testBit_ofFnW_hi (fun _ _ => imgW_lt _ _ _) hp

theorem vc_codeK {n w : Nat} (hw : n ≤ 2 ^ w) {l : List Nat} (h : tabL n l = true) :
    VC n w (codeK w l) := by
  obtain ⟨h1, h2⟩ := tabL_spec h
  refine ⟨(rep_fields (rep_codeK hw h)), fun p hp => ?_⟩
  exact testBit_codeK_hi l (fun x hx => Nat.lt_of_lt_of_le (h2 x hx) hw) p (by rw [h1]; exact hp)

section Norm

variable {n w : Nat}

theorem conj_gen {L : List Nat} (hvL : ∀ q ∈ L, VC n w q) {a b : Nat}
    (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    ((L.map (tabC n w)).all fun q =>
        (L.map (tabC n w)).contains (conjT (tabC n w a) (tabC n w b) q)) =
      allL L (fun q => hasW L (conjK n w a b q)) := by
  have hconj : ∀ z ∈ L, conjT (tabC n w a) (tabC n w b) (tabC n w z) =
      tabC n w (conjK n w a b z) := by
    intro z hz
    rw [conjT, compArr_tabC (hvL z hz).1 hb,
      compArr_tabC ha (vc_mul (hvL z hz).1 hb).1]
    rfl
  have hvk : ∀ z ∈ L, VC n w (conjK n w a b z) := fun z hz =>
    vc_mul ha (vc_mul (hvL z hz).1 hb).1
  have hmem : ∀ z ∈ L, ((L.map (tabC n w)).contains (tabC n w (conjK n w a b z)) = true ↔
      conjK n w a b z ∈ L) := by
    intro z hz
    rw [List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨z', hz', e⟩
      have := tabC_inj (hvk z hz) (hvL z' hz') e.symm
      rw [this]
      exact hz'
    · intro h
      exact ⟨_, h, rfl⟩
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, allL_eq, List.all_eq_true]
  constructor
  · intro h q hq
    have := h (tabC n w q) (List.mem_map.2 ⟨q, hq, rfl⟩)
    rw [hconj q hq, hmem q hq] at this
    rw [hasW_eq, List.contains_iff_mem]
    exact this
  · intro h q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
    rw [hconj z hz, hmem z hz]
    have := h z hz
    rw [hasW_eq, List.contains_iff_mem] at this
    exact this

theorem normOK_gen {L : List Nat} (hvL : ∀ q ∈ L, VC n w q) {a b : Nat}
    (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    normOK (L.map (tabC n w)) (tabC n w a) (tabC n w b) = normK n w L a b := by
  rw [normOK, normK, andB_eq, conj_gen hvL ha hb, conj_gen hvL hb ha]

theorem notNormOK_gen {L : List Nat} (hvL : ∀ q ∈ L, VC n w q) {a b : Nat}
    (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    notNormOK (L.map (tabC n w)) (tabC n w a) (tabC n w b) = notNormK n w L a b := by
  have h := conj_gen hvL ha hb
  rw [notNormOK, notNormK, anyL_eq]
  have e1 : ((L.map (tabC n w)).any fun q =>
      !((L.map (tabC n w)).contains (conjT (tabC n w a) (tabC n w b) q))) =
      !((L.map (tabC n w)).all fun q =>
        (L.map (tabC n w)).contains (conjT (tabC n w a) (tabC n w b) q)) := by
    rw [List.all_eq_not_any_not, Bool.not_not]
  have e2 : (L.any fun q => CFSG.KC.Ord.notB (hasW L (conjK n w a b q))) =
      !(allL L fun q => hasW L (conjK n w a b q)) := by
    rw [allL_eq, List.all_eq_not_any_not, Bool.not_not]
    congr 1
  rw [e1, e2, h]

end Norm

end CFSG.KC.LQT.XR.Pf

end

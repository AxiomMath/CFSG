module

public import CFSG.GF2Type.Smith1979.W4C2Check
public import Certificates.Data.Kernel.W4C2K

public section

namespace CFSG.KC.W4C2K

open CFSG.GF2Type.Smith1979.W4C2 LocalTest CFSG.Sporadic.SmallF2.Native

@[expose] def rc (R : Array Nat) (i : Nat) : Nat := R[i]?.getD 0 % 16

@[expose] def pk (R : Array Nat) : Nat := rc R 0 + rc R 1 * 16 + rc R 2 * 256 + rc R 3 * 4096

@[expose] def cd (E : El) : Nat := mk (pk E.G) (pk E.H) E.s

theorem rc_lt (R : Array Nat) (i : Nat) : rc R i < 16 := Nat.mod_lt _ (by omega)

theorem pk_lt (R : Array Nat) : pk R < 65536 := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3
  unfold pk; omega

theorem xor_mod16 (a b : Nat) : (a ^^^ b) % 16 = a % 16 ^^^ b % 16 :=
  Nat.xor_mod_two_pow (n := 4)

theorem xor_lt16 {a b : Nat} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

theorem vm_lt (m v : Nat) : vm m v < 16 := by
  have h : ∀ a b : Nat, b < 2 → a % 16 * b < 16 := by
    intro a b hb
    have := Nat.mod_lt a (show 16 > 0 by omega)
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simpa using this
  unfold vm
  exact xor_lt16 (xor_lt16 (xor_lt16 (h _ _ (Nat.mod_lt _ (by omega)))
    (h _ _ (Nat.mod_lt _ (by omega)))) (h _ _ (Nat.mod_lt _ (by omega))))
    (h _ _ (Nat.mod_lt _ (by omega)))

theorem vm_zero (m : Nat) : vm m 0 = 0 := by simp [vm]

theorem vm_pk (R : Array Nat) (v : Nat) :
    vm (pk R) v = rc R 0 * (v % 2) ^^^ rc R 1 * (v / 2 % 2) ^^^ rc R 2 * (v / 4 % 2) ^^^
      rc R 3 * (v / 8 % 2) := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3
  have h0 : pk R % 16 = rc R 0 := by unfold pk; omega
  have h1 : pk R / 16 % 16 = rc R 1 := by unfold pk; omega
  have h2 : pk R / 256 % 16 = rc R 2 := by unfold pk; omega
  have h3 : pk R / 4096 % 16 = rc R 3 := by unfold pk; omega
  unfold vm; rw [h0, h1, h2, h3]

theorem bit_cases (v : Nat) (k : Nat) : v / k % 2 = 0 ∨ v / k % 2 = 1 := Nat.mod_two_eq_zero_or_one _

theorem vecMulN_mod (R : Array Nat) (v : Nat) : vecMulN 4 R v % 16 = vm (pk R) (v % 16) := by
  rw [vm_pk]
  have e0 : v % 16 % 2 = v % 2 := by omega
  have e1 : v % 16 / 2 % 2 = v / 2 % 2 := by omega
  have e2 : v % 16 / 4 % 2 = v / 4 % 2 := by omega
  have e3 : v % 16 / 8 % 2 = v / 8 % 2 := by omega
  rw [e0, e1, e2, e3]
  unfold vecMulN
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.pow_zero, Nat.pow_one, show (2 : Nat) ^ 2 = 4 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl]
  unfold rc
  rcases Nat.mod_two_eq_zero_or_one v with h0 | h0 <;> rcases bit_cases v 2 with h1 | h1 <;>
    rcases bit_cases v 4 with h2 | h2 <;> rcases bit_cases v 8 with h3 | h3 <;>
    simp [h0, h1, h2, h3, xor_mod16]

theorem vm_mod16 (m v : Nat) : vm m v % 16 = vm m v := Nat.mod_eq_of_lt (vm_lt m v)

theorem pk_d0 (R : Array Nat) : pk R % 16 = rc R 0 := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3; unfold pk; omega

theorem pk_d1 (R : Array Nat) : pk R / 16 % 16 = rc R 1 := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3; unfold pk; omega

theorem pk_d2 (R : Array Nat) : pk R / 256 % 16 = rc R 2 := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3; unfold pk; omega

theorem pk_d3 (R : Array Nat) : pk R / 4096 % 16 = rc R 3 := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3; unfold pk; omega

theorem rc_mulRows (X Y : Array Nat) (i : Nat) : rc (mulRows 4 X Y) i = vm (pk Y) (rc X i) := by
  unfold rc mulRows
  rw [Array.getElem?_map]
  rcases h : X[i]? with _ | a
  · simp [vm_zero]
  · simp [vecMulN_mod]

theorem pk_mulRows (X Y : Array Nat) : pk (mulRows 4 X Y) = mm (pk X) (pk Y) := by
  unfold mm
  rw [pk_d0, pk_d1, pk_d2, pk_d3]
  conv => lhs; unfold pk
  rw [rc_mulRows, rc_mulRows, rc_mulRows, rc_mulRows]

theorem ofBits4 (f : Nat → Bool) : ofBits 4 f = (if f 0 then 1 else 0) + (if f 1 then 2 else 0) +
    (if f 2 then 4 else 0) + (if f 3 then 8 else 0) := by
  unfold ofBits
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> rfl

theorem ite_bit (x k c : Nat) : (if x.testBit k = true then c else 0) = x / 2 ^ k % 2 * c := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

theorem rc_transpose (R : Array Nat) (j : Nat) (hj : j < 4) :
    rc (transposeRows 4 R) j = rc R 0 / 2 ^ j % 2 + rc R 1 / 2 ^ j % 2 * 2 +
      rc R 2 / 2 ^ j % 2 * 4 + rc R 3 / 2 ^ j % 2 * 8 := by
  unfold transposeRows
  unfold rc
  simp only [Array.getElem?_ofFn, hj, dite_true, Option.getD_some]
  rw [ofBits4, ite_bit, ite_bit, ite_bit, ite_bit]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.pow_zero, Nat.pow_one, show (2 : Nat) ^ 2 = 4 from rfl,
      show (2 : Nat) ^ 3 = 8 from rfl] <;> omega

theorem tr_lt (m : Nat) : tr m < 65536 := by unfold tr trR; omega

theorem pk_transpose (R : Array Nat) : pk (transposeRows 4 R) = tr (pk R) := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3
  have e : pk R = rc R 0 + rc R 1 * 16 + rc R 2 * 256 + rc R 3 * 4096 := rfl
  conv => lhs; unfold pk
  rw [rc_transpose _ 0 (by omega), rc_transpose _ 1 (by omega), rc_transpose _ 2 (by omega),
    rc_transpose _ 3 (by omega)]
  unfold tr
  rw [pk_d0, pk_d1, pk_d2, pk_d3]
  unfold trR
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, show (2 : Nat) ^ 2 = 4 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl]

theorem pk_id : pk (idRows 4) = idM := by decide

theorem eqR_eq (R R' : Array Nat) : eqR R R' = (pk R == pk R') := by
  have := rc_lt R 0; have := rc_lt R 1; have := rc_lt R 2; have := rc_lt R 3
  have := rc_lt R' 0; have := rc_lt R' 1; have := rc_lt R' 2; have := rc_lt R' 3
  rw [Bool.eq_iff_iff]
  simp only [eqR, eqN, beq_iff_eq, List.all_eq_true, List.mem_range]
  unfold pk
  unfold rc at *
  constructor
  · intro h
    have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
    have h3 := h 3 (by omega)
    omega
  · intro h i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> omega

theorem gK_mk {g h : Nat} (s : Bool) (hg : g < 65536) (hh : h < 65536) : gK (mk g h s) = g := by
  cases s <;> simp [gK, mk] <;> omega

theorem hK_mk {g h : Nat} (s : Bool) (hg : g < 65536) (hh : h < 65536) : hK (mk g h s) = h := by
  cases s <;> simp [hK, mk] <;> omega

theorem sK_mk {g h : Nat} (s : Bool) (hg : g < 65536) (hh : h < 65536) : sK (mk g h s) = s := by
  cases s <;> simp [sK, mk] <;> omega

theorem gK_cd (E : El) : gK (cd E) = pk E.G := gK_mk _ (pk_lt _) (pk_lt _)

theorem hK_cd (E : El) : hK (cd E) = pk E.H := hK_mk _ (pk_lt _) (pk_lt _)

theorem sK_cd (E : El) : sK (cd E) = E.s := sK_mk _ (pk_lt _) (pk_lt _)

theorem eqE_eq (E E' : El) : eqE E E' = eqEK (cd E) (cd E') := by
  unfold eqE eqEK
  rw [eqR_eq, eqR_eq, gK_cd, gK_cd, hK_cd, hK_cd, sK_cd, sK_cd]

theorem eqE_eta (E : El) : eqE E = fun E' => eqEK (cd E) (cd E') := funext (eqE_eq E)

theorem cd_mulE (E E' : El) : cd (mulE E E') = mulK (cd E) (cd E') := by
  unfold mulE mulK
  rw [sK_cd, sK_cd, gK_cd, gK_cd, hK_cd, hK_cd]
  cases E.s <;> simp [cd, pk_mulRows]

theorem cd_invE (E : El) : cd (invE E) = invK (cd E) := by
  unfold invE invK
  rw [sK_cd, gK_cd, hK_cd]
  cases E.s <;> simp [cd, pk_transpose]

theorem cd_idE : cd idE = idK := by
  unfold cd idE idK; rw [pk_id]

theorem cd_conj (F E : El) : cd (conj F E) = conjK (cd F) (cd E) := by
  unfold conj conjK; rw [cd_mulE, cd_mulE, cd_invE]

theorem commuteE_eq (E X : El) : commuteE E X = commK (cd E) (cd X) := by
  unfold commuteE commK; rw [eqE_eq, cd_mulE, cd_mulE]

theorem cd_E1 : cd E1 = chkNK.E1K := by decide

theorem eqV_appE (E : El) (v w : Nat × Nat) : eqV (appE E v) w = eqVK (appK (cd E) v) w := by
  unfold eqV eqN eqVK appE appK
  rw [sK_cd, gK_cd, hK_cd]
  cases E.s <;> simp [vecMulN_mod, vm_mod16]

theorem eqV_xorV_appE (E : El) (v w : Nat × Nat) :
    eqV (xorV (appE E v) v) w = eqVK (xorVK (appK (cd E) v) v) w := by
  unfold eqV eqN eqVK appE appK xorV xorVK
  rw [sK_cd, gK_cd, hK_cd]
  cases E.s <;> simp [xor_mod16, vecMulN_mod, vm_mod16]

theorem validE_eq (E : El) : validE E = validK (cd E) := by
  unfold validE validK
  rw [eqR_eq, pk_mulRows, pk_transpose, pk_id, gK_cd, hK_cd]

theorem injRows_eq (R : Array Nat) : injRows R = injK (pk R) := by
  unfold injRows injK
  simp only [vecMulN_mod]

theorem pk_invRows (R : Array Nat) : pk (invRows R) = invMK (pk R) := by
  have hr : ∀ j : Nat, j < 4 → rc (invRows R) j = invRowK (pk R) j % 16 := by
    intro j hj
    unfold rc invRows invRowK
    simp [Array.getElem?_ofFn, hj, vecMulN_mod]
  unfold invMK
  conv => lhs; unfold pk
  rw [hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega)]

theorem pk_dualRows (R : Array Nat) : pk (dualRows R) = dualK (pk R) := by
  unfold dualRows dualK; rw [pk_transpose, pk_invRows]

@[expose] def rowsOf (n : Nat) : Array Nat := #[n % 16, n / 16 % 16, n / 256 % 16, n / 4096]

theorem pk_rowsOf {n : Nat} (hn : n < 65536) : pk (rowsOf n) = n := by
  unfold pk rc rowsOf; simp; omega

theorem cd_rowsOf {n : Nat} (hn : n < 65536) (s : Bool) :
    cd ⟨rowsOf n, dualRows (rowsOf n), s⟩ = mk n (dualK n) s := by
  unfold cd; simp only; rw [pk_dualRows, pk_rowsOf hn]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

@[expose] def hpair (n : Nat) : List Nat := [false, true].map (mk n (dualK n))

theorem rowsOf_eq (n : Nat) : #[n % 16, n / 16 % 16, n / 256 % 16, n / 4096] = rowsOf n := rfl

theorem Hlist_map : (Hlist ()).map cd = ((List.range 65536).filter injK).flatMap hpair := by
  unfold Hlist allRows
  rw [List.filter_map, List.flatMap_map, List.map_flatMap]
  have hf : (List.range 65536).filter
      (injRows ∘ fun n => #[n % 16, n / 16 % 16, n / 256 % 16, n / 4096]) =
      (List.range 65536).filter injK := by
    apply List.filter_congr
    intro n hn
    rw [List.mem_range] at hn
    simp only [Function.comp, rowsOf_eq, injRows_eq, pk_rowsOf hn]
  rw [hf]
  apply flatMap_congr'
  intro n hn
  rw [List.mem_filter, List.mem_range] at hn
  simp only [hpair, List.map_cons, List.map_nil, rowsOf_eq, cd_rowsOf hn.1]

theorem mem_Hlist {E : El} (h : E ∈ Hlist ()) :
    ∃ n, n < 65536 ∧ injK n = true ∧ ∃ s, E = ⟨rowsOf n, dualRows (rowsOf n), s⟩ := by
  unfold Hlist allRows at h
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range] at h
  obtain ⟨R, ⟨⟨n, hn, rfl⟩, hinj⟩, hE⟩ := h
  refine ⟨n, hn, ?_, ?_⟩
  · rw [rowsOf_eq, injRows_eq, pk_rowsOf hn] at hinj; exact hinj
  · simp only [rowsOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

theorem mem_Hlist_of {n : Nat} (hn : n < 65536) (hi : injK n = true) (s : Bool) :
    (⟨rowsOf n, dualRows (rowsOf n), s⟩ : El) ∈ Hlist () := by
  unfold Hlist allRows
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range]
  refine ⟨rowsOf n, ⟨⟨n, hn, rfl⟩, ?_⟩, ?_⟩
  · rw [injRows_eq, pk_rowsOf hn]; exact hi
  · cases s <;> simp

theorem stab_map (H : List El) (b : Nat × Nat) :
    (stabL H b).map cd = (H.map cd).filter (fun c => eqVK (appK c b) b) := by
  unfold stabL
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro E _
  simp only [Function.comp, eqV_appE]

theorem hpair_filter {n : Nat} (hn : n < 65536) (b : Nat × Nat) :
    (hpair n).filter (fun c => eqVK (appK c b) b) = stabPK b n := by
  unfold hpair stabPK
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro s _
  have hd : dualK n < 65536 := tr_lt _
  simp only [Function.comp, appK, eqVK, stabNK, sK_mk s hn hd, gK_mk s hn hd, hK_mk s hn hd]
  cases s <;> simp [vm_mod16]

theorem range_chunks (k : Nat) :
    List.range (4096 * k) = (List.range k).flatMap fun i => List.range' (4096 * i) 4096 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ← ih, List.flatMap_singleton,
      List.range_eq_range', List.range_eq_range',
      show 4096 * (k + 1) = 4096 * k + 4096 by omega, ← List.range'_append_1, Nat.zero_add]

theorem filter_chunks {p : Nat → Bool} {GL : List (List Nat)}
    (h : ∀ i < 16, (List.range' (4096 * i) 4096).filter p = GL.getD i []) :
    (List.range 65536).filter p = (List.range 16).flatMap fun i => GL.getD i [] := by
  rw [show 65536 = 4096 * 16 from rfl, range_chunks, List.filter_flatMap]
  apply flatMap_congr'
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem isComm_eq (P : List El) (E : El) : isComm P E = isCommK (P.map cd) (cd E) := by
  unfold isComm isCommK
  simp only [List.all_map, Function.comp_def, eqE_eq, cd_mulE, cd_idE, commuteE_eq, cd_conj]

theorem candOK_eq (P Cl : List El) : candOK P Cl = candOKK (P.map cd) (Cl.map cd) := by
  unfold candOK candOKK
  simp only [List.all_map, List.any_map, Function.comp_def, eqE_eq, eqE_eta, cd_mulE, cd_idE,
    commuteE_eq, cd_conj]

theorem filter_isComm (P : List El) :
    (P.filter (isComm P)).map cd = (P.map cd).filter (isCommK (P.map cd)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro E _
  simp only [Function.comp, isComm_eq]

theorem chkN_eq (H : List El) :
    chkN H = chkNK ((stabL H bN).map cd) (((stabL H bN).map cd).filter
      (isCommK ((stabL H bN).map cd))) := by
  unfold chkN chkNK
  generalize stabL H bN = P
  simp only [← filter_isComm, candOK_eq, List.all_map, List.any_map, Function.comp_def, eqE_eq,
    cd_idE, cd_conj, cd_E1]

theorem dot4_eq (x y : Nat) : dot4 x y = dotK x y := by
  unfold dot4 dotK
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.pow_one, Nat.div_one,
    show (2 : Nat) ^ 2 = 4 from rfl, show (2 : Nat) ^ 3 = 8 from rfl]
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h0 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 2) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 4) with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 8) with h3 | h3 <;>
    rcases Nat.mod_two_eq_zero_or_one y with g0 | g0 <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 2) with g1 | g1 <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 4) with g2 | g2 <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 8) with g3 | g3 <;>
    simp [h0, h1, h2, h3, g0, g1, g2, g3]

theorem perp_eq (b : Nat × Nat) : perp b = perpK b := by
  unfold perp perpK polarB
  simp only [dot4_eq]

theorem filterKl (Cl : List El) :
    (Cl.filter (·.s == false)).map cd = (Cl.map cd).filter (sK · == false) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro E _
  simp only [Function.comp, sK_cd]

theorem chkM_eq (H : List El) :
    chkM H = chkMK ((stabL H bM).map cd) (((stabL H bM).map cd).filter
      (isCommK ((stabL H bM).map cd))) := by
  unfold chkM chkMK
  generalize stabL H bM = P
  rw [← filter_isComm, ← filterKl, perp_eq]
  simp only [candOK_eq, List.all_map, List.any_map, List.length_map, Function.comp_def, eqE_eq,
    eqE_eta, cd_idE, cd_conj, cd_mulE, commuteE_eq, eqV_appE, eqV_xorV_appE, ws4, ws4K, bM, bMK]

end CFSG.KC.W4C2K

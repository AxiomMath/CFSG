module

public import Certificates.Data.Kernel.HMathieu.Wit22K
public import Certificates.Data.Kernel.HMathieu.Wit22
public import CFSG.Certificates.Kernel.HMathieu.PermThreeSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat

theorem pcS_eq (p q : Nat) : pcS p q = pc24 p q := by
  unfold pcS
  rw [strictN_eqP, strictN_eqP]

theorem vpK_pcS {p q : Nat} (hp : vpK p = true) (hq : vpK q = true) : vpK (pcS p q) = true := by
  rw [pcS_eq]
  exact vpK_pc24 hp hq

theorem comp24_unpkS (p : Nat) {q : Nat} (hq : vpK q = true) :
    comp24 (unpk p) (unpk q) = unpk (pcS p q) := by
  rw [pcS_eq, comp24_unpk p hq]

theorem vpK_conjK {a ai t : Nat} (ha : vpK a = true) (hai : vpK ai = true) (ht : vpK t = true) :
    vpK (conjK a ai t) = true :=
  vpK_pcS (vpK_pcS ha ht) hai

theorem conj24_unpk {a ai t : Nat} (hai : vpK ai = true) (ht : vpK t = true)
    (hi : invArr (unpk a) = unpk ai) : conj24 (unpk a) (unpk t) = unpk (conjK a ai t) := by
  unfold conj24 conjK
  rw [hi, comp24_unpkS a ht, comp24_unpkS _ hai]

theorem vpK_prod4K {t a ai b bi c ci : Nat} (ht : vpK t = true) (ha : vpK a = true)
    (hai : vpK ai = true) (hb : vpK b = true) (hbi : vpK bi = true) (hc : vpK c = true)
    (hci : vpK ci = true) : vpK (prod4K t a ai b bi c ci) = true :=
  vpK_pcS (vpK_pcS ht (vpK_conjK ha hai ht))
    (vpK_pcS (vpK_conjK hb hbi ht) (vpK_conjK hc hci ht))

theorem prod4_unpk {t a ai b bi c ci : Nat} (ht : vpK t = true) (ha : vpK a = true)
    (hai : vpK ai = true) (hb : vpK b = true) (hbi : vpK bi = true) (hc : vpK c = true)
    (hci : vpK ci = true) (h1 : invArr (unpk a) = unpk ai) (h2 : invArr (unpk b) = unpk bi)
    (h3 : invArr (unpk c) = unpk ci) :
    prod4 (unpk t) (unpk a) (unpk b) (unpk c) = unpk (prod4K t a ai b bi c ci) := by
  unfold prod4 prod4K
  rw [conj24_unpk hai ht h1, conj24_unpk hbi ht h2, conj24_unpk hci ht h3,
    comp24_unpkS _ (vpK_conjK hc hci ht), comp24_unpkS _ (vpK_conjK ha hai ht),
    comp24_unpkS _ (vpK_pcS (vpK_conjK hb hbi ht) (vpK_conjK hc hci ht))]

theorem powK_succ (a k : Nat) : powK a (k + 1) = pcS a (powK a k) := rfl

theorem vpK_powK {a : Nat} (ha : vpK a = true) (k : Nat) : vpK (powK a k) = true := by
  induction k with
  | zero => exact vpK_id
  | succ k ih =>
    rw [powK_succ]
    exact vpK_pcS ha ih

theorem pow24_unpk {a : Nat} (ha : vpK a = true) (k : Nat) : pow24 (unpk a) k = unpk (powK a k) := by
  induction k with
  | zero => exact range_eq_unpk
  | succ k ih =>
    rw [pow24, ih, powK_succ, comp24_unpkS _ (vpK_powK ha k)]

theorem ord11_eq {a : Nat} (ha : vpK a = true) : order11OK (unpk a) = ord11K a := by
  unfold ord11K order11OK
  rw [strictB_eqP, pow24_unpk ha]
  unfold fixK
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range, bne_iff_ne, ne_eq, beq_iff_eq]
  exact and_congr (exists_congr fun i => and_congr_right fun hi => by rw [unpk_get _ hi])
    (forall_congr' fun j => imp_congr_right fun hj => by rw [unpk_get _ hj])

theorem inv24_eq {e : Nat} (he : vpK e = true) : inv24 (unpk e) = inv24K e := by
  unfold inv24 inv24K
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  exact forall_congr' fun i => imp_congr_right fun hi => by
    rw [unpk_get _ hi, unpk_get _ ((vpK_spec he).2 i hi)]

theorem witE_eq (hP : ∀ i < 6, vpK (poolP.getD i 0) = true ∧ vpK (poolI.getD i 0) = true ∧
      unpk (poolP.getD i 0) = pool22[i]! ∧ unpk (poolI.getD i 0) = invArr pool22[i]!)
    {e : Nat} (he : vpK e = true) (p : Nat) : witE (unpk e) p = witK e p := by
  unfold witK witE
  rw [strictB_eqP, strictB_eqP, strictB_eqP]
  have hl : pool22.length = 6 := rfl
  rw [hl]
  by_cases hi : wit22I[p]! < 6
  · by_cases hj : wit22J[p]! < 6
    · by_cases hk : wit22K[p]! < 6
      · obtain ⟨vi, vii, ui, uii⟩ := hP _ hi
        obtain ⟨vj, vji, uj, uji⟩ := hP _ hj
        obtain ⟨vk, vki, uk, uki⟩ := hP _ hk
        have ii : invArr (unpk (poolP.getD wit22I[p]! 0)) = unpk (poolI.getD wit22I[p]! 0) := by
          rw [ui, uii]
        have ij : invArr (unpk (poolP.getD wit22J[p]! 0)) = unpk (poolI.getD wit22J[p]! 0) := by
          rw [uj, uji]
        have ik : invArr (unpk (poolP.getD wit22K[p]! 0)) = unpk (poolI.getD wit22K[p]! 0) := by
          rw [uk, uki]
        simp only [hi, hj, hk, decide_true, Bool.true_and]
        rw [← ui, ← uj, ← uk, prod4_unpk he vi vii vj vji vk vki ii ij ik,
          ord11_eq (vpK_prod4K he vi vii vj vji vk vki)]
      · simp [hk]
    · simp [hj]
  · simp [hi]

theorem chk7106K_cons (e : Nat) (E : List Nat) (s : Nat) :
    chk7106K (e :: E) s = ((s == 0 || !inv24K e || witK e s) && chk7106K E (s + 1)) := rfl

theorem chk7106K_all (E : List Nat) (s : Nat) : chk7106K E s = (List.range E.length).all
    fun p => s + p == 0 || !inv24K (E.getD p 0) || witK (E.getD p 0) (s + p) := by
  induction E generalizing s with
  | nil => rfl
  | cons e E ih =>
    rw [chk7106K_cons, ih, List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map]
    simp only [Nat.succ_eq_add_one, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ, Function.comp_def,
      Nat.add_right_comm s 1, ← Nat.add_assoc]

theorem chk7106K_eq (hP : ∀ i < 6, vpK (poolP.getD i 0) = true ∧ vpK (poolI.getD i 0) = true ∧
      unpk (poolP.getD i 0) = pool22[i]! ∧ unpk (poolI.getD i 0) = invArr pool22[i]!)
    {E : List Nat} (hv : ∀ e ∈ E, vpK e = true) :
    ((List.range E.length).all fun p => p == 0 || !inv24 ((E.map unpk).toArray[p]!) ||
      witE ((E.map unpk).toArray[p]!) p) = chk7106K E 0 := by
  rw [chk7106K_all, Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, Nat.zero_add]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hg : (E.map unpk).toArray[p]! = unpk (E.getD p 0) := by
    rw [List.getD_eq_getElem _ _ hp, getElem!_pos _ p (by simpa using hp)]
    simp
  have he : vpK (E.getD p 0) = true := by
    rw [List.getD_eq_getElem _ _ hp]
    exact hv _ (List.getElem_mem hp)
  rw [hg, inv24_eq he, witE_eq hP he]

end CFSG.KC.HMathieu

end

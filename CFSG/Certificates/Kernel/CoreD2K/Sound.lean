
module

public import Certificates.Data.Kernel.CoreD2K.Check
public import CFSG.Certificates.Kernel.MaxD2.Sound
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
public import CFSG.Certificates.Kernel.CoreD2K.Lines

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm

theorem exists_pow_mul_pow_of_mem {X : Type*} [Group X] {p : ℕ} (hp : 0 < p) {z v g : X}
    (hzv : z * v = v * z) (hz : z ^ p = 1) (hv : v ^ p = 1)
    (hg : g ∈ Subgroup.closure ({z, v} : Set X)) : ∃ a < p, ∃ b < p, g = z ^ a * v ^ b := by
  have hc : Commute z v := hzv
  have hred : ∀ x : X, x ^ p = 1 → ∀ m, x ^ m = x ^ (m % p) := fun x hx m => by
    conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hx, one_pow, one_mul]
  have hinv : ∀ x : X, x ^ p = 1 → ∀ a, (x ^ a)⁻¹ = x ^ (a * (p - 1)) := fun x hx a => by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have e : a + a * (p - 1) = p * a := by
      rcases p with _ | q
      · omega
      · rw [Nat.add_sub_cancel]
        ring
    rw [e, pow_mul, hx, one_pow]
  suffices h : ∃ a b : ℕ, g = z ^ a * v ^ b by
    obtain ⟨a, b, rfl⟩ := h
    exact ⟨a % p, Nat.mod_lt _ hp, b % p, Nat.mod_lt _ hp, by rw [← hred z hz, ← hred v hv]⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    have e : v ^ b * z ^ c = z ^ c * v ^ b := (hc.pow_pow c b).eq.symm
    refine ⟨a + c, b + d, ?_⟩
    rw [pow_add, pow_add]
    calc z ^ a * v ^ b * (z ^ c * v ^ d) = z ^ a * (v ^ b * z ^ c) * v ^ d := by
          simp only [mul_assoc]
      _ = z ^ a * (z ^ c * v ^ b) * v ^ d := by rw [e]
      _ = z ^ a * z ^ c * (v ^ b * v ^ d) := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    refine ⟨a * (p - 1), b * (p - 1), ?_⟩
    rw [mul_inv_rev, hinv z hz, hinv v hv, ← (hc.pow_pow _ _).eq]

section Packed

variable {n w : Nat}

abbrev PR (n w p : Nat) (g : Equiv.Perm (Fin n)) : Prop := Cn n w p ∧ TabRep (unpack n w p) g

theorem pr_one (hn : szOK n w = true) : PR n w (pidn n w) 1 :=
  ⟨pidn_canon hn, by rw [← id_u hn]; exact TabRep.idTab⟩

theorem pr_mul {p q : Nat} {g h : Equiv.Perm (Fin n)} (hp : PR n w p g) (hq : PR n w q h) :
    PR n w (pcomp n w (mask w) p q) (g * h) :=
  ⟨cc hp.1 hq.1, by rw [← comp_u hp.1 hq.1]; exact hp.2.comp hq.2⟩

theorem pr_pow (hn : szOK n w = true) {p : Nat} {g : Equiv.Perm (Fin n)} (hp : PR n w p g)
    (e : Nat) : PR n w (pw n w p e) (g ^ e) :=
  ⟨pw_canon hn hp.1 e, by rw [← powT_u hn hp.1 e]; exact powT_rep hp.2 e⟩

theorem pr_beq {p q : Nat} {g h : Equiv.Perm (Fin n)} (hp : PR n w p g) (hq : PR n w q h) :
    Nat.beq p q = true ↔ g = h := by
  rw [← eq_u hp.1 hq.1]
  exact hp.2.beq_iff hq.2

theorem pr_ne {p q : Nat} {g h : Equiv.Perm (Fin n)} (hp : PR n w p g) (hq : PR n w q h)
    (hb : Bool.rec (motive := fun _ => Bool) true false (Nat.beq p q) = true) : g ≠ h := by
  intro e
  have e' := (pr_beq hp hq).2 e
  rw [bnot_e hb] at e'
  exact absurd e' (by decide)

theorem pr_word {k r : Nat} {PS PSI : Nat → Nat} {L : List (Equiv.Perm (Fin n))}
    (hL : L.length = k) (hp : allN k (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hr : ∀ j < k, TabRep (unpack n w (PS j)) (L.getD j 1)) {wd : List Int}
    (h : wordEqK n w (mask w) (pidn n w) PS PSI k wd r = true) :
    TabRep (unpack n w r) (wordVal L wd) := by
  set Sa : Array Tab := Array.ofFn (n := k) fun j => unpack n w (PS j.val) with hSa
  have hS : Sa.size = k ∧ ∀ j < k, Sa[j]! = unpack n w (PS j) :=
    ⟨Array.size_ofFn, fun j hj => by
      rw [hSa, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]⟩
  rw [← wordT_u hS hp h]
  refine wordT_rep L _ _ (fun j => ?_) (fun j => ?_) wd
  · by_cases hj : j < k
    · have e : Sa.getD j (idTab n) = unpack n w (PS j) := by simp [hSa, Array.getD, hj]
      rw [e]
      exact hr j hj
    · have e : Sa.getD j (idTab n) = idTab n := by simp [hSa, Array.getD, hj]
      rw [e, List.getD_eq_default _ _ (by omega)]
      exact TabRep.idTab
  · by_cases hj : j < k
    · have hpj := PK.allN_iff.1 hp j hj
      have e : (Sa.map (invTab n)).getD j (idTab n) = unpack n w (PSI j) := by
        rw [← inv_u hpj]
        simp [hSa, Array.getD, hj]
      rw [e]
      exact (hr j hj).inv (size_u _) (inv_comp hpj)
    · have e : (Sa.map (invTab n)).getD j (idTab n) = idTab n := by simp [hSa, Array.getD, hj]
      rw [e, List.getD_eq_default _ _ (by omega), inv_one]
      exact TabRep.idTab

theorem cosK_sound (hn : szOK n w = true) {z x : Nat} {zz xx : Equiv.Perm (Fin n)}
    (hz : PR n w z zz) (hx : PR n w x xx) :
    ∀ k t (tt : Equiv.Perm (Fin n)), PR n w t tt → cosK n w z x k t = true →
      ∀ a < k, xx ≠ zz ^ a * tt := by
  intro k
  induction k with
  | zero => intro t tt _ _ a ha; omega
  | succ k ih =>
    intro t tt ht h a ha
    have e : cosK n w z x (k + 1) t = Bool.rec (motive := fun _ => Bool) false
        (strictB (pcomp n w (mask w) z t) (cosK n w z x k))
        (Bool.rec (motive := fun _ => Bool) true false (Nat.beq x t)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_e h
    rw [PK.strictB_eq] at h2
    rcases a with _ | a
    · rw [pow_zero, one_mul]
      exact pr_ne hx ht h1
    · rw [pow_succ, mul_assoc]
      exact ih _ _ (pr_mul hz ht) h2 a (by omega)

theorem outL_sound (hn : szOK n w = true) {p z v x : Nat} {zz vv xx : Equiv.Perm (Fin n)}
    (hz : PR n w z zz) (hv : PR n w v vv) (hx : PR n w x xx) :
    ∀ k t (tt : Equiv.Perm (Fin n)), PR n w t tt → outL n w p z v x k t = true →
      ∀ b < k, ∀ a < p, xx ≠ zz ^ a * (vv ^ b * tt) := by
  intro k
  induction k with
  | zero => intro t tt _ _ b hb; omega
  | succ k ih =>
    intro t tt ht h b hb a ha
    have e : outL n w p z v x (k + 1) t = Bool.rec (motive := fun _ => Bool) false
        (strictB (pcomp n w (mask w) v t) (outL n w p z v x k)) (cosK n w z x p t) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_e h
    rw [PK.strictB_eq] at h2
    rcases b with _ | b
    · rw [pow_zero, one_mul]
      exact cosK_sound hn hz hx p t tt ht h1 a ha
    · rw [pow_succ, mul_assoc]
      exact ih _ _ (pr_mul hv ht) h2 b (by omega) a ha

theorem outK_sound (hn : szOK n w = true) {p z v x : Nat} {zz vv xx : Equiv.Perm (Fin n)}
    (hz : PR n w z zz) (hv : PR n w v vv) (hx : PR n w x xx) (h : outK n w p z v x = true) :
    ∀ a < p, ∀ b < p, xx ≠ zz ^ a * vv ^ b := by
  intro a ha b hb
  have := outL_sound hn hz hv hx p (pidn n w) 1 (pr_one hn) h b hb a ha
  rwa [mul_one] at this

end Packed

structure KHyps (n w : Nat) (V : VData) (GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat)
    (cnt cap len : Nat) : Prop where
  hn : szOK n w = true
  hgens : gensK n w V GP GPI EG GT GTI = true
  hh : penumHdK (pidn n w) cnt cap T PL = true
  hsl : penumSlK n w (mask w) (n * w) false EG EGI V.base.eW.length cnt T PL POS SRT SRI 0 len =
    true
  hlen : cnt ≤ len
  hcnt : cnt = V.base.p ^ 3
  hnab : nabK n w V.base.eW.length EG = true
  hcen : cenK n w V.base.p V.base.eW.length EG = true
  hlines : linesK n w V.base.p V EG = true
  hkinds : kindsK n w V EG GT = true
  hwords : wordsK n w V GP GT GTI = true

theorem lines_facts {n w : Nat} {V : VData} {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat}
    {cnt cap len : Nat} (H : KHyps n w V GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hp : V.base.p.Prime) {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), IsPGroup V.base.p E ∧ Nat.card E = V.base.p ^ 3 ∧
      E ≤ Subgroup.closure {a, b} ∧
      ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E → IsElemAbelian V.base.p A →
        Nat.card A = V.base.p ^ 2 →
        ∃ Γ : Set (Equiv.Perm (Fin n)), Γ ⊆ Subgroup.closure {a, b} ∧
          ({a, b} : Set (Equiv.Perm (Fin n))) ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
            ((∃ j < V.gk.length, (V.gk.getD j default).kind = 0) ∧
              ∃ u v : Equiv.Perm (Fin n), u ∈ E ∧ v ∈ E ∧ u ^ V.base.p = 1 ∧
                v ^ V.base.p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ (∀ j < V.base.p, v ≠ u ^ j) ∧
                ∃ α β γ δ : ℕ, g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
            (∃ y ∈ A, y ≠ 1 ∧ y ^ V.base.p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g) := by
  have hn := H.hn
  set p := V.base.p with hpdef
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  have hgens := H.hgens
  unfold gensK at hgens
  obtain ⟨hG2, hrest⟩ := band_e hgens
  obtain ⟨hE1, hG1⟩ := band_e hrest
  have hG2' : allN 2 (fun j => permOK n w (mask w) (n * w) (GP j) (GPI j)) = true := hG2
  have hSr : ∀ j < 2, TabRep (unpack n w (GP j)) (S.getD j 1) := by
    intro j hj
    rcases j with _ | _ | j
    · exact ha
    · exact hb
    · omega
  have hword : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GP GPI 2 wd r = true → TabRep (unpack n w r) (wordVal S wd) :=
    fun h => pr_word (k := 2) rfl hG2' hSr h
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  set ne := V.base.eW.length with hne
  set Le : List (Equiv.Perm (Fin n)) := V.base.eW.map (wordVal S) with hLe
  have hLeget : ∀ k < ne, Le.getD k 1 = wordVal S (V.base.eW.getD k []) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLe] using hk), List.getD_eq_getElem _ _ hk,
      List.getElem_map]
  have hEk : ∀ k < ne, wordEqK n w (mask w) (pidn n w) GP GPI 2 (V.base.eW.getD k []) (EG k) =
      true ∧ canonK n w (mask w) (n * w) (EG k) = true := fun k hk =>
    band_e (PK.allN_iff.1 hE1 k hk)
  have hEP : ∀ k < ne, PR n w (EG k) (Le.getD k 1) := fun k hk =>
    ⟨(hEk k hk).2, by rw [hLeget k hk]; exact hword (hEk k hk).1⟩
  have hLmem : ∀ k < ne, Le.getD k 1 ∈ Le := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLe] using hk)]
    exact List.getElem_mem _
  have hLeG : ∀ g ∈ Le, g ∈ G := by
    intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  set ng := V.base.gWs.length with hng
  set Lg : List (Equiv.Perm (Fin n)) := V.base.gWs.map (wordVal S) with hLg
  have hLgget : ∀ j < ng, Lg.getD j 1 = wordVal S (V.base.gWs.getD j []) := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj), List.getD_eq_getElem _ _ hj,
      List.getElem_map]
  have hGk : ∀ j < ng, wordEqK n w (mask w) (pidn n w) GP GPI 2 (V.base.gWs.getD j []) (GT j) =
      true ∧ permOK n w (mask w) (n * w) (GT j) (GTI j) = true := fun j hj =>
    band_e (PK.allN_iff.1 hG1 j hj)
  have hgP : ∀ j < ng, PR n w (GT j) (Lg.getD j 1) := fun j hj =>
    ⟨(perm_canon (hGk j hj).2 hn).1, by rw [hLgget j hj]; exact hword (hGk j hj).1⟩
  have hGTp : allN ng (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) = true :=
    PK.allN_iff.2 fun j hj => (hGk j hj).2
  have hwordG : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GT GTI ng wd r = true → TabRep (unpack n w r) (wordVal Lg wd) :=
    fun h => pr_word (by simp [hLg, hng]) hGTp (fun j hj => (hgP j hj).2) h
  have hLgmem : ∀ j < ng, Lg.getD j 1 ∈ Lg := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj)]
    exact List.getElem_mem _
  have hLgG : ∀ g ∈ Lg, g ∈ G := by
    intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  set gens : Array Tab := Array.ofFn (n := ne) fun k => unpack n w (EG k.val) with hgens'
  have hgget : ∀ k < ne, gens[k]! = unpack n w (EG k) := fun k hk => by
    rw [hgens', getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hgsz : gens.size = ne := Array.size_ofFn
  have hgOK : GensOK n w ne EG gens := ⟨hgsz, fun j hj => ⟨hgget j hj, (hEk j hj).2⟩⟩
  obtain ⟨-, henum⟩ := penumK_left_sound hn hgOK H.hh
    (fun i hi => CFSG.KS.BaseMask.penumSl_spec H.hsl (Nat.zero_le i) (by have := H.hlen; omega) hi)
  set E := Subgroup.closure {g | g ∈ Le} with hEdef
  have hA : ∀ g ∈ {g | g ∈ Le}, ∃ j < gens.size, TabRep gens[j]! g := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have hk' : k < ne := by simpa [hLe] using hk
    refine ⟨k, by rw [hgsz]; exact hk', ?_⟩
    rw [hgget k hk', ← List.getD_eq_getElem _ 1 hk]
    exact (hEP k hk').2
  have hgensE : ∀ j < gens.size, ∃ g ∈ {g | g ∈ Le}, TabRep gens[j]! g := by
    intro j hj
    rw [hgsz] at hj
    exact ⟨Le.getD j 1, hLmem j hj, by rw [hgget j hj]; exact (hEP j hj).2⟩
  have hE := enumerates_closure hA hgensE henum
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE.card, Array.length_toList, rec_size, H.hcnt]
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  have hEG : E ≤ G := by
    rw [hEdef, Subgroup.closure_le]
    exact fun g hg => hLeG g hg
  have hmemE : ∀ k < ne, Le.getD k 1 ∈ E := fun k hk => Subgroup.subset_closure (hLmem k hk)
  have hnab := H.hnab
  unfold nabK at hnab
  have hnab' := bnot_e hnab
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hall : allN ne (fun i => strictB (EG i) (fun x => allN ne (fun j => strictB (EG j)
        (fun y => Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x))))) = true := by
      refine PK.allN_iff.2 fun i hi => ?_
      rw [PK.strictB_eq]
      refine PK.allN_iff.2 fun j hj => ?_
      rw [PK.strictB_eq]
      exact (pr_beq (pr_mul (hEP i hi) (hEP j hj)) (pr_mul (hEP j hj) (hEP i hi))).2
        (hcon _ (hmemE i hi) _ (hmemE j hj))
    rw [hall] at hnab'
    exact absurd hnab' (by decide)
  have hcen := H.hcen
  unfold cenK at hcen
  rw [PK.strictB_eq] at hcen
  obtain ⟨h0, hcen⟩ := band_e hcen
  obtain ⟨hzp, hcen⟩ := band_e hcen
  obtain ⟨hz1, hzc⟩ := band_e hcen
  have h0' : 0 < ne := Nat.blt_eq.mp h0
  set z := Le.getD 0 1 with hzdef
  have hzP : PR n w (EG 0) z := hEP 0 h0'
  have hzE : z ∈ E := hmemE 0 h0'
  have hzp' : z ^ p = 1 := (pr_beq (pr_pow hn hzP p) (pr_one hn)).1 hzp
  have hz1' : z ≠ 1 := pr_ne hzP (pr_one hn) hz1
  have hzcent : ∀ x ∈ E, x * z = z * x := by
    have hcl : E ≤ Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin n))) := by
      rw [hEdef, Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hk' : k < ne := by simpa [hLe] using hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← List.getD_eq_getElem _ 1 hk]
      have hc := PK.allN_iff.1 hzc k hk'
      rw [PK.strictB_eq] at hc
      exact ((pr_beq (pr_mul hzP (hEP k hk')) (pr_mul (hEP k hk') hzP)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  have hlines := H.hlines
  unfold linesK at hlines
  rw [PK.strictB_eq] at hlines
  obtain ⟨hys, hlines⟩ := band_e hlines
  obtain ⟨hvs, hds⟩ := band_e hlines
  have hys' : V.ys.length = p + 1 := Nat.eq_of_beq_eq_true hys
  set v : ℕ → Equiv.Perm (Fin n) := fun i => Le.getD (V.ys.getD i 0) 1 with hvdef
  have hvK : ∀ i < V.ys.length, V.ys.getD i 0 < ne ∧
      vK n w p (EG 0) (EG (V.ys.getD i 0)) = true := fun i hi => by
    obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hvs i hi)
    exact ⟨Nat.blt_eq.mp h1, h2⟩
  have hvP : ∀ i < V.ys.length, PR n w (EG (V.ys.getD i 0)) (v i) := fun i hi =>
    hEP _ (hvK i hi).1
  have hvfacts : ∀ i < V.ys.length, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧
      ∀ k < p, v i ≠ z ^ k := by
    intro i hi
    obtain ⟨hlt, hk⟩ := hvK i hi
    unfold vK at hk
    obtain ⟨hk1, hk2⟩ := band_e hk
    have hvE : v i ∈ E := hmemE _ hlt
    exact ⟨hvE, (pr_beq (pr_pow hn (hvP i hi) p) (pr_one hn)).1 hk1, (hzcent _ hvE).symm,
      fun k hk' => pr_ne (hvP i hi) (pr_pow hn hzP k) (PK.allN_iff.1 hk2 k hk')⟩
  have hv' : ∀ i ≤ p, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧ ∀ k < p, v i ≠ z ^ k :=
    fun i hi => hvfacts i (by omega)
  have hd : ∀ j ≤ p, ∀ i < j, v j ∉ Subgroup.closure ({z, v i} : Set (Equiv.Perm (Fin n))) := by
    intro j hj i hij hmem
    have hj' : j < V.ys.length := by omega
    have hi' : i < V.ys.length := by omega
    have hdj := PK.allN_iff.1 hds j hj'
    rw [PK.strictB_eq] at hdj
    have hout := PK.allN_iff.1 hdj i hij
    obtain ⟨hvi, hvp, hzv, -⟩ := hvfacts i hi'
    obtain ⟨c, hc, d, hd, e⟩ := exists_pow_mul_pow_of_mem hp.pos hzv hzp' hvp hmem
    exact outK_sound hn hzP (hvP i hi') (hvP j hj') hout c hc d hd e
  have hkinds := H.hkinds
  unfold kindsK at hkinds
  obtain ⟨hgkl, hkall⟩ := band_e hkinds
  have hgkl' : V.gk.length = ng := Nat.eq_of_beq_eq_true hgkl
  have hwords := H.hwords
  unfold wordsK at hwords
  obtain ⟨-, hwords⟩ := band_e hwords
  obtain ⟨-, hwall⟩ := band_e hwords
  refine ⟨E, hEp, hEc, hEG, ?_⟩
  intro A hAE hAe hAc
  obtain ⟨i, hi, hYA⟩ := eq_line_of_elemAbelian hp hEc hnc hzE hzp' hz1' hzcent hv' hd hAE hAe hAc
  have hi' : i < V.ys.length := by omega
  have hzA : z ∈ A := by
    rw [← hYA]
    exact Subgroup.subset_closure (by simp)
  set Γ : Set (Equiv.Perm (Fin n)) := {g | ∃ j < ng,
    (((V.gk.getD j default).kind = 0 ∨ (V.gk.getD j default).idx = i) ∨
      (V.gk.getD j default).f2 = 0) ∧ g = Lg.getD j 1} with hΓdef
  have hall : ∀ wd : List Int, (∀ l ∈ wd, (((V.gk.getD (l.natAbs - 1) default).kind = 0 ∨
      (V.gk.getD (l.natAbs - 1) default).idx = i) ∨ (V.gk.getD (l.natAbs - 1) default).f2 = 0)) →
      wordVal Lg wd ∈ Subgroup.closure Γ := by
    intro wd hw
    refine wordVal_mem_of Lg _ wd fun l hl => ?_
    by_cases hlt : l.natAbs - 1 < ng
    · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
    · rw [List.getD_eq_default _ _ (by simp [hLg]; omega)]
      exact Subgroup.one_mem _
  obtain ⟨hwA, hwrest⟩ := band_e (PK.allN_iff.1 hwall i hi')
  obtain ⟨hwB, hwrest⟩ := band_e hwrest
  obtain ⟨hoA, hoB⟩ := band_e hwrest
  simp only [wordOK, allowed, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hoA hoB
  have hA' : wordVal Lg (V.wAs.getD i []) = a := (hwordG hwA).perm_eq ha
  have hB' : wordVal Lg (V.wBs.getD i []) = b := (hwordG hwB).perm_eq hb
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rintro g ⟨j, hj, -, rfl⟩
    exact hLgG _ (hLgmem j hj)
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact hall _ hoA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact hall _ hoB
  · rintro g ⟨j, hj, hok, rfl⟩
    obtain ⟨hidx, hk⟩ := band_e (PK.allN_iff.1 hkall j hj)
    have hidx' : (V.gk.getD j default).idx < V.ys.length := Nat.blt_eq.mp hidx
    generalize hf : V.gk.getD j default = f at hk hok hidx'
    unfold kindK at hk
    rw [PK.strictB_eq] at hk
    have huP := hzP
    have hvfP := hvP f.idx hidx'
    obtain ⟨hvE', hvp', hzv', hvz'⟩ := hvfacts f.idx hidx'
    have hyP := pr_mul (pr_pow hn huP f.f1) (pr_pow hn hvfP f.f2)
    by_cases hk0 : f.kind = 0
    · have hk' := bif_t (by rw [hk0]; rfl) hk
      obtain ⟨e1, e2⟩ := band_e hk'
      left
      refine ⟨⟨j, by rw [hgkl']; exact hj, by rw [hf]; exact hk0⟩, z, v f.idx, hzE, hvE', hzp',
        hvp', hzv', hz1', hvz', f.f1, f.f2, f.f3, f.f4, ?_, ?_⟩
      · exact (pr_beq (pr_mul (hgP j hj) huP) (pr_mul hyP (hgP j hj))).1 e1
      · exact (pr_beq (pr_mul (hgP j hj) hvfP)
          (pr_mul (pr_mul (pr_pow hn huP f.f3) (pr_pow hn hvfP f.f4)) (hgP j hj))).1 e2
    · have hk' := bif_f (Bool.eq_false_iff.2 fun e => hk0 (Nat.eq_of_beq_eq_true e)) hk
      obtain ⟨e0, hk'⟩ := band_e hk'
      obtain ⟨e1, e2⟩ := band_e hk'
      right
      refine ⟨z ^ f.f1 * v f.idx ^ f.f2, ?_, pr_ne hyP (pr_one hn) e0,
        (pr_beq (pr_pow hn hyP p) (pr_one hn)).1 e1, f.f3,
        (pr_beq (pr_mul (hgP j hj) hyP) (pr_mul (pr_pow hn hyP f.f3) (hgP j hj))).1 e2⟩
      rcases hok with (hk0' | hidx'') | hf2
      · exact absurd hk0' hk0
      · rw [hidx'', ← hYA]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      · rw [hf2, pow_zero, mul_one]
        exact Subgroup.pow_mem _ hzA _

theorem coreGenerationVOf_of_kchecks {n w : Nat} {V : VData}
    {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat} {cnt cap len : Nat}
    (H : KHyps n w V GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len) (hp : V.base.p.Prime)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    CoreGenerationVOf ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) V.base.p := by
  obtain ⟨E, hEp, hEc, hEG, hΓ⟩ := lines_facts H hp ha hb
  refine coreGenerationVOf_of_gens hp rfl hEp hEc hEG fun A hAE hAe hAc => ?_
  obtain ⟨Γ, h1, h2, h3⟩ := hΓ A hAE hAe hAc
  exact ⟨Γ, h1, h2, fun g hg => (h3 g hg).imp_left And.right⟩

theorem exists_normalizer_gens_of_kchecks {n w : Nat} {V : VData}
    {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat} {cnt cap len : Nat}
    (H : KHyps n w V GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len) (hp : V.base.p.Prime)
    (hk0 : ∀ j < V.gk.length, (V.gk.getD j default).kind ≠ 0)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))),
      Nat.card E = V.base.p ^ 3 ∧
      ∀ A : Subgroup ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))), A ≤ E →
        IsElemAbelian V.base.p A → Nat.card A = V.base.p ^ 2 →
        ∃ Γ : Set ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))),
          Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧
            g ∈ Subgroup.normalizer (Q : Set ↥(Subgroup.closure ({a, b} :
              Set (Equiv.Perm (Fin n))))) := by
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  obtain ⟨E, -, hEc, hEG, hΓ⟩ := lines_facts H hp ha hb
  refine ⟨E.subgroupOf G, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  intro A' hA'E hA'e hA'c
  set A : Subgroup (Equiv.Perm (Fin n)) := A'.map G.subtype with hAdef
  have hAE : A ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hA'E hx)
  have hAe : IsElemAbelian V.base.p A := CFSG.SectionRank.isElemAbelian_map hA'e _
  have hAc : Nat.card A = V.base.p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective G.subtype_injective, hA'c]
  obtain ⟨Γ, hΓG, hgen, hnorm⟩ := hΓ A hAE hAe hAc
  refine ⟨{g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}, ?_, ?_⟩
  · rw [eq_top_iff]
    intro h _
    have hmap : (Subgroup.closure {g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}).map G.subtype =
        Subgroup.closure Γ := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hz
        exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
    have hle : G ≤ (Subgroup.closure {g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}).map G.subtype := by
      rw [hmap, hGdef, Subgroup.closure_le]
      exact hgen
    obtain ⟨k, hk, hkh⟩ := hle h.2
    have : k = h := Subtype.ext hkh
    rwa [← this]
  · intro g hg
    rcases hnorm _ hg with ⟨⟨j, hj, hk⟩, -⟩ | ⟨y, hyA, hy1, -, α, h1⟩
    · exact absurd hk (hk0 j hj)
    · obtain ⟨y', hy'A, rfl⟩ := Subgroup.mem_map.1 hyA
      refine ⟨Subgroup.zpowers y', Subgroup.zpowers_le.2 hy'A, ?_,
        mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
      intro hbot
      apply hy1
      rw [Subgroup.zpowers_eq_bot.1 hbot]
      rfl

end CFSG.KD.CoreD2K

end

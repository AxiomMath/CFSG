module

public import CFSG.Certificates.Kernel.SporSch.TabChainLv
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import Certificates.Data.Kernel.SporSch.HeSrch

public section

namespace CFSG.KS.SporSch.Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier
  CFSG.KS.SporSch

variable {n : Nat}

theorem nIf_succ (b : Bool) (s : Nat) :
    Bool.rec (motive := fun _ => Nat) s (Nat.succ s) b = s + if b = true then 1 else 0 := by
  cases b <;> rfl

theorem lor_shl {a c o : Nat} (ha : a < 2 ^ o) : Nat.lor a (Nat.shiftLeft c o) = a + c * 2 ^ o := by
  change a ||| c <<< o = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]
  ring

theorem shl_lor (a c o d : Nat) :
    Nat.lor (Nat.shiftLeft a o) (Nat.shiftLeft c (o + d)) =
      Nat.shiftLeft (Nat.lor a (Nat.shiftLeft c d)) o := by
  change a <<< o ||| c <<< (o + d) = (a ||| c <<< d) <<< o
  rw [Nat.shiftLeft_or_distrib, Nat.add_comm o d, Nat.shiftLeft_add]

theorem nf5_eq {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < 65536) (h1 : k1 < 65536) (h2 : k2 < 65536)
    (h3 : k3 < 65536) :
    nf5 k0 k1 k2 k3 k4 = k0 + 65536 * (k1 + 65536 * (k2 + 65536 * (k3 + 65536 * k4))) := by
  have e : nf5 k0 k1 k2 k3 k4 = Nat.lor k0 (Nat.lor (Nat.shiftLeft k1 16)
      (Nat.lor (Nat.shiftLeft k2 (16 + 16)) (Nat.lor (Nat.shiftLeft k3 (16 + 16 + 16))
        (Nat.shiftLeft k4 (16 + 16 + 16 + 16))))) := rfl
  have p : (65536 : Nat) = 2 ^ 16 := by norm_num
  rw [p] at h0 h1 h2 h3
  rw [e, shl_lor k3 k4 (16 + 16 + 16) 16, lor_shl (c := k4) h3,
    shl_lor k2 (k3 + k4 * 2 ^ 16) (16 + 16) 16, lor_shl (c := k3 + k4 * 2 ^ 16) h2,
    shl_lor k1 (k2 + (k3 + k4 * 2 ^ 16) * 2 ^ 16) 16 16,
    lor_shl (c := k2 + (k3 + k4 * 2 ^ 16) * 2 ^ 16) h1,
    lor_shl (c := k1 + (k2 + (k3 + k4 * 2 ^ 16) * 2 ^ 16) * 2 ^ 16) h0]
  ring

theorem nf5_fld {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < 65536) (h1 : k1 < 65536) (h2 : k2 < 65536)
    (h3 : k3 < 65536) (h4 : k4 < 65536) {i : Nat} (hi : i < 5) :
    nf5 k0 k1 k2 k3 k4 / 2 ^ (16 * i) % 65536 = [k0, k1, k2, k3, k4][i] := by
  rw [nf5_eq h0 h1 h2 h3]
  interval_cases i <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> norm_num <;>
    omega

theorem nfArr_nf5 {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < 65536) (h1 : k1 < 65536) (h2 : k2 < 65536)
    (h3 : k3 < 65536) (h4 : k4 < 65536) : nfArr 5 (nf5 k0 k1 k2 k3 k4) = #[k0, k1, k2, k3, k4] := by
  apply Array.ext (by simp [nfArr])
  intro i hi _
  simp only [nfArr, Array.size_ofFn] at hi
  simp only [nfArr, Array.getElem_ofFn]
  rw [nf5_fld h0 h1 h2 h3 h4 hi]
  interval_cases i <;> rfl

@[expose] noncomputable def E5 (n : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (k : Nat × Nat × Nat × Nat × Nat) : Equiv.Perm (Fin n) :=
  levT n S base 0 k.1 * levT n S base 1 k.2.1 * levT n S base 2 k.2.2.1 *
    levT n S base 3 k.2.2.2.1 * levT n S base 4 k.2.2.2.2

@[expose] def box5 (n : Nat) (S : Array (Array Nat)) (base : Array Nat) :
    Finset (Nat × Nat × Nat × Nat × Nat) :=
  Finset.range (lev n S base 0).pts.size ×ˢ Finset.range (lev n S base 1).pts.size ×ˢ
    Finset.range (lev n S base 2).pts.size ×ˢ Finset.range (lev n S base 3).pts.size ×ˢ
    Finset.range (lev n S base 4).pts.size

theorem prod_ofFn5 {G : Type*} [Monoid G] {m : Nat} (h5 : m = 5) (f : Fin m → G) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ * f ⟨1, by omega⟩ * f ⟨2, by omega⟩ * f ⟨3, by omega⟩ *
      f ⟨4, by omega⟩ := by
  subst h5
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

section NF

variable {Q : RawSchreierDatum n} {O S : Array (Array Nat)} {base : Array Nat}
  {W : Array (List Int)} {chunks : Nat} (hA : ChainArrays Q O S base W)
  (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) (h5 : Q.baseCount = 5)

include hA hF in
theorem levT_spec {i k : Nat} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size) :
    levT n S base i k ∈ Q.levelSubgroup i ∧
      levT n S base i k (Q.base.get ⟨i, hi⟩) = levPts Q S base i k := by
  have ht := hA.transversal_of_lt hF hi hk
  have hx : levPts Q S base i k ∈ Q.orbitPoints ⟨i, hi⟩ := by
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).isSome = true
    rw [ht]
    rfl
  have h := Q.transversal_getD_spec ⟨i, hi⟩ _ hx
  have e : (Q.transversal? ⟨i, hi⟩ (levPts Q S base i k)).getD 1 = levT n S base i k := by
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).getD 1 = _
    rw [ht, Option.getD_some]
  rw [e] at h
  exact ⟨h.2.1, h.2.2⟩

include hA hF in
theorem levT_fix {i j k : Nat} (hi : i < Q.baseCount) (hji : j < i)
    (hk : k < (lev n S base i).pts.size) :
    levT n S base i k (Q.base.get ⟨j, lt_trans hji hi⟩) = Q.base.get ⟨j, lt_trans hji hi⟩ := by
  have h1 := Q.levelSubgroup_antitone (j + 1) i hji (levT_spec hA hF hi hk).1
  have h2 : levT n S base i k ∈
      MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get ⟨j, lt_trans hji hi⟩) :=
    (Q.levelSubgroup_succ_le_stabilizer ⟨j, lt_trans hji hi⟩ h1).2
  rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h2

include hA hF in
theorem levPts_inj {i k k' : Nat} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size)
    (hk' : k' < (lev n S base i).pts.size) (e : levPts Q S base i k = levPts Q S base i k') :
    k = k' := by
  have F := hA.levelFacts hF hi
  have e1 := congrArg Fin.val e
  rw [hA.levPts_val hF hi hk, hA.levPts_val hF hi hk'] at e1
  rw [← F.pos_pts k hk, ← F.pos_pts k' hk', e1]

include hA hF hQ h5 in
theorem E5_mem {k : Nat × Nat × Nat × Nat × Nat} (hk : k ∈ box5 n S base) :
    E5 n S base k ∈ Q.originalSubgroup := by
  simp only [box5, Finset.mem_product, Finset.mem_range] at hk
  obtain ⟨h0, h1, h2, h3, h4⟩ := hk
  have hm : ∀ i (hi : i < 5) {k : Nat}, k < (lev n S base i).pts.size →
      levT n S base i k ∈ Q.originalSubgroup := fun i hi k hk => by
    rw [← Q.levelSubgroup_zero_eq_original hQ]
    exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) (levT_spec hA hF (by omega) hk).1
  unfold E5
  exact Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem
    (Q.originalSubgroup.mul_mem (hm 0 (by omega) h0) (hm 1 (by omega) h1)) (hm 2 (by omega) h2))
    (hm 3 (by omega) h3)) (hm 4 (by omega) h4)

include hA hF hQ h5 in
theorem E5_bij : (∀ g ∈ Q.originalSubgroup, ∃ k ∈ box5 n S base, E5 n S base k = g) ∧
    ∀ k ∈ box5 n S base, ∀ k' ∈ box5 n S base, E5 n S base k = E5 n S base k' → k = k' := by
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  have hT : ∀ (i : Fin Q.baseCount) (x : Q.orbitPoints i), Q.orbitTransversal i x =
      levT n S base i (lev n S base i).pos[((x : Fin n) : Nat)]! ∧
        (lev n S base i).pos[((x : Fin n) : Nat)]! < (lev n S base i).pts.size := fun i x =>
    ⟨(hA.orbitPoints_spec hF i.2 x.2).2.2, (hA.orbitPoints_spec hF i.2 x.2).1⟩
  have hprod : ∀ y, (Φ y : Equiv.Perm (Fin n)) = E5 n S base
      ((lev n S base 0).pos[((y ⟨0, by omega⟩ : Fin n) : Nat)]!,
       (lev n S base 1).pos[((y ⟨1, by omega⟩ : Fin n) : Nat)]!,
       (lev n S base 2).pos[((y ⟨2, by omega⟩ : Fin n) : Nat)]!,
       (lev n S base 3).pos[((y ⟨3, by omega⟩ : Fin n) : Nat)]!,
       (lev n S base 4).pos[((y ⟨4, by omega⟩ : Fin n) : Nat)]!) := fun y => by
    rw [hΦ y, prod_ofFn5 h5, (hT _ _).1, (hT _ _).1, (hT _ _).1, (hT _ _).1, (hT _ _).1]
    rfl
  refine ⟨fun g hg => ?_, fun k hk k' hk' e => ?_⟩
  · obtain ⟨y, hy⟩ := hbij.2 ⟨g, hg⟩
    refine ⟨_, ?_, (hprod y).symm.trans (congrArg Subtype.val hy)⟩
    simp only [box5, Finset.mem_product, Finset.mem_range]
    exact ⟨(hT _ _).2, (hT _ _).2, (hT _ _).2, (hT _ _).2, (hT _ _).2⟩
  · have mk : ∀ k ∈ box5 n S base, ∃ y, (Φ y : Equiv.Perm (Fin n)) = E5 n S base k ∧
        ∀ (i : Fin Q.baseCount), (y i : Fin n) =
          levPts Q S base i [k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2][i.val]! := by
      intro k hk
      simp only [box5, Finset.mem_product, Finset.mem_range] at hk
      have hkk : ∀ i : Fin Q.baseCount, [k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2][i.val]! <
          (lev n S base i).pts.size := fun i => by
        obtain ⟨i, hi⟩ := i
        have : i < 5 := h5 ▸ hi
        interval_cases i <;> simp [hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2]
      let y : ∀ i : Fin Q.baseCount, Q.orbitPoints i := fun i =>
        ⟨levPts Q S base i [k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2][i.val]!, by
          change ((Q.orbitSearch i).transversal? _).isSome = true
          rw [hA.transversal_of_lt hF i.2 (hkk i)]
          rfl⟩
      have hpos : ∀ i : Fin Q.baseCount, (lev n S base i).pos[((y i : Fin n) : Nat)]! =
          [k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2][i.val]! := fun i => by
        change (lev n S base i).pos[((levPts Q S base i _ : Fin n) : Nat)]! = _
        rw [hA.levPts_val hF i.2 (hkk i), (hA.levelFacts hF i.2).pos_pts _ (hkk i)]
      refine ⟨y, ?_, fun i => rfl⟩
      rw [hprod y, hpos ⟨0, by omega⟩, hpos ⟨1, by omega⟩, hpos ⟨2, by omega⟩, hpos ⟨3, by omega⟩,
        hpos ⟨4, by omega⟩]
      rfl
    obtain ⟨y, hy, hyk⟩ := mk k hk
    obtain ⟨y', hy', hyk'⟩ := mk k' hk'
    have hyy : y = y' := hbij.1 (Subtype.ext (by rw [hy, hy', e]))
    simp only [box5, Finset.mem_product, Finset.mem_range] at hk hk'
    have hc : ∀ (i : Nat) (hi : i < 5),
        [k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2][i]! =
          [k'.1, k'.2.1, k'.2.2.1, k'.2.2.2.1, k'.2.2.2.2][i]! := fun i hi => by
      have e1 := (hyk ⟨i, by omega⟩).symm.trans ((congrArg (fun y => (y ⟨i, by omega⟩ : Fin n)) hyy).trans
        (hyk' ⟨i, by omega⟩))
      refine levPts_inj hA hF (by omega) ?_ ?_ e1
      · interval_cases i <;> simp [hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2]
      · interval_cases i <;> simp [hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2]
    have c0 := hc 0 (by norm_num)
    have c1 := hc 1 (by norm_num)
    have c2 := hc 2 (by norm_num)
    have c3 := hc 3 (by norm_num)
    have c4 := hc 4 (by norm_num)
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at c0 c1 c2 c3 c4
    obtain ⟨a, b, c, d, e⟩ := k
    obtain ⟨a', b', c', d', e'⟩ := k'
    simp only at c0 c1 c2 c3 c4
    rw [c0, c1, c2, c3, c4]

include hA hF hQ h5 in
theorem card5 (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Nat.card {g : Q.originalSubgroup // P g} =
      ∑ k ∈ box5 n S base, if P (E5 n S base k) then 1 else 0 := by
  rw [← Finset.card_filter]
  obtain ⟨hex, hinj⟩ := E5_bij hA hF hQ h5
  let f : {k // k ∈ (box5 n S base).filter fun k => P (E5 n S base k)} →
      {g : Q.originalSubgroup // P g} := fun k =>
    ⟨⟨E5 n S base k.1, E5_mem hA hF hQ h5 (Finset.mem_filter.1 k.2).1⟩, (Finset.mem_filter.1 k.2).2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (hinj _ (Finset.mem_filter.1 a.2).1 _
      (Finset.mem_filter.1 b.2).1 (congrArg (fun g : {g : Q.originalSubgroup // P g} =>
        (g.1 : Equiv.Perm (Fin n))) hab)), fun g => ?_⟩
    obtain ⟨k, hk, e⟩ := hex g.1 g.1.2
    refine ⟨⟨k, Finset.mem_filter.2 ⟨hk, by rw [e]; exact g.2⟩⟩, Subtype.ext (Subtype.ext e)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe]

include hA hF in
theorem base_map_val : Q.base.toList.map Fin.val = base.toList := by
  rw [hA.base_toList hF, List.map_map]
  apply List.ext_getElem (by simp [hA.base_size])
  intro k h1 _
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Array.getElem_toList]
  rw [toFin_eq Q (hF.base_lt k (by rw [hA.base_size]; exact h1)), ← getElem!_pos base k
    (by rw [hA.base_size]; exact h1)]

end NF

theorem nfElt5 {S : Array (Array Nat)} {base : Array Nat} (a b c d e : Nat) :
    nfElt n S base #[a, b, c, d, e] = E5 n S base (a, b, c, d, e) := by
  simp only [nfElt, E5, List.size_toArray, List.length_cons, List.length_nil, List.range_succ,
    List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem getD_base {base : Array Nat} {l : List Nat} (h : base.toList = l) {i : Nat}
    (hi : i < l.length) : base[i]! = l[i] := by
  have hi' : i < base.size := by rw [← Array.length_toList, h]; exact hi
  rw [getElem!_pos base i hi', ← Array.getElem_toList]
  exact List.getElem_of_eq h _

theorem nfValid_nf5 {LR : Nat → Nat} {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < rcnt (LR 0))
    (h1 : k1 < rcnt (LR 1)) (h2 : k2 < rcnt (LR 2)) (h3 : k3 < rcnt (LR 3)) (h4 : k4 < rcnt (LR 4)) :
    nfValidK 5 LR (nf5 k0 k1 k2 k3 k4) = true := by
  unfold nfValidK
  rw [Orb.allN_iff]
  intro t ht
  rw [fld16, Nat.mul_eq, nf5_fld (lt_trans h0 (rcnt_lt _)) (lt_trans h1 (rcnt_lt _))
    (lt_trans h2 (rcnt_lt _)) (lt_trans h3 (rcnt_lt _)) (lt_trans h4 (rcnt_lt _)) ht]
  apply Nat.blt_eq.mpr
  interval_cases t <;> assumption

section Counts

variable {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat} {Q : RawSchreierDatum n} {O : Array (Array Nat)}
  {W : Array (List Int)} {chunks : Nat}

theorem stab0_spec {b0 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base (b0 :: bs))
    (hb0 : b0 < n) {t : Nat → Bool} {Pr : Equiv.Perm (Fin n) → Prop} [DecidablePred Pr]
    (ht : ∀ F, nfValidK 5 LR F = true → F % 65536 = 0 →
      (t F = true ↔ Pr (nfElt n S base (nfArr 5 F)))) :
    cnt0R LR t 0 (rcnt (LR 1)) =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ = ⟨b0, hb0⟩ ∧
        Pr g} := by
  obtain ⟨hb, hp, ho, hN, htab, hbs⟩ := hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h5 : Q.baseCount = 5 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm : ∀ i < 5, (lev n S base i).pts.size = rcnt (LR i) := fun i hi =>
    (cnt_eq hb hp ho hN hi).symm
  have hβ : Q.base.get ⟨0, by omega⟩ = ⟨b0, hb0⟩ := Fin.ext ((hA.base_val ⟨0, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hfix : ∀ k ∈ box5 n S base, E5 n S base k ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
    intro k hk
    simp only [box5, Finset.mem_product, Finset.mem_range] at hk
    rw [← hβ]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      levT_fix hA hF (i := 1) (by omega) (by omega) hk.2.1,
      (levT_spec hA hF (by omega) hk.1).2]
  have hroot : levPts Q S base 0 0 = ⟨b0, hb0⟩ := by
    have := (levT_spec hA hF (i := 0) (k := 0) (by omega) (hA.levelFacts hF (by omega)).pos).2
    rw [hA.levT_zero hF (by omega), Equiv.Perm.one_apply, hβ] at this
    exact this.symm
  rw [card5 hA hF hQ h5 (fun g => g ⟨b0, hb0⟩ = ⟨b0, hb0⟩ ∧ Pr g)]
  unfold cnt0R
  rw [sumN_eq, lsum]
  have e2 : rcnt (LR (nat_lit 2)) = (lev n S base 2).pts.size := (hm 2 (by norm_num)).symm
  have e3 : rcnt (LR (nat_lit 3)) = (lev n S base 3).pts.size := (hm 3 (by norm_num)).symm
  have e4 : rcnt (LR (nat_lit 4)) = (lev n S base 4).pts.size := (hm 4 (by norm_num)).symm
  unfold box5
  simp only [Finset.sum_product]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (hA.levelFacts hF (by omega)).pos)
    (fun a ha hne => Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun c hc =>
      Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun e he => ?_)]
  · rw [← hm 1 (by norm_num)]
    refine Finset.sum_congr rfl fun b hb => ?_
    unfold cnt234
    rw [e2, e3, e4, Nat.add_eq, Nat.zero_add]
    rw [foldUp_add _ (fun c _ s => foldUp_add _ (fun d _ s => foldUp_add _
      (fun e _ s => by rw [strictN_eq, nIf_succ]) s) s), Nat.zero_add]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd =>
      Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_range] at hb hc hd he
    have hk : ((0 : Nat), b, c, d, e) ∈ box5 n S base := by
      simp only [box5, Finset.mem_product, Finset.mem_range]
      exact ⟨(hA.levelFacts hF (by omega)).pos, hb, hc, hd, he⟩
    have h65 : ∀ i < 5, (lev n S base i).pts.size < 65536 := fun i hi =>
      (hm i hi) ▸ rcnt_lt _
    have h00 : 0 < rcnt (LR 0) := by
      rw [← hm 0 (by norm_num)]
      exact (hA.levelFacts hF (by omega)).pos
    have hv := nfValid_nf5 (LR := LR) (k0 := 0) h00 (hm 1 (by norm_num) ▸ hb)
      (hm 2 (by norm_num) ▸ hc) (hm 3 (by norm_num) ▸ hd) (hm 4 (by norm_num) ▸ he)
    have hz : nf5 0 b c d e % 65536 = 0 := by
      have := nf5_fld (k0 := 0) (by norm_num) (lt_trans hb (h65 1 (by norm_num)))
        (lt_trans hc (h65 2 (by norm_num))) (lt_trans hd (h65 3 (by norm_num)))
        (lt_trans he (h65 4 (by norm_num))) (i := 0) (by norm_num)
      simpa using this
    have hiff := ht _ hv hz
    rw [nfArr_nf5 (k0 := 0) (by norm_num) (lt_trans hb (h65 1 (by norm_num)))
      (lt_trans hc (h65 2 (by norm_num))) (lt_trans hd (h65 3 (by norm_num)))
      (lt_trans he (h65 4 (by norm_num))), nfElt5] at hiff
    rw [hfix _ hk, hroot]
    simp only [true_and, hiff]
  · have hk : (a, b, c, d, e) ∈ box5 n S base := by
      simp only [box5, Finset.mem_product]
      exact ⟨ha, hb, hc, hd, he⟩
    refine ite_eq_right_iff.2 fun h => absurd h ?_
    rintro ⟨h1, -⟩
    rw [hfix _ hk, ← hroot] at h1
    exact hne (levPts_inj hA hF (by omega) (Finset.mem_range.1 ha)
      (hA.levelFacts hF (by omega)).pos h1)

theorem ite_sum {C : Prop} [Decidable C] (s : Finset Nat) (f : Nat → Nat) :
    (if C then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if C then f i else 0 := by
  split_ifs <;> simp

theorem srchAAt_eq_sum {b0 b1 b2 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) {a : Nat} (ha : a < (lev n S base 0).pts.size) :
    srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y a =
      ∑ b ∈ Finset.range (lev n S base 1).pts.size, ∑ c ∈ Finset.range (lev n S base 2).pts.size,
        ∑ d ∈ Finset.range (lev n S base 3).pts.size, ∑ e ∈ Finset.range (lev n S base 4).pts.size,
          if E5 n S base (a, b, c, d, e) * x = y * E5 n S base (a, b, c, d, e) then 1 else 0 := by
  obtain ⟨hb, hp, ho, hN, htab, hbs⟩ := hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h5 : Q.baseCount = 5 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm : ∀ i < 5, (lev n S base i).pts.size = rcnt (LR i) := fun i hi =>
    (cnt_eq hb hp ho hN hi).symm
  have hbl := base_lt hb ho hN
  have hb0 : b0 < n := by
    have := hbl 0 (by norm_num)
    rwa [getD_base hbs (i := 0) (by simp)] at this
  have hb1 : b1 < n := by
    have := hbl 1 (by norm_num)
    rwa [getD_base hbs (i := 1) (by simp)] at this
  have hb2 : b2 < n := by
    have := hbl 2 (by norm_num)
    rwa [getD_base hbs (i := 2) (by simp)] at this
  have hβ0 : Q.base.get ⟨0, by omega⟩ = ⟨b0, hb0⟩ := Fin.ext ((hA.base_val ⟨0, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hβ1 : Q.base.get ⟨1, by omega⟩ = ⟨b1, hb1⟩ := Fin.ext ((hA.base_val ⟨1, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hβ2 : Q.base.get ⟨2, by omega⟩ = ⟨b2, hb2⟩ := Fin.ext ((hA.base_val ⟨2, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hfaith : BaseFaithful Q.originalSubgroup (b0 :: b1 :: b2 :: bs) := by
    have := baseFaithful_of_valid hQ
    rwa [base_map_val hA hF, hbs] at this
  have hlt : ∀ b ∈ b0 :: b1 :: b2 :: bs, b < n := fun b hb' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb'
    rw [← getD_base hbs hi]
    have : i < 5 := by rw [← hb.2.2.2.2.2.1, ← Array.length_toList, hbs]; exact hi
    exact hbl i this
  have hx0 : x ⟨b0, hb0⟩ = ⟨b0, hb0⟩ := Fin.ext ((hX b0 hb0).symm.trans h0)
  have hx1 : x ⟨b1, hb1⟩ = ⟨b2, hb2⟩ := Fin.ext ((hX b1 hb1).symm.trans h1)
  have hk' : ∀ {k : Nat × Nat × Nat × Nat × Nat}, k ∈ box5 n S base →
      k.1 < (lev n S base 0).pts.size ∧ k.2.1 < (lev n S base 1).pts.size ∧
        k.2.2.1 < (lev n S base 2).pts.size ∧ k.2.2.2.1 < (lev n S base 3).pts.size ∧
          k.2.2.2.2 < (lev n S base 4).pts.size := fun hk => by
    simpa only [box5, Finset.mem_product, Finset.mem_range] using hk
  have f0 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
    intro k hk
    have hk := hk' hk
    rw [← hβ0]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      levT_fix hA hF (i := 1) (by omega) (by omega) hk.2.1,
      (levT_spec hA hF (by omega) hk.1).2]
  have f1 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b1, hb1⟩ =
      levT n S base 0 k.1 (levPts Q S base 1 k.2.1) := by
    intro k hk
    have hk := hk' hk
    rw [← hβ1]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      (levT_spec hA hF (by omega) hk.2.1).2]
  have f2 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b2, hb2⟩ =
      levT n S base 0 k.1 (levT n S base 1 k.2.1 (levPts Q S base 2 k.2.2.1)) := by
    intro k hk
    have hk := hk' hk
    rw [← hβ2]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      (levT_spec hA hF (by omega) hk.2.2.1).2]
  have h65 : ∀ i < 5, (lev n S base i).pts.size < 65536 := fun i hi => (hm i hi) ▸ rcnt_lt _
  have eqv : ∀ k ∈ box5 n S base,
      (eqOnL (b0 :: b1 :: b2 :: bs)
        (fun b => nfPtT w NR NL LT PT 5 (nf5 k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) (X b))
        (fun b => Y (nfPtT w NR NL LT PT 5 (nf5 k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) b)) = true ↔
        E5 n S base k * x = y * E5 n S base k) := by
    intro k hk
    have hk := hk' hk
    have hv := nfValid_nf5 (LR := LR) (hm 0 (by norm_num) ▸ hk.1) (hm 1 (by norm_num) ▸ hk.2.1)
      (hm 2 (by norm_num) ▸ hk.2.2.1) (hm 3 (by norm_num) ▸ hk.2.2.2.1)
      (hm 4 (by norm_num) ▸ hk.2.2.2.2)
    have hR := (nfPtT_spec hb hp ho hN htab hv).2
    have e : nfA 5 (nf5 k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) = #[k.1, k.2.1, k.2.2.1, k.2.2.2.1,
        k.2.2.2.2] := nfArr_nf5 (lt_trans hk.1 (h65 0 (by norm_num)))
      (lt_trans hk.2.1 (h65 1 (by norm_num))) (lt_trans hk.2.2.1 (h65 2 (by norm_num)))
      (lt_trans hk.2.2.2.1 (h65 3 (by norm_num))) (lt_trans hk.2.2.2.2 (h65 4 (by norm_num)))
    rw [e, nfElt5] at hR
    rw [eqOnL_iff]
    have hmem := E5_mem hA hF hQ h5 (k := k) (by simpa only [box5, Finset.mem_product,
      Finset.mem_range] using hk)
    constructor
    · intro hall
      have h1 := hfaith _ (hxy _ hmem) fun z hz => by
        have := hall z hz
        rw [hX z z.2, hR _ (hX z z.2 ▸ (x z).2), hR z z.2, hY _ (E5 n S base k z).2] at this
        rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply]
        exact (Fin.ext this).symm
      exact (inv_mul_eq_one.1 h1)
    · intro he b hb'
      have hbn := hlt b hb'
      rw [hX b hbn, hR _ (x ⟨b, hbn⟩).2, hR b hbn, hY _ (E5 n S base k ⟨b, hbn⟩).2]
      have := congrArg (fun g => ((g ⟨b, hbn⟩ : Fin n) : Nat)) he
      simpa only [Equiv.Perm.mul_apply] using this
  have hT0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trPtT w NR NL LT PT (nat_lit 0) a z = (levT n S base 0 a ⟨z, hz⟩ : Nat) := fun ha z hz => by
    rw [trPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
      ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hI0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trInvPtT w kS NR NL LT PT (nat_lit 0) a z = ((levT n S base 0 a)⁻¹ ⟨z, hz⟩ : Nat) :=
    fun ha z hz => by
      rw [trInvPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
        ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hI1 : ∀ {b : Nat}, b < rcnt (LR (nat_lit 1)) → ∀ z (hz : z < n),
      trInvPtT w kS NR NL LT PT (nat_lit 1) b z = ((levT n S base 1 b)⁻¹ ⟨z, hz⟩ : Nat) :=
    fun hb' z hz => by
      rw [trInvPtT_eq hb hp ho hN htab (by norm_num) hb' ⟨z, hz⟩,
        ← trT_eq_levT hb hp ho hN (by norm_num) hb']
  have hpt : ∀ {i k : Nat}, i < 5 → k < (lev n S base i).pts.size →
      rpt w (mask w) (LR i) k = (levPts Q S base i k : Nat) := by
    intro i k hi hk
    rw [(agree hb hp ho hN hi).2.pt k hk, hA.levPts_val hF (by omega) hk]
  have forced : ∀ k ∈ box5 n S base, E5 n S base k * x = y * E5 n S base k →
      y (levT n S base 0 k.1 ⟨b0, hb0⟩) = levT n S base 0 k.1 ⟨b0, hb0⟩ ∧
        rpos w (mask w) (n * w) (LR 2) ((levT n S base 1 k.2.1)⁻¹ ((levT n S base 0 k.1)⁻¹
          (y (levT n S base 0 k.1 (levPts Q S base 1 k.2.1)))) : Nat) = k.2.2.1 := by
    intro k hk he
    have hk2 := hk' hk
    have hP0 : levT n S base 0 k.1 ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
      rw [← hβ0]
      exact (levT_spec hA hF (by omega) hk2.1).2
    have e0 := congrArg (fun g => g ⟨b0, hb0⟩) he
    have e1 := congrArg (fun g => g ⟨b1, hb1⟩) he
    simp only [Equiv.Perm.mul_apply] at e0 e1
    rw [hx0, f0 _ hk] at e0
    rw [hx1, f2 _ hk, f1 _ hk] at e1
    refine ⟨by rw [hP0]; exact e0.symm, ?_⟩
    rw [← e1, Equiv.Perm.inv_eq_iff_eq.2 rfl, Equiv.Perm.inv_eq_iff_eq.2 rfl,
      ← hpt (by norm_num) hk2.2.2.1]
    exact ((recFacts ho hN (i := 2) (by norm_num)).pt _ (hm 2 (by norm_num) ▸ hk2.2.2.1)).2
  have ha' : a < rcnt (LR (nat_lit 0)) := hm 0 (by norm_num) ▸ ha
  have mem : ∀ {b c d e : Nat}, b < (lev n S base 1).pts.size → c < (lev n S base 2).pts.size →
      d < (lev n S base 3).pts.size → e < (lev n S base 4).pts.size →
      (a, b, c, d, e) ∈ box5 n S base := fun hb' hc' hd' he' => by
    simp only [box5, Finset.mem_product, Finset.mem_range]
    exact ⟨ha, hb', hc', hd', he'⟩
  set P0 := levT n S base 0 a ⟨b0, hb0⟩ with hP0
  unfold srchAAt
  rw [strictN_eq, hT0 ha' b0 hb0, hY _ P0.2]
  by_cases hy0 : y P0 = P0
  · rw [hy0, Nat.beq_refl]
    change foldUp _ _ (nat_lit 0) = _
    have e1 : rcnt (LR (nat_lit 1)) = (lev n S base 1).pts.size := (hm 1 (by norm_num)).symm
    have e2 : rcnt (LR (nat_lit 2)) = (lev n S base 2).pts.size := (hm 2 (by norm_num)).symm
    have e3 : rcnt (LR (nat_lit 3)) = (lev n S base 3).pts.size := (hm 3 (by norm_num)).symm
    have e4 : rcnt (LR (nat_lit 4)) = (lev n S base 4).pts.size := (hm 4 (by norm_num)).symm
    rw [foldUp_add (fun b => ∑ c ∈ Finset.range (lev n S base 2).pts.size,
      ∑ d ∈ Finset.range (lev n S base 3).pts.size, ∑ e ∈ Finset.range (lev n S base 4).pts.size,
        if E5 n S base (a, b, c, d, e) * x = y * E5 n S base (a, b, c, d, e) then 1 else 0)
      (fun b hb' s => ?_) 0, Nat.zero_add, e1]
    rw [e1] at hb'
    have hb'' : b < rcnt (LR (nat_lit 1)) := e1 ▸ hb'
    have hq := hT0 ha' _ (levPts Q S base 1 b).2
    rw [strictN_eq, hpt (by norm_num) hb', hq, strictN_eq, hY _ (levT n S base 0 a _).2,
      hI0 ha' _ (y _).2, hI1 hb'' _ ((levT n S base 0 a)⁻¹ _).2, strictN_eq,
      lvT_QT htab (by norm_num) ((levT n S base 1 b)⁻¹ _).2, e2]
    simp only [Fin.eta]
    set K2 := rpos w (mask w) (n * w) (LR 2) ((levT n S base 1 b)⁻¹ ((levT n S base 0 a)⁻¹
      (y (levT n S base 0 a (levPts Q S base 1 b)))) : Nat) with hK2
    by_cases hK : K2 < (lev n S base 2).pts.size
    · rw [blt_true hK]
      dsimp only
      rw [e3, e4, foldUp_add _ (fun d _ s => foldUp_add _ (fun e _ s => by rw [strictN_eq, nIf_succ]) s) s]
      congr 1
      rw [Finset.sum_eq_single_of_mem K2 (Finset.mem_range.2 hK) (fun c hc hne =>
        Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun e he => ?_)]
      · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
        rw [Finset.mem_range] at hd he
        have hiff := eqv _ (mem hb' hK hd he)
        simp only at hiff
        simp only [hiff]
      · rw [Finset.mem_range] at hc hd he
        refine ite_eq_right_iff.2 fun h => absurd ?_ hne
        exact ((forced _ (mem hb' hc hd he) h).2).symm.trans hK2.symm |>.symm ▸ rfl
    · rw [blt_false hK]
      dsimp only
      refine (Nat.add_eq_left.2 ?_).symm
      refine Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun d hd =>
        Finset.sum_eq_zero fun e he => ite_eq_right_iff.2 fun h => absurd ?_ hK
      rw [Finset.mem_range] at hc hd he
      have := (forced _ (mem hb' hc hd he) h).2
      simp only at this
      rw [hK2, this]
      exact hc
  · have hne : Nat.beq ((y P0 : Fin n) : Nat) (P0 : Nat) = false := by
      rw [beq_dec]
      exact decide_eq_false fun h => hy0 (Fin.ext h)
    rw [hne]
    dsimp only
    symm
    refine Finset.sum_eq_zero fun b hb' => Finset.sum_eq_zero fun c hc =>
      Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun e he => ite_eq_right_iff.2 fun h =>
        absurd ?_ hy0
    rw [Finset.mem_range] at hb' hc hd he
    exact (forced _ (mem hb' hc hd he) h).1

theorem srchA_spec {b0 b1 b2 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) :
    sumN (rcnt (LR 0)) (srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y) =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) * x = y * g} := by
  obtain ⟨hb, hp, ho, hN, -, -⟩ := id hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h5 : Q.baseCount = 5 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm0 : (lev n S base 0).pts.size = rcnt (LR 0) := (cnt_eq hb hp ho hN (by norm_num)).symm
  rw [card5 hA hF hQ h5 (fun g => g * x = y * g), sumN_eq, lsum, ← hm0]
  unfold box5
  simp only [Finset.sum_product]
  exact Finset.sum_congr rfl fun a ha =>
    srchAAt_eq_sum hA hc hch hT hX hY hxy h0 h1 (Finset.mem_range.1 ha)

theorem srchAAt_card {b0 b1 b2 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) (hb0 : b0 < n) {a : Nat} (ha : a < rcnt (LR 0)) :
    srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y a =
      Nat.card {g : Q.originalSubgroup // (((g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ : Fin n) : Nat) =
        trPtT w NR NL LT PT (nat_lit 0) a b0 ∧ (g : Equiv.Perm (Fin n)) * x = y * g} := by
  obtain ⟨hb, hp, ho, hN, htab, hbs⟩ := id hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h5 : Q.baseCount = 5 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm : ∀ i < 5, (lev n S base i).pts.size = rcnt (LR i) := fun i hi =>
    (cnt_eq hb hp ho hN hi).symm
  have ha0 : a < (lev n S base 0).pts.size := (hm 0 (by norm_num)) ▸ ha
  have hβ0 : Q.base.get ⟨0, by omega⟩ = ⟨b0, hb0⟩ := Fin.ext ((hA.base_val ⟨0, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hP : trPtT w NR NL LT PT (nat_lit 0) a b0 = (levPts Q S base 0 a : Nat) := by
    rw [trPtT_eq hb hp ho hN htab (by norm_num) ha ⟨b0, hb0⟩,
      ← trT_eq_levT hb hp ho hN (by norm_num) ha, ← hβ0, (levT_spec hA hF (by omega) ha0).2]
  have f0 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
    intro k hk
    simp only [box5, Finset.mem_product, Finset.mem_range] at hk
    rw [← hβ0]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      levT_fix hA hF (i := 1) (by omega) (by omega) hk.2.1,
      (levT_spec hA hF (by omega) hk.1).2]
  rw [srchAAt_eq_sum hA hc hch hT hX hY hxy h0 h1 ha0, card5 hA hF hQ h5 (fun g =>
    ((g ⟨b0, hb0⟩ : Fin n) : Nat) = trPtT w NR NL LT PT (nat_lit 0) a b0 ∧ g * x = y * g)]
  unfold box5
  simp only [Finset.sum_product]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_range.2 ha0) (fun a' ha' hne =>
    Finset.sum_eq_zero fun b hb' => Finset.sum_eq_zero fun c hc' => Finset.sum_eq_zero fun d hd =>
      Finset.sum_eq_zero fun e he => ite_eq_right_iff.2 fun h => absurd ?_ hne)]
  · refine Finset.sum_congr rfl fun b hb' => Finset.sum_congr rfl fun c hc' =>
      Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
    have hk : (a, b, c, d, e) ∈ box5 n S base := by
      simp only [box5, Finset.mem_product]
      exact ⟨Finset.mem_range.2 ha0, hb', hc', hd, he⟩
    rw [f0 _ hk, hP]
    simp only [true_and]
  · have hk : (a', b, c, d, e) ∈ box5 n S base := by
      simp only [box5, Finset.mem_product]
      exact ⟨ha', hb', hc', hd, he⟩
    have h1' := h.1
    rw [f0 _ hk, hP] at h1'
    exact levPts_inj hA hF (by omega) (Finset.mem_range.1 ha') ha0 (Fin.ext h1')

end Counts

end CFSG.KS.SporSch.Tab

end

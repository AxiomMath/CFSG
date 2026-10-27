module

public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.RankThree.Native.PrimeLines

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Certificates.ChainArrays

theorem gLAPPrimeCoreOf_eq_bot_of_card_lt_three_mul {G : Type*} [Group G] [Finite G]
    {X T : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup 3 T)
    (hCT : IsPGroup 3 ↥(Subgroup.centralizer (T : Set G)))
    (hlt : Nat.card X < 3 * Nat.card T) : GLAPPrimeCoreOf 3 X = ⊥ := by
  set N := GLAPPrimeCoreOf 3 X with hN
  have hNX : N ≤ X := GLAPPrimeCoreOf_le X
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three X
  have hNT : N ⊓ T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.inf_eq_bot_of_coprime_isPGroup
      Nat.prime_three hcop hT
  have hinj : Function.Injective fun x : ↥N × ↥T =>
      (⟨(x.1 : G) * x.2, X.mul_mem (hNX x.1.2) (hTX x.2.2)⟩ : ↥X) := by
    rintro ⟨n, t⟩ ⟨n', t'⟩ h
    have h1 : (n : G) * t = n' * t' := congrArg Subtype.val h
    have h2 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
      calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
        _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
      ⟨N.mul_mem (N.inv_mem n'.2) n.2, h2 ▸ T.mul_mem t'.2 (T.inv_mem t.2)⟩
    rw [hNT, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hnn : n = n' := Subtype.ext hmem.symm
    subst hnn
    have htt : (t : G) = t' := mul_left_cancel h1
    rw [Subtype.ext htt]
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hN2 : Nat.card N ≤ 2 := by
    by_contra h
    have : 3 * Nat.card T ≤ Nat.card N * Nat.card T := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hwC : w ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hconj : t * w * t⁻¹ ∈ N := GLAPPrimeCoreOf_conj_mem t (hTX ht) w hw
    have hne : (⟨t * w * t⁻¹, hconj⟩ : ↥N) ≠ 1 := by
      intro h
      apply hw1
      have h' : t * w * t⁻¹ = 1 := congrArg Subtype.val h
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [h']; group
    have hne' : (⟨w, hw⟩ : ↥N) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
    have heq := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.eq_of_ne_one_of_card_le_two hN2
      hne hne'
    have heq' : t * w * t⁻¹ = w := congrArg Subtype.val heq
    calc t * w = t * w * t⁻¹ * t := by group
      _ = w * t := by rw [heq']
  obtain ⟨k, hk⟩ := hCT ⟨w, hwC⟩
  have hwk : w ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (⟨w, hw⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hord3 : orderOf (⟨w, hw⟩ : ↥N) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hwk
  have h1 : orderOf (⟨w, hw⟩ : ↥N) = 1 := by
    have hc : Nat.Coprime (3 ^ k) (Nat.card N) := Nat.Coprime.pow_left k hcop
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord3 hc) hord
  rw [orderOf_eq_one_iff] at h1
  exact hw1 (congrArg Subtype.val h1)

variable {n : ℕ}

theorem anyLt_true {n : ℕ} {p : ℕ → Bool} (h : CFSG.Sporadic.Schreier.Co3.Native.anyLt n p = true) :
    ∃ i < n, p i = true := by
  unfold CFSG.Sporadic.Schreier.Co3.Native.anyLt at h
  rw [Nat.any_eq_finRange_any, List.any_eq_true] at h
  obtain ⟨⟨i, hi⟩, -, h⟩ := h
  exact ⟨i, hi, h⟩

theorem card_le_length_of_rep {X : Subgroup (Equiv.Perm (Fin n))} {ls : List (Array ℕ)}
    (h : ∀ c ∈ X, ∃ e ∈ ls, Rep n e c) : Nat.card X ≤ ls.length := by
  have h' : ∀ c : X, ∃ i : Fin ls.length, Rep n ls[i] c := by
    intro c
    obtain ⟨e, he, hre⟩ := h c c.2
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    exact ⟨⟨i, hi⟩, hre⟩
  choose f hf using h'
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    rw [hab] at h1
    exact Subtype.ext (h1.unique (hf b))
  calc Nat.card X ≤ Nat.card (Fin ls.length) := Nat.card_le_card_of_injective f hinj
    _ = ls.length := Nat.card_fin _

@[expose] def dsearch (n : ℕ) (L : Array Level) (base : Array ℕ)
    (rels : Array (Option (ℕ × Array ℕ))) (pred : Array ℕ → Bool) :
    ℕ → ℕ → Array ℕ → Array ℕ → List (Array ℕ)
  | 0, _, acc, _ => if pred acc then [acc] else []
  | fuel + 1, i, acc, accI =>
    match rels.getD i none with
    | some (j, y) =>
      if (L[i]!).pos[accI[y[acc[base[j]!]!]!]!]! < (L[i]!).pts.size then
        dsearch n L base rels pred fuel (i + 1)
          (compA n acc (L[i]!).tr[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]!)
          (compA n (L[i]!).trInv[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]! accI)
      else []
    | none =>
      (List.range (L[i]!).pts.size).flatMap fun k =>
        dsearch n L base rels pred fuel (i + 1) (compA n acc (L[i]!).tr[k]!)
          (compA n (L[i]!).trInv[k]! accI)

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem levT_pos_inv_mul_mem {i : ℕ} (hi : i < Q.baseCount) {h : Equiv.Perm (Fin n)}
    (hh : h ∈ Q.levelSubgroup i) :
    (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]! < (lev n S base i).pts.size ∧
      (levT n S base i (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]!)⁻¹ * h ∈
        Q.levelSubgroup (i + 1) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  have hx : h b ∈ Q.orbitPoints ⟨i, hi⟩ := by
    rw [Q.orbitPoints_eq_orbit]
    exact ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨hk, -, ht⟩ := hA.orbitPoints_spec hF hi hx
  obtain ⟨-, hmem, hval⟩ := Q.transversal_getD_spec ⟨i, hi⟩ (h b) hx
  rw [ht] at hmem hval
  refine ⟨hk, ?_⟩
  set t := levT n S base i (lev n S base i).pos[((h b : Fin n) : ℕ)]! with htdef
  rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩]
  refine Subgroup.mem_inf.2
    ⟨(Q.levelSubgroup i).mul_mem ((Q.levelSubgroup i).inv_mem hmem) hh, ?_⟩
  have htb : t b = h b := hval
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
  change t⁻¹ (h b) = b
  rw [← htb]
  simp

theorem dsearch_spec {rels : Array (Option (ℕ × Array ℕ))} {pred : Array ℕ → Bool}
    {c : Equiv.Perm (Fin n)}
    (hrel : ∀ l (hl : l < Q.baseCount) j y, rels.getD l none = some (j, y) →
      ∃ hj : j < l, ∃ Y : Equiv.Perm (Fin n), Rep n y Y ∧
        c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨j, by omega⟩)))
    (hpred : ∀ a, Rep n a c → pred a = true) :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc accI : Array ℕ) (A : Equiv.Perm (Fin n)),
      Rep n acc A → Rep n accI A⁻¹ → A⁻¹ * c ∈ Q.levelSubgroup i →
      ∃ e ∈ dsearch n (rawLevels n S base) base rels pred fuel i acc accI, Rep n e c := by
  have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
    fun m hm => hA.base_val ⟨m, hm⟩
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc accI A hacc _ hh
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one] at hh
    subst hh
    have hp := hpred acc hacc
    refine ⟨acc, ?_, hacc⟩
    simp [dsearch, hp]
  | succ fuel ih =>
    intro i hi acc accI A hacc haccI hh
    have hib : i < Q.baseCount := by omega
    set h := A⁻¹ * c with hhdef
    obtain ⟨hk, hk'⟩ := levT_pos_inv_mul_mem hA hF hQ hib hh
    set k := (lev n S base i).pos[((h (Q.base.get ⟨i, hib⟩) : Fin n) : ℕ)]! with hkdef
    have hrepT : Rep n ((rawLevels n S base)[i]!).tr[k]! (levT n S base i k) :=
      hA.rep_levT hF hib hk
    have hrepTI : Rep n ((rawLevels n S base)[i]!).trInv[k]! (levT n S base i k)⁻¹ :=
      hA.rep_levTInv hF hib hk
    have hacc' : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc hrepT
    have haccI' : Rep n (compA n ((rawLevels n S base)[i]!).trInv[k]! accI)
        (A * levT n S base i k)⁻¹ := by
      rw [mul_inv_rev]
      exact rep_compA hrepTI haccI
    have hh' : (A * levT n S base i k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) := by
      rw [mul_inv_rev, mul_assoc]
      exact hk'
    obtain ⟨e, he, hre⟩ := ih (i + 1) (by omega) _ _ _ hacc' haccI' hh'
    refine ⟨e, ?_, hre⟩
    cases hr : rels.getD i none with
    | none =>
      simp only [dsearch, hr, List.mem_flatMap, List.mem_range]
      exact ⟨k, hk, he⟩
    | some jy =>
      obtain ⟨j, y⟩ := jy
      obtain ⟨hj, Y, hY, hcY⟩ := hrel i hib j y hr
      have hfixj : h (Q.base.get ⟨j, by omega⟩) = Q.base.get ⟨j, by omega⟩ :=
        Q.levelSubgroup_fixes_base_index i h hh ⟨j, by omega⟩ hj
      have hcj : c (Q.base.get ⟨j, by omega⟩) = A (Q.base.get ⟨j, by omega⟩) := by
        have : c = A * h := by rw [hhdef]; group
        rw [this, Equiv.Perm.mul_apply, hfixj]
      have hq : accI[y[acc[base[j]!]!]!]! = ((h (Q.base.get ⟨i, hib⟩) : Fin n) : ℕ) := by
        rw [← hbase j (by omega), hacc, ← hcj, hY, ← hcY, haccI, hhdef, Equiv.Perm.mul_apply]
      have hpos : ((rawLevels n S base)[i]!).pos[accI[y[acc[base[j]!]!]!]!]! = k := by
        rw [hq]
        rfl
      simp only [dsearch, hr]
      rw [hpos, ite_eq_left (by exact hk)]
      exact he

theorem exists_mem_dsearch {rels : Array (Option (ℕ × Array ℕ))} {pred : Array ℕ → Bool}
    {c : Equiv.Perm (Fin n)} (hc : c ∈ Q.originalSubgroup)
    (hrel : ∀ l (hl : l < Q.baseCount) j y, rels.getD l none = some (j, y) →
      ∃ hj : j < l, ∃ Y : Equiv.Perm (Fin n), Rep n y Y ∧
        c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨j, by omega⟩)))
    (hpred : ∀ a, Rep n a c → pred a = true) :
    ∃ e ∈ dsearch n (rawLevels n S base) base rels pred base.size 0 (idA n) (idA n), Rep n e c := by
  rw [hA.base_size]
  refine dsearch_spec hA hF hQ hrel hpred Q.baseCount 0 (by omega) (idA n) (idA n) 1 rep_idA
    (by rw [inv_one]; exact rep_idA) ?_
  rw [inv_one, one_mul, Q.levelSubgroup_zero_eq_original hQ]
  exact hc

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

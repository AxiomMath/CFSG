module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22Tests
public import CFSG.Certificates.Kernel.Census.RootConjBitSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Sporadic.FischerOddCore.Fi22Unitary

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.KC.Census

theorem fi22InPT_iff (a : Array ℕ)
    (g : Equiv.Perm (Fin 3510)) (h : Rep 3510 a g) :
    fi22InPT a = true ↔ g ∈ fi22P :=
  fi22InP_iff h

theorem fi22InRT_iff
    (a : Array ℕ)
    (g : Equiv.Perm (Fin 3510)) (h : Rep 3510 a g) :
    fi22InRT a = true ↔ g ∈ fi22R := by
  rw [fi22InRT, Bool.or_eq_true, fi22InPT_iff a g h, fi22InPT_iff _ _ (rep_compA rep_fi22U h),
    mem_fi22R_iff]

theorem fi22AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Fi22) ↥fi22R (fi22P.subgroupOf fi22R) := by
  obtain ⟨-, -, -, -, ⟨e, he, -⟩, -⟩ := CTUC_Fi22_full_automorphism_permutation_model
  exact autModel_of_conj fi22P_le_R fi22PermEquiv.symm e he

theorem fi22P_normal :
    (fi22P.subgroupOf fi22R).Normal
    :=
  normal_of_index_eq_two index_fi22P_subgroupOf_R

theorem fi22P_index_le :
    (fi22P.subgroupOf fi22R).index ≤
    2 := by
  rw [index_fi22P_subgroupOf_R]

theorem factorization_two_pow_mul (k m : ℕ) (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)), add_zero]

theorem fixP_fi22ExtRep :
    ∀ k < 6, fixP (fi22ExtRep k) =
    [54, 182, 694, 72, 360, 64][k]! := by
  have h := CTUC_Fi22_all_extension_involutions_covered.2.2.2.1
  simp only [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, List.map_cons, List.map_nil,
    List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := h
  intro k hk
  rw [fixP, Fintype.card_subtype]
  interval_cases k
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem fi22_conj_of_fix
    (g : Equiv.Perm (Fin 3510))
    (hg : g ∈ fi22R) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) {k : ℕ} (hk : k < 6) (hgk : fixP g = fixP (fi22ExtRep k)) :
    ∃ w ∈ fi22R, w * g * w⁻¹ = fi22ExtRep k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k', hk', w, hw, hwg⟩ := fi22R_involution_conj hg (orderOf_eq_prime hg2 hg1)
  have hfk : fixP (fi22ExtRep k') = fixP (fi22ExtRep k) := by rw [← hgk, ← hwg, fixP_conj]
  rw [fixP_fi22ExtRep k' hk', fixP_fi22ExtRep k hk] at hfk
  have hkk : k' = k := by interval_cases k <;> interval_cases k' <;> first | rfl | simp at hfk
  exact ⟨w, hw, hkk ▸ hwg⟩

theorem fi22_conj_inner
    (g : Equiv.Perm (Fin 3510))
    (hg : g ∈ fi22P) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) : ∃ k < 3, ∃ w ∈ fi22R, w * g * w⁻¹ = fi22ExtRep k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, w, hw, hwg⟩ := fi22R_involution_conj (fi22P_le_R hg) (orderOf_eq_prime hg2 hg1)
  refine ⟨k, ?_, w, hw, hwg⟩
  by_contra hk3
  have hout := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).2
  rw [show 3 + (k - 3) = k by omega] at hout
  apply hout
  rw [← hwg]
  have hN := fi22P_normal.conj_mem ⟨g, fi22P_le_R hg⟩ (by rwa [mem_subgroupOf]) ⟨w, hw⟩
  rwa [mem_subgroupOf] at hN

theorem card_centralizer_P
    {k : ℕ} (hk : k < 3) :
    Nat.card ↥(fi22P ⊓ centralizer {fi22ExtRep k}) = [1769472, 53084160, 18393661440][k]! := by
  obtain ⟨h0, h1, -, -, -, hcard⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.cons.injEq] at hcard
  interval_cases k
  · rw [h0, hcard.1]; rfl
  · rw [h1, hcard.2.1]; rfl
  · rw [fi22ExtRep_two, ← AT_Fi22_involution_centralizer_class.2.2.1,
      AT_Fi22_involution_centralizer_class.2.2.2.2.1]
    rfl

theorem card_centralizer_R
    {k : ℕ} (hk : k < 3) {c : Equiv.Perm (Fin 3510)} (hc : c ∈ fi22R)
    (hcP : c ∉ fi22P) (hct : c * fi22ExtRep k = fi22ExtRep k * c) :
    Nat.card ↥(fi22R ⊓ centralizer {fi22ExtRep k}) = 2 * [1769472, 53084160, 18393661440][k]! := by
  rw [card_inf_centralizer_R hc hcP hct, card_centralizer_P hk]

theorem card_inf_centralizer_conj {G : Type*} [Group G] {P : Subgroup G} {v g : G}
    (hv : v ∈ normalizer (P : Set G)) :
    Nat.card ↥(P ⊓ centralizer {v * g * v⁻¹}) = Nat.card ↥(P ⊓ centralizer {g}) := by
  have hv' := mem_normalizer_iff.mp hv
  have he : P ⊓ centralizer {v * g * v⁻¹} =
      (P ⊓ centralizer {g}).map (MulAut.conj v).toMonoidHom := by
    ext y
    simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hy, hc⟩
      refine ⟨v⁻¹ * y * v, ⟨?_, ?_⟩, by group⟩
      · rw [hv']
        convert hy using 1
        group
      · calc v⁻¹ * y * v * g = v⁻¹ * (y * (v * g * v⁻¹)) * v := by group
          _ = v⁻¹ * (v * g * v⁻¹ * y) * v := by rw [hc]
          _ = g * (v⁻¹ * y * v) := by group
    · rintro ⟨z, ⟨hz, hc⟩, rfl⟩
      refine ⟨(hv' z).mp hz, ?_⟩
      calc v * z * v⁻¹ * (v * g * v⁻¹) = v * (z * g) * v⁻¹ := by group
        _ = v * (g * z) * v⁻¹ := by rw [hc]
        _ = v * g * v⁻¹ * (v * z * v⁻¹) := by group
  rw [he, card_map_of_injective (MulAut.conj v).injective]

theorem conj_trans {G : Type*} [Group G] {w v g x c : G} (hw : w * g * w⁻¹ = c)
    (hv : v * x * v⁻¹ = c) : v⁻¹ * w * g * (v⁻¹ * w)⁻¹ = x := by
  calc v⁻¹ * w * g * (v⁻¹ * w)⁻¹ = v⁻¹ * (w * g * w⁻¹) * v := by group
    _ = v⁻¹ * (v * x * v⁻¹) * v := by rw [hw, hv]
    _ = x := by group

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) {l : List α}
    {i : ℕ} (hi : i < l.length) : (l.map f)[i]! = f l[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos l i hi, List.getElem_map]

theorem getElem!_mem_of_lt {α : Type*} [Inhabited α] {l : List α} {i : ℕ} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_pos l i hi]
  exact List.getElem_mem hi

@[expose] noncomputable def fi22RootPerm (rs : List RootConjP) (i : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (unpackP 3510 12 rs[i]!.x)

theorem fi22_censuses
    {inX inW : ℕ → Bool} {ks : List ℕ} {rs : List RootConjP}
    (hsX : ∀ P, canon1 3510 12 P = true → pvalid 3510 12 P = true → inX P = true →
      permOfArr 3510 (unpackP 3510 12 P) ∈ fi22P)
    (hsW : ∀ P, canon1 3510 12 P = true → pvalid 3510 12 P = true → inW P = true →
      permOfArr 3510 (unpackP 3510 12 P) ∈ fi22R)
    (hc : rs.all (canonR 3510 12) = true)
    (hII : prootsConjOKB 3510 12 fi22PS inX inW false 2 ks rs = true)
    (h17 : prootsConjOKB 3510 12 fi22PS inX inW true 1 ks rs = true)
    (hf : rs.map (fun r => pfix 3510 12 r.x) = [694, 182, 54])
    (hlen : rs.map (fun r => r.xs.length) = [17, 18, 17]) :
    YCensus (fi22P.subgroupOf fi22R) (· ≤ fi22P.subgroupOf fi22R) ∧
      YCensus17 (fi22P.subgroupOf fi22R) (fun _ => False) := by
  have hl : rs.length = 3 := by simpa using congrArg List.length hf
  have hII' := hII
  unfold prootsConjOKB at hII'
  rw [Bool.and_eq_true] at hII'
  have hfi : ∀ i < 3, pfix 3510 12 rs[i]!.x = [694, 182, 54][i]! := fun i hi => by
    rw [← hf, getElem!_map_of_lt _ (hl ▸ hi)]
  have hli : ∀ i < 3, rs[i]!.xs.length = [17, 18, 17][i]! := fun i hi => by
    rw [← hlen, getElem!_map_of_lt _ (hl ▸ hi)]
  have hfact : ∀ i < 3, fi22RootPerm rs i ∈ fi22R ∧ fi22RootPerm rs i ^ 2 = 1 ∧
      fi22RootPerm rs i ≠ 1 ∧ fixP (fi22RootPerm rs i) = pfix 3510 12 rs[i]!.x ∧
      ∃ T : Subgroup (Equiv.Perm (Fin 3510)), T ≤ fi22R ⊓ centralizer {fi22RootPerm rs i} ∧
        Nat.card T = 2 ^ rs[i]!.xs.length ∧
        permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) ∈ T ∧
        (permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) ∈ fi22P → T ≤ fi22P) := by
    intro i hi
    have hr := List.all_eq_true.1 hII'.2 i (List.mem_range.2 (hl ▸ hi))
    have hci : canonR 3510 12 rs[i]! = true :=
      List.all_eq_true.1 hc _ (getElem!_mem_of_lt (hl ▸ hi))
    obtain ⟨h1, h2, h3, h4, T, hT, hTc, hkT, hX⟩ :=
      rootConjB_facts (by norm_num) (by norm_num) hsW hci hr
    exact ⟨h1, h2, h3, h4, T, hT, hTc, hkT, (hX fi22P fi22P_le_R fi22P_normal fi22PS_lt hsX).1⟩
  have hfx : ∀ i < 3, fixP (fi22RootPerm rs i) = fixP (fi22ExtRep (2 - i)) := fun i hi => by
    rw [(hfact i hi).2.2.2.1, hfi i hi, fixP_fi22ExtRep (2 - i) (by omega)]
    interval_cases i <;> rfl
  have hv : ∀ i < 3, ∃ v ∈ fi22R, v * fi22RootPerm rs i * v⁻¹ = fi22ExtRep (2 - i) :=
    fun i hi => fi22_conj_of_fix _ (hfact i hi).1 (hfact i hi).2.1 (hfact i hi).2.2.1
      (by omega) (hfx i hi)
  have hnorm : ∀ v ∈ fi22R, v ∈ normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
    fun v hv => fi22R_le_normalizer hv
  have hin : ∀ i < 3, fi22RootPerm rs i ∈ fi22P := fun i hi => by
    obtain ⟨v, hvR, hve⟩ := hv i hi
    have ht := CTUC_Fi22_all_extension_involutions_covered.1 (2 - i) (by omega)
    rw [← hve] at ht
    exact (mem_normalizer_iff.mp (hnorm v hvR) (fi22RootPerm rs i)).mpr ht
  have hout : ∀ i < 3, permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) ∉ fi22P := by
    intro i hi hm
    obtain ⟨-, -, -, -, T, hT, hTc, -, hX⟩ := hfact i hi
    have hTP : T ≤ fi22P ⊓ centralizer {fi22RootPerm rs i} := fun t ht => ⟨hX hm ht, (hT ht).2⟩
    obtain ⟨v, hvR, hve⟩ := hv i hi
    have hd := card_dvd_of_le hTP
    rw [hTc, ← card_inf_centralizer_conj (hnorm v hvR), hve, card_centralizer_P (by omega),
      hli i hi] at hd
    interval_cases i <;> revert hd <;> decide
  have hsyl : ∀ i < rs.length, rs[i]!.xs.length =
      (Nat.card ↥(fi22R ⊓ centralizer {permOfArr 3510 (unpackP 3510 12 rs[i]!.x)})).factorization
        2 := by
    intro i hi
    rw [hl] at hi
    change rs[i]!.xs.length = (Nat.card ↥(fi22R ⊓ centralizer {fi22RootPerm rs i})).factorization 2
    obtain ⟨-, -, -, -, T, hT, -, hkT, -⟩ := hfact i hi
    obtain ⟨v, hvR, hve⟩ := hv i hi
    have hcR : v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹ ∈ fi22R :=
      fi22R.mul_mem (fi22R.mul_mem hvR (hT hkT).1) (fi22R.inv_mem hvR)
    have hcP : v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹ ∉ fi22P := fun h =>
      hout i hi ((mem_normalizer_iff.mp (hnorm v hvR) _).mpr h)
    have hcx := mem_centralizer_singleton_iff.mp (hT hkT).2
    have hct : v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹ * fi22ExtRep (2 - i) =
        fi22ExtRep (2 - i) * (v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹) := by
      rw [← hve]
      calc v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹ *
            (v * fi22RootPerm rs i * v⁻¹) =
            v * (permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * fi22RootPerm rs i) * v⁻¹ :=
              by group
        _ = v * (fi22RootPerm rs i * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!)) * v⁻¹ :=
              by rw [hcx]
        _ = v * fi22RootPerm rs i * v⁻¹ *
            (v * permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) * v⁻¹) := by group
    rw [← card_inf_centralizer_conj (le_normalizer hvR), hve,
      card_centralizer_R (by omega) hcR hcP hct, hli i hi]
    interval_cases i
    · have h2 : 2 * [1769472, 53084160, 18393661440][2 - 0]! = 2 ^ 17 * 280665 := by decide
      rw [h2, factorization_two_pow_mul 17 280665 (by decide)]
      rfl
    · have h2 : 2 * [1769472, 53084160, 18393661440][2 - 1]! = 2 ^ 18 * 405 := by decide
      rw [h2, factorization_two_pow_mul 18 405 (by decide)]
      rfl
    · have h2 : 2 * [1769472, 53084160, 18393661440][2 - 2]! = 2 ^ 17 * 27 := by decide
      rw [h2, factorization_two_pow_mul 17 27 (by decide)]
      rfl
  have hfix : ∀ g ∈ fi22R, g ^ 2 = 1 → g ≠ 1 → ∀ j < rs.length,
      fixP g = fixP (permOfArr 3510 (unpackP 3510 12 rs[j]!.x)) →
        ∃ v ∈ fi22R, v * g * v⁻¹ = permOfArr 3510 (unpackP 3510 12 rs[j]!.x) := by
    intro g hg hg2 hg1 j hj hgj
    rw [hl] at hj
    change fixP g = fixP (fi22RootPerm rs j) at hgj
    change ∃ v ∈ fi22R, v * g * v⁻¹ = fi22RootPerm rs j
    obtain ⟨u, huR, hu⟩ :=
      fi22_conj_of_fix g hg hg2 hg1 (k := 2 - j) (by omega) (hgj.trans (hfx j hj))
    obtain ⟨v, hvR, hve⟩ := hv j hj
    exact ⟨v⁻¹ * u, fi22R.mul_mem (fi22R.inv_mem hvR) huR, conj_trans hu hve⟩
  have hcls : ∀ a ∈ fi22P, a ^ 2 = 1 → a ≠ 1 →
      ∃ i < rs.length, ∃ g ∈ fi22R, g * a * g⁻¹ = permOfArr 3510 (unpackP 3510 12 rs[i]!.x) := by
    intro a ha ha2 ha1
    obtain ⟨k, hk, u, huR, hu⟩ := fi22_conj_inner a ha ha2 ha1
    obtain ⟨v, hvR, hve⟩ := hv (2 - k) (by omega)
    have h2k : 2 - (2 - k) = k := by omega
    rw [h2k] at hve
    exact ⟨2 - k, by omega, v⁻¹ * u, fi22R.mul_mem (fi22R.inv_mem hvR) huR, conj_trans hu hve⟩
  have hout' : ∀ i < rs.length, permOfArr 3510 (unpackP 3510 12 rs[i]!.xs[ks[i]!]!) ∉ fi22P :=
    fun i hi => hout i (hl ▸ hi)
  have hin' : ∀ i < rs.length, permOfArr 3510 (unpackP 3510 12 rs[i]!.x) ∈ fi22P :=
    fun i hi => hin i (hl ▸ hi)
  have hY := yCensusII_of_rootConjChecksB (by norm_num) (by norm_num) fi22P_le_R fi22P_normal
    fi22P_index_le fi22PS_lt hsX hsW hc hII hsyl hfix hout' hin' hcls
  exact ⟨hY, yCensus17_of_rootConjChecksB (by norm_num) (by norm_num) fi22P_le_R fi22P_normal
    fi22P_index_le fi22PS_lt hsX hsW hc h17 hsyl hfix hout' hY hcls⟩

theorem sporadicCaseOdd_Fi22_of_check
    {inX inW : ℕ → Bool}
    {ks : List ℕ} {rs : List RootConjP}
    (hsX : ∀ P, canon1 3510 12 P = true → pvalid 3510 12 P = true → inX P = true →
      permOfArr 3510 (unpackP 3510 12 P) ∈ fi22P)
    (hsW : ∀ P, canon1 3510 12 P = true → pvalid 3510 12 P = true → inW P = true →
      permOfArr 3510 (unpackP 3510 12 P) ∈ fi22R)
    (hc : rs.all (canonR 3510 12) = true)
    (hII : prootsConjOKB 3510 12 fi22PS inX inW false 2 ks rs = true)
    (h17 : prootsConjOKB 3510 12 fi22PS inX inW true 1 ks rs = true)
    (hf : rs.map (fun r => pfix 3510 12 r.x) = [694, 182, 54])
    (hlen : rs.map (fun r => r.xs.length) = [17, 18, 17])
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .Fi22 := by
  obtain ⟨hY, hY17⟩ := fi22_censuses hsX hsW hc hII h17 hf hlen
  exact sporadicCaseOdd_of_yCensus17 h32 h33 fi22AutModel
    (commutator_le_of_index_two index_fi22P_subgroupOf_R) hY hY17

end CFSG.ComponentClassification.RankTwoSporadic.Fi22

module

public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.Permutation.SymmetricCoxeter
public import Certificates.Certificate26965

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Permutation.SymmetricCoxeter
open scoped Pointwise

theorem centralizer_inf_equiv_of_conj {M : Type*} [Group M] (R : Subgroup M) {g x y : M}
    (hg : g ∈ R) (h : g * x * g⁻¹ = y) :
    Nonempty (↥(centralizer ({x} : Set M) ⊓ R) ≃* ↥(centralizer ({y} : Set M) ⊓ R)) := by
  subst h
  have hc : ∀ c : M, c ∈ centralizer ({x} : Set M) ↔
      g * c * g⁻¹ ∈ centralizer ({g * x * g⁻¹} : Set M) := by
    intro c
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
        _ = g * (x * c) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
    · intro h
      have h' : g * (c * x) * g⁻¹ = g * (x * c) * g⁻¹ := by
        calc g * (c * x) * g⁻¹ = g * c * g⁻¹ * (g * x * g⁻¹) := by group
          _ = g * x * g⁻¹ * (g * c * g⁻¹) := h
          _ = g * (x * c) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
  have hR : ∀ c : M, c ∈ R ↔ g * c * g⁻¹ ∈ R := by
    intro c
    constructor
    · intro h
      exact R.mul_mem (R.mul_mem hg h) (R.inv_mem hg)
    · intro h
      have := R.mul_mem (R.mul_mem (R.inv_mem hg) h) hg
      simpa [mul_assoc] using this
  exact ⟨{ toFun := fun c => ⟨g * c.1 * g⁻¹, mem_inf.2
                ⟨(hc c.1).1 (mem_inf.1 c.2).1, (hR c.1).1 (mem_inf.1 c.2).2⟩⟩
           invFun := fun c => ⟨g⁻¹ * c.1 * g, mem_inf.2
                ⟨(hc _).2 (by simpa [mul_assoc] using (mem_inf.1 c.2).1),
                  (hR _).2 (by simpa [mul_assoc] using (mem_inf.1 c.2).2)⟩⟩
           left_inv := fun c => Subtype.ext (by simp [mul_assoc])
           right_inv := fun c => Subtype.ext (by simp [mul_assoc])
           map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }⟩

theorem centralizer_inf_eq_of_zpowers_eq {M : Type*} [Group M] (R : Subgroup M) {x y : M}
    (h : zpowers x = zpowers y) :
    centralizer ({x} : Set M) ⊓ R = centralizer ({y} : Set M) ⊓ R := by
  have key : ∀ {a b : M}, zpowers a ≤ zpowers b → centralizer ({b} : Set M) ≤
      centralizer ({a} : Set M) := by
    intro a b hab c hc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hab (mem_zpowers a))
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← hk]
    exact ((Commute.zpow_right (show Commute c b from hc) k).eq)
  exact le_antisymm (inf_le_inf_right _ (key h.ge)) (inf_le_inf_right _ (key h.le))

noncomputable def powFiveHom {M : Type*} [Group M] (x : M) (hx : x ^ 5 = 1) :
    Multiplicative (ZMod 5) →* M where
  toFun a := x ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have hmod : x ^ ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) =
        x ^ (((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % 5) := by
      conv_lhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val +
        (Multiplicative.toAdd b).val) 5, pow_add, pow_mul, hx, one_pow, mul_one]
    show x ^ (Multiplicative.toAdd (a * b)).val = _
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← hmod]

theorem s5c_spec :
    Nonempty (↥(centralizer ({hs100FiveLine 2} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) ≃*
      Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  classical
  have h : s5cOK = true := Certificates.certificate26965
  simp only [s5cOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨henum, hsize⟩, hlist⟩, hcox⟩ := h
  have hps := hs100FiveKeys_lt
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  obtain ⟨hC2eq, hC2card⟩ := hs100FiveC2_spec
  set x₂ : Equiv.Perm (Fin 100) := hs100FiveLine 2 with hx₂
  set xs : ℕ → Equiv.Perm (Fin 100) := fun i => permOfArr 100 s5cS[i]! with hxs
  have hxsv : ∀ i < 4, validA 100 s5cS[i]! = true ∧
      hs100FiveC2Cert.pts.toList.any (eqA 100 s5cS[i]!) = true := by
    intro i hi
    have := allLt_spec hlist hi
    simp only [Bool.and_eq_true] at this
    exact this
  have hrx : ∀ i < 4, Rep 100 s5cS[i]! (xs i) := fun i hi => rep_of_validA (hxsv i hi).1
  have hxC : ∀ i < 4, xs i ∈ hs100FiveC2 := fun i hi =>
    enumOK_mem_of_any hps hs100FiveC2_enum (rep_of_validA (hxsv i hi).1) (hxsv i hi).2
  have hline : x₂ ∈ hs100FiveQ := linesOK_mem hps hs100Five_lines_ok 2
  have hxR : x₂ ∈ hs100R := hs100P_le_R (hs100FiveQ_le_P hline)
  have hx₂C : x₂ ∈ hs100FiveC2 := by
    rw [hC2eq]
    exact ⟨mem_centralizer_singleton_iff.2 rfl, hxR⟩
  have hcoxeter : IsCoxeterA 4 xs := by
    simp only [s5cCoxeterOK, Bool.and_eq_true] at hcox
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcox
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · exact (eqA_iff (rep_compA (hrx i hi) (hrx i hi)) rep_idA).1 (allLt_spec hc1 hi)
    · have hi3 : i < 3 := by omega
      exact (eqA_iff (rep_compA (rep_compA (hrx i (by omega)) (hrx (i + 1) hi)) (hrx i (by omega)))
        (rep_compA (rep_compA (hrx (i + 1) hi) (hrx i (by omega))) (hrx (i + 1) hi))).1
        (allLt_spec hc2 hi3)
    · have h1 := allLt_spec (allLt_spec hc3 (by omega : i < 4)) hj
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h1 | h1
      · omega
      · exact (eqA_iff (rep_compA (hrx i (by omega)) (hrx j hj))
          (rep_compA (hrx j hj) (hrx i (by omega)))).1 h1
  have hx₂' : x₂ = permOfArr 100 s5cGens[0]! := by
    have e : s5cGens[0]! = hs100FiveLines[2]! := by simp [s5cGens]
    rw [e, hx₂]
    unfold hs100FiveLine
    rfl
  have hgen : ∀ g ∈ permsA 100 s5cGens, g = x₂ ∨ ∃ i < 4, g = xs i := by
    rintro _ ⟨k, hk, rfl⟩
    have hk5 : k < 5 := hk
    interval_cases k
    · exact Or.inl hx₂'.symm
    · refine Or.inr ⟨0, by norm_num, ?_⟩
      have e : s5cGens[1]! = s5cS[0]! := by simp [s5cGens, s5cS]
      simp only [hxs, e]
    · refine Or.inr ⟨1, by norm_num, ?_⟩
      have e : s5cGens[2]! = s5cS[1]! := by simp [s5cGens, s5cS]
      simp only [hxs, e]
    · refine Or.inr ⟨2, by norm_num, ?_⟩
      have e : s5cGens[3]! = s5cS[2]! := by simp [s5cGens, s5cS]
      simp only [hxs, e]
    · refine Or.inr ⟨3, by norm_num, ?_⟩
      have e : s5cGens[4]! = s5cS[3]! := by simp [s5cGens, s5cS]
      simp only [hxs, e]
  have hG₁le : Subgroup.closure (permsA 100 s5cGens) ≤ hs100FiveC2 := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hgen g hg with rfl | ⟨i, hi, rfl⟩
    · exact hx₂C
    · exact hxC i hi
  have hG₁card : Nat.card (Subgroup.closure (permsA 100 s5cGens)) = 600 := hcard.trans hsize
  have hG₁eq : Subgroup.closure (permsA 100 s5cGens) = hs100FiveC2 :=
    Subgroup.eq_of_le_of_card_ge hG₁le (by rw [hG₁card, hC2card])
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 4 xs hcoxeter
  have hcomm_gen : ∀ i < 4, xs i * x₂ = x₂ * xs i := by
    intro i hi
    have hmem' := hxC i hi
    rw [hC2eq] at hmem'
    exact mem_centralizer_singleton_iff.1 hmem'.1
  have hcomm : ∀ σ : Equiv.Perm (Fin 5), ψ σ * x₂ = x₂ * ψ σ := by
    intro σ
    have : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤
        (centralizer ({x₂} : Set (Equiv.Perm (Fin 100)))).comap ψ := by
      rw [← closure_adjSwap 4, Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hψ i hi]
      exact mem_centralizer_singleton_iff.2 (hcomm_gen i hi)
    exact mem_centralizer_singleton_iff.1 (this (mem_top σ))
  have hψC : ∀ σ : Equiv.Perm (Fin 5), ψ σ ∈ hs100FiveC2 := by
    intro σ
    have : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ hs100FiveC2.comap ψ := by
      rw [← closure_adjSwap 4, Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hψ i hi]
      exact hxC i hi
    exact this (mem_top σ)
  have hx5 : x₂ ^ 5 = 1 := linesOK_pow_line hs100Five_lines_ok 2
  let Φ : Multiplicative (ZMod 5) × Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 100) :=
    MonoidHom.noncommCoprod (powFiveHom x₂ hx5) ψ
      (fun a σ => Commute.pow_left (show Commute x₂ (ψ σ) from (hcomm σ).symm) _)
  have hΦ : ∀ a σ, Φ (a, σ) = x₂ ^ (Multiplicative.toAdd a).val * ψ σ := fun a σ => rfl
  have hΦC : ∀ q, Φ q ∈ hs100FiveC2 := by
    rintro ⟨a, σ⟩
    rw [hΦ]
    exact hs100FiveC2.mul_mem (pow_mem hx₂C _) (hψC σ)
  let Φ' : Multiplicative (ZMod 5) × Equiv.Perm (Fin 5) →* ↥hs100FiveC2 :=
    Φ.codRestrict hs100FiveC2 hΦC
  have hsurj : Function.Surjective Φ' := by
    have hle : hs100FiveC2 ≤ Φ.range := by
      rw [← hG₁eq, Subgroup.closure_le]
      intro g hg
      rcases hgen g hg with rfl | ⟨i, hi, rfl⟩
      ·
        refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
        have h1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 5))).val = 1 := by
          have : Fact (1 < 5) := ⟨by norm_num⟩
          exact ZMod.val_one 5
        rw [hΦ, MonoidHom.map_one ψ, mul_one, h1, pow_one]
      · exact ⟨(1, adjSwap 4 i), by rw [hΦ, hψ i hi]; simp⟩
    rintro ⟨y, hy⟩
    obtain ⟨q, hq⟩ := hle hy
    exact ⟨q, Subtype.ext hq⟩
  have hcardD : Nat.card (Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) = 600 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm,
      Fintype.card_fin]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    norm_num
  have hbij : Function.Bijective Φ' :=
    hsurj.bijective_of_nat_card_le (by rw [hcardD, hC2card])
  exact ⟨(MulEquiv.subgroupCongr hC2eq).symm.trans (MulEquiv.ofBijective Φ' hbij).symm⟩

theorem exists_conj_mem_hs100FiveQ
    {x : Equiv.Perm (Fin 100)} (hxP : x ∈ hs100P) (hx : orderOf x = 5) :
    ∃ g ∈ hs100P, g * x * g⁻¹ ∈ hs100FiveQ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := hs100FiveQ_sylow
  let x' : ↥hs100P := ⟨x, hxP⟩
  have hx'ord : orderOf x' = 5 := by
    rw [← hx]
    exact Subgroup.orderOf_mk x hxP
  have hpg : IsPGroup 5 (zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx'ord]
    norm_num
  obtain ⟨S', hS'⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥hs100P S' S
  refine ⟨g, g.2, ?_⟩
  have hmem : ∀ y : ↥hs100P,
      y ∈ (S : Subgroup ↥hs100P) ↔ g⁻¹ * y * g ∈ (S' : Subgroup ↥hs100P) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc]
  have h1 : g * x' * g⁻¹ ∈ (S : Subgroup ↥hs100P) := by
    rw [hmem]
    simpa [mul_assoc] using hS' (mem_zpowers x')
  rw [hS, mem_subgroupOf] at h1
  have e : ((g * x' * g⁻¹ : ↥hs100P) : Equiv.Perm (Fin 100)) = (g : Equiv.Perm (Fin 100)) * x *
      (g : Equiv.Perm (Fin 100))⁻¹ := by
    simp [x']
  rw [e] at h1
  exact h1

theorem hs100_five_centralizer
    {x : Equiv.Perm (Fin 100)} (hxR : x ∈ hs100R)
    (hx : orderOf x = 5)
    (h3 : 3 ∣ Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R)) :
    Nonempty (↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) ≃*
      Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  classical
  obtain ⟨-, ⟨hlines, -⟩, htrans, hrecmem, -, hC0, hC2, hC23, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  have hxP : x ∈ hs100P := by
    have hidx : (hs100P.subgroupOf hs100R).index = 2 := by
      have h1 := Subgroup.card_mul_index (hs100P.subgroupOf hs100R)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs100P_le_R).toEquiv, card_hs100P,
        card_hs100R] at h1
      omega
    have hn : (hs100P.subgroupOf hs100R).Normal := hs100P_normal_R
    have h2 := Subgroup.pow_index_mem (hs100P.subgroupOf hs100R) (⟨x, hxR⟩ : ↥hs100R)
    rw [hidx, mem_subgroupOf] at h2
    have h6 : x = (x ^ 2) ^ 3 := by
      rw [← pow_mul]
      calc x = x ^ 5 * x := by rw [← hx, pow_orderOf_eq_one, one_mul]
        _ = x ^ 6 := by rw [← pow_succ]
    rw [h6]
    exact pow_mem h2 3
  obtain ⟨g, hgP, hgx⟩ := exists_conj_mem_hs100FiveQ hxP hx
  have hgR : g ∈ hs100R := hs100P_le_R hgP
  set y : Equiv.Perm (Fin 100) := g * x * g⁻¹ with hy
  have hyord : orderOf y = 5 := by
    rw [hy, ← hx]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  have hzin : zpowers y ∈ {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧
      Nat.card H = 5} :=
    ⟨(zpowers_le.2 hgx), by rw [Nat.card_zpowers, hyord]⟩
  rw [hlines] at hzin
  obtain ⟨j, hj⟩ := hzin
  obtain ⟨e1⟩ := centralizer_inf_equiv_of_conj hs100R hgR (rfl : g * x * g⁻¹ = y)
  have e2 := centralizer_inf_eq_of_zpowers_eq hs100R hj.symm
  obtain ⟨hRj, hconj⟩ := htrans j
  obtain ⟨e3⟩ := centralizer_inf_equiv_of_conj hs100R hRj hconj
  have hcard : Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) =
      Nat.card ↥(centralizer ({hs100FiveLine (hs100FiveRecordOf j)} : Set (Equiv.Perm (Fin 100))) ⊓
        hs100R) := by
    rw [Nat.card_congr e1.toEquiv]
    have : Nat.card ↥(centralizer ({y} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) =
        Nat.card ↥(centralizer ({hs100FiveLine j} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) := by
      rw [← e2]
    rw [this]
    exact (Nat.card_congr e3.toEquiv).symm
  have c0 : Nat.card ↥(centralizer ({hs100FiveLine 0} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) =
      50 := by
    rw [← hC0.1]
    exact hC0.2
  have c23 : Nat.card ↥(centralizer ({hs100FiveLine 23} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100R) = 1000 := by
    rw [← hC23.1]
    exact hC23.2
  have hrec : hs100FiveRecordOf j = 2 := by
    have hm := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exfalso
      have h0 : hs100FiveRecordOf j = 0 := Fin.ext hm
      rw [hcard, h0, c0] at h3
      omega
    · exact Fin.ext hm
    · exfalso
      have h0 : hs100FiveRecordOf j = 23 := Fin.ext hm
      rw [hcard, h0, c23] at h3
      omega
  rw [hrec] at hconj
  obtain ⟨e3'⟩ := centralizer_inf_equiv_of_conj hs100R hRj hconj
  obtain ⟨e4⟩ := s5c_spec
  have e2' : ↥(centralizer ({y} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) ≃*
      ↥(centralizer ({hs100FiveLine j} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) :=
    MulEquiv.subgroupCongr e2
  exact ⟨e1.trans (e2'.trans (e3'.symm.trans e4))⟩

end CFSG.EvenSporadicStandard.HSStd




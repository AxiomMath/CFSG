module

public import CFSG.LocalAnalysis.GH72.Sec4M0

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement

namespace G4b

section Generic

variable {G : Type*} [Group G]

theorem mem_of_mem_sup_of_odd {L N : Subgroup G} (hN : Odd (Nat.card N))
    (hNL : N ≤ normalizer (L : Set G)) {r : G} (hr : r ∈ L ⊔ N) {k : ℕ} (hk : r ^ 2 ^ k = 1) :
    r ∈ L := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left L N hNL] at hr
  obtain ⟨l, hl, o, ho, hlo⟩ := Set.mem_mul.1 hr
  rw [← hlo] at hk ⊢
  have key : ∀ j : ℕ, (l * o) ^ j * (o ^ j)⁻¹ ∈ L := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (l * o) ^ (j + 1) * (o ^ (j + 1))⁻¹ =
          ((l * o) ^ j * (o ^ j)⁻¹) * (o ^ j * l * (o ^ j)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact mul_mem ih ((mem_normalizer_iff.1 (pow_mem (hNL ho) j) l).1 hl)
  have hm : Odd (orderOf o) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N ho)
  have hlo : (l * o) ^ orderOf o ∈ L := by
    simpa [pow_orderOf_eq_one] using key (orderOf o)
  have hcop : Nat.Coprime (orderOf o) (orderOf (l * o)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hm)))
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hs]
  exact pow_mem hlo s

end Generic

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem k₀_facts {D M K Q : Subgroup G} (hD₀M : ⁅O2 M, O2 M⁆ ⊔ O M = ⁅O2 D, O2 D⁆ ⊔ O M)
    (hDK : D ≤ K) (hDM : D ≤ M) (hODM : D ⊓ O M ≤ O D) (hODM' : O D ≤ O M) (hODK : O D ≤ O K)
    (hOMK : O M ⊓ K ≤ O K) (hKn : K ≤ normalizer ((⁅O2 D, O2 D⁆ ⊔ O K : Subgroup G) : Set G))
    (hcard : ∀ R ≤ ⁅O2 D, O2 D⁆ ⊔ O K, IsPGroup 2 R → Nat.card R ≤ Nat.card Q)
    (hQ : Q ≤ ⁅O2 D, O2 D⁆ ⊔ O D) (hQ2 : IsPGroup 2 Q) :
    (K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K ≤ K ∧
      (((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K).subgroupOf K).Normal ∧
      ABGLocalTools.IsSylowOf 2 Q ((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K) ∧
      QuotIso ((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K) (O K) (⁅O2 M, O2 M⁆ ⊔ O M) (O M) := by
  have hD₀D : ⁅O2 D, O2 D⁆ ≤ D :=
    (commutator_mono (twoResidualOf_le_self D) (twoResidualOf_le_self D)).trans
      (commutator_le_self D)
  have hD₀K : ⁅O2 D, O2 D⁆ ≤ K := hD₀D.trans hDK
  have hD₀N : ⁅O2 D, O2 D⁆ ≤ normalizer (O M : Set G) := (hD₀D.trans hDM).trans (le_normalizer_O M)
  have hK₀ : (K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K = ⁅O2 D, O2 D⁆ ⊔ O K := by
    rw [hD₀M, inf_comm, sup_inf_eq_of_le hD₀K hD₀N, sup_assoc, sup_eq_right.2 hOMK]
  have hKO : K ≤ normalizer (O K : Set G) := le_normalizer_O K
  have hDOK : D ⊓ O K ≤ O D :=
    le_O_of_odd inf_le_left (fun d hd => mem_normalizer_inf (le_normalizer hd) (hKO (hDK hd)))
      (odd_card_of_le inf_le_right (card_O_odd K))
  have hN : ⁅O2 D, O2 D⁆ ⊓ O K = ⁅O2 D, O2 D⁆ ⊓ O M := by
    apply le_antisymm
    · exact le_inf inf_le_left ((le_inf (inf_le_left.trans hD₀D) inf_le_right).trans
        (hDOK.trans hODM'))
    · exact le_inf inf_le_left ((le_inf (inf_le_left.trans hD₀D) inf_le_right).trans
        (hODM.trans hODK))
  rw [hK₀]
  refine ⟨sup_le hD₀K (O_le_self K), (normal_subgroupOf_iff_le_normalizer
    (sup_le hD₀K (O_le_self K))).2 hKn,
    isSylowOf_of_forall_card_le (hQ.trans (sup_le_sup_left hODK _)) hQ2 hcard, ?_⟩
  have hD₀M₀ : ⁅O2 D, O2 D⁆ ≤ ⁅O2 M, O2 M⁆ ⊔ O M := by
    rw [hD₀M]
    exact le_sup_left
  exact quotIso_of_sup (E := ⁅O2 D, O2 D⁆) le_sup_left ((sup_le hD₀K (O_le_self K)).trans hKO)
    rfl hD₀M₀ ((core_le M).trans (le_normalizer_O M)) hD₀M.symm hN

end Assembly

section Side

variable {G : Type} [Group G] [Finite G] {z : G} {P Q : Subgroup G} {H₁ : Subgroup (Bar (C z))}

theorem exists_involution {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    ∃ t ∈ T, t ≠ 1 ∧ t * t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).1 h) hT
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  refine ⟨t, t.2, fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  · rw [← pow_two, ← ht']
    exact pow_orderOf_eq_one _

theorem centralizer_facts (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆)
    (htrans : ∀ t ∈ P, t ≠ 1 → t * t = 1 → ∃ (n : G) (V' : Subgroup G),
      n * z * n⁻¹ = t ∧ V' ≤ P ∧ z ∈ V' ∧ n ∈ normalizer (V' : Set G))
    {T : Subgroup G} (hTP : T ≤ P) (hT : T ≠ ⊥) :
    ⁅O2 (centralizer (T : Set G)), O2 (centralizer (T : Set G))⁆ ⊔ O (centralizer (T : Set G)) =
      ⁅O2 (centralizer (P : Set G)), O2 (centralizer (P : Set G))⁆ ⊔ O (centralizer (T : Set G)) ∧
    (∀ R ≤ centralizer (T : Set G), Odd (Nat.card R) →
      centralizer (P : Set G) ≤ normalizer (R : Set G) → R ≤ O (centralizer (T : Set G))) ∧
    (∀ R ≤ ⁅O2 (centralizer (T : Set G)), O2 (centralizer (T : Set G))⁆ ⊔
        O (centralizer (T : Set G)), IsPGroup 2 R → Nat.card R ≤ Nat.card Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hgen : O2 H₁ = H₁ := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  have hPz : P ≤ C z := le_sup_left.trans hS.le
  have hCp : H₁ ≤ bar (C z) (centralizer (P : Set G)) := le_bar_centralizer hP hPz h₃
  obtain ⟨t, htT, ht1, ht2⟩ := exists_involution (hP.to_le hTP) hT
  obtain ⟨n, V', hnt, hV'P, hzV', hnV'⟩ := htrans t (hTP htT) ht1 ht2
  have hW'z : centralizer (V' : Set G) ≤ C z := centralizer_le (Set.singleton_subset_iff.2 hzV')
  have hDW' : centralizer (P : Set G) ≤ centralizer (V' : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hV'P)
  have hW'n : (centralizer (V' : Set G)).map (MulAut.conj n⁻¹).toMonoidHom =
      centralizer (V' : Set G) :=
    mem_normalizer_iff_map_conj_eq'.1 (mem_normalizer_centralizer (inv_mem hnV'))
  set D' : Subgroup G := (centralizer (P : Set G)).map (MulAut.conj n⁻¹).toMonoidHom with hD'
  have hD'W' : D' ≤ centralizer (V' : Set G) := by
    rw [hD', ← hW'n]
    exact map_mono hDW'
  have hD'z : D' ≤ C z := hD'W'.trans hW'z
  have hO2W' : O2 (centralizer (V' : Set G)) = O2 D' ⊔ O (centralizer (V' : Set G)) := by
    have h := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom)
      (O2_eq_sup hP h₁ h₂ h₃ hgen hDW' hW'z hCp)
    rwa [map_O2, Subgroup.map_sup, map_O2, map_O, hW'n] at h
  have hHW' : H₁ ≤ bar (C z) (centralizer (V' : Set G)) := hCp.trans (bar_mono hDW')
  have hD'cov : H₁ ≤ bar (C z) D' := by
    have hbar := bar_O2_eq hP h₁ h₂ h₃ hgen hW'z hHW'
    have hO : bar (C z) (O (centralizer (V' : Set G))) = ⊥ := by
      rw [O_eq_inf hP h₁ h₂ h₃ hW'z hHW']
      exact eq_bot_iff.2 ((bar_mono inf_le_right).trans (bar_O (C z)).le)
    rw [hO2W', bar_sup ((twoResidualOf_le_self D').trans hD'z)
      ((O_le_self _).trans hW'z), hO, sup_bot_eq] at hbar
    rw [← hbar]
    exact bar_mono (twoResidualOf_le_self D')
  set K' : Subgroup G := (centralizer (T : Set G)).map (MulAut.conj n⁻¹).toMonoidHom with hK'
  have hK'z : K' ≤ C z := by
    rw [hK', map_centralizer]
    refine centralizer_le (Set.singleton_subset_iff.2 (mem_map_conj.2 ?_))
    rw [inv_inv, hnt]
    exact htT
  have hD'K' : D' ≤ K' := map_mono (centralizer_le (SetLike.coe_subset_coe.2 hTP))
  have hHK' : H₁ ≤ bar (C z) K' := hD'cov.trans (bar_mono hD'K')
  have hback : ∀ L : Subgroup G,
      (L.map (MulAut.conj n⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom = L := fun L => by
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  have hKK' : K'.map (MulAut.conj n).toMonoidHom = centralizer (T : Set G) := hback _
  have hDD' : D'.map (MulAut.conj n).toMonoidHom = centralizer (P : Set G) := hback _
  refine ⟨?_, fun R hRK hR hDR => ?_, fun R hRK hR2 => ?_⟩
  ·
    have h := congrArg (Subgroup.map (MulAut.conj n).toMonoidHom)
      (core_eq hP h₁ h₂ h₃ hgen hD'K' hK'z hD'cov)
    simp only [Subgroup.map_sup, map_commutator, map_O2, map_O, hKK', hDD'] at h
    exact h
  ·
    set R' : Subgroup G := R.map (MulAut.conj n⁻¹).toMonoidHom with hR'
    have hR'K' : R' ≤ K' := map_mono hRK
    have hR'odd : Odd (Nat.card R') := by
      rw [hR', card_map_of_injective (MulAut.conj n⁻¹).injective]
      exact hR
    have hD'R' : D' ≤ normalizer (R' : Set G) := by
      rw [hR', ← map_equiv_normalizer_eq]
      exact map_mono hDR
    have h1 : R' ≤ O K' := by
      rw [O_eq_inf hP h₁ h₂ h₃ hK'z hHK']
      exact le_inf hR'K' (le_O_C_of_odd hP h₁ h₂ h₃ hD'cov (hR'K'.trans hK'z) hR'odd hD'R')
    have h2 := map_mono (f := (MulAut.conj n).toMonoidHom) h1
    rwa [hR', hback, map_O, hKK'] at h2
  ·
    set R' : Subgroup G := R.map (MulAut.conj n⁻¹).toMonoidHom with hR'
    have hcore : (⁅O2 (centralizer (T : Set G)), O2 (centralizer (T : Set G))⁆ ⊔
        O (centralizer (T : Set G))).map (MulAut.conj n⁻¹).toMonoidHom = ⁅O2 K', O2 K'⁆ ⊔ O K' := by
      rw [Subgroup.map_sup, map_commutator, map_O2, map_O]
    have hR'K : R' ≤ ⁅O2 K', O2 K'⁆ ⊔ O K' := by
      rw [← hcore]
      exact map_mono hRK
    have hR'2 : IsPGroup 2 R' := hR2.map _
    have h1 := card_le_of_bar_le hS hQP hPQ h₁ h₃ (hR'K.trans ((core_le K').trans hK'z)) hR'2
      ((bar_mono hR'K).trans ((bar_core hP h₁ h₂ h₃ hgen hK'z hHK').le.trans
        (commutator_le_self H₁)))
    rwa [hR', card_map_of_injective (MulAut.conj n⁻¹).injective] at h1

theorem side_lemma_4_9 (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆)
    (htrans : ∀ t ∈ P, t ≠ 1 → t * t = 1 → ∃ (n : G) (V' : Subgroup G),
      n * z * n⁻¹ = t ∧ V' ≤ P ∧ z ∈ V' ∧ n ∈ normalizer (V' : Set G))
    {V M : Subgroup G} (hVP : V ≤ P) (hzV : z ∈ V) (hM : M = centralizer (V : Set G))
    {T : Subgroup G} (hTP : T ≤ P) (hT : T ≠ ⊥) {K : Subgroup G}
    (hK : K ∈ ({centralizer (T : Set G), normalizer (T : Set G)} : Set (Subgroup G))) :
    (K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K ≤ K ∧
      (((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K).subgroupOf K).Normal ∧
      ABGLocalTools.IsSylowOf 2 Q ((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K) ∧
      QuotIso ((K ⊓ (⁅O2 M, O2 M⁆ ⊔ O M)) ⊔ O K) (O K) (⁅O2 M, O2 M⁆ ⊔ O M) (O M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  have hgen : O2 H₁ = H₁ := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  have hPz : P ≤ C z := le_sup_left.trans hS.le
  have hCp : H₁ ≤ bar (C z) (centralizer (P : Set G)) := le_bar_centralizer hP hPz h₃
  subst hM
  have hDz : centralizer (P : Set G) ≤ C z :=
    centralizer_le (Set.singleton_subset_iff.2 (hVP hzV))
  have hDM : centralizer (P : Set G) ≤ centralizer (V : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hVP)
  have hMz : centralizer (V : Set G) ≤ C z := centralizer_le (Set.singleton_subset_iff.2 hzV)
  have hOM : O (centralizer (V : Set G)) = centralizer (V : Set G) ⊓ O (C z) :=
    O_eq_inf hP h₁ h₂ h₃ hMz (hCp.trans (bar_mono hDM))
  have hOD : O (centralizer (P : Set G)) = centralizer (P : Set G) ⊓ O (C z) :=
    O_eq_inf hP h₁ h₂ h₃ hDz hCp
  have hD₀M := core_eq hP h₁ h₂ h₃ hgen hDM hMz hCp
  have hODM : centralizer (P : Set G) ⊓ O (centralizer (V : Set G)) ≤
      O (centralizer (P : Set G)) := by
    rw [hOM, hOD]
    exact inf_le_inf_left _ inf_le_right
  have hODM' : O (centralizer (P : Set G)) ≤ O (centralizer (V : Set G)) := by
    rw [hOM, hOD]
    exact inf_le_inf_right _ hDM
  have hQ := le_core hS hQP hPQ h₁ h₂ h₃ h₄ hDz hCp hQP
  obtain ⟨hK2, hK3, hK4⟩ := centralizer_facts hS hQP hPQ h₁ h₂ h₃ h₄ htrans hTP hT
  have hDKc : centralizer (P : Set G) ≤ centralizer (T : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hTP)
  have hODKc : O (centralizer (P : Set G)) ≤ O (centralizer (T : Set G)) :=
    hK3 _ ((O_le_self _).trans hDKc) (card_O_odd _) (le_normalizer_O _)
  have hOMKc : O (centralizer (V : Set G)) ⊓ centralizer (T : Set G) ≤
      O (centralizer (T : Set G)) :=
    hK3 _ inf_le_right (odd_card_of_le inf_le_left (card_O_odd _))
      (fun d hd => mem_normalizer_inf (le_normalizer_O _ (hDM hd)) (le_normalizer (hDKc hd)))
  rcases hK with rfl | hK
  ·
    refine k₀_facts hD₀M hDKc hDM hODM hODM' hODKc hOMKc ?_ ?_ hQ hQ2
    · rw [← hK2]
      exact le_normalizer_core _
    · rw [← hK2]
      exact hK4
  ·
    rw [Set.mem_singleton_iff] at hK
    subst hK
    have hKcKn : centralizer (T : Set G) ≤ normalizer (T : Set G) := centralizer_le_normalizer _
    have hOKc : O (centralizer (T : Set G)) ≤ O (normalizer (T : Set G)) := by
      refine le_O_of_odd ((O_le_self _).trans hKcKn) (fun g hg => ?_) (card_O_odd _)
      rw [mem_normalizer_iff_map_conj_eq', map_O,
        mem_normalizer_iff_map_conj_eq'.1 (mem_normalizer_centralizer hg)]
    have hOMKn : O (centralizer (V : Set G)) ⊓ normalizer (T : Set G) ≤
        O (centralizer (V : Set G)) ⊓ centralizer (T : Set G) := by
      refine le_inf inf_le_left fun g hg => ?_
      obtain ⟨hgO, hgN⟩ := mem_inf.1 hg
      have hgOz : g ∈ O (C z) := by
        rw [hOM] at hgO
        exact (mem_inf.1 hgO).2
      rw [mem_centralizer_iff]
      intro τ hτ
      have hτz : τ ∈ C z := hPz (hTP hτ)
      have h1 : g * τ * g⁻¹ * τ⁻¹ ∈ T :=
        mul_mem ((mem_normalizer_iff.1 hgN τ).1 hτ) (inv_mem hτ)
      have h2 : g * τ * g⁻¹ * τ⁻¹ ∈ O (C z) := by
        have h3 : τ * g⁻¹ * τ⁻¹ ∈ O (C z) :=
          (mem_normalizer_iff.1 (le_normalizer_O (C z) hτz) _).1 (inv_mem hgOz)
        have e : g * τ * g⁻¹ * τ⁻¹ = g * (τ * g⁻¹ * τ⁻¹) := by group
        rw [e]
        exact mul_mem hgOz h3
      have h4 := eq_one_of_mem_of_mem (hP.to_le hTP) (card_O_odd (C z)) h1 h2
      have h5 : g * τ * g⁻¹ = τ := mul_inv_eq_one.1 h4
      calc τ * g = g * τ * g⁻¹ * g := by rw [h5]
        _ = g * τ := by group
    have e : ⁅O2 (centralizer (P : Set G)), O2 (centralizer (P : Set G))⁆ ⊔
        O (normalizer (T : Set G)) = (⁅O2 (centralizer (T : Set G)), O2 (centralizer (T : Set G))⁆ ⊔
          O (centralizer (T : Set G))) ⊔ O (normalizer (T : Set G)) := by
      rw [hK2, sup_assoc, sup_eq_right.2 hOKc]
    refine k₀_facts hD₀M (hDKc.trans hKcKn) hDM hODM hODM' (hODKc.trans hOKc)
      (hOMKn.trans (hOMKc.trans hOKc)) ?_ ?_ hQ hQ2
    · rw [e]
      exact fun g hg => mem_normalizer_sup (mem_normalizer_centralizer_core hg)
        (le_normalizer_O _ hg)
    · intro R hR hR2
      refine hK4 R (fun r hr => ?_) hR2
      obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
      have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact mem_of_mem_sup_of_odd (card_O_odd _)
        (fun g hg => mem_normalizer_centralizer_core (O_le_self _ hg)) (e ▸ hR hr) hk'

end Side

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem lemma_4_9_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁))) :
    (∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ →
      ∀ K ∈ ({centralizer (T₁ : Set G), normalizer (T₁ : Set G)} : Set (Subgroup G)),
        let K₀ := (K ⊓ 𝔖.M₀ A) ⊔ O K
        K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ K₀ ∧
          QuotIso K₀ (O K) (𝔖.M₀ A) (O (𝔖.M A))) ∧
    (∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ →
      ∀ K ∈ ({centralizer (T₂ : Set G), normalizer (T₂ : Set G)} : Set (Subgroup G)),
        let K₀ := (K ⊓ 𝔖.N₀ A) ⊔ O K
        K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ K₀ ∧
          QuotIso K₀ (O K) (𝔖.N₀ A) (O (𝔖.N A))) := by
  obtain ⟨⟨H₁, h₁, h₂, h₃, h₄, -⟩, ⟨K₁, k₁, k₂, k₃, k₄, -⟩⟩ := h315 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have hS₁ : ABGLocalTools.IsSylowOf 2 (𝔖.S₁ ⊔ 𝔖.S₂) (C 𝔖.z₁) := by
    rw [𝔖.decomp.sup_eq]
    exact isSylowOf_of_sylow_le 𝔖.S 𝔖.S_le_C_z₁
  have hS₂ : ABGLocalTools.IsSylowOf 2 (𝔖.S₂ ⊔ 𝔖.S₁) (C 𝔖.z₂) := by
    rw [sup_comm, 𝔖.decomp.sup_eq]
    exact isSylowOf_of_sylow_le 𝔖.S (S_le_C_z₂ 𝔖)
  have hPQ₂ : 𝔖.S₂ ⊓ 𝔖.S₁ = ⊥ := by
    rw [inf_comm]
    exact 𝔖.decomp.inf_eq
  have htrans₁ : ∀ t ∈ 𝔖.S₁, t ≠ 1 → t * t = 1 → ∃ (n : G) (V' : Subgroup G),
      n * 𝔖.z₁ * n⁻¹ = t ∧ V' ≤ 𝔖.S₁ ∧ 𝔖.z₁ ∈ V' ∧ n ∈ normalizer (V' : Set G) := by
    intro t ht ht1 ht2
    obtain ⟨A', hA'S, hA', htA'⟩ := 𝔖.decomp.exists_e16_mem (S₁_le_S 𝔖 ht) ht2
    obtain ⟨n, hnA', hnt⟩ :=
      exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hA'S hA' (mem_inf.2 ⟨htA', ht⟩) ht1
    exact ⟨n, 𝔖.X A', hnt, X_le_S₁ 𝔖, z₁_mem_X 𝔖 hA'S hA',
      normalizer_le_normalizer_X 𝔖 hA'S hA' hnA'⟩
  have htrans₂ : ∀ t ∈ 𝔖.S₂, t ≠ 1 → t * t = 1 → ∃ (n : G) (V' : Subgroup G),
      n * 𝔖.z₂ * n⁻¹ = t ∧ V' ≤ 𝔖.S₂ ∧ 𝔖.z₂ ∈ V' ∧ n ∈ normalizer (V' : Set G) := by
    intro t ht ht1 ht2
    obtain ⟨A', hA'S, hA', htA'⟩ := 𝔖.decomp.exists_e16_mem (S₂_le_S 𝔖 ht) ht2
    obtain ⟨n, hnA', hnt⟩ :=
      exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hA'S hA' (mem_inf.2 ⟨htA', ht⟩) ht1
    exact ⟨n, 𝔖.Y A', hnt, Y_le_S₂ 𝔖, z₂_mem_Y 𝔖 hA'S hA',
      normalizer_le_normalizer_Y 𝔖 hA'S hA' hnA'⟩
  refine ⟨fun T₁ hT₁ hT₁1 K hK => ?_, fun T₂ hT₂ hT₂1 K hK => ?_⟩
  · exact side_lemma_4_9 hS₁ (S₂_le_centralizer_S₁ 𝔖) 𝔖.decomp.inf_eq h₁ h₂ h₃ h₄ htrans₁
      (X_le_S₁ 𝔖) (z₁_mem_X 𝔖 hAS hA) (M := 𝔖.M A) rfl hT₁ hT₁1 hK
  · exact side_lemma_4_9 hS₂ (S₁_le_centralizer_S₂ 𝔖) hPQ₂ k₁ k₂ k₃ k₄ htrans₂
      (Y_le_S₂ 𝔖) (z₂_mem_Y 𝔖 hAS hA) (M := 𝔖.N A) rfl hT₂ hT₂1 hK

end Sec4Setting

end CFSG.GH72

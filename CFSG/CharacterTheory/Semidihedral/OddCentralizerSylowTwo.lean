module

public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Semidihedral.OddCentralizerSylowTwo

open scoped commutatorElement

variable {K : Type*} [Group K]

theorem mem_zpowers_involution (i : K) (hi : orderOf i = 2) (x : K) :
    x ∈ Subgroup.zpowers i ↔ x = 1 ∨ x = i := by
  classical
  have hfin : IsOfFinOrder i := orderOf_pos_iff.mp (by rw [hi]; decide)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hi]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp
    · simp
  · rintro (h | h)
    · exact ⟨0, by decide, (pow_zero i).trans h.symm⟩
    · exact ⟨1, by decide, (pow_one i).trans h.symm⟩

variable [Finite K]

theorem sylow_centralizer_eq_zpowers (i : K) (hi : orderOf i = 2)
    (hC : ∀ P : Sylow 2 (Subgroup.centralizer ({i} : Set K)), Nat.card P = 2)
    (S : Sylow 2 K) (hiS : i ∈ S) :
    Subgroup.centralizer ({(⟨i, hiS⟩ : S)} : Set S) =
      Subgroup.zpowers (⟨i, hiS⟩ : S) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let j : S := ⟨i, hiS⟩
  let D : Subgroup S := Subgroup.centralizer ({j} : Set S)
  let C : Subgroup K := Subgroup.centralizer ({i} : Set K)
  let f : D →* C :=
    { toFun := fun x => ⟨x.val.val,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have hv : x.val.val = y.val.val := congrArg (fun z : C => (z : K)) h
    exact Subtype.ext (Subtype.ext hv)
  have hD : IsPGroup 2 D := S.isPGroup'.to_subgroup D
  obtain ⟨P, hP⟩ := (hD.of_equiv (MonoidHom.ofInjective hf)).exists_le_sylow
  have hc : Nat.card D ≤ 2 := by
    have hdvd : Nat.card f.range ∣ Nat.card P := Subgroup.card_dvd_of_le hP
    have hcard : Nat.card f.range = Nat.card D :=
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    rw [hcard, hC P] at hdvd
    exact Nat.le_of_dvd (by decide) hdvd
  have hj : orderOf j = 2 :=
    (Subgroup.orderOf_coe (⟨i, hiS⟩ : S)).symm.trans hi
  have hle : Subgroup.zpowers j ≤ D := Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcard : Nat.card (Subgroup.zpowers j) = 2 := (Nat.card_zpowers j).trans hj
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard]
  exact hc

theorem sylow_containing_involution_eq_zpowers (i : K) (hi : orderOf i = 2)
    (hC : ∀ P : Sylow 2 (Subgroup.centralizer ({i} : Set K)), Nat.card P = 2)
    (S : Sylow 2 K) (hiS : i ∈ S) : (S : Subgroup K) = Subgroup.zpowers i := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let j : S := ⟨i, hiS⟩
  have hj : orderOf j = 2 :=
    (Subgroup.orderOf_coe (⟨i, hiS⟩ : S)).symm.trans hi
  have hjne : j ≠ 1 := by
    intro h
    simp [h] at hj
  let : Nontrivial S := ⟨⟨j, 1, hjne⟩⟩
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center S)
  have hzj : (z : S) = j := by
    have hzD : (z : S) ∈ Subgroup.centralizer ({j} : Set S) :=
      Subgroup.center_le_centralizer _ z.property
    rw [sylow_centralizer_eq_zpowers i hi hC S hiS] at hzD
    rcases (mem_zpowers_involution j hj (z : S)).mp hzD with h | h
    · exact (hz (Subtype.ext h)).elim
    · exact h
  have hjZ : j ∈ Subgroup.center S := hzj ▸ z.property
  have hall : ∀ x : S, x ∈ Subgroup.zpowers j := by
    intro x
    rw [← sylow_centralizer_eq_zpowers i hi hC S hiS]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp hjZ x)
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hall ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  · exact Subgroup.zpowers_le.mpr hiS

theorem all_sylow_two_card_eq_two (i : K) (hi : orderOf i = 2)
    (hC : ∀ P : Sylow 2 (Subgroup.centralizer ({i} : Set K)), Nat.card P = 2) :
    ∀ S : Sylow 2 K, Nat.card S = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi, pow_one])
  obtain ⟨S, hS⟩ := hI.exists_le_sylow
  have hiS : i ∈ S := hS (Subgroup.mem_zpowers i)
  have hScard : Nat.card S = 2 := by
    rw [sylow_containing_involution_eq_zpowers i hi hC S hiS, Nat.card_zpowers, hi]
  intro T
  rw [← Nat.card_congr (S.equiv T).toEquiv, hScard]

variable {K : Type*} [Group K]

theorem normalizer_zpowers_involution_le_centralizer (i : K) (hi : orderOf i = 2) :
    Subgroup.normalizer (Subgroup.zpowers i : Set K) ≤
      Subgroup.centralizer (Subgroup.zpowers i : Set K) := by
  intro g hg
  have hconj : g * i * g⁻¹ = i := by
    have hm : g * i * g⁻¹ ∈ Subgroup.zpowers i :=
      (Subgroup.mem_normalizer_iff.mp hg i).mp (Subgroup.mem_zpowers i)
    rcases (mem_zpowers_involution i hi _).mp hm with h | h
    · have hi1 : i = 1 := by
        have h' := congrArg (fun x : K => g⁻¹ * x * g) h
        simpa [mul_assoc] using h'
      simp [hi1] at hi
    · exact h
  have hgi : g * i = i * g := by
    have h := congrArg (fun x : K => x * g) hconj
    simpa [mul_assoc] using h
  intro x hx
  rcases (mem_zpowers_involution i hi x).mp hx with rfl | rfl
  · simp
  · exact hgi.symm

theorem odd_subgroup_le_two_group_kernel {Q : Type*} [Group Q]
    (f : K →* Q) (hQ : IsPGroup 2 Q) (H : Subgroup K) (hH : Odd (Nat.card H)) :
    H ≤ f.ker := by
  have hp : IsPGroup 2 (H.map f) := hQ.to_subgroup _
  have hdvd : Nat.card (H.map f) ∣ Nat.card H := Subgroup.card_map_dvd H f
  have htriv : H.map f = ⊥ := by
    apply Subgroup.card_eq_one.mp
    exact hp.card_eq_or_dvd.resolve_right (fun h => hH.not_two_dvd_nat (h.trans hdvd))
  intro x hx
  have hm : f x ∈ H.map f := ⟨x, hx, rfl⟩
  rw [htriv] at hm
  exact hm

variable [Finite K]

theorem involution_centralizer_two_part_odd_core (i : K) (hi : orderOf i = 2)
    (hC : ∀ P : Sylow 2 (Subgroup.centralizer ({i} : Set K)), Nat.card P = 2) :
    (∀ S : Sylow 2 K, Nat.card S = 2) ∧
      Odd (Nat.card (CFSG.oddCore K)) ∧ (CFSG.oddCore K).index = 2 ∧
      Nat.card (K ⧸ CFSG.oddCore K) = 2 ∧
      (CFSG.oddCore K).IsComplement' (Subgroup.zpowers i) ∧
      (∀ H : Subgroup K, H.Normal → Odd (Nat.card H) → H ≤ CFSG.oddCore K) ∧
      (∃ e : K ⧸ CFSG.oddCore K ≃* ↥(Subgroup.zpowers i),
        ∀ x : Subgroup.zpowers i, e.symm x = QuotientGroup.mk' (CFSG.oddCore K) x) ∧
      (∀ a b : K ⧸ CFSG.oddCore K, a * b = b * a) ∧
      (QuotientGroup.mk' (CFSG.oddCore K) i ∈ Subgroup.center (K ⧸ CFSG.oddCore K)) ∧
      (∀ k : K, ⁅k, i⁆ ∈ CFSG.oddCore K) ∧
      ⁅(⊤ : Subgroup K), Subgroup.zpowers i⁆ ≤ CFSG.oddCore K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi, pow_one])
  obtain ⟨S, hS⟩ := hI.exists_le_sylow
  have hiS : i ∈ S := hS (Subgroup.mem_zpowers i)
  have hSdef : (S : Subgroup K) = Subgroup.zpowers i :=
    sylow_containing_involution_eq_zpowers i hi hC S hiS
  have hNS : Subgroup.normalizer (S : Set K) ≤ Subgroup.centralizer (S : Set K) := by
    change Subgroup.normalizer ((S : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((S : Subgroup K) : Set K)
    rw [hSdef]
    exact normalizer_zpowers_involution_le_centralizer i hi
  let f : K →* S := MonoidHom.transferSylow S hNS
  let O : Subgroup K := f.ker
  have hcomp : O.IsComplement' (S : Subgroup K) :=
    MonoidHom.ker_transferSylow_isComplement' S hNS
  have hodd : Odd (Nat.card O) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact MonoidHom.not_dvd_card_ker_transferSylow S hNS
  have hO : O = CFSG.oddCore K := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hodd⟩
    · apply sSup_le
      intro H hH
      exact odd_subgroup_le_two_group_kernel f S.isPGroup' H hH.2
  have hidx : (CFSG.oddCore K).index = 2 := by
    rw [← hO, hcomp.symm.index_eq_card, all_sylow_two_card_eq_two i hi hC S]
  have hcompl : (CFSG.oddCore K).IsComplement' (Subgroup.zpowers i) := by
    simpa only [hO, hSdef] using hcomp
  let e : K ⧸ CFSG.oddCore K ≃* ↥(Subgroup.zpowers i) := hcompl.symm.QuotientMulEquiv
  have hcomm : ∀ a b : K ⧸ CFSG.oddCore K, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rcases (mem_zpowers_involution i hi (e a : K)).mp (e a).property with h | h
    · simp [h]
    · rcases (mem_zpowers_involution i hi (e b : K)).mp (e b).property with h' | h'
      · simp [h']
      · simp [h, h']
  have hZ : QuotientGroup.mk' (CFSG.oddCore K) i ∈
      Subgroup.center (K ⧸ CFSG.oddCore K) :=
    Subgroup.mem_center_iff.mpr (fun a => hcomm a _)
  have hki : ∀ k : K, ⁅k, i⁆ ∈ CFSG.oddCore K := by
    intro k
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (CFSG.oddCore K) ⁅k, i⁆ = 1
    rw [map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  refine ⟨all_sylow_two_card_eq_two i hi hC, hO ▸ hodd, hidx, ?_, hcompl,
    ?_, ⟨e, ?_⟩, hcomm, hZ, hki, ?_⟩
  · rwa [← Subgroup.index_eq_card]
  · intro H hHN hHodd
    exact le_sSup ⟨hHN, hHodd⟩
  · intro x
    rfl
  · apply Subgroup.commutator_le.mpr
    intro k _ x hx
    rcases (mem_zpowers_involution i hi x).mp hx with rfl | rfl
    · simp
    · exact hki k

@[expose] def originalOddCore {G : Type*} [Group G] (K : Subgroup G) : Subgroup G :=
  (CFSG.oddCore K).map K.subtype

theorem mem_originalOddCore {G : Type*} [Group G] (K : Subgroup G) (x : K) :
    (x : G) ∈ originalOddCore K ↔ x ∈ CFSG.oddCore K := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := Subtype.ext heq
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem originalOddCore_comap {G : Type*} [Group G] (K : Subgroup G) :
    (originalOddCore K).comap K.subtype = CFSG.oddCore K := by
  ext x
  exact mem_originalOddCore K x

instance originalOddCore_normal {G : Type*} [Group G] (K : Subgroup G) :
    ((originalOddCore K).subgroupOf K).Normal := by
  rw [show (originalOddCore K).subgroupOf K = CFSG.oddCore K from originalOddCore_comap K]
  infer_instance

end CFSG.Semidihedral.OddCentralizerSylowTwo

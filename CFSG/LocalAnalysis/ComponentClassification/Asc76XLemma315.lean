module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma314

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def omega1 (H : Subgroup G) : Subgroup G :=
  closure {x | x ∈ H ∧ x ^ 2 = 1}

theorem mem_omega1_of_sq {H : Subgroup G} {x : G} (hx : x ∈ H) (hx2 : x ^ 2 = 1) :
    x ∈ omega1 H :=
  subset_closure ⟨hx, hx2⟩

theorem omega1_le (H : Subgroup G) : omega1 H ≤ H :=
  (closure_le _).mpr fun _ hx => hx.1

theorem rightConjugate_closure_le {s : Set G} {g : G} {H : Subgroup G}
    (h : ∀ x ∈ s, g⁻¹ * x * g ∈ H) : rightConjugate (closure s) g ≤ H := by
  rw [rightConjugate, map_le_iff_le_comap, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_comap]
  simpa [MulAut.conj_apply] using h x hx

theorem isElemAbelian_closure {s : Set G} (hs : ∀ x ∈ s, x ^ 2 = 1)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsElemAbelian 2 (closure s) := by
  have h1 : closure s ≤ centralizer s :=
    (closure_le _).mpr fun x hx => mem_centralizer_iff.mpr fun y hy => hc y hy x hx
  have h2 : closure s ≤ centralizer (closure s : Set G) :=
    (closure_le _).mpr fun x hx => mem_centralizer_iff.mpr fun y hy =>
      (mem_centralizer_iff.mp (h1 hy) x hx).symm
  have hsq : ∀ x ∈ closure s, x ^ 2 = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx => exact hs x hx
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := mem_centralizer_iff.mp (h2 hb) a ha
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha ih => rw [inv_pow, ih, inv_one]
  exact ⟨isMulCommutative_of_forall_sq_eq_one hsq, hsq⟩

theorem exists_sylow_eq_of_isSylowOf_top {H : Type} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsSylowOf 2 P ⊤) : ∃ S : Sylow 2 H, (S : Subgroup H) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylowOf_iff_card.mp hP).2
  rw [Subgroup.card_top] at h
  exact ⟨Sylow.ofCard P h, Sylow.coe_ofCard _ _⟩

variable [Finite G]

theorem commute_of_sq_eq_one (hB : BenderFacts) {A T : Subgroup G} (hTA : T ≤ A)
    (hT2 : IsPGroup 2 T) (hsz : IsSzOrU3 (BarGroup A)) (hTs : IsSylowOf 2 (bar A T) ⊤)
    {x y : G} (hx : x ∈ T) (hx2 : x ^ 2 = 1) (hy : y ∈ T) : x * y = y * x := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top hTs
  have hxP : barMk A ⟨x, hTA hx⟩ ∈ (P : Subgroup (BarGroup A)) := by
    rw [hP]
    exact barMk_mem_bar hx
  have hyP : barMk A ⟨y, hTA hy⟩ ∈ (P : Subgroup (BarGroup A)) := by
    rw [hP]
    exact barMk_mem_bar hy
  have hx2' : (barMk A ⟨x, hTA hx⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have h : (⟨x, hTA hx⟩ : A) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    rw [h, map_one]
  have hcomm := mem_centralizer_iff.mp (hB.involution_center _ hsz P _ hxP hx2') _ hyP
  set c : A := ⟨x, hTA hx⟩ * ⟨y, hTA hy⟩ * (⟨x, hTA hx⟩)⁻¹ * (⟨y, hTA hy⟩)⁻¹ with hcdef
  have hc1 : barMk A c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hcT : (c : G) ∈ T := by
    rw [hcdef]
    simp only [coe_mul, coe_inv]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
  have hk' : c ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 := congrArg Subtype.val
    (eq_one_of_two_element_of_ker (barMk A) (odd_card_ker_barMk A) hk' hc1)
  rw [hcdef] at h1
  simp only [coe_mul, coe_inv, OneMemClass.coe_one] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem commute_of_aut (hB : BenderFacts) {A T : Subgroup G} (hTA : T ≤ A) (hT2 : IsPGroup 2 T)
    (hsz : IsSzOrU3 (BarGroup A)) (hTs : IsSylowOf 2 (bar A T) ⊤) {v : G}
    (hvA : v ∈ normalizer (A : Set G)) (hvT : v ∈ normalizer (T : Set G)) (hv2 : v ^ 2 = 1)
    {t : G} (ht : t ∈ T) (ht2 : t ^ 2 = 1) : v * t = t * v := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top hTs
  set ψ := conjAutOf A hvA with hψdef
  set φ : MulAut (BarGroup A) :=
    QuotientGroup.congr (CFSG.oddCore A) (CFSG.oddCore A) ψ (oddCore_map_mulEquiv' ψ) with hφdef
  have hφ : ∀ y : A, φ (barMk A y) = barMk A (ψ y) := fun y => rfl
  have hvv : v * v = 1 := by rw [← sq]; exact hv2
  have hφ2 : φ * φ = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore A) x
    rw [MulAut.mul_apply, MulAut.one_apply]
    change φ (φ (barMk A y)) = barMk A y
    rw [hφ, hφ]
    congr 1
    apply Subtype.ext
    rw [conjAutOf_apply, conjAutOf_apply]
    calc v * (v * (y : G) * v⁻¹) * v⁻¹ = (v * v) * (y : G) * (v * v)⁻¹ := by group
      _ = y := by rw [hvv, one_mul, inv_one, mul_one]
  have hφP : ∀ x ∈ (P : Subgroup (BarGroup A)), φ x ∈ (P : Subgroup (BarGroup A)) := by
    intro x hx
    rw [hP] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hφ]
    refine barMk_mem_bar ?_
    rw [conjAutOf_apply]
    exact (mem_normalizer_iff.mp hvT _).mp (mem_subgroupOf.mp hy)
  have htP : barMk A ⟨t, hTA ht⟩ ∈ (P : Subgroup (BarGroup A)) := by
    rw [hP]
    exact barMk_mem_bar ht
  have ht2' : (barMk A ⟨t, hTA ht⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have h : (⟨t, hTA ht⟩ : A) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [h, map_one]
  have hfix := hB.aut_involution_center _ hsz P φ hφ2 hφP _ htP
    (hB.involution_center _ hsz P _ htP ht2')
  rw [hφ] at hfix
  set w : A := ψ ⟨t, hTA ht⟩ * (⟨t, hTA ht⟩)⁻¹ with hwdef
  have hw1 : barMk A w = 1 := by rw [hwdef, map_mul, map_inv, hfix, mul_inv_cancel]
  have hwG : (w : G) = v * t * v⁻¹ * t⁻¹ := by
    rw [hwdef, coe_mul, coe_inv, conjAutOf_apply]
  have hwT : (w : G) ∈ T := by
    rw [hwG]
    exact mul_mem ((mem_normalizer_iff.mp hvT t).mp ht) (inv_mem ht)
  obtain ⟨k, hk⟩ := hT2 ⟨w, hwT⟩
  have hk' : w ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 := congrArg Subtype.val
    (eq_one_of_two_element_of_ker (barMk A) (odd_card_ker_barMk A) hk' hw1)
  rw [hwG, OneMemClass.coe_one] at h1
  calc v * t = (v * t * v⁻¹ * t⁻¹) * (t * v) := by group
    _ = t * v := by rw [h1, one_mul]

theorem mem_of_weaklyClosed {S Z : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hZS : Z ≤ S)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hwc : ∀ h : G, rightConjugate Z h ≤ S → rightConjugate Z h = Z) {u h : G}
    (huZ : ∀ z ∈ Z, z * u = u * z) (hhu : h⁻¹ * u * h ∈ Z) : u ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hZ2 : IsPGroup 2 Z := hS2.to_le hZS
  set C := centralizer ({u} : Set G) with hCdef
  have hmemC : ∀ x, x * u = u * x → x ∈ C := fun x hx => mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx.symm
  have hZC : Z ≤ C := fun z hz => hmemC z (huZ z hz)
  have hZhC : rightConjugate Z h⁻¹ ≤ C := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    apply hmemC
    have h1 := hZab _ hx _ hhu
    calc x * u = h * ((h⁻¹ * x * h) * (h⁻¹ * u * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * u * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [h1]
      _ = u * x := by group
  have hZh2 : IsPGroup 2 (rightConjugate Z h⁻¹) := hZ2.map _
  obtain ⟨Q, hQ, hZQ⟩ := exists_isSylowOf_le hZC hZ2
  obtain ⟨Q', hQ', hZQ'⟩ := exists_isSylowOf_le hZhC hZh2
  obtain ⟨c, hc, hQc⟩ := exists_conj_of_isSylowOf hQ hQ'
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (isSylowOf_iff_card.mp hQ).2
  obtain ⟨S', hS'', hQS'⟩ := exists_isSylowOf_le (le_top : Q ≤ ⊤) hQ2
  obtain ⟨d, -, hS'd⟩ := exists_conj_of_isSylowOf hS hS''
  have hcu : c * u * c⁻¹ = u := by
    have h1 := mem_centralizer_iff.mp hc u (Set.mem_singleton u)
    rw [← h1, mul_inv_cancel_right]
  have hd1 : rightConjugate Z d⁻¹ = Z := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := hQS' (hZQ hx)
    rw [hS'd, mem_rightConjugate_iff] at h1
    have e : d * (d⁻¹ * x * d) * d⁻¹ = x := by group
    rwa [e] at h1
  have hd2 : rightConjugate Z (d * c * h)⁻¹ = Z := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 : h * ((d * c * h)⁻¹ * x * (d * c * h)) * h⁻¹ ∈ rightConjugate Z h⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      have e : h⁻¹ * (h * ((d * c * h)⁻¹ * x * (d * c * h)) * h⁻¹) * h =
          (d * c * h)⁻¹ * x * (d * c * h) := by group
      rw [e]
      exact hx
    have h2 := hZQ' h1
    rw [hQc, mem_rightConjugate_iff] at h2
    have h3 := hQS' h2
    rw [hS'd, mem_rightConjugate_iff] at h3
    have e : d * (c * (h * ((d * c * h)⁻¹ * x * (d * c * h)) * h⁻¹) * c⁻¹) * d⁻¹ = x := by group
    rwa [e] at h3
  have h1 : (d * c * h) * (h⁻¹ * u * h) * (d * c * h)⁻¹ ∈ Z := by
    have h0 : (d * c * h) * (h⁻¹ * u * h) * (d * c * h)⁻¹ ∈ rightConjugate Z (d * c * h)⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      have e : (d * c * h)⁻¹ * ((d * c * h) * (h⁻¹ * u * h) * (d * c * h)⁻¹) * (d * c * h) =
          h⁻¹ * u * h := by group
      rw [e]
      exact hhu
    rwa [hd2] at h0
  have h2 : d * u * d⁻¹ ∈ Z := by
    have e : (d * c * h) * (h⁻¹ * u * h) * (d * c * h)⁻¹ = d * (c * u * c⁻¹) * d⁻¹ := by group
    rw [e, hcu] at h1
    exact h1
  have h3 : d * u * d⁻¹ ∈ rightConjugate Z d⁻¹ := by
    rw [hd1]
    exact h2
  rw [mem_rightConjugate_iff] at h3
  have e : d⁻¹ * (d * u * d⁻¹) * d⁻¹⁻¹ = u := by group
  rwa [e] at h3

structure Sec3Inputs : Prop where
  h22 : Lemma22Four
  hB : BenderFacts
  h26 : L26.Asc76Lemma26
  h28 : Asc76Lemma28

structure Config (Ω : Set (Subgroup G)) (K J R T S : Subgroup G) : Prop where
  mem : K ∈ Ω
  adjKJ : adj Ω K J
  sylowR : IsSylowOf 2 R K
  sylowT : IsSylowOf 2 T J
  sylowS : IsSylowOf 2 S ⊤
  le_R : R ≤ S
  le_T : T ≤ S
  good : IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K))

variable {Ω : Set (Subgroup G)}

theorem MinCounter.nbr_facts (hM : MinCounter Ω) (hI : Sec3Inputs) {K : Subgroup G} (hK : K ∈ Ω) :
    OrbitData Ω K (nbr Ω K) ∧ IsSzOrU3 (BarGroup (sSup (nbr Ω K))) ∧
      ∀ J ∈ nbr Ω K, ∀ T : Subgroup G, IsSylowOf 2 T J →
        IsSylowOf 2 (bar (sSup (nbr Ω K)) T) ⊤ := by
  obtain ⟨hπ, -⟩ := hM.orbitData_nbr hI.h22 hI.hB hI.h26 hI.h28 hK
  obtain ⟨hsz, hsyl⟩ := hM.orbit_structure hK hπ
  exact ⟨hπ, hsz, hsyl⟩

namespace Config

variable {K J R T S : Subgroup G}

omit [Finite G] in
theorem J_mem (hc : Config Ω K J R T S) : J ∈ Ω := hc.adjKJ.1

theorem R2 (hc : Config Ω K J R T S) : IsPGroup 2 R :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (isSylowOf_iff_card.mp hc.sylowR).2

theorem T2 (hc : Config Ω K J R T S) : IsPGroup 2 T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (isSylowOf_iff_card.mp hc.sylowT).2

theorem S2 (hc : Config Ω K J R T S) : IsPGroup 2 S :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (isSylowOf_iff_card.mp hc.sylowS).2

theorem R_ne_T (hc : Config Ω K J R T S) (hΩ : Sec3Setting Ω) : R ≠ T := fun h =>
  hc.adjKJ.2.1 (hΩ.eq_of_pGroup_le hc.mem hc.J_mem hc.R2 (hΩ.sylow_ne_bot hc.mem hc.sylowR)
    hc.sylowR.le (h ▸ hc.sylowT.le)).symm

theorem commute_RT (hc : Config Ω K J R T S) (hΩ : Sec3Setting Ω) : ⁅R, T⁆ = ⊥ :=
  hΩ.commute_of_sylow hc.S2 hc.mem hc.J_mem hc.sylowR hc.sylowT hc.le_R hc.le_T (hc.R_ne_T hΩ)

theorem inf_RT (hc : Config Ω K J R T S) (hΩ : Sec3Setting Ω) : R ⊓ T = ⊥ := by
  by_contra h
  exact hc.adjKJ.2.1 (hΩ.eq_of_pGroup_le hc.J_mem hc.mem (hc.R2.to_le inf_le_left) h
    (inf_le_right.trans hc.sylowT.le) (inf_le_left.trans hc.sylowR.le))

omit [Finite G] in
theorem Z_le (hc : Config Ω K J R T S) : omega1 R ⊔ omega1 T ≤ S :=
  sup_le ((omega1_le R).trans hc.le_R) ((omega1_le T).trans hc.le_T)

theorem sylow_eq (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    {L P : Subgroup G} (hL : L ∈ Ω) (hP : IsSylowOf 2 P L) (hPS : P ≤ S) : P = R ∨ P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨hπ, -, hsyl⟩ := hM.nbr_facts hI hc.mem
  have hS2 := hc.S2
  have same : ∀ {M U V : Subgroup G}, IsSylowOf 2 U M → IsSylowOf 2 V M → U ≤ S → V ≤ S →
      U = V := by
    intro M U V hU hV hUS hVS
    have h1 := eq_of_isSylowOf_le hU (hS2.to_le inf_le_left) inf_le_right (le_inf hUS hU.le)
    have h2 := eq_of_isSylowOf_le hV (hS2.to_le inf_le_left) inf_le_right (le_inf hVS hV.le)
    rw [← h1, h2]
  by_cases hLK : L = K
  · subst hLK
    exact Or.inl (same hP hc.sylowR hPS hc.le_R)
  by_cases hLJ : L = J
  · subst hLJ
    exact Or.inr (same hP hc.sylowT hPS hc.le_T)
  exfalso
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (isSylowOf_iff_card.mp hP).2
  have hP1 := hΩ.sylow_ne_bot hL hP
  have hnorm : ∀ {M U : Subgroup G}, M ∈ Ω → IsSylowOf 2 U M → U ≤ S → M ≠ L →
      Even (Nat.card (L ⊓ normalizer (M : Set G) : Subgroup G)) := by
    intro M U hM' hU hUS hML
    have hU2 : IsPGroup 2 U := IsPGroup.of_card (isSylowOf_iff_card.mp hU).2
    have hU1 := hΩ.sylow_ne_bot hM' hU
    have hPU : P ≠ U := fun h =>
      hML (hΩ.eq_of_pGroup_le hM' hL hU2 hU1 hU.le (h ▸ hP.le))
    have hcPU := hΩ.commute_of_sylow hS2 hL hM' hP hU hPS hUS hPU
    have hPN : P ≤ normalizer (M : Set G) :=
      ((commutator_eq_bot_iff_le_centralizer.mp hcPU).trans (centralizer_le_normalizer _)).trans
        (hΩ.normalizer_le_normalizer hM' hU2 hU1 hU.le)
    obtain ⟨x, hx, hx2⟩ := exists_involution hP2 hP1
    rw [even_iff_two_dvd, ← hx2]
    exact orderOf_dvd_natCard _ (mem_inf.mpr ⟨hP.le hx, hPN hx⟩)
  have hKL : adj Ω K L := hΩ.adj_of_even hI.h22 hc.mem hL hLK
    (hnorm hc.mem hc.sylowR hc.le_R (Ne.symm hLK))
  have hJL : adj Ω J L := hΩ.adj_of_even hI.h22 hc.J_mem hL hLJ
    (hnorm hc.J_mem hc.sylowT hc.le_T (Ne.symm hLJ))
  exact hπ.not_adj hΩ hsyl hc.adjKJ hKL (Ne.symm hLJ) hJL

theorem szK (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    IsSzOrU3 (BarGroup (sSup (nbr Ω K))) ∧ IsSylowOf 2 (bar (sSup (nbr Ω K)) T) ⊤ ∧
      T ≤ sSup (nbr Ω K) := by
  obtain ⟨-, hsz, hsyl⟩ := hM.nbr_facts hI hc.mem
  exact ⟨hsz, hsyl J hc.adjKJ T hc.sylowT, hc.sylowT.le.trans (le_sSup hc.adjKJ)⟩

theorem szJ (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    IsSzOrU3 (BarGroup (sSup (nbr Ω J))) ∧ IsSylowOf 2 (bar (sSup (nbr Ω J)) R) ⊤ ∧
      R ≤ sSup (nbr Ω J) := by
  obtain ⟨-, hsz, hsyl⟩ := hM.nbr_facts hI hc.J_mem
  have hJK : adj Ω J K := hM.setting.adj_symm hI.h22 hc.mem hc.adjKJ
  exact ⟨hsz, hsyl K hJK R hc.sylowR, hc.sylowR.le.trans (le_sSup hJK)⟩

theorem isElemAbelian_Z (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    IsElemAbelian 2 (omega1 R ⊔ omega1 T) := by
  obtain ⟨hszK, hTs, hTA⟩ := hc.szK hM hI
  obtain ⟨hszJ, hRs, hRB⟩ := hc.szJ hM hI
  have hRT := hc.commute_RT hM.setting
  have hRTc : ∀ x ∈ R, ∀ y ∈ T, x * y = y * x := fun x hx y hy => by
    have h := commutator_mem_commutator hx hy
    rw [hRT, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  rw [omega1, omega1, ← Subgroup.closure_union]
  refine isElemAbelian_closure ?_ ?_
  · rintro x (hx | hx) <;> exact hx.2
  · rintro x (hx | hx) y (hy | hy)
    · exact commute_of_sq_eq_one hI.hB hRB hc.R2 hszJ hRs hx.1 hx.2 hy.1
    · exact hRTc x hx.1 y hy.1
    · exact (hRTc y hy.1 x hx.1).symm
    · exact commute_of_sq_eq_one hI.hB hTA hc.T2 hszK hTs hx.1 hx.2 hy.1

theorem weaklyClosed (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) {h : G}
    (hZh : rightConjugate (omega1 R ⊔ omega1 T) h ≤ S) :
    rightConjugate (omega1 R ⊔ omega1 T) h = omega1 R ⊔ omega1 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have key : ∀ {M U : Subgroup G}, M ∈ Ω → IsSylowOf 2 U M → omega1 U ≤ omega1 R ⊔ omega1 T →
      rightConjugate (omega1 U) h ≤ omega1 R ⊔ omega1 T := by
    intro M U hM' hU hUZ
    have hUh : rightConjugate (omega1 U) h ≤ S := (map_mono hUZ).trans hZh
    obtain ⟨E, hEU, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank M hM' U hU).1
    have hEo : E ≤ omega1 U := fun e he => mem_omega1_of_sq (hEU he) (hE.2 e he)
    have hEh : rightConjugate E h ≤ S ⊓ rightConjugate M h :=
      le_inf ((map_mono hEo).trans hUh) (map_mono (hEU.trans hU.le))
    have hsyl := hM.lemma310 hI.h22 hI.hB hc.mem hc.sylowR hc.S2 hc.le_R hc.good
      (hΩ.conj_mem M hM' h) hEh (isElemAbelian_rightConjugate hE h)
      (by rw [rightConjugate_card, hE4])
    have hor := hc.sylow_eq hM hI (hΩ.conj_mem M hM' h) hsyl inf_le_left
    refine rightConjugate_closure_le fun x hx => ?_
    have hy : h⁻¹ * x * h ∈ rightConjugate U h := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx.1
    have hy2 : (h⁻¹ * x * h) ^ 2 = 1 := by
      have e := conj_pow (a := h⁻¹) (b := x) (i := 2)
      rw [inv_inv] at e
      rw [e, hx.2, mul_one, inv_mul_cancel]
    have hxo : x ∈ omega1 U := mem_omega1_of_sq hx.1 hx.2
    have hyS : h⁻¹ * x * h ∈ S := hUh (by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hxo)
    have hmem : h⁻¹ * x * h ∈ S ⊓ rightConjugate M h := mem_inf.mpr ⟨hyS, map_mono hU.le hy⟩
    rcases hor with h1 | h1
    · rw [h1] at hmem
      exact mem_sup_left (mem_omega1_of_sq hmem hy2)
    · rw [h1] at hmem
      exact mem_sup_right (mem_omega1_of_sq hmem hy2)
  have hle : rightConjugate (omega1 R ⊔ omega1 T) h ≤ omega1 R ⊔ omega1 T := by
    rw [rightConjugate, Subgroup.map_sup]
    exact sup_le (key hc.mem hc.sylowR le_sup_left) (key hc.J_mem hc.sylowT le_sup_right)
  exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])

theorem mem_normalizer_T (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    {v : G} (hvS : v ∈ S) (hvR : v ∈ normalizer (R : Set G)) : v ∈ normalizer (T : Set G) := by
  have hΩ := hM.setting
  have hTvS : rightConjugate T v ≤ S := fun x hx => by
    rw [mem_rightConjugate_iff] at hx
    have h1 := hc.le_T hx
    have e : x = v⁻¹ * (v * x * v⁻¹) * v := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hvS) h1) hvS
  rcases hc.sylow_eq hM hI (hΩ.conj_mem J hc.J_mem v) (isSylowOf_rightConjugate hc.sylowT v)
    hTvS with h | h
  · exfalso
    have h1 : rightConjugate R v = R := (rightConjugate_eq_self_iff R v).mpr hvR
    exact hc.R_ne_T hΩ (rightConjugate_injective v (h.trans h1.symm)).symm
  · exact (rightConjugate_eq_self_iff T v).mp h

theorem commute_of_mem_normalizer (hc : Config Ω K J R T S) (hM : MinCounter Ω)
    (hI : Sec3Inputs) {v : G} (hvS : v ∈ S) (hv2 : v ^ 2 = 1)
    (hvR : v ∈ normalizer (R : Set G)) : ∀ z ∈ omega1 R ⊔ omega1 T, z * v = v * z := by
  have hΩ := hM.setting
  have hvT := hc.mem_normalizer_T hM hI hvS hvR
  have hvK : v ∈ normalizer (K : Set G) := hΩ.normalizer_le_normalizer hc.mem hc.R2
    (hΩ.sylow_ne_bot hc.mem hc.sylowR) hc.sylowR.le hvR
  have hvJ : v ∈ normalizer (J : Set G) := hΩ.normalizer_le_normalizer hc.J_mem hc.T2
    (hΩ.sylow_ne_bot hc.J_mem hc.sylowT) hc.sylowT.le hvT
  have hvA : v ∈ normalizer ((sSup (nbr Ω K) : Subgroup G) : Set G) :=
    mem_normalizer_sSup fun L hL => adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hL hvK
  have hvB : v ∈ normalizer ((sSup (nbr Ω J) : Subgroup G) : Set G) :=
    mem_normalizer_sSup fun L hL => adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hL hvJ
  obtain ⟨hszK, hTs, hTA⟩ := hc.szK hM hI
  obtain ⟨hszJ, hRs, hRB⟩ := hc.szJ hM hI
  have hZC : omega1 R ⊔ omega1 T ≤ centralizer ({v} : Set G) := by
    rw [omega1, omega1, ← Subgroup.closure_union, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rcases hx with hx | hx
    · exact commute_of_aut hI.hB hRB hc.R2 hszJ hRs hvB hvR hv2 hx.1 hx.2
    · exact commute_of_aut hI.hB hTA hc.T2 hszK hTs hvA hvT hv2 hx.1 hx.2
  intro z hz
  exact (mem_centralizer_iff.mp (hZC hz) v (Set.mem_singleton v)).symm

theorem lemma315 (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    (∀ L ∈ Ω, ∀ P : Subgroup G, IsSylowOf 2 P L → P ≤ S → P = R ∨ P = T) ∧
    ∀ u ∈ S, u ∉ omega1 R ⊔ omega1 T → u ^ 2 = 1 →
      (∃ h : G, h⁻¹ * u * h ∈ omega1 R ⊔ omega1 T) → rightConjugate R u = T := by
  refine ⟨fun L hL P hP hPS => hc.sylow_eq hM hI hL hP hPS, fun u huS huZ hu2 ⟨h, hh⟩ => ?_⟩
  have hΩ := hM.setting
  have hZab := hc.isElemAbelian_Z hM hI
  have hZcomm : ∀ a ∈ omega1 R ⊔ omega1 T, ∀ b ∈ omega1 R ⊔ omega1 T, a * b = b * a :=
    fun a ha b hb => by
      have h1 : (⟨a, ha⟩ : ↥(omega1 R ⊔ omega1 T)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
        hZab.1.is_comm.comm _ _
      simpa using congrArg Subtype.val h1
  have huN : u ∉ normalizer (R : Set G) := fun hu =>
    huZ (mem_of_weaklyClosed hc.sylowS hc.Z_le hZcomm (fun g hg => hc.weaklyClosed hM hI hg)
      (hc.commute_of_mem_normalizer hM hI huS hu2 hu) hh)
  have hRuS : rightConjugate R u ≤ S := fun x hx => by
    rw [mem_rightConjugate_iff] at hx
    have h1 := hc.le_R hx
    have e : x = u⁻¹ * (u * x * u⁻¹) * u := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem huS) h1) huS
  rcases hc.sylow_eq hM hI (hΩ.conj_mem K hc.mem u) (isSylowOf_rightConjugate hc.sylowR u)
    hRuS with h1 | h1
  · exact absurd ((rightConjugate_eq_self_iff R u).mp h1) huN
  · exact h1

end Config

end CFSG.ComponentClassification.Asc76X

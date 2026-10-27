module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiToral
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)
open scoped Pointwise

local instance f4PilotXiCaseLTorusNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Generic

variable {X : Type*} [Group X]

theorem natCard_sup_eq_mul_of_le_normalizer {Q D : Subgroup X}
    (hDQ : D ≤ normalizer (Q : Set X)) (hdisj : Q ⊓ D = ⊥) :
    Nat.card (Q ⊔ D : Subgroup X) = Nat.card Q * Nat.card D := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : Q × D => (⟨(p.1 : X) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
      (Q ⊔ D : Subgroup X))) ⟨fun p p' h => ?_, fun x => ?_⟩)).symm
  · have h' : (p.1 : X) * p.2 = p'.1 * p'.2 := congrArg Subtype.val h
    have hmem : (p'.1 : X)⁻¹ * p.1 ∈ Q ⊓ D := by
      refine mem_inf.2 ⟨mul_mem (inv_mem p'.1.2) p.1.2, ?_⟩
      have e : (p'.1 : X)⁻¹ * p.1 = p'.2 * (p.2 : X)⁻¹ := by
        calc (p'.1 : X)⁻¹ * p.1 = (p'.1 : X)⁻¹ * (p.1 * p.2) * (p.2 : X)⁻¹ := by group
          _ = (p'.1 : X)⁻¹ * (p'.1 * p'.2) * (p.2 : X)⁻¹ := by rw [h']
          _ = p'.2 * (p.2 : X)⁻¹ := by group
      rw [e]
      exact mul_mem p'.2.2 (inv_mem p.2.2)
    rw [hdisj, mem_bot] at hmem
    have h1 : (p.1 : X) = p'.1 := by
      calc (p.1 : X) = p'.1 * ((p'.1 : X)⁻¹ * p.1) := by group
        _ = p'.1 := by rw [hmem, mul_one]
    have h2 : (p.2 : X) = p'.2 := by
      have := h'
      rw [h1] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · have hx : (x : X) ∈ ((Q ⊔ D : Subgroup X) : Set X) := x.2
    rw [coe_mul_of_right_le_normalizer_left Q D hDQ] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem exists_mem_map_conj_le_of_le_sup [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {U T S : Subgroup X} (hU : IsPGroup p U) (hTU : T ≤ normalizer (U : Set X))
    (hUT : U ⊓ T = ⊥) (hS : S ≤ T ⊔ U) (hcop : Nat.Coprime p (Nat.card S)) :
    ∃ u ∈ U, S.map (MulAut.conj u).toMonoidHom ≤ T := by
  have hUN : U ≤ normalizer (U : Set X) := le_normalizer
  have hSN : S ≤ normalizer (U : Set X) := hS.trans (sup_le hTU hUN)
  set F : Subgroup X := U ⊔ S with hF
  have hUF : U ≤ F := le_sup_left
  have hSF : S ≤ F := le_sup_right
  have hFN : F ≤ normalizer (U : Set X) := sup_le hUN hSN
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hU
  have hUS : U ⊓ S = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hcop.pow_left n))
  set N : Subgroup F := U.subgroupOf F with hNdef
  set H : Subgroup F := T.subgroupOf F with hHdef
  set S' : Subgroup F := S.subgroupOf F with hS'def
  have hNnormal : N.Normal := (normal_subgroupOf_iff_le_normalizer hUF).2 hFN
  have hNp : IsPGroup p N := hU.comap_subtype
  have hNsolv : Group.IsSolvable N := by
    have := hNp.isNilpotent
    infer_instance
  have hcardN : Nat.card N = Nat.card U := card_subgroupOf_of_le hUF
  have hcardF : Nat.card F = Nat.card U * Nat.card S := natCard_sup_eq_mul_of_le_normalizer hSN hUS
  have hindex : N.index = Nat.card S := by
    have h1 := N.card_mul_index
    rw [hcardN, hcardF] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcopN : Nat.Coprime (Nat.card N) N.index := by
    rw [hcardN, hindex, hn]
    exact hcop.pow_left n
  have hNH : (N : Set F) * (H : Set F) = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : X) ∈ ((U ⊔ T : Subgroup X) : Set X) := by
      have hle : F ≤ U ⊔ T := sup_le le_sup_left (hS.trans (sup_comm T U).le)
      exact hle f.2
    rw [coe_mul_of_right_le_normalizer_left U T hTU] at hf
    obtain ⟨u, hu, h, hh, huh⟩ := hf
    have hhF : h ∈ F := by
      have : h = u⁻¹ * f := by rw [← huh]; group
      rw [this]
      exact mul_mem (inv_mem (hUF hu)) f.2
    refine ⟨⟨u, hUF hu⟩, hu, ⟨h, hhF⟩, hh, Subtype.ext huh⟩
  have hNK : (N : Set F) * (S' : Set F) = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : X) ∈ ((U ⊔ S : Subgroup X) : Set X) := f.2
    rw [coe_mul_of_right_le_normalizer_left U S hSN] at hf
    obtain ⟨u, hu, s, hs, hus⟩ := hf
    exact ⟨⟨u, hUF hu⟩, hu, ⟨s, hSF hs⟩, hs, Subtype.ext hus⟩
  have hNH' : N ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfU, hfT⟩
    have : (f : X) ∈ U ⊓ T := ⟨hfU, hfT⟩
    rw [hUT, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  have hNK' : N ⊓ S' = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfU, hfS⟩
    have : (f : X) ∈ U ⊓ S := ⟨hfU, hfS⟩
    rw [hUS, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  obtain ⟨m, hmN, hm⟩ :=
    CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNsolv hcopN hNH hNK hNH' hNK'
  refine ⟨(m : X), hmN, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (⟨s, hSF hs⟩ : F) ∈ S' := hs
  rw [hm] at hs'
  obtain ⟨h, hh, hhs⟩ := hs'
  have hhs' : (m : X)⁻¹ * h * m = s := by
    have := congrArg Subtype.val hhs
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] using this
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← hhs']
  have : (m : X) * ((m : X)⁻¹ * (h : X) * m) * (m : X)⁻¹ = h := by group
  rw [this]
  exact hh

end Generic

section Orders

open CFSG.Assembly.LowTwoRank (StatedSp)
open ClassReps

theorem eq_of_two_pow_dvd_of_dvd_two_pow {a k P R : ℕ} (hP : Odd P) (hR : Odd R)
    (h1 : 2 ^ a ∣ 2 ^ k * P) (h2 : 2 ^ k * P ∣ 2 ^ a * R) : k = a := by
  have hcP : Nat.Coprime (2 ^ a) P := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hP)
  have hcR : Nat.Coprime (2 ^ k) R := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hR)
  have ha : a ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcP.dvd_of_dvd_mul_right h1)
  have hk : k ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
    (hcR.dvd_of_dvd_mul_right ((Dvd.intro P rfl).trans h2))
  omega

theorem odd_two_pow_pow_sub_one {f j : ℕ} (hf : 1 ≤ f) (hj : 1 ≤ j) : Odd ((2 ^ f) ^ j - 1) := by
  rw [← pow_mul]
  have h1 : 1 ≤ 2 ^ (f * j) := Nat.one_le_two_pow
  have hev : Even (2 ^ (f * j)) := (Nat.even_pow.2 ⟨even_two, by positivity⟩)
  rcases hev with ⟨m, hm⟩
  exact ⟨m - 1, by omega⟩

theorem natCard_statedSp_three_eq (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp 3 K) = Nat.card K ^ 9 *
      ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring_nf

theorem natCard_statedSp_two_eq (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp 2 K) = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K

theorem map_conj_centralizer_singleton {G : Type*} [Group G] (n a : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * a * n⁻¹} : Set G) := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    calc n * x * n⁻¹ * (n * a * n⁻¹) = n * (x * a) * n⁻¹ := by group
      _ = n * (a * x) * n⁻¹ := by rw [hx]
      _ = n * a * n⁻¹ * (n * x * n⁻¹) := by group
  · intro h
    refine ⟨n⁻¹ * g * n, ?_, by group⟩
    calc n⁻¹ * g * n * a = n⁻¹ * (g * (n * a * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * a * n⁻¹) * g) * n := by rw [h]
      _ = a * (n⁻¹ * g * n) := by group

theorem natCard_centralizer_conj {G : Type*} [Group G] (n a : G) :
    Nat.card (centralizer ({n * a * n⁻¹} : Set G)) = Nat.card (centralizer ({a} : Set G)) := by
  rw [← map_conj_centralizer_singleton, card_map_of_injective (MulAut.conj n).injective]


variable {K : Type} [Field K]

theorem exists_natCard_centralizer_yRep_eq [Finite K] [CharP K 2] (κ : TwoCentral) :
    ∃ k, Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) =
      2 ^ k * Nat.card (levi K κ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hsup, hinf, hN⟩ := factF3 (K := K) κ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hQ
  refine ⟨k, ?_⟩
  rw [← hsup, natCard_sup_eq_mul_of_le_normalizer hN hinf, hk]

theorem pow_dvd_natCard_centralizer_yRep [Finite K] [CharP K 2] (κ : TwoCentral) :
    Nat.card K ^ 24 ∣ Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) := by
  obtain ⟨hT, hU, hTU, -⟩ := weylEltC_conj_frame (K := K)
  set n := weylEltC K weylWordT
  have hUcard : Nat.card ((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)) =
      Nat.card K ^ 24 := by
    rw [card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent,
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4]
  have hle : ∀ z : adjointGroup .F4 K, (∀ u ∈ posUnipotent .F4 K, u * z = z * u) →
      Nat.card K ^ 24 ∣ Nat.card (centralizer ({z} : Set (adjointGroup .F4 K))) := by
    intro z hz
    rw [← hUcard]
    refine Subgroup.card_dvd_of_le fun u hu => mem_centralizer_singleton_iff.2 ?_
    exact Subtype.ext (hz u (Subgroup.mem_subgroupOf.1 hu))
  have hT' : ∀ u ∈ posUnipotent .F4 K, u * (frameT K : ModGL .F4 K) = frameT K * u :=
    fun u hu => f4x_central (Or.inr rfl) 1 hu
  have hU' : ∀ u ∈ posUnipotent .F4 K, u * (frameU K : ModGL .F4 K) = frameU K * u :=
    fun u hu => f4x_central (Or.inl rfl) 1 hu
  have hTU' : ∀ u ∈ posUnipotent .F4 K, u * (frameTU K : ModGL .F4 K) = frameTU K * u := by
    intro u hu
    change u * (f4x K 47 1 * f4x K 44 1) = f4x K 47 1 * f4x K 44 1 * u
    rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hu, mul_assoc, f4x_central (Or.inl rfl) 1 hu,
      mul_assoc]
  cases κ with
  | t => rw [← hT, natCard_centralizer_conj]; exact hle _ hT'
  | u => rw [← hU, natCard_centralizer_conj]; exact hle _ hU'
  | tu => rw [← hTU, natCard_centralizer_conj]; exact hle _ hTU'

theorem natCard_centralizer_yRep_eq_of_levi [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (κ : TwoCentral) {m P : ℕ} (hP : Odd P)
    (hlevi : Nat.card (levi K κ) = (2 ^ f) ^ m * P) :
    Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) = (2 ^ f) ^ 24 * P := by
  obtain ⟨k, hk⟩ := exists_natCard_centralizer_yRep_eq (K := K) κ
  rw [hlevi] at hk
  set R := ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)
  have hR : Odd R := (((odd_two_pow_pow_sub_one hf (by norm_num)).mul
    (odd_two_pow_pow_sub_one hf (by norm_num))).mul (odd_two_pow_pow_sub_one hf (by norm_num))).mul
      (odd_two_pow_pow_sub_one hf (by norm_num))
  have hk' : Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) =
      2 ^ (k + f * m) * P := by
    rw [hk, pow_add, pow_mul, mul_assoc]
  have h1 : 2 ^ (f * 24) ∣ 2 ^ (k + f * m) * P := by
    have h := pow_dvd_natCard_centralizer_yRep (K := K) κ
    rwa [hk', hK, ← pow_mul] at h
  have h2 : 2 ^ (k + f * m) * P ∣ 2 ^ (f * 24) * R := by
    have hd := Subgroup.card_subgroup_dvd_card
      (centralizer ({yRep K κ} : Set (adjointGroup .F4 K)))
    rw [hk', CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK] at hd
    convert hd using 1
    simp only [CFSG.Open.ordF4, R, ← pow_mul]
    ring
  have hka := eq_of_two_pow_dvd_of_dvd_two_pow hP hR h1 h2
  rw [hk', hka, pow_mul]

theorem natCard_centralizer_yRep_of_ne_tu [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {κ : TwoCentral} (hκ : κ ≠ .tu) :
    Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) =
      (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) := by
  refine natCard_centralizer_yRep_eq_of_levi hf hK κ (m := 9)
    (((odd_two_pow_pow_sub_one hf (by norm_num)).mul (odd_two_pow_pow_sub_one hf (by norm_num))).mul
      (odd_two_pow_pow_sub_one hf (by norm_num))) ?_
  rw [natCard_levi_of_ne_tu K hκ, natCard_statedSp_three_eq, hK]

theorem natCard_centralizer_yRep_tu [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (centralizer ({yRep K .tu} : Set (adjointGroup .F4 K))) =
      (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
  refine natCard_centralizer_yRep_eq_of_levi hf hK .tu (m := 4)
    ((odd_two_pow_pow_sub_one hf (by norm_num)).mul (odd_two_pow_pow_sub_one hf (by norm_num))) ?_
  rw [natCard_levi_tu K, natCard_statedSp_two_eq, hK]

theorem not_dvd_natCard_centralizer_yRep_tu {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁]
    [Finite K₂] [CharP K₁ 2] [CharP K₂ 2] {f : ℕ} (hf : 1 ≤ f) (hK₁ : Nat.card K₁ = 2 ^ f)
    (hK₂ : Nat.card K₂ = 2 ^ f) {κ : TwoCentral} (hκ : κ ≠ .tu) :
    ¬ Nat.card (centralizer ({yRep K₁ κ} : Set (adjointGroup .F4 K₁))) ∣
      Nat.card (centralizer ({yRep K₂ .tu} : Set (adjointGroup .F4 K₂))) := by
  rw [natCard_centralizer_yRep_of_ne_tu hf hK₁ hκ, natCard_centralizer_yRep_tu hf hK₂]
  intro h
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h0 : 0 < (2 ^ f) ^ 24 := by positivity
  have hA : 0 < ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) := by
    have h2 : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have h4 : 1 < (2 ^ f) ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have h' := Nat.dvd_of_mul_dvd_mul_left h0 h
  have h'' : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1) ∣
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * 1 := by rwa [mul_one]
  have h1 := Nat.dvd_of_mul_dvd_mul_left hA h''
  have h6 : 64 ≤ (2 ^ f) ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ (2 ^ f) ^ 6 := Nat.pow_le_pow_left hq 6
  have := Nat.le_of_dvd one_pos h1
  omega

end Orders

section Toral

open ClassReps

theorem mem_map_conj_iff' {G : Type*} [Group G] {P : Subgroup G} {g y : G} :
    y ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ P := by
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact hz
  · intro h
    exact ⟨_, h, by group⟩

theorem conj_inv_mem_normalizer_of_mem_normalizer_map {G : Type*} [Group G] {P : Subgroup G}
    {g s : G} (hs : s ∈ normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g⁻¹ * s * g ∈ normalizer (P : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  have h1 := (mem_normalizer_iff.1 hs) (g * h * g⁻¹)
  rw [mem_map_conj_iff', mem_map_conj_iff'] at h1
  have e1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  have e2 : g⁻¹ * (s * (g * h * g⁻¹) * s⁻¹) * g = (g⁻¹ * s * g) * h * (g⁻¹ * s * g)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem conj_mem_normalizer_map_of_mem_normalizer {G : Type*} [Group G] {P : Subgroup G}
    {g y : G} (hy : y ∈ normalizer (P : Set G)) :
    g * y * g⁻¹ ∈ normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  rw [mem_map_conj_iff', mem_map_conj_iff']
  have e : g⁻¹ * (g * y * g⁻¹ * z * (g * y * g⁻¹)⁻¹) * g = y * (g⁻¹ * z * g) * y⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hy _


variable {K : Type} [Field K]

theorem coe_mem_normalizer_posUnipotent_iff [Finite K] [CharP K 2] (y : adjointGroup .F4 K) :
    (y : ModGL .F4 K) ∈ normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) ↔
      y ∈ normalizer ((posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
  constructor
  · intro hy
    rw [mem_normalizer_iff]
    intro h
    rw [mem_posUnipotentSylow, mem_posUnipotentSylow]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mem_normalizer_iff.1 hy (h : ModGL .F4 K)
  · intro hy
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhC : h ∈ adjointGroup .F4 K := posUnipotent_le_adjointGroup hh
      have h1 := (mem_normalizer_iff.1 hy ⟨h, hhC⟩).1 (mem_posUnipotentSylow.2 hh)
      rw [mem_posUnipotentSylow] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · intro hh
      have hC : (y : ModGL .F4 K) * h * (y : ModGL .F4 K)⁻¹ ∈ adjointGroup .F4 K :=
        posUnipotent_le_adjointGroup hh
      have hhC : h ∈ adjointGroup .F4 K := by
        have e : h = (y : ModGL .F4 K)⁻¹ * ((y : ModGL .F4 K) * h * (y : ModGL .F4 K)⁻¹) * y := by
          group
        rw [e]
        exact mul_mem (mul_mem (inv_mem y.2) hC) y.2
      have h1 := (mem_normalizer_iff.1 hy ⟨h, hhC⟩).2 (mem_posUnipotentSylow.2
        (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hh))
      exact mem_posUnipotentSylow.1 h1

theorem mem_kerTorus_of_mem_torusGroup_of_commute {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {a : K} (ha : a ≠ 0) {h : ModGL .F4 K} (hh : h ∈ torusGroup .F4 K)
    (hc : h * pinnedX .F4 K γ a = pinnedX .F4 K γ a * h) : h ∈ kerTorus K γ := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  refine ⟨b, ?_, rfl⟩
  have h1 := rootDiagUnit_conj_pinnedX b hγ a
  rw [hc, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective .F4 K γ h1
  apply Units.ext
  have h3 : ((rootChar b γ : Kˣ) : K) * a = 1 * a := by rw [one_mul]; exact h2.symm
  exact mul_right_cancel₀ ha h3

theorem kerTorus_le_normalizer_posUnipotent (γ : Fin (Tag.rank .F4) → ℤ) :
    kerTorus K γ ≤ normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) := by
  rintro _ ⟨b, -, rfl⟩
  exact torusGroup_le_normalizer_posUnipotent
    (E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup b (f4RootDiagUnit_mem_adjointGroup b))

theorem exists_conj_pinnedX_of_mem_centralizer_sylow [Finite K] [CharP K 2]
    (U : Sylow 2 (adjointGroup .F4 K)) {x : adjointGroup .F4 K}
    (hx : x ∈ centralizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)))
    (hx1 : x ≠ 1) (htu : ∀ c : adjointGroup .F4 K, c * x * c⁻¹ ≠ yRep K .tu) :
    ∃ (g : adjointGroup .F4 K) (γ : Fin (Tag.rank .F4) → ℤ) (a : K), (γ = rootR ∨ γ = rootS) ∧
      a ≠ 0 ∧ (U : Subgroup (adjointGroup .F4 K)) =
        (posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)).map
          (MulAut.conj g).toMonoidHom ∧
      ((g⁻¹ * x * g : adjointGroup .F4 K) : ModGL .F4 K) = pinnedX .F4 K γ a := by
  obtain ⟨g, hU, c, d, hcd⟩ := exists_conj_eq_f4x_44_mul_f4x_47_of_mem_centralizer U hx
  obtain ⟨h47, h44⟩ := orbitCertRoot_47_44
  by_cases hc : c = 0
  · by_cases hd : d = 0
    · exfalso
      apply hx1
      have h1 : g⁻¹ * x * g = 1 := Subtype.ext (by rw [hcd, hc, hd, f4x_zero, f4x_zero, mul_one]; rfl)
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · refine ⟨g, rootR, d, Or.inl rfl, hd, hU, ?_⟩
      rw [hcd, hc, f4x_zero, one_mul, f4x, h47]
  · by_cases hd : d = 0
    · refine ⟨g, rootS, c, Or.inr rfl, hc, hU, ?_⟩
      rw [hcd, hd, f4x_zero, mul_one, f4x, h44]
    · exfalso
      obtain ⟨b, hb47, hb44⟩ := exists_rootChar_eq (K := K) (Units.mk0 d hd)⁻¹ (Units.mk0 c hc)⁻¹
      set h : adjointGroup .F4 K := ⟨rootDiagUnit .F4 b, f4RootDiagUnit_mem_adjointGroup b⟩
      obtain ⟨-, -, hTU, -⟩ := weylEltC_conj_frame (K := K)
      set n := weylEltC K weylWordT
      have hframe : h * (g⁻¹ * x * g) * h⁻¹ = frameTU K := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcd ⊢
        rw [hcd]
        change rootDiagUnit .F4 b * (f4x K 44 c * f4x K 47 d) * (rootDiagUnit .F4 b)⁻¹ =
          f4x K 47 1 * f4x K 44 1
        rw [rootDiagUnit_conj_f4x_44_mul_f4x_47, hb47, hb44, Units.val_inv_eq_inv_val,
          Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, inv_mul_cancel₀ hc,
          inv_mul_cancel₀ hd]
        exact (f4x_central (Or.inl rfl) 1 (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ 1)).symm
      apply htu (n * h * g⁻¹)
      rw [← hTU, ← hframe]
      group

theorem map_subtype_posUnipotentSylow [Finite K] [CharP K 2] :
    (posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)).map
      (adjointGroup .F4 K).subtype = posUnipotent .F4 K := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_posUnipotentSylow.1 hy
  · intro hg
    exact ⟨⟨g, posUnipotent_le_adjointGroup hg⟩, mem_posUnipotentSylow.2 hg, rfl⟩

theorem exists_conj_leviTorus_of_mem_centralizer_sylow [Finite K] [CharP K 2]
    (U : Sylow 2 (adjointGroup .F4 K)) {x : adjointGroup .F4 K}
    (hx : x ∈ centralizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)))
    (hx1 : x ≠ 1) (htu : ∀ c : adjointGroup .F4 K, c * x * c⁻¹ ≠ yRep K .tu)
    {S : Subgroup (adjointGroup .F4 K)}
    (hSU : S ≤ normalizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)))
    (hSx : S ≤ centralizer ({x} : Set (adjointGroup .F4 K))) (hS : Odd (Nat.card S)) :
    ∃ (c : adjointGroup .F4 K) (i : Fin (Tag.rank .F4)) (a : K), (i = 1 ∨ i = 2) ∧ a ≠ 0 ∧
      ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) = pinnedX .F4 K (Pi.single i 1) a ∧
      (∀ s ∈ S, ((c * s * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ leviTorus K {i}) ∧
      ∀ d : adjointGroup .F4 K, (d : ModGL .F4 K) ∈ leviTorus K {i} →
        c⁻¹ * d * c ∈
          normalizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : Finite (ModGL .F4 K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, γ, a, hγ, ha, hU, hgx⟩ := exists_conj_pinnedX_of_mem_centralizer_sylow U hx hx1 htu
  have hγR : IsRoot .F4 γ := by
    rcases hγ with rfl | rfl
    exacts [isRoot_rootR, isRoot_rootS]
  have hcent : ∀ u ∈ posUnipotent .F4 K, u * pinnedX .F4 K γ a = pinnedX .F4 K γ a * u := by
    intro u hu
    obtain ⟨h47, h44⟩ := orbitCertRoot_47_44
    rcases hγ with rfl | rfl
    · have h := f4x_central (Or.inr rfl) a hu
      rwa [f4x, h47] at h
    · have h := f4x_central (Or.inl rfl) a hu
      rwa [f4x, h44] at h
  set S₀ : Subgroup (ModGL .F4 K) :=
    (S.map (MulAut.conj g⁻¹).toMonoidHom).map (adjointGroup .F4 K).subtype with hS₀
  have hS₀B : S₀ ≤ torusGroup .F4 K ⊔ posUnipotent .F4 K := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hsU : s ∈ normalizer (((posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)).map
        (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) :=
      hU ▸ hSU hs
    have hsN := conj_inv_mem_normalizer_of_mem_normalizer_map hsU
    have hmem : ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) ∈
        adjointGroup .F4 K ⊓ normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) :=
      ⟨(g⁻¹ * s * g).2, (coe_mem_normalizer_posUnipotent_iff _).2 hsN⟩
    rw [(borel_self_normalizers .F4 K).1] at hmem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
      borelGroup] using hmem
  have hUp : IsPGroup 2 (posUnipotent .F4 K) := by
    rw [← map_subtype_posUnipotentSylow]
    exact (posUnipotentSylow (K := K)).isPGroup'.map _
  have hcop : Nat.Coprime 2 (Nat.card S₀) := by
    rw [hS₀, card_map_of_injective (subtype_injective _),
      card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact Nat.coprime_two_left.2 hS
  obtain ⟨u, hu, huS⟩ := exists_mem_map_conj_le_of_le_sup hUp torusGroup_le_normalizer_posUnipotent
    (by rw [inf_comm]; exact torusGroup_inf_posUnipotent) hS₀B hcop
  have hux : u * pinnedX .F4 K γ a * u⁻¹ = pinnedX .F4 K γ a := by
    rw [hcent u hu, mul_inv_cancel_right]
  have hker : ∀ s ∈ S, u * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * u⁻¹ ∈
      kerTorus K γ := by
    intro s hs
    have hT : u * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * u⁻¹ ∈ torusGroup .F4 K := by
      refine huS ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, inv_inv,
        Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_kerTorus_of_mem_torusGroup_of_commute hγR ha hT ?_
    have hsx : s * x = x * s := mem_centralizer_singleton_iff.1 (hSx hs)
    have hsx' : ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * pinnedX .F4 K γ a =
        pinnedX .F4 K γ a * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) := by
      rw [← hgx, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      congr 1
      calc g⁻¹ * s * g * (g⁻¹ * x * g) = g⁻¹ * (s * x) * g := by group
        _ = g⁻¹ * (x * s) * g := by rw [hsx]
        _ = g⁻¹ * x * g * (g⁻¹ * s * g) := by group
    calc u * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * u⁻¹ * pinnedX .F4 K γ a =
          u * (((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) *
            (u⁻¹ * pinnedX .F4 K γ a * u)) * u⁻¹ := by group
      _ = u * (((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * pinnedX .F4 K γ a) * u⁻¹ := by
          rw [show u⁻¹ * pinnedX .F4 K γ a * u = pinnedX .F4 K γ a by
            rw [mul_assoc, ← hcent u hu, inv_mul_cancel_left]]
      _ = u * (pinnedX .F4 K γ a * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K)) * u⁻¹ := by
          rw [hsx']
      _ = (u * pinnedX .F4 K γ a * u⁻¹) * (u * ((g⁻¹ * s * g : adjointGroup .F4 K) :
            ModGL .F4 K) * u⁻¹) := by group
      _ = pinnedX .F4 K γ a * (u * ((g⁻¹ * s * g : adjointGroup .F4 K) : ModGL .F4 K) * u⁻¹) := by
          rw [hux]
  obtain ⟨w, i, hi, hwγ, hnC, hTw, -, -⟩ := exists_weyl_kerTorus (K := K) hγR
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  have hnx := canonicalRep_mul_pinnedX_mul_inv_eq_single h2 hγR hwγ a
  set c : adjointGroup .F4 K :=
    ⟨n, hnC⟩ * ⟨u, posUnipotent_le_adjointGroup hu⟩ * g⁻¹ with hc
  have hcoe : ∀ y : adjointGroup .F4 K, ((c * y * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) =
      n * (u * ((g⁻¹ * y * g : adjointGroup .F4 K) : ModGL .F4 K) * u⁻¹) * n⁻¹ := by
    intro y
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    group
  refine ⟨c, i, a, ?_, ha, ?_, ?_, ?_⟩
  · rcases hi with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [Or.inl rfl, Or.inr rfl]
  · rw [hcoe, hgx, hux, hnx]
  · intro s hs
    rw [hcoe, ← hTw]
    exact ⟨_, hker s hs, rfl⟩
  · intro d hd
    rw [← hTw] at hd
    obtain ⟨k, hk, hkd⟩ := hd
    have hkd' : n * k * n⁻¹ = d := hkd
    have hkC : k ∈ adjointGroup .F4 K := by
      have e : k = n⁻¹ * d * n := by rw [← hkd']; group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hnC) d.2) hnC
    set y : adjointGroup .F4 K := (⟨u, posUnipotent_le_adjointGroup hu⟩ : adjointGroup .F4 K)⁻¹ *
      ⟨k, hkC⟩ * ⟨u, posUnipotent_le_adjointGroup hu⟩ with hy
    have hyN : (y : ModGL .F4 K) ∈ normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) := by
      simp only [hy, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (mul_mem (inv_mem (le_normalizer hu)) (kerTorus_le_normalizer_posUnipotent γ hk))
        (le_normalizer hu)
    have hyN' := conj_mem_normalizer_map_of_mem_normalizer (g := g)
      ((coe_mem_normalizer_posUnipotent_iff y).1 hyN)
    rw [← hU] at hyN'
    have e : c⁻¹ * d * c = g * y * g⁻¹ := by
      apply Subtype.ext
      simp only [hc, hy, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      rw [← hkd']
      group
    rw [e]
    exact hyN'

end Toral

end CFSG.SeitzReduction.F4Pilot

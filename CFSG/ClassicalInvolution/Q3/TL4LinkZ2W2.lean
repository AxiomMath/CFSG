module

public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.AschTight.S1916Help
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W0

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Helpers

variable {G : Type} [Group G]

private theorem conj_inv_eq_of_conj_eq {x a b : G} (h : x * a * x⁻¹ = b) : x⁻¹ * b * x = a := by
  rw [← h]
  group

private theorem exists_swap_of_sylow [Finite G] (P : Sylow 2 G) {t u g : G}
    (hP : ∀ x ∈ (P : Subgroup G),
      (x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u) ∨ (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t))
    (hgt : g * t * g⁻¹ = u) (hgu : g * u * g⁻¹ = t) :
    ∃ b ∈ (P : Subgroup G), b * t * b⁻¹ = u := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, ∀ x, x ∈ H ↔
      ((x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u) ∨ (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t)) := by
    refine ⟨{ carrier := {x | (x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u) ∨
                (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t)}
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      have ea : ∀ w : G, a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := fun w => by group
      rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · exact Or.inl ⟨by rw [ea, hb1, ha1], by rw [ea, hb2, ha2]⟩
      · exact Or.inr ⟨by rw [ea, hb1, ha2], by rw [ea, hb2, ha1]⟩
      · exact Or.inr ⟨by rw [ea, hb1, ha1], by rw [ea, hb2, ha2]⟩
      · exact Or.inl ⟨by rw [ea, hb1, ha2], by rw [ea, hb2, ha1]⟩
    · exact Or.inl ⟨by group, by group⟩
    · intro x hx
      have hx' : (x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u) ∨ (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t) := hx
      show (x⁻¹ * t * x⁻¹⁻¹ = t ∧ x⁻¹ * u * x⁻¹⁻¹ = u) ∨
        (x⁻¹ * t * x⁻¹⁻¹ = u ∧ x⁻¹ * u * x⁻¹⁻¹ = t)
      rw [inv_inv]
      rcases hx' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨conj_inv_eq_of_conj_eq h1, conj_inv_eq_of_conj_eq h2⟩
      · exact Or.inr ⟨conj_inv_eq_of_conj_eq h2, conj_inv_eq_of_conj_eq h1⟩
  have hg2 : g * g ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · have e : g * g * t * (g * g)⁻¹ = t := by
        calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
          _ = t := by rw [hgt, hgu]
      exact mul_inv_eq_iff_eq_mul.mp e
    · have e : g * g * u * (g * g)⁻¹ = u := by
        calc g * g * u * (g * g)⁻¹ = g * (g * u * g⁻¹) * g⁻¹ := by group
          _ = u := by rw [hgu, hgt]
      exact mul_inv_eq_iff_eq_mul.mp e
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  obtain ⟨k, hk⟩ := hm
  have hgm : g ^ m = (g * g) ^ k * g := by rw [hk, pow_succ, pow_mul, sq]
  have hc := Subgroup.pow_mem _ hg2 k
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff] at hc
  have hsw : g ^ m * t * (g ^ m)⁻¹ = u ∧ g ^ m * u * (g ^ m)⁻¹ = t := by
    rw [hgm]
    constructor
    · calc (g * g) ^ k * g * t * ((g * g) ^ k * g)⁻¹ =
            (g * g) ^ k * (g * t * g⁻¹) * ((g * g) ^ k)⁻¹ := by group
        _ = u := by rw [hgt, hc.2, mul_inv_cancel_right]
    · calc (g * g) ^ k * g * u * ((g * g) ^ k * g)⁻¹ =
            (g * g) ^ k * (g * u * g⁻¹) * ((g * g) ^ k)⁻¹ := by group
        _ = t := by rw [hgu, hc.1, mul_inv_cancel_right]
  have hm0 : m ≠ 0 := by omega
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers (g ^ m)) := by
    apply IsPGroup.of_card (n := a)
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 ⟨2 ^ a, by rw [hord, mul_comm]⟩, hord,
      Nat.mul_div_cancel _ (by omega)]
  have hgH : g ^ m ∈ H := (hH _).mpr (Or.inr hsw)
  have hPH : (P : Subgroup G) ≤ H := fun x hx => (hH x).mpr (hP x hx)
  have hPs : IsSylow2In (P : Subgroup G) H :=
    ⟨hPH, P.isPGroup', fun V _ hV2 hPV => P.is_maximal' hV2 hPV⟩
  obtain ⟨V, hV, hgV⟩ := IsSylow2In.exists_ge h2 (Subgroup.zpowers_le.mpr hgH)
  obtain ⟨h, hhH, hhV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hPs
  have hb : h * g ^ m * h⁻¹ ∈ (P : Subgroup G) := by
    rw [← hhV]
    exact conj_mem_conjSub (hgV (Subgroup.mem_zpowers _)) h
  refine ⟨h * g ^ m * h⁻¹, hb, ?_⟩
  have e : h * g ^ m * h⁻¹ * t * (h * g ^ m * h⁻¹)⁻¹ =
      h * (g ^ m * (h⁻¹ * t * h) * (g ^ m)⁻¹) * h⁻¹ := by group
  rw [e]
  rcases (hH h).mp hhH with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [conj_inv_eq_of_conj_eq h1, hsw.1, h2]
  · rw [conj_inv_eq_of_conj_eq h2, hsw.2, h1]

end Helpers

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem exists_adapted_sylow (hL : TightLargeHypR 3 n Y R S t)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hu : IsUniqueInvolution J u) :
    ∃ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) ∧
      R₀ ≤ Subgroup.centralizer ({u} : Set Y) ∧ IsSylow2In T₀ J ∧
      T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) ∧
      ∃ P : Sylow 2 Y, R₀ ≤ (P : Subgroup Y) ∧ T₀ ≤ (P : Subgroup Y) := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨hJΩ, -, T₀, hT₀R, hT₀J, hT₀N⟩ := id hJ
  have hT₀ : IsSylow2In T₀ J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT₀R hT₀J
  have hT₀u : T₀ ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
      (mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_self_of_mem (hT₀J hx)))
  obtain ⟨-, -, R₁, hR₁R, hR₁K, hR₁N⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJΩ hJ
  have hR₁ : IsSylow2In R₁ (tightCore R) := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hR₁R hR₁K
  have hR₁u : R₁ ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (hR₁N hx)
  have hT₀C : T₀ ≤ Subgroup.normalizer
      ((tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) : Set Y) := by
    intro x hx
    have h1 := Subgroup.mem_normalizer_iff.mp (hT₀N hx)
    have h2 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (H := Subgroup.centralizer ({u} : Set Y)) (hT₀u hx))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr (h1 y) (h2 y)
  have hMN : tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) ⊔ T₀ ≤ Subgroup.normalizer
      ((tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) : Set Y) :=
    sup_le Subgroup.le_normalizer hT₀C
  obtain ⟨Q, hQ, hT₀Q⟩ := IsSylow2In.exists_ge hT₀.2.1
    (le_sup_right : T₀ ≤ tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) ⊔ T₀)
  have hR₀ := isSylow2In_inf_of_le_normalizer hQ le_sup_left hMN
  refine ⟨Q ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)), T₀, ?_,
    inf_le_right.trans inf_le_right, hT₀, hT₀N, ?_⟩
  · exact hR₁.of_natCard_le hR₀.2.1 (inf_le_right.trans inf_le_left)
      (hR₀.natCard_le hR₁.2.1 (le_inf hR₁.1 hR₁u))
  · obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hQ.2.1
    exact ⟨P, inf_le_left.trans hP, hT₀Q.trans hP⟩

theorem Z2Set.exists_conj_u (hs : Z2Set n R S t J u R₀ T₀ P) : ∃ g : Y, g * t * g⁻¹ = u := by
  obtain ⟨g, hg⟩ := hs.hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have h1 := hs.large.datum.isUniqueInvolution_core.conj g
  rw [hg'] at h1
  exact ⟨g, (hs.hu.eq h1).symm⟩

private theorem Z2Set.ne_tu' (hs : Z2Set n R S t J u R₀ T₀ P) : t ≠ u := fun e =>
  hs.hJ.2.1 (eq_core_of_isUniqueInvolution hs.large hs.hJ.1 (e ▸ hs.hu))

private theorem Z2Set.ctu' (hs : Z2Set n R S t J u R₀ T₀ P) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hs.large.datum.hypOmegaGen
    hs.large.datum.isUniqueInvolution_core hs.hJ hs.hu

private theorem Z2Set.uniq_R₀ (hs : Z2Set n R S t J u R₀ T₀ P) : IsUniqueInvolution R₀ t :=
  AscL62.isUniqueInvolution_of_le hs.large.datum.isUniqueInvolution_core hs.hR₀.1
    (Sec6Gen.mem_of_isSylow2In hs.large.datum.isUniqueInvolution_core hs.hR₀)

private theorem Z2Set.uniq_T₀ (hs : Z2Set n R S t J u R₀ T₀ P) : IsUniqueInvolution T₀ u :=
  AscL62.isUniqueInvolution_of_le hs.hu hs.hT₀.1 (Sec6Gen.mem_of_isSylow2In hs.hu hs.hT₀)

private theorem Z2Set.inter_eq_one' (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y} (hyR : y ∈ R₀)
    (hyT : y ∈ T₀) : y = 1 := by
  have ht := hs.large.datum.isUniqueInvolution_core
  by_contra hy1
  have hR2 : IsPGroup 2 ↥(R₀ ⊓ T₀) := hs.hR₀.2.1.to_le inf_le_left
  have hne : R₀ ⊓ T₀ ≠ ⊥ := by
    intro e
    have hy : y ∈ R₀ ⊓ T₀ := ⟨hyR, hyT⟩
    rw [e] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hcard := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have htT : t ∈ R₀ ⊓ T₀ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup ht (inf_le_left.trans hs.hR₀.1) hR2 (by omega)
  exact hs.ne_tu' ((hs.uniq_T₀.unique t htT.2 ht.sq).resolve_left ht.ne_one)

theorem Z2Set.not_mem_omegaNbr_J (hs : Z2Set n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
  intro hLJ
  have hd := hs.large.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have h := TightLargeHypR.typeRFam hs.large
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL.1
  have cuv : u * v = v * u := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hu hLJ hv
  have nuv : u ≠ v := fun e => hLJ.2.1 (h.noTwins J hs.hJ.1 L ⟨hL.1, u, hs.hu, e ▸ hv⟩)
  have hKL := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hL.1 hL
  have hJL := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.hJ.1 hL.1 hLJ
  obtain ⟨Q, hQ, -, hQt, hQu⟩ :=
    exists_isSylow2In_member_le_centralizer hs.large hL.1 hv hKL hJL ht hs.hu hs.ne_tu' hs.ctu'
  have hQN : Q ≤ Subgroup.normalizer (J : Set Y) := hQu.trans (h.tight J hs.hJ.1 u hs.hu)
  have hne := secImg_ne h (xMem_of_mem_omegaNbr_core hs.large hs.hJ)
    (xMem_of_mem_omegaNbr_core hs.large hL) hs.hu hv cuv nuv
  have h1 := secImg_mem_omegaNbr (xMem_of_mem_omegaNbr_core hs.large hs.hJ)
    (xMem_of_mem_omegaNbr_core hs.large hL) hQ hQt hQN hne
  have h2 := omegaNbr_link_of_secFam hs.large hs.hJ hL h1
  exact hs.z2.2.2.1 _ (subgroupOf_mem_linkRestrict hs.hJ) _ (subgroupOf_mem_linkRestrict hL)
    (Or.inl h2)

theorem Z2Set.rSet_le (hs : Z2Set n R S t J u R₀ T₀ P) {R' : Subgroup Y}
    (hR' : R' ∈ RSet (CoreAssembly.conjClass (tightCore R))) (hR'P : R' ≤ (P : Subgroup Y)) :
    R' = R₀ ∨ R' = T₀ := by
  have hd := hs.large.datum
  have hΩ := hd.hypOmegaGen
  have h := TightLargeHypR.typeRFam hs.large
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne0, hne1⟩ := hcon
  have c0 := Q3CP.l67Gen Y _ hΩ P R' hR' R₀ (mem_RSet_of_isSylow2In hK hs.hR₀) hR'P hs.hR₀P hne0
  have c1 := Q3CP.l67Gen Y _ hΩ P R' hR' T₀ (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀) hR'P
    hs.hT₀P hne1
  have hR't : R' ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c0 x hx t hs.uniq_R₀.mem)
  have hR'u : R' ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c1 x hx u hs.uniq_T₀.mem)
  obtain ⟨L, hLΩ, hR'L⟩ := exists_isSylow2In_of_mem_RSet hR'
  by_cases hLK : L = tightCore R
  · rw [hLK] at hR'L
    exact hne0 (Q3CP.eq_of_isSylow2In_of_le_sylow' hR'L hs.hR₀ hR'P hs.hR₀P)
  by_cases hLJ : L = J
  · rw [hLJ] at hR'L
    exact hne1 (Q3CP.eq_of_isSylow2In_of_le_sylow' hR'L hs.hT₀ hR'P hs.hT₀P)
  exact hs.not_mem_omegaNbr_J ⟨hLΩ, hLK, R', hR', hR'L.1, hR't.trans hd.le_normalizer_core⟩
    ⟨hLΩ, hLJ, R', hR', hR'L.1, hR'u.trans (h.tight J hs.hJ.1 u hs.hu)⟩

private theorem Z2Set.conjSub_R₀_cases (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) : conjSub x R₀ = R₀ ∨ conjSub x R₀ = T₀ :=
  hs.rSet_le (RSet.conj hs.large.datum.hypOmegaGen.conjInvariant
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hs.hR₀) x)
    ((conjSub_mono (n := x) hs.hR₀P).trans (conjSub_eq_self_of_mem hx).le)

private theorem Z2Set.conjSub_T₀_cases (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) : conjSub x T₀ = R₀ ∨ conjSub x T₀ = T₀ :=
  hs.rSet_le (RSet.conj hs.large.datum.hypOmegaGen.conjInvariant
    (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀) x)
    ((conjSub_mono (n := x) hs.hT₀P).trans (conjSub_eq_self_of_mem hx).le)

theorem Z2Set.perm (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y} (hx : x ∈ (P : Subgroup Y)) :
    (x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u) ∨ (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t) := by
  have i0 := hs.uniq_R₀.conj x
  have i1 := hs.uniq_T₀.conj x
  have hinj : x * t * x⁻¹ = x * u * x⁻¹ → False := fun e => hs.ne_tu' (by simpa using e)
  rcases hs.conjSub_R₀_cases hx with e0 | e0 <;> rcases hs.conjSub_T₀_cases hx with e1 | e1 <;>
    rw [e0] at i0 <;> rw [e1] at i1
  · exact absurd ((i0.eq hs.uniq_R₀).trans (i1.eq hs.uniq_R₀).symm) hinj
  · exact Or.inl ⟨i0.eq hs.uniq_R₀, i1.eq hs.uniq_T₀⟩
  · exact Or.inr ⟨i0.eq hs.uniq_T₀, i1.eq hs.uniq_R₀⟩
  · exact absurd ((i0.eq hs.uniq_T₀).trans (i1.eq hs.uniq_T₀).symm) hinj

private theorem Z2Set.perm' (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y} (hx : x ∈ (P : Subgroup Y)) :
    (x * t * x⁻¹ = t ∧ x * u * x⁻¹ = u ∧ x⁻¹ * t * x = t ∧ x⁻¹ * u * x = u) ∨
      (x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t ∧ x⁻¹ * t * x = u ∧ x⁻¹ * u * x = t) := by
  rcases hs.perm hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, conj_inv_eq_of_conj_eq h1, conj_inv_eq_of_conj_eq h2⟩
  · exact Or.inr ⟨h1, h2, conj_inv_eq_of_conj_eq h2, conj_inv_eq_of_conj_eq h1⟩

theorem Z2Set.mem_edgeCent_iff (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y} :
    x ∈ edgeCent (P : Subgroup Y) t u ↔ x ∈ (P : Subgroup Y) ∧ x * t * x⁻¹ = t := by
  simp only [edgeCent, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hxt⟩, -⟩
    exact ⟨hx, by rw [hxt, mul_inv_cancel_right]⟩
  · rintro ⟨hx, hxt⟩
    rcases hs.perm hx with ⟨-, hxu⟩ | ⟨hxt', -⟩
    · exact ⟨⟨hx, mul_inv_eq_iff_eq_mul.mp hxt⟩, mul_inv_eq_iff_eq_mul.mp hxu⟩
    · exact absurd (hxt.symm.trans hxt') hs.ne_tu'

theorem Z2Set.commutator_mem (hs : Z2Set n R S t J u R₀ T₀ P) {y z : Y}
    (hy : y ∈ (P : Subgroup Y)) (hz : z ∈ (P : Subgroup Y)) :
    y * z * y⁻¹ * z⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
  rw [hs.mem_edgeCent_iff]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hz)
    (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hz), ?_⟩
  have e : y * z * y⁻¹ * z⁻¹ * t * (y * z * y⁻¹ * z⁻¹)⁻¹ =
      y * (z * (y⁻¹ * (z⁻¹ * t * z) * y) * z⁻¹) * y⁻¹ := by group
  rw [e]
  rcases hs.perm' hy with ⟨hy1, hy2, hy3, hy4⟩ | ⟨hy1, hy2, hy3, hy4⟩ <;>
    rcases hs.perm' hz with ⟨hz1, hz2, hz3, hz4⟩ | ⟨hz1, hz2, hz3, hz4⟩
  · rw [hz3, hy3, hz1, hy1]
  · rw [hz3, hy4, hz2, hy1]
  · rw [hz3, hy3, hz2, hy2]
  · rw [hz3, hy4, hz1, hy2]

theorem Z2Set.conj_mem_edgeCent (hs : Z2Set n R S t J u R₀ T₀ P) {y q : Y}
    (hy : y ∈ (P : Subgroup Y)) (hq : q ∈ edgeCent (P : Subgroup Y) t u) :
    y * q * y⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
  have hqu : q * u * q⁻¹ = u := by
    have h1 := (Subgroup.mem_inf.mp hq).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  obtain ⟨hqP, hqt⟩ := hs.mem_edgeCent_iff.mp hq
  rw [hs.mem_edgeCent_iff]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hqP) (Subgroup.inv_mem _ hy), ?_⟩
  have e : y * q * y⁻¹ * t * (y * q * y⁻¹)⁻¹ = y * (q * (y⁻¹ * t * y) * q⁻¹) * y⁻¹ := by group
  rw [e]
  rcases hs.perm' hy with ⟨hy1, -, hy3, -⟩ | ⟨-, hy2, hy3, -⟩
  · rw [hy3, hqt, hy1]
  · rw [hy3, hqu, hy2]

theorem Z2Set.comm_tu (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y} (hy : y ∈ (P : Subgroup Y)) :
    y * (t * u) = t * u * y := by
  rcases hs.perm hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc y * (t * u) = (y * t * y⁻¹) * (y * u * y⁻¹) * y := by group
      _ = t * u * y := by rw [h1, h2]
  · calc y * (t * u) = (y * t * y⁻¹) * (y * u * y⁻¹) * y := by group
      _ = u * t * y := by rw [h1, h2]
      _ = t * u * y := by rw [hs.ctu']

private theorem exists_centralizer_conj_of_linkTrans (hL : TightLargeHypR 3 n Y R S t)
    (htr : LinkTrans R t) {J L : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hL' : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c J = L := by
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hJ) _
    (subgroupOf_mem_linkRestrict (t := t) hL')
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hL')] at h1
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
    (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  rw [← hy, conjSub_secImg] at h1
  have hyt : (y : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer y.2
  have hJy := conjSub_mem_omegaNbr_core hL hJ hyt
  obtain ⟨ν, -, hνL⟩ := exists_conj_of_secImg_eq (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJy) (xMem_of_mem_omegaNbr_core hL hL') h1
  refine ⟨(ν : Y) * y, Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hyt, ?_⟩
  rw [conjSub_mul]
  exact hνL.symm

theorem Z2Set.exists_swap (hs : Z2Set n R S t J u R₀ T₀ P) :
    ∃ b ∈ (P : Subgroup Y), b * t * b⁻¹ = u := by
  have hd := hs.large.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨g₁, hg₁⟩ := hs.hJ.1
  have hg₁' : conjSub g₁ (tightCore R) = J := hg₁
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hs.hJ.1 hs.hJ
  have hJ' : conjSub g₁⁻¹ (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hKJ g₁⁻¹
    rwa [← hg₁', conjSub_inv_conjSub] at h1
  obtain ⟨c, hc, hcJ⟩ := exists_centralizer_conj_of_linkTrans hs.large hs.z2.1 hs.hJ hJ'
  have e1 : conjSub (g₁ * c) (tightCore R) = J := by
    rw [conjSub_mul, conjSub_core_of_mem_centralizer hs.large hc, hg₁']
  have e2 : conjSub (g₁ * c) J = tightCore R := by
    rw [conjSub_mul, hcJ, conjSub_conjSub_inv]
  have hgt : g₁ * c * t * (g₁ * c)⁻¹ = u := by
    have h1 := ht.conj (g₁ * c)
    rw [e1] at h1
    exact h1.eq hs.hu
  have hgu : g₁ * c * u * (g₁ * c)⁻¹ = t := by
    have h1 := hs.hu.conj (g₁ * c)
    rw [e2] at h1
    exact h1.eq ht
  exact exists_swap_of_sylow P (fun x hx => hs.perm hx) hgt hgu

theorem Z2Set.mem_or_mem_of_swap (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) {x : Y} (hx : x ∈ (P : Subgroup Y)) :
    x ∈ edgeCent (P : Subgroup Y) t u ∨ b⁻¹ * x ∈ edgeCent (P : Subgroup Y) t u := by
  rw [hs.mem_edgeCent_iff, hs.mem_edgeCent_iff]
  rcases hs.perm hx with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl ⟨hx, h1⟩
  · refine Or.inr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hbP) hx, ?_⟩
    calc b⁻¹ * x * t * (b⁻¹ * x)⁻¹ = b⁻¹ * (x * t * x⁻¹) * b := by group
      _ = t := by rw [h1, conj_inv_eq_of_conj_eq hbt]

theorem Z2Set.tu_not_conj (hs : Z2Set n R S t J u R₀ T₀ P) (g : Y) : g * (t * u) * g⁻¹ ≠ t := by
  intro hg
  have ht := hs.large.datum.isUniqueInvolution_core
  have h := TightLargeHypR.typeRFam hs.large
  have hM : conjSub g⁻¹ (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g⁻¹, rfl⟩
  have hMtu : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) (t * u) := by
    have h1 := ht.conj g⁻¹
    have e : g⁻¹ * t * g⁻¹⁻¹ = t * u := by
      calc g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * (g * (t * u) * g⁻¹) * g := by rw [hg, inv_inv]
        _ = t * u := by group
    rwa [e] at h1
  have hPN : (P : Subgroup Y) ≤ Subgroup.normalizer (conjSub g⁻¹ (tightCore R) : Set Y) :=
    fun y hy => h.tight _ hM (t * u) hMtu
      (Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_tu hy))
  have hsyl := Hall196.isSylow2In_inf_of_le_normalizer P hPN
  have h1 := AscL62.isUniqueInvolution_of_le hMtu hsyl.1 (Sec6Gen.mem_of_isSylow2In hMtu hsyl)
  rcases hs.rSet_le (mem_RSet_of_isSylow2In hM hsyl) inf_le_left with e | e
  · rw [e] at h1
    exact hs.hu.ne_one (by simpa using h1.eq hs.uniq_R₀)
  · rw [e] at h1
    exact ht.ne_one (by simpa using h1.eq hs.uniq_T₀)

private theorem Z2Set.conjSub_R₀_eq (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) (hxt : x * t * x⁻¹ = t) : conjSub x R₀ = R₀ := by
  rcases hs.conjSub_R₀_cases hx with e | e
  · exact e
  · have h1 := hs.uniq_R₀.conj x
    rw [e, hxt] at h1
    exact absurd (h1.eq hs.uniq_T₀) hs.ne_tu'

private theorem Z2Set.conjSub_T₀_eq (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) (hxu : x * u * x⁻¹ = u) : conjSub x T₀ = T₀ := by
  rcases hs.conjSub_T₀_cases hx with e | e
  · have h1 := hs.uniq_T₀.conj x
    rw [e, hxu] at h1
    exact absurd (h1.eq hs.uniq_R₀).symm hs.ne_tu'
  · exact e

private theorem Z2Set.conjSub_R₀_swap (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) (hxt : x * t * x⁻¹ = u) : conjSub x R₀ = T₀ := by
  rcases hs.conjSub_R₀_cases hx with e | e
  · have h1 := hs.uniq_R₀.conj x
    rw [e, hxt] at h1
    exact absurd (h1.eq hs.uniq_R₀).symm hs.ne_tu'
  · exact e

private theorem Z2Set.eq_tu_of_centralizer_aux (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) (hbu : b * u * b⁻¹ = t)
    (hb2 : b * b = 1) {w : Y} (hwP : w ∈ (P : Subgroup Y)) (hwt : w * t * w⁻¹ = t)
    (hwb : w * b = b * w) (hwc : ∀ y ∈ (P : Subgroup Y), y * b = b * y → w * y = y * w)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) : w = t * u := by
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hwu : w * u * w⁻¹ = u := by
    rcases hs.perm hwP with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (hwt.symm.trans h1) hs.ne_tu'
  have hwR := hs.conjSub_R₀_eq hwP hwt
  have hwT := hs.conjSub_T₀_eq hwP hwu
  have hbR := hs.conjSub_R₀_swap hbP hbt
  have hRT : R₀ ≠ T₀ := fun e => hs.ne_tu' (hs.uniq_R₀.eq (e ▸ hs.uniq_T₀))
  have hcomm : Commutes R₀ T₀ := Q3CP.l67Gen Y _ hΩ P R₀ (mem_RSet_of_isSylow2In hK hs.hR₀) T₀
    (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀) hs.hR₀P hs.hT₀P hRT
  have hfix : ∀ x ∈ R₀, w * x * w⁻¹ = x ∧ w * (b * x * b⁻¹) * w⁻¹ = b * x * b⁻¹ := by
    intro x hx
    have hy : b * x * b⁻¹ ∈ T₀ := by
      rw [← hbR]
      exact conj_mem_conjSub hx b
    have hdP : x * (b * x * b⁻¹) ∈ (P : Subgroup Y) :=
      Subgroup.mul_mem _ (hs.hR₀P hx) (hs.hT₀P hy)
    have hdb : x * (b * x * b⁻¹) * b = b * (x * (b * x * b⁻¹)) := by
      have h1 : b * (x * (b * x * b⁻¹)) * b⁻¹ = x * (b * x * b⁻¹) := by
        calc b * (x * (b * x * b⁻¹)) * b⁻¹ = (b * x * b⁻¹) * ((b * b) * x * (b * b)⁻¹) := by
              group
          _ = (b * x * b⁻¹) * x := by rw [hb2]; group
          _ = x * (b * x * b⁻¹) := (hcomm x hx _ hy).symm
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hwd := hwc _ hdP hdb
    have hx' : w * x * w⁻¹ ∈ R₀ := by
      rw [← hwR]
      exact conj_mem_conjSub hx w
    have hy' : w * (b * x * b⁻¹) * w⁻¹ ∈ T₀ := by
      rw [← hwT]
      exact conj_mem_conjSub hy w
    have he : (w * x * w⁻¹) * (w * (b * x * b⁻¹) * w⁻¹) = x * (b * x * b⁻¹) := by
      calc (w * x * w⁻¹) * (w * (b * x * b⁻¹) * w⁻¹) = w * (x * (b * x * b⁻¹)) * w⁻¹ := by
            group
        _ = x * (b * x * b⁻¹) := by rw [hwd, mul_inv_cancel_right]
    have hm1 : x⁻¹ * (w * x * w⁻¹) = (b * x * b⁻¹) * (w * (b * x * b⁻¹) * w⁻¹)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
      exact he
    have h1 : x⁻¹ * (w * x * w⁻¹) = 1 := by
      refine hs.inter_eq_one' (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hx') ?_
      rw [hm1]
      exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hy')
    have h2 : (b * x * b⁻¹) * (w * (b * x * b⁻¹) * w⁻¹)⁻¹ = 1 := hm1 ▸ h1
    exact ⟨(inv_mul_eq_one.mp h1).symm, (mul_inv_eq_one.mp h2).symm⟩
  have hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hfix x hx).1).symm
  have hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y) := by
    intro y hy
    have hy' : b⁻¹ * y * b ∈ R₀ := by
      rw [← hbR] at hy
      exact mem_conjSub_iff.mp hy
    have h1 := (hfix _ hy').2
    have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
    rw [e] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hwE : w ∈ Subgroup.closure ({t, u} : Set Y) := by
    by_contra hwE
    exact hs.noA1 ⟨w, hw2, mul_inv_eq_iff_eq_mul.mp hwt, mul_inv_eq_iff_eq_mul.mp hwu, hwE,
      hR₀w, hT₀w⟩
  rcases T3CII.closure_pair_cases ht.sq hs.hu.sq hs.ctu' hwE with h | h | h | h
  · exact absurd h hw1
  · exfalso
    rw [h] at hwb
    have e : b * t * b⁻¹ = t := by rw [← hwb, mul_inv_cancel_right]
    exact hs.ne_tu' (e.symm.trans hbt)
  · exfalso
    rw [h] at hwb
    have e : b * u * b⁻¹ = u := by rw [← hwb, mul_inv_cancel_right]
    exact hs.ne_tu' (e.symm.trans hbu).symm
  · exact h

theorem Z2Set.eq_of_center_centralizer (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u) (hb2 : b * b = 1)
    {z : Y} (hzP : z ∈ (P : Subgroup Y)) (hzb : z * b = b * z)
    (hzc : ∀ y ∈ (P : Subgroup Y), y * b = b * y → z * y = y * z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : z = t * u ∨ z = b ∨ z = t * u * b := by
  obtain ⟨hbt, hbu⟩ : b * t * b⁻¹ = u ∧ b * u * b⁻¹ = t := by
    rcases hs.perm hbP with ⟨h1, -⟩ | h
    · exact absurd (hs.mem_edgeCent_iff.mpr ⟨hbP, h1⟩) hbA
    · exact h
  by_cases hzt : z * t * z⁻¹ = t
  · exact Or.inl (hs.eq_tu_of_centralizer_aux hbP hbt hbu hb2 hzP hzt hzb hzc hz2 hz1)
  have hzu : z * u * z⁻¹ = t := by
    rcases hs.perm hzP with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hzt
    · exact h2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  by_cases hzb1 : z * b = 1
  · refine Or.inr (Or.inl ?_)
    calc z = z * b * b⁻¹ := by group
      _ = b := by rw [hzb1, one_mul, hbinv]
  refine Or.inr (Or.inr ?_)
  have hw := hs.eq_tu_of_centralizer_aux hbP hbt hbu hb2 (Subgroup.mul_mem _ hzP hbP)
    (by
      calc z * b * t * (z * b)⁻¹ = z * (b * t * b⁻¹) * z⁻¹ := by group
        _ = t := by rw [hbt, hzu])
    (by
      calc z * b * b = b * z * b := by rw [hzb]
        _ = b * (z * b) := mul_assoc _ _ _)
    (fun y hy hyb => by
      calc z * b * y = z * (b * y) := by rw [mul_assoc]
        _ = z * (y * b) := by rw [hyb]
        _ = z * y * b := by rw [mul_assoc]
        _ = y * z * b := by rw [hzc y hy hyb]
        _ = y * (z * b) := by rw [mul_assoc])
    (by
      calc z * b * (z * b) = z * (b * z) * b := by group
        _ = z * (z * b) * b := by rw [hzb]
        _ = (z * z) * (b * b) := by group
        _ = 1 := by rw [hz2, hb2, one_mul])
    hzb1
  calc z = z * b * b⁻¹ := by group
    _ = t * u * b := by rw [hw, hbinv]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W

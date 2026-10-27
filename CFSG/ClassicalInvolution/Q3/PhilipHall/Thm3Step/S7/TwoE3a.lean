module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
import CFSG.Goldschmidt.Steps.Rank2List

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement MatrixGroups

@[expose] def L2CentDihedral : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → Even f →
    CFSG.Blueprint.LieModel X .PSL 2 p f → ∀ z : X, orderOf z = 2 →
      ∃ C : Subgroup X, IsCyclic ↥C ∧ z ∈ C ∧
        ∀ x ∈ Subgroup.centralizer ({z} : Set X), x ∉ C → x * x = 1

@[expose] def L3CentComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → p ^ f ≠ 3 →
    (CFSG.Blueprint.LieModel X .PSL 3 p f ∨ CFSG.Blueprint.LieModel X .PSU 3 p f) →
    ∀ z : X, orderOf z = 2 →
      CFSG.Open.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set X),
          Subgroup.centralizer ({z} : Set X)⁆ ∧
        Even (Nat.card ↥⁅Subgroup.centralizer ({z} : Set X),
          Subgroup.centralizer ({z} : Set X)⁆) ∧
        IsCyclic ↥(Subgroup.centralizer ({z} : Set X) ⊓
          Subgroup.centralizer ((⁅Subgroup.centralizer ({z} : Set X),
            Subgroup.centralizer ({z} : Set X)⁆ : Subgroup X) : Set X))

theorem eq_of_inf_le_isCyclic {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    (hΦ : HypOmegaGen Φ) {K₁ K₂ L C : Subgroup Y} (h1 : K₁ ∈ Φ) (h2 : K₂ ∈ Φ)
    (hC : IsCyclic ↥C) (hK₁ : K₁ ⊓ L ≤ C) (hK₂ : K₂ ⊓ L ≤ C)
    (h4₁ : 4 ∣ Nat.card ↥(K₁ ⊓ L)) (h4₂ : 4 ∣ Nat.card ↥(K₂ ⊓ L)) : K₁ = K₂ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : ∀ {K : Subgroup Y}, 4 ∣ Nat.card ↥(K ⊓ L) →
      ∃ D : Subgroup Y, D ≤ K ⊓ L ∧ Nat.card ↥D = 4 := by
    intro K h4
    obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(K ⊓ L)) 2 (n := 2)
      (show 2 ^ 2 ∣ Nat.card ↥(K ⊓ L) by norm_num; exact h4)
    refine ⟨D.map (K ⊓ L).subtype, Subgroup.map_subtype_le D, ?_⟩
    rw [Subgroup.card_map_of_injective (K ⊓ L).subtype_injective, hD]
    norm_num
  obtain ⟨D₁, hD₁, hc₁⟩ := hD h4₁
  obtain ⟨D₂, hD₂, hc₂⟩ := hD h4₂
  have hcard : ∀ {D : Subgroup Y}, D ≤ C → Nat.card ↥(D.subgroupOf C) = Nat.card ↥D :=
    fun hDC => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have h1C : D₁ ≤ C := hD₁.trans hK₁
  have h2C : D₂ ≤ C := hD₂.trans hK₂
  have heq : D₁.subgroupOf C = D₂.subgroupOf C :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [hcard h1C, hcard h2C, hc₁, hc₂])
  have hD12 : D₁ = D₂ := by
    have := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr h1C, inf_eq_left.mpr h2C] at this
  by_contra hne
  have hle : D₁ ≤ K₁ ⊓ K₂ := le_inf (hD₁.trans inf_le_left) (hD12 ▸ hD₂.trans inf_le_left)
  have hdvd : 2 ^ 2 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
    have := Subgroup.card_dvd_of_le hle
    rw [hc₁] at this
    simpa using this
  have hpos : Nat.card ↥(K₁ ⊓ K₂) ≠ 0 := Nat.card_pos.ne'
  have := (padicValNat_dvd_iff_le hpos).mp hdvd
  have := (hΦ.omega4 K₁ h1 K₂ h2 hne).1
  omega

section Member

variable {Y : Type} [Group Y] [Finite Y] {L H : Subgroup Y}

theorem relIndex_dvd_two (hLn : L.Normal) (hLH : L ≤ H)
    (hidx : (L.subgroupOf H).index ≤ 2 ∨ (L.subgroupOf H).index ∣ 6) {T : Subgroup Y}
    (hTH : T ≤ H) (hT : IsPGroup 2 ↥T) : L.relIndex T ∣ 2 := by
  haveI : (L.subgroupOf H).Normal := hLn.subgroupOf H
  have h1 : L.relIndex T ∣ (L.subgroupOf H).index := by
    rw [← Subgroup.relIndex_subgroupOf hTH]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT
  have h2 : L.relIndex T ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card L T
  have hcop : Nat.Coprime (L.relIndex T) 3 :=
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k (by norm_num))
  have hpos : (L.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases hidx with h | h
  · have h' : (L.subgroupOf H).index ∣ 2 := by
      interval_cases hi : (L.subgroupOf H).index
      · exact absurd rfl hpos
      · exact one_dvd 2
      · exact dvd_refl 2
    exact h1.trans h'
  · exact hcop.dvd_of_dvd_mul_right (show L.relIndex T ∣ 2 * 3 from h1.trans h)

theorem mem_and_four_dvd {Φ : Set (Subgroup Y)} (hΦ : TypeRHyp Φ) {K : Subgroup Y} (hK : K ∈ Φ)
    {z : Y} (hz : IsUniqueInvolution K z) (hLn : L.Normal) (hLH : L ≤ H) (hKH : K ≤ H)
    (hidx : (L.subgroupOf H).index ≤ 2 ∨ (L.subgroupOf H).index ∣ 6) :
    z ∈ L ∧ 4 ∣ Nat.card ↥(K ⊓ L) := by
  classical
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  set T : Subgroup Y := (S : Subgroup K).map K.subtype with hT
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  have hTs : IsSylow2In T K := isSylow2In_map_subtype K S
  obtain ⟨e⟩ := hΦ.sylow K hK T hTs
  have h8 : Nat.card ↥T = 8 := card_eq_eight_of_q8 e
  have hr := relIndex_dvd_two hLn hLH hidx (hTK.trans hKH) hTs.2.1
  have hmul := Subgroup.card_mul_index (L.subgroupOf T)
  have hA : Nat.card ↥(L ⊓ T) = Nat.card ↥(L.subgroupOf T) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective T.subtype_injective]
  have h4 : 4 ∣ Nat.card ↥(L ⊓ T) := by
    rw [hA]
    have hri : (L.subgroupOf T).index = L.relIndex T := rfl
    rw [hri, h8] at hmul
    rcases (Nat.dvd_prime Nat.prime_two).mp hr with h | h
    · rw [h] at hmul
      exact ⟨2, by omega⟩
    · rw [h] at hmul
      exact ⟨1, by omega⟩
  refine ⟨?_, (h4.trans (Subgroup.card_dvd_of_le (le_inf (inf_le_right.trans hTK) inf_le_left)))⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ T)) 2
    (dvd_trans (by norm_num) h4)
  have hgK : (g : Y) ∈ K := hTK (g.2.2)
  have hg2 : (g : Y) * (g : Y) = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg, pow_two] at this
    exact congrArg Subtype.val this
  have hg1 : (g : Y) ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  rcases hz.unique _ hgK hg2 with h | h
  · exact absurd h hg1
  · exact h ▸ g.2.1

theorem conj_mem_of_normal {K : Subgroup Y} {z : Y} (hz : IsUniqueInvolution K z) (hKH : K ≤ H)
    (hzH : z ∈ H)
    (hn : ((K.subgroupOf H).subgroupOf (Subgroup.centralizer ({⟨z, hzH⟩} : Set ↥H))).Normal)
    {c : Y} (hcH : c ∈ H) (hcz : c * z = z * c) {k : Y} (hk : k ∈ K) : c * k * c⁻¹ ∈ K := by
  have hc : (⟨c, hcH⟩ : ↥H) ∈ Subgroup.centralizer ({⟨z, hzH⟩} : Set ↥H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hcz)
  have hkz : k * z = z * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isUniqueInvolution hz hk)
  have hk' : (⟨k, hKH hk⟩ : ↥H) ∈ Subgroup.centralizer ({⟨z, hzH⟩} : Set ↥H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hkz)
  have hmem : (⟨⟨k, hKH hk⟩, hk'⟩ : ↥(Subgroup.centralizer ({⟨z, hzH⟩} : Set ↥H))) ∈
      (K.subgroupOf H).subgroupOf (Subgroup.centralizer ({⟨z, hzH⟩} : Set ↥H)) := hk
  have := hn.conj_mem _ hmem ⟨⟨c, hcH⟩, hc⟩
  exact this

end Member

section Cyclic

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem inf_le_of_dihedral {K : Subgroup Y} {z : ↥L} (hz : IsUniqueInvolution K (z : Y))
    {C : Subgroup ↥L} (hzC : z ∈ C)
    (hC : ∀ x ∈ Subgroup.centralizer ({z} : Set ↥L), x ∉ C → x * x = 1) :
    K ⊓ L ≤ C.map L.subtype := by
  rintro x ⟨hxK, hxL⟩
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  by_contra hxC
  have hxz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.centralizer ({z} : Set ↥L) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isUniqueInvolution hz hxK)))
  have h2 : x * x = 1 := congrArg Subtype.val (hC _ hxz hxC)
  rcases hz.unique x hxK h2 with h | h
  · subst h
    exact hxC C.one_mem
  · apply hxC
    have : (⟨x, hxL⟩ : ↥L) = z := Subtype.ext h
    rw [this]
    exact hzC

theorem eq_top_or_le_center_of_isQuasisimple {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem le_or_commutator_eq_bot {E A : Subgroup Y} (hE : CFSG.Open.IsQuasisimple ↥E)
    (hAE : A ≤ Subgroup.normalizer (E : Set Y)) (hEA : E ≤ Subgroup.normalizer (A : Set Y)) :
    E ≤ A ∨ ⁅A, E⁆ = ⊥ := by
  have hc : ⁅A, E⁆ ≤ A ⊓ E := by
    rw [Subgroup.commutator_le]
    intro k hk e he
    refine ⟨?_, ?_⟩
    · have h1 : e * k⁻¹ * e⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hEA he) _).mp (A.inv_mem hk)
      have h2 : ⁅k, e⁆ = k * (e * k⁻¹ * e⁻¹) := by rw [commutatorElement_def]; group
      rw [h2]
      exact A.mul_mem hk h1
    · have h1 : k * e * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hAE hk) _).mp he
      rw [commutatorElement_def]
      exact E.mul_mem h1 (E.inv_mem he)
  have hn : ((A ⊓ E).subgroupOf E).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, E.mul_mem (E.mul_mem g.2 hx.2) (E.inv_mem g.2)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hEA g.2) _).mp hx.1
  rcases eq_top_or_le_center_of_isQuasisimple hE hn with htop | hcen
  · left
    intro e he
    have : (⟨e, he⟩ : ↥E) ∈ (A ⊓ E).subgroupOf E := htop ▸ Subgroup.mem_top _
    exact this.1
  · right
    have hZ : ⁅A, E⁆ ≤ (Subgroup.center ↥E).map E.subtype := by
      intro x hx
      have hxE : x ∈ E := (hc hx).2
      refine ⟨⟨x, hxE⟩, hcen (show (⟨x, hxE⟩ : ↥E) ∈ (A ⊓ E).subgroupOf E from hc hx), rfl⟩
    have hZE : ⁅(Subgroup.center ↥E).map E.subtype, E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨e, he⟩)
    have h1 : ⁅⁅A, E⁆, E⁆ = ⊥ := le_bot_iff.mp (hZE ▸ Subgroup.commutator_mono hZ le_rfl)
    have h2' : ⁅⁅E, A⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm E A]; exact h1
    have h3 : ⁅⁅E, E⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2' h1
    have hEE : ⁅E, E⁆ = E := by
      rw [← Subgroup.map_subtype_commutator, hE.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [hEE] at h3
    rw [Subgroup.commutator_comm]
    exact h3

theorem le_oddCoreOf_of_perfect {E K : Subgroup Y} (hE : commutator ↥E = ⊤) (hEK : E ≤ K)
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) : E ≤ oddCoreOf K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (↥K ⧸ classicalInvolutionOddCore ↥K) := h2.isNilpotent
  let ψ : ↥E →* ↥K ⧸ classicalInvolutionOddCore ↥K :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hEK)
  obtain ⟨n, hnd⟩ :=
    (inferInstance : Group.IsSolvable (↥K ⧸ classicalInvolutionOddCore ↥K)).solvable
  have hd : ∀ k, derivedSeries ↥E k = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [derivedSeries_succ, ih]; exact hE
  have h1 : (derivedSeries ↥E n).map ψ ≤ derivedSeries _ n :=
    map_derivedSeries_le_derivedSeries ψ n
  rw [hd n, hnd] at h1
  intro e he
  have hψ : ψ ⟨e, he⟩ = 1 := by
    have : ψ ⟨e, he⟩ ∈ (⊥ : Subgroup _) := h1 ⟨⟨e, he⟩, Subgroup.mem_top _, rfl⟩
    simpa using this
  have hmem : (⟨e, hEK he⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K :=
    (QuotientGroup.eq_one_iff _).mp hψ
  exact ⟨_, hmem, rfl⟩

theorem commutator_eq_bot_of_quasisimple {E K : Subgroup Y} (hE : CFSG.Open.IsQuasisimple ↥E)
    (hev : Even (Nat.card ↥E)) (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K))
    (hKE : K ≤ Subgroup.normalizer (E : Set Y)) (hEK : E ≤ Subgroup.normalizer (K : Set Y)) :
    ⁅K, E⁆ = ⊥ := by
  rcases le_or_commutator_eq_bot hE hKE hEK with hle | h
  · exfalso
    have hle' := le_oddCoreOf_of_perfect hE.1 hle h2
    have hodd : Odd (Nat.card ↥(oddCoreOf K)) := oddCoreOf_odd_natCard K
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle'))) hev
  · exact h

theorem le_or_commutator_eq_bot_of_isSubnormal {E Λ X : Subgroup Y}
    (hE : CFSG.Open.IsQuasisimple ↥E) (hEX : E ≤ X) (hXE : X ≤ Subgroup.normalizer (E : Set Y))
    (hΛ : CFSG.Open.IsSubnormal Λ X) : E ≤ Λ ∨ ⁅Λ, E⁆ = ⊥ := by
  induction hΛ with
  | refl => exact Or.inl hEX
  | @step H M K hHM hHn hMK ih =>
    rcases ih hEX hXE with hEM | hc
    · have hMK' : M ≤ K := hMK.le
      have hHE : H ≤ Subgroup.normalizer (E : Set Y) := (hHM.trans hMK').trans hXE
      have hEH : E ≤ Subgroup.normalizer (H : Set Y) := by
        intro e he
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHn (hEM he)
        exact Subgroup.mem_normalizer_iff.mp hn h
      exact le_or_commutator_eq_bot hE hHE hEH
    · exact Or.inr (le_bot_iff.mp (hc ▸ Subgroup.commutator_mono hHM le_rfl))

theorem inf_le_of_component (hLn : L.Normal) {z : ↥L} {K : Subgroup Y}
    (hz : IsUniqueInvolution K (z : Y)) (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K))
    (hq : CFSG.Open.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set ↥L),
      Subgroup.centralizer ({z} : Set ↥L)⁆)
    (hev : Even (Nat.card ↥⁅Subgroup.centralizer ({z} : Set ↥L),
      Subgroup.centralizer ({z} : Set ↥L)⁆))
    (hEK : ∀ e ∈ ⁅Subgroup.centralizer ({z} : Set ↥L), Subgroup.centralizer ({z} : Set ↥L)⁆,
      ∀ k ∈ K, (e : Y) * k * (e : Y)⁻¹ ∈ K) :
    K ⊓ L ≤ (Subgroup.centralizer ({z} : Set ↥L) ⊓
      Subgroup.centralizer ((⁅Subgroup.centralizer ({z} : Set ↥L),
        Subgroup.centralizer ({z} : Set ↥L)⁆ : Subgroup ↥L) : Set ↥L)).map L.subtype := by
  set C := Subgroup.centralizer ({z} : Set ↥L) with hCdef
  set E := ⁅C, C⁆ with hEdef
  set Cz := Subgroup.centralizer ({(z : Y)} : Set Y) with hCzdef
  have hCY : C.map L.subtype = L ⊓ Cz := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))⟩
    · rintro ⟨hxL, hxz⟩
      exact ⟨⟨x, hxL⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxz)), rfl⟩
  have hEY : E.map L.subtype = ⁅L ⊓ Cz, L ⊓ Cz⁆ := by
    rw [hEdef, Subgroup.map_commutator, hCY]
  have hqY : CFSG.Open.IsQuasisimple ↥(E.map L.subtype) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (E.equivMapOfInjective L.subtype L.subtype_injective).symm hq
  have hevY : Even (Nat.card ↥(E.map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hev
  have hKE : K ≤ Subgroup.normalizer ((E.map L.subtype : Subgroup Y) : Set Y) := by
    intro k hk
    have hkz : k ∈ Cz := le_centralizer_of_isUniqueInvolution hz hk
    have hkL : conjSub k L = L := mem_normalizer_iff_conjSub_eq.mp
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; trivial)
    have hkC : conjSub k (L ⊓ Cz) = L ⊓ Cz := by
      ext x
      rw [mem_conjSub_iff, Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [← hkL, mem_conjSub_iff]
          exact h1
        · rw [← conjSub_eq_self_of_mem hkz, mem_conjSub_iff]
          exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [← hkL, mem_conjSub_iff] at h1
          exact h1
        · rw [← conjSub_eq_self_of_mem hkz, mem_conjSub_iff] at h2
          exact h2
    rw [mem_normalizer_iff_conjSub_eq, hEY]
    unfold conjSub at hkC ⊢
    rw [Subgroup.map_commutator, hkC]
  have hEK' : E.map L.subtype ≤ Subgroup.normalizer (K : Set Y) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hEK e he k hk
    · intro hk
      have h1 := hEK e⁻¹ (E.inv_mem he) _ hk
      have h2 : ((e⁻¹ : ↥L) : Y) * ((L.subtype e) * k * (L.subtype e)⁻¹) * ((e⁻¹ : ↥L) : Y)⁻¹ =
          k := by
        simp only [Subgroup.coe_subtype, Subgroup.coe_inv]
        group
      rwa [h2] at h1
  have hcomm := commutator_eq_bot_of_quasisimple hqY hevY h2 hKE hEK'
  rintro x ⟨hxK, hxL⟩
  refine ⟨⟨x, hxL⟩, ⟨?_, ?_⟩, rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isUniqueInvolution hz hxK)))
  · refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hxK
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 (e : Y) ⟨e, he, rfl⟩)

end Cyclic

section Ident

variable {Y : Type} [Group Y] [Finite Y]

theorem e3aShape_cases (hF : FStarSimple Y) {H : Subgroup Y} (hLH : genFittingFStar Y ≤ H)
    (h : E3aShape ↥H) :
    (((genFittingFStar Y).subgroupOf H).index ≤ 2 ∨
        ((genFittingFStar Y).subgroupOf H).index ∣ 6) ∧ IsE3aGroup ↥(genFittingFStar Y) := by
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF.1
  have hFH := genFittingFStar_eq_of_le (genFittingFStar_normal Y) hF.2
    (centralizer_eq_bot_of_fStarSimple hF) hLH
  obtain ⟨eF⟩ := nonempty_fStarQuot_equiv (genFittingFStar_normal Y) hF.2
    (centralizer_eq_bot_of_fStarSimple hF) hLH
  rcases h with ⟨p, f, hp, hp2, ⟨hfe, hl2, hidx⟩ | ⟨hl3, h3, hidx⟩⟩
  · rw [hFH] at hidx
    exact ⟨Or.inl hidx, p, f, hp, hp2, Or.inl ⟨hfe, hl2.of_mulEquiv eF⟩⟩
  · rw [hFH] at hidx
    exact ⟨Or.inr hidx, p, f, hp, hp2,
      Or.inr ⟨hl3.imp (fun h => h.of_mulEquiv eF) (fun h => h.of_mulEquiv eF), h3⟩⟩

theorem isConj_of_isE3aGroup {X : Type} [Group X] [Finite X] (h : IsE3aGroup X) {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨p, f, hp, hp2, ⟨hfe, hl2⟩ | ⟨hl3 | hu3, -⟩⟩ := h
  · have hf : 1 ≤ f := hl2.admissible.2.1
    have h8 : p ^ f % 8 = 1 := by
      obtain ⟨k, rfl⟩ := hfe
      have hp8 : p ^ 2 % 8 = 1 := by
        have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
        have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
      rw [show k + k = 2 * k by ring, pow_mul, Nat.pow_mod, hp8, one_pow]
      norm_num
    exact (Goldschmidt.Rank2List.psl2_concl X hp hp2 hf (Or.inl h8)
      (hl2.statedClassicalModel (by decide))).1 x y hx hy
  · exact (Goldschmidt.Rank2List.psl3_concl X hp hp2
      (hl3.statedClassicalModel (by decide))).1 x y hx hy
  · exact (Goldschmidt.Rank2List.psu3_concl X hp hp2 hu3.admissible.2.1
      (hu3.statedClassicalModel (by decide))).1 x y hx hy

end Ident

section E3a

theorem e3aOneClass_of_inputs (hL2 : L2CentDihedral) (hL3 : L3CentComponent) : E3aOneClass := by
  intro Y _ _ _ _ hF Φ hΦ K₁ hK₁ K₂ hK₂ z₁ z₂ hz₁ hz₂ ⟨hzH₁, hsh₁, hn₁⟩ ⟨hzH₂, hsh₂, hn₂⟩
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF.1
  have hLn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC := centralizer_eq_bot_of_fStarSimple hF
  have hne : ∀ {K : Subgroup Y} {z : Y}, IsUniqueInvolution K z → K ≠ ⊥ := fun hz h =>
    hz.ne_one (Subgroup.mem_bot.mp (h ▸ hz.mem))
  have hLH₁ := le_omegaGen_lOrbit hLn hC (hne hz₁)
  have hLH₂ := le_omegaGen_lOrbit hLn hC (hne hz₂)
  have hKH₁ : K₁ ≤ omegaGen (lOrbit (genFittingFStar Y) K₁) := le_omegaGen mem_lOrbit_self
  have hKH₂ : K₂ ≤ omegaGen (lOrbit (genFittingFStar Y) K₂) := le_omegaGen mem_lOrbit_self
  obtain ⟨hidx₁, hE⟩ := e3aShape_cases hF hLH₁ hsh₁
  obtain ⟨hidx₂, -⟩ := e3aShape_cases hF hLH₂ hsh₂
  obtain ⟨hzL₁, h4₁⟩ := mem_and_four_dvd hΦ hK₁ hz₁ hLn hLH₁ hKH₁ hidx₁
  obtain ⟨hzL₂, h4₂⟩ := mem_and_four_dvd hΦ hK₂ hz₂ hLn hLH₂ hKH₂ hidx₂
  have hord : ∀ {K : Subgroup Y} {z : Y} (_ : IsUniqueInvolution K z)
      (hzL : z ∈ genFittingFStar Y), orderOf (⟨z, hzL⟩ : ↥(genFittingFStar Y)) = 2 :=
    fun hz _ => orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hz.sq)
      (fun h => hz.ne_one (congrArg Subtype.val h))
  obtain ⟨l, hl⟩ := isConj_iff.mp (isConj_of_isE3aGroup hE (hord hz₂ hzL₂) (hord hz₁ hzL₁))
  have hlz : (l : Y) * z₂ * (l : Y)⁻¹ = z₁ := congrArg Subtype.val hl
  have hz₂' : z₂ = (l : Y)⁻¹ * z₁ * (l : Y) := by rw [← hlz]; group
  set K₃ := conjSub (l : Y) K₂ with hK₃
  have hK₃Φ : K₃ ∈ Φ := hΦ.hyp.conjInvariant _ _ hK₂
  have hz₃ : IsUniqueInvolution K₃ z₁ := by
    have := hz₂.conj (l : Y)
    rwa [hlz] at this
  have h4₃ : 4 ∣ Nat.card ↥(K₃ ⊓ genFittingFStar Y) := by
    have heq : K₃ ⊓ genFittingFStar Y = conjSub (l : Y) (K₂ ⊓ genFittingFStar Y) := by
      ext x
      rw [Subgroup.mem_inf, hK₃, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (genFittingFStar Y).mul_mem ((genFittingFStar Y).mul_mem
          ((genFittingFStar Y).inv_mem l.2) h2) l.2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := (genFittingFStar Y).mul_mem ((genFittingFStar Y).mul_mem l.2 h2)
          ((genFittingFStar Y).inv_mem l.2)
        simpa [mul_assoc] using this
    rw [heq]
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj (l : Y)).injective]
    exact h4₂
  suffices h : K₁ = K₃ by
    refine ⟨(l : Y)⁻¹, (genFittingFStar Y).inv_mem l.2, ?_⟩
    rw [h, hK₃, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  rcases hE with ⟨p, f, hp, hp2, ⟨hfe, hl2⟩ | ⟨hl3, h3⟩⟩
  ·
    obtain ⟨C, hCc, hzC, hCd⟩ := hL2 _ p f hp hp2 hfe hl2 ⟨z₁, hzL₁⟩ (hord hz₁ hzL₁)
    have hcyc : IsCyclic ↥(C.map (genFittingFStar Y).subtype) :=
      isCyclic_of_surjective (C.equivMapOfInjective _ (genFittingFStar Y).subtype_injective)
        (MulEquiv.surjective _)
    exact eq_of_inf_le_isCyclic hΦ.hyp hK₁ hK₃Φ hcyc (inf_le_of_dihedral hz₁ hzC hCd)
      (inf_le_of_dihedral hz₃ hzC hCd) h4₁ h4₃
  ·
    obtain ⟨hq, hev, hcyc⟩ := hL3 _ p f hp hp2 h3 hl3 ⟨z₁, hzL₁⟩ (hord hz₁ hzL₁)
    have hcyc' : IsCyclic ↥((Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y)) ⊓
        Subgroup.centralizer ((⁅Subgroup.centralizer
          ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y)), Subgroup.centralizer
          ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y))⁆ : Subgroup ↥(genFittingFStar Y)) :
            Set ↥(genFittingFStar Y))).map (genFittingFStar Y).subtype) :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _
        (genFittingFStar Y).subtype_injective) (MulEquiv.surjective _)
    have hez : ∀ e ∈ ⁅Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y)),
        Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y))⁆,
        (e : Y) * z₁ = z₁ * (e : Y) := fun e he =>
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.commutator_le_self _ he))
    have hE₁ : ∀ e ∈ ⁅Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y)),
        Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y))⁆,
        ∀ k ∈ K₁, (e : Y) * k * (e : Y)⁻¹ ∈ K₁ := fun e he k hk =>
      conj_mem_of_normal hz₁ hKH₁ hzH₁ hn₁ (hLH₁ e.2) (hez e he) hk
    have hE₃ : ∀ e ∈ ⁅Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y)),
        Subgroup.centralizer ({⟨z₁, hzL₁⟩} : Set ↥(genFittingFStar Y))⁆,
        ∀ k ∈ K₃, (e : Y) * k * (e : Y)⁻¹ ∈ K₃ := by
      intro e he k hk
      rw [hK₃, mem_conjSub_iff] at hk ⊢
      have hcH : (l : Y)⁻¹ * (e : Y) * (l : Y) ∈ omegaGen (lOrbit (genFittingFStar Y) K₂) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLH₂ ((genFittingFStar Y).inv_mem l.2))
          (hLH₂ e.2)) (hLH₂ l.2)
      have hcz : (l : Y)⁻¹ * (e : Y) * (l : Y) * z₂ = z₂ * ((l : Y)⁻¹ * (e : Y) * (l : Y)) := by
        rw [hz₂']
        calc (l : Y)⁻¹ * (e : Y) * (l : Y) * ((l : Y)⁻¹ * z₁ * (l : Y))
            = (l : Y)⁻¹ * ((e : Y) * z₁) * (l : Y) := by group
          _ = (l : Y)⁻¹ * (z₁ * (e : Y)) * (l : Y) := by rw [hez e he]
          _ = (l : Y)⁻¹ * z₁ * (l : Y) * ((l : Y)⁻¹ * (e : Y) * (l : Y)) := by group
      have := conj_mem_of_normal hz₂ hKH₂ hzH₂ hn₂ hcH hcz hk
      have e' : (l : Y)⁻¹ * ((e : Y) * k * (e : Y)⁻¹) * (l : Y) =
          (l : Y)⁻¹ * (e : Y) * (l : Y) * ((l : Y)⁻¹ * k * (l : Y)) *
            ((l : Y)⁻¹ * (e : Y) * (l : Y))⁻¹ := by group
      rw [e']
      exact this
    exact eq_of_inf_le_isCyclic hΦ.hyp hK₁ hK₃Φ hcyc'
      (inf_le_of_component hLn hz₁ (hΦ.twoGroup K₁ hK₁) hq hev hE₁)
      (inf_le_of_component hLn hz₃ (hΦ.twoGroup K₃ hK₃Φ) hq hev hE₃) h4₁ h4₃

end E3a

section Coinc

variable {X : Type} [Group X] [Finite X]

theorem eq_of_mul_self_sl23 : ∀ a b : SL(2, ZMod 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 →
    a = b := by
  decide

theorem false_of_le_isCyclic {Λ C : Subgroup X} (e : ↥Λ ≃* SL(2, ZMod 3)) (hC : IsCyclic ↥C)
    (hΛC : Λ ≤ C) : False := by
  apply Q3.sl2Three_not_comm
  intro a b
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  rw [← map_mul, ← map_mul]
  congr 1
  have h := hC.commGroup.mul_comm (⟨a', hΛC a'.2⟩ : ↥C) ⟨b', hΛC b'.2⟩
  have h' : (a' : X) * (b' : X) = (b' : X) * (a' : X) := congrArg Subtype.val h
  exact Subtype.ext h'

theorem not_isE3aGroup_of_classical (hL2 : L2CentDihedral) (hL3 : L3CentComponent)
    {Λ : Subgroup X} {z : X} (hΛ : IsClassicalMember3 Λ z) (h24 : Nat.card Λ = 24) :
    ¬ IsE3aGroup X := by
  obtain ⟨e⟩ := nonempty_sl23_of_classical hΛ h24
  have hΛz : Λ ≤ Subgroup.centralizer ({z} : Set X) := hΛ.subnormal.le
  rintro ⟨p, f, hp, hp2, ⟨hfe, hl2⟩ | ⟨hl3, h3⟩⟩
  · obtain ⟨C, hCc, hzC, hCd⟩ := hL2 X p f hp hp2 hfe hl2 z hΛ.orderOf_eq_two
    refine false_of_le_isCyclic e hCc fun x hx => ?_
    by_contra hxC
    have hx2 := hCd x (hΛz hx) hxC
    have hz2 : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hΛ.orderOf_eq_two, pow_two] at this
    have hx1 : x ≠ 1 := fun h => hxC (h ▸ C.one_mem)
    have hz1 : z ≠ 1 := hΛ.ne_one
    have h := eq_of_mul_self_sl23 (e ⟨x, hx⟩) (e ⟨z, hΛ.mem⟩)
      (by rw [← map_mul, ← map_one e]; congr 1; exact Subtype.ext hx2)
      (by rw [← map_mul, ← map_one e]; congr 1; exact Subtype.ext hz2)
      (fun h => hx1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
      (fun h => hz1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
    have hxz : x = z := congrArg Subtype.val (e.injective h)
    exact hxC (hxz ▸ hzC)
  · obtain ⟨hq, hev, hcyc⟩ := hL3 X p f hp hp2 h3 hl3 z hΛ.orderOf_eq_two
    set Cz := Subgroup.centralizer ({z} : Set X) with hCz
    have hEX : ⁅Cz, Cz⁆ ≤ Cz := Subgroup.commutator_le_self _
    have hXE : Cz ≤ Subgroup.normalizer ((⁅Cz, Cz⁆ : Subgroup X) : Set X) := by
      intro c hc
      rw [mem_normalizer_iff_conjSub_eq]
      have h1 : conjSub c Cz = Cz := conjSub_eq_self_of_mem hc
      unfold conjSub at h1 ⊢
      rw [Subgroup.map_commutator, h1]
    rcases le_or_commutator_eq_bot_of_isSubnormal hq hEX hXE hΛ.subnormal with hle | hc
    ·
      have hsol : Group.IsSolvable ↥Λ :=
        haveI := Q3.isSolvable_sl2Three
        solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
      haveI : Group.IsSolvable ↥(⁅Cz, Cz⁆ : Subgroup X) :=
        solvable_of_solvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable ↥(⁅Cz, Cz⁆ : Subgroup X)).solvable
      have hd : ∀ k, derivedSeries ↥(⁅Cz, Cz⁆ : Subgroup X) k = ⊤ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [derivedSeries_succ, ih]; exact hq.1
      have hn' : (⊤ : Subgroup ↥(⁅Cz, Cz⁆ : Subgroup X)) = ⊥ := (hd n).symm.trans hn
      have h1 : Nat.card ↥(⁅Cz, Cz⁆ : Subgroup X) = 1 := by
        rw [← Subgroup.card_top (G := ↥(⁅Cz, Cz⁆ : Subgroup X)), hn', Subgroup.card_bot]
      rw [h1] at hev
      exact absurd hev (by decide)
    · refine false_of_le_isCyclic e hcyc (le_inf hΛz ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc

end Coinc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

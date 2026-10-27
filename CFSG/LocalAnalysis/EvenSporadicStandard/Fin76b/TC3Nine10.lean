module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6D8
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def D8InCentralizer16 (K : Type*) [Group K] : Prop :=
  ∃ (s : K) (D : Subgroup K), orderOf s = 16 ∧ D ≤ centralizer ({s} : Set K) ∧
    Nonempty (↥D ≃* DihedralGroup 4)

@[expose] def BranchK (K : Type) [Group K] : Prop :=
  (∃ N : Subgroup K, N.Normal ∧
      Nonempty (↥N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
      centralizer (N : Set K) = ⊥) ∨ Nonempty (K ≃* ↥U43Ext)

@[expose] def FinK16 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], BranchK K → ¬ D8InCentralizer16 K

theorem exists_orderOf_sixteen {X : Type*} [Group X] {x : X} {m : ℕ} (hx : orderOf x = 2 ^ m)
    (hm : 4 ≤ m) : ∃ y : X, orderOf y = 16 := by
  refine ⟨x ^ (2 ^ (m - 4)), ?_⟩
  have hdvd : 2 ^ (m - 4) ∣ orderOf x := by
    rw [hx]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hx]
  rw [show 2 ^ m = 2 ^ (m - 4) * 16 by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    congr 1
    omega]
  exact Nat.mul_div_cancel_left _ (by positivity)

theorem exists_orderOf_sixteen_of_shape {G : Type*} [Group G] {S : Subgroup G}
    (hS : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n))
    (h : 16 < Nat.card ↥S) : ∃ s ∈ S, orderOf s = 16 := by
  rcases hS with ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hc : Nat.card ↥S = 2 * 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hx : orderOf (e.symm (DihedralGroup.r 1)) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq]
      exact DihedralGroup.orderOf_r_one
    obtain ⟨y, hy⟩ := exists_orderOf_sixteen hx hk4
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  · have hn3 : 3 ≤ n := by omega
    have hc : Nat.card ↥S = 2 ^ n := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Semidihedral.card n hn3
    have hn5 : 5 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hx : orderOf (e.symm (CFSG.Semidihedral.r n)) = 2 ^ (n - 1) := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_r n hn3
    obtain ⟨y, hy⟩ := exists_orderOf_sixteen hx (by omega)
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem orderOf_mk_of_orderOf_sixteen {K : Type*} [Group K] [Finite K] {s : K}
    (hs : orderOf s = 16) : orderOf (QuotientGroup.mk s : K ⧸ fusionOddCore K) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Odd (Nat.card (fusionOddCore K)) := odd_natCard_fusionOddCore K
  have h16 : s ^ 16 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  refine orderOf_eq_prime_pow (p := 2) (n := 3) ?_ ?_
  · intro h
    have h8 : s ^ (2 ^ 3) ∈ fusionOddCore K := by
      rw [← QuotientGroup.mk_pow] at h
      exact (QuotientGroup.eq_one_iff _).1 h
    have hodd : Odd (orderOf (s ^ (2 ^ 3))) :=
      Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ h8)
    have hord : orderOf (s ^ (2 ^ 3)) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs]; norm_num), hs]
      norm_num
    rw [hord] at hodd
    exact absurd hodd (by decide)
  · rw [← QuotientGroup.mk_pow, show 2 ^ (3 + 1) = 16 by norm_num, h16, QuotientGroup.mk_one]

theorem dihedral_of_odd_quotient {X : Type*} [Group X] [Finite X]
    (e : X ⧸ fusionOddCore X ≃* alternatingGroup (Fin 6)) {P : Subgroup X} (hP2 : IsPGroup 2 P)
    (hP8 : Nat.card ↥P = 8) : Nonempty (↥P ≃* DihedralGroup 4) := by
  have hO : Odd (Nat.card (fusionOddCore X)) := odd_natCard_fusionOddCore X
  let ρ : ↥P →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (fusionOddCore X)).comp P.subtype)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : X) ∈ fusionOddCore X := by
      have : QuotientGroup.mk' (fusionOddCore X) (x : X) = 1 := by
        apply e.injective
        simpa [ρ] using hx
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨m, hm⟩ := hP2 x
    have hodd : Odd (orderOf x) := by
      rw [← Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ h1)
    exact M10Config.eq_one_of_odd_of_pow_two hodd m hm
  let Q : Subgroup (alternatingGroup (Fin 6)) := ρ.range
  have hQ : Nat.card ↥Q = 8 := by
    rw [← hP8]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  obtain ⟨f⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight Q hQ
  exact ⟨(MonoidHom.ofInjective hρ).trans f⟩

theorem exists_dihedral_image {G : Type} [Group G] [Finite G] {L E : Subgroup G} {β : G}
    (hE2 : IsPGroup 2 E) (hEL : E ≤ L)
    (h8 : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8)
    (hDq : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6))) :
    ∃ D : Subgroup (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))),
      Nonempty (↥D ≃* DihedralGroup 4) ∧
      ∀ d ∈ D, ∃ y : ↥(centralizer ({β} : Set G)), (y : G) ∈ E ∧ QuotientGroup.mk y = d := by
  obtain ⟨eA⟩ := hDq
  set K : Subgroup G := centralizer ({β} : Set G) with hK
  set DG : Subgroup G := E ⊓ K with hDG
  set DK : Subgroup ↥K := DG.subgroupOf K with hDK
  have hO : Odd (Nat.card (fusionOddCore ↥K)) := odd_natCard_fusionOddCore _
  have hDG2 : IsPGroup 2 DG := hE2.to_le inf_le_left
  let ρ : ↥DK →* ↥K ⧸ fusionOddCore ↥K := (QuotientGroup.mk' (fusionOddCore ↥K)).comp DK.subtype
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((x : ↥K) : ↥K) ∈ fusionOddCore ↥K := (QuotientGroup.eq_one_iff _).1 hx
    have hxDG : ((x : ↥K) : G) ∈ DG := mem_subgroupOf.1 x.2
    obtain ⟨m, hm⟩ := hDG2 (⟨((x : ↥K) : G), hxDG⟩ : ↥DG)
    have hm' : ((x : ↥K) : G) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    have hodd : Odd (orderOf (x : ↥K)) :=
      Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ h1)
    have : (x : ↥K) = 1 := by
      refine M10Config.eq_one_of_odd_of_pow_two hodd m ?_
      apply Subtype.ext
      simpa using hm'
    exact Subtype.ext this
  have hDKcard : Nat.card ↥DK = 8 := by
    rw [hDK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show DG ≤ K from inf_le_right)).toEquiv]
    exact h8
  have hdih : Nonempty (↥DK ≃* DihedralGroup 4) := by
    let X : Type := ↥(L ⊓ K)
    let P : Subgroup X := DG.subgroupOf (L ⊓ K)
    have hDGL : DG ≤ L ⊓ K := le_inf (inf_le_left.trans hEL) inf_le_right
    have hPcard : Nat.card ↥P = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDGL).toEquiv]
      exact h8
    have hP2 : IsPGroup 2 P := by
      have : IsPGroup 2 DG := hDG2
      exact this.comap_subtype
    obtain ⟨f⟩ := dihedral_of_odd_quotient eA hP2 hPcard
    exact ⟨((Subgroup.subgroupOfEquivOfLe (show DG ≤ K from inf_le_right)).trans
      (Subgroup.subgroupOfEquivOfLe hDGL).symm).trans f⟩
  let e : ↥DK ≃* ↥(DK.map (QuotientGroup.mk' (fusionOddCore ↥K))) :=
    (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr (by
      ext x
      simp [ρ, MonoidHom.mem_range, Subgroup.mem_map]))
  refine ⟨DK.map (QuotientGroup.mk' (fusionOddCore ↥K)), ⟨e.symm.trans hdih.some⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, mem_subgroupOf.1 hy |>.1, rfl⟩

theorem card_le_sixteen_of_finK16 (hFin : FinK16) {G : Type} [Group G] [Finite G]
    {L E S : Subgroup G} {β : G} (hE2 : IsPGroup 2 E) (hEL : E ≤ L)
    (hDq : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)))
    (h8 : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8) (hSC : S ≤ centralizer (E : Set G))
    (hSβ : ∀ s ∈ S, s * β = β * s)
    (hshape : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n))
    (hbranch : BranchK (↥(centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(centralizer ({β} : Set G)))) : Nat.card ↥S ≤ 16 := by
  by_contra hlt
  obtain ⟨s, hsS, hs16⟩ := exists_orderOf_sixteen_of_shape hshape (not_le.1 hlt)
  obtain ⟨D, hDd, hDmem⟩ := exists_dihedral_image hE2 hEL h8 hDq
  let sK : ↥(centralizer ({β} : Set G)) := ⟨s, mem_centralizer_singleton_iff.2 (hSβ s hsS)⟩
  have hsK : orderOf sK = 16 := by rw [← Subgroup.orderOf_coe]; exact hs16
  refine hFin _ hbranch ⟨QuotientGroup.mk sK, D, orderOf_mk_of_orderOf_sixteen hsK, ?_, hDd⟩
  intro d hd
  obtain ⟨y, hyE, rfl⟩ := hDmem d hd
  rw [mem_centralizer_singleton_iff]
  have hys : (y : G) * s = s * (y : G) := mem_centralizer_iff.1 (hSC hsS) y hyE
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext hys)

end CFSG.EvenSporadicStandard.Fin76b

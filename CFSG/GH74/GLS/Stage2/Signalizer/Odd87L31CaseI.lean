module

public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cHyp
import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
import CFSG.GH74.GLS.Stage2.Local.Prop27Br
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Dih
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def NonCentralT1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    IsClassicalKind k → ∀ x : G, IsNonCentralInvolution x → ∀ T : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)) →
      ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ IsDihedral ↥T₁

section Basic

theorem l31_isDihedral_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsDihedral B) :
    IsDihedral A := by
  obtain ⟨m, k, hm, hk, ⟨f⟩⟩ := h
  exact ⟨m, k, hm, hk, ⟨e.trans f⟩⟩

theorem l31_dihTwo_of_isDihedral {Y : Type} [Group Y] (hD : IsDihedral Y) (h2 : IsPGroup 2 Y) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (Y ≃* DihedralGroup (2 ^ (n - 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, k, hm, hk, ⟨e⟩⟩ := hD
  have hp : IsPGroup 2 (DihedralGroup k) := h2.of_equiv e
  have : NeZero k := ⟨by omega⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hp) (DihedralGroup.r 1)
  rw [DihedralGroup.orderOf_r_one] at hj
  have hj1 : 1 ≤ j := by
    by_contra hj0
    have : j = 0 := by omega
    rw [this] at hj
    simp at hj
    omega
  refine ⟨j + 1, by omega, ?_⟩
  rw [Nat.add_sub_cancel, ← hj]
  exact ⟨e⟩

theorem l31_eq_one_of_sq_of_odd {K : Type} [Group K] (N : Subgroup K)
    (hN : Odd (Nat.card N)) {x : K} (hx : x ∈ N) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hodd : Odd (orderOf x) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2) with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem l31_exists_involution {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 ↥Q) (hne : Q ≠ ⊥) : ∃ r ∈ Q, orderOf r = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq Q (by simpa using hn))
  have h2 : 2 ∣ Nat.card ↥Q := by
    rw [hn]
    exact dvd_pow_self 2 hn1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 h2
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Basic

section Sylow

variable {G : Type} [Group G]

theorem l31_exists_sylow_ge {K A : Subgroup G} (hAK : A ≤ K) (hA : IsPGroup 2 ↥A) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T K ∧ A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  refine ⟨Q.map K.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAK ha⟩, hQ ha, rfl⟩

theorem l31_exists_dihedral_ge {X₀ A : Subgroup G}
    (hF : ∀ P : Sylow 2 ↥X₀, IsDihedral ↥P) (hAX : A ≤ X₀) (hA : IsPGroup 2 ↥A) :
    ∃ D : Subgroup G, A ≤ D ∧ D ≤ X₀ ∧ IsPGroup 2 ↥D ∧ IsDihedral ↥D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, ⟨Q, rfl⟩, hAT⟩ := l31_exists_sylow_ge hAX hA
  refine ⟨_, hAT, map_subtype_le _, Q.isPGroup'.map X₀.subtype, ?_⟩
  exact l31_isDihedral_of_equiv
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥X₀) X₀.subtype X₀.subtype_injective).symm (hF Q)

end Sylow

section Quot

open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix in
theorem l31_not_isCyclic_sylow_of_perfect {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [Nontrivial Y] (P : Sylow 2 Y) : ¬ IsCyclic ↥(P : Subgroup Y) := by
  intro hc
  have hmin : (Nat.card Y).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).2 (even_iff_two_dvd.1 (TwoGroups.even_natCard_of_perfect Y))
  exact TwoGroups.not_normalizer_le_centralizer P (hc.normalizer_le_centralizer hmin)

theorem l31_equiv_map_quotient {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) {P : Subgroup M} (hP : IsPGroup 2 ↥P) :
    Nonempty (↥P ≃* ↥(P.map (QuotientGroup.mk' N))) := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).domRestrict P) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : (x : M) ∈ N := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hbot : P ⊓ N = ⊥ := isPGroup_two_inf_eq_bot_of_odd P N hP hN
    have : (x : M) ∈ P ⊓ N := ⟨x.2, hxN⟩
    rw [hbot, mem_bot] at this
    exact Subtype.ext this
  exact ⟨(MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))⟩

end Quot

section Main

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
  CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem l31_inf_eq_bot
    {X₀ J₀ Q : Subgroup G} (hF : ∀ P : Sylow 2 ↥X₀, IsDihedral ↥P) (hJ : J₀ ≤ X₀)
    (hQX : Q ≤ X₀) (hQ : IsPGroup 2 ↥Q) (hcomm : ∀ x ∈ J₀, ∀ q ∈ Q, x * q = q * x)
    (hq : IsQuasisimple (↥J₀ ⧸ pPrimeCore 2 ↥J₀)) : Q = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQne
  obtain ⟨r, hrQ, hr2⟩ := l31_exists_involution hQ hQne
  set N : Subgroup ↥J₀ := pPrimeCore 2 ↥J₀ with hNdef
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥J₀))
  obtain ⟨hperf, hsimp, a, b, hab⟩ := hq
  have : Group.IsPerfect (↥J₀ ⧸ N) := hperf
  have hnt : Nontrivial (↥J₀ ⧸ N) := by
    have : Nontrivial ((↥J₀ ⧸ N) ⧸ center (↥J₀ ⧸ N)) := ⟨⟨a * b, b * a, hab⟩⟩
    exact (QuotientGroup.mk_surjective (s := center (↥J₀ ⧸ N))).nontrivial
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J₀) := inferInstance
  set PG : Subgroup G := (P : Subgroup ↥J₀).map J₀.subtype with hPG
  have hPG2 : IsPGroup 2 ↥PG := P.isPGroup'.map J₀.subtype
  have hPGJ : PG ≤ J₀ := Subgroup.map_subtype_le _
  have ePG : ↥(P : Subgroup ↥J₀) ≃* ↥PG :=
    Subgroup.equivMapOfInjective _ J₀.subtype J₀.subtype_injective
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  obtain ⟨eP⟩ := l31_equiv_map_quotient N hNodd P.isPGroup'
  have hPnc : ¬ IsCyclic ↥(P : Subgroup ↥J₀) := by
    intro hc
    have : IsCyclic ↥((P.mapSurjective hπ : Sylow 2 (↥J₀ ⧸ N)) : Subgroup (↥J₀ ⧸ N)) := by
      rw [Sylow.coe_mapSurjective]
      exact eP.isCyclic.mp hc
    exact l31_not_isCyclic_sylow_of_perfect _ this
  obtain ⟨D₀, hPD₀, hD₀X, hD₀2, hD₀d⟩ := l31_exists_dihedral_ge hF (hPGJ.trans hJ) hPG2
  have hPGnc : ¬ IsCyclic ↥PG := fun hc => hPnc (ePG.isCyclic.mpr hc)
  have hPGdih : IsDihedral ↥PG := by
    have e : ↥(PG.subgroupOf D₀) ≃* ↥PG := Subgroup.subgroupOfEquivOfLe hPD₀
    rcases subgroup_of_dihedral hD₀d (PG.subgroupOf D₀) with h | h
    · exact absurd (e.isCyclic.mp h) hPGnc
    · exact l31_isDihedral_of_equiv e.symm h
  have hP'dih : IsDihedral ↥(P.map (QuotientGroup.mk' N)) :=
    l31_isDihedral_of_equiv (eP.symm.trans ePG) hPGdih
  have hcenter : Odd (Nat.card ↥(center (↥J₀ ⧸ N))) := by
    obtain ⟨n, hn, ⟨e⟩⟩ := l31_dihTwo_of_isDihedral hP'dih
      (P.isPGroup'.map (QuotientGroup.mk' N))
    exact odd_card_center_of_quasisimple_dihedral
      ⟨hperf.commutator_eq_top, hsimp⟩ ⟨P.mapSurjective hπ, n, hn, ⟨e⟩⟩
  have hPGne : PG ≠ ⊥ := fun h => hPGnc (by rw [h]; infer_instance)
  obtain ⟨a₀, ha₀PG, ha₀2⟩ := l31_exists_involution hPG2 hPGne
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha₀2
    omega
  have ha₀sq : a₀ ^ 2 = 1 := by rw [← ha₀2]; exact pow_orderOf_eq_one a₀
  obtain ⟨V, hVPG, -, -, hVab, hV4⟩ :=
    dihedral_centralizer_four (l31_dihTwo_of_isDihedral hPGdih hPG2) ha₀PG ha₀1 ha₀sq
  have hVJ : V ≤ J₀ := hVPG.trans hPGJ
  have hVnc : ¬ IsCyclic ↥V := by
    intro hc
    obtain ⟨g, hg⟩ := hc.exists_generator
    have hord : orderOf g = 4 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg]
      exact hV4
    have hg2 : g ^ 2 = 1 := Subtype.ext (hVab.2 g g.2)
    have := orderOf_dvd_of_pow_eq_one hg2
    rw [hord] at this
    omega
  have hrcV : zpowers r ≤ centralizer (V : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    exact hcomm h (hVJ hh) r hrQ
  have hVrc : V ≤ centralizer (zpowers r : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact hrcV
  have hrQ' : zpowers r ≤ Q := zpowers_le.mpr hrQ
  have hA2 : IsPGroup 2 ↥(V ⊔ zpowers r) :=
    (hPG2.to_le hVPG).to_sup_of_normal_right' (hQ.to_le hrQ')
      (hVrc.trans (Subgroup.centralizer_le_normalizer _))
  have hAX : V ⊔ zpowers r ≤ X₀ := sup_le (hVJ.trans hJ) (hrQ'.trans hQX)
  obtain ⟨D, hAD, hDX, hD2, hDd⟩ := l31_exists_dihedral_ge hF hAX hA2
  have hAnc : ¬ IsCyclic ↥(V ⊔ zpowers r) := fun hc =>
    hVnc (Subgroup.isCyclic_of_le (le_sup_left : V ≤ V ⊔ zpowers r))
  have hVc : V ≤ centralizer (V : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hVab.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have heq : V ⊔ zpowers r = V :=
    commuting_noncyclic_eq (Or.inr (Or.inl (l31_dihTwo_of_isDihedral hDd hD2))) hAD
      (le_sup_left.trans hAD) hAnc hVnc
      (fun x hx y hy => ((mem_centralizer_iff.mp (sup_le hVc hrcV hx) y hy)).symm)
  have hrV : r ∈ V := heq ▸ (Subgroup.mem_sup_right (mem_zpowers r) : r ∈ V ⊔ zpowers r)
  have hrJ : r ∈ J₀ := hVJ hrV
  let r' : ↥J₀ := ⟨r, hrJ⟩
  have hr'c : (QuotientGroup.mk r' : ↥J₀ ⧸ N) ∈ center (↥J₀ ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm y' y'.2 r hrQ)
  have hr'sq : (QuotientGroup.mk r' : ↥J₀ ⧸ N) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : r' ^ 2 = 1 := Subtype.ext (by
      show r ^ 2 = 1
      rw [← hr2]
      exact pow_orderOf_eq_one r)
    rw [this]
    rfl
  have h1 := l31_eq_one_of_sq_of_odd (center (↥J₀ ⧸ N)) hcenter hr'c hr'sq
  have hr'N : r' ∈ N := (QuotientGroup.eq_one_iff r').mp h1
  have hdvd : orderOf r' ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hr'N
  have hord : orderOf r' = 2 := by
    rw [← Subgroup.orderOf_coe r']
    exact hr2
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)

end Main

section Embed

variable {G : Type} [Group G]

theorem l31_embed {T J R T₁ : Subgroup G} (hTn : T ≤ normalizer (J : Set G)) (hRT : R ≤ T)
    (hT₁T : T₁ ≤ T) (hsup : (T ⊓ J) ⊔ T₁ = T) (hinf : T₁ ⊓ J = ⊥) (hRJ : R ⊓ J = ⊥)
    (hd : IsDihedral ↥T₁) : IsCyclic ↥R ∨ IsDihedral ↥R := by
  set Nt : Subgroup ↥T := (T ⊓ J).subgroupOf T with hNt
  have hNtn : Nt.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : (n : G) ∈ T ⊓ J := hn
    show (g : G) * n * (g : G)⁻¹ ∈ T ⊓ J
    exact ⟨T.mul_mem (T.mul_mem g.2 n.2) (T.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp (hTn g.2) (n : G)).mp h1.2⟩
  let g₁ : ↥T₁ →* ↥T ⧸ Nt := (QuotientGroup.mk' Nt).comp (Subgroup.inclusion hT₁T)
  have hg₁inj : Function.Injective g₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : Subgroup.inclusion hT₁T x ∈ Nt :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hxJ : (x : G) ∈ T ⊓ J := hxN
    have : (x : G) ∈ T₁ ⊓ J := ⟨x.2, hxJ.2⟩
    rw [hinf, mem_bot] at this
    exact Subtype.ext this
  have hg₁surj : Function.Surjective g₁ := by
    intro q
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    have hsup' : (T ⊓ J).subgroupOf T ⊔ T₁.subgroupOf T = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (inf_le_left : T ⊓ J ≤ T) hT₁T, hsup]
      exact Subgroup.subgroupOf_self T
    have ht : t ∈ (T ⊓ J).subgroupOf T ⊔ T₁.subgroupOf T := by rw [hsup']; trivial
    obtain ⟨n, hn, x, hx, hnx⟩ := Subgroup.mem_sup_of_normal_left.mp ht
    refine ⟨⟨(x : G), hx⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hT₁T ⟨(x : G), hx⟩) = QuotientGroup.mk t
    have : Subgroup.inclusion hT₁T ⟨(x : G), hx⟩ = x := rfl
    rw [this, ← hnx, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  let e : ↥T₁ ≃* ↥T ⧸ Nt := MulEquiv.ofBijective g₁ ⟨hg₁inj, hg₁surj⟩
  let g₂ : ↥R →* ↥T ⧸ Nt := (QuotientGroup.mk' Nt).comp (Subgroup.inclusion hRT)
  have hg₂inj : Function.Injective g₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : Subgroup.inclusion hRT x ∈ Nt :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hxJ : (x : G) ∈ T ⊓ J := hxN
    have : (x : G) ∈ R ⊓ J := ⟨x.2, hxJ.2⟩
    rw [hRJ, mem_bot] at this
    exact Subtype.ext this
  let ψ : ↥R →* ↥T₁ := (e.symm : ↥T ⧸ Nt →* ↥T₁).comp g₂
  have hψ : Function.Injective ψ := e.symm.injective.comp hg₂inj
  rcases subgroup_of_dihedral hd ψ.range with h | h
  · exact Or.inl ((MonoidHom.ofInjective hψ).isCyclic.mpr h)
  · exact Or.inr (l31_isDihedral_of_equiv (MonoidHom.ofInjective hψ) h)

end Embed

section Final

variable {G : Type} [Group G] [Finite G]

theorem l31_le_O2Of_of_perfect {X K : Subgroup G} (hKX : K ≤ X) (hK : Group.IsPerfect ↥K) :
    K ≤ O2Of X := by
  have hK' : Group.IsPerfect ↥(K.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKX).symm.surjective
  have hle := CFSG.GH74.GLS.Stage1.Main.perfect_le_oResidual (K.subgroupOf X) hK'
  intro x hx
  exact ⟨⟨x, hKX hx⟩, hle hx, rfl⟩

theorem l31_Jx_le_O2Of (s : G) : Jx s ≤ O2Of (centralizer ({s} : Set G)) :=
  l31_le_O2Of_of_perfect (sSup_le fun _ hL => hL.1) (Stage2.Local.P27Br.Jx_isPerfect s)

theorem l31_a_nonCentral
    (hNCD : NonCentralDihedral) (hT1 : NonCentralT1)
    {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S)
    (hk : IsClassicalKind k) {J₀ R : Subgroup G} {s : G} (hR : IsPGroup 2 ↥R)
    (hs : IsNonCentralInvolution s) (hsR : s ∈ R) (hsZ : ∀ r ∈ R, r * s = s * r)
    (hcomm : ∀ x ∈ J₀, ∀ r ∈ R, x * r = r * x) (hJ₀ : J₀ ≤ O2Of (centralizer ({s} : Set G)))
    (hq : IsQuasisimple (↥J₀ ⧸ pPrimeCore 2 ↥J₀)) :
    IsCyclic ↥R ∨ IsDihedral ↥R := by
  classical
  have _ := hsR
  have hRC : R ≤ centralizer ({s} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hsZ r hr)
  obtain ⟨T, hT, hRT⟩ := l31_exists_sylow_ge hRC hR
  obtain ⟨T₁, hT₁T, hsup, hinf, hdih⟩ := hT1 G z k S hctx hk s hs T hT
  have hbot : R ⊓ Jx s = ⊥ :=
    l31_inf_eq_bot (hNCD G z k S hctx s hs) hJ₀ (inf_le_right.trans (l31_Jx_le_O2Of s))
      (hR.to_le inf_le_left) (fun x hx q hq' => hcomm x hx q hq'.1) hq
  exact l31_embed (hT.le.trans (Stage2.Local.P27Br.Jx_normalizes s)) hRT hT₁T hsup hinf hbot hdih

end Final

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

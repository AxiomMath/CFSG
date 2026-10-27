module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BStruct
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMoved
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

section CfgE3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

theorem cfg_of_plane63E3 {p : ℕ} {X : Type} [Group X] [Finite X] {P : Sylow p X} {x z : X}
    (hpl : Plane63E3 p X P x z) :
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B.Cfg p
      ((P : Subgroup X).map (QuotientGroup.mk' (primeComplementCore (G := X) p)))
      (x : X ⧸ primeComplementCore (G := X) p) (z : X ⧸ primeComplementCore (G := X) p) := by
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hPp : IsPGroup p (P : Subgroup X) := P.isPGroup'
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hxB : x ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_left (mem_zpowers x)
  have hzB : z ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_right (mem_zpowers z)
  have hBP : (zpowers x ⊔ zpowers z : Subgroup X) ≤ (P : Subgroup X) :=
    hpl.plane.isIsolatedPlane.1
  have hxP : x ∈ (P : Subgroup X) := hBP hxB
  have hzP : z ∈ (P : Subgroup X) := hBP hzB
  have hxp : x ^ p = 1 := hpl.plane.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hpl.plane.isElemAbelian.2 z hzB
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (zpowers x ⊔ zpowers z : Subgroup X) = zpowers x := by
      rw [h, zpowers_one_eq_bot, sup_bot_eq]
    have h2 : Nat.card (zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hprime.pos (orderOf_dvd_of_pow_eq_one hxp)
    have h3 := hpl.plane.card_eq
    rw [h1] at h3
    have h4 : p ^ 2 ≤ p := h3 ▸ h2
    have h5 : 1 < p := hprime.one_lt
    nlinarith
  have hzD : ¬ z ∈ D := by
    intro hzD
    have hD3 : ¬ p ∣ Nat.card D :=
      (Nat.Prime.coprime_iff_not_dvd hprime).mp (primeComplementCore_coprime p)
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    apply hD3
    rw [← hord, ← Subgroup.orderOf_mk z hzD]
    exact orderOf_dvd_natCard _
  refine ⟨hprime, hpl.five_le, ?_, mem_map_of_mem π hxP, mem_map_of_mem π hzP, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact isSylowOf_map_core hprime P
  ·
    show (x : X ⧸ D) ^ p = 1
    rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
  · show (z : X ⧸ D) ^ p = 1
    rw [← QuotientGroup.mk_pow, hzp, QuotientGroup.mk_one]
  ·
    intro h
    exact hzD ((QuotientGroup.eq_one_iff z).mp h)
  ·
    rintro _ ⟨g, hg, rfl⟩
    show (g : X ⧸ D) * z = z * g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact mem_centralizer_iff.mp hpl.z_central g hg
  ·
    rintro _ ⟨w, hw, rfl⟩ hcent hwp
    have hw1 : w ^ p = 1 := by
      apply eq_one_of_mk_eq_one hprime hPp (pow_mem hw p)
      show ((w ^ p : X) : X ⧸ D) = 1
      rw [QuotientGroup.mk_pow]
      exact hwp
    have hwc : w ∈ centralizer ((P : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro g hg
      have h1 := hcent (π g) (mem_map_of_mem π hg)
      have h2 : ((g * w * g⁻¹ * w⁻¹ : X) : X ⧸ D) = 1 := by
        change (π g * π w) = (π w * π g) at h1
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        show π g * π w * (π g)⁻¹ * (π w)⁻¹ = 1
        rw [h1]
        group
      have h3 : g * w * g⁻¹ * w⁻¹ = 1 := by
        refine eq_one_of_mk_eq_one hprime hPp ?_ h2
        exact P.mul_mem (P.mul_mem (P.mul_mem hg hw) (P.inv_mem hg)) (P.inv_mem hw)
      have h4 : g * w = w * g := by
        calc g * w = (g * w * g⁻¹ * w⁻¹) * (w * g) := by group
          _ = w * g := by rw [h3, one_mul]
      exact h4
    have hmem : w ∈ zpowers z := hpl.plane.center w hw hwc hw1
    exact (MonoidHom.map_zpowers π z) ▸ mem_map_of_mem π hmem
  ·
    intro E hEP hE hEx
    have hcentE : ∀ e ∈ E, ∃ g ∈ (P : Subgroup X), π g = e := by
      intro e he
      obtain ⟨g, hg, rfl⟩ := hEP he
      exact ⟨g, hg, rfl⟩
    set E' : Subgroup X := ((E.comap π) ⊓ (P : Subgroup X)) with hE'
    have hE'map : ∀ g ∈ E', π g ∈ E := fun g hg => hg.1
    have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
      intro a ha b hb
      have h1 : π a * π b = π b * π a :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨π a, hE'map a ha⟩ ⟨π b, hE'map b hb⟩)
      have h2 : ((a * b * a⁻¹ * b⁻¹ : X) : X ⧸ D) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        show π a * π b * (π a)⁻¹ * (π b)⁻¹ = 1
        rw [h1]
        group
      have h3 : a * b * a⁻¹ * b⁻¹ = 1 :=
        eq_one_of_mk_eq_one hprime hPp
          (P.mul_mem (P.mul_mem (P.mul_mem ha.2 hb.2) (P.inv_mem ha.2)) (P.inv_mem hb.2)) h2
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h3, one_mul]
    have hE'p : ∀ a ∈ E', a ^ p = 1 := by
      intro a ha
      refine eq_one_of_mk_eq_one hprime hPp (pow_mem ha.2 p) ?_
      show ((a ^ p : X) : X ⧸ D) = 1
      rw [QuotientGroup.mk_pow]
      exact hE.2 _ (hE'map a ha)
    have hE'el : IsElemAbelian p E' :=
      ⟨⟨⟨fun a b => Subtype.ext (hE'comm a a.2 b b.2)⟩⟩, hE'p⟩
    have hE'x : E' ≤ centralizer ({x} : Set X) := by
      intro a ha
      rw [mem_centralizer_singleton_iff]
      have h1 : π a * π x = π x * π a := hEx (π a) (hE'map a ha)
      have h2 : ((a * x * a⁻¹ * x⁻¹ : X) : X ⧸ D) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        show π a * π x * (π a)⁻¹ * (π x)⁻¹ = 1
        rw [h1]
        group
      have h3 : a * x * a⁻¹ * x⁻¹ = 1 :=
        eq_one_of_mk_eq_one hprime hPp
          (P.mul_mem (P.mul_mem (P.mul_mem ha.2 hxP) (P.inv_mem ha.2)) (P.inv_mem hxP)) h2
      have h4 : a * x = x * a := by
        calc a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
          _ = x * a := by rw [h3, one_mul]
      first | exact h4 | exact h4.symm
    have hsurj : Function.Surjective (fun a : E' => (⟨π a, hE'map a a.2⟩ : E)) := by
      rintro ⟨e, he⟩
      obtain ⟨g, hg, rfl⟩ := hcentE e he
      exact ⟨⟨g, ⟨he, hg⟩⟩, rfl⟩
    have hcardE : Nat.card E ≤ Nat.card E' := Nat.card_le_card_of_surjective _ hsurj
    obtain ⟨k, hk⟩ : ∃ k, Nat.card E' = p ^ k := by
      have : IsPGroup p E' := hPp.to_le inf_le_right
      exact this.exists_card_eq
    have hk2 : k ≤ 2 :=
      (CFSG.SectionRank.le_pRank hprime.one_lt hE'x hE'el hk).trans hpl.rank_centralizer
    calc Nat.card E ≤ Nat.card E' := hcardE
      _ = p ^ k := hk
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hprime.pos hk2
  ·
    exact primeComplementCore_quotient_eq_bot p
  ·
    exact hpl.catalog.of_surjective π (QuotientGroup.mk'_surjective D)

end CfgE3

section BetaE3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem betaStructure_E3 (h64 : CFSG.LocalAnalysis.RankFourTheoremC.KFactCenterCyclicGeFive)
    (h610 : GL83.I_6_10_1) (h7131 : GL83.I_7_13_1)
    (hsplit : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFactSylowSplit)
    {p : ℕ} {X : Type} [Group X] [Finite X] {P : Sylow p X} {x z : X}
    (hpl : Plane63E3 p X P x z)
    (hcomp : ∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K) :
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.BetaStructure p X P x z := by
  have hcfg := cfg_of_plane63E3 hpl
  have hprime := hpl.prime
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  obtain ⟨L, K, hL, hK, hLK⟩ := hcomp
  have hcomp' : ∃ C C' : ComponentIndex (X ⧸ D), C ≠ C' :=
    ⟨⟨L, (CFSG.isComponent_iff_open L).2 hL⟩, ⟨K, (CFSG.isComponent_iff_open K).2 hK⟩,
      fun h => hLK (congrArg Subtype.val h)⟩
  obtain ⟨-, hcyc, hZ, hcard, htrans, hzl, hC⟩ :=
    hcfg.struct h64 h610 (fun C hC => hcfg.isCyclic_inf_of_moved h64 hC) hcomp'
  refine ⟨hcard, hZ, htrans, hzl, ?_⟩
  have hR : Open.pRank p ((P : Subgroup X).map (QuotientGroup.mk' D)) ≤ p :=
    pRank_le_of_beta hprime hpl.five_le hcfg.sylow hcfg.x_mem hcfg.x_pow
      (fun E hE hEe hxE => hcfg.card_le_of_normalizes hE hEe hxE) hcfg.catalog hcard hZ htrans hcyc
      hC (fun C => hcfg.dvd_card_comp C) h7131 hsplit
  refine le_trans ?_ hR
  refine CFSG.GH74.Uniqueness.SU.SU1.pRank_le_of fun E hEP hE k hk => ?_
  have hEp : IsPGroup p E := (P.isPGroup').to_le hEP
  have hEm : IsElemAbelian p (E.map (QuotientGroup.mk' D)) := by
    haveI := hE.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    show (QuotientGroup.mk' D e) ^ p = 1
    rw [← map_pow, hE.2 e he, map_one]
  have hcardm : Nat.card (E.map (QuotientGroup.mk' D)) = p ^ k := by
    rw [card_map_mk_eq hprime hEp, hk]
  exact CFSG.SectionRank.le_pRank hprime.one_lt (Subgroup.map_mono hEP) hEm hcardm

end BetaE3

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

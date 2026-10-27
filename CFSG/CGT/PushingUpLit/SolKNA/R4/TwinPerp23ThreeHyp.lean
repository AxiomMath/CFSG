module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeData
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Odd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeComp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

namespace Perp23

namespace Three

section Conj

theorem tightInO2_conj' {G : Type} [Group G] [Finite G] (g a a' x x' : G) (ha : g * a * g⁻¹ = a')
    (hx : g * x * g⁻¹ = x') (hxC : x ∈ Subgroup.centralizer ({a} : Set G))
    (hxC' : x' ∈ Subgroup.centralizer ({a'} : Set G))
    (h : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({a} : Set G))) (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({a} : Set G))))) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({a'} : Set G))) (⟨x', hxC'⟩ : ↥(Subgroup.centralizer ({a'} : Set G)))) := by
  subst ha hx
  exact tightInO2_conj g a hxC h

end Conj

section Hyp


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  (d : Data r n Y R S t)

namespace Data

include d

theorem e2_of_centralizes (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) {a : Y}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haR : ∀ x ∈ d.D.F.ρ.R, x * a = a * x)
    (haR' : ∀ x ∈ d.D.F.ρ'.R, x * a = a * x) (htc : t ∈ Subgroup.centralizer ({a} : Set Y)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set Y)))
      (⟨t, htc⟩ : ↥(Subgroup.centralizer ({a} : Set Y)))) := by
  classical
  have hStd : TwinStdR r n Y R S t :=
    ⟨d.h.core.card, d.h.core.simple, d.h.core.nonab, d.h.core.datum, d.h.core.quat, d.h.core.gen,
      d.h.core.oddFree, d.h.core.hyp, d.h.core.aEmpty, d.h.core.twin⟩
  obtain ⟨S₀, hStd₀⟩ := hStd.core
  have hRc : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hZ : Subgroup.center Y = ⊥ := d.h.center_eq_bot
  have haK : a ∈ trivialOnQuot (tightCore R) :=
    TwinADescent3.mem_tq_of_sylCent d.hΩ d.h2all d.hKΩ
      ⟨d.D.F.ρ.R, d.hRK, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (haR x hx)⟩
  have haK' : a ∈ trivialOnQuot d.K' :=
    TwinADescent3.mem_tq_of_sylCent d.hΩ d.h2all d.hK'Ω
      ⟨d.D.F.ρ'.R, d.hRK', fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (haR' x hx)⟩
  exact inO2_cent_of_twin_R h4 hT hStd₀ hRc hZ ha2 ha1
    (mem_centralizerModOdd_of_trivialOnQuot haK) htc (K' := d.K')
    (by rw [hRc]; exact d.hK') (by rw [hRc]; exact d.hne) haK'

theorem K_le_centralizer : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) :=
  CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer d.hz

theorem K'_le_centralizer : d.K' ≤ Subgroup.centralizer ({t} : Set Y) :=
  CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer d.hz'

theorem sup_le_centralizer : tightCore R ⊔ d.K' ≤ Subgroup.centralizer ({t} : Set Y) :=
  sup_le d.K_le_centralizer d.K'_le_centralizer

theorem conj_mem_sup : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ x ∈ tightCore R ⊔ d.K',
    c * x * c⁻¹ ∈ tightCore R ⊔ d.K' := by
  classical
  intro c hc x hx
  have hhull : tightCore R ⊔ d.K' = ⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R))
      (tightCore R), J := by
    refine le_antisymm (sup_le (le_iSup₂_of_le (tightCore R) ?_ le_rfl)
      (le_iSup₂_of_le d.K' d.hK' le_rfl)) (iSup₂_le fun J hJ => ?_)
    · exact mem_twinSet_self d.hKΩ d.hz
    · rw [d.hpair] at hJ
      rcases hJ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  rw [hhull] at hx ⊢
  exact d.h.conj_mem_twinHull hc hx

theorem oddCoreIn_K_le : oddCoreIn (tightCore R) ≤ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
  oddCoreIn_le_of_isSubnormal
    (d.h.partIHypG.cls.isSubnormal_of_uniqueInvolution d.hKΩ d.hz)

theorem oddCoreIn_K'_le : oddCoreIn d.K' ≤ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
  oddCoreIn_le_of_isSubnormal
    (d.h.partIHypG.cls.isSubnormal_of_uniqueInvolution d.hK'Ω d.hz')

theorem comm_KK' : ∀ a ∈ tightCore R, ∀ b ∈ d.K',
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
  intro a ha b hb
  have hm : ⁅a, b⁆ ∈ ⁅tightCore R, d.K'⁆ := Subgroup.commutator_mem_commutator ha hb
  have h1 := (Sec6Gen.comm_le_oddCore_of_twin d.hΩ d.hKΩ d.hK'Ω d.hne.symm d.hz d.hz' hm).1
  have h2 := d.oddCoreIn_K_le h1
  rwa [commutatorElement_def] at h2

theorem tightInO2_twinHull {x : Y} (hx : x ∈ tightCore R ⊔ d.K') :
    TightInO2 (oddQuotMk t ⟨x, d.sup_le_centralizer hx⟩) := by
  classical
  set K := tightCore R with hKdef
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hsupC := d.sup_le_centralizer
  have hnormC : ((K ⊔ d.K').subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hsupC]
    intro y c hy hc
    exact d.conj_mem_sup c hc y hy
  have hQn : (modOdd t (K ⊔ d.K')).Normal :=
    hnormC.map (oddQuotMk t) (QuotientGroup.mk'_surjective _)
  refine ⟨modOdd t (K ⊔ d.K'), hQn, ?_, oddQuotMk_mem_modOdd hx (hsupC hx)⟩
  have hKN : K ≤ Subgroup.normalizer (d.K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin d.hΩ d.hKΩ d.hK'Ω d.hne.symm d.hz d.hz'
  have hone : ∀ {y : Y} (hyC : y ∈ C), y ∈ oddCoreIn C → oddQuotMk t ⟨y, hyC⟩ = 1 := by
    intro y hyC hy
    rw [oddQuotMk_eq_one_iff]
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = ⟨y, hyC⟩ := Subtype.ext hzy
    rw [← this]
    exact hz
  have h2pow : ∀ k : ↥C, (k : Y) ∈ K ⊔ d.K' → ∃ i : ℕ, (oddQuotMk t k) ^ (2 ^ i) = 1 := by
    intro k hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K d.K' hKN] at hk
    obtain ⟨a, ha, b, hb, hab⟩ := hk
    obtain ⟨i₁, hi₁⟩ := exists_pow_mem_oddCoreIn (d.h2all K d.hKΩ) ha
    obtain ⟨i₂, hi₂⟩ := exists_pow_mem_oddCoreIn (d.h2all _ d.hK'Ω) hb
    refine ⟨i₁ + i₂, ?_⟩
    have haC : a ∈ C := d.K_le_centralizer ha
    have hbC : b ∈ C := d.K'_le_centralizer hb
    have hk' : k = ⟨a, haC⟩ * ⟨b, hbC⟩ := Subtype.ext hab.symm
    have hpa : (oddQuotMk t ⟨a, haC⟩) ^ (2 ^ (i₁ + i₂)) = 1 := by
      rw [← map_pow]
      have hmem : a ^ (2 ^ (i₁ + i₂)) ∈ oddCoreIn C := by
        refine d.oddCoreIn_K_le ?_
        rw [pow_add, pow_mul]
        exact Subgroup.pow_mem _ hi₁ _
      have e : (⟨a, haC⟩ : ↥C) ^ (2 ^ (i₁ + i₂)) = ⟨a ^ (2 ^ (i₁ + i₂)), Subgroup.pow_mem _ haC _⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact hone _ hmem
    have hpb : (oddQuotMk t ⟨b, hbC⟩) ^ (2 ^ (i₁ + i₂)) = 1 := by
      rw [← map_pow]
      have hmem : b ^ (2 ^ (i₁ + i₂)) ∈ oddCoreIn C := by
        refine d.oddCoreIn_K'_le ?_
        rw [add_comm, pow_add, pow_mul]
        exact Subgroup.pow_mem _ hi₂ _
      have e : (⟨b, hbC⟩ : ↥C) ^ (2 ^ (i₁ + i₂)) = ⟨b ^ (2 ^ (i₁ + i₂)), Subgroup.pow_mem _ hbC _⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact hone _ hmem
    have hcomm : oddQuotMk t ⟨a, haC⟩ * oddQuotMk t ⟨b, hbC⟩ =
        oddQuotMk t ⟨b, hbC⟩ * oddQuotMk t ⟨a, haC⟩ := by
      have hc := d.comm_KK' a ha b hb
      have h1 : oddQuotMk t (⟨a, haC⟩ * ⟨b, hbC⟩ * ⟨a, haC⟩⁻¹ * ⟨b, hbC⟩⁻¹) = 1 := by
        have e : (⟨a, haC⟩ * ⟨b, hbC⟩ * ⟨a, haC⟩⁻¹ * ⟨b, hbC⟩⁻¹ : ↥C) =
            ⟨a * b * a⁻¹ * b⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haC hbC)
              (Subgroup.inv_mem _ haC)) (Subgroup.inv_mem _ hbC)⟩ := Subtype.ext rfl
        rw [e]
        exact hone _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc oddQuotMk t ⟨a, haC⟩ * oddQuotMk t ⟨b, hbC⟩
          = (oddQuotMk t ⟨a, haC⟩ * oddQuotMk t ⟨b, hbC⟩ * (oddQuotMk t ⟨a, haC⟩)⁻¹ *
              (oddQuotMk t ⟨b, hbC⟩)⁻¹) * (oddQuotMk t ⟨b, hbC⟩ * oddQuotMk t ⟨a, haC⟩) := by
            group
        _ = oddQuotMk t ⟨b, hbC⟩ * oddQuotMk t ⟨a, haC⟩ := by rw [h1, one_mul]
    rw [hk', map_mul, Commute.mul_pow hcomm, hpa, hpb, mul_one]
  intro q
  obtain ⟨k, hk, hkq⟩ := q.2
  obtain ⟨i, hi⟩ := h2pow k (Subgroup.mem_subgroupOf.mp hk)
  refine ⟨i, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hkq]
  exact hi

theorem u_ne_one (he1 : d.D.ce ≠ 1) : d.D.u ≠ 1 := by
  intro h
  have h1 := e_mul_j d.D d.hc
  rw [h] at h1
  exact ce_ne_j d.D d.hc ((eq_inv_of_mul_eq_one_left h1).trans
    (inv_eq_of_mul_eq_one_right d.D.j_sq))

theorem u_ne_t : d.D.u ≠ t := by
  intro h
  have h1 := e_mul_j d.D d.hc
  rw [h] at h1
  apply ce_ne_t_mul_j d.D d.hc
  calc d.D.ce = (d.D.ce * d.D.F.j) * d.D.F.j⁻¹ := by group
    _ = t * d.D.F.j := by rw [h1, inv_eq_of_mul_eq_one_right d.D.j_sq]

theorem j_ne_u (he1 : d.D.ce ≠ 1) : d.D.F.j ≠ d.D.u := by
  intro h
  have h1 := e_mul_j d.D d.hc
  rw [← h] at h1
  apply he1
  have h2 : d.D.ce * d.D.F.j = 1 * d.D.F.j := by rw [one_mul]; exact h1
  exact mul_right_cancel h2

theorem u_mem_sup : d.D.u ∈ tightCore R ⊔ d.K' :=
  (tightCore R ⊔ d.K').mul_mem (Subgroup.mem_sup_left d.D.b_mem_K)
    ((tightCore R ⊔ d.K').inv_mem (Subgroup.mem_sup_right d.D.b'_mem_K'))

theorem t_mem_centralizer_ce : t ∈ Subgroup.centralizer ({d.D.ce} : Set Y) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.D.t_mem_W _ d.D.e_mem_W)

theorem hyp51At_t (he1 : d.D.ce ≠ 1) : Hyp51At (bGrp d.D) t := by
  have huC : d.D.u ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.D.u_mem_W _ d.D.t_mem_W)
  refine hyp51At_of_centralizes (isElemAbelian_bGrp d.D d.hc) (t_mem_bGrp d.D) (t_ne_one d.D)
    (u_mem_bGrp d.D d.hc) (d.u_ne_one he1) d.u_ne_t huC ?_
  intro L hL y hy
  exact commute_of_tightInO2 (d.tightInO2_twinHull d.u_mem_sup) hL y hy

theorem hyp51At_e (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) (he1 : d.D.ce ≠ 1) :
    Hyp51At (bGrp d.D) d.D.ce := by
  have htC := d.t_mem_centralizer_ce
  have hin := d.e2_of_centralizes h4 hT (a := d.D.ce) (ce_mul_self d.D d.hc) he1
    (fun x hx => d.D.e_central d.hΩ d.hW d.ctx he1 (d.R_le_normalizer hx))
    (fun x hx => d.D.e_central d.hΩ d.hW d.ctx he1 (d.R'_le_normalizer hx)) htC
  refine hyp51At_of_centralizes (isElemAbelian_bGrp d.D d.hc) (e_mem_bGrp d.D) he1
    (t_mem_bGrp d.D) (t_ne_one d.D) (ce_ne_t d.D d.hc).symm htC ?_
  intro L hL y hy
  exact commute_of_tightInO2 hin hL y hy

theorem e2_et (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) (he1 : d.D.ce ≠ 1)
    (htc : t ∈ Subgroup.centralizer ({d.D.ce * t} : Set Y)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({d.D.ce * t} : Set Y)))
      (⟨t, htc⟩ : ↥(Subgroup.centralizer ({d.D.ce * t} : Set Y)))) := by
  have hce := ce_mul_self d.D d.hc
  have hct : t * d.D.ce = d.D.ce * t := d.hc _ d.D.t_mem_W _ d.D.e_mem_W
  have ha2 : (d.D.ce * t) * (d.D.ce * t) = 1 := by
    calc (d.D.ce * t) * (d.D.ce * t) = d.D.ce * (t * d.D.ce) * t := by group
      _ = d.D.ce * (d.D.ce * t) * t := by rw [hct]
      _ = (d.D.ce * d.D.ce) * (t * t) := by group
      _ = 1 := by rw [hce, d.D.hzK.sq, one_mul]
  have ha1 : d.D.ce * t ≠ 1 := by
    intro h
    exact ce_ne_t d.D d.hc ((eq_inv_of_mul_eq_one_left h).trans
      (inv_eq_of_mul_eq_one_right d.D.hzK.sq))
  have hR : ∀ x ∈ d.D.F.ρ.R, x * (d.D.ce * t) = (d.D.ce * t) * x := by
    intro x hx
    have h1 := d.D.e_central d.hΩ d.hW d.ctx he1 (d.R_le_normalizer hx)
    have h2 : x * t = t * x := (d.hz.commute_of_mem (d.hRK.1 hx)).symm
    calc x * (d.D.ce * t) = (x * d.D.ce) * t := by group
      _ = (d.D.ce * x) * t := by rw [h1]
      _ = d.D.ce * (x * t) := by group
      _ = d.D.ce * (t * x) := by rw [h2]
      _ = (d.D.ce * t) * x := by group
  have hR' : ∀ x ∈ d.D.F.ρ'.R, x * (d.D.ce * t) = (d.D.ce * t) * x := by
    intro x hx
    have h1 := d.D.e_central d.hΩ d.hW d.ctx he1 (d.R'_le_normalizer hx)
    have h2 : x * t = t * x := (d.hz'.commute_of_mem (d.hRK'.1 hx)).symm
    calc x * (d.D.ce * t) = (x * d.D.ce) * t := by group
      _ = (d.D.ce * x) * t := by rw [h1]
      _ = d.D.ce * (x * t) := by group
      _ = d.D.ce * (t * x) := by rw [h2]
      _ = (d.D.ce * t) * x := by group
  exact d.e2_of_centralizes h4 hT ha2 ha1 hR hR' htc

theorem hyp51At_u (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) (he1 : d.D.ce ≠ 1) :
    Hyp51At (bGrp d.D) d.D.u := by
  have hej := e_mul_j d.D d.hc
  have hct : t * d.D.ce = d.D.ce * t := d.hc _ d.D.t_mem_W _ d.D.e_mem_W
  have htc : t ∈ Subgroup.centralizer ({d.D.ce * t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc t * (d.D.ce * t) = (t * d.D.ce) * t := by group
        _ = (d.D.ce * t) * t := by rw [hct])
  have hin := d.e2_et h4 hT he1 htc
  have hgu : (d.D.F.ρ.r * d.D.F.ρ₃.r) * (d.D.ce * t) * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹ = d.D.u := by
    calc (d.D.F.ρ.r * d.D.F.ρ₃.r) * (d.D.ce * t) * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹
        = ((d.D.F.ρ.r * d.D.F.ρ₃.r) * d.D.ce * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹) *
          ((d.D.F.ρ.r * d.D.F.ρ₃.r) * t * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹) := by group
      _ = d.D.ce * d.D.F.j := by rw [g0_e d.D d.hc, g0_t d.D d.hc]
      _ = d.D.u := hej
  have hjC : d.D.F.j ∈ Subgroup.centralizer ({d.D.u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.D.j_mem_W _ d.D.u_mem_W)
  have hin' := tightInO2_conj' (d.D.F.ρ.r * d.D.F.ρ₃.r) (d.D.ce * t) d.D.u t d.D.F.j hgu
    (g0_t d.D d.hc) htc hjC hin
  refine hyp51At_of_centralizes (isElemAbelian_bGrp d.D d.hc) (u_mem_bGrp d.D d.hc)
    (d.u_ne_one he1) (j_mem_bGrp d.D) (j_ne_one d.D) (d.j_ne_u he1) hjC ?_
  intro L hL y hy
  exact commute_of_tightInO2 hin' hL y hy

theorem hyp51_bGrp (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) (he1 : d.D.ce ≠ 1) :
    Hyp51 (bGrp d.D) := by
  refine ExactLayer.hyp51_of_orbitReps (isElemAbelian_bGrp d.D d.hc) (card_bGrp d.D d.hc he1)
    (R := {t, d.D.u, d.D.ce}) ?_ ?_
  · intro x hx
    rcases hx with rfl | rfl | rfl
    · exact d.hyp51At_t he1
    · exact d.hyp51At_u h4 hT he1
    · exact d.hyp51At_e h4 hT he1
  · intro x hx hx1
    obtain ⟨g, hg, h⟩ := exists_normalizer_conj_of_mem_bGrp d.D d.hΩ d.hW d.ctx hx hx1
    rcases h with h | h | h
    · exact ⟨t, by simp, g, hg, h⟩
    · exact ⟨d.D.u, by simp, g, hg, h⟩
    · exact ⟨d.D.ce, by simp, g, hg, h⟩

end Data

end Hyp

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4

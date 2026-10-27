module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3Cent
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.exists_swap (hF : E3Frame n R S t J u)
    (hOJ : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ g' : Y, conjSub g' (tightCore R) = J ∧ conjSub g' J = tightCore R ∧
      g' * t * g'⁻¹ = u ∧ g' * u * g'⁻¹ = t := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer
  obtain ⟨gs, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub gs R) = J := by rw [← conjSub_tightCore, hgJ]
  have hCJ : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), conjSub c J = J := by
    intro c hc'
    have h1 := hs.large.datum.le_normalizer_core hc'
    rw [hcore] at h1
    exact mem_normalizer_iff_conjSub_eq.mp h1
  obtain ⟨g₀, hg₀'⟩ := hJn.1
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have hJ₁ : conjSub g₀ J ∈ omegaNbr Ω J := by
    have h1 := omegaNbr_conj hc hJn g₀
    rwa [hg₀] at h1
  obtain ⟨l₁, hl₁, hl₁J⟩ := hOJ hJ₁
  have hl₁C := hXC hl₁
  refine ⟨l₁⁻¹ * g₀, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg₀, hCJ _ ((Subgroup.centralizer _).inv_mem hl₁C)]
  · rw [conjSub_mul, ← hl₁J, conjSub_inv_conjSub]
  · have h1 := hd.isUniqueInvolution_core.conj (l₁⁻¹ * g₀)
    rw [conjSub_mul, hg₀, hCJ _ ((Subgroup.centralizer _).inv_mem hl₁C)] at h1
    exact h1.eq hF.inv
  · have h1 := hF.inv.conj (l₁⁻¹ * g₀)
    rw [conjSub_mul, ← hl₁J, conjSub_inv_conjSub] at h1
    exact h1.eq hd.isUniqueInvolution_core

theorem E3Frame.cent_or_cent_mul (hF : E3Frame n R S t J u)
    (hOJ : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {s : Y} (hs2 : s * s = 1)
    (hst : s * t = t * s) (hsJ : ∀ j ∈ J, s * j = j * s) :
    (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅s, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) ∨
      ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅u * s, y⁆ ∈
          oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hd.hypOmegaGen hF.maxAdj.1.1 hJn.1 hJn
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  have hXC : X ≤ C := hF.nbrGen_le_centralizer
  have hHX : secH R u = X.subgroupOf C := le_antisymm hF.secH_le_nbrGen (hF.nbrGen_le_secH hOJ)
  obtain ⟨gs, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub gs R) = J := by rw [← conjSub_tightCore, hgJ]
  have hCJ : ∀ c ∈ C, conjSub c J = J := by
    intro c hc'
    have h1 := hs.large.datum.le_normalizer_core hc'
    rw [hcore] at h1
    exact mem_normalizer_iff_conjSub_eq.mp h1
  have hCX : ∀ c ∈ C, conjSub c X = X := by
    intro c hc'
    rw [hXdef, E3.nbrGen_eq_omegaNbrGen hJΩ]
    exact conjSub_omegaNbrGen_of_conjSub_eq hc (hCJ c hc')
  have hXorb : E3.orbGen Ω J (tightCore R) = X := by
    apply le_antisymm
    · refine iSup₂_le fun M hM => ?_
      obtain ⟨l, hl, rfl⟩ := hM
      have h1 := omegaNbr_conj hc hK₀J l
      rw [hCJ l (hXC hl)] at h1
      exact le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj Ω J N}) => N) _ ⟨hJΩ, h1⟩
    · refine iSup₂_le fun M hM => ?_
      exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N) M (hOJ hM.2)
  obtain ⟨g', hg'K, hg'J, hgt, hgu⟩ := hF.exists_swap hOJ
  have hu2 : u * u = 1 := hF.inv.sq
  set s₀ := g'⁻¹ * s * g' with hs₀def
  have hs₀C : s₀ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have hu' : u = g'⁻¹ * t * g' := by rw [← hgu]; group
    rw [hu', hs₀def]
    calc g'⁻¹ * s * g' * (g'⁻¹ * t * g') = g'⁻¹ * (s * t) * g' := by group
      _ = g'⁻¹ * (t * s) * g' := by rw [hst]
      _ = g'⁻¹ * t * g' * (g'⁻¹ * s * g') := by group
  have hs₀K : ∀ k ∈ tightCore R, s₀ * k * s₀⁻¹ = k := by
    intro k hk
    have hkJ : g' * k * g'⁻¹ ∈ J := by
      rw [← hg'K]
      exact conj_mem_conjSub hk
    have h1 := hsJ _ hkJ
    calc s₀ * k * s₀⁻¹ = g'⁻¹ * (s * (g' * k * g'⁻¹)) * s⁻¹ * g' := by rw [hs₀def]; group
      _ = g'⁻¹ * ((g' * k * g'⁻¹) * s) * s⁻¹ * g' := by rw [h1]
      _ = k := by group
  have hs₀2 : s₀ * s₀ = 1 := by
    calc s₀ * s₀ = g'⁻¹ * (s * s) * g' := by rw [hs₀def]; group
      _ = 1 := by rw [hs2]; group
  set d : C := ⟨s₀, hs₀C⟩ with hddef
  have hdd : d * d = 1 := Subtype.ext hs₀2
  have hdH : conjSub d (secH R u) = secH R u := by
    rw [hHX, conjSub_subgroupOf C d X]
    exact congrArg (fun A => A.subgroupOf C) (hCX s₀ hs₀C)
  have hdx : ∀ x ∈ secH R u, d * x * d⁻¹ ∈ secH R u := fun x hx => hdH ▸ conj_mem_conjSub hx
  set β := E3.conjQ (secH R u) d hdH with hβdef
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun q => ?_
    refine QuotientGroup.induction_on q fun x => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    show β (β (QuotientGroup.mk' _ x)) = QuotientGroup.mk' _ x
    rw [hβdef, E3.conjQ_mk, E3.conjQ_mk]
    congr 1
    apply Subtype.ext
    rw [E3.conjQ_val, E3.conjQ_val]
    calc d * (d * (x : C) * d⁻¹) * d⁻¹ = (d * d) * (x : C) * (d * d)⁻¹ := by group
      _ = x := by rw [hdd]; group
  have hβK : ∀ k ∈ tightCore (secR R u), β k = k := by
    rw [hF.tightCore_secR]
    rintro _ ⟨k, hk, rfl⟩
    rw [hβdef, E3.conjQ_mk]
    congr 1
    apply Subtype.ext
    rw [E3.conjQ_val]
    apply Subtype.ext
    exact hs₀K _ (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hk))
  have horb : E3.orbGen Ω (tightCore R) J = conjSub g' X := by
    have h1 := E3.orbGen_conj hc hJΩ (J := tightCore R) g'
    rwa [hg'J, hg'K, hXorb] at h1
  have hodd : oddCoreOf (conjSub g' X) = conjSub g' (oddCoreOf X) :=
    Vtx.oddCoreOf_map_of_inj (MulAut.conj g').toMonoidHom (MulAut.conj g').injective X
  have hcomm : ∀ (e : C) (he : e ∈ secH R u), (∀ x (hx : x ∈ secH R u),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
        (⟨d * x * d⁻¹, hdx x hx⟩ : ↥(secH R u)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
        (⟨e * x * e⁻¹, (secH R u).mul_mem ((secH R u).mul_mem he hx)
          ((secH R u).inv_mem he)⟩ : ↥(secH R u))) →
      ∀ y ∈ E3.orbGen Ω (tightCore R) J,
        ⁅g' * ((e : Y)⁻¹ * s₀) * g'⁻¹, y⁆ ∈ oddCoreOf (E3.orbGen Ω (tightCore R) J) := by
    intro e he h y hy
    have hH := E3.comm_mem_oddCoreOf he hdx h
    have hX : ∀ x ∈ X, ⁅(e : Y)⁻¹ * s₀, x⁆ ∈ oddCoreOf X := by
      intro x hx
      have hxH : (⟨x, hXC hx⟩ : C) ∈ secH R u := by
        rw [hHX]
        exact Subgroup.mem_subgroupOf.mpr hx
      have h1 := hH _ hxH
      rw [hHX] at h1
      have h2 := Subgroup.mem_map_of_mem C.subtype h1
      rw [← Vtx.oddCoreOf_map_of_inj C.subtype Subtype.val_injective,
        Subgroup.map_subgroupOf_eq_of_le hXC, map_commutatorElement] at h2
      exact h2
    rw [horb, mem_conjSub_iff] at hy
    rw [horb, hodd]
    have h3 := conj_mem_conjSub (n := g') (hX _ hy)
    convert h3 using 1
    simp only [commutatorElement_def]
    group
  rcases h163 β hβ2 hβK with h1 | h1
  ·
    left
    intro y hy
    have h2 := hcomm 1 (secH R u).one_mem (fun x hx => by
      have h3 := congrArg (fun γ : MulAut (SecQ R u) => γ (QuotientGroup.mk' _ ⟨x, hx⟩)) h1
      simp only [MulAut.one_apply] at h3
      rw [hβdef, E3.conjQ_mk] at h3
      refine Eq.trans rfl (h3.trans ?_)
      congr 1
      apply Subtype.ext
      simp) y hy
    convert h2 using 2
    rw [hs₀def]
    simp only [OneMemClass.coe_one, inv_one, one_mul]
    group
  ·
    right
    intro y hy
    have h2 := hcomm ⟨t, htu⟩ ht (fun x hx => by
      have h3 := congrArg (fun γ : MulAut (SecQ R u) => γ (QuotientGroup.mk' _ ⟨x, hx⟩)) h1
      simp only [MulAut.conj_apply] at h3
      rw [hβdef, E3.conjQ_mk] at h3
      refine Eq.trans rfl (h3.trans ?_)
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl) y hy
    convert h2 using 2
    have hut : g' * t⁻¹ * g'⁻¹ = u := by
      have h4 : (g' * t * g'⁻¹)⁻¹ = u⁻¹ := by rw [hgt]
      have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      rw [← hu', ← h4]
      group
    calc u * s = (g' * t⁻¹ * g'⁻¹) * (g' * (g'⁻¹ * s * g') * g'⁻¹) := by rw [hut]; group
      _ = g' * (t⁻¹ * s₀) * g'⁻¹ := by rw [hs₀def]; group

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

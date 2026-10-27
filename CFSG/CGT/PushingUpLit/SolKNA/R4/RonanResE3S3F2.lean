module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F1
public import CFSG.ClassicalInvolution.Q3.TL4E3Rank1O
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  (transitive_of_maxOrb piGen le_piGen piGen_le piGen_conj)
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.eq_one_of_le_centralizer (hF : E3FrameR r n R S t J u) {w : Y}
    (h1 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤
      Subgroup.centralizer ({w} : Set Y))
    (h2 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
      Subgroup.centralizer ({w} : Set Y)) : w = 1 := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hFam := hF.graphFam
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hF.large.cls.2.1
  have hY := hF.lemma1710.generate hgen g (by rw [hgJ]; exact mem_orbOf_self _ _)
  have hπ : conjSub g '' orbOf (TC.nbrAdj Ω) (tightCore R) J =
      orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    have h1 := isMaxOrb_conj hFam hF.maxAdj.2 g
    rw [hgJ] at h1
    exact maxOrb_unique hFam hJn.1 h1 (orbOf_mem_maxOrbs hFam hF.maxAdj.1 hF.maxAdj.2)
  have htop : (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({w} : Set Y) := by
    rw [← hY]
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | hM
    · exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) (tightCore R) J) => N)
        M hM).trans h1
    · rw [hπ] at hM
      exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N)
        M hM).trans h2
  have hwZ : w ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top y))
  rw [hF.large.center] at hwZ
  exact hwZ

theorem E3FrameR.orbGen_core_le_centralizer (hF : E3FrameR r n R S t J u) :
    E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤
      Subgroup.centralizer ({t} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hNt : nbrGen (TC.nbrAdj Ω) (tightCore R) ≤ Subgroup.centralizer ({t} : Set Y) :=
    iSup₂_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM.2
      hd.isUniqueInvolution_core
  refine iSup₂_le fun M hM => ?_
  obtain ⟨l, hl, rfl⟩ := hM
  have hlK : conjSub l (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core (hNt hl))
  have h1 := omegaNbr_conj hc hF.maxAdj.1.2 l
  rw [hlK] at h1
  exact hF.le_centralizer_of_mem_omegaNbr hK₀Ω h1 hd.isUniqueInvolution_core

theorem E3FrameR.oddCoreOf_orbGen_core_le (hF : E3FrameR r n R S t J u) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) ≤
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  have hle := hF.orbGen_core_le_centralizer
  have hn : ((E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J).subgroupOf
      (Subgroup.centralizer ({t} : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc =>
      mem_normalizer_of_conjSub_eq (hF.conjSub_orbGen_core hc)
  exact Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_normal_subgroupOf hle hn)

theorem E3FrameR.eq_top_of_orbGen_le (hF : E3FrameR r n R S t J u) {H : Subgroup Y}
    (h1 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤ H)
    (h2 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤ H) : H = ⊤ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hFam := hF.graphFam
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hF.large.cls.2.1
  have hY := hF.lemma1710.generate hgen g (by rw [hgJ]; exact mem_orbOf_self _ _)
  have hπ : conjSub g '' orbOf (TC.nbrAdj Ω) (tightCore R) J =
      orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    have h3 := isMaxOrb_conj hFam hF.maxAdj.2 g
    rw [hgJ] at h3
    exact maxOrb_unique hFam hJn.1 h3 (orbOf_mem_maxOrbs hFam hF.maxAdj.1 hF.maxAdj.2)
  rw [eq_top_iff, ← hY]
  refine iSup₂_le fun M hM => ?_
  rcases hM with hM | hM
  · exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) (tightCore R) J) => N)
      M hM).trans h1
  · rw [hπ] at hM
    exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N)
      M hM).trans h2

theorem E3FrameR.cent_or_cent_conj (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) (g : Y) {s : Y} (hs2 : s * s = 1)
    (hsu : g⁻¹ * s * g ∈ Subgroup.centralizer ({u} : Set Y))
    (hsK : ∀ k ∈ tightCore R, g⁻¹ * s * g * k * (g⁻¹ * s * g)⁻¹ = k) :
    (∀ y ∈ conjSub g (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)),
        ⁅s, y⁆ ∈ oddCoreOf
          (conjSub g (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)))) ∨
      ∀ y ∈ conjSub g (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)),
        ⁅g * t * g⁻¹ * s, y⁆ ∈ oddCoreOf
          (conjSub g (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R))) := by
  classical
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set X := E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) with hXdef
  have hXC : X ≤ C := hF.orbGen_J_le_centralizer
  have hHX : secH R u = X.subgroupOf C := hF.secH_eq_orbGen
  have ht2 : t * t = 1 := hF.large.datum.isUniqueInvolution_core.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set s₀ := g⁻¹ * s * g with hs₀def
  have hs₀2 : s₀ * s₀ = 1 := by
    calc s₀ * s₀ = g⁻¹ * (s * s) * g := by rw [hs₀def]; group
      _ = 1 := by rw [hs2]; group
  set d : C := ⟨s₀, hsu⟩ with hddef
  have hdd : d * d = 1 := Subtype.ext hs₀2
  have hdH : conjSub d (secH R u) = secH R u := by
    rw [hHX, conjSub_subgroupOf C d X]
    exact congrArg (fun A => A.subgroupOf C) (hF.conjSub_orbGen_J hsu)
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
    exact hsK _ (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hk))
  have hodd : oddCoreOf (conjSub g X) = conjSub g (oddCoreOf X) :=
    Vtx.oddCoreOf_map_of_inj (MulAut.conj g).toMonoidHom (MulAut.conj g).injective X
  have hcomm : ∀ (e : C) (he : e ∈ secH R u), (∀ x (hx : x ∈ secH R u),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
        (⟨d * x * d⁻¹, hdx x hx⟩ : ↥(secH R u)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
        (⟨e * x * e⁻¹, (secH R u).mul_mem ((secH R u).mul_mem he hx)
          ((secH R u).inv_mem he)⟩ : ↥(secH R u))) →
      ∀ y ∈ conjSub g X, ⁅g * ((e : Y)⁻¹ * s₀) * g⁻¹, y⁆ ∈ oddCoreOf (conjSub g X) := by
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
    rw [mem_conjSub_iff] at hy
    rw [hodd]
    have h3 := conj_mem_conjSub (n := g) (hX _ hy)
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
    show g * t * g⁻¹ * s = g * (t⁻¹ * (g⁻¹ * s * g)) * g⁻¹
    rw [htinv]
    group

theorem E3FrameR.cent_or_cent_mul' (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {s : Y} (hs2 : s * s = 1)
    (hst : s * t = t * s) (hsJ : ∀ j ∈ J, s * j = j * s) :
    (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅s, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) ∨
      ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅u * s, y⁆ ∈
          oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) := by
  obtain ⟨g', hg'K, hg'J, hgt, hgu⟩ := hF.exists_swap'
  have hcl := hF.large.datum.hypOmegaGen.conjInvariant
  have horb : conjSub g' (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := by
    rw [← E3.orbGen_conj hcl hF.maxAdj.1.2.1 g', hg'J, hg'K]
  have hsu : g'⁻¹ * s * g' ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hu' : u = g'⁻¹ * t * g' := by rw [← hgu]; group
    rw [hu']
    calc g'⁻¹ * s * g' * (g'⁻¹ * t * g') = g'⁻¹ * (s * t) * g' := by group
      _ = g'⁻¹ * (t * s) * g' := by rw [hst]
      _ = g'⁻¹ * t * g' * (g'⁻¹ * s * g') := by group
  have hsK : ∀ k ∈ tightCore R, g'⁻¹ * s * g' * k * (g'⁻¹ * s * g')⁻¹ = k := by
    intro k hk
    have hkJ : g' * k * g'⁻¹ ∈ J := by
      rw [← hg'K]
      exact conj_mem_conjSub hk
    have h1 := hsJ _ hkJ
    calc g'⁻¹ * s * g' * k * (g'⁻¹ * s * g')⁻¹ = g'⁻¹ * (s * (g' * k * g'⁻¹)) * s⁻¹ * g' := by
          group
      _ = g'⁻¹ * ((g' * k * g'⁻¹) * s) * s⁻¹ * g' := by rw [h1]
      _ = k := by group
  rcases hF.cent_or_cent_conj htu ht h163 g' hs2 hsu hsK with h | h
  · left
    rw [← horb]
    exact h
  · right
    rw [← horb]
    rw [hgt] at h
    exact h

theorem E3FrameR.inv_off_orbit (hF : E3FrameR r n R S t J u) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hMπ : M ∉ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    {v : Y} (hv : IsUniqueInvolution M v) :
    v ≠ u ∧ J ≤ Subgroup.centralizer ({v} : Set Y) ∧
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
        Subgroup.centralizer ({v} : Set Y) ∧
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({v} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hF.maxAdj.1.1 hJn.1 hJn
  have hvu : v ≠ u := by
    intro hvu
    rw [hvu] at hv
    exact hM.2.1 ((TightLargeHypR.typeRFam hF.large).noTwins J hJΩ M ⟨hM.1, u, hF.inv, hv⟩)
  have hJM : J ∈ omegaNbr Ω M := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hJΩ hM.1 hM
  have hJv := hF.le_centralizer_of_mem_omegaNbr hM.1 hJM hv
  have hXv : E3.orbGen Ω J (tightCore R) ≤ Subgroup.centralizer ({v} : Set Y) := by
    refine iSup₂_le fun P hP => ?_
    obtain ⟨l, hl, rfl⟩ := hP
    have hPn : conjSub l (tightCore R) ∈ omegaNbr Ω J := by
      have h1 := omegaNbr_conj hc hK₀J l
      rwa [hF.conjSub_J_of_mem_centralizer (hF.nbrGen_le_centralizer hl)] at h1
    have hMP : M ∉ orbOf (TC.nbrAdj Ω) J (conjSub l (tightCore R)) := by
      rintro ⟨l', hl', hl'M⟩
      refine hMπ ⟨l' * l, (nbrGen (TC.nbrAdj Ω) J).mul_mem hl' hl, ?_⟩
      rw [conjSub_mul]
      exact hl'M
    have hadj := hF.sep ⟨hJΩ, hPn⟩ ⟨hJΩ, hM⟩ hMP
    have hPM : conjSub l (tightCore R) ∈ omegaNbr Ω M :=
      Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hadj.1 hadj.2.1 hadj.2
    exact hF.le_centralizer_of_mem_omegaNbr hM.1 hPM hv
  have hMK : M ∈ omegaNbr Ω (tightCore R) :=
    (hF.sep ⟨hJΩ, hK₀J⟩ ⟨hJΩ, hM⟩ fun h' => hMπ h').2
  exact ⟨hvu, hJv, hXv, E3.oddCore_le_centralizer_of_alpha (hF.alpha M hMK v hv)
    hd.isUniqueInvolution_core.ne_one⟩

theorem E3FrameR.eq_of_cent_modO (hF : E3FrameR r n R S t J u) {v : Y} (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hJv : J ≤ Subgroup.centralizer ({v} : Set Y))
    (hXv : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
      Subgroup.centralizer ({v} : Set Y))
    (hOv : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({v} : Set Y))
    (h : (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅v, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) ∨
      ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅v * u, y⁆ ∈
          oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) :
    v = u := by
  by_contra hvu
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set X₀ := E3.orbGen Ω (tightCore R) J with hX₀def
  have hd := hF.large.datum
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hOu : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
      Subgroup.centralizer ({u} : Set Y) :=
    E3.oddCore_le_centralizer_of_alpha (hF.alpha J hJn u hF.inv)
      hd.isUniqueInvolution_core.ne_one
  have hO₀ := hF.oddCoreOf_orbGen_core_le
  have hXu : E3.orbGen Ω J (tightCore R) ≤ Subgroup.centralizer ({u} : Set Y) :=
    hF.orbGen_J_le_centralizer
  have hNodd : Odd (Nat.card ↥(oddCoreOf X₀)) := oddCoreOf_odd_natCard X₀
  have hexact : ∀ w : Y, w * w = 1 → oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
      Subgroup.centralizer ({w} : Set Y) →
      (∀ y ∈ X₀, ⁅w, y⁆ ∈ oddCoreOf X₀) → X₀ ≤ Subgroup.centralizer ({w} : Set Y) := by
    intro w hw2 hwO hw y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (E3.commute_of_comm_mem_odd hNodd (Balance.isPGroup_zpowers_of_mul_self_eq_one hw2)
      (fun m hm => (Subgroup.mem_centralizer_singleton_iff.mp (hwO (hO₀ hm))).symm)
      (hw y hy)).symm
  rcases h with h0 | h0
  · exact hv1 (hF.eq_one_of_le_centralizer (hexact v hv2 hOv h0) hXv)
  · have hvuc : v * u = u * v :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hJv hF.inv.mem)).symm
    have hw2 : v * u * (v * u) = 1 := by
      calc v * u * (v * u) = v * (u * v) * u := by group
        _ = v * (v * u) * u := by rw [hvuc]
        _ = (v * v) * (u * u) := by group
        _ = 1 := by rw [hv2, hF.inv.sq, one_mul]
    have hwO : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
        Subgroup.centralizer ({v * u} : Set Y) := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 := Subgroup.mem_centralizer_singleton_iff.mp (hOv hx)
      have e2 := Subgroup.mem_centralizer_singleton_iff.mp (hOu hx)
      calc x * (v * u) = (x * v) * u := by group
        _ = v * (x * u) := by rw [e1]; group
        _ = v * u * x := by rw [e2]; group
    have hXvu : E3.orbGen Ω J (tightCore R) ≤ Subgroup.centralizer ({v * u} : Set Y) :=
      fun x hx => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have e1 := Subgroup.mem_centralizer_singleton_iff.mp (hXv hx)
        have e2 := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
        calc x * (v * u) = (x * v) * u := by group
          _ = v * (x * u) := by rw [e1]; group
          _ = v * u * x := by rw [e2]; group
    have h1 := hF.eq_one_of_le_centralizer (hexact (v * u) hw2 hwO h0) hXvu
    exact hvu (by
      calc v = v * u * u := by rw [mul_assoc, hF.inv.sq, mul_one]
        _ = u := by rw [h1, one_mul])

theorem E3FrameR.omegaNbr_subset_orbOf (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) := by
  intro M hM
  by_contra hMπ
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hF.large.datum.hypOmegaGen hM.1
  obtain ⟨hvu, hJv, hXv, hOv⟩ := hF.inv_off_orbit hM hMπ hv
  have hK₀X : tightCore R ≤ E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) :=
    le_iSup₂ (f := fun M (_ : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J
      (tightCore R)) => M) _ (mem_orbOf_self _ _)
  have htv : t * v = v * t := Subgroup.mem_centralizer_singleton_iff.mp
    (hXv (hK₀X hF.large.datum.isUniqueInvolution_core.mem))
  have hsJ : ∀ j ∈ J, v * j = j * v := fun j hj =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hJv hj)).symm
  have huv : u * v = v * u := Subgroup.mem_centralizer_singleton_iff.mp (hJv hF.inv.mem)
  rcases hF.cent_or_cent_mul' htu ht h163 hv.sq htv.symm hsJ with h | h
  · exact hvu (hF.eq_of_cent_modO hv.sq hv.ne_one hJv hXv hOv (Or.inl h))
  · rw [huv] at h
    exact hvu (hF.eq_of_cent_modO hv.sq hv.ne_one hJv hXv hOv (Or.inr h))

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

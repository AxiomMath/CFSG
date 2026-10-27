module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4X
public import CFSG.ClassicalInvolution.Q3.TL4Conn261
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Nbr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)
open scoped commutatorElement

@[expose] def TightLambdaCommR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ L ∈ Φ, ∀ M ∈ omegaNbr Φ L, Commutes L M

theorem tightSecNbrGenR_of_comm {r n : ℕ} (h : TightLambdaCommR r n) : TightSecNbrGenR r n := by
  intro X _ _ hn Φ hΦ hO hgen hA L hL htop
  have hc := h X hn Φ hΦ hO hgen hA L hL
  have hle : omegaNbrGen Φ L ≤ Subgroup.centralizer (L : Set X) := by
    refine iSup₂_le fun M hM m hm => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hc M hM l hl m hm
  rw [htop] at hle
  obtain ⟨-, P, hP, hPnc⟩ := hΦ.hyp.omega1 L hL
  apply hPnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb : (b : X) ∈ Subgroup.centralizer (L : Set X) := hle (Subgroup.mem_top _)
  exact (Subgroup.mem_centralizer_iff.mp hb) a (hP.1 a.2)

theorem mem_omegaNbr_of_le_centralizer_typeR {r : ℕ} {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A M : Subgroup X} (hA : A ∈ Φ) (hM : M ∈ Φ)
    (hne : M ≠ A) {x : X} (hx : IsUniqueInvolution A x)
    (hc : M ≤ Subgroup.centralizer ({x} : Set X)) : M ∈ omegaNbr Φ A := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := M) (IsPGroup.of_bot (p := 2)) bot_le
  exact ⟨hM, hne, P, mem_RSet_of_isSylow2In hM hP, hP.1, (hP.1.trans hc).trans
    (hΦ.tight A hA x hx)⟩

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.exists_sylow_RT (hs : TightStd8R r n Rd Sd z J S R T W t) :
    ∃ S₂ : Sylow 2 Y, R ≤ (S₂ : Subgroup Y) ∧ T ≤ (S₂ : Subgroup Y) ∧
      IsSylow2In ((S₂ : Subgroup Y) ⊓
        omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
        (omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  set X : Subgroup Y := omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
    with hXdef
  have hΩ := hs.hyp
  have hRN : ∀ r ∈ R, conjSub r X = X := fun r hr =>
    conjSub_omegaNbrGen_of_conjSub_eq hΩ.conjInvariant (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
  have hYN : X ⊔ R ≤ Subgroup.normalizer (X : Set Y) :=
    sup_le Subgroup.le_normalizer (fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRN r hr))
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have hTX : T ≤ X := hs.hT.2.1.trans hJX
  have hRT : IsPGroup 2 ↥(R ⊔ T) := S.isPGroup'.to_le (sup_le hs.hR.2.2 hs.hT.2.2)
  have hRTle : R ⊔ T ≤ X ⊔ R := sup_le le_sup_right (hTX.trans le_sup_left)
  obtain ⟨V, hV, hRTV⟩ := IsSylow2In.exists_ge hRT hRTle
  have hVX : IsSylow2In (V ⊓ X) X := AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hYN
  obtain ⟨S₂, hS₂⟩ := hV.2.1.exists_le_sylow
  have heq : (S₂ : Subgroup Y) ⊓ X = V ⊓ X :=
    hVX.2.2 _ inf_le_right S₂.isPGroup'.to_inf_left (inf_le_inf_right X hS₂)
  exact ⟨S₂, le_sup_left.trans (hRTV.trans hS₂), le_sup_right.trans (hRTV.trans hS₂), heq ▸ hVX⟩

theorem TightStd8R.eq_J_of_mem_X (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y)) (hTS₂ : T ≤ (S₂ : Subgroup Y))
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore Rd))
    (hLX : L ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hcard : 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup Y))) : L = J := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hP : Q3CL.PartIHypG Ω := hs.partIHypG
  obtain ⟨g, η₂, hη₂, hinv₂, hgW⟩ := exists_conj_eta hΩ.conjInvariant hs.hW.1 S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup Y := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup Y), s ∈ Subgroup.normalizer (W₂ : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup Y) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := Q3CL.T8.ctxOf hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    rw [← hgW]
    exact ⟨(muGroupConjEquivGen hΩ g W).symm.trans φ⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hs.hT.1 hs.hT.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  have hTD : T ∈ DSet Ω W₂ := ⟨hs.hT.1, fun x hx => hSN x (hTS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hTD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let ρJ : Rep Ω W₂ := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  have h611 : L ⊓ W₂ ∈ η₂ := Sec6Gen.l6_11Gen Y Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := Sec6Gen.isPGroup_of_mem_USet hΩ hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := exists_rep_of_involution_mem_gen c₂ hP.cls hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_cases hLK : L = K
  · exact absurd (hLK ▸ hLX) hKX
  by_contra hLJ
  exact no_three_reps_E4_gen hP hW₂ hE₂ ρK ρJ ρL (Ne.symm hs.hJ.2.1)
    (by show K ≠ ρL.K; rw [hρLL]; exact Ne.symm hLK)
    (by show J ≠ ρL.K; rw [hρLL]; exact Ne.symm hLJ)

theorem TightStd8R.sX_normalizes_J (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y)) (hTS₂ : T ≤ (S₂ : Subgroup Y))
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {s : Y} (hsS : s ∈ (S₂ : Subgroup Y))
    (hsX : s ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    conjSub s J = J := by
  set X := omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) with hXdef
  have hΩ := hs.hyp
  have hJΩ := hs.hJ.1
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have hJsΩ := hΩ.conjInvariant s J hJΩ
  have hJsX : conjSub s J ≤ X := by
    intro y hy
    have h2 : s⁻¹ * y * s ∈ X := hJX (mem_conjSub_iff.mp hy)
    have := X.mul_mem (X.mul_mem hsX h2) (X.inv_mem hsX)
    simpa [mul_assoc] using this
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hT.1
  have hle : conjSub s (J ⊓ (S₂ : Subgroup Y)) ≤ conjSub s J ⊓ (S₂ : Subgroup Y) := by
    intro y hy
    have h1 := mem_conjSub_iff.mp hy
    refine ⟨mem_conjSub_iff.mpr h1.1, ?_⟩
    have : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
    rw [this]
    exact (S₂ : Subgroup Y).mul_mem ((S₂ : Subgroup Y).mul_mem hsS h1.2)
      ((S₂ : Subgroup Y).inv_mem hsS)
  have hcardT : Nat.card T ≤ Nat.card ↥(J ⊓ (S₂ : Subgroup Y)) :=
    Subgroup.card_le_of_le (le_inf hs.hT.2.1 hTS₂)
  have hcard : 2 < Nat.card ↥(conjSub s J ⊓ (S₂ : Subgroup Y)) := by
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(conjSub s (J ⊓ (S₂ : Subgroup Y))) =
        Nat.card ↥(J ⊓ (S₂ : Subgroup Y)) :=
      Subgroup.card_map_of_injective (MulAut.conj s).injective
    omega
  exact hs.eq_J_of_mem_X hE hRS₂ hTS₂ hKX hJsΩ hJsX hcard

theorem TightStd8R.sX_centralizes_t (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y)) (hTS₂ : T ≤ (S₂ : Subgroup Y))
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {s : Y} (hsS : s ∈ (S₂ : Subgroup Y))
    (hsX : s ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    s * t * s⁻¹ = t :=
  hs.ht.conj_eq (hs.sX_normalizes_J hE hRS₂ hTS₂ hKX hsS hsX)

theorem TightStd8R.sup_omegaNbrGen_ne_top (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd))) :
    tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hΛN : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    sup_le (s26_le_sigmaNorm_of_mem_dComp hΩ.conjInvariant hs.mem Relation.ReflTransGen.refl)
      (omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hs.mem)
  intro htop
  rw [htop, top_le_iff] at hΛN
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans hΛN)

theorem TightStd8R.commutator_mem_oddCoreOf_lambda_of_ne_top (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤) :
    ∀ k ∈ tightCore Rd, ∀ x ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ⁅k, x⁆ ∈ oddCoreOf (tightCore Rd ⊔
        omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  set X : Subgroup Y := omegaNbrGen Ω K with hXdef
  set Λ : Subgroup Y := K ⊔ X with hΛdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hKΛ : K ≤ Λ := le_sup_left
  have hXΛ : X ≤ Λ := le_sup_right
  have hlt : Nat.card (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) < n := by
    have h1 : Nat.card ↥Λ < Nat.card Y := by
      rw [← Subgroup.card_top (G := Y)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hΛp)
    rw [← hs.large.card]
    exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) h1
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) with hπ
  set Φ : Set (Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) :=
    oddQuotientFamily (restrictFamily Ω Λ) with hΦdef
  have hΦR : TypeRFam r Φ :=
    (h.restrict Λ).quotFamily (CFSG.ComponentClassification.OddCore.odd_card _)
  have hgen : omegaGen Φ = ⊤ := by
    have hΛgen : omegaGen (restrictFamily Ω Λ) = ⊤ := by
      apply Subgroup.map_injective Λ.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype]
      refine le_antisymm (Subgroup.map_subtype_le _) (sup_le ?_ ?_)
      · have hmem : K.subgroupOf Λ ≤ omegaGen (restrictFamily Ω Λ) :=
          le_omegaGen ⟨K, hK, hKΛ, rfl⟩
        calc K = (K.subgroupOf Λ).map Λ.subtype := (Subgroup.map_subgroupOf_eq_of_le hKΛ).symm
          _ ≤ _ := Subgroup.map_mono hmem
      · refine iSup₂_le fun M hM => ?_
        have hMΛ : M ≤ Λ := (le_omegaNbrGen hM).trans hXΛ
        have hmem : M.subgroupOf Λ ≤ omegaGen (restrictFamily Ω Λ) :=
          le_omegaGen ⟨M, hM.1, hMΛ, rfl⟩
        calc M = (M.subgroupOf Λ).map Λ.subtype := (Subgroup.map_subgroupOf_eq_of_le hMΛ).symm
          _ ≤ _ := Subgroup.map_mono hmem
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Λ)), ← hΛgen,
      Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_omegaGen ⟨L, hL, rfl⟩
  have hKb : (K.subgroupOf Λ).map π ∈ Φ := ⟨_, ⟨K, hK, hKΛ, rfl⟩, rfl⟩
  have hcomm : ∀ J' ∈ omegaNbr Ω K,
      Commutes ((K.subgroupOf Λ).map π) ((J'.subgroupOf Λ).map π) := by
    intro J' hJ'
    obtain ⟨t', ht'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ'.1
    have hJ'Λ : J' ≤ Λ := (le_omegaNbrGen hJ').trans hXΛ
    have hnbr := map_mk_mem_omegaNbr_of_le h hKΛ hJ'Λ hJ'
      (map_mk_ne_of_isUniqueInvolution hKΛ hJ'Λ hs.hz ht'
        (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hJ' ht')
        (T8.ne_of_mem_omegaNbr hs.noTwins hJ' hs.hz ht'))
    exact hLC _ hlt Φ hΦR (CFSG.ComponentClassification.OddCore.quotient_corefree _) hgen
      (fun _ hL => aEmpty_of_noTwins hΦR.hyp hL (hΦR.noTwins _ hL)) _ hKb _ hnbr
  have hXC : X ≤ ((Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))).comap
      π).map Λ.subtype := by
    refine iSup₂_le fun J' hJ' j hj => ?_
    have hJ'Λ : J' ≤ Λ := (le_omegaNbrGen hJ').trans hXΛ
    refine ⟨⟨j, hJ'Λ hj⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm J' hJ' b hb _ ⟨⟨j, hJ'Λ hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  intro k hk x hx
  have hkΛ : k ∈ Λ := hKΛ hk
  have hxΛ : x ∈ Λ := hXΛ hx
  have hxC : π ⟨x, hxΛ⟩ ∈ Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) := by
    obtain ⟨y, hy, hyx⟩ := hXC hx
    have hyeq : y = ⟨x, hxΛ⟩ := Subtype.ext hyx
    rw [hyeq] at hy
    exact hy
  have hcomm2 : π ⟨k, hkΛ⟩ * π ⟨x, hxΛ⟩ = π ⟨x, hxΛ⟩ * π ⟨k, hkΛ⟩ :=
    Subgroup.mem_centralizer_iff.mp hxC _ ⟨⟨k, hkΛ⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hmem1 : π ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm2
  have hmem2 : ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ ∈ classicalInvolutionOddCore ↥Λ :=
    (QuotientGroup.eq_one_iff _).mp hmem1
  exact ⟨_, hmem2, by simp [commutatorElement_def]⟩

theorem TightStd8R.commute_of_mem_two_subgroup_of_ne_top (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    {P : Subgroup Y} (hP : IsPGroup 2 ↥P) {k x : Y} (hk : k ∈ tightCore Rd)
    (hx : x ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hkP : k ∈ P) (hxP : x ∈ P) : k * x = x * k := by
  have h1 := hs.commutator_mem_oddCoreOf_lambda_of_ne_top hLC hΛp k hk x hx
  have hmemP : ⁅k, x⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hkP hxP) (P.inv_mem hkP)) (P.inv_mem hxP)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅k, x⁆) := hP.to_le (Subgroup.zpowers_le.mpr hmemP)
  have h2 : ⁅k, x⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1 hpg
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem TightStd8R.exists_zStar_conj_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {S₂ : Sylow 2 Y}
    (hRS₂ : R ≤ (S₂ : Subgroup Y)) (hTS₂ : T ≤ (S₂ : Subgroup Y))
    (hS₂X : IsSylow2In ((S₂ : Subgroup Y) ⊓
      omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
      (omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))) :
    ∃ g ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      g⁻¹ * t * g ∈ (S₂ : Subgroup Y) ∧ g⁻¹ * t * g ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set X : Subgroup Y := omegaNbrGen Ω (tightCore Rd) with hXdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  have htT : t ∈ (S₂ : Subgroup Y) := by
    have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
    have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hT.1
    exact hTS₂ (T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTsyl.2.1 (by omega))
  let SH : Sylow 2 ↥X := AscP1Nine3.sylowOfIsSylow2In₉ hS₂X
  have hSH : (SH : Subgroup ↥X) = ((S₂ : Subgroup Y) ⊓ X).subgroupOf X := rfl
  have htSH : (⟨t, htX⟩ : ↥X) ∈ (SH : Subgroup ↥X) := by
    rw [hSH, Subgroup.mem_subgroupOf]
    exact ⟨htT, htX⟩
  let zt : ↥(SH : Subgroup ↥X) := ⟨⟨t, htX⟩, htSH⟩
  have hzZ : zt ∈ Subgroup.center ↥(SH : Subgroup ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsmem : (s : ↥X) ∈ ((S₂ : Subgroup Y) ⊓ X).subgroupOf X := s.2
    rw [Subgroup.mem_subgroupOf] at hsmem
    have hsc := hs.sX_centralizes_t hE hRS₂ hTS₂ hKX hsmem.1 hsmem.2
    apply Subtype.ext
    apply Subtype.ext
    show (s : ↥X).1 * t = t * (s : ↥X).1
    calc (s : ↥X).1 * t = ((s : ↥X).1 * t * (s : ↥X).1⁻¹) * (s : ↥X).1 := by group
      _ = t * (s : ↥X).1 := by rw [hsc]
  have hzo : orderOf zt = 2 := by
    have h2 : orderOf (t : Y) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs.ht.sq) hs.ht.ne_one
    have h3 : orderOf (⟨t, htX⟩ : ↥X) = 2 := (Subgroup.orderOf_mk t htX).trans h2
    exact (Subgroup.orderOf_mk _ htSH).trans h3
  have hwc : ∀ g : ↥X, g⁻¹ * (zt : ↥X) * g ∈ (SH : Subgroup ↥X) →
      g⁻¹ * (zt : ↥X) * g = zt := by
    intro g hg
    have hg' : g⁻¹ * (zt : ↥X) * g ∈ ((S₂ : Subgroup Y) ⊓ X).subgroupOf X := hg
    rw [Subgroup.mem_subgroupOf] at hg'
    apply Subtype.ext
    show g.1⁻¹ * t * g.1 = t
    exact hcon g.1 g.2 hg'.1
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar SH zt hzZ hzo hwc
  set NX : Subgroup ↥X := classicalInvolutionOddCore ↥X with hNdef
  have hNodd : Odd (Nat.card NX) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  set π := QuotientGroup.mk' NX with hπ
  have hcen' : π ⟨t, htX⟩ ∈ Subgroup.center (↥X ⧸ NX) := hcen
  have hDE := hs.dEdgeless_xFam_E4_of_not_le hKX hE
  have htop := hs.top_not_mem_xFam
  have hJΦ : (J.subgroupOf X).map π ∈ xFam Ω (tightCore Rd) :=
    ⟨_, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩
  have hzJb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd (J.subgroupOf X))
    (isUniqueInvolution_subgroupOf hs.ht hJX)
  have hall : ∀ M ∈ xFam Ω (tightCore Rd), M = (J.subgroupOf X).map π := by
    intro M hM
    by_contra hne
    have hc : M ≤ Subgroup.centralizer ({π ⟨t, htX⟩} : Set (↥X ⧸ NX)) := by
      intro m _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hcen' m)
    have hnbr := mem_omegaNbr_of_le_centralizer_typeR h.xFam hJΦ hM hne hzJb hc
    exact hDE _ hJΦ _ hM (Or.inl hnbr)
  apply htop
  have hgen : omegaGen (xFam Ω (tightCore Rd)) = (J.subgroupOf X).map π := by
    refine le_antisymm (iSup₂_le fun L hL => ?_) (le_omegaGen hJΦ)
    rw [hall L hL]
  rw [← omegaGen_xFam, hgen]
  exact hJΦ

theorem TightStd8R.exists_conj_mul_E4_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {g : Y}
    (hgX : g ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hne : g⁻¹ * t * g ≠ t) (hcomm : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t) :
    ∃ y ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      y * t * y⁻¹ = t * (g⁻¹ * t * g) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set X : Subgroup Y := omegaNbrGen Ω (tightCore Rd) with hXdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  have hΛ := h.restrict X
  have hJΛ : J.subgroupOf X ∈ restrictFamily Ω X := ⟨J, hJΩ, hJX, rfl⟩
  have hA : AEmpty (restrictFamily Ω X) (J.subgroupOf X) :=
    aEmpty_of_noTwins hΛ.hyp hJΛ (hΛ.noTwins _ hJΛ)
  have hz := isUniqueInvolution_subgroupOf hs.ht hJX
  set zt : ↥X := ⟨t, htX⟩ with hztdef
  set gX : ↥X := ⟨g, hgX⟩ with hgXdef
  have hne' : gX⁻¹ * zt * gX ≠ zt := fun e => hne (congrArg Subtype.val e)
  have hcomm' : zt * (gX⁻¹ * zt * gX) = gX⁻¹ * zt * gX * zt := Subtype.ext hcomm
  rcases isConj_or_mem_omegaNbr_gen hΛ.hyp hJΛ hA (hΛ.noTwins _ hJΛ) hz hne' hcomm' with
    hconj | hnbr
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
  · exfalso
    set J₁ : Subgroup Y := conjSub g⁻¹ J with hJ₁def
    have hJ₁Ω : J₁ ∈ Ω := hΩ.conjInvariant g⁻¹ J hJΩ
    have hJ₁X : J₁ ≤ X := by
      intro y hy
      have h1 : g * y * g⁻¹ ∈ J := by simpa using mem_conjSub_iff.mp hy
      have := X.mul_mem (X.mul_mem (X.inv_mem hgX) (hJX h1)) hgX
      simpa [mul_assoc] using this
    have hJ₁e : conjSub gX⁻¹ (J.subgroupOf X) = J₁.subgroupOf X := by
      rw [conjSub_subgroupOf]
      rfl
    rw [hJ₁e] at hnbr
    obtain ⟨-, -, P', hP', hP'J₁, hP'N⟩ := hnbr
    obtain ⟨M, hMΩ, -, hPM⟩ := exists_isSylow2In_of_mem_RSet_restrict hP'
    have hP'G : P'.map X.subtype ≤ J₁ := by
      rintro _ ⟨p, hp, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hP'J₁ hp)
    have hP'R : P'.map X.subtype ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hPM
    have ht₁ : IsUniqueInvolution J₁ (g⁻¹ * t * g) := by
      have := hs.ht.conj g⁻¹
      rwa [inv_inv] at this
    have hJ₁J : J₁ ≠ J := by
      intro e
      have h1 : g⁻¹ * t * g ∈ J := e ▸ ht₁.mem
      rcases hs.ht.unique _ h1 ht₁.sq with h2 | h2
      · exact ht₁.ne_one h2
      · exact hne h2
    have hJ₁nbr : J₁ ∈ omegaNbr Ω J := by
      refine ⟨hJ₁Ω, hJ₁J, P'.map X.subtype, hP'R, hP'G, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (mem_normalizer_subgroupOf_iff hJX).mpr (hP'N hp)
    have himg := map_mk_ne_of_isUniqueInvolution hJX hJ₁X hs.ht ht₁ hcomm (Ne.symm hne)
    have hnbr' := map_mk_mem_omegaNbr_of_le h hJX hJ₁X hJ₁nbr himg
    have hDE := hs.dEdgeless_xFam_E4_of_not_le hKX hE
    exact hDE _ ⟨_, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩ _ ⟨_, ⟨J₁, hJ₁Ω, hJ₁X, rfl⟩, rfl⟩ (Or.inl hnbr')

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

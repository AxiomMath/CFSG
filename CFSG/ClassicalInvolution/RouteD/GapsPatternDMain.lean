module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import CFSG.ClassicalInvolution.RouteD.PatternD
public import CFSG.ClassicalInvolution.RouteD.Pattern
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import CFSG.ClassicalInvolution.Balance.LayerGenerationRoots
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.RouteD.Finite
public import CFSG.ClassicalInvolution.RouteD.Tri

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember LocalOddCentral ExactMembers centralizingMembers ConjInvariant LieSystemData
  centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.Balance (iSup_rankOneImage_eq_range rankOneImage)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem exists_adapted_y_normal {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    (hPat : PatternLemma Y.D.cartan) {t : G} (ht : t * z * t⁻¹ = z)
    (v : Fin Y.D.rank → ZMod 2) (hv : v ≠ 0) (k₀ : Y.K)
    (hT : ∀ γ ∈ Y.D.roots,
      ((conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ).map
          (locAut hΩ ht).toMonoidHom = (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ ∧
        ((∀ x ∈ (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ, locAut hΩ ht x = x) ↔
          charOf v γ = 0))
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∃ p₀ : Fin Y.D.rank, ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), locAut hΩ ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (locAut hΩ ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (ψ k₀)
  let ψ₀ : Y.K →* locQuot Ω z := ψ.comp (MulAut.conj k₀).toMonoidHom
  have hmap : ∀ S : Subgroup Y.K, (conjSub k₀ S).map ψ = S.map ψ₀ := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hT₀ : ∀ γ ∈ Y.D.roots,
      ((Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀).map (locAut hΩ ht).toMonoidHom =
          (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀ ∧
        ((∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀, locAut hΩ ht x = x) ↔
          charOf v γ = 0) := fun γ hγ => by
    rw [← hmap]
    exact hT γ hγ
  have hjimg₀ : ∀ a, locImg Ω z (conjSub (y₀ : G) (j a)) =
      (rankOne Y.D.rootGroup a).map ψ₀ := fun a => by
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = ψ k₀ from hy₀,
      map_conj_map_hom, hmap]
  obtain ⟨w, hw, p₀, rfl⟩ := hPat v hv
  obtain ⟨W₀, k, hk, hW₀⟩ := exists_actsAs_of_charReach hct hw
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (ψ₀ k)
  refine ⟨(y₁ : G) * (y₀ : G), (locLayer Ω z).mul_mem y₁.2 y₀.2, p₀, fun a => ?_⟩
  have hroot : weylAction Y.D.isFiniteType W₀ (Pi.single a 1) ∈ Y.D.roots :=
    weylAction_mem_roots _ W₀ (single_mem_roots _ a)
  have himg : locImg Ω z (conjSub ((y₁ : G) * (y₀ : G)) (j a)) =
      (Y.D.rootGroup (weylAction Y.D.isFiniteType W₀ (Pi.single a 1)) ⊔
        Y.D.rootGroup (-weylAction Y.D.isFiniteType W₀ (Pi.single a 1))).map ψ₀ := by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_mul, locImg_conjSub_layer, hjimg₀ a,
      show locMk Ω z y₁ = ψ₀ k from hy₁, map_conj_map_hom]
    congr 1
    exact conjSub_rankOne_of_actsAs hk (single_mem_roots _ a)
      (CFSG.Timmesfeld.LevisExtras.neg_mem_roots (single_mem_roots _ a))
  obtain ⟨hstab, hfixiff⟩ := hT₀ _ hroot
  rw [himg]
  refine ⟨?_, hstab⟩
  rw [hfixiff, hW₀ a, Pi.single_apply]
  by_cases hap : a = p₀
  · simp [hap]
  · simp [hap]

section Moved

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

theorem exists_moved_layer_member
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (hfix : HasFixedMember Ω K β z) :
    ∃ N ∈ centralizingMembers Ω {z}, ¬ locImg Ω z N ≤ c.d.Q₁ ∧ Commutes K N ∧
      ¬ Commutes β N := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨M, hMΩ, hKM, hβM, -⟩ := hfix
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨S₁, hS₁, S₂, hS₂, hS12, hc₁, hc₂, hn₁, hn₂⟩ := hF.perp2 RK hRK Rβ hRβ hadj hlinR
  obtain ⟨N₁, hN₁, -, -, hN₁R⟩ := cx.exists_member_of_fund hS₁
  obtain ⟨N₂, hN₂, -, -, hN₂R⟩ := cx.exists_member_of_fund hS₂
  have hN12 : N₁ ≠ N₂ := fun h => hS12 (eq_of_map_eq_of_perfect cx.d.ψ cx.d.ker_le
    (cx.hY.perfR S₁ hS₁) (cx.hY.perfR S₂ hS₂) (by rw [← hN₁R, ← hN₂R, h]))
  have hKN₁ : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁ hRK hKR hN₁R).mpr hc₁
  have hKN₂ : Commutes K N₂ := (cx.commutes_iff_fund hKx hN₂ hRK hKR hN₂R).mpr hc₂
  have hβN₁ : ¬ Commutes β N₁ := fun h =>
    hn₁ ((cx.commutes_iff_fund hβx hN₁ hRβ hβR hN₁R).mp h)
  have hβN₂ : ¬ Commutes β N₂ := fun h =>
    hn₂ ((cx.commutes_iff_fund hβx hN₂ hRβ hβR hN₂R).mp h)
  have hz₁ : N₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (commutes_symm hKN₁)
  have hz₂ : N₂ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 c.hz.mem (commutes_symm hKN₂)
  by_cases h₁ : locImg Ω z N₁ ≤ c.d.Q₁
  · by_cases h₂ : locImg Ω z N₂ ≤ c.d.Q₁
    · exact absurd (c.eq_of_locImg_le_Q₁ hz₁ hz₂ h₁ h₂) hN12
    · exact ⟨N₂, hz₂, h₂, hKN₂, hβN₂⟩
  · exact ⟨N₁, hz₁, h₁, hKN₁, hβN₁⟩

theorem commutes_partner_of_centralizes (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNt : N ≤ Subgroup.centralizer ({t} : Set G))
    (hNK : Commutes K N) : Commutes β N := by
  have : NeZero f := ⟨c.hf⟩
  have hS3 : StandardPairAutAbelian (GaloisField p f) :=
    standardPairAutAbelian_galoisField c.hp2 c.hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  obtain ⟨z', hz'⟩ := c.hΩ.classical N hN.1
  exact commutes_partner_of_perfect_conj c.hp2 c.hq hMFZ hS3 c.hΩ hsingle c.hz hD4 c.hP1 hβ ht hKβ
    (commutator_eq_of_isClassicalMember hz') hNt (fun y hy x hx => hNK x hx y hy)

end Moved

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

@[expose] def ToralNormalD (c : TCtx p f .POmegaPlus m Ω K z) {t : G} (ht : t * z * t⁻¹ = z) :
    Prop :=
  ∃ (k₀ : (modelUniv .POmegaPlus m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ZMod 2),
    ∀ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
      ((conjSub k₀ ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ).map
          (locAut c.hΩ.conjInvariant ht).toMonoidHom =
        (conjSub k₀ ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ ∧
      ((∀ x ∈ (conjSub k₀ ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
        locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

theorem PartnerPatternD.of_toral_normal (hm : 7 ≤ m) (hMFZ : FundNoncentral p)
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ)) :
    PartnerPatternD p f m Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hKβ
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaPlus m p f Fact.out trivial hadm
  obtain ⟨e, he⟩ := exists_equiv_cartan_plus (p := p) (f := f) (by omega : 3 ≤ m)
  obtain ⟨j, hj, hjimg, hjK, hjc, hjp⟩ := TCtx.exists_nodes_plus' (by omega : 4 ≤ m) c e he
  have hPat : PatternLemma (modelUniv .POmegaPlus m p f Fact.out).D.cartan :=
    PatternLemma.of_equiv e (fun a b => by rw [he, cartanD_eq]) (patternLemma_D (by omega))
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNQ, hKN, hβN⟩ :=
      exists_moved_layer_member hF c hsingle hshape hβ ht hKβ hfixM
    have hNK : N ≠ K := fun h => by
      rw [h] at hKN
      exact not_commutes_self_of_mem hΩ c.hK hKN
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
    have hgen := iSup_rankOneImage_eq_range .POmegaPlus m p f Fact.out trivial hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, locAut hΩ.conjInvariant htz x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (locAut hΩ.conjInvariant htz).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
          rankOneImage (modelUniv .POmegaPlus m p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff hΩ c.hP1 htz hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (commutes_partner_of_centralizes hMFZ c hsingle hshape hβ ht hKβ hNz hNt hKN)
  obtain ⟨y, hy, p₀, hfixed⟩ := exists_adapted_y_normal hΩ.conjInvariant c.d.ψ hct hPat htz v hv k₀
    hTT hjimg
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemy : ∀ a, conjSub y (j a) ∈ centralizingMembers Ω {z} := fun a => by
    have := centralizingMembers_conj hΩ.conjInvariant y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, (hj a).1, rfl⟩
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [htz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  have hex : ∀ a : Fin m, ∃ w, IsClassicalMember p f (conjSub y (j (e.symm a))) w := fun a => by
    obtain ⟨w₀, hw₀⟩ := hΩ.classical (j (e.symm a)) (hj _).1.1
    exact ⟨_, hw₀.conj y⟩
  choose w hw using hex
  let nd : DNodes p f m Ω K :=
    { J := fun a => conjSub y (j (e.symm a))
      w := w
      mem := fun a => hΩ.conjInvariant y _ (hj _).1.1
      cl := hw
      commK := fun a => commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _)
      comm := fun a b hab h1 h2 =>
        (hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1)
          (by simpa using h2)).conjSub y
      pair := fun a b h => by
        obtain ⟨W, hW⟩ := hjp (e.symm a) (e.symm b) (by simpa using h)
        exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW y⟩ }
  have hfix' : ∀ a, a ≠ e p₀ → Commutes β (nd.J a) := fun a ha => by
    have hne : e.symm a ≠ p₀ := fun h => ha (by rw [← h]; exact (e.apply_symm_apply a).symm)
    have h1 := (hfixed (e.symm a)).1.mpr hne
    have hNt := (locAut_fixed_iff hΩ c.hP1 htz (hmemy (e.symm a))).mpr h1
    exact commutes_partner_of_centralizes hMFZ c hsingle hshape hβ ht hKβ (hmemy _) hNt
      (commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _))
  have hmov' : ¬ Commutes β (nd.J (e p₀)) := fun h => by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at h
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t ht.mem n hn).symm
    have := (hfixed p₀).1.mp ((locAut_fixed_iff hΩ c.hP1 htz (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm' : conjSub t (nd.J (e p₀)) = nd.J (e p₀) := by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ]
    have h1 := (hfixed p₀).2
    rw [locAut_locImg hΩ.conjInvariant htz] at h1
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  obtain ⟨hp0, hlin⟩ := adapted_pattern_D hm hF c hsingle hshape nd hβ ht hKβ hfix' hmov' hnorm'
  have hFix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j (e.symm a))),
      locAut hΩ.conjInvariant htz x = x := fun a ha => by
    refine (hfixed (e.symm a)).1.mpr fun h => ?_
    have h1 : a = e p₀ := by rw [← h]; exact (e.apply_symm_apply a).symm
    have := congrArg Fin.val h1
    omega
  refine PartnerPatternD.of_locAut c (j := fun a : Fin m => j (e.symm a)) (fun a => (hj _).1)
    (fun a => hjK _) ?_ ?_ hy htz hFix ?_
  · intro a b hab h1 h2
    exact hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1) (by simpa using h2)
  · intro a b h
    exact hjp (e.symm a) (e.symm b) (by simpa using h)
  · intro a ha
    have h1 : a = e p₀ := Fin.ext (by omega)
    subst h1
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at hlin
    simpa using hlin

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps

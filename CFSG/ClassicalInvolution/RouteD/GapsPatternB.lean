module

public import CFSG.ClassicalInvolution.RouteD.GapsMoved
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.GapsScenario
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes

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

theorem exists_adapted_y_normal' {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
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
    ∃ y ∈ locLayer Ω z, ∃ p₀ : Fin Y.D.rank, CharReach Y.D.cartan v (Pi.single p₀ 1) ∧ ∀ a,
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
  refine ⟨(y₁ : G) * (y₀ : G), (locLayer Ω z).mul_mem y₁.2 y₀.2, p₀, hw, fun a => ?_⟩
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

section Path

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

@[expose] def adjPath (n : ℕ) (a b : Fin n) : Prop := a.val + 1 = b.val

local macro "pidx_tac" : tactic =>
  `(tactic| first
    | (simp [LNodes.Adj, adjPath]; done)
    | (simp [LNodes.Adj, adjPath]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem path_interior_false {n : ℕ} (hn : 7 ≤ n)
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath n) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp : Fin n} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h1 : 1 ≤ pp.val) (h2 : pp.val + 2 ≤ n) : False := by
  have hpt : pp.val < n := pp.isLt
  have hcases : pp.val = 1 ∨ (2 ≤ pp.val ∧ pp.val ≤ 3) ∨ 4 ≤ pp.val := by omega
  rcases hcases with h | h | h
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨0, by omega⟩)
      (a₁ := ⟨2, by omega⟩) (e := ⟨3, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp)
      (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
      (e := ⟨pp.val - 2, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp)
      (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
      (e := ⟨pp.val - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac

end Path

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

@[expose] def ToralPropB (c : TCtx p f .POmegaOdd m Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2) : Prop :=
  ∀ γ ∈ (modelUniv .POmegaOdd m p f Fact.out).D.roots,
    ((conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ).map
        (locAut c.hΩ.conjInvariant ht).toMonoidHom =
      (conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ ∧
    ((∀ x ∈ (conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
      locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

@[expose] def ToralNormalB (c : TCtx p f .POmegaOdd m Ω K z) {t : G} (ht : t * z * t⁻¹ = z) :
    Prop :=
  ∃ (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2), ToralPropB c ht k₀ v

@[expose] def LastNodesExcluded (m : ℕ) (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank →
    ZMod 2) : Prop :=
  ∀ p₀ : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank,
    CharReach (modelUniv .POmegaOdd m p f Fact.out).D.cartan v (Pi.single p₀ 1) → p₀.val + 2 < m

theorem PartnerPatternBPair.of_toral_normal_odd (hm : 8 ≤ m) (hMFZ : FundNoncentral p)
    (hF : OrthFacts (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaOdd m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalB c (partner_involution_commutes c.hp2 c.hz ht hKβ))
    (hres : ∀ k₀ v, ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
      LastNodesExcluded m v) :
    PartnerPatternBPair p f m Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hKβ
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hm3 : 3 ≤ m := by omega
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf1, hm3, c.hp2⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaOdd m p f Fact.out trivial hadm
  obtain ⟨j, hjmem, hjY, hjperf, hjK, hjc, hjp, hjsp, hjimg⟩ := TCtx.exists_nodes_odd_full hm3 c
  have hPat : PatternLemma (modelUniv .POmegaOdd m p f Fact.out).D.cartan := by
    have := patternLemma_B m
    rw [← cartanB_eq] at this
    exact this
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNQ, hKN, hβN⟩ :=
      exists_moved_layer_member_gen hF c hsingle hshape hβ ht hKβ hfixM
    have hNK : N ≠ K := fun h => by
      rw [h] at hKN
      exact not_commutes_self_of_mem hΩ c.hK hKN
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
    have hgen := iSup_rankOneImage_eq_range .POmegaOdd m p f Fact.out trivial hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, locAut hΩ.conjInvariant htz x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (locAut hΩ.conjInvariant htz).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaOdd m p f Fact.out).D.roots,
          rankOneImage (modelUniv .POmegaOdd m p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff hΩ c.hP1 htz hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (commutes_partner_of_centralizes_gen hMFZ c hsingle hshape hβ ht hKβ hNz hNt hKN)
  obtain ⟨y, hy, p₀, hreach, hfixed⟩ := exists_adapted_y_normal' hΩ.conjInvariant c.d.ψ hct hPat
    htz v hv k₀ hTT hjimg
  have hlt : p₀.val + 2 < m := hres k₀ v hTT p₀ hreach
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemy : ∀ a : Fin m, a.val + 1 < m → conjSub y (j a) ∈ centralizingMembers Ω {z} :=
    fun a ha => by
      have := centralizingMembers_conj hΩ.conjInvariant y z
      rw [hyz] at this
      rw [this]
      exact ⟨j a, (hjmem a ha).1, rfl⟩
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [htz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  let jj : Fin (m - 1) → Fin m := fun a => ⟨a.val, by have := a.isLt; omega⟩
  have hjjl : ∀ a : Fin (m - 1), (jj a).val + 1 < m := fun a => by
    have := a.isLt
    show a.val + 1 < m
    omega
  have hex : ∀ a : Fin (m - 1), ∃ w, IsClassicalMember p f (conjSub y (j (jj a))) w := fun a => by
    obtain ⟨w₀, hw₀⟩ := hΩ.classical (j (jj a)) (hjmem _ (hjjl a)).1.1
    exact ⟨_, hw₀.conj y⟩
  choose w hw using hex
  let nd : LNodes p f (adjPath (m - 1)) Ω K :=
    { J := fun a => conjSub y (j (jj a))
      w := w
      mem := fun a => hΩ.conjInvariant y _ (hjmem _ (hjjl a)).1.1
      cl := hw
      commK := fun a => commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _)
      comm := fun a b hab h1 h2 => by
        have hlt' : a.val + 1 < b.val ∨ b.val + 1 < a.val := by
          have : a.val ≠ b.val := fun e => hab (Fin.ext e)
          unfold adjPath at h1 h2
          omega
        rcases hlt' with h | h
        · exact (hjc (jj a) (jj b) h).conjSub y
        · exact commutes_symm ((hjc (jj b) (jj a) h).conjSub y)
      pair := fun a b h => by
        obtain ⟨W, hW⟩ := hjp (jj a) (jj b) h (by have := b.isLt; show b.val + 1 < m; omega)
        exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW y⟩ }
  let pp : Fin (m - 1) := ⟨p₀.val, by omega⟩
  have hjpp : jj pp = p₀ := Fin.ext rfl
  have hfix' : ∀ a, a ≠ pp → Commutes β (nd.J a) := fun a ha => by
    have hne : jj a ≠ p₀ := fun h => ha (Fin.ext (by
      have := congrArg Fin.val h
      simpa [jj, pp] using this))
    have h1 := (hfixed (jj a)).1.mpr hne
    have hNt := (locAut_fixed_iff hΩ c.hP1 htz (hmemy (jj a) (hjjl a))).mpr h1
    exact commutes_partner_of_centralizes_gen hMFZ c hsingle hshape hβ ht hKβ (hmemy _ (hjjl a))
      hNt (commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _))
  have hmov' : ¬ Commutes β (nd.J pp) := fun h => by
    have hNt : conjSub y (j (jj pp)) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t ht.mem n hn).symm
    have := (hfixed (jj pp)).1.mp ((locAut_fixed_iff hΩ c.hP1 htz (hmemy _ (hjjl pp))).mp hNt)
    exact this hjpp
  have hnorm' : conjSub t (nd.J pp) = nd.J pp := by
    have h1 := (hfixed (jj pp)).2
    rw [locAut_locImg hΩ.conjInvariant htz] at h1
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hmemy _ (hjjl pp))) (hmemy _ (hjjl pp)) h1
  by_cases hp0 : p₀.val = 0
  ·
    have hpair0 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp) :=
      scenarioC hF c hsingle hshape nd hβ ht hKβ hfix' hmov' hnorm' (b := ⟨2, by omega⟩)
        (by apply fin_ne_of_val_ne; simp only [pp]; omega)
        (by simp [LNodes.Adj, adjPath, pp]; omega)
    refine PartnerPatternBPair.of_locAut hΩ c.hP1 (j := j) (fun a ha => (hjmem a ha).1.1) hjY hjK
      hjperf c.locLayer_le_normalizer hjc hjp hjsp hy htz (fun a ha x hx => ?_) (fun a ha => ?_)
    · exact ((hfixed a).1.mpr (fun h => by have := congrArg Fin.val h; omega)) x hx
    · have : jj pp = a := Fin.ext (by simp only [jj, pp]; omega)
      rw [← this]
      exact hpair0
  ·
    exact absurd (path_interior_false (n := m - 1) (by omega) hF.toOrthGeom c hsingle hshape nd hβ
      ht hKβ (pp := pp) hfix' hmov' hnorm' (by simp only [pp]; omega) (by simp only [pp]; omega))
      id

theorem PartnerPatternBPair.of_toral_odd (hm : 8 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaOdd m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalB c (partner_involution_commutes c.hp2 c.hz ht hKβ))
    (hres : ∀ k₀ v, ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
      LastNodesExcluded m v) :
    PartnerPatternBPair p f m Ω K β t :=
  PartnerPatternBPair.of_toral_normal_odd hm hMFZ (orthFacts_odd c.hp2 (by omega) c.hq) c hsingle
    hshape hβ ht hKβ hfixM hT hres

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps

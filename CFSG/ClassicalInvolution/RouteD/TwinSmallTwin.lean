module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallLocal
public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallZ
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Eigen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eigen_contradiction (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ l ∈ L, g * l = l * g) {e a : V} (he : e ∈ negSpace i) (ha : a ∈ negSpace i)
    (he0 : e ≠ 0) (ha0 : a ≠ 0) (hge : g e = -e) (hga : g a = a) : False := by
  rcases negSpace_le_eigenspace_of_commute h2 hL hgO hg2 hcomm with h | h
  · have h1 : g e = e := by
      have := Module.End.mem_eigenspace_iff.mp (h he)
      simpa using this
    rw [hge] at h1
    have h3 : e + e = 0 := neg_eq_iff_add_eq_zero.mp h1
    rw [← two_smul K] at h3
    exact he0 ((smul_eq_zero.mp h3).resolve_left h2)
  · have h1 : g a = -a := by
      have := Module.End.mem_eigenspace_iff.mp (h ha)
      simpa using this
    rw [hga] at h1
    have h3 : a + a = 0 := by
      have := neg_eq_iff_add_eq_zero.mp h1.symm
      exact this
    rw [← two_smul K] at h3
    exact ha0 ((smul_eq_zero.mp h3).resolve_left h2)

theorem commutes_of_span_orth (F F' : OPFrame Q) (h : ∀ x ∈ F.span, ∀ y ∈ F'.span, polar Q x y = 0)
    (A B : SL(2, K)) : F.La A * F'.La B = F'.La B * F.La A :=
  Frame.La_comm_of_orth (fun X Y => h _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩) A B

theorem span_orth_of_commutes_ne [Finite K] (hodd : Odd (Nat.card K)) {F F' : OPFrame Q}
    (hc : Commutes F.La.range F'.La.range) (hne : F.La (-1) ≠ F'.La (-1)) :
    ∀ x ∈ F.span, ∀ y ∈ F'.span, polar Q x y = 0 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rcases orth_or_twin hodd (IsFundamental.of_frame F) (IsFundamental.of_frame F') hc with h | h
  · rwa [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at h
  · exact absurd h.symm hne


end Eigen

noncomputable abbrev QM (p f m : ℕ) [Fact p.Prime] :
    QuadraticForm (GaloisField p f) (Vm m (GaloisField p f)) :=
  quadMinus m (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2

noncomputable abbrev SpinM (p f m : ℕ) [Fact p.Prime] : Type := spinGroup (QM p f m)

section Layer

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} {x : G}

omit [Finite G] in
theorem ctx_centralQuot (cx : TCtx p f .POmegaMinus m Ω N x) (hm : 4 ≤ m) :
    CentralQuot (spinAction (QM p f m)) (fundamentalSubgroups .POmegaMinus (minusDatum m
      (minusCoeffs_irr p f))) (fundSet (QM p f m))
      (scalars (GaloisField p f) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f)) :=
  Exotic.centralQuot_minus cx.hp2 cx.hq ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr cx.hf, hm⟩

theorem locElt_mul_psi (cx : TCtx p f .POmegaMinus m Ω N x) {A B : Subgroup G}
    (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    {RA RB : Subgroup (SpinM p f m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ) {wA wB : G}
    (hwA : IsClassicalMember p f A wA) (hwB : IsClassicalMember p f B wB) :
    ∃ rA rB : SpinM p f m, InvOf RA rA ∧ InvOf RB rB ∧
      locElt Ω x (wA * wB) ((locLayer Ω x).mul_mem (le_centralizingLayer hA hwA.mem)
        (le_centralizingLayer hB hwB.mem)) = cx.d.ψ (rA * rB) := by
  obtain ⟨rA, hrA, hψA⟩ : ∃ r : SpinM p f m, InvOf RA r ∧
      cx.d.ψ r = locElt Ω x wA (le_centralizingLayer hA hwA.mem) :=
    exists_involution_of_fund cx hA hRA hAR hwA
  obtain ⟨rB, hrB, hψB⟩ : ∃ r : SpinM p f m, InvOf RB r ∧
      cx.d.ψ r = locElt Ω x wB (le_centralizingLayer hB hwB.mem) :=
    exists_involution_of_fund cx hB hRB hBR hwB
  refine ⟨rA, rB, hrA, hrB, ?_⟩
  calc locElt Ω x (wA * wB) _ = locElt Ω x wA (le_centralizingLayer hA hwA.mem) *
        locElt Ω x wB (le_centralizingLayer hB hwB.mem) := (locElt_mul _ _).symm
    _ = cx.d.ψ rA * cx.d.ψ rB := by rw [hψA, hψB]
    _ = cx.d.ψ (rA * rB) := (map_mul cx.d.ψ rA rB).symm

theorem centralizes_prod_of_same (cx : TCtx p f .POmegaMinus m Ω N x) (hm : 4 ≤ m)
    {A B : Subgroup G} (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    {RA RB : Subgroup (SpinM p f m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ) {wA wB : G}
    (hwA : IsClassicalMember p f A wA) (hwB : IsClassicalMember p f B wB)
    {iA : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f)}
    (hiA : IsFundamental (QM p f m) (RA.map (spinAction (QM p f m))) iA)
    (hiB : IsFundamental (QM p f m) (RB.map (spinAction (QM p f m))) iA)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) {R : Subgroup (SpinM p f m)}
    (hLR : locImg Ω x L = R.map cx.d.ψ) :
    L ≤ Subgroup.centralizer ({wA * wB} : Set G) := by
  have cq := ctx_centralQuot cx hm
  obtain ⟨rA, rB, hrA, hrB, hloc⟩ := locElt_mul_psi cx hA hB hRA hRB hAR hBR hwA hwB
  have hodd := cx.hodd
  have hπA := map_invOf_eq hodd cq hRA hiA hrA
  have hπB := map_invOf_eq hodd cq hRB hiB hrB
  have hπ : spinAction (QM p f m) (rA * rB) = 1 := by
    rw [map_mul, hπA, hπB]
    exact hiA.mul_self
  have hcen := cq.ker_le (MonoidHom.mem_ker.mpr hπ)
  rw [centralizes_iff_locElt cx.hΩ cx.hP1 ((locLayer Ω x).mul_mem
    (le_centralizingLayer hA hwA.mem) (le_centralizingLayer hB hwB.mem)) hL hLR]
  intro s hs
  obtain ⟨r, -, rfl⟩ : ∃ r : SpinM p f m, r ∈ R ∧ cx.d.ψ r = s := hs
  rw [hloc]
  have := Subgroup.mem_center_iff.mp hcen r
  calc cx.d.ψ (rA * rB) * cx.d.ψ r = cx.d.ψ ((rA * rB) * r) := (map_mul cx.d.ψ _ _).symm
    _ = cx.d.ψ (r * (rA * rB)) := congrArg cx.d.ψ this.symm
    _ = cx.d.ψ r * cx.d.ψ (rA * rB) := map_mul cx.d.ψ _ _

theorem not_centralizes_prod_mixed (cx : TCtx p f .POmegaMinus m Ω N x) (hm : 4 ≤ m)
    {A B L : Subgroup G} (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    (hL : L ∈ centralizingMembers Ω {x}) {RA RB R : Subgroup (SpinM p f m)}
    (hRA : RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hRB : RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hAR : locImg Ω x A = RA.map cx.d.ψ) (hBR : locImg Ω x B = RB.map cx.d.ψ)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {wA wB : G} (hwA : IsClassicalMember p f A wA)
    (hwB : IsClassicalMember p f B wB) (F₁ F₂ F : OPFrame (QM p f m))
    (hF₁ : RA.map (spinAction (QM p f m)) = F₁.La.range)
    (hF₂ : RB.map (spinAction (QM p f m)) = F₂.La.range)
    (hF : R.map (spinAction (QM p f m)) = F.La.range)
    (horth : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar (QM p f m) x y = 0)
    {e a : Vm m (GaloisField p f)} (he : e ∈ F.span) (he0 : e ≠ 0) (heA : e ∈ F₁.span)
    (heB : ∀ y ∈ F₂.span, polar (QM p f m) e y = 0) (ha : a ∈ F.span) (ha0 : a ≠ 0)
    (haA : ∀ y ∈ F₁.span, polar (QM p f m) a y = 0)
    (haB : ∀ y ∈ F₂.span, polar (QM p f m) a y = 0) :
    ¬ L ≤ Subgroup.centralizer ({wA * wB} : Set G) := by
  intro hcent
  have cq := ctx_centralQuot cx hm
  have hodd := cx.hodd
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨rA, rB, hrA, hrB, hloc⟩ := locElt_mul_psi cx hA hB hRA hRB hAR hBR hwA hwB
  have hiA : IsFundamental (QM p f m) (RA.map (spinAction (QM p f m))) (F₁.La (-1)) := by
    rw [hF₁]
    exact IsFundamental.of_frame F₁
  have hiB : IsFundamental (QM p f m) (RB.map (spinAction (QM p f m))) (F₂.La (-1)) := by
    rw [hF₂]
    exact IsFundamental.of_frame F₂
  have hiL : IsFundamental (QM p f m) (R.map (spinAction (QM p f m))) (F.La (-1)) := by
    rw [hF]
    exact IsFundamental.of_frame F
  have hπA := map_invOf_eq hodd cq hRA hiA hrA
  have hπB := map_invOf_eq hodd cq hRB hiB hrB
  have h1 := (centralizes_iff_locElt cx.hΩ cx.hP1 ((locLayer Ω x).mul_mem
    (le_centralizingLayer hA hwA.mem) (le_centralizingLayer hB hwB.mem)) hL hLR).mp hcent
  have h2' : ∀ r : SpinM p f m, r ∈ R → Commute (cx.d.ψ (rA * rB)) (cx.d.ψ r) := fun r hr => by
    have := h1 (cx.d.ψ r) ⟨r, hr, rfl⟩
    rwa [hloc] at this
  have h3 := commute_of_perfect_of_map_commute cx.d.ψ cx.d.ker_le (cq.perf R hR) h2'
  set g : Vm m (GaloisField p f) ≃ₗ[GaloisField p f] Vm m (GaloisField p f) :=
    F₁.La (-1) * F₂.La (-1) with hg
  have hπ : spinAction (QM p f m) (rA * rB) = g := by
    rw [map_mul, hπA, hπB]
  have hcommg : ∀ l ∈ F.La.range, g * l = l * g := by
    intro l hl
    rw [← hF] at hl
    obtain ⟨r, hr, rfl⟩ := hl
    have h3' : (rA * rB) * r = r * (rA * rB) := (h3 r hr).eq
    rw [← hπ, ← map_mul, ← map_mul, h3']
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (QM p f m) :=
    Subgroup.mul_mem _ (F₁.La_mem_orthogonalGroup (-1)) (F₂.La_mem_orthogonalGroup (-1))
  have hc12 : F₁.La (-1) * F₂.La (-1) = F₂.La (-1) * F₁.La (-1) :=
    commutes_of_span_orth F₁ F₂ horth (-1) (-1)
  have hg2 : g * g = 1 := by
    calc g * g = F₁.La (-1) * (F₂.La (-1) * F₁.La (-1)) * F₂.La (-1) := by rw [hg]; group
      _ = F₁.La (-1) * (F₁.La (-1) * F₂.La (-1)) * F₂.La (-1) := by rw [← hc12]
      _ = (F₁.La (-1) * F₁.La (-1)) * (F₂.La (-1) * F₂.La (-1)) := by group
      _ = 1 := by rw [F₁.La_neg_one_mul_self, F₂.La_neg_one_mul_self, one_mul]
  have hperpB : ∀ v, (∀ y ∈ F₂.span, polar (QM p f m) v y = 0) → F₂.La (-1) v = v := fun v hv =>
    (Frame.mem_perp_iff_fix F₂ h2).mp ((Frame.mem_perp_iff_forall_incl F₂).mpr fun Y =>
      hv _ ⟨Y, rfl⟩)
  have hperpA : ∀ v, (∀ y ∈ F₁.span, polar (QM p f m) v y = 0) → F₁.La (-1) v = v := fun v hv =>
    (Frame.mem_perp_iff_fix F₁ h2).mp ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y =>
      hv _ ⟨Y, rfl⟩)
  have hge : g e = -e := by
    rw [hg, LinearEquiv.mul_apply, hperpB e heB]
    exact (Frame.mem_span_iff_inv F₁ h2).mp heA
  have hga : g a = a := by
    rw [hg, LinearEquiv.mul_apply, hperpB a haB, hperpA a haA]
  have hnegF : negSpace (F.La (-1)) = F.span := negSpace_La_neg_one h2 F
  exact eigen_contradiction h2 hiL hgO hg2 (fun l hl => hcommg l (by rw [← hF]; exact hl))
    (hnegF ▸ he) (hnegF ▸ ha) he0 ha0 hge hga

theorem false_of_twins_other_layer {K M : Subgroup G} {z xM : G}
    (c : TCtx p f .POmegaMinus m Ω K z) (cM : TCtx p f .POmegaMinus m Ω M xM) (hm : 7 ≤ m)
    (hKxM : K ∈ centralizingMembers Ω {xM}) {A B : Subgroup G}
    (hAz : A ∈ centralizingMembers Ω {z}) (hBz : B ∈ centralizingMembers Ω {z})
    (hAM : A ∈ centralizingMembers Ω {xM}) (hBM : B ∈ centralizingMembers Ω {xM})
    {wA wB : G} (hwA : IsClassicalMember p f A wA) (hwB : IsClassicalMember p f B wB)
    {RAz RBz : Subgroup (SpinM p f m)}
    (hRAz : RAz ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hRBz : RBz ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hAimgz : locImg Ω z A = RAz.map c.d.ψ) (hBimgz : locImg Ω z B = RBz.map c.d.ψ)
    (hsame : ∀ i j, IsFundamental (QM p f m) (RAz.map (spinAction (QM p f m))) i →
      IsFundamental (QM p f m) (RBz.map (spinAction (QM p f m))) j → i = j)
    {RKM RAM RBM : Subgroup (SpinM p f m)}
    (hRAM : RAM ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hRBM : RBM ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
    (hKimgM : locImg Ω xM K = RKM.map cM.d.ψ) (hAimgM : locImg Ω xM A = RAM.map cM.d.ψ)
    (hBimgM : locImg Ω xM B = RBM.map cM.d.ψ) (F₀ F₁ F₂ : OPFrame (QM p f m))
    (hF₀ : RKM.map (spinAction (QM p f m)) = F₀.La.range)
    (hF₁ : RAM.map (spinAction (QM p f m)) = F₁.La.range)
    (hF₂ : RBM.map (spinAction (QM p f m)) = F₂.La.range)
    (h01 : ∀ x ∈ F₀.span, ∀ y ∈ F₁.span, polar (QM p f m) x y = 0)
    (h02 : ∀ x ∈ F₀.span, ∀ y ∈ F₂.span, polar (QM p f m) x y = 0)
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar (QM p f m) x y = 0) : False := by
  have hm4 : 4 ≤ m := by omega
  have cq := ctx_centralQuot c hm4
  have hodd := c.hodd
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hQ : (polarBilin (QM p f m)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f)
  have hdim : 13 ≤ Module.finrank (GaloisField p f) (Vm m (GaloisField p f)) := by
    rw [finrank_minus p f m (by omega)]
    omega
  obtain ⟨iA, hiA⟩ := cq.map_mem _ hRAz
  obtain ⟨iB, hiB⟩ := cq.map_mem _ hRBz
  have hAB : iA = iB := hsame iA iB hiA hiB
  subst hAB
  obtain ⟨F, hFK, ⟨e, heF, he0, heA, heB⟩, ⟨a, haF, ha0, haA, haB⟩, ⟨e', he'F, f', hf'A, hpol⟩⟩ :=
    exists_mixed_frame h2 hQ F₀ F₁ F₂ h01 h02 h12 hdim
  have hL : F.La.range ∈ fundSet (QM p f m) := ⟨F.La (-1), IsFundamental.of_frame F⟩
  obtain ⟨R', hR', hR'F⟩ := cq.surj _ hL
  obtain ⟨Nn, hNnM, hNnne, -, hNnimg⟩ := cM.exists_member_of_fund hR'
  have hRK : Commutes R' RKM := by
    refine (cq.commutes_iff hR').mp ?_
    rw [hR'F, hF₀]
    rintro _ ⟨A', rfl⟩ _ ⟨B', rfl⟩
    exact commutes_of_span_orth F F₀ hFK A' B'
  have hNnK : Commutes Nn K :=
    (cM.commutes_iff_fund hNnM hKxM hR' hNnimg hKimgM).mpr hRK
  have hNnz : Nn ∈ centralizingMembers Ω {z} := by
    refine ⟨hNnM.1, fun n hn => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hNnK n hn z c.hz.mem
  have hspan : ¬ F₁.span = F.span := by
    intro h
    have : a ∈ F₁.span := h ▸ haF
    exact ha0 (F₁.polarNondegOn_span a this haA)
  have hFiso : IsFundamental (QM p f m) F.La.range (F.La (-1)) := IsFundamental.of_frame F
  have hF₁iso : IsFundamental (QM p f m) F₁.La.range (F₁.La (-1)) := IsFundamental.of_frame F₁
  have hnegF : negSpace (F.La (-1)) = F.span := negSpace_La_neg_one h2 F
  have hnegF₁ : negSpace (F₁.La (-1)) = F₁.span := negSpace_La_neg_one h2 F₁
  have hnc : ¬ Commutes Nn A := by
    intro hc
    have h1 : Commutes R' RAM := (cM.commutes_iff_fund hNnM hAM hR' hNnimg hAimgM).mp hc
    have h2' : Commutes F.La.range F₁.La.range := by
      rw [← hR'F, ← hF₁]
      exact (cq.commutes_iff hR').mpr h1
    rcases orth_or_twin hodd hFiso hF₁iso h2' with h | h
    · have := h e' (hnegF ▸ he'F) f' (hnegF₁ ▸ hf'A)
      rw [hpol] at this
      exact one_ne_zero this
    · apply hspan
      rw [← hnegF₁, ← hnegF, h]
  have hne : Nn ≠ A := by
    rintro rfl
    have h1 : R'.map cM.d.ψ = RAM.map cM.d.ψ := hNnimg.symm.trans hAimgM
    have h2' : R' = RAM := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cM.d.ψ
      cM.d.ker_le (cq.perf R' hR') (cq.perf RAM hRAM) h1
    have h3 : F.La.range = F₁.La.range := by rw [← hR'F, ← hF₁, h2']
    have h4 : F.La (-1) = F₁.La (-1) :=
      IsFundamental.involution_unique hodd hFiso (h3 ▸ hF₁iso)
    exact hspan (by rw [← hnegF₁, ← hnegF, h4])
  have hlayer : IsLayerMember c Nn := IsLayerMember.of_not_commutes c hNnz hAz hne hnc
  obtain ⟨Rz, hRz, hNnimgz⟩ := hlayer.exists_fund
  have hcent := centralizes_prod_of_same c hm4 hAz hBz hRAz hRBz hAimgz hBimgz hwA hwB hiA hiB
    hNnz hNnimgz
  exact not_centralizes_prod_mixed cM hm4 hAM hBM hNnM hRAM hRBM hR' hAimgM hBimgM hNnimg hwA hwB
    F₁ F₂ F hF₁ hF₂ hR'F h12 heF he0 heA heB haF ha0 haA haB hcent


end Layer

end CFSG.ClassicalInvolution.RouteD.TwinSmall

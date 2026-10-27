module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidTheta
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofULevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidBarW

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin (perfectCore)

section Generic

variable {G : Type} [Group G]

theorem perfect_subgroupOf {Y X : Subgroup G} (hYX : Y ≤ X) (hY : ⁅Y, Y⁆ = Y) :
    ⁅Y.subgroupOf X, Y.subgroupOf X⁆ = Y.subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYX, hY]

@[expose] noncomputable def conjAut {X : Subgroup G} {x : G} (hX : rightConjugate X x = X) :
    MulAut ↥X :=
  ((MulAut.conj x⁻¹).subgroupMap X).trans (MulEquiv.subgroupCongr hX)

theorem coe_conjAut {X : Subgroup G} {x : G} (hX : rightConjugate X x = X) (y : ↥X) :
    ((conjAut hX y : ↥X) : G) = x⁻¹ * y * x := by
  change (MulAut.conj x⁻¹) (y : G) = x⁻¹ * y * x
  rw [MulAut.conj_apply, inv_inv]

theorem mulAut_mem_center {X : Type*} [Group X] (γ : MulAut X) {y : X} (hy : y ∈ center X) :
    γ y ∈ center X := by
  rw [mem_center_iff]
  intro z
  obtain ⟨w, rfl⟩ := γ.surjective z
  rw [← map_mul, ← map_mul, mem_center_iff.mp hy w]

end Generic

section Core

variable {K : Type} [Field K] [CharP K 2] [Finite K] {k f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K)}

omit [Finite K] [Finite G] in
theorem map_theta_eq_stdW (hk : 2 ≤ k) {s : K} (hs : s + h.bar s = 1) {X : Subgroup G}
    (hXA : X ≤ A) {Θ : ↥X →* stabE (ε := k) h}
    (hΘ : ∀ x, psiU h (isHypTransport_uFrame h hk hs) (Θ x) = θ (Subgroup.inclusion hXA x))
    {W : Subgroup G} (hWX : W ≤ X)
    (hWθ : ∀ w (hw : w ∈ W), θ ⟨w, hXA (hWX hw)⟩ ∈ uBarW K k f)
    (hWs : ∀ u ∈ uBarW K k f, ∃ w, ∃ hw : w ∈ W, θ ⟨w, hXA (hWX hw)⟩ = u) :
    (W.subgroupOf X).map Θ = stdW h := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_stdW_iff_uBarW h hk hs, ← psiU_apply, hΘ]
    exact hWθ x hx
  · intro hg
    rw [mem_stdW_iff_uBarW h hk hs, ← psiU_apply] at hg
    obtain ⟨w, hw, hwg⟩ := hWs _ hg
    refine ⟨⟨w, hWX hw⟩, hw, psiU_injective h (isHypTransport_uFrame h hk hs) ?_⟩
    rw [hΘ, ← hwg]
    rfl

theorem rigidCore_unitary (hf : 2 ≤ f) (hk : 3 ≤ k) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) {c : K} (hc0 : c ≠ 0) (hc : h.bar c = c)
    {Mp : StatedSU (2 + k) (2 ^ f) K}
    (hMp : ((Mp : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 (1 + c • vecMulVec (uw₀ (K := K) (show 2 ≤ k by omega)) (uw₀ (show 2 ≤ k by omega))))
    (hθp : θ ⟨p, hpA⟩ = uProj K (2 + k) f Mp) :
    RigidCore A p (uLeviW θ) := by
  have hk2 : 2 ≤ k := by omega
  have hK := h.card_eq_sq
  obtain ⟨s, hs⟩ := exists_add_bar_eq h (map_one h.bar)
  have hR := isHypTransport_uFrame h hk2 hs
  have hθp' : θ ⟨p, hpA⟩ = psiU h hR ⟨tz h hc, tz_mem_stabE h hc⟩ := by
    rw [hθp, psiU_apply]
    congr 1
    exact Subtype.ext (Units.ext (hMp.trans (tmat_tz h hk2 hs hc).symm))
  obtain ⟨Θ, hΘs, hΘ⟩ := exists_theta_stabE h hR hf hk2 hθ hker hodd hpA hp2 hc hc0 hθp'
  have hXA := perfectCore_inf_le A p
  have hWperf : ⁅uLeviW θ, uLeviW θ⁆ = uLeviW θ :=
    commutator_levLift hker hθ (commutator_uBarW hK hf)
  have hWp : uLeviW θ ≤ centralizer ({p} : Set G) := by
    refine levLift_le_centralizer hker hpA fun u hu => ?_
    rw [hθp]
    obtain ⟨S, hS⟩ := mem_range_uL_of h (g := Mp) hMp
    have hMpL : uProj K (2 + k) f Mp ∈ uBarL K k f :=
      ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩
    exact (uBarW_commute_uBarL hu hMpL).symm
  have hWX : uLeviW θ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf levLift_le hWp) hWperf
  have hWstd : ((uLeviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      stdW h :=
    map_theta_eq_stdW h hk2 hs hXA hΘ hWX (fun w hw => theta_mem_of_mem_levLift hw)
      (fun u hu => exists_mem_levLift hθ (commutator_uBarW hK hf) hu)
  have hstdperf : ⁅stdW (ε := k) h, stdW (ε := k) h⁆ = stdW (ε := k) h := by
    rw [← hWstd, ← Subgroup.map_commutator, perfect_subgroupOf hWX hWperf]
  intro x hXx _ _
  have hWxX : rightConjugate (uLeviW θ) x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hWX).trans hXx.le
  have hWxA : rightConjugate (uLeviW θ) x ≤ A := hWxX.trans hXA
  have hWxperf : ⁅rightConjugate (uLeviW θ) x, rightConjugate (uLeviW θ) x⁆ =
      rightConjugate (uLeviW θ) x := by
    rw [rightConjugate, ← Subgroup.map_commutator, hWperf]
  have hγ : ∀ y, Θ y = 1 → Θ (conjAut hXx y) = 1 := by
    intro y hy
    have hyA : Subgroup.inclusion hXA y ∈ center ↥A := by
      rw [← hker, MonoidHom.mem_ker, ← hΘ, hy, map_one]
    have hyc : y ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) := by
      rw [mem_center_iff]
      intro z
      apply Subgroup.inclusion_injective hXA
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hyA _
    have hyo : Odd (orderOf y) := by
      rw [← orderOf_injective (Subgroup.inclusion hXA) (Subgroup.inclusion_injective hXA) y]
      have h1 := orderOf_dvd_natCard (⟨_, hyA⟩ : center ↥A)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    refine theta_eq_one_of_mem_center h hΘs (mulAut_mem_center (conjAut hXx) hyc) ?_
    rwa [MulEquiv.orderOf_eq]
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_of_ker Θ hΘs (conjAut hXx) hγ
  obtain ⟨g₀, hg₀⟩ := exists_map_stdW_eq_conj h hf hk hstdperf β
  have hγw : ∀ w (hw : w ∈ uLeviW θ), conjAut hXx ⟨w, hWX hw⟩ =
      ⟨x⁻¹ * w * x, hWxX ⟨w, hw, by simp⟩⟩ := fun w hw =>
    Subtype.ext (coe_conjAut hXx _)
  have hA' : ∀ y (hy : y ∈ rightConjugate (uLeviW θ) x),
      Θ ⟨y, hWxX hy⟩ ∈ (stdW h).map β.toMonoidHom := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hγw w hw
    have h2 : (⟨(MulAut.conj x⁻¹).toMonoidHom w, hWxX ⟨w, hw, rfl⟩⟩ :
        ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) = ⟨x⁻¹ * w * x, hWxX ⟨w, hw,
          by simp⟩⟩ := Subtype.ext (by simp)
    rw [h2, ← h1, ← hβ]
    refine ⟨Θ ⟨w, hWX hw⟩, ?_, rfl⟩
    rw [← hWstd]
    exact ⟨⟨w, hWX hw⟩, hw, rfl⟩
  have hB' : ∀ g ∈ (stdW h).map β.toMonoidHom,
      ∃ y, ∃ hy : y ∈ rightConjugate (uLeviW θ) x, Θ ⟨y, hWxX hy⟩ = g := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hWstd] at hg
    obtain ⟨⟨w, hwX⟩, hw, rfl⟩ := hg
    refine ⟨x⁻¹ * w * x, ⟨w, hw, by simp⟩, ?_⟩
    change _ = β (Θ ⟨w, hwX⟩)
    rw [hβ]
    exact congrArg Θ (hγw w hw).symm
  have hψconj : ∀ g : stabE (ε := k) h, psiU h hR ((MulAut.conj g₀).toMonoidHom g) =
      (MulAut.conj (psiU h hR g₀)).toMonoidHom (psiU h hR g) := fun g => by
    simp [MulAut.conj_apply]
  have hθW : ((rightConjugate (uLeviW θ) x).subgroupOf A).map θ =
      (uBarW K k f).map (MulAut.conj (psiU h hR g₀)).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hA' a ha
      rw [hg₀] at h1
      obtain ⟨s', hs', hs'e⟩ := h1
      refine ⟨psiU h hR s', by rw [psiU_apply]; exact (mem_stdW_iff_uBarW h hk2 hs s').mp hs', ?_⟩
      have e1 : θ a = psiU h hR (Θ ⟨a, hWxX ha⟩) := by
        rw [hΘ]
        rfl
      rw [e1, ← hs'e, hψconj]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨w, hw, hwu⟩ := exists_mem_levLift hθ (commutator_uBarW hK hf) hu
      have hs₀ : Θ ⟨w, hWX hw⟩ ∈ stdW h := by
        rw [← hWstd]
        exact ⟨⟨w, hWX hw⟩, hw, rfl⟩
      have hψs₀ : psiU h hR (Θ ⟨w, hWX hw⟩) = u := by
        rw [hΘ, ← hwu]
        rfl
      have hmem : (MulAut.conj g₀).toMonoidHom (Θ ⟨w, hWX hw⟩) ∈
          (stdW h).map β.toMonoidHom := by
        rw [hg₀]
        exact ⟨_, hs₀, rfl⟩
      obtain ⟨y, hy, hye⟩ := hB' _ hmem
      refine ⟨⟨y, hWxA hy⟩, hy, ?_⟩
      have e1 : θ ⟨y, hWxA hy⟩ = psiU h hR (Θ ⟨y, hWxX hy⟩) := by
        rw [hΘ]
        rfl
      rw [e1, hye, hψconj, hψs₀]
  refine noNormalTwo_inf_centralizer_of_quot hθ hker hodd hWxA hWxperf ?_
  rw [hθW, ← centralizer_map_mulAut]
  exact noNormalTwo_map_mulAut (noNormalTwo_centralizer_uBarW h hf hk2) _

end Core

end CFSG.ComponentClassification.RankTwoClassical.URigid

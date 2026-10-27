module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A02
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A03

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

abbrev _root_.CFSG.ClassicalInvolution.Q8P.Asc77.T7E.Frame4 :=
  @CFSG.ClassicalInvolution.Asc77.T7E.Frame4

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem inf_W_conj_of_img (c : Q3.Q3CL.Thompson.Ctx Ω W) {m : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) (σ ρ₀ : Thompson.Rep Ω W)
    (h : σ.img = Thompson.piG W m * ρ₀.img * (Thompson.piG W m)⁻¹) :
    σ.K ⊓ W = conjSub m (ρ₀.K ⊓ W) := by
  have hK : σ.K = conjSub m ρ₀.K :=
    c.K_eq_of_img_eq σ (T7D.conjRep c.hΩ hm ρ₀) (by rw [T7D.conjRep_img]; exact h)
  rw [hK, conjSub_inf_W hm]
namespace Frame4
open CFSG.ClassicalInvolution.Asc77.T7E.Frame4

theorem exists_gens [hcl : Fact (Q3.Q3CL.ClassicalClause Ω)] (c : Q3.Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω
    W) :
    ∃ x₁ x₂ x₃ : G, Subgroup.zpowers x₁ = F.ρ.R ⊓ W ∧ Subgroup.zpowers x₂ = F.ρ'.R ⊓ W ∧
    Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W ∧
    F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹ ∧ F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂ ∧ F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁ ∧
    F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁ ∧ F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹ ∧
    F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂ ∧
    F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃ ∧ F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃ ∧
    F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹ := by
  obtain ⟨x₁, h₁⟩ := Q3.Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ.hR
  obtain ⟨v₂, hv₂⟩ := Q3.Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ'.hR
  obtain ⟨v₃, hv₃⟩ := Q3.Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ₃.hR
  obtain ⟨x₃, hx₃, hs₁, hr₃⟩ := c.rel_exact F.hne₁ F.hn₁ h₁ hv₃
  have h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W := hx₃.trans hv₃
  obtain ⟨x₂, hx₂, ht₃, hs₂⟩ := c.rel_exact (F.hne₂.symm) F.hn₂' h₃ hv₂
  have h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W := hx₂.trans hv₂
  have m₁ : x₁ ∈ F.ρ.K ⊓ W := mem_inf_of_mem_inf (h₁ ▸ Subgroup.mem_zpowers x₁)
  have m₂ : x₂ ∈ F.ρ'.K ⊓ W := mem_inf_of_mem_inf (h₂ ▸ Subgroup.mem_zpowers x₂)
  have m₃ : x₃ ∈ F.ρ₃.K ⊓ W := mem_inf_of_mem_inf (h₃ ▸ Subgroup.mem_zpowers x₃)
  have cen : ∀ (ρ σ : Thompson.Rep Ω W), σ.K ∈ omegaNbr Ω ρ.K → ∀ {x : G}, x ∈ σ.K ⊓ W →
      ρ.r * x * ρ.r⁻¹ = x := fun ρ σ hnbr x hx => by
    rw [c.centralizes ρ σ hnbr hx]
    group
  refine ⟨x₁, x₂, x₃, h₁, h₂, h₃, c.conj_inv F.ρ m₁, cen _ _ F.hnbr m₂, hr₃,
    cen _ _ F.hnbr' m₁, c.conj_inv F.ρ' m₂, ht₃, hs₁, hs₂, c.conj_inv F.ρ₃ m₃⟩

theorem orders (c : Q3.Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω W) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) :
    ∃ m : ℕ, 0 < m ∧ orderOf x₁ = 4 * m ∧ orderOf x₂ = 4 * m ∧ orderOf x₃ = 4 * m ∧
      x₁ ^ (2 * m) = F.z ∧ x₂ ^ (2 * m) = F.z ∧ x₃ ^ (2 * m) = F.j := by
  have hord : ∀ (ρ : Thompson.Rep Ω W) (x : G), Subgroup.zpowers x = ρ.R ⊓ W →
      2 * orderOf x = Nat.card ρ.R := by
    intro ρ x hx
    have h1 : orderOf x = Nat.card ↥(ρ.R ⊓ W) := by rw [← Nat.card_zpowers, hx]
    rw [h1]
    exact (Q3.Q3CL.Thompson.D_card c.hΩ c.hW ρ.hR).symm
  obtain ⟨N, hcard⟩ : ∃ N : ℕ, ∀ ρ : Thompson.Rep Ω W, Nat.card ρ.R = 2 ^ N :=
    by
      obtain ⟨N, hN⟩ := F.ρ.hRK.2.1.exists_card_eq
      exact ⟨N, fun ρ =>
          (CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq c.hΩ ρ.hK
          F.ρ.hK ρ.hRK
        F.ρ.hRK).trans hN⟩
  have h4 : 4 ≤ orderOf x₁ := by
    have := (Q3.Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW F.ρ.hR F.ρ.hK F.ρ.hRK).2.2.2.1
    rwa [← h₁, Nat.card_zpowers] at this
  have e₁ := hord F.ρ x₁ h₁
  have e₂ := hord F.ρ' x₂ h₂
  have e₃ := hord F.ρ₃ x₃ h₃
  rw [hcard] at e₁ e₂ e₃
  have hN3 : 3 ≤ N := by
    by_contra hlt
    have : 2 ^ N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have hpow : (2 : ℕ) ^ N = 8 * 2 ^ k := by rw [hk, pow_add]; ring
  have hm : 0 < 2 ^ k := pow_pos (by norm_num) k
  have o₁ : orderOf x₁ = 4 * 2 ^ k := by omega
  have o₂ : orderOf x₂ = 4 * 2 ^ k := by omega
  have o₃ : orderOf x₃ = 4 * 2 ^ k := by omega
  have m₁ : x₁ ∈ F.ρ.K := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
  have m₂ : x₂ ∈ F.ρ'.K := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
  have m₃ : x₃ ∈ F.ρ₃.K := F.ρ₃.hRK.1 (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).1
  exact ⟨2 ^ k, hm, o₁, o₂, o₃, pow_half_eq F.hz m₁ hm o₁, pow_half_eq F.hz' m₂ hm o₂,
    pow_half_eq F.hj m₃ hm o₃⟩

theorem W_le_closure (c : Q3.Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) (r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂)
    (r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁)
    (t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂) :
    W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) := by
  set Wc := Subgroup.closure ({x₁, x₂, x₃} : Set G) with hWc
  have hx₁ : x₁ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₃ : x₃ ∈ Wc := Subgroup.subset_closure (by simp)
  have hKW : ∀ ρ : Thompson.Rep Ω W, ρ.K ⊓ W = ρ.R ⊓ W := fun ρ =>
    (Q3.Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK).1.symm
  have hsq : ∀ ρ : Thompson.Rep Ω W, ρ.img * ρ.img = 1 := fun ρ =>
    congrArg Subtype.val
      (Q3.Q3T8.Asc77.Thompson.muDelta_mul_self c.hΩ c.hW (T7D.imgQ_mem ρ))
  have hinv : ∀ ρ : Thompson.Rep Ω W, ρ.img⁻¹ = ρ.img := fun ρ =>
    inv_eq_of_mul_eq_one_right (hsq ρ)
  have key : ∀ σ : Thompson.Rep Ω W, σ.K ⊓ W ≤ Wc := by
    intro σ
    rcases swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃) hab
      hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
    · rw [c.K_eq_of_img_eq σ F.ρ (congrArg Subtype.val h), hKW, ← h₁]
      exact Subgroup.zpowers_le.mpr hx₁
    · rw [c.K_eq_of_img_eq σ F.ρ' (congrArg Subtype.val h), hKW, ← h₂]
      exact Subgroup.zpowers_le.mpr hx₂
    · rw [c.K_eq_of_img_eq σ F.ρ₃ (congrArg Subtype.val h), hKW, ← h₃]
      exact Subgroup.zpowers_le.mpr hx₃
    · have e1 : σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ.r * F.ρ₃.img * (Thompson.piG W F.ρ.r)⁻¹ := by
        show σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', r₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₁)
    · have e1 : σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ'.r * F.ρ₃.img * (Thompson.piG W F.ρ'.r)⁻¹ := by
        show σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ'.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', t₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₂)
    · have e1 : σ.img = F.ρ.img * F.ρ'.img * F.ρ₃.img * F.ρ'.img * F.ρ.img :=
        congrArg Subtype.val h
      have hm : F.ρ.r * F.ρ'.r ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.mul_mem _ F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hpm : Thompson.piG W (F.ρ.r * F.ρ'.r) = F.ρ.img * F.ρ'.img :=
        Thompson.piG_mul F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hval : σ.img = Thompson.piG W (F.ρ.r * F.ρ'.r) * F.ρ₃.img *
          (Thompson.piG W (F.ρ.r * F.ρ'.r))⁻¹ := by
        rw [hpm, mul_inv_rev, hinv, hinv, e1]
        simp only [mul_assoc]
      rw [inf_W_conj_of_img c hm σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers']
      have : (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹ = x₃ * x₁ * x₂ := by
        calc (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹
            = F.ρ.r * (F.ρ'.r * x₃ * F.ρ'.r⁻¹) * F.ρ.r⁻¹ := by group
          _ = F.ρ.r * (x₃ * x₂) * F.ρ.r⁻¹ := by rw [t₃]
          _ = (F.ρ.r * x₃ * F.ρ.r⁻¹) * (F.ρ.r * x₂ * F.ρ.r⁻¹) := by group
          _ = x₃ * x₁ * x₂ := by rw [r₃, r₂]
      rw [this]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem (Wc.mul_mem hx₃ hx₁) hx₂)
  obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := c.hW
  obtain ⟨S, hWS⟩ := Thompson.exists_sylow_ge_of_mem_WSet c.hW
  have hηW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  intro w hw
  rw [hWη] at hw
  refine (iSup₂_le (fun V hV => ?_) : (⨆ V ∈ η, V : Subgroup G) ≤ Wc) hw
  have hVU : V ∈ USet Ω := (hη.1 hV).1
  obtain ⟨J, hJ, hVJ⟩ := c.hΩ.exists_member_of_mem_USet hVU
  obtain ⟨T, hTD, hTJ⟩ := Q3.Q3CL.Thompson.exists_sylow_mem_DSet c.hΩ c.hW hWS hJ hVU hVJ
    ((hηW V hV).trans hWS)
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep c.hΩ c.hW hJ hTJ hTD
  have := key σ
  rw [hσK] at this
  exact (le_inf hVJ (hηW V hV)).trans this
end Frame4
end T7E
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_frame4_of_sylow [CoreLike G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) {R R' : Subgroup G}
    (hRsyl : IsSylow2In R K) (hR'syl : IsSylow2In R' K') (hRD : R ∈ DSet Ω W)
    (hR'D : R' ∈ DSet Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.ρ.R = R ∧
      F.ρ'.R = R' ∧ F.z = z ∧ T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Q3.Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hS4
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, hρR, hρ'R, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)
end T7E
end Asc77

end

end CFSG.ClassicalInvolution.Q8P

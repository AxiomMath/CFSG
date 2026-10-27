module

public import CFSG.CGT.PushingUpLit.BHS7.SymNestedData
public import CFSG.CGT.PushingUpLit.BHS7.SevenEleven
public import CFSG.CGT.PushingUpLit.BHS6.SixEightPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ} {m : ℕ}

theorem exists_mem_cenModSub_cyc (h : MinCex G T) (hZ : ⁅vSub G T, zSub T⁆ = ⊥)
    (hEb : IsBTBlock G T E) (X : SymModel G T E m) (hF : IsBTBlock G T F) (hFC : ¬ F ≤ cStarIn G T)
    (hFT : ∀ x ∈ qSub (vSub G T) T, ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ))
    (hFE : F ≤ E) (N : NestedData X F hFE) {a : Fin (2 * m + 1)} (haΩ : a ∈ N.Ω₀)
    {t₁ : Equiv.Perm (Fin (2 * m + 1))} (ht₁ : t₁ ∈ X.T') (ha1 : t₁ a ≠ a)
    {t : Equiv.Perm (Fin (2 * m + 1))} (ht : t ∈ X.T') {x : Fin (2 * m + 1)} (hx : t x ≠ x)
    (hxΩ : x ∉ N.Ω₀) :
    ∃ g : ↥E, (g : Γ) ∈ cenModSub G (vSub G T) (qSub (vSub G T) T)
        (le_normalizer_vSub G T) ∧ X.M.Ψ g = cyc x (t x) X.c := by
  classical
  have hG : CharTwo G := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := hT
  have hEG : E ≤ G := hEb.le
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT2
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hT₀G : qSub (vSub G T) T ≤ G := qSub_le.trans hT2.1
  have hT₀2 : IsPGroup 2 ↥(qSub (vSub G T) T) := hT2.2.1.to_le qSub_le
  have hbΩ : t₁ a ∈ N.Ω₀ := (N.hinv t₁ ht₁ a).2 haΩ
  have hab : a ≠ t₁ a := ha1.symm
  have hxt : t x ∉ N.Ω₀ := fun hmem => hxΩ ((N.hinv t ht x).1 hmem)
  have hxa : x ≠ a := fun e' => hxΩ (e' ▸ haΩ)
  have hxb : x ≠ t₁ a := fun e' => hxΩ (e' ▸ hbΩ)
  have htb : t x ≠ t₁ a := fun e' => hxt (e' ▸ hbΩ)
  obtain ⟨-, hay, -⟩ := pair_ne_of_ne X.hs X.hc ht₁ ht ha1 hx hxa hxb
  have hac : a ≠ X.c := fun e' => ha1 (by rw [e']; exact X.hcfix t₁ ht₁)
  have hbc : t₁ a ≠ X.c := fun e' => hac (by
    have h1 := X.hcfix t₁ ht₁
    rw [← e', isSwap_apply_apply (X.hs t₁ ht₁) a] at h1
    exact h1.trans e')
  set σ : Equiv.Perm (Fin (2 * m + 1)) := pairExchange x a (t x) (t₁ a) with hσ
  have hσN : σ ∈ Subgroup.normalizer
      (Subgroup.closure X.T' : Set (Equiv.Perm (Fin (2 * m + 1)))) :=
    pairExchange_mem_normalizer X.hs X.hc ht₁ ht ha1 hx hxa hxb
  have hσsign : Equiv.Perm.sign σ = 1 := sign_pairExchange hxa htb
  have σa : σ a = x := pairExchange_apply_a hay hab
  have σb : σ (t₁ a) = t x := pairExchange_apply_b hx hay.symm
  have σx : σ x = a := pairExchange_apply_x hx.symm hxb
  have σy : σ (t x) = t₁ a := pairExchange_apply_y hxb.symm ha1
  have σc : σ X.c = X.c := pairExchange_apply_of_fixed X.hs ht₁ ht ha1 hx X.hcfix
  obtain ⟨e, he⟩ := X.hsurj σ (Equiv.Perm.mem_alternatingGroup.2 hσsign)
  have heN : (e : Γ) ∈ Subgroup.normalizer (baum T : Set Γ) :=
    mem_normalizer_baum_of_Ψ_mem_normalizer hT2 hEb X e (by rw [he]; exact hσN)
  have heC : (e : Γ) ∈ cStarIn G T := inf_normalizer_baum_le_cStarIn hb0 ⟨hEG e.2, heN⟩
  set F' : Subgroup Γ := A1b.conjSub (e : Γ) F with hF'
  have hF'mem : ∀ g : Γ, g ∈ F' ↔ (e : Γ)⁻¹ * g * (e : Γ) ∈ F := fun g => A1b.mem_conjSub_iff
  have hF'C : ¬ F' ≤ cStarIn G T := by
    intro hle
    apply hFC
    intro f hf
    have h1 : (e : Γ) * f * (e : Γ)⁻¹ ∈ F' := by
      rw [hF'mem]
      have : (e : Γ)⁻¹ * ((e : Γ) * f * (e : Γ)⁻¹) * (e : Γ) = f := by group
      rw [this]
      exact hf
    have h2 := hle h1
    have h3 := (cStarIn G T).mul_mem ((cStarIn G T).mul_mem ((cStarIn G T).inv_mem heC) h2) heC
    have : (e : Γ)⁻¹ * ((e : Γ) * f * (e : Γ)⁻¹) * (e : Γ) = f := by group
    rwa [this] at h3
  have hF'b : IsBTBlock G T F' := by
    have h1 := isBTBlock_conj (e : Γ) hF
    have hG' : A1b.conjSub (e : Γ) G = G :=
      conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer (hEG e.2))
    have hb' : baum (A1b.conjSub (e : Γ) T) = baum T := by
      rw [baum_conjSub]
      exact conjSub_eq_of_mem_normalizer heN
    rw [hG'] at h1
    exact isBTBlock_of_sub h1 le_rfl hb' hF'C
  have hF'E : F' ≤ E := by
    intro g hg
    have hf : (e : Γ)⁻¹ * g * (e : Γ) ∈ F := (hF'mem g).1 hg
    have : g = (e : Γ) * ((e : Γ)⁻¹ * g * (e : Γ)) * (e : Γ)⁻¹ := by group
    rw [this]
    exact E.mul_mem (E.mul_mem e.2 (hFE hf)) (E.inv_mem e.2)
  set w₀ : Γ := X.vec (pairVec a (t₁ a)) with hw₀
  have hw₀F : w₀ ∈ blockW F := N.vec_pairVec_mem_blockW h hEb X hF hFE haΩ hbΩ hab
  have hFV : ⁅F, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hF.le hFC
  have hWT : ⁅blockW F, qSub (vSub G T) T⁆ = ⊥ :=
    commutator_blockW_eq_bot_of_comm_mod hG hT hF hVQ hGV hFV hT₀2 hT₀G hFT
  have hT₀w : ∀ y ∈ qSub (vSub G T) T, w₀ * y = y * w₀ := by
    intro y hy
    have h1 : ⁅w₀, y⁆ ∈ (⁅blockW F, qSub (vSub G T) T⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw₀F hy
    rw [hWT, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set L : Subgroup Γ := G ⊓ Subgroup.centralizer ({w₀} : Set Γ) with hL
  have hmemL : ∀ g : Γ, g ∈ L ↔ g ∈ G ∧ w₀ * g = g * w₀ := by
    intro g
    rw [hL, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
  have hT₀L : qSub (vSub G T) T ≤ L := fun y hy => (hmemL y).2 ⟨hT₀G hy, hT₀w y hy⟩
  have hBL : baum T ≤ L := by
    intro y hy
    refine (hmemL y).2 ⟨hT2.1 ((inf_le_left : baum T ≤ T) hy), ?_⟩
    have h2 : y * w₀ * y⁻¹ = w₀ := X.conj_vec_baum_pair hEb ⟨y, hy⟩ ht₁ ha1
    calc w₀ * y = (y * w₀ * y⁻¹) * y := by rw [h2]
      _ = y * w₀ := by group
  have hF'L : F' ≤ L := by
    intro g hg
    have hgE : g ∈ E := hF'E hg
    refine (hmemL g).2 ⟨hEG hgE, ?_⟩
    have hf : (e : Γ)⁻¹ * g * (e : Γ) ∈ F := (hF'mem g).1 hg
    have hΨg : X.M.Ψ ⟨g, hgE⟩ = σ * X.M.Ψ ⟨(e : Γ)⁻¹ * g * (e : Γ), hFE hf⟩ * σ⁻¹ := by
      have : (⟨g, hgE⟩ : ↥E) = e * ⟨(e : Γ)⁻¹ * g * (e : Γ), hFE hf⟩ * e⁻¹ := by
        apply Subtype.ext
        show g = (e : Γ) * ((e : Γ)⁻¹ * g * (e : Γ)) * (e : Γ)⁻¹
        group
      rw [this, map_mul, map_mul, map_inv, he]
    have hfx := N.hfix ⟨(e : Γ)⁻¹ * g * (e : Γ), hf⟩ x hxΩ
    have hfy := N.hfix ⟨(e : Γ)⁻¹ * g * (e : Γ), hf⟩ (t x) hxt
    have hga : X.M.Ψ ⟨g, hgE⟩ a = a := by
      rw [hΨg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have : σ⁻¹ a = x := by rw [Equiv.Perm.inv_eq_iff_eq, σx]
      rw [this, hfx, σx]
    have hgb : X.M.Ψ ⟨g, hgE⟩ (t₁ a) = t₁ a := by
      rw [hΨg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have : σ⁻¹ (t₁ a) = t x := by rw [Equiv.Perm.inv_eq_iff_eq, σy]
      rw [this, hfy, σy]
    have hconj := X.conj_vec ⟨g, hgE⟩ (pairVec a (t₁ a))
    rw [coreAct_pairVec, hga, hgb] at hconj
    calc w₀ * g = (g * w₀ * g⁻¹) * g := by rw [hw₀, hconj]
      _ = g * w₀ := by group
  have hLG : L < G := by
    refine lt_of_le_of_ne (fun g hg => ((hmemL g).1 hg).1) ?_
    intro hEq
    have hπ : cyc a (t₁ a) X.c ∈ alternatingGroup (Fin (2 * m + 1)) :=
      cyc_mem_alternatingGroup hab hac hbc
    obtain ⟨e', he'⟩ := X.hsurj _ hπ
    have he'L : (e' : Γ) ∈ L := by rw [hEq]; exact hEG e'.2
    have h1 := ((hmemL _).1 he'L).2
    have h2 := X.conj_vec e' (pairVec a (t₁ a))
    rw [he', coreAct_pairVec, cyc_apply_first hac hbc, cyc_apply_second hab hbc] at h2
    have h3 : (e' : Γ) * w₀ * (e' : Γ)⁻¹ = w₀ := by
      calc (e' : Γ) * w₀ * (e' : Γ)⁻¹ = (w₀ * (e' : Γ)) * (e' : Γ)⁻¹ := by rw [← h1]
        _ = w₀ := by group
    rw [hw₀, h2] at h3
    have h4 := X.vec_injective h3
    have h5 := congrArg (fun v => vcoord v X.c) h4
    simp only [vcoord_pairVec] at h5
    have h6 : X.c ≠ a := fun e'' => hac e''.symm
    have h7 : X.c ≠ t₁ a := fun e'' => hbc e''.symm
    simp [h6, h7] at h5
  have hL : L ∈ lSet G T := ⟨hLG, hBL, fun hle => hF'C (hF'L.trans hle)⟩
  have hT0L : tZero G T ≤ L := by
    rw [tZero_of_eq hZ]
    exact hT₀L
  have key := seven_eleven h hF'b hF'C hL hF'L hT0L
  rw [tZero_of_eq hZ] at key
  have hπ₀ : cyc a (t₁ a) X.c ∈ altOn N.Ω₀ := cyc_mem_altOn haΩ hbΩ N.hcmem hab hac hbc
  obtain ⟨f₀, hf₀⟩ := N.hgen _ hπ₀
  have hgF' : (e : Γ) * (f₀ : Γ) * (e : Γ)⁻¹ ∈ F' := by
    rw [hF'mem]
    have : (e : Γ)⁻¹ * ((e : Γ) * (f₀ : Γ) * (e : Γ)⁻¹) * (e : Γ) = (f₀ : Γ) := by group
    rw [this]
    exact f₀.2
  have hgE : (e : Γ) * (f₀ : Γ) * (e : Γ)⁻¹ ∈ E := hF'E hgF'
  refine ⟨⟨(e : Γ) * (f₀ : Γ) * (e : Γ)⁻¹, hgE⟩, ?_, ?_⟩
  · refine ⟨hEG hgE, fun f hf => ?_⟩
    have := (Subgroup.centralizer (vSub G T : Set Γ)).inv_mem (key f hf _ hgF')
    rwa [commutatorElement_inv] at this
  · have : (⟨(e : Γ) * (f₀ : Γ) * (e : Γ)⁻¹, hgE⟩ : ↥E) = e * ⟨(f₀ : Γ), hFE f₀.2⟩ * e⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, he, hf₀, conj_cyc, σa, σb, σc]

end CFSG.CGT.PushingUpLit.BHS7

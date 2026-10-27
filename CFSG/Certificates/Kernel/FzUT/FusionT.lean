module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Elt
public import CFSG.Certificates.Kernel.FzUT.Transport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Rules

public section

namespace CFSG.KC.FzUT

open Certificates.FzL26 Certificates.FzR10
open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

theorem card_filter_bij {φ ψ : ℕ → ℕ} (hφ : ∀ x < 512, φ x < 512) (hψ : ∀ x < 512, ψ x < 512)
    (hψφ : ∀ x < 512, ψ (φ x) = x) (hφψ : ∀ x < 512, φ (ψ x) = x) (p q : ℕ → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ x < 512, p x ↔ q (φ x)) :
    ((Finset.range 512).filter p).card = ((Finset.range 512).filter q).card := by
  refine Finset.card_nbij' φ ψ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha ⊢
    exact ⟨hφ a ha.1, (hpq a ha.1).mp ha.2⟩
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha ⊢
    refine ⟨hψ a ha.1, (hpq _ (hψ a ha.1)).mpr ?_⟩
    rw [hφψ a ha.1]
    exact ha.2
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha
    exact hψφ a ha.1
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha
    exact hφψ a ha.1

section Map

variable {P P' : Par} {φ ψ : ℕ → ℕ} (hφ : ∀ x < 512, φ x < 512) (hψ : ∀ x < 512, ψ x < 512)
  (hψφ : ∀ x < 512, ψ (φ x) = x) (hφψ : ∀ x < 512, φ (ψ x) = x)
  (he : ∀ x y, x < 512 → y < 512 → φ (P'.e x y) = P.e (φ x) (φ y))
  (hlt : ∀ x y, x < 512 → y < 512 → P'.e x y < 512)

include hφ hψφ he hlt

theorem map_eq_iff {x y : ℕ} (hx : x < 512) (hy : y < 512) : φ x = φ y ↔ x = y := by
  constructor
  · intro h
    rw [← hψφ x hx, ← hψφ y hy, h]
  · rintro rfl
    rfl

theorem kord_map (h0 : φ 0 = 0) {x : ℕ} (hx : x < 512) : kord P'.e x = kord P.e (φ x) := by
  have hxx := hlt x x hx hx
  have h4 := hlt _ _ hxx hxx
  have h8 := hlt _ _ h4 h4
  have e0 : ∀ {y}, y < 512 → (P'.e y y = 0 ↔ P.e (φ y) (φ y) = 0) := by
    intro y hy
    have := map_eq_iff hφ hψφ he hlt (hlt y y hy hy) (show (0 : ℕ) < 512 by norm_num)
    rw [h0, he y y hy hy] at this
    exact this.symm
  have ex : x = 0 ↔ φ x = 0 := by
    have := map_eq_iff hφ hψφ he hlt hx (show (0 : ℕ) < 512 by norm_num)
    rw [h0] at this
    exact this.symm
  unfold kord
  have r1 := e0 hx
  have r2 := e0 hxx
  have r3 := e0 h4
  rw [he x x hx hx] at r2
  rw [he _ _ hxx hxx, he x x hx hx] at r3
  by_cases a : x = 0
  · rw [if_pos a, if_pos (ex.mp a)]
  rw [if_neg a, if_neg (fun h => a (ex.mpr h))]
  by_cases b : P'.e x x = 0
  · rw [if_pos b, if_pos (r1.mp b)]
  rw [if_neg b, if_neg (fun h => b (r1.mpr h))]
  by_cases c : P'.e (P'.e x x) (P'.e x x) = 0
  · rw [if_pos c, if_pos (r2.mp c)]
  rw [if_neg c, if_neg (fun h => c (r2.mpr h))]
  by_cases d : P'.e (P'.e (P'.e x x) (P'.e x x)) (P'.e (P'.e x x) (P'.e x x)) = 0
  · rw [if_pos d, if_pos (r3.mp d)]
  rw [if_neg d, if_neg (fun h => d (r3.mpr h))]

include hψ hφψ in
theorem rules_map (h0 : φ 0 = 0) (htI : P'.tI < 512) (hsI : P'.sI < 512)
    (htI' : φ P'.tI = P.tI) (hsI' : φ P'.sI = P.sI) (hgens : ∀ g ∈ P'.gens.toList, g < 512)
    (hrho : ∀ x < 256, P'.rhoMap x < 512 ∧ φ x < 256 ∧ φ (P'.rhoMap x) = P.rhoMap (φ x))
    (hTL : ∀ x < 512, P'.inTL x = P.inTL (φ x)) (hW : ∀ x < 512, P'.inW x = P.inW (φ x))
    (hTZ : ∀ x < 512, P'.inTZ x = P.inTZ (φ x)) {θ : ℕ → Prop} (hθ : FzRules P θ) :
    FzRules P' (fun x => x < 512 ∧ θ (φ x)) := by
  have inj : ∀ {x y : ℕ}, x < 512 → y < 512 → (φ x = φ y ↔ x = y) :=
    fun hx hy => map_eq_iff hφ hψφ he hlt hx hy
  have hψe : ∀ x y, x < 512 → y < 512 → ψ (P.e x y) = P'.e (ψ x) (ψ y) := by
    intro x y hx hy
    rw [← hφψ x hx, ← hφψ y hy, ← he _ _ (hψ x hx) (hψ y hy), hψφ _ (hlt _ _ (hψ x hx) (hψ y hy)),
      hφψ x hx, hφψ y hy]
  have htψ : ψ P.tI = P'.tI := by rw [← htI', hψφ _ htI]
  have hS : ∀ x < 512, fzrS P' x ↔ fzrS P (φ x) := by
    intro x hx
    simp only [fzrS]
    rw [← htI', ← he _ _ hx htI, ← he _ _ htI hx, inj (hlt _ _ hx htI) (hlt _ _ htI hx)]
    exact ⟨fun h => ⟨hφ x hx, h.2⟩, fun h => ⟨hx, h.2⟩⟩
  have hcent : ∀ u < 512, (fzrCent P' u).card = (fzrCent P (φ u)).card := by
    intro u hu
    unfold fzrCent
    refine card_filter_bij hφ hψ hψφ hφψ _ _ fun x hx => ?_
    rw [← he _ _ hx hu, ← he _ _ hu hx, inj (hlt _ _ hx hu) (hlt _ _ hu hx)]
  refine
    { mul := ⟨fun x y hx hy => hlt x y hx hy, fun x y z hx hy hz => ?_, fun x hx => ?_,
        fun x hx => ?_⟩
      tI_lt := htI
      sI_lt := hsI
      gens_lt := hgens
      rho_lt := fun x hx => (hrho x hx).1
      th_t := ⟨htI, by rw [htI']; exact hθ.th_t⟩
      th_inv := fun x hx => ?_
      conj := fun g x y hg hx hy hc => ?_
      rho := fun x hx => ?_
      forb := fun x hx htl hx0 hxx hxθ => ?_
      wrule := fun x hw hxθ => ?_
      ktl := fun x hx htl hx0 hxx => ?_
      kout := fun sp hsp l hl htl hl2 => ?_
      cover := fun f hf hft => ?_
      prof := fun u hu hc => ?_ }
  · rw [← inj (hlt _ _ (hlt _ _ hx hy) hz) (hlt _ _ hx (hlt _ _ hy hz)), he _ _ (hlt _ _ hx hy) hz,
      he _ _ hx hy, he _ _ hx (hlt _ _ hy hz), he _ _ hy hz]
    exact hθ.mul.assoc _ _ _ (hφ x hx) (hφ y hy) (hφ z hz)
  · rw [← inj (hlt _ _ hx (by norm_num)) hx, he _ _ hx (by norm_num), h0]
    exact hθ.mul.one_r _ (hφ x hx)
  · rw [← inj (hlt _ _ (by norm_num) hx) hx, he _ _ (by norm_num) hx, h0]
    exact hθ.mul.one_l _ (hφ x hx)
  · obtain ⟨hx5, hxθ⟩ := hx
    obtain ⟨-, h1, h2⟩ := hθ.th_inv _ hxθ
    refine ⟨hx5, fun h => h1 (by rw [h, h0]), ?_⟩
    rw [← inj (hlt _ _ hx5 hx5) (by norm_num), he _ _ hx5 hx5, h0]
    exact h2
  · have hc' : P.e (φ y) (φ g) = P.e (φ g) (φ x) := by
      rw [← he _ _ hy hg, ← he _ _ hg hx, hc]
    have := hθ.conj _ _ _ (hφ g hg) (hφ x hx) (hφ y hy) hc'
    exact ⟨fun h => ⟨hy, this.mp h.2⟩, fun h => ⟨hx, this.mpr h.2⟩⟩
  · obtain ⟨hr, hφx, hφr⟩ := hrho x hx
    have := hθ.rho _ hφx
    rw [← hφr] at this
    exact ⟨fun h => ⟨hr, this.mp h.2⟩, fun h => ⟨by omega, this.mpr h.2⟩⟩
  · refine hθ.forb _ (hφ x hx) (by rw [← hTL x hx]; exact htl) (fun h => hx0 ?_) ?_ hxθ.2
    · rw [← inj hx (by norm_num), h, h0]
    · rw [← he _ _ hx hx, hxx, h0]
  · rw [hTZ x hxθ.1]
    exact hθ.wrule _ (by rw [← hW x hxθ.1]; exact hw) hxθ.2
  · refine ⟨hlt _ _ htI hx, ?_⟩
    rw [he _ _ htI hx, htI']
    refine hθ.ktl _ (hφ x hx) (by rw [← hTL x hx]; exact htl) (fun h => hx0 ?_) ?_
    · rw [← inj hx (by norm_num), h, h0]
    · rw [← he _ _ hx hx, hxx, h0]
  · have hsp5 : sp < 512 := by
      rcases hsp with rfl | rfl
      · exact hsI
      · exact hlt _ _ htI hsI
    have hsp' : φ sp = P.sI ∨ φ sp = P.e P.tI P.sI := by
      rcases hsp with rfl | rfl
      · exact Or.inl hsI'
      · right
        rw [he _ _ htI hsI, htI', hsI']
    have hls := hlt _ _ hl hsp5
    have h2 : P.e (P.e (φ l) (φ sp)) (P.e (φ l) (φ sp)) = 0 := by
      rw [← he _ _ hl hsp5, ← he _ _ hls hls, hl2, h0]
    have := hθ.kout _ hsp' _ (hφ l hl) (by rw [← hTL l hl]; exact htl) h2
    rw [← he _ _ hl hsp5] at this
    exact ⟨fun h => ⟨hsp5, this.mp h.2⟩, fun h => ⟨hls, this.mpr h.2⟩⟩
  · have hg : ∀ x y, x < 512 → y < 512 →
        (f ∘ ψ) (P.e x y) = xor ((f ∘ ψ) x) ((f ∘ ψ) y) := by
      intro x y hx hy
      simp only [Function.comp_apply]
      rw [hψe x y hx hy]
      exact hf _ _ (hψ x hx) (hψ y hy)
    obtain ⟨x, hx, hxθ, hfx⟩ := hθ.cover (f ∘ ψ) hg (by simp only [Function.comp_apply]; rw [htψ]; exact hft)
    refine ⟨ψ x, hψ x hx, ⟨hψ x hx, ?_⟩, hfx⟩
    rw [hφψ x hx]
    exact hxθ
  · obtain ⟨hu5, huθ⟩ := hu
    rw [hcent u hu5] at hc
    obtain ⟨f₀, f₁, hf₀, hf₁, h0t, h1t, hcard, hkey⟩ := hθ.prof _ huθ hc
    have hkeyx : ∀ x < 512, fzrKey P' (fun x => x < 512 ∧ θ (φ x)) x = fzrKey P θ (φ x) := by
      intro x hx
      unfold fzrKey
      rw [kord_map hφ hψφ he hlt h0 hx]
      by_cases h : θ (φ x)
      · rw [if_pos ⟨hx, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2), if_neg h]
    have hH : ∀ x < 512, (fzrS P' x ∧ (f₀ ∘ φ) x = false ∧ (f₁ ∘ φ) x = false) ↔
        (fzrS P (φ x) ∧ f₀ (φ x) = false ∧ f₁ (φ x) = false) := by
      intro x hx
      rw [hS x hx]
      rfl
    refine ⟨f₀ ∘ φ, f₁ ∘ φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y hx hy
      simp only [Function.comp_apply]
      rw [he _ _ hx.1 hy.1]
      exact hf₀ _ _ ((hS x hx.1).mp hx) ((hS y hy.1).mp hy)
    · intro x y hx hx0 hy hy0
      simp only [Function.comp_apply]
      rw [he _ _ hx.1 hy.1]
      exact hf₁ _ _ ((hS x hx.1).mp hx) hx0 ((hS y hy.1).mp hy) hy0
    · simp only [Function.comp_apply]
      rw [htI']
      exact h0t
    · simp only [Function.comp_apply]
      rw [htI']
      exact h1t
    · rw [hcent u hu5, ← hcard]
      unfold fzrH
      exact card_filter_bij hφ hψ hψφ hφψ _ _ hH
    · intro k
      have e1 : ((fzrH P' (f₀ ∘ φ) (f₁ ∘ φ)).filter fun x =>
          fzrKey P' (fun x => x < 512 ∧ θ (φ x)) x = k).card =
          ((fzrH P f₀ f₁).filter fun x => fzrKey P θ x = k).card := by
        unfold fzrH
        rw [Finset.filter_filter, Finset.filter_filter]
        refine card_filter_bij hφ hψ hψφ hφψ _ _ fun x hx => ?_
        rw [hH x hx, hkeyx x hx]
      have e2 : ((fzrCent P' u).filter fun x =>
          fzrKey P' (fun x => x < 512 ∧ θ (φ x)) x = k).card =
          ((fzrCent P (φ u)).filter fun x => fzrKey P θ x = k).card := by
        unfold fzrCent
        rw [Finset.filter_filter, Finset.filter_filter]
        refine card_filter_bij hφ hψ hψφ hφψ _ _ fun x hx => ?_
        rw [hkeyx x hx, ← he _ _ hx hu5, ← he _ _ hu5 hx,
          inj (hlt _ _ hx hu5) (hlt _ _ hu5 hx)]
      rw [e1, e2]
      exact hkey k

end Map

abbrev parT (t s l : MulAut FzUT) : Par :=
  parOf (pctx ()) (fzAutI t) (actTab (fzAutI t) (fzAutI s) (fzAutI l))

theorem parT_e (t s l : MulAut FzUT) (x y : FzElt) :
    (parT t s l).e (fzEIdx x) (fzEIdx y) = fzEIdx (fzMulC t s l x y) := fzEm t s l x y

theorem fzIdx_Z : ∀ q : FzUT, fzIdx q % 16 = 0 ↔ FzInZ q := by
  unfold FzInZ
  decide +kernel

theorem eOf_digits {x : ℕ} (hx : x < 512) :
    fzIdx (fzEOf x).1 = x % 64 ∧ fzEIdx (fzEOf x) = fzIdx (fzEOf x).1 + 64 * (x / 64) := by
  have h1 : fzIdx (fzEOf x).1 = x % 64 := fzIdx_fzElt (Nat.mod_lt _ (by norm_num))
  have h2 := fzEIdx_fzEOf hx
  refine ⟨h1, ?_⟩
  rw [h2]
  have h3 : fzEIdx (fzEOf x) = fzIdx (fzEOf x).1 + 64 * ((fzEOf x).2.1.val +
      2 * (fzEOf x).2.2.1.val + 4 * (fzEOf x).2.2.2.val) := rfl
  rw [h2, h1] at h3
  omega

variable (β : MulAut FzUT)

@[expose] def phN (x : ℕ) : ℕ := fzEIdx (phiE β (fzEOf x))

@[expose] def phNi (x : ℕ) : ℕ := fzEIdx ((phiE β).symm (fzEOf x))

theorem phN_digits {x : ℕ} (hx : x < 512) :
    phN β x = fzIdx (β.symm (fzElt (x % 64))) + 64 * (x / 64) := by
  obtain ⟨h1, h2⟩ := eOf_digits hx
  have h3 : phN β x = fzIdx (β.symm (fzEOf x).1) + 64 * ((fzEOf x).2.1.val +
      2 * (fzEOf x).2.2.1.val + 4 * (fzEOf x).2.2.2.val) := rfl
  have h4 : fzEIdx (fzEOf x) = fzIdx (fzEOf x).1 + 64 * ((fzEOf x).2.1.val +
      2 * (fzEOf x).2.2.1.val + 4 * (fzEOf x).2.2.2.val) := rfl
  rw [h3]
  rw [h4] at h2
  have h5 : (fzEOf x).1 = fzElt (x % 64) := rfl
  rw [h5] at h2 ⊢
  omega

theorem phN_lt (x : ℕ) : phN β x < 512 := fzEIdx_lt _

theorem phNi_lt (x : ℕ) : phNi β x < 512 := fzEIdx_lt _

theorem phNi_phN {x : ℕ} (hx : x < 512) : phNi β (phN β x) = x := by
  unfold phN phNi
  rw [fzEOf_fzEIdx, Equiv.symm_apply_apply, fzEIdx_fzEOf hx]

theorem phN_phNi {x : ℕ} (hx : x < 512) : phN β (phNi β x) = x := by
  unfold phN phNi
  rw [fzEOf_fzEIdx, Equiv.apply_symm_apply, fzEIdx_fzEOf hx]

theorem phN_e (t s l : MulAut FzUT) {x y : ℕ} (hx : x < 512) (hy : y < 512) :
    phN β ((parT (cj β t) (cj β s) (cj β l)).e x y) =
      (parT t s l).e (phN β x) (phN β y) := by
  rw [← fzEIdx_fzEOf hx, ← fzEIdx_fzEOf hy, parT_e]
  unfold phN
  rw [fzEOf_fzEIdx, fzEOf_fzEIdx, fzEOf_fzEIdx, phi_mul, parT_e]

theorem parT_lt (t s l : MulAut FzUT) {x y : ℕ} (hx : x < 512) (hy : y < 512) :
    (parT t s l).e x y < 512 := by
  rw [← fzEIdx_fzEOf hx, ← fzEIdx_fzEOf hy, parT_e]
  exact fzEIdx_lt _

theorem phN_zero : phN β 0 = 0 := by
  have h : (0 : ℕ) = fzEIdx fzOneC := fzEIdx_one.symm
  unfold phN
  rw [h, fzEOf_fzEIdx]
  have : phiE β fzOneC = fzOneC := by simp [phiE_apply, fzOneC]
  rw [this]

theorem phN_v {x : ℕ} (hx : x < 64) (v : ℕ) (hv : v < 8) (h1 : β.symm (fzElt x) = fzElt x) :
    phN β (x + 64 * v) = x + 64 * v := by
  rw [phN_digits β (by omega)]
  have e1 : (x + 64 * v) % 64 = x := by omega
  have e2 : (x + 64 * v) / 64 = v := by omega
  rw [e1, e2, h1, fzIdx_fzElt hx]

theorem fzElt_zero : fzElt 0 = 1 := by decide +kernel

theorem ap_eq_iff (σ : MulAut FzUT) {x : ℕ} (hx : x < 64) :
    ((fzAutI σ).ap x == x) = decide (σ (fzElt x) = fzElt x) := by
  have h := fzAutI_ap σ (fzElt x)
  rw [fzIdx_fzElt hx] at h
  rw [h]
  by_cases e : σ (fzElt x) = fzElt x
  · rw [decide_eq_true e, e, fzIdx_fzElt hx]
    exact beq_self_eq_true x
  · rw [decide_eq_false e]
    apply beq_false_of_ne
    intro h'
    apply e
    rw [← fzElt_fzIdx (σ (fzElt x)), h']

theorem fix_cj_iff (σ : MulAut FzUT) (q : FzUT) :
    cj β σ q = q ↔ σ (β.symm q) = β.symm q := by
  rw [cj_apply]
  constructor
  · intro h
    have h' := congrArg β.symm h
    rwa [MulEquiv.symm_apply_apply] at h'
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem parOf_inTL (K : PCtx) (t : AutI) (act : Array ℕ) (x : ℕ) :
    (parOf K t act).inTL x = (t.ap (x % 64) == x % 64 && x / 64 % 4 == 0) := rfl

theorem parOf_inW (K : PCtx) (t : AutI) (act : Array ℕ) (x : ℕ) :
    (parOf K t act).inW x = (t.ap (x % 64) == x % 64 && decide (x / 64 < 2)) := rfl

theorem parOf_inTZ (K : PCtx) (t : AutI) (act : Array ℕ) (x : ℕ) :
    (parOf K t act).inTZ x = (x / 64 == 1 && x % 64 % 16 == 0) := rfl

theorem parOf_rho (K : PCtx) (t : AutI) (act : Array ℕ) (x : ℕ) :
    (parOf K t act).rhoMap x = rho0 (x % 64) + 64 * (x / 64) := rfl

theorem parOf_tI (K : PCtx) (t : AutI) (act : Array ℕ) : (parOf K t act).tI = 64 := rfl

theorem parOf_sI (K : PCtx) (t : AutI) (act : Array ℕ) : (parOf K t act).sI = 128 := rfl

theorem parOf_gens (K : PCtx) (t : AutI) (act : Array ℕ) :
    (parOf K t act).gens = #[1, 2, 4, 8, 64, 128, 256] := rfl

variable (hβ : ∀ x, β (fzRho0 x) = fzRho0 (β x))
include hβ

theorem fusion_cj {t s l : MulAut FzUT}
    (h : ¬ ∃ θ : ℕ → Prop, FzRules (parT (cj β t) (cj β s) (cj β l)) θ) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ := by
  rintro ⟨θ, hθ⟩
  have hb1 : β.symm (fzElt 0) = fzElt 0 := by rw [fzElt_zero, map_one]
  have hd : ∀ {x : ℕ}, x < 512 → x % 64 < 64 := fun _ => Nat.mod_lt _ (by norm_num)
  have hq : ∀ {x : ℕ}, x < 512 → phN β x % 64 = fzIdx (β.symm (fzElt (x % 64))) ∧
      phN β x / 64 = x / 64 := by
    intro x hx
    have := fzIdx_lt (β.symm (fzElt (x % 64)))
    rw [phN_digits β hx]
    omega
  have hq' : ∀ {x : ℕ}, x < 512 → fzElt (phN β x % 64) = β.symm (fzElt (x % 64)) := by
    intro x hx
    rw [(hq hx).1, fzElt_fzIdx]
  have hfix : ∀ {x : ℕ}, x < 512 →
      ((fzAutI (cj β t)).ap (x % 64) == x % 64) =
        ((fzAutI t).ap (phN β x % 64) == phN β x % 64) := by
    intro x hx
    rw [ap_eq_iff _ (hd hx), ap_eq_iff _ (hd (phN_lt β x)), hq' hx]
    by_cases hc : t (β.symm (fzElt (x % 64))) = β.symm (fzElt (x % 64))
    · simp [hc, (fix_cj_iff β t _).mpr hc]
    · have hc' : ¬ cj β t (fzElt (x % 64)) = fzElt (x % 64) := fun h' =>
        hc ((fix_cj_iff β t _).mp h')
      simp [hc, hc']
  have hgens : ∀ g ∈ (parT (cj β t) (cj β s) (cj β l)).gens.toList, g < 512 := by
    rw [parOf_gens]
    decide
  have htI : (parT (cj β t) (cj β s) (cj β l)).tI < 512 := by
    rw [parOf_tI]
    norm_num
  have hsI : (parT (cj β t) (cj β s) (cj β l)).sI < 512 := by
    rw [parOf_sI]
    norm_num
  have htI' : phN β (parT (cj β t) (cj β s) (cj β l)).tI = (parT t s l).tI := by
    rw [parOf_tI, parOf_tI]
    exact phN_v β (x := 0) (by norm_num) 1 (by norm_num) hb1
  have hsI' : phN β (parT (cj β t) (cj β s) (cj β l)).sI = (parT t s l).sI := by
    rw [parOf_sI, parOf_sI]
    exact phN_v β (x := 0) (by norm_num) 2 (by norm_num) hb1
  refine h ⟨_, rules_map (fun x _ => phN_lt β x) (fun x _ => phNi_lt β x)
    (fun x hx => phNi_phN β hx) (fun x hx => phN_phNi β hx) (fun x y hx hy => phN_e β t s l hx hy)
    (fun x y hx hy => parT_lt _ _ _ hx hy) (phN_zero β) htI hsI htI' hsI' hgens ?_ ?_ ?_ ?_ hθ⟩
  · intro x hx
    have hx5 : x < 512 := by omega
    have hr : rho0 (x % 64) = fzIdx (fzRho0 (fzElt (x % 64))) := by
      rw [← fzIdx_rho0, fzIdx_fzElt (hd hx5)]
    have hrl := fzIdx_lt (fzRho0 (fzElt (x % 64)))
    have hr5 : rho0 (x % 64) + 64 * (x / 64) < 512 := by omega
    rw [parOf_rho, parOf_rho]
    refine ⟨hr5, ?_, ?_⟩
    · have := (hq hx5).2
      have := (hq hx5).1
      have := fzIdx_lt (β.symm (fzElt (x % 64)))
      omega
    · rw [phN_digits β hr5, (hq hx5).1, (hq hx5).2, fzIdx_rho0, ← symm_rho β hβ]
      have e1 : (rho0 (x % 64) + 64 * (x / 64)) % 64 = rho0 (x % 64) := by omega
      have e2 : (rho0 (x % 64) + 64 * (x / 64)) / 64 = x / 64 := by omega
      rw [e1, e2, hr, fzElt_fzIdx]
  · intro x hx
    rw [parOf_inTL, parOf_inTL, hfix hx, (hq hx).2]
  · intro x hx
    rw [parOf_inW, parOf_inW, hfix hx, (hq hx).2]
  · intro x hx
    rw [parOf_inTZ, parOf_inTZ, (hq hx).2, (hq hx).1]
    have e : x % 64 = fzIdx (fzElt (x % 64)) := (fzIdx_fzElt (hd hx)).symm
    have e2 : x % 64 % 16 = fzIdx (fzElt (x % 64)) % 16 := by rw [← e]
    have key : (x % 64 % 16 == 0) = (fzIdx (β.symm (fzElt (x % 64))) % 16 == 0) := by
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, beq_iff_eq, e2, fzIdx_Z, fzIdx_Z]
      exact ⟨fun h => inZ_map' β.symm h, fun h => by
        have := inZ_map' β h
        rwa [MulEquiv.apply_symm_apply] at this⟩
    rw [key]

end CFSG.KC.FzUT

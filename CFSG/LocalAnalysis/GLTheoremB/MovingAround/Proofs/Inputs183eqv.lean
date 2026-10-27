module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs183eqv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

section Diag

variable {Y : Type} [Group Y]

@[expose] def diagSub (b : Y) (p : ℕ) (X : Subgroup Y)
    (hc : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x) : ↥X →* Y where
  toFun x := Input183.oprod p (fun j => b ^ j * (x : Y) * (b ^ j)⁻¹)
  map_one' := by
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
    exact Input183.oprod_ones p
  map_mul' x y := by
    have e : (fun j => b ^ j * ((x * y : ↥X) : Y) * (b ^ j)⁻¹) =
        fun j => (b ^ j * (x : Y) * (b ^ j)⁻¹) * (b ^ j * (y : Y) * (b ^ j)⁻¹) := by
      funext j
      simp only [Subgroup.coe_mul]
      group
    simp only [e]
    exact Input183.oprod_mul_of_comm fun j k hj hk hjk =>
      hc j k hj hk hjk _ (Input183.mem_orbA x.2) _ (Input183.mem_orbA y.2)

theorem diagSub_apply (b : Y) (p : ℕ) (X : Subgroup Y)
    (hc : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x) (x : ↥X) :
    diagSub b p X hc x = Input183.oprod p (fun j => b ^ j * (x : Y) * (b ^ j)⁻¹) := rfl

end Diag

section Gen

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_of_gen {p : ℕ} (hp : p.Prime) {L M : Subgroup Y} {𝓛 : Set (Subgroup Y)}
    (D : Subgroup Y → Subgroup Y) (hDM : ∀ X ∈ 𝓛, D X ≤ M) (hML : M ≤ L)
    (hgen : ∀ m ∈ M, ∃ d ∈ ⨆ X ∈ 𝓛, D X, ∃ w ∈ L ⊓ Subgroup.centralizer (L : Set Y), m = d * w)
    (hDN : ∀ X ∈ 𝓛, ∀ m ∈ M, m ∈ Subgroup.normalizer (D X : Set Y))
    (hψ : ∀ X ∈ 𝓛, ∃ ψ : ↥X →* Y, ψ.range = D X)
    (hXq : ∀ X ∈ 𝓛, CFSG.Open.IsQuasisimple ↥X)
    {R : Subgroup Y} (hR : GLAPComponent p M R) : ∃ X ∈ 𝓛, R = D X := by
  classical
  set DD : Subgroup Y := ⨆ X ∈ 𝓛, D X with hDD
  have hDDM : DD ≤ M := iSup₂_le hDM
  have hRne : R ≠ ⊥ := Input183.glaPComponent_ne_bot' hR
  have hRperf : ⁅R, R⁆ = R := glaPComponent_perfect hR
  have hMM : ⁅M, M⁆ ≤ DD := by
    rw [Subgroup.commutator_le]
    intro m₁ hm₁ m₂ hm₂
    obtain ⟨d₁, hd₁, w₁, hw₁, rfl⟩ := hgen m₁ hm₁
    obtain ⟨d₂, hd₂, w₂, hw₂, rfl⟩ := hgen m₂ hm₂
    have hc₁ : ∀ l ∈ L, l * w₁ = w₁ * l := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw₁).2) l hl
    have hc₂ : ∀ l ∈ L, l * w₂ = w₂ * l := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw₂).2) l hl
    have hd₁L : d₁ ∈ L := hML (hDDM hd₁)
    have hd₂L : d₂ ∈ L := hML (hDDM hd₂)
    have hw₁L : w₁ ∈ L := (Subgroup.mem_inf.1 hw₁).1
    have e1 : d₁ * w₁ * (d₂ * w₂) = d₁ * d₂ * (w₁ * w₂) := by
      calc d₁ * w₁ * (d₂ * w₂) = d₁ * (d₂ * w₁) * w₂ := by rw [hc₁ d₂ hd₂L]; group
        _ = d₁ * d₂ * (w₁ * w₂) := by group
    have e2 : d₂ * w₂ * (d₁ * w₁) = d₂ * d₁ * (w₁ * w₂) := by
      calc d₂ * w₂ * (d₁ * w₁) = d₂ * (d₁ * w₂) * w₁ := by rw [hc₂ d₁ hd₁L]; group
        _ = d₂ * d₁ * (w₂ * w₁) := by group
        _ = d₂ * d₁ * (w₁ * w₂) := by rw [hc₂ w₁ hw₁L]
    have e3 : d₁ * w₁ * (d₂ * w₂) * (d₁ * w₁)⁻¹ * (d₂ * w₂)⁻¹ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by
      calc d₁ * w₁ * (d₂ * w₂) * (d₁ * w₁)⁻¹ * (d₂ * w₂)⁻¹
          = (d₁ * w₁ * (d₂ * w₂)) * (d₂ * w₂ * (d₁ * w₁))⁻¹ := by group
        _ = (d₁ * d₂ * (w₁ * w₂)) * (d₂ * d₁ * (w₁ * w₂))⁻¹ := by rw [e1, e2]
        _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by group
    rw [commutatorElement_def, e3]
    exact DD.mul_mem (DD.mul_mem (DD.mul_mem hd₁ hd₂) (DD.inv_mem hd₁)) (DD.inv_mem hd₂)
  have hRDD : R ≤ DD := by
    rw [← hRperf]
    exact (Subgroup.commutator_mono hR.1 hR.1).trans hMM
  have hex : ∃ X ∈ 𝓛, R ≤ D X := by
    by_contra hno
    push Not at hno
    set S : Subgroup Y := ((Subgroup.centralizer ((barX p M R : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map
        M.subtype with hS
    have hDS : ∀ X ∈ 𝓛, D X ≤ S := by
      intro X hX
      haveI : ((D X).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hDM X hX)).2 fun m hm => hDN X hX m hm
      rcases CFSG.HardMathSupport.Solomon.Coordinator.i183_le_or_commutator_eq_bot hp hR
          (hDM X hX) with h | h
      · exact absurd h (hno X hX)
      · refine (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (hDM X hX)).1 ?_
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hRS : R ≤ S := hRDD.trans (iSup₂_le hDS)
    have hRc : barX p M R ≤ Subgroup.centralizer ((barX p M R : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hR.1).2 hRS
    obtain ⟨r, hr, t, ht, hrt⟩ := Input183.exists_noncomm_of_isComponentOf hR.2.2.1
    exact hrt ((Subgroup.mem_centralizer_iff.1 (hRc ht)) r hr)
  obtain ⟨X₀, hX₀, hRX⟩ := hex
  obtain ⟨ψ, hψr⟩ := hψ X₀ hX₀
  have hsn : IsSubnormal R (D X₀) := isSubnormal_of_le_of_le hR.2.1 hRX (hDM X₀ hX₀)
  have hker : ψ.ker ≠ ⊤ := by
    intro htop
    apply hRne
    rw [eq_bot_iff]
    refine hRX.trans ?_
    rw [← hψr]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ψ.ker := htop ▸ Subgroup.mem_top x
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact Subgroup.one_mem _
  have hkc : ψ.ker ≤ Subgroup.center ↥X₀ := l119_normal_le_center (hXq X₀ hX₀) hker
  have hq : CFSG.Open.IsQuasisimple ↥(D X₀) := by
    have h1 := CFSG.ComponentClassification.Quasisimple.central_quotient (hXq X₀ hX₀) ψ.ker hkc
    have e : (↥X₀ ⧸ ψ.ker) ≃* ↥(D X₀) :=
      (QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hψr)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e h1
  rcases CFSG.HardMathSupport.Solomon.Coordinator.i183v_eq_or_le_center hsn hq with h | h
  · exact ⟨X₀, hX₀, h⟩
  · exfalso
    apply hRne
    rw [← hRperf, eq_bot_iff, Subgroup.commutator_le]
    intro r hr t ht
    obtain ⟨z, hz, rfl⟩ := h hr
    have hzt := Subgroup.mem_center_iff.1 hz ⟨t, hRX ht⟩
    have hzt' : t * (z : Y) = (z : Y) * t := congrArg Subtype.val hzt
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hzt'.symm

end Gen

section Cases

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_comp_of_centralizes {p : ℕ} (hp : p.Prime) {𝓛 : Set (Subgroup Y)} {b : Y}
    (hb : orderOf b = p) (hbN : b ∈ Subgroup.normalizer ((sSup 𝓛 : Subgroup Y) : Set Y))
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X ⊤)
    (hbC : b ∈ Subgroup.centralizer ((sSup 𝓛 : Subgroup Y) : Set Y))
    {R : Subgroup Y} (hR : GLAPComponent p (sSup 𝓛 ⊓ Subgroup.centralizer ({b} : Set Y)) R) :
    ∃ X ∈ 𝓛, R = X := by
  classical
  set L : Subgroup Y := sSup 𝓛 with hL
  have hp0 : 0 < p := hp.pos
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x :=
    fun X hX X' hX' hne x hx y hy =>
      Prop95Parts.Input18.comp_comm (hcomp X hX) (hcomp X' hX') hne hx hy
  have hcompL : ∀ X ∈ 𝓛, IsComponentOf X L := fun X hX => l119_isComponentOf_sSup hcomp hcomm hX
  have hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j ∈ 𝓛 := fun X hX j =>
    Input183.orbA_mem_family hL hcompL hcomm hbN hX j
  have hXL : ∀ X ∈ 𝓛, X ≤ L := fun X hX => le_sSup hX
  have hbX : ∀ X ∈ 𝓛, b ∈ Subgroup.normalizer (X : Set Y) := fun X hX =>
    Input183.normalizer_of_commute fun s hs =>
      ((Subgroup.mem_centralizer_iff.1 hbC) s (hXL X hX hs)).symm
  have horb : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j = X := by
    intro X hX j
    induction j with
    | zero => exact Input183.orbA_zero b X
    | succ j ih =>
      rw [Input183.orbA_succ, ih]
      exact gLBConj_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hbX X hX))
  have hOJ : ∀ X ∈ 𝓛, Input183.OJ b X = X := by
    intro X hX
    rw [Input183.OJ_eq_fin hb hp0]
    simp only [horb X hX]
    haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
    exact iSup_const
  have hDM : ∀ X ∈ 𝓛, X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) := fun X hX x hx =>
    Subgroup.mem_inf.2 ⟨hXL X hX hx, Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hbC) x (hXL X hX hx))⟩
  have hDOJ : ∀ X ∈ 𝓛, X ≤ Input183.OJ b X := fun X hX => by rw [hOJ X hX]
  have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z →
        o ∈ (fun X : Subgroup Y => X) X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) :=
    fun X hX o ho _ _ _ => Subgroup.mem_sup_left (show o ∈ X from by rw [hOJ X hX] at ho; exact ho)
  have hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, Input183.OJ b X = Input183.OJ b X' →
      (fun X : Subgroup Y => X) X' ≤
        (fun X : Subgroup Y => X) X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) :=
    fun X hX X' hX' h =>
      (le_of_eq (by rw [hOJ X hX, hOJ X' hX'] at h; exact h.symm)).trans le_sup_left
  obtain ⟨hC1, hC2⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm (fun X : Subgroup Y => X)
    hDM hDOJ hSO hDeq
  exact eq_of_gen hp (fun X : Subgroup Y => X) hDM inf_le_left hC1 hC2
    (fun X _ => ⟨X.subtype, Subgroup.range_subtype X⟩) (fun X hX => (hcomp X hX).2.2) hR

theorem eq_diag_of_moves {p : ℕ} (hp : p.Prime) {𝓛 : Set (Subgroup Y)} {b : Y}
    (hb : orderOf b = p) (hbN : b ∈ Subgroup.normalizer ((sSup 𝓛 : Subgroup Y) : Set Y))
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X ⊤)
    (hnot : ∀ X ∈ 𝓛, b ∉ Subgroup.normalizer (X : Set Y))
    {R : Subgroup Y} (hR : GLAPComponent p (sSup 𝓛 ⊓ Subgroup.centralizer ({b} : Set Y)) R) :
    ∃ X ∈ 𝓛, ∃ hc : (∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x), R = (diagSub b p X hc).range := by
  classical
  set L : Subgroup Y := sSup 𝓛 with hL
  have hp0 : 0 < p := hp.pos
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x :=
    fun X hX X' hX' hne x hx y hy =>
      Prop95Parts.Input18.comp_comm (hcomp X hX) (hcomp X' hX') hne hx hy
  have hcompL : ∀ X ∈ 𝓛, IsComponentOf X L := fun X hX => l119_isComponentOf_sSup hcomp hcomm hX
  have hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j ∈ 𝓛 := fun X hX j =>
    Input183.orbA_mem_family hL hcompL hcomm hbN hX j
  have hAcomm_of : ∀ X ∈ 𝓛, ∀ j k : ℕ, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x := fun X hX j k hj hk hjk x hx y hy =>
    hcomm _ (hmem X hX j) _ (hmem X hX k)
      (Input183.orbA_ne_of_not_normalizer hp hb (hnot X hX) hj hk hjk) x hx y hy
  have hAL : ∀ X ∈ 𝓛, ∀ j < p, Input183.orbA b X j ≤ L := fun X hX j _ => le_sSup (hmem X hX j)
  let Dg : Subgroup Y → Subgroup Y := fun X =>
    if h : X ∈ 𝓛 then (diagSub b p X (hAcomm_of X h)).range else ⊥
  have hDg : ∀ X (hX : X ∈ 𝓛), Dg X = (diagSub b p X (hAcomm_of X hX)).range :=
    fun X hX => dif_pos hX
  have hdiag_fixed : ∀ X (hX : X ∈ 𝓛) (x : ↥X),
      b * diagSub b p X (hAcomm_of X hX) x * b⁻¹ = diagSub b p X (hAcomm_of X hX) x :=
    fun X hX x => Input183.diag_shift hb hp0 (hAcomm_of X hX) (x : Y) x.2
  have hDM : ∀ X ∈ 𝓛, Dg X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [diagSub_apply]
      exact Input183.oprod_mem fun j hj => hAL X hX j hj (Input183.mem_orbA x.2)
    · exact (mul_inv_eq_iff_eq_mul.1 (hdiag_fixed X hX x)).symm
  have hDOJ : ∀ X ∈ 𝓛, Dg X ≤ Input183.OJ b X := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    rw [diagSub_apply]
    exact Input183.oprod_mem fun j _ => Input183.orbA_le_OJ b X j (Input183.mem_orbA x.2)
  have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z → o ∈ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
    intro X hX o ho z hz h
    rw [Input183.OJ_eq_fin hb hp0] at ho
    obtain ⟨x, hxX, w, hw, rfl⟩ := Input183.orbit_fixed hp0 hb hL hcomm
      (fun j _ => hmem X hX j) (fun j hj => hAL X hX j hj) (hAcomm_of X hX) hbN ho hz h
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hw)
    rw [hDg X hX]
    exact MonoidHom.mem_range.2 ⟨⟨x, hxX⟩, rfl⟩
  have hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, Input183.OJ b X = Input183.OJ b X' →
      Dg X' ≤ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
    intro X hX X' hX' h d hd
    have hdOJ := hDOJ X' hX' hd
    rw [← h] at hdOJ
    rw [hDg X' hX'] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    have hfix : b * diagSub b p X' (hAcomm_of X' hX') x * b⁻¹ =
        diagSub b p X' (hAcomm_of X' hX') x * 1 := by
      rw [mul_one]
      exact hdiag_fixed X' hX' x
    exact hSO X hX _ hdOJ 1 (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem hfix
  obtain ⟨hC1, hC2⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm Dg hDM hDOJ hSO hDeq
  obtain ⟨X, hX, hRX⟩ := eq_of_gen hp Dg hDM inf_le_left hC1 hC2
    (fun X hX => ⟨diagSub b p X (hAcomm_of X hX), (hDg X hX).symm⟩)
    (fun X hX => (hcomp X hX).2.2) hR
  exact ⟨X, hX, hAcomm_of X hX, hRX.trans (hDg X hX)⟩

end Cases

section Img

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def toImg (p : ℕ) {C J : Subgroup G} (hJC : J ≤ C) : ↥J →* ↥(barX p C J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hJC)).codRestrict (barX p C J)
    (fun x => ⟨⟨x, hJC x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

theorem toImg_apply (p : ℕ) {C J : Subgroup G} (hJC : J ≤ C) (x : ↥J) :
    ((toImg p hJC x : ↥(barX p C J)) : ↥C ⧸ GLAPPrimeCore p ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hJC x.2⟩ := rfl

theorem toImg_surjective (p : ℕ) {C J : Subgroup G} (hJC : J ≤ C) :
    Function.Surjective (toImg p hJC) := by
  rintro ⟨_, ⟨⟨l, hlC⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

theorem ker_toImg_le {p : ℕ} (hp : p.Prime) {C J : Subgroup G} (hJC : J ≤ C) :
    (toImg p hJC).ker ≤ GLAPPrimeCore p ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (toImg p hJC).ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx1 : toImg p hJC (x : ↥J) = 1 := x.2
    have hmem : (⟨((x : ↥J) : G), hJC (x : ↥J).2⟩ : ↥C) ∈ GLAPPrimeCore p ↥C := by
      have h1 := congrArg Subtype.val hx1
      rw [toImg_apply] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hord : orderOf (⟨⟨((x : ↥J) : G), hJC (x : ↥J).2⟩, hmem⟩ : ↥(GLAPPrimeCore p ↥C)) = p := by
      have hx' : orderOf (((x : ↥J) : G)) = p := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hx
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact hx'
    have hdiv := orderOf_dvd_natCard (⟨⟨((x : ↥J) : G), hJC (x : ↥J).2⟩, hmem⟩ :
      ↥(GLAPPrimeCore p ↥C))
    rw [hord] at hdiv
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card hdiv
  exact CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcop

theorem not_dvd_card_ker_toImg {p : ℕ} (hp : p.Prime) {C J : Subgroup G} (hJC : J ≤ C) :
    ¬ p ∣ Nat.card (toImg p hJC).ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have h1 := Subgroup.card_dvd_of_le (ker_toImg_le hp hJC)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card (h.trans h1)

@[expose] noncomputable def sigmaHom {p : ℕ} (hp : p.Prime) {C J : Subgroup G} (hJC : J ≤ C) :
    ↥(barX p C J) →* barOf p J :=
  (QuotientGroup.lift (toImg p hJC).ker (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
      (by rw [QuotientGroup.ker_mk']; exact ker_toImg_le hp hJC)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (toImg p hJC)
      (toImg_surjective p hJC)).symm.toMonoidHom

theorem sigmaHom_toImg {p : ℕ} (hp : p.Prime) {C J : Subgroup G} (hJC : J ≤ C) (x : ↥J) :
    sigmaHom hp hJC (toImg p hJC x) = QuotientGroup.mk x := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (toImg p hJC)
      (toImg_surjective p hJC)).symm (toImg p hJC x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  unfold sigmaHom
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk,
    QuotientGroup.mk'_apply]

theorem map_toImg_subtype (p : ℕ) {C Y T : Subgroup G} (hYC : Y ≤ C) (hTY : T ≤ Y) :
    ((T.subgroupOf Y).map (toImg p hYC)).map (barX p C Y).subtype = barX p C T := by
  ext z
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨⟨t, hYC t.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ht), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hcT : (c : G) ∈ T := Subgroup.mem_subgroupOf.1 hc
    exact ⟨toImg p hYC ⟨c, hTY hcT⟩, ⟨⟨c, hTY hcT⟩, Subgroup.mem_subgroupOf.2 hcT, rfl⟩, rfl⟩

theorem eq_of_barX_eq {p : ℕ} (hp : p.Prime) {C Y J J' : Subgroup G} (hYC : Y ≤ C)
    (hJ : GLAPComponent p Y J) (hJ' : GLAPComponent p Y J') (h : barX p C J = barX p C J') :
    J = J' := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJY, hL⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ
  obtain ⟨hJ'Y, hL'⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ'
  have hbij :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (toImg p hYC) (toImg_surjective p hYC) (not_dvd_card_ker_toImg hp hYC)
  have heq : (J.subgroupOf Y).map (toImg p hYC) = (J'.subgroupOf Y).map (toImg p hYC) := by
    apply Subgroup.map_injective (barX p C Y).subtype_injective
    rw [map_toImg_subtype p hYC hJY, map_toImg_subtype p hYC hJ'Y, h]
  have h2 : J.subgroupOf Y = J'.subgroupOf Y := hbij.1.injOn hL hL' heq
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hJY, inf_eq_left.2 hJ'Y] at h2
  exact h2

end Img

section Final

variable {G : Type} [Group G] [Finite G]

theorem final {p : ℕ} (hp : p.Prime) {C K B J : Subgroup G} {b : G} (hK : GLAPComponent p C K)
    (hBC : B ≤ C) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hbB : b ∈ B)
    (hJ : GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (θ : barOf p K →* ↥C ⧸ GLAPPrimeCore p ↥C) (hθr : θ.range = barX p C J)
    (hθe : ∀ x (hx : x ∈ B) (hxK : x ∈ Subgroup.normalizer (K : Set G)) (k : barOf p K),
      θ (barAut p K ⟨x, hxK⟩ k) = QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ * θ k *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩)⁻¹) :
    ∃ π : barOf p K →* barOf p J, Function.Surjective π ∧
      π.ker ≤ Subgroup.center (barOf p K) ∧
      ∀ x ∈ B, ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        ∃ hxJ : x ∈ Subgroup.normalizer (J : Set G),
          ∀ k : barOf p K, π (barAut p K ⟨x, hxK⟩ k) = barAut p J ⟨x, hxJ⟩ (π k) := by
  have hJC : J ≤ C := hJ.1.trans inf_le_left
  have hθmem : ∀ k, θ k ∈ barX p C J := fun k => by rw [← hθr]; exact ⟨k, rfl⟩
  let θ' : barOf p K →* ↥(barX p C J) := θ.codRestrict (barX p C J) hθmem
  have hθ'v : ∀ k, ((θ' k : ↥(barX p C J)) : ↥C ⧸ GLAPPrimeCore p ↥C) = θ k := fun k => rfl
  let π : barOf p K →* barOf p J := (sigmaHom hp hJC).comp θ'
  have hπ : ∀ k, π k = sigmaHom hp hJC (θ' k) := fun k => rfl
  have hsurj : Function.Surjective π := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : ((toImg p hJC j : ↥(barX p C J)) : ↥C ⧸ GLAPPrimeCore p ↥C) ∈ θ.range := by
      rw [hθr]
      exact (toImg p hJC j).2
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    have h1 : θ' k = toImg p hJC j := Subtype.ext hk
    rw [hπ, h1, sigmaHom_toImg]
  refine ⟨π, hsurj, ?_, ?_⟩
  · have hqK : CFSG.Open.IsQuasisimple (barOf p K) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
    have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
    haveI : Nontrivial (barOf p J ⧸ Subgroup.center (barOf p J)) := hqJ.2.toNontrivial
    haveI : Nontrivial (barOf p J) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (barOf p J))).nontrivial
    have hne : π.ker ≠ ⊤ := by
      intro htop
      obtain ⟨q, hq⟩ := exists_ne (1 : barOf p J)
      obtain ⟨k, rfl⟩ := hsurj q
      exact hq (MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top k))
    exact l119_normal_le_center hqK hne
  · intro x hx hxK
    have hxC : x ∈ C := hBC hx
    have hxb : x * b = b * x := hBab x hx b hbB
    have hxJ1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ ∈
        Subgroup.normalizer ((barX p C J : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
          Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
      rw [← hθr, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨barAut p K ⟨x, hxK⟩ k, hθe x hx hxK k⟩
      · rintro ⟨k, hk⟩
        refine ⟨(barAut p K ⟨x, hxK⟩).symm k, ?_⟩
        have h1 := hθe x hx hxK ((barAut p K ⟨x, hxK⟩).symm k)
        rw [MulEquiv.apply_symm_apply, hk] at h1
        exact (mul_left_cancel (mul_right_cancel h1)).symm
    have hxY : x ∈ C ⊓ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_inf.2 ⟨hxC, Subgroup.mem_centralizer_singleton_iff.2 hxb⟩
    have hYx : GLBConj x (C ⊓ Subgroup.centralizer ({b} : Set G)) =
        C ⊓ Subgroup.centralizer ({b} : Set G) :=
      gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hxY)
    have hJx : GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) (GLBConj x J) := by
      have h := glaPComponent_gLBConj hJ x
      rwa [hYx] at h
    have hbar : barX p C (GLBConj x J) = barX p C J := by
      rw [barX_gLBConj_eq p hxC J]
      exact gLBConj_eq_of_mem_normalizer hxJ1
    have hxJ : x ∈ Subgroup.normalizer (J : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 (eq_of_barX_eq hp inf_le_left hJx hJ hbar)
    refine ⟨hxJ, fun k => ?_⟩
    obtain ⟨j, hj⟩ := toImg_surjective p hJC (θ' k)
    have hxjx : x * (j : G) * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hxJ j).1 j.2
    have hθk : θ k = QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hJC j.2⟩ := by
      rw [← hθ'v, ← hj, toImg_apply]
    have h1 : θ' (barAut p K ⟨x, hxK⟩ k) = toImg p hJC ⟨x * j * x⁻¹, hxjx⟩ := by
      apply Subtype.ext
      rw [hθ'v, hθe x hx hxK k, toImg_apply, hθk, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hπ, hπ, h1, ← hj, sigmaHom_toImg, sigmaHom_toImg,
      CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    rfl

@[expose] noncomputable def conjBar {p : ℕ} (hp : p.Prime) {C K : Subgroup G}
    (hK : GLAPComponent p C K) (g : ↥C ⧸ GLAPPrimeCore p ↥C) :
    barOf p K →* ↥(GLBConj g (barX p C K)) :=
  (conjEquiv g (barX p C K)).toMonoidHom.comp (quotEquivBarX hp hK.1 hK.2.1).toMonoidHom

theorem conjBar_apply {p : ℕ} (hp : p.Prime) {C K : Subgroup G} (hK : GLAPComponent p C K)
    (g : ↥C ⧸ GLAPPrimeCore p ↥C) (k : barOf p K) :
    ((conjBar hp hK g k : ↥(GLBConj g (barX p C K))) : ↥C ⧸ GLAPPrimeCore p ↥C) =
      g⁻¹ * ((quotEquivBarX hp hK.1 hK.2.1 k : ↥(barX p C K)) : ↥C ⧸ GLAPPrimeCore p ↥C) * g :=
  rfl

theorem conjBar_surjective {p : ℕ} (hp : p.Prime) {C K : Subgroup G} (hK : GLAPComponent p C K)
    (g : ↥C ⧸ GLAPPrimeCore p ↥C) : Function.Surjective (conjBar hp hK g) := by
  intro w
  obtain ⟨u, rfl⟩ := (conjEquiv g (barX p C K)).surjective w
  obtain ⟨k, rfl⟩ := (quotEquivBarX hp hK.1 hK.2.1).surjective u
  exact ⟨k, rfl⟩

theorem conjBar_barAut {p : ℕ} (hp : p.Prime) {C K : Subgroup G} (hK : GLAPComponent p C K)
    (g : ↥C ⧸ GLAPPrimeCore p ↥C) {x : G} (hxC : x ∈ C)
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxg : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ * g =
      g * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩) (k : barOf p K) :
    ((conjBar hp hK g (barAut p K ⟨x, hxK⟩ k) : ↥(GLBConj g (barX p C K))) :
        ↥C ⧸ GLAPPrimeCore p ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ *
        ((conjBar hp hK g k : ↥(GLBConj g (barX p C K))) : ↥C ⧸ GLAPPrimeCore p ↥C) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩)⁻¹ := by
  rw [conjBar_apply, conjBar_apply, Lemma129b.quotEquivBarX_barAut hp hK hxC hxK k]
  generalize QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ = xb at hxg ⊢
  generalize ((quotEquivBarX hp hK.1 hK.2.1 k : ↥(barX p C K)) : ↥C ⧸ GLAPPrimeCore p ↥C) = u
  have hc : Commute xb g := hxg
  calc g⁻¹ * (xb * u * xb⁻¹) * g = (g⁻¹ * xb) * u * (xb⁻¹ * g) := by group
    _ = (xb * g⁻¹) * u * (g * xb⁻¹) := by rw [← hc.inv_right.eq, hc.inv_left.eq]
    _ = xb * (g⁻¹ * u * g) * xb⁻¹ := by group

end Final

section Main

theorem input18_3_eqv_main (G : Type) [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (C K B : Subgroup G) (hK : GLAPComponent p C K) (hBel : IsElemAbelian p B) (hBC : B ≤ C)
    (b : G) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbC : b ∈ C)
    (hcase : b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p C K,
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩)
    (J : Subgroup G) (hJ : GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (hJL : barX p C J ≤ barX p C (⨆ y ∈ B, GLBConj y K)) :
    ∃ π : barOf p K →* barOf p J, Function.Surjective π ∧
      π.ker ≤ Subgroup.center (barOf p K) ∧
      ∀ x ∈ B, ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        ∃ hxJ : x ∈ Subgroup.normalizer (J : Set G),
          ∀ k : barOf p K, π (barAut p K ⟨x, hxK⟩ k) = barAut p J ⟨x, hxJ⟩ (π k) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbp : b ^ p = 1 := hBel.2 b hbB
  have hcommB : ∀ x (hx : x ∈ B) (z : ↥C), (z : G) ∈ B →
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥C) z =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) z *
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ := by
    intro x hx z hz
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab x hx z hz)
  have hbb1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ≠ 1 := by
    intro h
    apply hb1
    have hpow : (⟨b, hbC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simpa using hbp)
    have h2 := l119_eq_one_of_pow_of_mem_core hp hpow ((QuotientGroup.eq_one_iff _).1 h)
    exact congrArg Subtype.val h2
  have hbbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) = p :=
    orderOf_eq_prime (Lemma129b.mk_pow_eq_one hbC hbp) hbb1
  have hcomp : ∀ X ∈ Prop126b.Fam p C K (B.subgroupOf C), IsComponentOf X ⊤ :=
    Prop126b.Fam_comp hK (B.subgroupOf C)
  have hbN : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ∈
      Subgroup.normalizer ((sSup (Prop126b.Fam p C K (B.subgroupOf C)) :
        Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    Prop126b.Fam_bar_normalizes (B.subgroupOf C) (Subgroup.mem_subgroupOf.2 hbB)
  have hconjC : ∀ y ∈ B, GLBConj y K ≤ C := fun y hy => by
    have h := gLBConj_mono y hK.1
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBC hy))] at h
  have hLbar : barX p C (⨆ y ∈ B, GLBConj y K) ≤ sSup (Prop126b.Fam p C K (B.subgroupOf C)) := by
    have hSC : (⨆ y ∈ B, GLBConj y K) ≤ C := iSup₂_le hconjC
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hSC]
    refine iSup₂_le fun y hy => ?_
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (hconjC y hy),
      barX_gLBConj_eq p (hBC hy) K]
    exact le_sSup ⟨⟨y, hBC hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hJ0 : GLAPComponent p (⊤ ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (barX p C J) := by
    have h := Prop126b.glaPComponent_barX_inf_centralizer hp hbC (le_refl C)
      (Subgroup.le_normalizer hbC) (l119_isPGroup_zpowers hbp) hJ
    rwa [barX_self] at h
  have hJ₁ : GLAPComponent p (sSup (Prop126b.Fam p C K (B.subgroupOf C)) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (barX p C J) :=
    glaPComponent_of_le hp hJ0 (le_inf (hJL.trans hLbar) (hJ0.1.trans inf_le_right))
      (inf_le_inf_right _ le_top)
  rcases hcase with hN | hC
  ·
    have hnot : ∀ X ∈ Prop126b.Fam p C K (B.subgroupOf C),
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ∉
          Subgroup.normalizer (X : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
      rintro X ⟨z, hz, rfl⟩ hX
      apply hN
      have h1 := (l119_normalizer_gLBConj_iff
        (hcommB b hbB z (Subgroup.mem_subgroupOf.1 hz)) (barX p C K)).1 hX
      exact Lemma129b.mem_normalizer_of_mk hp hK hbC h1
    obtain ⟨X, ⟨z, hz, rfl⟩, hc, hJX⟩ := eq_diag_of_moves hp hbbord hbN hcomp hnot hJ₁
    have hzB : (z : G) ∈ B := Subgroup.mem_subgroupOf.1 hz
    refine final hp hK hBC hBab hbB hJ
      ((diagSub _ p _ hc).comp (conjBar hp hK (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z))) ?_ ?_
    · rw [hJX]
      ext w
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨conjBar hp hK _ k, rfl⟩
      · rintro ⟨u, rfl⟩
        obtain ⟨k, rfl⟩ := conjBar_surjective hp hK _ u
        exact ⟨k, rfl⟩
    · intro x hx hxK k
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, diagSub_apply, diagSub_apply,
        conjBar_barAut hp hK _ (hBC hx) hxK (hcommB x hx z hzB) k, Input183.conj_oprod]
      refine Input183.oprod_congr fun j _ => ?_
      have hxb : Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩)
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) := hcommB x hx ⟨b, hbC⟩ hbB
      have hj : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) ^ j *
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ =
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ *
            (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) ^ j := (hxb.pow_right j).eq.symm
      generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) ^ j = c at hj ⊢
      generalize QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hBC hx⟩ = xb at hj ⊢
      generalize ((conjBar hp hK (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) k :
        ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K))) :
          ↥C ⧸ GLAPPrimeCore p ↥C) = u
      calc c * (xb * u * xb⁻¹) * c⁻¹ = (c * xb) * u * (c * xb)⁻¹ := by group
        _ = (xb * c) * u * (xb * c)⁻¹ := by rw [hj]
        _ = xb * (c * u * c⁻¹) * xb⁻¹ := by group
  ·
    have hbcen : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ∈
        Subgroup.centralizer ((sSup (Prop126b.Fam p C K (B.subgroupOf C)) :
          Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
      have hle : sSup (Prop126b.Fam p C K (B.subgroupOf C)) ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨z, hz, rfl⟩ := hX
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (l119_centralizes_gLBConj (hcommB b hbB z (Subgroup.mem_subgroupOf.1 hz)) hC w hw).symm
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
    obtain ⟨X, ⟨z, hz, rfl⟩, hJX⟩ := eq_comp_of_centralizes hp hbbord hbN hcomp hbcen hJ₁
    have hzB : (z : G) ∈ B := Subgroup.mem_subgroupOf.1 hz
    refine final hp hK hBC hBab hbB hJ
      ((GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)).subtype.comp
        (conjBar hp hK _)) ?_ ?_
    · rw [hJX]
      ext w
      constructor
      · rintro ⟨k, rfl⟩
        exact (conjBar hp hK _ k).2
      · intro hw
        obtain ⟨k, hk⟩ := conjBar_surjective hp hK _ ⟨w, hw⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    · intro x hx hxK k
      exact conjBar_barAut hp hK _ (hBC hx) hxK (hcommB x hx z hzB) k

theorem input18_3_eqv_holds : Inputs123b.Input18_3_eqv := by
  intro G _ _ p hp _ C K B hK hBel hBC b hbB hb1 hbC hcase J hJ hJL
  exact input18_3_eqv_main G p hp C K B hK hBel hBC b hbB hb1 hbC hcase J hJ hJL

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs183eqv

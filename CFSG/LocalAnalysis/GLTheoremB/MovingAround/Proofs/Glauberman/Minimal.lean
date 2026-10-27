module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Fusion
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Wielandt
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.ChiefHom
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.KSeries
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Reduction

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Bg (kLowInfty Kfam gen)
open CFSG.GH74.GLS.Stage2.Signalizer.L53 (IsChiefPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem kLowInfty_normal {P : Subgroup G} (hPn : P.Normal) : (kLowInfty P).Normal := by
  have := CFSG.GH74.GLS.Stage2.Signalizer.L53.normalizer_le_kLowInfty P
  rw [normalizer_eq_top_iff.mpr hPn] at this
  exact normalizer_eq_top_iff.mp (top_le_iff.mp this)

theorem comap_ne_top {H : Type*} [Group H] {f : G →* H} (hf : Function.Surjective f)
    {L : Subgroup H} (hL : L ≠ ⊤) : L.comap f ≠ ⊤ := by
  intro h
  apply hL
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have : x ∈ L.comap f := by rw [h]; exact mem_top x
  exact this

theorem le_of_normal_pSubgroup (hp5 : 5 ≤ p) (S : Sylow p G) (P : Subgroup G) [hPn : P.Normal]
    (hPp : IsPGroup p P) (hPmax : ∀ N : Subgroup G, N.Normal → IsPGroup p N → N ≤ P)
    (hind : ∀ H T : Subgroup G, H ≠ ⊤ → IsSylowOf p H T → T ⊓ ⁅H, H⁆ ≤ ⁅H ⊓ nK T, H ⊓ nK T⁆)
    (hquot : ControlsTransfer p (G ⧸ P)) :
    (S : Subgroup G) ⊓ commutator G ≤ ⁅nK (S : Subgroup G), nK (S : Subgroup G)⁆ := by
  classical
  by_contra hI
  set N := nK (S : Subgroup G) with hNdef
  set D := ⁅N, N⁆ with hDdef
  have hPS : P ≤ S := hPp.le_sylow_of_normal S
  have hSN : (S : Subgroup G) ≤ N := le_nK (S : Subgroup G)
  have hDG : D ≤ commutator G := Subgroup.commutator_mono le_top le_top
  have hNtop : N ≠ ⊤ := by
    intro h
    apply hI
    rw [hDdef, h, ← _root_.commutator_def]
    exact inf_le_right
  set Q := D ⊓ P with hQdef
  have hQD : Q ≤ D := inf_le_left
  have hQP : Q ≤ P := inf_le_right
  set M := normalizer (Q : Set G) with hMdef
  have hIII : ∀ L : Subgroup G, (S : Subgroup G) ≤ L → L ≠ ⊤ → L ≤ M := by
    intro L hSL hL
    have h1 := hind L S hL (IsSylowOf.of_sylow S hSL)
    have h2 : (S : Subgroup G) ⊓ ⁅L, L⁆ ≤ D :=
      h1.trans (Subgroup.commutator_mono inf_le_right inf_le_right)
    have key : ∀ l ∈ L, ∀ x ∈ Q, l * x * l⁻¹ ∈ Q := by
      intro l hl x hx
      have hxP : x ∈ P := hQP hx
      have hcP : ⁅l, x⁆ ∈ P := by
        have e : ⁅l, x⁆ = (l * x * l⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact P.mul_mem (hPn.conj_mem x hxP l) (P.inv_mem hxP)
      have hc : ⁅l, x⁆ ∈ Q :=
        Subgroup.mem_inf.mpr ⟨h2 (Subgroup.mem_inf.mpr ⟨hPS hcP,
          Subgroup.commutator_mem_commutator hl (hSL (hPS hxP))⟩), hcP⟩
      have e : l * x * l⁻¹ = ⁅l, x⁆ * x := by simp only [commutatorElement_def]; group
      rw [e]
      exact Q.mul_mem hc hx
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact key l hl h
    · intro hh
      have := key l⁻¹ (L.inv_mem hl) _ hh
      have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
      rwa [e] at this
  have hNM : N ≤ M := hIII N hSN hNtop
  have hDM : D ≤ ⁅M, M⁆ := Subgroup.commutator_mono hNM hNM
  have hMtop : M ≠ ⊤ := by
    intro hM
    have hQn : Q.Normal := normalizer_eq_top_iff.mp hM
    let C : Subgroup G :=
      { carrier := {m | ∀ x ∈ P, ⁅m, x⁆ ∈ Q}
        mul_mem' := by
          intro a b ha hb x hx
          have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact Q.mul_mem (hQn.conj_mem _ (hb x hx) a) (ha x hx)
        one_mem' := by intro x _; simp
        inv_mem' := by
          intro a ha x hx
          have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by simp only [commutatorElement_def]; group
          rw [e]
          have := hQn.conj_mem _ (Q.inv_mem (ha x hx)) a⁻¹
          simpa using this }
    haveI hCn : C.Normal := by
      refine ⟨fun c hc m x hx => ?_⟩
      have e : ⁅m * c * m⁻¹, x⁆ = m * ⁅c, m⁻¹ * x * m⁆ * m⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine hQn.conj_mem _ (hc _ ?_) m
      have := hPn.conj_mem x hx m⁻¹
      simpa using this
    have hNSC : normalizer ((S : Subgroup G) : Set G) ≤ C := by
      intro m hm x hx
      have hmN : m ∈ N := CFSG.GH74.GLS.Stage2.Signalizer.L53.normalizer_le_kLowInfty _ hm
      have hcP : ⁅m, x⁆ ∈ P := by
        have e : ⁅m, x⁆ = (m * x * m⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact P.mul_mem (hPn.conj_mem x hx m) (P.inv_mem hx)
      exact Subgroup.mem_inf.mpr ⟨Subgroup.commutator_mem_commutator hmN (hSN (hPS hx)), hcP⟩
    have hSC : (S : Subgroup G) ≤ C := le_normalizer.trans hNSC
    have hCtop : C = ⊤ := by
      have := Sylow.normalizer_sup_eq_top' (N := C) S hSC
      rw [eq_top_iff, ← this]
      exact sup_le hNSC le_rfl
    have hIVb : commutator G ⊓ P ≤ Q := by
      have hT : commutator G ⊓ P ≤ D ⊓ (S : Subgroup G) := by
        refine commutator_inf_le_of_conj S inf_le_right ?_ hPS ?_
        · refine le_inf (Subgroup.commutator_mono hSN hSN) (Subgroup.commutator_le.mpr ?_)
          intro a ha b hb
          rw [commutatorElement_def]
          exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ha hb)
            ((S : Subgroup G).inv_mem ha)) ((S : Subgroup G).inv_mem hb)
        · intro x hx m
          have hmx : m⁻¹ * x * m ∈ P := by
            have := hPn.conj_mem x hx m⁻¹
            simpa using this
          refine ⟨hmx, ?_⟩
          have hmC : m⁻¹ ∈ C := by rw [hCtop]; exact mem_top _
          have h1 := hmC x⁻¹ (P.inv_mem hx)
          have e : x⁻¹ * (m⁻¹ * x * m) = ⁅m⁻¹, x⁻¹⁆⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          have := Q.inv_mem h1
          exact Subgroup.mem_inf.mpr ⟨hQD this, hPS (hQP this)⟩
      intro x hx
      exact Subgroup.mem_inf.mpr ⟨(hT hx).1, hx.2⟩
    have hSP : ¬ (S : Subgroup G) ≤ P := by
      intro h
      have hSPeq : (S : Subgroup G) = P := le_antisymm h hPS
      apply hNtop
      rw [hNdef, hSPeq]
      exact normalizer_eq_top_iff.mpr (kLowInfty_normal hPn)
    let π := QuotientGroup.mk' P
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective P
    let S' : Sylow p (G ⧸ P) := S.mapSurjective hπ
    have hS' : (S' : Subgroup (G ⧸ P)) = (S : Subgroup G).map π := rfl
    have hS'1 : (S' : Subgroup (G ⧸ P)) ≠ ⊥ := by
      rw [hS']
      intro h
      apply hSP
      intro s hs
      have : π s ∈ (S : Subgroup G).map π := ⟨s, hs, rfl⟩
      rw [h, mem_bot] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have hK1 : kLowInfty (S' : Subgroup (G ⧸ P)) ≠ ⊥ := kLowInfty_ne_bot S'.isPGroup' hS'1
    have hN'top : nK (S' : Subgroup (G ⧸ P)) ≠ ⊤ := by
      intro h
      have hKn : (kLowInfty (S' : Subgroup (G ⧸ P))).Normal := normalizer_eq_top_iff.mp h
      have hKp : IsPGroup p (kLowInfty (S' : Subgroup (G ⧸ P))) :=
        S'.isPGroup'.to_le (kLowInfty_le' _)
      have hcn : ((kLowInfty (S' : Subgroup (G ⧸ P))).comap π).Normal := hKn.comap π
      have hcp : IsPGroup p ((kLowInfty (S' : Subgroup (G ⧸ P))).comap π) :=
        hKp.comap_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact hPp)
      have hle := hPmax _ hcn hcp
      apply hK1
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      rw [mem_bot]
      exact (QuotientGroup.eq_one_iff _).mpr (hle hy)
    set L := (nK (S' : Subgroup (G ⧸ P))).comap π with hLdef
    have hLtop : L ≠ ⊤ := comap_ne_top hπ hN'top
    have hSL : (S : Subgroup G) ≤ L := fun s hs => le_nK (S' : Subgroup (G ⧸ P)) ⟨s, hs, rfl⟩
    have h1 : (S : Subgroup G) ⊓ ⁅L, L⁆ ≤ D :=
      (hind L S hLtop (IsSylowOf.of_sylow S hSL)).trans
        (Subgroup.commutator_mono inf_le_right inf_le_right)
    have h2 := hquot S'
    apply hI
    rintro x ⟨hxS, hxc⟩
    have hπx : π x ∈ (S' : Subgroup (G ⧸ P)) ⊓ commutator (G ⧸ P) := by
      refine Subgroup.mem_inf.mpr ⟨⟨x, hxS, rfl⟩, ?_⟩
      have : π x ∈ (commutator G).map π := ⟨x, hxc, rfl⟩
      rwa [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
        ← _root_.commutator_def] at this
    have h3 := h2 hπx
    have hmapL : L.map π = nK (S' : Subgroup (G ⧸ P)) := map_comap_eq_self_of_surjective hπ _
    rw [← hmapL, ← Subgroup.map_commutator] at h3
    obtain ⟨l, hl, hlx⟩ := h3
    have hy : l⁻¹ * x ∈ P := QuotientGroup.eq.mp hlx
    have hlS : l ∈ (S : Subgroup G) := by
      have : l = x * (l⁻¹ * x)⁻¹ := by group
      rw [this]
      exact (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem (hPS hy))
    have hlD : l ∈ D := h1 (Subgroup.mem_inf.mpr ⟨hlS, hl⟩)
    have hyc : l⁻¹ * x ∈ commutator G := (commutator G).mul_mem
      ((commutator G).inv_mem (hDG hlD)) hxc
    have hyD : l⁻¹ * x ∈ D := hQD (hIVb (Subgroup.mem_inf.mpr ⟨hyc, hy⟩))
    have : x = l * (l⁻¹ * x) := by group
    rw [this]
    exact D.mul_mem hlD hyD
  have hIVb : ⁅M, M⁆ ⊓ P ≤ Q := by
    rintro x ⟨hxM, hxP⟩
    have h1 := hind M S hMtop (IsSylowOf.of_sylow S (hSN.trans hNM))
    have h2 := h1 (Subgroup.mem_inf.mpr ⟨hPS hxP, hxM⟩)
    exact Subgroup.mem_inf.mpr ⟨Subgroup.commutator_mono inf_le_right inf_le_right h2, hxP⟩
  have hQlt : Q < commutator G ⊓ P := by
    refine lt_of_le_of_ne (le_inf (hQD.trans hDG) hQP) fun h => ?_
    apply hMtop
    rw [hMdef, h]
    exact normalizer_eq_top_iff.mpr inferInstance
  set X := Q.normalCore with hXdef
  have hXQ : X ≤ Q := normalCore_le Q
  have hXn : X.Normal := normalCore_normal Q
  obtain ⟨Y, hYmin⟩ := (Set.toFinite {Y : Subgroup G | Y.Normal ∧ X < Y ∧
    Y ≤ commutator G ⊓ P}).exists_minimal
    ⟨commutator G ⊓ P, inferInstance, lt_of_le_of_lt hXQ hQlt, le_rfl⟩
  obtain ⟨hYn, hXY, hYGP⟩ := hYmin.prop
  have hcY : IsChiefPair Y X := by
    refine ⟨hYn, hXn, hXY, fun Z hZn hXZ hZY => ?_⟩
    by_cases hZX : Z = X
    · exact Or.inl hZX
    · right
      exact le_antisymm hZY (hYmin.le_of_le ⟨hZn, lt_of_le_of_ne hXZ (Ne.symm hZX),
        hZY.trans hYGP⟩ hZY)
  have hYP : Y ≤ P := hYGP.trans inf_le_right
  have hYM : ¬ Y ≤ ⁅M, M⁆ := by
    intro h
    have hYQ : Y ≤ Q := fun y hy => hIVb (Subgroup.mem_inf.mpr ⟨h hy, hYP hy⟩)
    exact hXY.not_ge (normal_le_normalCore.mpr hYQ)
  have he : ∀ g ∈ (S : Subgroup G), g ∉ P → ∃ y ∈ Y, iterComm y g (p - 1) ∉ X := by
    intro g₀ hg₀S hg₀P
    by_contra hcon
    push Not at hcon
    let π := QuotientGroup.mk' X
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective X
    let S' : Sylow p (G ⧸ X) := S.mapSurjective hπ
    have hS' : (S' : Subgroup (G ⧸ X)) = (S : Subgroup G).map π := rfl
    have hY'n : (Y.map π).Normal := hYn.map π hπ
    have hY'S : Y.map π ≤ S' := by rw [hS']; exact map_mono (hYP.trans hPS)
    have hYY : ⁅Y, Y⁆ ≤ X := comm_self_le_of_chief hPp.isNilpotent hPn hYP hcY
    have hY'c : ∀ a ∈ Y.map π, ∀ b ∈ Y.map π, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h : π ⁅a, b⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hYY (Subgroup.commutator_mem_commutator ha hb))
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have hY'p : ∀ y ∈ Y.map π, y ^ p = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (chief_pow_mem hPn hPp hYP hcY y hy)
    let E₀ : Set (G ⧸ X) := {e | e ∈ (S' : Subgroup (G ⧸ X)) ∧
      ∀ y ∈ Y.map π, iterComm y e (p - 1) = 1}
    have hE₀S : E₀ ⊆ (S' : Subgroup (G ⧸ X)) := fun e he => he.1
    have hwc : ∀ g : G ⧸ X, (∀ e ∈ E₀, g⁻¹ * e * g ∈ (S' : Subgroup (G ⧸ X))) →
        ∀ e ∈ E₀, g⁻¹ * e * g ∈ E₀ := by
      intro g hg e he
      refine ⟨hg e he, fun y hy => ?_⟩
      have hgy : g * y * g⁻¹ ∈ Y.map π := hY'n.conj_mem y hy g
      have := conj_iterComm g⁻¹ (g * y * g⁻¹) e (p - 1)
      rw [he.2 _ hgy] at this
      have e1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [e1, inv_inv] at this
      rw [← this]
      group
    have hnil : ∀ e ∈ E₀, ∀ y ∈ Y.map π, iterComm y e (p - 1) = 1 := fun e he => he.2
    obtain ⟨hSL, hYL⟩ := wielandt S' hY'n hY'S hY'c hY'p E₀ hE₀S hwc hnil
    set L' := normalizer ((closure E₀ : Subgroup (G ⧸ X)) : Set (G ⧸ X)) with hL'def
    have hg₀E : π g₀ ∈ E₀ := by
      refine ⟨⟨g₀, hg₀S, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_iterComm]
      exact (QuotientGroup.eq_one_iff _).mpr (hcon y hy)
    have hL'top : L' ≠ ⊤ := by
      intro h
      have hEn : (closure E₀).Normal := normalizer_eq_top_iff.mp h
      have hEp : IsPGroup p (closure E₀) := S'.isPGroup'.to_le ((closure_le _).mpr hE₀S)
      have hcn : ((closure E₀).comap π).Normal := hEn.comap π
      have hcp : IsPGroup p ((closure E₀).comap π) :=
        hEp.comap_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact hPp.to_le (hXQ.trans hQP))
      exact hg₀P (hPmax _ hcn hcp (show π g₀ ∈ closure E₀ from subset_closure hg₀E))
    set H := L'.comap π with hHdef
    have hHtop : H ≠ ⊤ := comap_ne_top hπ hL'top
    have hSH : (S : Subgroup G) ≤ H := fun s hs => hSL ⟨s, hs, rfl⟩
    have hHM : H ≤ M := hIII H hSH hHtop
    have hY'c' : Y.map π ≤ commutator (G ⧸ X) := by
      rintro _ ⟨y, hy, rfl⟩
      have : π y ∈ (commutator G).map π := ⟨y, (hYGP hy).1, rfl⟩
      rwa [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
        ← _root_.commutator_def] at this
    apply hYM
    intro y hy
    have h1 : π y ∈ ⁅L', L'⁆ := hYL (Subgroup.mem_inf.mpr ⟨⟨y, hy, rfl⟩, hY'c' ⟨y, hy, rfl⟩⟩)
    rw [← map_comap_eq_self_of_surjective hπ L', ← Subgroup.map_commutator] at h1
    obtain ⟨h, hh, hhy⟩ := h1
    have hx : h⁻¹ * y ∈ X := QuotientGroup.eq.mp hhy
    have : y = h * (h⁻¹ * y) := by group
    rw [this]
    exact ⁅M, M⁆.mul_mem (Subgroup.commutator_mono hHM hHM hh) (hDM (hQD (hXQ hx)))
  obtain ⟨A, hAn, hAP, hPA, hCA⟩ := exists_critical hPn hPp
  have hA2 : ⁅⁅A, A⁆, A⁆ = ⊥ := comm_comm_eq_bot_of_critical hAP hPA
  have hZn : (A ⊓ centralizer (A : Set G)).Normal := by
    have : (centralizer (A : Set G)).Normal := Subgroup.normal_centralizer
    infer_instance
  have hbad : ¬ ∀ m, 1 ≤ m → gen (Kfam (S : Subgroup G) m) ≤ P := fun h =>
    hNtop (normalizer_eq_top_iff.mpr
      (CFSG.GH74.GLS.Stage2.Signalizer.L53.normal_of_le hPn hPS h).2)
  obtain ⟨g, hgS, hgP, ha, hb⟩ := exists_element_ab hPS hAn hAP hA2 hPA hbad
  have hT3 := chief_iterComm_le hPn hPp hAn hAP hPA hCA g (i := 3) (j := 2) (by norm_num)
    (by norm_num) (hypQ_of_ab hZn ha hb) (hypZ_of_ab hb)
  obtain ⟨y, hyY, hyX⟩ := he g hgS hgP
  exact hyX (iterComm_mem_of_le hXn (hT3 Y X hcY hYP y hyY) (by omega))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end

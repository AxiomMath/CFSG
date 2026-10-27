module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltComponents
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltOddCore

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

section Prod

variable {S : Type*} [Group S] [IsSimpleGroup S]

theorem fst_eq_one_of_normal (hZ : Subgroup.center S = ⊥) {Nn : Subgroup (S × S)} [Nn.Normal]
    {a : S} (ha : (a, 1) ∉ Nn) {x : S × S} (hx : x ∈ Nn) : x.1 = 1 := by
  set N₁ : Subgroup S := Nn.comap (MonoidHom.inl S S) with hN₁
  have : N₁.Normal := Subgroup.Normal.comap inferInstance _
  have hbot : N₁ = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁).resolve_right fun htop =>
      ha (htop ▸ Subgroup.mem_top a : a ∈ N₁)
  have hcent : x.1 ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : ((g, 1) : S × S) * x * (g, 1)⁻¹ * x⁻¹ ∈ Nn :=
      Nn.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx _) (Nn.inv_mem hx)
    have h3 : ((g, 1) : S × S) * x * (g, 1)⁻¹ * x⁻¹ = (g * x.1 * g⁻¹ * x.1⁻¹, 1) := by
      ext <;> simp
    have h2 : g * x.1 * g⁻¹ * x.1⁻¹ ∈ N₁ := by
      rw [hN₁, Subgroup.mem_comap]
      rw [h3] at h1
      exact h1
    rw [hbot, Subgroup.mem_bot] at h2
    calc g * x.1 = (g * x.1 * g⁻¹ * x.1⁻¹) * (x.1 * g) := by group
      _ = x.1 * g := by rw [h2, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcent
  exact hcent

theorem snd_eq_one_of_normal (hZ : Subgroup.center S = ⊥) {Nn : Subgroup (S × S)} [Nn.Normal]
    {b : S} (hb : (1, b) ∉ Nn) {x : S × S} (hx : x ∈ Nn) : x.2 = 1 := by
  set N₂ : Subgroup S := Nn.comap (MonoidHom.inr S S) with hN₂
  have : N₂.Normal := Subgroup.Normal.comap inferInstance _
  have hbot : N₂ = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N₂).resolve_right fun htop =>
      hb (htop ▸ Subgroup.mem_top b : b ∈ N₂)
  have hcent : x.2 ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : ((1, g) : S × S) * x * (1, g)⁻¹ * x⁻¹ ∈ Nn :=
      Nn.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx _) (Nn.inv_mem hx)
    have h3 : ((1, g) : S × S) * x * (1, g)⁻¹ * x⁻¹ = (1, g * x.2 * g⁻¹ * x.2⁻¹) := by
      ext <;> simp
    have h2 : g * x.2 * g⁻¹ * x.2⁻¹ ∈ N₂ := by
      rw [hN₂, Subgroup.mem_comap]
      rw [h3] at h1
      exact h1
    rw [hbot, Subgroup.mem_bot] at h2
    calc g * x.2 = (g * x.2 * g⁻¹ * x.2⁻¹) * (x.2 * g) := by group
      _ = x.2 * g := by rw [h2, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcent
  exact hcent

theorem forall_snd_mem_of_normal {Nn : Subgroup (S × S)} [Nn.Normal]
    (h1 : ∀ x ∈ Nn, x.1 = 1) {x : S × S} (hx : x ∈ Nn) (hx2 : x.2 ≠ 1) :
    ∀ b : S, (1, b) ∈ Nn := by
  set N₂ : Subgroup S := Nn.comap (MonoidHom.inr S S) with hN₂
  have : N₂.Normal := Subgroup.Normal.comap inferInstance _
  have hx2mem : x.2 ∈ N₂ := by
    rw [hN₂, Subgroup.mem_comap]
    have : x = (1, x.2) := Prod.ext (h1 x hx) rfl
    show ((1, x.2) : S × S) ∈ Nn
    rw [← this]
    exact hx
  have htop : N₂ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N₂).resolve_left fun hbot =>
      hx2 (by simpa [hbot] using hx2mem)
  intro b
  have : b ∈ N₂ := htop ▸ Subgroup.mem_top b
  exact this

theorem forall_fst_mem_of_normal {Nn : Subgroup (S × S)} [Nn.Normal]
    (h2 : ∀ x ∈ Nn, x.2 = 1) {x : S × S} (hx : x ∈ Nn) (hx1 : x.1 ≠ 1) :
    ∀ a : S, (a, 1) ∈ Nn := by
  set N₁ : Subgroup S := Nn.comap (MonoidHom.inl S S) with hN₁
  have : N₁.Normal := Subgroup.Normal.comap inferInstance _
  have hx1mem : x.1 ∈ N₁ := by
    rw [hN₁, Subgroup.mem_comap]
    have : x = (x.1, 1) := Prod.ext rfl (h2 x hx)
    show ((x.1, 1) : S × S) ∈ Nn
    rw [← this]
    exact hx
  have htop : N₁ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁).resolve_left fun hbot =>
      hx1 (by simpa [hbot] using hx1mem)
  intro a
  have : a ∈ N₁ := htop ▸ Subgroup.mem_top a
  exact this

end Prod

theorem mem_of_psi_eq {W Q : Type*} [Group W] [Group Q] {p : ℕ} (ψ : W →* Q) (C : Subgroup W)
    [C.Normal] (hker : ∀ n : W, ψ n = 1 → (orderOf n).Coprime p) {x w : W} (hxp : x ^ p = 1)
    (hw : w ∈ C) (hψ : ψ x = ψ w) : x ∈ C := by
  set q := QuotientGroup.mk' C with hq
  have hn : ψ (w⁻¹ * x) = 1 := by rw [map_mul, map_inv, hψ, inv_mul_cancel]
  have hqw : q w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
  have hqx : q x = q (w⁻¹ * x) := by
    rw [map_mul, map_inv, hqw, inv_one, one_mul]
  have h1 : orderOf (q x) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
  have h2 : orderOf (q x) ∣ orderOf (w⁻¹ * x) := by
    rw [hqx]
    exact orderOf_map_dvd q _
  have h3 : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes (hker _ hn) h2 h1
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

section Bar

variable {G : Type} [Group G]

@[expose] def barElt (M : Subgroup G) {W : Subgroup G} (hWM : W ≤ M) :
    ↥W →* ↥M ⧸ CFSG.pCore 2 ↥M :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hWM)

@[expose] def centralizerBar (M : Subgroup G) {W : Subgroup G} (hWM : W ≤ M)
    (Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup W :=
  (Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap (barElt M hWM)

theorem mem_centralizerBar_iff {M W : Subgroup G} (hWM : W ≤ M)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {w : W} :
    w ∈ centralizerBar M hWM Lb ↔
      barElt M hWM w ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Iff.rfl

theorem barElt_mem_barM {M W : Subgroup G} (hWM : W ≤ M) (w : W) : barElt M hWM w ∈ barM M W :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr w.2)

theorem normal_centralizerBar {M W : Subgroup G} (hWM : W ≤ M)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hLb : barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (centralizerBar M hWM Lb).Normal := by
  have hNC : Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  refine ⟨fun n hn w => ?_⟩
  rw [mem_centralizerBar_iff] at hn ⊢
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hNC (hLb (barElt_mem_barM hWM w))) _).mp hn

theorem mem_centralizerBar_of_psi_mem {M W : Subgroup G} {Q : Type*} [Group Q] {p : ℕ}
    (hWM : W ≤ M) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hLb : barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) {ψ : W →* Q}
    (hker : ∀ n : W, ψ n = 1 → (orderOf n).Coprime p) {x : W} (hxp : x ^ p = 1)
    (hx : ψ x ∈ (centralizerBar M hWM Lb).map ψ) : x ∈ centralizerBar M hWM Lb := by
  have := normal_centralizerBar hWM hLb
  obtain ⟨w, hw, hwx⟩ := hx
  exact mem_of_psi_eq ψ _ hker hxp hw hwx.symm

end Bar

namespace D2AltData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem carrying_dichotomy_of (h : D2AltData p M H R X) (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) {c₀ c₁ s : G} {g : ℕ} {W : Subgroup G}
    {ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)}
    (hsc : AltScalar p (H ⊓ M) X c₀ c₁ s g) (hWK : W ≤ H ⊓ M) (hWM : W ≤ M) (hW : ⁅W, W⁆ = W)
    (hXW : X ≤ W) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker = (GLBPrimeCore p H).subgroupOf W)
    (hc₀ : ∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) (hc₁ : ∀ w : W, (w : G) = c₁ → (ψ w).1 = 1) :
    (∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
      ∀ w ∈ centralizerBar M hWM Lb, ψ w = 1) ∨
    (∃ L₀ L₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L₀ ⊤ ∧ IsComponentOf L₁ ⊤ ∧
      L₀ ≠ L₁ ∧ (∀ w ∈ centralizerBar M hWM L₀, (ψ w).1 = 1) ∧
      (∀ w ∈ centralizerBar M hWM L₁, (ψ w).2 = 1) ∧
      (∀ b, ∃ w ∈ centralizerBar M hWM L₀, ψ w = (1, b)) ∧
      (∀ a, ∃ w ∈ centralizerBar M hWM L₁, ψ w = (a, 1)) ∧
      (∀ w : W, (w : G) = c₀ → w ∉ centralizerBar M hWM L₀) ∧
      (∀ w : W, (w : G) = c₁ → w ∉ centralizerBar M hWM L₁) ∧
      (∀ w : W, (w : G) = c₁ → w ∈ centralizerBar M hWM L₀) ∧
      (∀ w : W, (w : G) = c₀ → w ∈ centralizerBar M hWM L₁)) := by
  have hp : p.Prime := Fact.out
  have hp5 := h.five_le
  have hX : IsElemAbelian p X := h.elem
  have hc₀X : c₀ ∈ X := hsc.mem_zero
  have hc₁X : c₁ ∈ X := hsc.mem_one
  have : IsSimpleGroup (alternatingGroup (Fin p)) :=
    alternatingGroup.isSimpleGroup (by simpa using hp5)
  have hZ : Subgroup.center (alternatingGroup (Fin p)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  set w₀ : W := ⟨c₀, hXW hc₀X⟩ with hw₀
  set w₁ : W := ⟨c₁, hXW hc₁X⟩ with hw₁
  have hw₀p : w₀ ^ p = 1 := Subtype.ext (hX.2 c₀ hc₀X)
  have hw₁p : w₁ ^ p = 1 := Subtype.ext (hX.2 c₁ hc₁X)
  have hc₀ne : c₀ ≠ 1 := by
    intro hc
    have hc' : c₁ = 1 := by rw [← hsc.conj_zero, hc]; group
    have hXbot : X = ⊥ := by rw [hsc.span, hc, hc']; simp
    have := h.card
    rw [hXbot, Subgroup.card_bot] at this
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hc₁ne : c₁ ≠ 1 := by
    intro hc
    refine hc₀ne ?_
    have h1 : s * c₀ * s⁻¹ = 1 := by rw [hsc.conj_zero, hc]
    simpa using h1
  have hfaith : ∀ x : W, (x : G) ∈ X → x ≠ 1 → barElt M hWM x ≠ 1 := fun x hxX hx1 hbar =>
    hx1 (Subtype.ext (h.pair.eq_one_of_mem_twoCore hX hxX
      (coe_mem_pCoreOf_two_of_mk_eq_one _ hbar)))
  have hodd := h.le_centralizer_oddCore hD1 h84 hD2
  have hbarX : ∀ w : W, (w : G) ∈ X → barElt M hWM w ∈ barM M X := fun w hwX =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwX)
  have hnotcomp : ∀ w : W, (w : G) ∈ X → w ≠ 1 → ∃ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      IsComponentOf L ⊤ ∧ w ∉ centralizerBar M hWM L := by
    intro w hwX hw1
    obtain ⟨L, hL, hnc⟩ := h.exists_not_le_centralizer h84 hD2 hodd
      (U := Subgroup.zpowers (barElt M hWM w)) (Subgroup.zpowers_le.mpr (hbarX w hwX))
      (mt Subgroup.zpowers_eq_bot.mp (hfaith w hwX hw1))
    exact ⟨L, hL, fun hw => hnc (Subgroup.zpowers_le.mpr hw)⟩
  obtain ⟨L₀, hL₀, hw₀L⟩ := hnotcomp w₀ hc₀X (fun h1 => hc₀ne (congrArg Subtype.val h1))
  obtain ⟨L₁, hL₁, hw₁L⟩ := hnotcomp w₁ hc₁X (fun h1 => hc₁ne (congrArg Subtype.val h1))
  have hker' : ∀ n : W, ψ n = 1 → (orderOf n).Coprime p := by
    intro n hn
    have hnN : (n : G) ∈ GLBPrimeCore p H := by
      have hn' : n ∈ ψ.ker := hn
      rw [hker] at hn'
      exact hn'
    have hdvd : orderOf n ∣ Nat.card (GLBPrimeCore p H) := by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hnN
    exact Nat.Coprime.coprime_dvd_left hdvd (glbPrimeCore_coprime p H).symm
  have hnormL : ∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ →
      barM M W ≤ Subgroup.normalizer (L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    h.le_normalizer_component hD1 hα hB3 hWK hW hL
  have hnorm : ∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ →
      (centralizerBar M hWM L).Normal := fun L hL => normal_centralizerBar hWM (hnormL L hL)
  have hnormψ : ∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ →
      ((centralizerBar M hWM L).map ψ).Normal := fun L hL =>
    have := hnorm L hL
    Subgroup.Normal.map inferInstance ψ hsurj
  have hpsi : ∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ → ∀ x : W, x ^ p = 1 →
      ψ x ∈ (centralizerBar M hWM L).map ψ → x ∈ centralizerBar M hWM L := fun L hL x hxp hx =>
    mem_centralizerBar_of_psi_mem hWM (hnormL L hL) hker' hxp hx
  have claim₀ : ∀ w ∈ centralizerBar M hWM L₀, (ψ w).1 = 1 := by
    intro w hw
    have := hnormψ L₀ hL₀
    refine fst_eq_one_of_normal hZ (a := (ψ w₀).1) (fun hmem => hw₀L (hpsi L₀ hL₀ w₀ hw₀p ?_))
      (Subgroup.mem_map_of_mem ψ hw)
    rwa [show ψ w₀ = ((ψ w₀).1, 1) from Prod.ext rfl (hc₀ w₀ rfl)]
  have claim₁ : ∀ w ∈ centralizerBar M hWM L₁, (ψ w).2 = 1 := by
    intro w hw
    have := hnormψ L₁ hL₁
    refine snd_eq_one_of_normal hZ (b := (ψ w₁).2) (fun hmem => hw₁L (hpsi L₁ hL₁ w₁ hw₁p ?_))
      (Subgroup.mem_map_of_mem ψ hw)
    rwa [show ψ w₁ = (1, (ψ w₁).2) from Prod.ext (hc₁ w₁ rfl) rfl]
  by_cases hS₀ : ∀ w ∈ centralizerBar M hWM L₀, ψ w = 1
  · exact Or.inl ⟨L₀, hL₀, hS₀⟩
  by_cases hS₁ : ∀ w ∈ centralizerBar M hWM L₁, ψ w = 1
  · exact Or.inl ⟨L₁, hL₁, hS₁⟩
  by_cases hLe : L₀ = L₁
  · subst hLe
    exact Or.inl ⟨L₀, hL₀, fun w hw => Prod.ext (claim₀ w hw) (claim₁ w hw)⟩
  push Not at hS₀ hS₁
  obtain ⟨u₀, hu₀, hu₀1⟩ := hS₀
  obtain ⟨u₁, hu₁, hu₁1⟩ := hS₁
  have hsnd : ∀ b, (1, b) ∈ (centralizerBar M hWM L₀).map ψ := by
    have := hnormψ L₀ hL₀
    exact forall_snd_mem_of_normal (Nn := (centralizerBar M hWM L₀).map ψ)
      (fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx
        exact claim₀ w hw)
      (Subgroup.mem_map_of_mem ψ hu₀) (fun h2 => hu₀1 (Prod.ext (claim₀ u₀ hu₀) h2))
  have hfst : ∀ a, (a, 1) ∈ (centralizerBar M hWM L₁).map ψ := by
    have := hnormψ L₁ hL₁
    exact forall_fst_mem_of_normal (Nn := (centralizerBar M hWM L₁).map ψ)
      (fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx
        exact claim₁ w hw)
      (Subgroup.mem_map_of_mem ψ hu₁) (fun h1 => hu₁1 (Prod.ext h1 (claim₁ u₁ hu₁)))
  refine Or.inr ⟨L₀, L₁, hL₀, hL₁, hLe, claim₀, claim₁, fun b => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hwb⟩ := hsnd b
    exact ⟨w, hw, hwb⟩
  · obtain ⟨w, hw, hwa⟩ := hfst a
    exact ⟨w, hw, hwa⟩
  · intro w hw
    rw [show w = w₀ from Subtype.ext hw]
    exact hw₀L
  · intro w hw
    rw [show w = w₁ from Subtype.ext hw]
    exact hw₁L
  · intro w hw
    rw [show w = w₁ from Subtype.ext hw]
    refine hpsi L₀ hL₀ w₁ hw₁p ?_
    rw [show ψ w₁ = (1, (ψ w₁).2) from Prod.ext (hc₁ w₁ rfl) rfl]
    exact hsnd _
  · intro w hw
    rw [show w = w₀ from Subtype.ext hw]
    refine hpsi L₁ hL₁ w₀ hw₀p ?_
    rw [show ψ w₀ = ((ψ w₀).1, 1) from Prod.ext rfl (hc₀ w₀ rfl)]
    exact hfst _

theorem carrying_dichotomy (h : D2AltData p M H R X) (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    ∃ (c₀ c₁ s : G) (g : ℕ) (W : Subgroup G)
      (ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)) (hWM : W ≤ M),
      AltScalar p (H ⊓ M) X c₀ c₁ s g ∧ W ≤ H ⊓ M ∧ ⁅W, W⁆ = W ∧ X ≤ W ∧
      H ⊓ M ≤ Subgroup.normalizer (W : Set G) ∧ Function.Surjective ψ ∧
      ψ.ker = (GLBPrimeCore p H).subgroupOf W ∧
      (∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) ∧ (∀ w : W, (w : G) = c₁ → (ψ w).1 = 1) ∧
      (∀ w w' : W, (w' : G) = s * w * s⁻¹ →
        ((ψ w).2 = 1 → (ψ w').1 = 1) ∧ ((ψ w).1 = 1 → (ψ w').2 = 1)) ∧
      ((∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
        ∀ w ∈ centralizerBar M hWM Lb, ψ w = 1) ∨
      (∃ L₀ L₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L₀ ⊤ ∧ IsComponentOf L₁ ⊤ ∧
        L₀ ≠ L₁ ∧ (∀ w ∈ centralizerBar M hWM L₀, (ψ w).1 = 1) ∧
        (∀ w ∈ centralizerBar M hWM L₁, (ψ w).2 = 1) ∧
        (∀ b, ∃ w ∈ centralizerBar M hWM L₀, ψ w = (1, b)) ∧
        (∀ a, ∃ w ∈ centralizerBar M hWM L₁, ψ w = (a, 1)) ∧
        (∀ w : W, (w : G) = c₀ → w ∉ centralizerBar M hWM L₀) ∧
        (∀ w : W, (w : G) = c₁ → w ∉ centralizerBar M hWM L₁) ∧
        (∀ w : W, (w : G) = c₁ → w ∈ centralizerBar M hWM L₀) ∧
        (∀ w : W, (w : G) = c₀ → w ∈ centralizerBar M hWM L₁))) := by
  obtain ⟨c₀, c₁, s, g, W, ψ, hsc, hWK, hW, hXW, hKW, hsurj, hker, hc₀, hc₁, hswap⟩ := h.perfect
  exact ⟨c₀, c₁, s, g, W, ψ, hWK.trans inf_le_right, hsc, hWK, hW, hXW, hKW, hsurj, hker, hc₀,
    hc₁, hswap, h.carrying_dichotomy_of hD1 hα hB3 h84 hD2 hsc hWK (hWK.trans inf_le_right) hW hXW
      hsurj hker hc₀ hc₁⟩

end D2AltData

end CFSG.AGLEmbeddingD2

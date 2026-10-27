module

public import CFSG.CGT.PushingUpLit.A78Sp4.Stmts
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.Assembly CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem mem_cj_iff' (g : G) (H : Subgroup G) (x : G) : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  show x ∈ H.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_cj_of_mem' (g : G) {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem side_case {L V Z J T S M : Subgroup G} {e : ℕ} (hs : Sp4Side G L V Z J T M e)
    (hSM : S ⊓ M = T) {x n : G} (hxS : x ∈ S) (hn : n ∈ M) (hx : n⁻¹ * x * n ∈ J) : x ∈ J := by
  have hL : n * (n⁻¹ * x * n) * n⁻¹ ∈ L := by
    have h1 : n⁻¹ * x * n ∈ L := hs.J_le_L hx
    have h2 := hs.normal_L.conj_mem ⟨_, hs.L_le_M h1⟩ (Subgroup.mem_subgroupOf.2 h1) ⟨n, hn⟩
    exact Subgroup.mem_subgroupOf.1 h2
  have h3 : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
  rw [h3] at hL
  have hxT : x ∈ T := by
    rw [← hSM]
    exact ⟨hxS, hs.L_le_M hL⟩
  rw [← hs.T_inf_L]
  exact ⟨hxT, hL⟩

theorem cj_cj' (a b : G) (H : Subgroup G) : cj a (cj b H) = cj (a * b) H := by
  ext x
  rw [mem_cj_iff', mem_cj_iff', mem_cj_iff']
  have : b⁻¹ * (a⁻¹ * x * a) * b = (a * b)⁻¹ * x * (a * b) := by group
  rw [this]

theorem card_cj' (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem elemAb2_cj' (g : G) {H : Subgroup G} (hH : ElemAb2 H) : ElemAb2 (cj g H) := by
  intro x hx y hy
  rw [mem_cj_iff'] at hx hy
  obtain ⟨h1, h2⟩ := hH _ hx _ hy
  refine ⟨?_, ?_⟩
  · calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  · have h3 := (hH _ hx _ hx).2
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group

theorem cj_mono' (g : G) {H K : Subgroup G} (h : H ≤ K) : cj g H ≤ cj g K :=
  Subgroup.map_mono h

theorem cj_sup' (g : G) (A B : Subgroup G) : cj g (A ⊔ B) = cj g A ⊔ cj g B :=
  Subgroup.map_sup _ _ _

theorem cj_eq_of_mem_normalizer' {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cj g H = H := by
  ext y
  rw [mem_cj_iff']
  have h1 := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)
  have h2 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h2] at h1
  exact h1

theorem exists_conj_le_sylow' [Finite G] {S K U : Subgroup G} (hS : IsSylowOf 2 S K)
    (hU : IsPGroup 2 U) (hUK : U ≤ K) : ∃ k ∈ K, cj k U ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU' : IsPGroup 2 (U.subgroupOf K) := hU.comap_subtype
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  have hP : IsSylowOf 2 ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hkc⟩ := hS.exists_mem_conj hP
  refine ⟨k⁻¹, K.inv_mem hk, fun x hx => ?_⟩
  rw [mem_cj_iff', inv_inv] at hx
  have hxP : k * x * k⁻¹ ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨k * x * k⁻¹, hUK hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have h1 := (hkc _).1 hxP
  have h2 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [h2] at h1
  exact h1

theorem inf_central' {V V₂ J : Subgroup G} (hsup : V ⊔ V₂ = J) (hV : ElemAb2 V)
    (hV₂ : ElemAb2 V₂) {y : G} (hy : y ∈ V ⊓ V₂) : J ≤ Subgroup.centralizer ({y} : Set G) := by
  rw [← hsup]
  refine sup_le (fun v hv => ?_) (fun v hv => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hV y hy.1 v hv).1.symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hV₂ y hy.2 v hv).1.symm

section Loc

variable [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem conj_mem_J' (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {s y : G} (hs : s ∈ S)
    (hy : y ∈ J) : s * y * s⁻¹ ∈ J := by
  have hJS : J ≤ S := h.base.J_le.trans h.base.T_le
  exact Subgroup.mem_subgroupOf.1
    (h.base.normal_J.conj_mem ⟨y, hJS hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨s, hs⟩)

theorem S_le_normalizer' (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) :
    S ≤ Subgroup.normalizer (J : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_J' h hs hy, fun hy => ?_⟩
  have h1 := conj_mem_J' h (S.inv_mem hs) hy
  have h2 : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rw [h2] at h1
  exact h1

theorem V_ne_V₂' (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) : V ≠ V₂ := by
  intro hVV
  have h1 := h.base.card_inf
  have h2 := h.base.card_V
  rw [← hVV, inf_idem, h2] at h1
  have h3 := Nat.pow_right_injective (le_refl 2) h1
  have h4 := h.base.two_le
  omega

theorem utype_case (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J)
    {i g x : G} (hi : UType V V₂ Z Z₂ i) (hig : g⁻¹ * i * g ∈ V ⊓ V₂)
    (hx : g⁻¹ * x * g ∈ J) : x ∈ J := by
  have hcent := inf_central' h.base.sup h.base.elem_V h.base.elem_V₂ hig
  have hcj : cj g J ≤ Subgroup.centralizer ({i} : Set G) := by
    intro z hz
    rw [mem_cj_iff'] at hz
    have h0 := hcent hz
    rw [Subgroup.mem_centralizer_singleton_iff] at h0 ⊢
    have h1 : g⁻¹ * (z * i) * g = g⁻¹ * (i * z) * g := by
      have e1 : g⁻¹ * (z * i) * g = g⁻¹ * z * g * (g⁻¹ * i * g) := by group
      have e2 : g⁻¹ * (i * z) * g = g⁻¹ * i * g * (g⁻¹ * z * g) := by group
      rw [e1, e2]
      exact h0
    exact mul_left_cancel (mul_right_cancel h1)
  have hN : cj g J ≤ Subgroup.normalizer (J : Set G) := hcj.trans (h410 i hi)
  have hJS : J ≤ S := h.base.J_le.trans h.base.T_le
  have hSN : IsSylowOf 2 S (Subgroup.normalizer (J : Set G)) :=
    h.base.sylow.of_le (S_le_normalizer' h) le_top
  have hpg : IsPGroup 2 (cj g J) := (h.base.sylow.isPGroup.to_le hJS).map _
  obtain ⟨n, hn, hnle⟩ := exists_conj_le_sylow' hSN hpg hN
  rw [cj_cj'] at hnle
  have hVJ : V ≤ J := by rw [← h.base.sup]; exact le_sup_left
  have hV₂J : V₂ ≤ J := by rw [← h.base.sup]; exact le_sup_right
  have hA : ∀ W : Subgroup G, W ≤ cj (n * g) J → ElemAb2 W → Nat.card W = 2 ^ (3 * e) →
      W = V ∨ W = V₂ := fun W hW hW2 hWc => h.base.A_S W (hW.trans hnle) hW2 hWc
  have h1 := hA (cj (n * g) V) (cj_mono' _ hVJ) (elemAb2_cj' _ h.base.elem_V)
    (by rw [card_cj', h.base.card_V])
  have h2 := hA (cj (n * g) V₂) (cj_mono' _ hV₂J) (elemAb2_cj' _ h.base.elem_V₂)
    (by rw [card_cj', h.base.card_V₂])
  have hne : cj (n * g) V ≠ cj (n * g) V₂ := fun hh =>
    V_ne_V₂' h (Subgroup.map_injective (MulAut.conj (n * g)).injective hh)
  have hJJ : cj (n * g) J = J := by
    rw [← h.base.sup, cj_sup']
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hne
  have hgJ : cj g J = J := by
    have h3 := cj_cj' n⁻¹ (n * g) J
    rw [hJJ, cj_eq_of_mem_normalizer' (Subgroup.inv_mem _ hn)] at h3
    have h4 : n⁻¹ * (n * g) = g := by group
    rw [h4] at h3
    exact h3.symm
  have : x ∈ cj g J := (mem_cj_iff' g J x).2 hx
  rwa [hgJ] at this

omit [Finite G] in
theorem ti_normalizer {L' V' Z' M' : Subgroup G} (hs : Sp4Side G L' V' Z' J T M' e) {w n : G}
    (hw : w ∈ Z') (hw1 : w ≠ 1) (hn : n⁻¹ * w * n ∈ Z') : n ∈ M' := by
  have hv1 : n⁻¹ * w * n ≠ 1 := by
    intro h1
    apply hw1
    have h2 : w = n * (n⁻¹ * w * n) * n⁻¹ := by group
    rw [h2, h1]
    group
  have hv : n⁻¹ * w * n ∈ cj n⁻¹ Z' := by
    rw [mem_cj_iff', inv_inv]
    have h3 : n * (n⁻¹ * w * n) * n⁻¹ = w := by group
    rw [h3]
    exact hw
  have hne : Z' ⊓ cj n⁻¹ Z' ≠ ⊥ := by
    intro hbot
    have : n⁻¹ * w * n ∈ Z' ⊓ cj n⁻¹ Z' := ⟨hn, hv⟩
    rw [hbot] at this
    exact hv1 ((Subgroup.mem_bot).1 this)
  have hcj := hs.ti n⁻¹ hne
  rw [← hs.normalizer_Z, Subgroup.mem_normalizer_iff]
  intro y
  have h4 : y ∈ Z' ↔ y ∈ cj n⁻¹ Z' := by rw [hcj]
  rw [h4, mem_cj_iff', inv_inv]

theorem z_case (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {i g x : G}
    (hi : i ∈ Z ∨ i ∈ Z₂) (hi1 : i ≠ 1) (hig : g⁻¹ * i * g ∈ Z ∨ g⁻¹ * i * g ∈ Z₂)
    (hxS : x ∈ S) (hx : g⁻¹ * x * g ∈ J) : x ∈ J := by
  obtain ⟨s, hsS, hsT⟩ := h.base.exists_swap
  have hZs := h.cross.swap_Z s hsS hsT
  have hxs : s * x * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS)
  have hconj : ∀ w : G, w ≠ 1 → s * w * s⁻¹ ≠ 1 := by
    intro w hw1 hw
    apply hw1
    have : w = s⁻¹ * (s * w * s⁻¹) * s := by group
    rw [this, hw]
    group
  have hsx : (s * g)⁻¹ * (s * x * s⁻¹) * (s * g) = g⁻¹ * x * g := by group
  have hsi : (s * g)⁻¹ * (s * i * s⁻¹) * (s * g) = g⁻¹ * i * g := by group
  rcases hi with hi | hi <;> rcases hig with hig | hig
  ·
    have hn : g ∈ M := ti_normalizer h.side₁ hi hi1 hig
    exact side_case h.side₁ h.base.S_inf_M hxS hn hx
  ·
    have hw : s * i * s⁻¹ ∈ Z₂ := by
      have := mem_cj_of_mem' s hi
      rwa [hZs.1] at this
    have hn : s * g ∈ M₂ := ti_normalizer h.side₂ hw (hconj i hi1) (by rw [hsi]; exact hig)
    have := side_case h.side₂ h.base.S_inf_M₂ hxs hn (by rw [hsx]; exact hx)
    have h5 := conj_mem_J' h (S.inv_mem hsS) this
    simpa [mul_assoc] using h5
  ·
    have hw : s * i * s⁻¹ ∈ Z := by
      have := mem_cj_of_mem' s hi
      rwa [hZs.2] at this
    have hn : s * g ∈ M := ti_normalizer h.side₁ hw (hconj i hi1) (by rw [hsi]; exact hig)
    have := side_case h.side₁ h.base.S_inf_M hxs hn (by rw [hsx]; exact hx)
    have h5 := conj_mem_J' h (S.inv_mem hsS) this
    simpa [mul_assoc] using h5
  ·
    have hn : g ∈ M₂ := ti_normalizer h.side₂ hi hi1 hig
    exact side_case h.side₂ h.base.S_inf_M₂ hxS hn hx

theorem sp4_413 (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J)
    (hM : Sp4StmtM S J) (h412 : Sp4Stmt412 T J) : S = J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hTJ : T = J := h412
  have hJS : J ≤ S := h.base.J_le.trans h.base.T_le
  have hrel : J.relIndex S ≤ 2 := by rw [← hTJ]; exact h.base.index
  have hrel1 : J.relIndex S ≠ 1 := fun h1 => hne (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hJS)
  have hrel0 : J.relIndex S ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hidx : J.relIndex S = 2 := by omega
  have hsq : ∀ y ∈ S, y * y ∈ J := fun y hy =>
    Subgroup.mem_subgroupOf.1
      (Subgroup.mul_self_mem_of_index_two (H := J.subgroupOf S) hidx ⟨y, hy⟩)
  have hex : ∃ n : ℕ, ∃ y ∈ S, y ∉ J ∧ orderOf y = n := by
    obtain ⟨y, hyS, hyJ⟩ : ∃ y ∈ S, y ∉ J := by
      by_contra hcon
      refine hne (le_antisymm (fun y hy => ?_) hJS)
      by_contra hyJ
      exact hcon ⟨y, hy, hyJ⟩
    exact ⟨_, y, hyS, hyJ, rfl⟩
  obtain ⟨x, hxS, hxJ, hxo⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ S, y ∉ J → orderOf x ≤ orderOf y := fun y hy hyJ => by
    rw [hxo]
    exact Nat.find_min' hex ⟨y, hy, hyJ, rfl⟩
  have hxT : x ∉ T := by rw [hTJ]; exact hxJ
  have hconj : ∀ g : G, g⁻¹ * x * g ∉ J := by
    intro g hg
    by_cases hx2 : x * x = 1
    · exact hxJ (hM x hxS hx2 g hg)
    · have hxg2 : g⁻¹ * x * g * (g⁻¹ * x * g) ∈ V ⊓ V₂ := h.base.sq_mem _ hg
      have hid : g⁻¹ * (x * x) * g = g⁻¹ * x * g * (g⁻¹ * x * g) := by group
      have hii : x * x * (x * x) = 1 := by
        have h1 := (h.base.elem_V _ hxg2.1 _ hxg2.1).2
        have h2 : x * x * (x * x) = g * (g⁻¹ * x * g * (g⁻¹ * x * g) *
            (g⁻¹ * x * g * (g⁻¹ * x * g))) * g⁻¹ := by group
        rw [h2, h1]
        group
      have hiJ : x * x ∈ J := hsq x hxS
      have hiV : x * x ∈ V ∨ x * x ∈ V₂ := h.base.inv_mem _ hiJ hii
      have hsw := h.base.swap x hxS hxT
      have hcomm : x * (x * x) * x⁻¹ = x * x := by group
      have hiVV : x * x ∈ V ⊓ V₂ := by
        rcases hiV with hv | hv
        · refine ⟨hv, ?_⟩
          have := mem_cj_of_mem' x hv
          rw [hcomm, hsw.1] at this
          exact this
        · refine ⟨?_, hv⟩
          have := mem_cj_of_mem' x hv
          rw [hcomm, hsw.2] at this
          exact this
      have hig : g⁻¹ * (x * x) * g ∈ V ⊓ V₂ := by rw [hid]; exact hxg2
      by_cases hu : UType V V₂ Z Z₂ (x * x)
      · exact hxJ (utype_case h h410 hu hig hg)
      · have hiZ : x * x ∈ Z ∨ x * x ∈ Z₂ := by
          by_contra hcon
          exact hu ⟨hiVV, fun h1 => hcon (Or.inl h1), fun h2 => hcon (Or.inr h2)⟩
        have hguZ : g⁻¹ * (x * x) * g ∈ Z ∨ g⁻¹ * (x * x) * g ∈ Z₂ := by
          by_contra hcon
          have hut : UType V V₂ Z Z₂ (g⁻¹ * (x * x) * g) :=
            ⟨hig, fun h1 => hcon (Or.inl h1), fun h2 => hcon (Or.inr h2)⟩
          have := h.cross.u_not_conj _ (x * x) hut hiZ hx2 g⁻¹
          apply this
          group
        exact hxJ (z_case h hiZ hx2 hguZ hxS hg)
  have hSp : IsPGroup 2 S := h.base.sylow.isPGroup
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 := (isSylowOf_iff.1 h.base.sylow).2.2
    rwa [Subgroup.relIndex_top_right] at h1
  obtain ⟨N, hN, hNi⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hSp hSidx hJS
    hidx hxS hxJ hmin hconj
  rcases h.simple.eq_bot_or_eq_top_of_normal N with hN1 | hN1
  · rw [hN1, Subgroup.index_bot] at hNi
    have h1 := Subgroup.card_le_card_group V
    rw [h.base.card_V, hNi] at h1
    have h2 := h.base.two_le
    have h3 : 2 ^ 2 ≤ 2 ^ (3 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [hN1, Subgroup.index_top] at hNi
    omega

end Loc

end CFSG.CGT.PushingUpLit.A78Sp4

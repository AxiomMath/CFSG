module

public import CFSG.CGT.PushingUpLit.A78Sp4.Stmts
public import CFSG.CGT.PushingUpLit.A78Sp4.UCentral

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem Sp4Side.conj_mem_L {L V Z J T M : Subgroup G} {e : ℕ} (hs : Sp4Side G L V Z J T M e)
    {m x : G} (hm : m ∈ M) (hx : x ∈ L) : m * x * m⁻¹ ∈ L := by
  have h2 := hs.normal_L.conj_mem ⟨x, hs.L_le_M hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 h2

theorem sp4_side_step [Finite G] {L V W Z J T M S : Subgroup G} {e : ℕ}
    (hs : Sp4Side G L V Z J T M e) (hTS : T ≤ S) (hSM : S ⊓ M = T)
    (hA : ∀ E : Subgroup G, E ≤ S → ElemAb2 E → Nat.card E = 2 ^ (3 * e) → E = V ∨ E = W)
    (hWJ : W ≤ J) {U : Subgroup G} (hU : ElemAb2 U) (hUcard : Nat.card U = 2 ^ (3 * e))
    (hUM : U ≤ M) {a : G} (haS : a ∈ S) (haU : a ∈ U) : a ∈ J := by
  obtain ⟨m, hm, hmU⟩ := exists_conj_le_of_isSylowOf hs.sylow_T hUM hU.isPGroup
  have hE : ElemAb2 (cj m U) := elemAb2_cj hU m
  have hcard : Nat.card (cj m U) = 2 ^ (3 * e) := (card_cj m U).trans hUcard
  have hma : m * a * m⁻¹ ∈ cj m U := mul_mem_cj m haU
  have haL : a ∈ L := by
    rcases hA (cj m U) (hmU.trans hTS) hE hcard with hV | hW
    · rw [hV] at hma
      have hm' : m ∈ Subgroup.normalizer (V : Set G) := by
        rw [← hs.M_eq]
        exact hm
      exact hs.V_le_L ((Subgroup.mem_normalizer_iff.1 hm' a).2 hma)
    · rw [hW] at hma
      have h1 := hs.conj_mem_L (M.inv_mem hm) (hs.J_le_L (hWJ hma))
      have h3 : m⁻¹ * (m * a * m⁻¹) * m⁻¹⁻¹ = a := by group
      rwa [h3] at h1
  have haT : a ∈ T := hSM ▸ ⟨haS, hs.L_le_M haL⟩
  exact hs.T_inf_L ▸ ⟨haT, haL⟩

theorem sp4_sylow_cent_side [Finite G] {L V Z J T M : Subgroup G} {e : ℕ}
    (hs : Sp4Side G L V Z J T M e) (hV : ElemAb2 V) (he : 1 ≤ e)
    (hTZ : ∀ t ∈ T, cj t Z = Z) {y : G} (hy : y ∈ Z) (hy1 : y ≠ 1) :
    ∃ m : G, IsSylowOf 2 (cj m T) (Subgroup.centralizer ({y} : Set G)) := by
  have hZV : Z ≤ V := by
    rw [hs.Z_eq]
    exact inf_le_left
  have hZ1 : Z ≠ ⊥ := by
    intro hbot
    have h1 : (2 : ℕ) ^ e = 1 := by rw [← hs.card_Z, hbot, Subgroup.card_bot]
    have := Nat.one_lt_two_pow (n := e) (by omega)
    omega
  obtain ⟨z₀, hz₀, hz₀1, hz₀T⟩ := exists_fixed_ne_one hs.sylow_T.isPGroup (hV.mono hZV) hZ1 hTZ
  obtain ⟨m, hm, hmz⟩ := hs.trans z₀ hz₀ hz₀1 y hy hy1
  refine ⟨m, (isSylowOf_cj_of_mem hs.sylow_T hm).of_le ?_ (hs.cent_z y hy hy1)⟩
  intro x hx
  rw [mem_cj_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← hmz]
  have h1 : m⁻¹ * x * m * z₀ = z₀ * (m⁻¹ * x * m) := by
    have h2 := hz₀T _ hx
    calc m⁻¹ * x * m * z₀ = m⁻¹ * x * m * z₀ * (m⁻¹ * x * m)⁻¹ * (m⁻¹ * x * m) := by group
      _ = z₀ * (m⁻¹ * x * m) := by rw [h2]
  calc x * (m * z₀ * m⁻¹) = m * (m⁻¹ * x * m * z₀) * m⁻¹ := by group
    _ = m * (z₀ * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
    _ = m * z₀ * m⁻¹ * x := by group

variable [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem sp4_M_final (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J)
    {U : Subgroup G} (hU : ElemAb2 U) (hUcard : Nat.card U = 2 ^ (3 * e)) {a y : G}
    (haS : a ∈ S) (haU : a ∈ U) (hyU : y ∈ U) (hyE : y ∈ V ⊓ V₂) (hy1 : y ≠ 1) : a ∈ J := by
  have hUy : U ≤ Subgroup.centralizer ({y} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hU x hx y hyU).1
  have hVJ : V ≤ J := by
    rw [← h.base.sup]
    exact le_sup_left
  have hV₂J : V₂ ≤ J := by
    rw [← h.base.sup]
    exact le_sup_right
  by_cases hZ : y ∈ Z
  · exact sp4_side_step h.side₁ h.base.T_le h.base.S_inf_M h.base.A_S hV₂J hU hUcard
      (hUy.trans (h.side₁.cent_z y hZ hy1)) haS haU
  by_cases hZ₂ : y ∈ Z₂
  · exact sp4_side_step h.side₂ h.base.T_le h.base.S_inf_M₂
      (fun E hE hE2 hc => (h.base.A_S E hE hE2 hc).symm) hVJ hU hUcard
      (hUy.trans (h.side₂.cent_z y hZ₂ hy1)) haS haU
  have hN : U ≤ Subgroup.normalizer (J : Set G) := hUy.trans (h410 y ⟨hyE, hZ, hZ₂⟩)
  have hJS : J ≤ S := h.base.J_le.trans h.base.T_le
  have hSN : S ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).1 h.base.normal_J
  have hSyl : IsSylowOf 2 S (Subgroup.normalizer (J : Set G)) := h.base.sylow.of_le hSN le_top
  obtain ⟨n, hn, hnU⟩ := exists_conj_le_of_isSylowOf hSyl hN hU.isPGroup
  have hE : ElemAb2 (cj n U) := elemAb2_cj hU n
  have hcard : Nat.card (cj n U) = 2 ^ (3 * e) := (card_cj n U).trans hUcard
  have hna : n * a * n⁻¹ ∈ cj n U := mul_mem_cj n haU
  have hnaJ : n * a * n⁻¹ ∈ J := by
    rcases h.base.A_S (cj n U) hnU hE hcard with hV | hV₂
    · rw [hV] at hna
      exact hVJ hna
    · rw [hV₂] at hna
      exact hV₂J hna
  exact (Subgroup.mem_normalizer_iff.1 hn a).2 hnaJ

theorem sp4_M_core (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J)
    {a h0 : G} {P : Subgroup G} (hP : P = T ∨ P = S) (haS : a ∈ S) (ha2 : a * a = 1)
    (hRC : cj h0 P ≤ Subgroup.centralizer ({a} : Set G))
    (hCS : S ⊓ Subgroup.centralizer ({a} : Set G) ≤ cj h0 P) : a ∈ J := by
  have hJS : J ≤ S := h.base.J_le.trans h.base.T_le
  have hPS : P ≤ S := by
    rcases hP with rfl | rfl
    · exact h.base.T_le
    · exact le_rfl
  have hJP : J ≤ P := by
    rcases hP with rfl | rfl
    · exact h.base.J_le
    · exact hJS
  have hVJ : V ≤ J := by
    rw [← h.base.sup]
    exact le_sup_left
  have hV₂J : V₂ ≤ J := by
    rw [← h.base.sup]
    exact le_sup_right
  have step2 : ∀ W : Subgroup G, ElemAb2 W → Nat.card W = 2 ^ (3 * e) → W ≤ J →
      h0⁻¹ * a * h0 ∈ W := by
    intro W hW hWc hWJ
    refine mem_of_commute_involution hW hWc h.base.rank (a := h0⁻¹ * a * h0) ?_ ?_
    · calc h0⁻¹ * a * h0 * (h0⁻¹ * a * h0) = h0⁻¹ * (a * a) * h0 := by group
        _ = 1 := by rw [ha2]; group
    · intro v hv
      have hcomm : a * (h0 * v * h0⁻¹) = (h0 * v * h0⁻¹) * a :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hRC (mul_mem_cj h0 (hJP (hWJ hv))))).symm
      calc h0⁻¹ * a * h0 * v = h0⁻¹ * (a * (h0 * v * h0⁻¹)) * h0 := by group
        _ = h0⁻¹ * ((h0 * v * h0⁻¹) * a) * h0 := by rw [hcomm]
        _ = v * (h0⁻¹ * a * h0) := by group
  have hE₀ : ElemAb2 (V ⊓ V₂) := h.base.elem_V.mono inf_le_left
  have hcardE : 2 ^ (2 * e) ≤
      Nat.card ↥((V ⊓ V₂) ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
    have := card_le_card_centralizer_sq hE₀ ha2 (fun x hx => h.base.conj_mem_inf haS hx)
    rwa [h.base.card_inf] at this
  have hc4 : 4 ≤ Nat.card ↥((V ⊓ V₂) ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have h2e : 2 ^ e ≤ Nat.card ↥((V ⊓ V₂) ⊓ Subgroup.centralizer ({a} : Set G)) := by
      refine (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
      rwa [← pow_mul, mul_comm]
    have h4 : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.base.two_le
    exact h4.trans h2e
  set C₀ := (V ⊓ V₂) ⊓ Subgroup.centralizer ({a} : Set G) with hC₀
  have hC₀P : C₀ ≤ cj h0 P := fun x hx => hCS ⟨hJS (hVJ hx.1.1), hx.2⟩
  have hC₀E : ElemAb2 (cj h0⁻¹ C₀) := elemAb2_cj (hE₀.mono inf_le_left) h0⁻¹
  have hC''S : cj h0⁻¹ C₀ ≤ S := by
    intro x hx
    rw [mem_cj_iff, inv_inv] at hx
    have h1 := hC₀P hx
    rw [mem_cj_iff] at h1
    have h3 : h0⁻¹ * (h0 * x * h0⁻¹) * h0 = x := by group
    rw [h3] at h1
    exact hPS h1
  obtain ⟨y'', hy''C, hy''J, hy''1⟩ := inf_ne_bot_of_quot_cyclic h.base.normal_J
    h.field.S_cyclic hC''S hC₀E (by rwa [card_cj])
  have hy''C' : h0 * y'' * h0⁻¹ ∈ C₀ := by
    rw [mem_cj_iff, inv_inv] at hy''C
    exact hy''C
  have hy''sq : y'' * y'' = 1 := (hC₀E y'' hy''C y'' hy''C).2
  have hfin : ∀ W : Subgroup G, ElemAb2 W → Nat.card W = 2 ^ (3 * e) → W ≤ J → y'' ∈ W →
      a ∈ J := by
    intro W hW hWc hWJ hyW
    refine sp4_M_final h h410 (U := cj h0 W) (elemAb2_cj hW h0) ((card_cj h0 W).trans hWc) haS
      ?_ (mul_mem_cj h0 hyW) hy''C'.1 ?_
    · rw [mem_cj_iff]
      exact step2 W hW hWc hWJ
    · intro h1
      apply hy''1
      have h3 : y'' = h0⁻¹ * (h0 * y'' * h0⁻¹) * h0 := by group
      rw [h3, h1]
      group
  rcases h.base.inv_mem y'' hy''J hy''sq with hV | hV₂
  · exact hfin V h.base.elem_V h.base.card_V hVJ hV
  · exact hfin V₂ h.base.elem_V₂ h.base.card_V₂ hV₂J hV₂

theorem sp4_M_step1 (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {a c y₀ : G}
    (hc : c * y₀ * c⁻¹ = a) (hy₀1 : y₀ ≠ 1)
    (hcls : y₀ ∈ Z ∨ y₀ ∈ Z₂ ∨ UType V V₂ Z Z₂ y₀) :
    ∃ h0 : G, ∃ P : Subgroup G, (P = T ∨ P = S) ∧
      cj h0 P ≤ Subgroup.centralizer ({a} : Set G) ∧
      S ⊓ Subgroup.centralizer ({a} : Set G) ≤ cj h0 P := by
  have he : 1 ≤ e := le_trans (by norm_num) h.base.two_le
  obtain ⟨R, hR, hCSR⟩ := exists_isSylowOf_ge (K := Subgroup.centralizer ({a} : Set G))
    (U := S ⊓ Subgroup.centralizer ({a} : Set G)) h.base.sylow.isPGroup.to_inf_left inf_le_right
  have key : ∃ h0 : G, ∃ P : Subgroup G, (P = T ∨ P = S) ∧ R = cj h0 P := by
    rcases hcls with hZ | hZ₂ | hU
    · obtain ⟨m, hm⟩ := sp4_sylow_cent_side h.side₁ h.base.elem_V he
        (fun t ht => (h.cross.T_normZ t ht).1) hZ hy₀1
      obtain ⟨h1, h1R⟩ := exists_eq_cj_of_centralizer hc hm hR
      exact ⟨h1 * m, T, Or.inl rfl, by rw [h1R, cj_cj]⟩
    · obtain ⟨m, hm⟩ := sp4_sylow_cent_side h.side₂ h.base.elem_V₂ he
        (fun t ht => (h.cross.T_normZ t ht).2) hZ₂ hy₀1
      obtain ⟨h1, h1R⟩ := exists_eq_cj_of_centralizer hc hm hR
      exact ⟨h1 * m, T, Or.inl rfl, by rw [h1R, cj_cj]⟩
    · obtain ⟨u, hu, hucent⟩ := sp4_exists_u_central h
      obtain ⟨n, -, hn⟩ := h.cross.u_conj y₀ u hU hu
      have hw : (c * n⁻¹) * u * (c * n⁻¹)⁻¹ = a := by
        rw [← hc, ← hn]
        group
      have hSu : IsSylowOf 2 S (Subgroup.centralizer ({u} : Set G)) := by
        refine h.base.sylow.of_le (fun s hs => ?_) le_top
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc s * u = s * u * s⁻¹ * s := by group
          _ = u * s := by rw [hucent s hs]
      obtain ⟨h1, h1R⟩ := exists_eq_cj_of_centralizer hw hSu hR
      exact ⟨h1, S, Or.inr rfl, h1R⟩
  obtain ⟨h0, P, hP, hRP⟩ := key
  refine ⟨h0, P, hP, ?_, ?_⟩
  · rw [← hRP]
    exact hR.le
  · rw [← hRP]
    exact hCSR

theorem sp4_M (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J) :
    Sp4StmtM S J := by
  intro a haS ha2 g hg
  by_contra haJ
  have ha1 : a ≠ 1 := by
    intro h1
    apply haJ
    rw [h1]
    exact J.one_mem
  have hb2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hb1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨g', hg'⟩ := h.cross.inv_class _ hg hb2 hb1
  have hc : (g * g') * (g'⁻¹ * (g⁻¹ * a * g) * g') * (g * g')⁻¹ = a := by group
  have hy₀1 : g'⁻¹ * (g⁻¹ * a * g) * g' ≠ 1 := by
    intro h1
    apply ha1
    calc a = (g * g') * (g'⁻¹ * (g⁻¹ * a * g) * g') * (g * g')⁻¹ := hc.symm
      _ = 1 := by rw [h1]; group
  obtain ⟨h0, P, hP, hRC, hCS⟩ := sp4_M_step1 h hc hy₀1 hg'
  exact haJ (sp4_M_core h h410 hP haS ha2 hRC hCS)

end CFSG.CGT.PushingUpLit.A78Sp4

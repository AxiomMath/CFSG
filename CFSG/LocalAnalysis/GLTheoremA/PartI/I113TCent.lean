module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Tri
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgtAC
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJK
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

structure Red3 (B M : Subgroup Q) (c : Q) (T : Subgroup Q) : Prop where
  tri : Triple3 B M c
  hidx_all : ∀ M' : Subgroup Q, IsComponentOf M' ⊤ →
    (Subgroup.normalizer (M' : Set Q)).relIndex B ∣ 3
  T_ne : T ≠ ⊥
  T_two : IsPGroup 2 T
  T_norm : B ≤ Subgroup.normalizer (T : Set Q)
  T_min : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T
  T_elem : IsElemAbelian 2 T
  T_card : Nat.card T ≤ 4

section Perm

variable {B L : Subgroup Q} {x : Q}

theorem Triple3.cjk_conj_B (Tr : Triple3 B L x) {g : Q} (hg : g ∈ B) :
    ∃ n : ℕ, n < 3 ∧ GLBConj g L = GLBConj (x ^ n) L := by
  set N := Subgroup.normalizer (L : Set Q) with hN
  have hnorm : (N.subgroupOf B).Normal := ⟨fun n hn g => by
    have : ((g * n * g⁻¹ : B) : Q) = (n : Q) := by
      have h := Tr.comm_B g.2 n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]; group
    rw [Subgroup.mem_subgroupOf, this]
    exact hn⟩
  have hidx : (N.subgroupOf B).index = 3 := Tr.index
  have hcard : Nat.card (B ⧸ N.subgroupOf B) = 3 := by
    rw [← hidx, Subgroup.index_eq_card]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact Tr.not_mem h
  have htop := zpowers_eq_top_of_prime_card hcard hx1
  have hg' : (QuotientGroup.mk (⟨g, hg⟩ : B) : B ⧸ N.subgroupOf B) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) := by
    rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'
  have hx3 : (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ^ 3 = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  have e := zpow_eq_zpow_emod' (x := (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B))
    k hx3
  have hr : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  have key : ∀ n : ℕ, n < 3 →
      (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ^ n =
        (QuotientGroup.mk (⟨g, hg⟩ : B) : B ⧸ N.subgroupOf B) → GLBConj g L = GLBConj (x ^ n) L := by
    intro n hn hnk
    have hq : (QuotientGroup.mk (⟨x ^ n, B.pow_mem Tr.mem n⟩ : B) : B ⧸ N.subgroupOf B) =
        QuotientGroup.mk (⟨g, hg⟩ : B) := by
      rw [← hnk]; rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
    have hq' : (x ^ n)⁻¹ * g ∈ N := hq
    have hc : (x ^ n) * g = g * (x ^ n) := Tr.comm_B (B.pow_mem Tr.mem n) hg
    have hgeq : g = ((x ^ n)⁻¹ * g) * x ^ n := by
      calc g = (x ^ n)⁻¹ * (x ^ n * g) := by group
        _ = (x ^ n)⁻¹ * (g * x ^ n) := by rw [hc]
        _ = _ := by group
    have h1 : GLBConj ((x ^ n)⁻¹ * g) L = L := mem_normalizer_iff_gLBConj_eq.1 hq'
    calc GLBConj g L = GLBConj (((x ^ n)⁻¹ * g) * x ^ n) L := by rw [← hgeq]
      _ = GLBConj (x ^ n) (GLBConj ((x ^ n)⁻¹ * g) L) := (gLBConj_gLBConj _ _ _).symm
      _ = GLBConj (x ^ n) L := by rw [h1]
  rcases hr with h | h | h
  · refine ⟨0, by norm_num, key 0 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp
  · refine ⟨1, by norm_num, key 1 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp
  · refine ⟨2, by norm_num, key 2 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp


theorem Triple3.cjkC_succ (Tr : Triple3 B L x) (i : Fin 3) :
    GLBConj x (cjkC L x i) = cjkC L x (i + 1) := by
  unfold cjkC
  rw [gLBConj_gLBConj]
  fin_cases i
  · simp
  · simp [pow_two]
  · have h3 : x ^ 2 * x = x ^ 3 := by group
    have := mem_normalizer_iff_gLBConj_eq.1 Tr.pow_three_mem
    show GLBConj (x ^ 2 * x) L = GLBConj (x ^ 0) L
    rw [h3, this, pow_zero, gLBConj_one]

theorem Triple3.cjkC_pred (Tr : Triple3 B L x) (i : Fin 3) :
    GLBConj x⁻¹ (cjkC L x i) = cjkC L x (i - 1) := by
  have h := Tr.cjkC_succ (i - 1)
  rw [sub_add_cancel] at h
  rw [← h, gLBConj_inv_gLBConj]


theorem Triple3.cjkC_inj (Tr : Triple3 B L x) {i j : Fin 3} (h : cjkC L x i = cjkC L x j) :
    i = j := by
  have h1 := Tr.conj1_ne
  have h2 := Tr.conj2_ne
  have h21 := Tr.conj21_ne
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cjkC_zero, cjkC_one,
         cjkC_two] at h
       first | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm | exact h21 h | exact h21 h.symm)


theorem Triple3.cjk_mem_of_normalizes (Tr : Triple3 B L x) {t : Q}
    (ht : t ∈ Subgroup.normalizer (t113K B L : Set Q)) (i : Fin 3) :
    ∃ j : Fin 3, GLBConj t (cjkC L x i) = cjkC L x j := by
  have hMeq : GLBConj t (cjkC L x i) = GLBConj (x ^ (i : ℕ) * t) L := by
    unfold cjkC; rw [gLBConj_gLBConj]
  have hMcomp : IsComponentOf (GLBConj (x ^ (i : ℕ) * t) L) ⊤ := Tr.comp_conj _
  have hMK : GLBConj (x ^ (i : ℕ) * t) L ≤ t113K B L := by
    intro z hz
    rw [mem_gLBConj] at hz
    have h1 := Tr.conj_le_K (B.pow_mem Tr.mem (i : ℕ))
      (cjk_conj_mem_conj (g := x ^ (i : ℕ)) hz)
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) _).1 h1
    have hk : z = t⁻¹ * ((x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * t * z * (x ^ (i : ℕ) * t)⁻¹) *
        x ^ (i : ℕ)) * t := by group
    rw [hk]
    simpa using h2
  have hex : ∃ g ∈ B, GLBConj (x ^ (i : ℕ) * t) L = GLBConj g L := by
    by_contra hno
    push Not at hno
    have hcomm : ∀ g ∈ B, ∀ u ∈ GLBConj (x ^ (i : ℕ) * t) L, ∀ w ∈ GLBConj g L,
        u * w = w * u := by
      intro g hg
      rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hMcomp (Tr.comp_conj g) with h | h
      · exact absurd h (hno g hg)
      · exact h
    have hcK : ∀ u ∈ GLBConj (x ^ (i : ℕ) * t) L, ∀ w ∈ t113K B L, u * w = w * u := by
      intro u hu
      have hle : t113K B L ≤ Subgroup.centralizer ({u} : Set Q) := by
        refine iSup₂_le fun g hg w hw => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm g hg u hu w hw).symm
      intro w hw
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hw)).symm
    exact not_commute_of_isComponentOf hMcomp
      (fun u hu w hw => hcK u hu w (hMK hw))
  obtain ⟨g, hg, hMg⟩ := hex
  obtain ⟨n, hn, hgn⟩ := Tr.cjk_conj_B hg
  exact ⟨⟨n, hn⟩, by rw [hMeq, hMg, hgn]; rfl⟩


theorem Triple3.cjk_le_normalizer (Tr : Triple3 B L x) {T : Subgroup Q}
    (hTK : T ≤ Subgroup.normalizer (t113K B L : Set Q))
    (hTB : B ≤ Subgroup.normalizer (T : Set Q)) (hTe : IsElemAbelian 2 T) :
    T ≤ Subgroup.normalizer (L : Set Q) := by
  intro t ht
  have hex : ∀ s ∈ T, ∃ f : Fin 3 → Fin 3, ∀ i, GLBConj s (cjkC L x i) = cjkC L x (f i) := by
    intro s hs
    choose f hf using fun i => Tr.cjk_mem_of_normalizes (hTK hs) i
    exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hex t ht
  have ht' : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hTB Tr.mem) t).1 ht
  obtain ⟨f', hf'⟩ := hex _ ht'
  have hff : ∀ i, f (f i) = i := by
    intro i
    have h : GLBConj t (GLBConj t (cjkC L x i)) = cjkC L x i := by
      rw [gLBConj_gLBConj, ← pow_two, hTe.2 t ht, gLBConj_one]
    rw [hf, hf] at h
    exact Tr.cjkC_inj h
  have hf'eq : ∀ i, f' i = f (i + 1) - 1 := by
    intro i
    have h : GLBConj (x * t * x⁻¹) (cjkC L x i) =
        GLBConj x⁻¹ (GLBConj t (GLBConj x (cjkC L x i))) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_assoc]
    rw [hf', Tr.cjkC_succ, hf, Tr.cjkC_pred] at h
    exact Tr.cjkC_inj h
  have hcomm : ∀ i, f' (f i) = f (f' i) := by
    intro i
    have hc : t * (x * t * x⁻¹) = (x * t * x⁻¹) * t := by
      have := hTe.1.is_comm.comm (⟨t, ht⟩ : T) ⟨x * t * x⁻¹, ht'⟩
      exact congrArg Subtype.val this
    have h : GLBConj (x * t * x⁻¹) (GLBConj t (cjkC L x i)) =
        GLBConj t (GLBConj (x * t * x⁻¹) (cjkC L x i)) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, hc]
    rw [hf, hf', hf', hf] at h
    exact Tr.cjkC_inj h
  have h0 := cjk_perm_aux f hff (fun i => by
    have := hcomm i
    simp only [hf'eq] at this
    exact this) 0
  have h1 := hf 0
  rw [h0, cjkC_zero] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1



end Perm

section ACent

variable {B L T : Subgroup Q} {x : Q}

theorem Red3.A_centralizes {B L T : Subgroup Q} {x : Q} (R : Red3 B L x T)
    (hK : ¬ T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q)) :
    ∀ a ∈ t113A B L, ∀ t ∈ T, a * t = t * a := by
  have Tr := R.tri
  have hBT : ∀ b ∈ B, ∀ u ∈ T, b * u * b⁻¹ ∈ T := fun b hb u hu =>
    ((Subgroup.mem_normalizer_iff.1 (R.T_norm hb)) u).1 hu
  by_contra hcon
  push Not at hcon
  obtain ⟨a0, ha0, t, ht, hne⟩ := hcon
  have hCTbot : T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) = ⊥ := by
    have hn : B ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) : Subgroup Q) : Set Q) := by
      have fwd : ∀ b ∈ B, ∀ h ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q),
          b * h * b⁻¹ ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) := by
        intro b hb h hh
        refine ⟨hBT b hb h hh.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
        have hc2 : Commute a h := Subgroup.mem_centralizer_iff.1 hh.2 a ha
        have hab : Commute a b := Tr.comm_B ha.2 hb
        exact ((hab.mul_right hc2).mul_right hab.inv_right).eq
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fwd b hb h, fun h' => ?_⟩
      have := fwd b⁻¹ (B.inv_mem hb) _ h'
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [e] at this
    rcases R.T_min _ inf_le_left hn with h | h
    · exact h
    · exfalso
      have : t ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) := by
        rw [h]; exact ht
      exact hne (Subgroup.mem_centralizer_iff.1 this.2 a0 ha0)
  have hCT : ∀ u ∈ T, (∀ a ∈ t113A B L, a * u = u * a) → u = 1 := by
    intro u hu hc
    have : u ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) :=
      ⟨hu, Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha⟩
    rw [hCTbot, Subgroup.mem_bot] at this
    exact this
  have hTL : ¬ T ≤ Subgroup.normalizer (L : Set Q) := fun h =>
    hK (t113_T_le_normalizer_K (t113_h_of_T_le_normalizer R.T_norm h))
  have hT1 : ∀ u ∈ T, u ∈ Subgroup.normalizer (L : Set Q) → u = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨τ, hτT, hτN, hτ1⟩ := hcon
    set T1 : Subgroup Q := T ⊓ Subgroup.normalizer (L : Set Q) with hT1def
    have hcard : Nat.card T1 ≤ 2 := by
      have hrel := Subgroup.relIndex_mul_card (H := T1) (K := T)
      have hinf : T1 ⊓ T = T1 := inf_eq_left.2 inf_le_left
      rw [hinf] at hrel
      have hr1 : T1.relIndex T ≠ 1 := fun h1 =>
        hTL (fun u hu => (Subgroup.relIndex_eq_one.1 h1 hu).2)
      have hpos : 0 < Nat.card T1 := Nat.card_pos
      have hTpos : 0 < Nat.card T := Nat.card_pos
      have hr0 : T1.relIndex T ≠ 0 := by
        intro h0
        rw [h0] at hrel
        omega
      have hr2 : 2 ≤ T1.relIndex T := by omega
      have := R.T_card
      by_contra hgt
      push Not at hgt
      nlinarith
    have hfix : ∀ a ∈ t113A B L, a * τ = τ * a := by
      intro a ha
      have hu : a * τ * a⁻¹ ∈ T1 := by
        refine ⟨hBT a ha.2 τ hτT, ?_⟩
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha.1 hτN) (Subgroup.inv_mem _ ha.1)
      have hu1 : a * τ * a⁻¹ ≠ 1 := by
        intro h1
        apply hτ1
        calc τ = a⁻¹ * (a * τ * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      by_contra hne'
      have hune : a * τ * a⁻¹ ≠ τ := fun h2 => hne' (by
        calc a * τ = (a * τ * a⁻¹) * a := by group
          _ = τ * a := by rw [h2])
      have h3 : 2 < Nat.card T1 := by
        have := Fintype.ofFinite ↥T1
        rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
        refine ⟨⟨1, T1.one_mem⟩, ⟨τ, ⟨hτT, hτN⟩⟩, ⟨a * τ * a⁻¹, hu⟩, ?_, ?_, ?_⟩
        · intro h; exact hτ1 (congrArg Subtype.val h).symm
        · intro h; exact hu1 (congrArg Subtype.val h).symm
        · intro h; exact hune (congrArg Subtype.val h).symm
      omega
    exact hτ1 (hCT τ hτT hfix)
  have hrel := R.hidx_all (GLBConj t L) (Tr.comp_conj t)
  have hsub : Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B ≤
      t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) := by
    rintro b ⟨hbM, hbB⟩
    have hbM' := mem_normalizer_iff_gLBConj_eq.1 hbM
    have h1 : t * b * t⁻¹ ∈ Subgroup.normalizer (L : Set Q) := by
      rw [mem_normalizer_iff_gLBConj_eq]
      have := congrArg (GLBConj t⁻¹) hbM'
      simpa only [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] using this
    have hτT : t * b * t⁻¹ * b⁻¹ ∈ T := by
      have : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
      rw [this]
      exact T.mul_mem ht (hBT b hbB t⁻¹ (T.inv_mem ht))
    have hτb : (t * b * t⁻¹ * b⁻¹) * b ∈ Subgroup.normalizer (L : Set Q) := by
      have : (t * b * t⁻¹ * b⁻¹) * b = t * b * t⁻¹ := by group
      rw [this]; exact h1
    have hτ1 : t * b * t⁻¹ * b⁻¹ = 1 := by
      by_contra hτ1
      set τ := t * b * t⁻¹ * b⁻¹ with hτ
      have e1 : GLBConj τ L = GLBConj b⁻¹ L := by
        have h2 := mem_normalizer_iff_gLBConj_eq.1 hτb
        rw [← gLBConj_gLBConj] at h2
        have h3 := congrArg (GLBConj b⁻¹) h2
        rwa [gLBConj_inv_gLBConj] at h3
      apply hτ1
      apply hCT τ hτT
      intro a ha
      have hab : a * b⁻¹ = b⁻¹ * a := (Tr.comm_B ha.2 (B.inv_mem hbB))
      have e2 : GLBConj (τ * a) L = GLBConj τ L := by
        rw [← gLBConj_gLBConj, e1, gLBConj_gLBConj, ← hab, ← gLBConj_gLBConj,
          mem_normalizer_iff_gLBConj_eq.1 ha.1]
      have h3 : τ * a * τ⁻¹ ∈ Subgroup.normalizer (L : Set Q) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        have := congrArg (GLBConj τ⁻¹) e2
        simpa only [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] using this
      have h4 : τ * a * τ⁻¹ * a⁻¹ = 1 := by
        refine hT1 _ ?_ (Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ ha.1))
        have : τ * a * τ⁻¹ * a⁻¹ = τ * (a * τ⁻¹ * a⁻¹) := by group
        rw [this]
        exact T.mul_mem hτT (hBT a ha.2 τ⁻¹ (T.inv_mem hτT))
      have h5 : τ * a * τ⁻¹ = a := mul_inv_eq_one.1 h4
      exact (mul_inv_eq_iff_eq_mul.1 h5).symm
    have h5 : t * b * t⁻¹ = b := mul_inv_eq_one.1 hτ1
    refine ⟨⟨?_, hbB⟩, ?_⟩
    · rw [← h5]; exact h1
    · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h5).symm
  have hcardA := Tr.card_A
  have hrelm := Subgroup.relIndex_mul_card
    (H := Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q)) (K := B)
  have hle3 : (Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q)).relIndex B ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hrel
  have hA_le : Nat.card (t113A B L) ≤
      Nat.card ↥(Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B) := by
    have := Nat.mul_le_mul_right
      (Nat.card ↥(Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B)) hle3
    omega
  have hAt_le := Subgroup.card_le_of_le hsub
  have heq : t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) = t113A B L :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_trans hA_le hAt_le)
  have hmem : a0 ∈ t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) := by
    rw [heq]; exact ha0
  exact hne (Subgroup.mem_centralizer_singleton_iff.1 hmem.2)


end ACent

end CFSG.LocalAnalysis.GLTheoremA.I113

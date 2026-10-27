
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin

theorem isSubnormal_map_of_surjective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) {H : Subgroup G} (h : H.IsSubnormal) :
    (H.map f).IsSubnormal := by
  induction h with
  | top =>
    rw [Subgroup.map_top_of_surjective f hf]
    exact Subgroup.IsSubnormal.top
  | step H K hHK hK hN ih =>
    refine Subgroup.IsSubnormal.step (H.map f) (K.map f) (Subgroup.map_mono hHK) ih ?_
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hHK)]
    rintro _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
    refine ⟨k * h * k⁻¹, ?_, by simp⟩
    exact (Subgroup.normal_subgroupOf_iff hHK).1 hN h k hh hk

@[expose] def Chi0Order (t : ℕ) : Prop :=
  t = 3 ∨ ∃ n : ℕ, 2 ≤ n ∧ t = 2 ^ n * (4 ^ n - 1)

theorem chi0_type_data {G : Type*} [Group G] {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 3 ∨ IsAltType B 5) :
    ∃ (A : Type) (_ : Group A) (α : ↥B →* A), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥B ∧
      Nontrivial A ∧ Chi0Order (Nat.card A) := by
  rcases h with ⟨n, hn, F, hF, hFin, hcard, α, hαs, hαk, -⟩ | h3 | h5
  · have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have h42 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ n * (4 ^ n - 1) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq, h42]
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, α, hαs, hαk, ?_,
      Or.inr ⟨n, by omega, hcardSL⟩⟩
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 1 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [hcardSL]
      have h16 : 16 ≤ 4 ^ n := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h15 : 15 ≤ 4 ^ n - 1 := by omega
      calc 1 < 2 ^ n * 15 := by omega
        _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul_left _ h15
    exact Finite.one_lt_card_iff_nontrivial.1 h1
  · obtain ⟨α, hαs, hαk, -⟩ := h3
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
    refine ⟨alternatingGroup (Fin 3), inferInstance, α, hαs, hαk, ?_, Or.inl hc⟩
    exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
    refine ⟨alternatingGroup (Fin 5), inferInstance, α, hαs, hαk, ?_,
      Or.inr ⟨2, le_rfl, by rw [hc]; norm_num⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)

section Quotient

variable {G : Type*} [Group G] {K : Subgroup G} {T : Type*} [Group T] (q : ↥K →* T)

theorem open_pCore_eq (p : ℕ) (H : Type*) [Group H] : CFSG.Open.pCore p H = CFSG.pCore p H :=
  (CFSG.pCore_eq_open H p).symm

theorem le_pCore_of_normal {H : Type*} [Group H] {N : Subgroup H} [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ CFSG.pCore 2 H :=
  le_sSup ⟨inferInstance, hN⟩

theorem pCore_eq_ker_of_quotient (hq : Function.Surjective q) (hT : IsSimpleGroup T)
    (hT2 : ¬ IsPGroup 2 T) (hker : IsPGroup 2 q.ker) : CFSG.pCore 2 ↥K = q.ker := by
  apply le_antisymm
  · have hn : ((CFSG.pCore 2 ↥K).map q).Normal := Subgroup.Normal.map CFSG.pCore_normal q hq
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map q) with h | h
    · intro x hx
      have : q x ∈ (CFSG.pCore 2 ↥K).map q := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hT2
      intro t
      obtain ⟨x, hx, rfl⟩ : t ∈ (CFSG.pCore 2 ↥K).map q := h ▸ Subgroup.mem_top t
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg q (congrArg Subtype.val hk)⟩
  · exact le_pCore_of_normal hker

theorem charTwo_of_quotient (hq : Function.Surjective q) (hT : IsSimpleGroup T)
    (hT2 : ¬ IsPGroup 2 T) (hker : IsPGroup 2 q.ker)
    (hC : ∀ x : ↥K, (∀ n : ↥K, n ∈ q.ker → x * n = n * x) → x ∈ q.ker) : CharTwo K := by
  have hO := pCore_eq_ker_of_quotient q hq hT hT2 hker
  rw [CFSG.QuasithinUnique.charTwo_iff_internal, hO]
  intro x hx
  apply hC
  intro n hn
  have := Subgroup.mem_centralizer_iff.1 hx n (by exact_mod_cast hn)
  exact this.symm

theorem not_hasChi0Block_of_quotient (hq : Function.Surjective q) (hT : IsSimpleGroup T)
    (hker : IsPGroup 2 q.ker) (hord : ¬ Chi0Order (Nat.card T)) : ¬ HasChi0Block K := by
  rintro ⟨B, ⟨hshort, hBK, hsub⟩, htype⟩
  obtain ⟨A, _, α, hαs, hαk, hAnt, hAord⟩ := chi0_type_data htype
  have hsub' : ((B.subgroupOf K).map q).IsSubnormal := isSubnormal_map_of_surjective q hq hsub
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hT hsub' with hbot | htop
  ·
    have hB2 : IsPGroup 2 ↥B := by
      intro b
      have hb : q (Subgroup.inclusion hBK b) = 1 := by
        have : q (Subgroup.inclusion hBK b) ∈ (B.subgroupOf K).map q :=
          ⟨Subgroup.inclusion hBK b, b.2, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      obtain ⟨k, hk⟩ := hker ⟨Subgroup.inclusion hBK b, hb⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun x : ↥q.ker => ((x : ↥K) : G)) hk
      simpa using this
    have hcore : CFSG.pCore 2 ↥B = ⊤ := by
      rw [eq_top_iff]
      refine le_pCore_of_normal (N := (⊤ : Subgroup ↥B)) fun x => ?_
      obtain ⟨k, hk⟩ := hB2 (x : ↥B)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    rw [hcore] at hαk
    have : ∀ y : A, y = 1 := by
      intro y
      obtain ⟨b, rfl⟩ := hαs y
      exact MonoidHom.mem_ker.1 (hαk ▸ Subgroup.mem_top b)
    obtain ⟨y, hy⟩ := exists_ne (1 : A)
    exact hy (this y)
  ·
    set β : ↥B →* T := q.comp (Subgroup.inclusion hBK) with hβ
    have hβs : Function.Surjective β := by
      intro t
      obtain ⟨k, hk, rfl⟩ : t ∈ (B.subgroupOf K).map q := htop ▸ Subgroup.mem_top t
      exact ⟨⟨k, hk⟩, rfl⟩
    have hβ2 : IsPGroup 2 β.ker := by
      intro b
      obtain ⟨k, hk⟩ := hker ⟨Subgroup.inclusion hBK b, b.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun x : ↥q.ker => ((x : ↥K) : G)) hk
      simpa using this
    have hle : β.ker ≤ α.ker := by
      rw [hαk]
      exact le_pCore_of_normal hβ2
    set α' : T →* A := β.liftOfSurjective hβs ⟨α, hle⟩ with hα'
    have hα'β : ∀ b : ↥B, α' (β b) = α b := fun b =>
      MonoidHom.liftOfRightInverse_comp_apply β _ _ ⟨α, hle⟩ b
    have hα's : Function.Surjective α' := by
      intro y
      obtain ⟨b, rfl⟩ := hαs y
      exact ⟨β b, hα'β b⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α'.ker with h | h
    · have hinj : Function.Injective α' := (MonoidHom.ker_eq_bot_iff α').1 h
      have : Nat.card T = Nat.card A := Nat.card_congr (Equiv.ofBijective α' ⟨hinj, hα's⟩)
      exact hord (this ▸ hAord)
    · exfalso
      have : ∀ y : A, y = 1 := by
        intro y
        obtain ⟨t, rfl⟩ := hα's y
        exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top t)
      obtain ⟨y, hy⟩ := exists_ne (1 : A)
      exact hy (this y)

theorem charTwo_not_hasChi0Block_map {S G : Type*} [Group S] [Group G] (ι : S →* G)
    (hι : Function.Injective ι) {P : Subgroup S} {T : Type*} [Group T] (q : ↥P →* T)
    (hq : Function.Surjective q) (hT : IsSimpleGroup T) (hT2 : ¬ IsPGroup 2 T)
    (hker : IsPGroup 2 q.ker)
    (hC : ∀ x : ↥P, (∀ n : ↥P, n ∈ q.ker → x * n = n * x) → x ∈ q.ker)
    (hord : ¬ Chi0Order (Nat.card T)) : CharTwo (P.map ι) ∧ ¬ HasChi0Block (P.map ι) := by
  let e : ↥P ≃* ↥(P.map ι) := P.equivMapOfInjective ι hι
  let q' : ↥(P.map ι) →* T := q.comp e.symm.toMonoidHom
  have hq' : Function.Surjective q' := hq.comp e.symm.surjective
  have hmem : ∀ x : ↥(P.map ι), x ∈ q'.ker ↔ e.symm x ∈ q.ker := fun x => Iff.rfl
  have hker' : IsPGroup 2 q'.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker ⟨e.symm x.1, (hmem x.1).1 x.2⟩
    refine ⟨k, Subtype.ext (e.symm.injective ?_)⟩
    have h1 := congrArg (fun y : ↥q.ker => (y : ↥P)) hk
    simpa using h1
  have hC' : ∀ x : ↥(P.map ι), (∀ n : ↥(P.map ι), n ∈ q'.ker → x * n = n * x) → x ∈ q'.ker := by
    intro x hx
    rw [hmem]
    apply hC
    intro n hn
    have h1 := hx (e n) (by rw [hmem]; simpa using hn)
    apply e.injective
    simpa using h1
  exact ⟨charTwo_of_quotient q' hq' hT hT2 hker' hC',
    not_hasChi0Block_of_quotient q' hq' hT hker' hord⟩

end Quotient

end CFSG.QuasithinUnique.Vol2Native.L239

module

public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem omega1_le_self (H : Subgroup G) : omega1 H ≤ H :=
  (Subgroup.closure_le _).2 fun _ hu => hu.1

theorem isS_self [Finite G] {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) : IsS B B := by
  obtain ⟨hc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  refine ⟨le_rfl, hB, le_antisymm ?_ ?_⟩
  · refine le_omega1_of_isElementaryAbelian hB (le_inf le_rfl ?_)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc'
    exact hc c hc' b hb
  · exact (omega1_mono inf_le_left).trans (omega1_le_self B)

theorem isSn_elementaryAbelian_iff [Finite G] {X : Subgroup G} (hX : CFSG.IsElementaryAbelian 2 ↥X)
    {n : ℕ} (hn : n ≤ pRank 2 ↥X) (B : Subgroup G) : IsSn n X B ↔ B = X := by
  constructor
  · rintro ⟨⟨hBX, hBel, hBeq⟩, -⟩
    obtain ⟨hc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hX
    have h1 : X ⊓ centralizer (B : Set G) = X := by
      refine inf_eq_left.2 fun a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hc b (hBX hb) a ha
    rw [h1] at hBeq
    exact le_antisymm hBX (le_omega1_of_isElementaryAbelian hX le_rfl |>.trans hBeq.ge)
  · rintro rfl
    exact ⟨isS_self hX, hn⟩

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

section L74

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem bt_3c_eq [Finite G] (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {D₀ : Subgroup G}
    (hD₀ : IsDSub K (T ⊓ K) D₀) :
    {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''} = {B'' : Subgroup G | IsSn 4 (D₀ ⊔ (T ⊓ CxK x K)) B''} := by
  have hcen := centerlessBar_of_A7 h7
  have hPQ := h.commDisj hcen
  have hD₀P : D₀ ≤ T ⊓ K := hD₀.1
  have hD₀el : CFSG.IsElementaryAbelian 2 ↥D₀ := hD₀.2.2.1
  have hD₀le : D₀ ⊔ (T ⊓ CxK x K) ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup hD₀P le_rfl
  have hA : ∀ g ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K), (∀ d ∈ D₀, d * g = g * d) →
      g ∈ D₀ ⊔ (T ⊓ CxK x K) := by
    intro g hg hgc
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hPQ.comm hg
    have hpc : ∀ d ∈ D₀, d * p = p * d := by
      intro d hd
      have h1 := hgc d hd
      have h2 : d * p * q = p * d * q := by
        calc d * p * q = d * (p * q) := by group
          _ = p * q * d := h1
          _ = p * (q * d) := by group
          _ = p * (d * q) := by rw [← hPQ.comm d (hD₀P hd) q hq]
          _ = p * d * q := by group
      exact mul_right_cancel h2
    exact Subgroup.mul_mem_sup (isDSub_centralizer h.sylow_P hD₀ p hp hpc) hq
  ext B'
  constructor
  · rintro ⟨⟨⟨hBR, hBel, hBeq⟩, hrk⟩, D, hD, hDB⟩
    have hDeq : D = D₀ := isDSub_unique h.sylow_P hD hD₀
    subst hDeq
    obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
    have hBle : B' ≤ D ⊔ (T ⊓ CxK x K) := fun b hb =>
      hA b (hBR hb) fun d hd => hBc d (hDB hd) b hb
    refine ⟨⟨hBle, hBel, le_antisymm ?_ ?_⟩, hrk⟩
    · refine le_omega1_of_isElementaryAbelian hBel (le_inf hBle ?_)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hBc c hc b hb
    · exact (omega1_mono (inf_le_inf_right _ hD₀le)).trans hBeq.ge
  · rintro ⟨⟨hBle, hBel, hBeq⟩, hrk⟩
    obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
    have hDB : D₀ ≤ B' := by
      have h1 : D₀ ≤ omega1 ((D₀ ⊔ (T ⊓ CxK x K)) ⊓ centralizer (B' : Set G)) := by
        refine le_omega1_of_isElementaryAbelian hD₀el (le_inf le_sup_left ?_)
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨d', hd', q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute
          (fun k hk l hl => hPQ.comm k (hD₀P hk) l hl) (hBle hb)
        have hc1 : d * d' = d' * d := (C3.Layer1.Back.forall_of_isElementaryAbelian hD₀el).1 d hd d' hd'
        calc d' * q * d = d' * (q * d) := by group
          _ = d' * (d * q) := by rw [← hPQ.comm d (hD₀P hd) q hq]
          _ = (d' * d) * q := by group
          _ = (d * d') * q := by rw [hc1]
          _ = d * (d' * q) := by group
      exact h1.trans hBeq.ge
    refine ⟨⟨⟨hBle.trans hD₀le, hBel, le_antisymm ?_ ?_⟩, hrk⟩, D₀, hD₀, hDB⟩
    · refine le_omega1_of_isElementaryAbelian hBel (le_inf (hBle.trans hD₀le) ?_)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hBc c hc b hb
    · refine (Subgroup.closure_le _).2 ?_
      rintro u ⟨⟨huR, huC⟩, hu2⟩
      have huD : u ∈ D₀ ⊔ (T ⊓ CxK x K) := hA u huR fun d hd =>
        Subgroup.mem_centralizer_iff.1 huC d (hDB hd)
      have : u ∈ omega1 ((D₀ ⊔ (T ⊓ CxK x K)) ⊓ centralizer (B' : Set G)) :=
        Subgroup.subset_closure ⟨⟨huD, huC⟩, hu2⟩
      rw [← hBeq] at this
      exact this

theorem b_thm2_l74_A7_of (h3b : B_thm2_A7_3b) : B_thm2_l74_A7 := by
  intro G _ _ hG x y K T S ρ hρ hstd hrow
  rcases hρ with rfl | rfl | rfl
  · obtain ⟨h7, -, h3⟩ := hrow
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_A7 h7)
      (rankTwoShape_sylow_A7 hstd.sylow_P h7) h3).elim
  · obtain ⟨h7, hQ4, hTS⟩ := hrow
    obtain ⟨D₀, hD₀⟩ := exists_isDSub hstd.sylow_P h7
    obtain ⟨hel, hrk⟩ := h3b G hG x y K T S hstd h7 hQ4 hTS D₀ hD₀
    set B₀ : Subgroup G := ⨆ s ∈ S, D₀.map (MulAut.conj s).toMonoidHom with hB₀
    have hBT : ∀ B' : Subgroup G, B' ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
        B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom} ↔ B' = B₀ := by
      intro B'
      constructor
      · rintro ⟨D', hD', rfl⟩
        rw [isDSub_unique hstd.sylow_P hD' hD₀]
      · rintro rfl; exact ⟨D₀, hD₀, rfl⟩
    have hX : (⨆ B' ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
        B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}, B') = B₀ := by
      apply le_antisymm
      · exact iSup₂_le fun B' hB' => ((hBT B').1 hB').le
      · exact le_iSup₂ (f := fun (B : Subgroup G) (_ :
          B ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
            B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}) => B) B₀ ((hBT B₀).2 rfl)
    show {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
        B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom} =
      {B' : Subgroup G | IsSn 4 (⨆ B ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
        B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}, B) B'}
    rw [hX]
    ext B'
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, isSn_elementaryAbelian_iff hel hrk]
    exact hBT B'
  · obtain ⟨h7, -⟩ := hrow
    obtain ⟨D₀, hD₀⟩ := exists_isDSub hstd.sylow_P h7
    show {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
        ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''} =
      {B' : Subgroup G | IsSn 4 (⨆ B ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
        ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}, B) B'}
    rw [bt_3c_eq hstd h7 hD₀]
    exact isSn_tstar_eq _ 4

end L74

end CFSG.GH74.GLS

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFRel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD5
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Wt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE


variable {n : ℕ}

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem frame_prod_of_exit {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ : Subgroup Y}
    (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄) {M : Fin 4 → Subgroup Y}
    (hinj : Function.Injective M) (hmem : ∀ i, M i ∈ twinSet Ω[R] K)
    (hsurj : ∀ J ∈ twinSet Ω[R] K, ∃ i, M i = J) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet Ω[R]) (htW₁ : t ∈ W₁)
    {Sm : Subgroup Y} {zS : Y} (hSΩ : Sm ∈ Ω[R])
    (hSD : Sm ∈ DSet Ω[R] W₁) (hSz : IsUniqueInvolution Sm zS)
    (hSne : Sm ≠ M 0) (hSnot : M 0 ∉ omegaNbr Ω[R] Sm) {w : Y}
    (hw : w ∈ Sm ⊓ W₁) (hw2 : w * w = zS) :
    ∃ k : Fin 4 → Y, (∀ i, k i ∈ M i ⊓ W₁ ∧ k i * k i = t) ∧ k 0 * k 1 * k 2 * k 3 = zS := by
  have hStd := hin.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have c : Q3CL.Thompson.Ctx Ω[R] W₁ := Q3CL.T8.ctxOf hP hW₁
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := hin.2.2.2.1
  have huniq : ∀ i, IsUniqueInvolution (M i) t := fun i =>
    Asc77.isUniqueInvolution_of_mem_twinSet hd.hz (hmem i)
  have hMD : ∀ l, M l ∈ DSet Ω[R] W₁ := fun l =>
    twin_mem_DSet hP h2g hW₁ htW₁ (hmem l).1 (huniq l)
  have hMsyl : ∀ l, IsSylow2In (M l) (M l) := fun l =>
    ⟨le_rfl, h2g _ (hmem l).1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hSsyl : IsSylow2In Sm Sm := ⟨le_rfl, h2g _ hSΩ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Fin 4 → Asc77.Thompson.Rep Ω[R] W₁, ∀ i, (ρ i).K = M i :=
    ⟨fun i => Q3CL.T8.mkRep hP hW₁ (hmem i).1 (hMD i) (hMsyl i), fun i => rfl⟩
  obtain ⟨ρS, hρSK⟩ : ∃ ρS : Asc77.Thompson.Rep Ω[R] W₁, ρS.K = Sm :=
    ⟨Q3CL.T8.mkRep hP hW₁ hSΩ hSD hSsyl, rfl⟩
  have hperp : ∀ i, KPerp Ω[R] (M i) = twinSet Ω[R] (M i) := fun i =>
    kPerp_datum hStd.perp (hmem i).1 (huniq i)
  have hnbrM : ∀ i j, i ≠ j → M j ∈ omegaNbr Ω[R] (M i) := by
    intro i j hij
    have hmem' : M j ∈ KPerp Ω[R] (M i) := by
      rw [hperp i]
      exact ⟨(hmem j).1, t, huniq i, huniq j⟩
    exact hmem'.resolve_left (fun e => hij (hinj e).symm)
  have hnc : ¬ DbarConnected Ω[R] W₁ := by
    obtain ⟨j₀, hj₀⟩ := hsurj K (mem_twinSet_self hd.mem hd.hz)
    exact not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) hW₁ (ρ j₀)
      ((hρK j₀).trans hj₀) (hStd.wyl W₁ hW₁)
  have hTT := Q3T6.Mu.isTT_muDelta hP hW₁
  have hS := Q3T6.Mu.isStar_muDelta c
  have hmu_ne : ∀ i j, i ≠ j →
      Asc77.MuTab.muTabElt (ρ i) ≠ Asc77.MuTab.muTabElt (ρ j) := fun i j hij e =>
    hij (hinj (by
      rw [← hρK i, ← hρK j]; exact (Q3T6.Mu.muTabElt_eq_iff hP hW₁ _ _).mp e))
  have hmu_comm : ∀ i j, i ≠ j → Asc77.MuTab.muTabElt (ρ i) * Asc77.MuTab.muTabElt (ρ j) =
      Asc77.MuTab.muTabElt (ρ j) * Asc77.MuTab.muTabElt (ρ i) := fun i j hij =>
    (Q3T6.Mu.muTab_commute_iff hP hW₁ (ρ i) (ρ j) (by
      rw [hρK i, hρK j]; exact fun e => hij (hinj e))).mpr
      (by rw [hρK i, hρK j]; exact hnbrM i j hij)
  obtain ⟨a', ha'Δ, hconna'⟩ :=
    Q3T6.Mu.exists_not_conn_at hP hW₁ hnc (Asc77.MuTab.muTabElt (ρ 0))
  have hxa := Asc77.MuTab.muTabElt_mem (ρ 0)
  have hyF : Asc77.MuTab.muTabElt ρS ∉
      Asc77.Star3T.cent (muDelta Ω[R] W₁) (Asc77.MuTab.muTabElt (ρ 0)) := by
    rintro ⟨-, hx⟩
    exact c.noncomm ρS (ρ 0) (by rw [hρSK, hρK 0]; exact hSne)
      (by rw [hρSK, hρK 0]; exact hSnot) (congrArg Subtype.val hx)
  have hconn : ¬ Asc77.Star3T.Conn (muDelta Ω[R] W₁)
      (Asc77.MuTab.muTabElt (ρ 0)) (Asc77.MuTab.muTabElt ρS) :=
    TwinMu.not_conn_of_not_mem_cent hTT hS hxa ha'Δ hconna' hyF
  obtain ⟨ρd, zd, hF4, hzd, -, -, ka, kb, kc, kd, hka, hkb, hkc, hkd, hka2, hkb2, hkc2, hkd2, -, -,
    -, -, hprod⟩ :=
    TwinMu.frame_prod hP hW₁ (hmu_ne 0 1 (by decide)) (hmu_ne 0 2 (by decide))
      (hmu_ne 1 2 (by decide)) (hmu_comm 0 1 (by decide)) (hmu_comm 0 2 (by decide))
      (hmu_comm 1 2 (by decide)) hconn (w := w) (zS := zS) (za := t) (zb := t) (zc := t)
      (by rw [hρSK]; exact hw) (by rw [hρSK]; exact hSz) hw2
      (by rw [hρK 0]; exact huniq 0) (by rw [hρK 1]; exact huniq 1)
      (by rw [hρK 2]; exact huniq 2)
  have hρdJ : ∃ l, M l = ρd.K := by
    have h1 : ρd.K ∈ omegaNbr Ω[R] (M 0) := by
      have := hF4.ad
      rwa [hρK 0] at this
    have h2 : ρd.K ∈ twinSet Ω[R] (M 0) := by
      rw [← hperp 0]; exact Set.mem_insert_of_mem _ h1
    have h2' : ρd.K ∈ twinSet Ω[R] K := by
      rw [← twinSet_eq_of_mem_twinSet hd.hz (hmem 0)]; exact h2
    exact hsurj _ h2'
  obtain ⟨l, hl⟩ := hρdJ
  have hl0 : l ≠ 0 := fun e => (hF4.ad.2.1) (by rw [← hl, e, hρK 0])
  have hl1 : l ≠ 1 := fun e => (hF4.bd.2.1) (by rw [← hl, e, hρK 1])
  have hl2 : l ≠ 2 := fun e => (hF4.cd.2.1) (by rw [← hl, e, hρK 2])
  have hl3 : l = 3 := by
    have key : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → l ≠ 2 → l = 3 := by decide
    exact key l hl0 hl1 hl2
  subst hl3
  have hzdt : zd = t := hzd.eq (by rw [← hl]; exact huniq 3)
  rw [hzdt] at hkd2
  rw [hρK 0] at hka
  rw [hρK 1] at hkb
  rw [hρK 2] at hkc
  rw [← hl] at hkd
  refine ⟨![ka, kb, kc, kd], ?_, hprod⟩
  intro i
  fin_cases i
  exacts [⟨hka, hka2⟩, ⟨hkb, hkb2⟩, ⟨hkc, hkc2⟩, ⟨hkd, hkd2⟩]

theorem prod4_of_cases {G : Type*} [Group G] {t a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : G} (htt : t * t = 1)
    (h₀ : a₀ * t = t * a₀) (h₁ : a₁ * t = t * a₁) (h₂ : a₂ * t = t * a₂) (h₃ : a₃ * t = t * a₃)
    (e₀ : b₀ = a₀ ∨ b₀ = a₀ * t) (e₁ : b₁ = a₁ ∨ b₁ = a₁ * t) (e₂ : b₂ = a₂ ∨ b₂ = a₂ * t)
    (e₃ : b₃ = a₃ ∨ b₃ = a₃ * t) :
    b₀ * b₁ * b₂ * b₃ = a₀ * a₁ * a₂ * a₃ ∨ b₀ * b₁ * b₂ * b₃ = t * (a₀ * a₁ * a₂ * a₃) := by
  have c₀ : ∀ X : G, a₀ * (t * X) = t * (a₀ * X) := fun X => by rw [← mul_assoc, h₀, mul_assoc]
  have c₁ : ∀ X : G, a₁ * (t * X) = t * (a₁ * X) := fun X => by rw [← mul_assoc, h₁, mul_assoc]
  have c₂ : ∀ X : G, a₂ * (t * X) = t * (a₂ * X) := fun X => by rw [← mul_assoc, h₂, mul_assoc]
  have tt : ∀ X : G, t * (t * X) = X := fun X => by rw [← mul_assoc, htt, one_mul]
  rcases e₀ with rfl | rfl <;> rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl <;>
    rcases e₃ with rfl | rfl <;> simp only [mul_assoc, h₃, c₀, c₁, c₂, tt, true_or, or_true]

theorem mem_tG_W {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    {w : Y} (hwW : w ∈ W) {g : Y} (hg : g * t * g⁻¹ = w) :
    w = t ∨ w = y * t * y⁻¹ ∨ w = t * (y * t * y⁻¹) := by
  have hStd := H.ex.1
  have hF := H.ex.2.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have hP := hC.partIHypG
  have hQ8 := A6Gen.q8Omega_of_hyp H
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  have htt : t * t = 1 := hd.hz.sq
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W H.hW) fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨S₀, hWS₀, hWC, -⟩ := A6Gen.exists_weaklyClosed_conj_of_nonab hP htr H.hW hnab
  have hWab : ∀ {v : Y}, v ∈ W → v ∈ Subgroup.centralizer (W : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp H.hW x hx _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab htW) (g := g) (by rw [hg]; exact hWab hwW)
  rw [hg] at hm
  set J := conjSub m K with hJdef
  have hJΩ : J ∈ Ω[R] := hΩ.conjInvariant m K hd.mem
  have hJz : IsUniqueInvolution J w := by
    have := A6jB.isUniqueInvolution_conjSub hd.hz m
    rwa [hm] at this
  have hJD : J ∈ DSet Ω[R] W := by
    have := hQ8.conjSub_mem_DSet H.hK m
    rwa [mem_normalizer_iff_conjSub_eq.mp hmN] at this
  by_cases htw : J ∈ twinSet Ω[R] K
  · left
    exact (hJz.eq (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz htw))
  right
  set M : Fin 4 → Subgroup Y := ![K, K', K₃, K₄] with hM
  have hmemM : ∀ i, M i ∈ twinSet Ω[R] K := by
    intro i
    fin_cases i
    exacts [mem_twinSet_self hd.mem hd.hz, hd.hK', hd.hK₃, hF.1]
  have hinj : Function.Injective M := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hM] at hij ⊢ <;>
      first
      | exact (hd.hne hij.symm).elim
      | exact (hd.hne hij).elim
      | exact (hd.hK₃K hij.symm).elim
      | exact (hd.hK₃K hij).elim
      | exact (hd.hK₃K' hij.symm).elim
      | exact (hd.hK₃K' hij).elim
      | exact (hF.2.1 hij.symm).elim
      | exact (hF.2.1 hij).elim
      | exact (hF.2.2.1 hij.symm).elim
      | exact (hF.2.2.1 hij).elim
      | exact (hF.2.2.2.1 hij.symm).elim
      | exact (hF.2.2.2.1 hij).elim
  have hsurj : ∀ L ∈ twinSet Ω[R] K, ∃ i, M i = L := by
    intro L hL
    rcases twinSet_four hStd hF L hL with h | h | h | h
    exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩, ⟨3, h.symm⟩]
  have hJne : J ≠ M 0 := fun e => htw (by rw [e]; exact hmemM 0)
  have hJnot : M 0 ∉ omegaNbr Ω[R] J := by
    intro hnb
    have h1 := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJΩ hd.mem hnb
    have h2 : J ∈ KPerp Ω[R] K := Set.mem_insert_of_mem _ h1
    rw [kPerp_datum hStd.perp hd.mem hd.hz] at h2
    exact htw h2
  obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g J hJΩ
  obtain ⟨v, hvJ, hvW, hvv⟩ := WF.exists_gen_sq hΩ H.hW hJΩ hJD (h2g J hJΩ) (WF.q8Facts_of_iso hJz e)
  obtain ⟨k, hk, hprod⟩ := frame_prod_of_exit H.ex hinj hmemM hsurj H.hW htW hJΩ hJD hJz hJne
    hJnot ⟨hvJ, hvW⟩ hvv
  have hcyc : ∀ {L : Subgroup Y}, L ∈ DSet Ω[R] W → L ∈ Ω[R] → IsCyclic ↥(L ⊓ W) := fun hLD hL =>
    (Q3CL.Thompson.inf_W_of_mem_D hd.hyp H.hW hLD hL
      ⟨le_rfl, h2g _ hL, fun _ hV' _ h => le_antisymm hV' h⟩).2.2.1
  have hMD : ∀ i, M i ∈ DSet Ω[R] W := fun i =>
    twin_mem_DSet hP h2g H.hW htW (hmemM i).1 (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz (hmemM i))
  have hord4 : ∀ i, orderOf (k i) = 4 := by
    intro i
    have hk2 : k i ^ 2 = t := by rw [sq]; exact (hk i).2
    have hne : ¬ k i ^ 2 ^ 1 = 1 := by
      rw [pow_one, hk2]; exact hd.hz.ne_one
    have hfin : k i ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hk2, sq, htt]
    exact orderOf_eq_prime_pow hne hfin
  have ha : ∀ i, ![a₁, a₂, a₃, a₄] i ∈ M i ⊓ W ∧ orderOf (![a₁, a₂, a₃, a₄] i) = 4 := by
    intro i
    fin_cases i
    exacts [⟨fr.h₁, fr.o₁⟩, ⟨fr.h₂, fr.o₂⟩, ⟨fr.h₃, fr.o₃⟩, ⟨fr.h₄, fr.o₄⟩]
  have hsq : ∀ i, ![a₁, a₂, a₃, a₄] i * ![a₁, a₂, a₃, a₄] i = t := fun i =>
    Asc77.sq_eq_of_orderOf_four (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz (hmemM i))
      (ha i).1.1 (ha i).2
  have hcase : ∀ i, k i = ![a₁, a₂, a₃, a₄] i ∨ k i = ![a₁, a₂, a₃, a₄] i * t := by
    intro i
    rcases Asc77.eq_or_eq_inv_of_orderOf_four_of_cyclic (hcyc (hMD i) (hmemM i).1) (ha i).1 (hk i).1
      (ha i).2 (hord4 i) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h]
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, hsq i, htt]
  have hcomm : ∀ i, ![a₁, a₂, a₃, a₄] i * t = t * ![a₁, a₂, a₃, a₄] i := by
    intro i
    rw [← hsq i, mul_assoc]
  have hτ : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄ := fr.hy
  rcases prod4_of_cases htt (hcomm 0) (hcomm 1) (hcomm 2) (hcomm 3) (hcase 0) (hcase 1) (hcase 2)
    (hcase 3) with h | h
  · left
    rw [← hprod, hτ]
    simpa using h
  · right
    rw [← hprod, hτ]
    simpa using h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Wt

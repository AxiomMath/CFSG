module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFRel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFB0Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WAe5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD5
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Th.Max3.Packet

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section FrameRel

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem frame_relOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {M : Fin 4 → Subgroup Y}
    (hMinj : Function.Injective M) (hMmem : ∀ i, M i ∈ twinSet Ω[R] K)
    (hMsurj : ∀ J ∈ twinSet Ω[R] K, ∃ i, M i = J) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet Ω[R]) (htW₁ : t ∈ W₁)
    {Sm : Subgroup Y} {zS : Y} (hSΩ : Sm ∈ Ω[R])
    (hSD : Sm ∈ DSet Ω[R] W₁) (hSz : IsUniqueInvolution Sm zS)
    (hSne : Sm ≠ M 0) (hSnot : M 0 ∉ omegaNbr Ω[R] Sm) {w : Y}
    (hw : w ∈ Sm ⊓ W₁) (hw2 : w * w = zS) :
    ∃ k : Fin 4 → Y, (∀ i, k i ∈ M i ⊓ W₁ ∧ k i * k i = t) ∧ k 0 * k 1 * k 2 * k 3 = zS ∧
      ∀ i, ∀ v ∈ M i, v ∉ W₁ → v * w * v⁻¹ = k i * w := by
  have hP := (partIOf H)
  have c : Q3CL.Thompson.Ctx Ω[R] W₁ := Q3CL.T8.ctxOf hP hW₁
  have h2g := (h2gOf H)
  have hd := (stdOf H).datum
  have hMD : ∀ l, M l ∈ DSet Ω[R] W₁ := fun l =>
    twin_mem_DSet hP h2g hW₁ htW₁ (hMmem l).1 ((uniqInvOf H) (hMmem l))
  have hMsyl : ∀ l, IsSylow2In (M l) (M l) := fun l =>
    ⟨le_rfl, h2g _ (hMmem l).1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hSsyl : IsSylow2In Sm Sm := ⟨le_rfl, h2g _ hSΩ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Fin 4 → Asc77.Thompson.Rep Ω[R] W₁,
      ∀ i, (ρ i).K = M i :=
    ⟨fun i => Q3CL.T8.mkRep hP hW₁ (hMmem i).1 (hMD i) (hMsyl i), fun i => rfl⟩
  obtain ⟨ρS, hρSK⟩ : ∃ ρS : Asc77.Thompson.Rep Ω[R] W₁,
      ρS.K = Sm := ⟨Q3CL.T8.mkRep hP hW₁ hSΩ hSD hSsyl, rfl⟩
  have hperp : ∀ i, KPerp Ω[R] (M i) =
      twinSet Ω[R] (M i) := fun i =>
    kPerp_datum (stdOf H).perp (hMmem i).1 ((uniqInvOf H) (hMmem i))
  have hnbrM : ∀ i j, i ≠ j → M j ∈ omegaNbr Ω[R] (M i) := by
    intro i j hij
    have hmem : M j ∈ KPerp Ω[R] (M i) := by
      rw [hperp i]
      exact ⟨(hMmem j).1, t, (uniqInvOf H) (hMmem i), (uniqInvOf H) (hMmem j)⟩
    exact hmem.resolve_left (fun e => hij (hMinj e).symm)
  have hnc : ¬ DbarConnected Ω[R] W₁ := by
    obtain ⟨j₀, hj₀⟩ := hMsurj K (mem_twinSet_self hd.mem hd.hz)
    exact not_dbarConnected_of_wyl' hP hd (kPerp_datum (stdOf H).perp hd.mem hd.hz) hW₁ (ρ j₀)
      ((hρK j₀).trans hj₀) ((stdOf H).wyl W₁ hW₁)
  have hTT := Q3T6.Mu.isTT_muDelta hP hW₁
  have hS := Q3T6.Mu.isStar_muDelta c
  have hmu_ne : ∀ i j, i ≠ j →
      Asc77.MuTab.muTabElt (ρ i) ≠ Asc77.MuTab.muTabElt (ρ j) := fun i j hij e =>
    hij (hMinj (by
      rw [← hρK i, ← hρK j]; exact (Q3T6.Mu.muTabElt_eq_iff hP hW₁ _ _).mp e))
  have hmu_comm : ∀ i j, i ≠ j → Asc77.MuTab.muTabElt (ρ i) * Asc77.MuTab.muTabElt (ρ j) =
      Asc77.MuTab.muTabElt (ρ j) * Asc77.MuTab.muTabElt (ρ i) := fun i j hij =>
    (Q3T6.Mu.muTab_commute_iff hP hW₁ (ρ i) (ρ j) (by
      rw [hρK i, hρK j]; exact fun e => hij (hMinj e))).mpr
      (by rw [hρK i, hρK j]; exact hnbrM i j hij)
  obtain ⟨a', ha'Δ, hconna'⟩ :=
    Q3T6.Mu.exists_not_conn_at hP hW₁ hnc (Asc77.MuTab.muTabElt (ρ 0))
  have hxa := Asc77.MuTab.muTabElt_mem (ρ 0)
  have hyF : Asc77.MuTab.muTabElt ρS ∉
      Asc77.Star3T.cent (muDelta Ω[R] W₁)
        (Asc77.MuTab.muTabElt (ρ 0)) := by
    rintro ⟨-, hx⟩
    exact c.noncomm ρS (ρ 0) (by rw [hρSK, hρK 0]; exact hSne)
      (by rw [hρSK, hρK 0]; exact hSnot) (congrArg Subtype.val hx)
  have hconn : ¬ Asc77.Star3T.Conn (muDelta Ω[R] W₁)
      (Asc77.MuTab.muTabElt (ρ 0)) (Asc77.MuTab.muTabElt ρS) :=
    TwinMu.not_conn_of_not_mem_cent hTT hS hxa ha'Δ hconna' hyF
  obtain ⟨ρd, zd, hF4, hzd, -, -, ka, kb, kc, kd, hka, hkb, hkc, hkd, hka2, hkb2, hkc2, hkd2, hra, hrb,
    hrc, hrd, hprod⟩ :=
    TwinMu.frame_prod hP hW₁ (hmu_ne 0 1 (by decide)) (hmu_ne 0 2 (by decide))
      (hmu_ne 1 2 (by decide)) (hmu_comm 0 1 (by decide)) (hmu_comm 0 2 (by decide))
      (hmu_comm 1 2 (by decide)) hconn (w := w) (zS := zS) (za := t) (zb := t) (zc := t)
      (by rw [hρSK]; exact hw) (by rw [hρSK]; exact hSz) hw2
      (by rw [hρK 0]; exact (uniqInvOf H) (hMmem 0)) (by rw [hρK 1]; exact (uniqInvOf H) (hMmem 1))
      (by rw [hρK 2]; exact (uniqInvOf H) (hMmem 2))
  have hρdJ : ∃ l, M l = ρd.K := by
    have h1 : ρd.K ∈ omegaNbr Ω[R] (M 0) := by
      have := hF4.ad
      rwa [hρK 0] at this
    have h2 : ρd.K ∈ twinSet Ω[R] (M 0) := by
      rw [← hperp 0]; exact Set.mem_insert_of_mem _ h1
    have h2' : ρd.K ∈ twinSet Ω[R] K := by
      rw [← twinSet_eq_of_mem_twinSet hd.hz (hMmem 0)]; exact h2
    exact hMsurj _ h2'
  obtain ⟨l, hl⟩ := hρdJ
  have hl0 : l ≠ 0 := fun e => (hF4.ad.2.1) (by rw [← hl, e, hρK 0])
  have hl1 : l ≠ 1 := fun e => (hF4.bd.2.1) (by rw [← hl, e, hρK 1])
  have hl2 : l ≠ 2 := fun e => (hF4.cd.2.1) (by rw [← hl, e, hρK 2])
  have hl3 : l = 3 := by
    have key : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → l ≠ 2 → l = 3 := by decide
    exact key l hl0 hl1 hl2
  subst hl3
  have hzdt : zd = t := hzd.eq (by rw [← hl]; exact (uniqInvOf H) (hMmem 3))
  rw [hzdt] at hkd2
  rw [hρK 0] at hka
  rw [hρK 1] at hkb
  rw [hρK 2] at hkc
  rw [← hl] at hkd
  have hactM : ∀ (i : Fin 4) (v r : Y), v ∈ M i → r ∈ M i → v ∉ W₁ → r ∉ W₁ →
      v * w * v⁻¹ = r * w * r⁻¹ := fun i v r hv hr hvW hrW =>
    WF.act_indep (hypOf H) hW₁ (hMD i) hv hr hvW hrW hw.2
  refine ⟨![ka, kb, kc, kd], ?_, hprod, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨hka, hka2⟩, ⟨hkb, hkb2⟩, ⟨hkc, hkc2⟩, ⟨hkd, hkd2⟩]
  · intro i v hv hvW
    fin_cases i
    · show v * w * v⁻¹ = ka * w
      rw [hactM 0 v (ρ 0).r hv (by rw [← hρK 0]; exact (ρ 0).hRK.1 (ρ 0).hr) hvW (ρ 0).hrW]
      exact hra
    · show v * w * v⁻¹ = kb * w
      rw [hactM 1 v (ρ 1).r hv (by rw [← hρK 1]; exact (ρ 1).hRK.1 (ρ 1).hr) hvW (ρ 1).hrW]
      exact hrb
    · show v * w * v⁻¹ = kc * w
      rw [hactM 2 v (ρ 2).r hv (by rw [← hρK 2]; exact (ρ 2).hRK.1 (ρ 2).hr) hvW (ρ 2).hrW]
      exact hrc
    · show v * w * v⁻¹ = kd * w
      rw [hactM 3 v ρd.r hv (by rw [hl]; exact ρd.hRK.1 ρd.hr) hvW ρd.hrW]
      exact hrd



theorem Mfr_inj (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    Function.Injective (![K, K', K₃, K₄] : Fin 4 → Subgroup Y) := by
  have h1 := neKPKOf H
  have h2 := neK₃KOf H
  have h3 := neK₃KPOf H
  have h4 := neK₄KOf H
  have h5 := neK₄KPOf H
  have h6 := neK₄K₃Of H
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm, h5,
    h5.symm, h6, h6.symm] at hij ⊢

theorem Mfr_mem (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∀ i, (![K, K', K₃, K₄] : Fin 4 → Subgroup Y) i ∈ twinSet Ω[R] K := by
  intro i
  fin_cases i
  · exact memKOf H
  · exact memKPOf H
  · exact memK₃Of H
  · exact memK₄Of H

theorem Mfr_surj (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∀ J ∈ twinSet Ω[R] K, ∃ i, (![K, K', K₃, K₄] : Fin 4 → Subgroup Y) i = J := by
  intro J hJ
  rcases twinSet_four (stdOf H) (fourthOf H) J hJ with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem frame_fn {a₁ a₂ a₃ a₄ y : Y} (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∀ i, (![a₁, a₂, a₃, a₄] : Fin 4 → Y) i ∈ (![K, K', K₃, K₄] : Fin 4 → Subgroup Y) i ⊓ W ∧
      (![a₁, a₂, a₃, a₄] : Fin 4 → Y) i * (![a₁, a₂, a₃, a₄] : Fin 4 → Y) i = t := by
  intro i
  fin_cases i
  · exact ⟨fr.h₁, Asc77.sq_eq_of_orderOf_four (uniqInvOf H (memKOf H)) fr.h₁.1 fr.o₁⟩
  · exact ⟨fr.h₂, Asc77.sq_eq_of_orderOf_four (uniqInvOf H (memKPOf H)) fr.h₂.1 fr.o₂⟩
  · exact ⟨fr.h₃, Asc77.sq_eq_of_orderOf_four (uniqInvOf H (memK₃Of H)) fr.h₃.1 fr.o₃⟩
  · exact ⟨fr.h₄, Asc77.sq_eq_of_orderOf_four (uniqInvOf H (memK₄Of H)) fr.h₄.1 fr.o₄⟩

theorem inv_trich {a₁ a₂ a₃ a₄ y : Y} (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Sm : Subgroup Y} {zS : Y}
    (hSΩ : Sm ∈ Ω[R]) (hSD : Sm ∈ DSet Ω[R] W) (hSz : IsUniqueInvolution Sm zS) :
    zS = t ∨ zS = a₁ * a₂ * a₃ * a₄ ∨ zS = a₁ * a₂ * a₃ * a₄ * t := by
  by_cases hSK : Sm = K
  · left
    subst hSK
    exact hSz.eq (uniqInvOf H (memKOf H))
  by_cases hnb : K ∈ omegaNbr Ω[R] Sm
  · left
    have hsymm : Sm ∈ omegaNbr Ω[R] K :=
      Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen (hypOf H) hSΩ (memKOf H).1 hnb
    have hperp := kPerp_datum (stdOf H).perp (stdOf H).datum.mem (stdOf H).datum.hz
    have hSK' : Sm ∈ twinSet Ω[R] K := by
      rw [← hperp]
      exact Set.mem_insert_of_mem _ hsymm
    exact hSz.eq (uniqInvOf H hSK')
  · right
    have hSsyl : IsSylow2In Sm Sm :=
      ⟨le_rfl, h2gOf H Sm hSΩ, fun V' hV' _ hKV' => le_antisymm hV' hKV'⟩
    have hinf := Q3CL.Thompson.inf_W_of_mem_D (hypOf H) H.hW hSD hSΩ hSsyl
    obtain ⟨w, hwmem, hw4⟩ := Asc77.AscL62.exists_orderOf_four_of_cyclic hinf.2.2.1
      (Thompson.isPGroup_of_mem_WSet H.hW).to_inf_right hinf.2.2.2.1
    have hw2 : w * w = zS := Asc77.sq_eq_of_orderOf_four hSz hwmem.1 hw4
    obtain ⟨k, hk, hprod, -⟩ := frame_relOf H (Mfr_inj H) (Mfr_mem H) (Mfr_surj H) H.hW (tmemOf H)
      hSΩ hSD hSz hSK hnb hwmem hw2
    have hkb : ∀ i, k i = (![a₁, a₂, a₃, a₄] : Fin 4 → Y) i ∨
        k i = (![a₁, a₂, a₃, a₄] : Fin 4 → Y) i * t := by
      intro i
      exact eq_or_mul_t_of_comm (q8Of H (Mfr_mem H i)) (frame_fn H fr i).1.1 (hk i).1.1
        (frame_fn H fr i).2 (hk i).2
        (abelianOf H _ (frame_fn H fr i).1.2 _ (hk i).1.2)
    have := WF.prod4_twist (b := ![a₁, a₂, a₃, a₄]) (b' := k) (stdOf H).datum.hz.sq
      (fun i => (q8Of H (Mfr_mem H i)).z_central _ (frame_fn H fr i).1.1) hkb
    rw [hprod] at this
    simpa using this

end FrameRel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

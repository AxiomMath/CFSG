module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Model
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverMain
public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverModel

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift (E8Datum)
open CFSG.Sporadic.Recognition.CoverTransfer (sq_eq_sq_of_conj)


section Lifts


theorem fixCard_coverXPerm : fixCard coverXPerm = 170 := by
  have h := (s6Fix_parts.2)
  simp only [s6FixCoverOK, Bool.and_eq_true, beq_iff_eq] at h
  rw [← fixTbl_eq rep_coverX]
  exact h.1

theorem fixCard_hsC : fixCard CFSG.QuasithinUnique.Id2519.UHS.hsC = 30 := by
  have h := (s6Fix_parts.2)
  simp only [s6FixCoverOK, Bool.and_eq_true, beq_iff_eq] at h
  have hw : ∀ l ∈ s6CWord, l = 0 ∨ l = 1 := by decide
  have hr := rep_coverWord hw
  have hc : CFSG.Sporadic.Th.wordG coverGenPerm s6CWord =
      CFSG.QuasithinUnique.Id2519.UHS.hsC := by
    simp [CFSG.Sporadic.Th.wordG, coverGenPerm, s6CWord, CFSG.QuasithinUnique.Id2519.UHS.hsC,
      pow_succ, mul_assoc]
  rw [← hc, ← fixTbl_eq hr]
  exact h.2

end Lifts

section Cover

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem exists_center_gen (hZ : Nat.card (center L) = 2) :
    ∃ t : L, t ∈ center L ∧ t ≠ 1 ∧ ∀ c ∈ center L, c = 1 ∨ c = t := by
  obtain ⟨t, ht1, htu⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hZ
  refine ⟨t, t.2, fun h => ht1 (Subtype.ext h), fun c hc => ?_⟩
  by_cases h : (⟨c, hc⟩ : center L) = 1
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val (htu _ h))

omit [Finite L] in
theorem sq_of_mem_ker {q : L →* ↥hsP} (hker : q.ker = center L) (hZ : Nat.card (center L) = 2) :
    ∀ c ∈ q.ker, c ^ 2 = 1 := by
  intro c hc
  rw [hker] at hc
  have h2 : orderOf (⟨c, hc⟩ : center L) ∣ 2 := hZ ▸ orderOf_dvd_natCard _
  simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h2)


theorem coverE8Datum_P :
    E8Datum (⟨coverXPerm, coverXPerm_mem⟩ : ↥hsP)
      (⟨coverNPerm, coverNPerm_mem⟩ * ⟨coverXPerm, coverXPerm_mem⟩ *
        ⟨coverNPerm, coverNPerm_mem⟩⁻¹)
      (⟨coverNPerm, coverNPerm_mem⟩ * (⟨coverNPerm, coverNPerm_mem⟩ *
        ⟨coverXPerm, coverXPerm_mem⟩ * ⟨coverNPerm, coverNPerm_mem⟩⁻¹) *
        ⟨coverNPerm, coverNPerm_mem⟩⁻¹) ⟨coverNPerm, coverNPerm_mem⟩ :=
  E8Datum.of_map hsP.subtype Subtype.val_injective coverE8Datum

theorem conj_of_perm_conj {a b : ↥hsP} {g₁ g₂ r : Equiv.Perm (Fin 3850)} (hg₁ : g₁ ∈ hsP)
    (hg₂ : g₂ ∈ hsP) (h₁ : (a : Equiv.Perm (Fin 3850)) = g₁ * r * g₁⁻¹)
    (h₂ : (b : Equiv.Perm (Fin 3850)) = g₂ * r * g₂⁻¹) :
    ∃ h : ↥hsP, a = h * b * h⁻¹ :=
  ⟨⟨g₁ * g₂⁻¹, hsP.mul_mem hg₁ (hsP.inv_mem hg₂)⟩, Subtype.ext (by
    show (a : Equiv.Perm (Fin 3850)) = g₁ * g₂⁻¹ * (b : Equiv.Perm (Fin 3850)) * (g₁ * g₂⁻¹)⁻¹
    rw [h₁, h₂]
    group)⟩

omit [Finite L] in
theorem sq_of_fixCard_170 {q : L →* ↥hsP}
    (hq : Function.Surjective q) (hker : q.ker = center L) (hZ : Nat.card (center L) = 2)
    {τ : ↥hsP} (hτ : orderOf τ = 2) (hf : fixCard (τ : Equiv.Perm (Fin 3850)) = 170) :
    ∀ l : L, q l = τ → l * l = 1 := by
  intro l hl
  obtain ⟨b₁, -, -, hb₁, -, -, hb₁sq, -⟩ := coverE8Datum_P.exists_lift (φ := q) hq hker.le
  have hxsq : coverXPerm ^ 2 = 1 := by
    have := congrArg Subtype.val coverE8Datum_P.sq
    simpa using this
  have hx1 : coverXPerm ≠ 1 := fun h => coverE8Datum_P.ne_one (Subtype.ext h)
  have hx2 : orderOf coverXPerm = 2 := orderOf_eq_two_of_sq (by rw [← sq]; exact hxsq) hx1
  obtain ⟨g₁, hg₁, h₁⟩ := exists_conj_hsT1_of_fixCard τ.2
    (by rw [Subgroup.orderOf_coe]; exact hτ) hf
  obtain ⟨g₂, hg₂, h₂⟩ := exists_conj_hsT1_of_fixCard coverXPerm_mem hx2 fixCard_coverXPerm
  obtain ⟨h, hh⟩ := conj_of_perm_conj (a := τ) (b := ⟨coverXPerm, coverXPerm_mem⟩) hg₁ hg₂ h₁ h₂
  have hv : q l = h * q b₁ * h⁻¹ := by rw [hl, hb₁]; exact hh
  have hp : q b₁ ^ 2 = 1 := by rw [← map_pow, hb₁sq, map_one]
  have := sq_eq_sq_of_conj q hq hker.le (sq_of_mem_ker hker hZ) hv hp
  rw [hb₁sq] at this
  rwa [sq] at this

theorem sq_ne_of_fixCard_30 [Group.IsPerfect L] {q : L →* ↥hsP}
    (hq : Function.Surjective q) (hker : q.ker = center L) (hZ : Nat.card (center L) = 2)
    {τ : ↥hsP} (hτ : orderOf τ = 2) (hf : fixCard (τ : Equiv.Perm (Fin 3850)) = 30) :
    ∀ l : L, q l = τ → l * l ≠ 1 := by
  intro l hl hll
  obtain ⟨t, htZ, ht1, htu⟩ := exists_center_gen hZ
  have htq : t ∈ q.ker := hker ▸ htZ
  have hP : CFSG.QuasithinUnique.Id2519.UHS.hsC ∈ hsP := by
    rw [hsP_eq_original]
    exact CFSG.QuasithinUnique.Id2519.UHS.hsC_mem
  let X : CFSG.QuasithinUnique.Ch1.M22Cover.CentralExt L (Equiv.Perm (Fin 3850)) :=
    { φ := hsP.subtype.comp q
      ζ := t
      φ_ζ := by simp [MonoidHom.mem_ker.1 htq]
      ne_one := ht1
      sq := by simpa [sq] using sq_of_mem_ker hker hZ t htq
      central := fun e => (mem_center_iff.1 htZ e).symm
      ker := fun e he => htu e (hker ▸ MonoidHom.mem_ker.2 (Subtype.ext he)) }
  obtain ⟨u, hu⟩ := hq ⟨CFSG.QuasithinUnique.Id2519.UHS.hsC, hP⟩
  have hPP : ∀ x : Equiv.Perm (Fin 3850), x ∈ hsP ↔ x ∈ CFSG.QuasithinUnique.Id2519.UHS.PP :=
    fun x => by rw [hsP_eq_original]
  have hrange : ∀ y ∈ CFSG.QuasithinUnique.Id2519.UHS.PP, ∃ e : L, X.φ e = y := by
    intro y hy
    obtain ⟨e, he⟩ := hq ⟨y, (hPP y).2 hy⟩
    exact ⟨e, congrArg Subtype.val he⟩
  have hφmem : ∀ e : L, X.φ e ∈ CFSG.QuasithinUnique.Id2519.UHS.PP := fun e =>
    (hPP _).1 (q e).2
  have hcc : CFSG.QuasithinUnique.Id2519.UHS.hsC = CFSG.QuasithinUnique.Ch1.HSCover.cElt := by
    rw [CFSG.QuasithinUnique.Ch1.HSCover.cElt_eq]
    rfl
  have hcsq : CFSG.QuasithinUnique.Id2519.UHS.hsC * CFSG.QuasithinUnique.Id2519.UHS.hsC = 1 := by
    have h1 := pow_orderOf_eq_one CFSG.QuasithinUnique.Id2519.UHS.hsC
    rwa [CFSG.QuasithinUnique.Id2519.UHS.orderOf_hsC, sq] at h1
  obtain ⟨g₁, hg₁, h₁⟩ := exists_conj_hsT2_of_fixCard τ.2
    (by rw [Subgroup.orderOf_coe]; exact hτ) hf
  obtain ⟨g₂, hg₂, h₂⟩ := exists_conj_hsT2_of_fixCard hP
    CFSG.QuasithinUnique.Id2519.UHS.orderOf_hsC fixCard_hsC
  obtain ⟨h, hh⟩ := conj_of_perm_conj (a := τ)
    (b := ⟨CFSG.QuasithinUnique.Id2519.UHS.hsC, hP⟩) hg₁ hg₂ h₁ h₂
  have hv : q l = h * q u * h⁻¹ := by rw [hl, hu]; exact hh
  have hp : q u ^ 2 = 1 := by
    rw [hu]
    apply Subtype.ext
    simpa [sq] using hcsq
  have hl2 := sq_eq_sq_of_conj q hq hker.le (sq_of_mem_ker hker hZ) hv hp
  have hu2 : u * u = 1 := by
    have : l ^ 2 = 1 := by rwa [sq]
    rw [← sq, ← hl2, this]
  exact CFSG.QuasithinUnique.Ch1.HSCover.hs_no_involution_over_c X hrange hφmem u hu2
    (by rw [← hcc]; exact congrArg Subtype.val hu)

theorem fixCard_eq_170_of_tight (z : ↥hsP) (hz : orderOf z = 2)
    (φ : MulAut ↥hsP) (hφ2 : φ * φ = MulAut.conj z)
    (hφ : ∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → φ c = c) :
    fixCard (z : Equiv.Perm (Fin 3850)) = 170 := by
  rcases fixCard_involution z hz with h | h
  · exact h
  · exact (hs_not_tight_2B z hz h φ hφ2 hφ).elim

theorem s6_cover_data
    [Group.IsPerfect L]
    {q : L →* ↥hsP} (hq : Function.Surjective q) (hker : q.ker = center L)
    (hZ : Nat.card (center L) = 2) (z : ↥hsP) (hz : orderOf z = 2)
    (hz170 : fixCard (z : Equiv.Perm (Fin 3850)) = 170) :
    (∀ l : L, q l = z → l * l = 1) ∧
      ∃ w : ↥hsP, w * w = z ∧
        (∀ φ : MulAut ↥hsP, φ * φ = MulAut.conj z →
          (∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → φ c = c) →
            φ = MulAut.conj w ∨ φ = MulAut.conj w⁻¹) ∧
        ∃ x p : L, x * x = 1 ∧ (∀ l : L, q l = z → x * l = l * x) ∧ q x * w * (q x)⁻¹ = w⁻¹ ∧
          q x = q p * z * (q p)⁻¹ ∧ ∀ l : L, q l = w → x * l * (x * l) ≠ 1 := by
  obtain ⟨w, x', hww, hφuniq, hxx, hxz, hxw, hfx, hfxz, hfxw⟩ := hs_tight_data z hz hz170
  have hsq := fun {τ : ↥hsP} (hτ : orderOf τ = 2)
      (hf : fixCard (τ : Equiv.Perm (Fin 3850)) = 170) =>
    sq_of_fixCard_170 hq hker hZ hτ hf
  refine ⟨hsq hz hz170, w, hww, hφuniq, ?_⟩
  obtain ⟨x, hx⟩ := hq x'
  have hx'1 : x' ≠ 1 := fun h => ne_one_of_fixCard_lt hfx (by norm_num) (congrArg Subtype.val h)
  have hx'ord : orderOf x' = 2 := orderOf_eq_two_of_sq hxx hx'1
  have hxx' : x * x = 1 := hsq hx'ord hfx x hx
  have hcomm : ∀ l : L, q l = z → x * l = l * x := by
    intro l hl
    have hll : l * l = 1 := hsq hz hz170 l hl
    have hxzq : q (x * l) = x' * z := by rw [map_mul, hx, hl]
    have hxz1 : x' * z ≠ 1 := fun h => ne_one_of_fixCard_lt hfxz (by norm_num)
      (congrArg Subtype.val h)
    have hxz2 : (x' * z) * (x' * z) = 1 := by
      calc (x' * z) * (x' * z) = x' * (z * x') * z := by group
        _ = x' * (x' * z) * z := by rw [← hxz]
        _ = (x' * x') * (z * z) := by group
        _ = 1 := by
          rw [hxx]
          have : z * z = 1 := by
            have h1 := pow_orderOf_eq_one z
            rwa [hz, sq] at h1
          rw [this, one_mul]
    have hxl : (x * l) * (x * l) = 1 :=
      hsq (orderOf_eq_two_of_sq hxz2 hxz1) hfxz (x * l) hxzq
    have h1 : (x * l)⁻¹ = x * l := inv_eq_of_mul_eq_one_right hxl
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hll, inv_eq_of_mul_eq_one_right hxx'] at h1
    exact h1.symm
  have hzP : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hz
  have hx'P : orderOf (x' : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hx'ord
  obtain ⟨g₁, hg₁, h₁⟩ := exists_conj_hsT1_of_fixCard x'.2 hx'P hfx
  obtain ⟨g₂, hg₂, h₂⟩ := exists_conj_hsT1_of_fixCard z.2 hzP hz170
  obtain ⟨h, hh⟩ := conj_of_perm_conj (a := x') (b := z) hg₁ hg₂ h₁ h₂
  obtain ⟨p, hp⟩ := hq h
  refine ⟨x, p, hxx', hcomm, by rw [hx]; exact hxw, by rw [hx, hp]; exact hh, ?_⟩
  intro l hl
  have hxwq : q (x * l) = x' * w := by rw [map_mul, hx, hl]
  have hxw1 : x' * w ≠ 1 := fun h => ne_one_of_fixCard_lt hfxw (by norm_num)
    (congrArg Subtype.val h)
  have hxw2 : (x' * w) * (x' * w) = 1 := by
    have h1 : x' * w * x' = w⁻¹ := by
      have := hxw
      rwa [inv_eq_of_mul_eq_one_right hxx] at this
    calc (x' * w) * (x' * w) = (x' * w * x') * w := by group
      _ = 1 := by rw [h1]; group
  exact sq_ne_of_fixCard_30 hq hker hZ (orderOf_eq_two_of_sq hxw2 hxw1) hfxw (x * l) hxwq

end Cover

end CFSG.EvenSporadicStandard.TwoHS

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSCentralExt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHS

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def HSFacts : Prop :=
  (∀ {Y : Type} [Group Y], IsSporadic Y .HS → Nat.card Y = 44352000) ∧
  (∀ {Y : Type} [Group Y], IsSporadic Y .HS → ∀ y : Y, orderOf y = 2 →
    Nat.card ↥(centralizer ({y} : Set Y)) = 7680 ∨
      Nat.card ↥(centralizer ({y} : Set Y)) = 2880) ∧
  (∀ {Y : Type} [Group Y] (N : Subgroup Y), IsSporadic ↥N .HS →
    ∀ y : Y, (∀ n ∈ N, y * n * y⁻¹ ∈ N) → y * y = 1 → (∃ n ∈ N, y * n ≠ n * y) →
      Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 7680 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 2880 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 40320 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 1920) ∧
  (∀ {E : Type} [Group E] [Finite E], Group.IsPerfect E → IsSporadic (E ⧸ center E) .HS →
    Nat.card ↥(center E) ≤ 2)

open CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem u_conj_sq {Y : Type*} [Group Y] {y : Y} (hyy : y * y = 1) (x : Y) :
    y * (y * x * y⁻¹) * y⁻¹ = x := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  rw [hyinv]
  calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
    _ = x := by rw [hyy]; group

theorem hsFacts_holds :
    HSFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y _ hY
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_eq_of_isSporadic_hs hY
  · intro Y _ hY y hy
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs hY y hy
  · intro Y _ N hN y hyN hyy hnc
    obtain ⟨e₀⟩ := hN
    have e : ↥N ≃* NativeSporadic.HS := e₀
    have hN' : IsSporadic ↥N .HS := ⟨e₀⟩
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have hle : N.map (MulAut.conj y : Y →* Y) ≤ N := by
      rintro x ⟨n, hn, rfl⟩
      simpa [MulAut.conj_apply] using hyN n hn
    have hge : N ≤ N.map (MulAut.conj y : Y →* Y) := by
      intro x hx
      refine ⟨(MulAut.conj y).symm x, ?_, (MulAut.conj y).apply_symm_apply x⟩
      have h := hyN x hx
      rw [MulAut.conj_symm_apply, hyinv]
      rwa [hyinv] at h
    have hmapN : N.map (MulAut.conj y : Y →* Y) = N := le_antisymm hle hge
    let σ : MulAut ↥N :=
      ((MulAut.conj y).subgroupMap N).trans (MulEquiv.subgroupCongr hmapN)
    have hσn : ∀ n : ↥N, (σ n : Y) = y * (n : Y) * y⁻¹ := fun n => rfl
    have hσ2 : σ * σ = 1 := by
      ext n
      change (σ (σ n) : Y) = (n : Y)
      rw [hσn (σ n), hσn n]
      exact u_conj_sq hyy (n : Y)
    have hσ1 : σ ≠ 1 := by
      intro h
      obtain ⟨n, hn, hny⟩ := hnc
      have hfix : σ ⟨n, hn⟩ = ⟨n, hn⟩ := by rw [h]; rfl
      have hval : y * n * y⁻¹ = n := by
        have := congrArg Subtype.val hfix
        rwa [hσn ⟨n, hn⟩] at this
      have hcomm : y * n = n * y := by
        have h' := hval
        rw [hyinv] at h'
        calc y * n = y * n * (y * y) := by rw [hyy, mul_one]
          _ = (y * n * y) * y := by group
          _ = n * y := by rw [h']
      exact hny hcomm
    have hσord : orderOf σ = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
    have hmapfixed : (fixedSubgroup σ).map N.subtype = N ⊓ centralizer ({y} : Set Y) := by
      ext x
      constructor
      · rintro ⟨n, hnfix, rfl⟩
        have hfix : σ n = n := hnfix
        have hval : y * (n : Y) * y⁻¹ = (n : Y) := by
          have := congrArg Subtype.val hfix
          rwa [hσn n] at this
        refine ⟨n.2, ?_⟩
        change (n : Y) ∈ Subgroup.centralizer ({y} : Set Y)
        rw [Subgroup.mem_centralizer_singleton_iff]
        conv_lhs => rw [← hval]
        group
      · intro hx
        obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
        rw [Subgroup.mem_centralizer_singleton_iff] at hxC
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        show σ ⟨x, hxN⟩ = ⟨x, hxN⟩
        apply Subtype.ext
        rw [hσn ⟨x, hxN⟩]
        rw [← hxC]
        group
    have hcardN : Nat.card (fixedSubgroup σ) =
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) := by
      rw [← Subgroup.card_map_of_injective N.subtype_injective, hmapfixed]
    have hfixed : Nat.card (fixedSubgroup σ) = 7680 ∨ Nat.card (fixedSubgroup σ) = 2880 ∨
        Nat.card (fixedSubgroup σ) = 40320 ∨ Nat.card (fixedSubgroup σ) = 1920 := by
      by_cases hout : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
      ·
        obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 hout
        have hσ2' : MulAut.conj n * MulAut.conj n = 1 := by rw [hn]; exact hσ2
        have hσ1' : MulAut.conj n ≠ 1 := by rw [hn]; exact hσ1
        have hconj : MulAut.conj (n * n) = 1 := by rw [map_mul, hσ2']
        have hnn_center : n * n ∈ center ↥N := by
          rw [Subgroup.mem_center_iff]
          intro g
          have h : (n * n) * g * (n * n)⁻¹ = g := by
            have h0 := congrArg (fun f : MulAut ↥N => f g) hconj
            simpa only [MulAut.conj_apply, MulAut.coe_one, id_eq] using h0
          have h' : (n * n) * g = g * (n * n) := by
            calc (n * n) * g = ((n * n) * g * (n * n)⁻¹) * (n * n) := by group
              _ = g * (n * n) := by rw [h]
          exact h'.symm
        have hnn : n * n = 1 := by
          have hc := CFSG.EvenSporadicStandard.TwoHS.center_eq_bot_of_isSporadic_hs hN'
          rw [hc, Subgroup.mem_bot] at hnn_center
          exact hnn_center
        have hn1 : n ≠ 1 := fun h => hσ1' (by rw [h, map_one])
        have hn2 : orderOf n = 2 := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime (by rw [pow_two]; exact hnn) hn1
        have hfixeq : fixedSubgroup (MulAut.conj n) = centralizer ({n} : Set ↥N) := by
          ext g
          constructor
          · intro hg
            have h : (MulAut.conj n) g = g := hg
            rw [MulAut.conj_apply] at h
            rw [Subgroup.mem_centralizer_singleton_iff]
            conv_lhs => rw [← h]
            group
          · intro hg
            rw [Subgroup.mem_centralizer_singleton_iff] at hg
            show (MulAut.conj n) g = g
            rw [MulAut.conj_apply]
            rw [← hg]
            group
        rw [← hn, hfixeq]
        rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs
          hN' n hn2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      ·
        obtain ⟨r, hr, hrout, ⟨ψ⟩⟩ :=
          CFSG.ComponentClassification.CatFC.hs_fixedSubgroup_rows_outer e hσord hout
        obtain ⟨-, -, -, hrows, -, -, hmap, -⟩ :=
          CFSG.Sporadic.SmallOddCore.hs_involution_centralizers
        have hcardC : Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} :
            Set (Equiv.Perm (Fin 3850)))) = r.centOrder := (hrows r hr).2.2.2.2.1
        have hmem : (r.outer, r.classSize, r.centOrder) ∈
            [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320),
              (true, 23100, 1920)] := by
          rw [← hmap]
          exact List.mem_map_of_mem
            (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder)) hr
        have hcent : r.centOrder = 40320 ∨ r.centOrder = 1920 := by
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
          rcases hmem with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
          · exact absurd (h1.symm.trans hrout) (by decide)
          · exact absurd (h1.symm.trans hrout) (by decide)
          · exact Or.inl h3
          · exact Or.inr h3
        have hcardFixed : Nat.card (fixedSubgroup σ) = r.centOrder :=
          (Nat.card_congr ψ.toEquiv).trans hcardC
        rcases hcent with h | h
        · exact Or.inr (Or.inr (Or.inl (hcardFixed.trans h)))
        · exact Or.inr (Or.inr (Or.inr (hcardFixed.trans h)))
    have hfinal : Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 7680 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 2880 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 40320 ∨
        Nat.card ↥(N ⊓ centralizer ({y} : Set Y)) = 1920 := by
      rw [← hcardN]
      exact hfixed
    exact hfinal
  · intro E _ _ hperf hq
    by_cases hbot : center E = ⊥
    · rw [hbot, Subgroup.card_bot]
      norm_num
    · rw [CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot hperf hq hbot]

end CFSG.OddStandard.AltStdSec.SwapPartner

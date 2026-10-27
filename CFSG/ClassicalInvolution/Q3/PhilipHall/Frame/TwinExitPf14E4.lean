module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Balance

section Norm

variable {G : Type} [Group G] [Finite G]

theorem normalizes_oddCoreIn {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) {x : G} (hx : x ∈ oddCoreIn H) :
    g * x * g⁻¹ ∈ oddCoreIn H := by
  have hS : conjSub g (oddCoreIn H) ≤ oddCoreIn H := by
    refine le_oddCoreIn_of_normalizes (S := conjSub g (oddCoreIn H)) ?_ ?_ ?_
    · intro y hy
      rw [mem_conjSub_iff] at hy
      have := hg _ (oddCoreIn_le H hy)
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e] at this
    · intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn H (hg' h hh)) (g⁻¹ * y * g)
      rw [mem_conjSub_iff, mem_conjSub_iff]
      have e : g⁻¹ * (h * y * h⁻¹) * g = (g⁻¹ * h * g) * (g⁻¹ * y * g) * (g⁻¹ * h * g)⁻¹ := by
        group
      rw [e]
      exact h1
    · have hc : Nat.card (conjSub g (oddCoreIn H)) = Nat.card (oddCoreIn H) := by
        unfold conjSub
        exact Subgroup.card_map_of_injective (fun a b h => (MulAut.conj g).injective h)
      rw [hc]
      exact odd_card_oddCoreIn H
  refine hS ((mem_conjSub_iff).mpr ?_)
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e]
  exact hx

end Norm

section Surj

variable {X M : Type} [Group X] [Finite X] [Group M] [Finite M]

theorem oddCent_bot_of_surj_simple [IsSimpleGroup M] (f : X →* M) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker)
    (hM : ∀ s : M, orderOf s = 2 → oddCoreIn (Subgroup.centralizer ({s} : Set M)) = ⊥)
    (hO : classicalInvolutionOddCore X = ⊥) {w : X} (hw : w * w = 1) :
    oddCoreIn (Subgroup.centralizer ({w} : Set X)) = ⊥ := by
  have hfn : f.ker.Normal := MonoidHom.normal_ker f
  by_cases hfw : f w = 1
  · exact oddCoreIn_centralizer_eq_bot_of_mem_normal hO hfn hk (MonoidHom.mem_ker.mpr hfw)
  have hws : orderOf (f w) = 2 := by
    refine orderOf_eq_prime ?_ hfw
    rw [sq, ← map_mul, hw, map_one]
  have hz : IsPGroup 2 (Subgroup.zpowers w) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hw
  set N := f.ker with hN
  set C := Subgroup.centralizer ({w} : Set X) with hC
  set Q := oddCoreIn C with hQ
  set Y₀ := Subgroup.centralizer (N : Set X) with hY₀
  have hQY : Q ≤ Y₀ := oddCoreIn_centralizer_le_centralizer_of_normal hfn hk hz
  have hNY : ∀ y ∈ Y₀, ∀ n ∈ N, n * y = y * n := fun y hy n hn =>
    Subgroup.mem_centralizer_iff.mp hy n hn
  have hY₀n : ∀ y ∈ Y₀, ∀ g : X, g * y * g⁻¹ ∈ Y₀ := by
    intro y hy g
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : g⁻¹ * n * g ∈ N := by
      have := hfn.conj_mem n hn g⁻¹
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hy (g⁻¹ * n * g) hn'
    calc n * (g * y * g⁻¹) = g * ((g⁻¹ * n * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
      _ = (g * y * g⁻¹) * n := by group
  have hY₀normal : Y₀.Normal := ⟨fun y hy g => hY₀n y hy g⟩
  have hmapn : (Y₀.map f).Normal := Subgroup.Normal.map hY₀normal f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y₀.map f) with hbot | htop
  · have hYN : ∀ y ∈ Y₀, f y = 1 := by
      intro y hy
      have : f y ∈ Y₀.map f := ⟨y, hy, rfl⟩
      rw [hbot] at this
      simpa using this
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    have hqN : q ∈ N := MonoidHom.mem_ker.mpr (hYN q (hQY hq))
    exact eq_one_of_odd_orderOf_of_pGroup (L := N) hk hqN
      (odd_orderOf_of_mem_odd (odd_card_oddCoreIn C) hq)
  · set H : Subgroup X := C ⊓ Y₀ with hH
    have hQH : Q ≤ H := fun q hq => ⟨oddCoreIn_le C hq, hQY hq⟩
    have hHnorm : H ≤ Subgroup.normalizer (Q : Set X) := fun h hh => normalizer_oddCoreIn C hh.1
    have hQO : Q ≤ oddCoreIn H := le_oddCoreIn_of_normalizes hQH hHnorm (odd_card_oddCoreIn C)
    have hG₁ : ∀ g ∈ Y₀, f g * f w = f w * f g → ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
      intro g hg hc h hh
      have hhC' : h ∈ Subgroup.centralizer ({w} : Set X) := hh.1
      have hhC : h * w = w * h := Subgroup.mem_centralizer_singleton_iff.mp hhC'
      refine ⟨?_, Y₀.mul_mem (Y₀.mul_mem hg hh.2) (Y₀.inv_mem hg)⟩
      set μ : X := g⁻¹ * w * g * w⁻¹ with hμ
      have hμN : μ ∈ N := by
        rw [hN, MonoidHom.mem_ker, hμ]
        simp only [map_mul, map_inv]
        calc (f g)⁻¹ * f w * f g * (f w)⁻¹ = (f g)⁻¹ * (f w * f g) * (f w)⁻¹ := by group
          _ = (f g)⁻¹ * (f g * f w) * (f w)⁻¹ := by rw [← hc]
          _ = 1 := by group
      have hμh : μ * h = h * μ := hNY h hh.2 μ hμN
      have hgw : g⁻¹ * w * g = μ * w := by rw [hμ]; group
      have hcomm : h * (g⁻¹ * w * g) = (g⁻¹ * w * g) * h := by
        rw [hgw]
        calc h * (μ * w) = (h * μ) * w := by group
          _ = (μ * h) * w := by rw [← hμh]
          _ = μ * (h * w) := by group
          _ = μ * (w * h) := by rw [hhC]
          _ = (μ * w) * h := by group
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (g * h * g⁻¹) * w = g * (h * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * h) * g⁻¹ := by rw [hcomm]
        _ = w * (g * h * g⁻¹) := by group
    have hcinv : ∀ g : X, f g * f w = f w * f g → f g⁻¹ * f w = f w * f g⁻¹ := by
      intro g hc
      rw [map_inv]
      exact (show Commute (f g) (f w) from hc).inv_left.eq
    have hOnorm : ∀ g ∈ Y₀, f g * f w = f w * f g → ∀ x ∈ oddCoreIn H,
        g * x * g⁻¹ ∈ oddCoreIn H := fun g hg hc x hx =>
      normalizes_oddCoreIn (hG₁ g hg hc) (by
        have := hG₁ g⁻¹ (Y₀.inv_mem hg) (hcinv g hc)
        simpa using this) hx
    have hfO : (oddCoreIn H).map f ≤ oddCoreIn (Subgroup.centralizer ({f w} : Set M)) := by
      refine le_oddCoreIn_of_normalizes (X := Subgroup.centralizer ({f w} : Set M))
        (S := (oddCoreIn H).map f) ?_ ?_ ?_
      · rintro _ ⟨o, ho, rfl⟩
        have hoH := oddCoreIn_le H ho
        have hoC : o ∈ Subgroup.centralizer ({w} : Set X) := hoH.1
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hoC
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        rw [← map_mul, ← map_mul, h1]
      · intro m hm
        have hm' : m * f w = f w * m := Subgroup.mem_centralizer_singleton_iff.mp hm
        have hmY : m ∈ Y₀.map f := by rw [htop]; trivial
        obtain ⟨g, hg, rfl⟩ := hmY
        have hc : f g * f w = f w * f g := hm'
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨o, ho, rfl⟩
          exact ⟨g * o * g⁻¹, hOnorm g hg hc o ho, by simp [map_mul]⟩
        · rintro ⟨o, ho, hoy⟩
          refine ⟨g⁻¹ * o * g, ?_, ?_⟩
          · have := hOnorm g⁻¹ (Y₀.inv_mem hg) (hcinv g hc) o ho
            simpa using this
          · rw [map_mul, map_mul, map_inv, hoy]
            group
      · exact Odd.of_dvd_nat (odd_card_oddCoreIn H) (Subgroup.card_map_dvd (oddCoreIn H) f)
    rw [hM (f w) hws] at hfO
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    have hqO := hQO hq
    have hfq : f q = 1 := by
      have : f q ∈ (oddCoreIn H).map f := ⟨q, hqO, rfl⟩
      have := hfO this
      simpa using this
    exact eq_one_of_odd_orderOf_of_pGroup (L := N) hk (MonoidHom.mem_ker.mpr hfq)
      (odd_orderOf_of_mem_odd (odd_card_oddCoreIn C) hq)

end Surj

section Models

theorem oddCoreIn_centralizer_eq_bot_of_autOddFree {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hA : Q3NM.AutOddFree Q) {s : Q} (hs : orderOf s = 2) :
    oddCoreIn (Subgroup.centralizer ({s} : Set Q)) = ⊥ := by
  by_cases hZ : Subgroup.center Q = ⊥
  · set 𝒳 : Subgroup (MulAut Q) := Q3NM.innSubgroup Q with h𝒳
    have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) :=
      fun a b h => Q3NM.conj_injective_of_center_eq_bot hZ h
    set f : ↥𝒳 := ⟨MulAut.conj s, ⟨s, rfl⟩⟩ with hf
    have hf2 : orderOf f = 2 := by
      rw [← hs, ← orderOf_injective (MulAut.conj : Q →* MulAut Q) hinj s,
        ← Subgroup.orderOf_coe f]
    have h1 : oddCoreIn (Subgroup.centralizer ({f} : Set ↥𝒳)) = ⊥ := hA 𝒳 le_rfl f hf2
    set ψ : Q →* ↥𝒳 := (MulAut.conj : Q →* MulAut Q).codRestrict 𝒳 (fun x => ⟨x, rfl⟩) with hψ
    have hψinj : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
    set C := Subgroup.centralizer ({s} : Set Q) with hC
    set T := oddCoreIn C with hT
    have hS : T.map ψ ≤ oddCoreIn (Subgroup.centralizer ({f} : Set ↥𝒳)) := by
      refine le_oddCoreIn_of_normalizes (X := Subgroup.centralizer ({f} : Set ↥𝒳))
        (S := T.map ψ) ?_ ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        have hqC : q ∈ Subgroup.centralizer ({s} : Set Q) := oddCoreIn_le C hq
        have h2 := Subgroup.mem_centralizer_singleton_iff.mp hqC
        refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
        show (MulAut.conj q) * (MulAut.conj s) = (MulAut.conj s) * (MulAut.conj q)
        rw [← map_mul, ← map_mul, h2]
      · intro c hc
        have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
        obtain ⟨x, hx⟩ := c.2
        have hxc : ψ x = c := Subtype.ext hx
        have hxC : x ∈ C := by
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          apply hinj
          have := congrArg Subtype.val hc'
          rw [← hxc] at this
          rw [map_mul, map_mul]
          exact this
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have hxn := Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn C hxC)
        have hxn' := Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn C (C.inv_mem hxC))
        rw [← hxc]
        constructor
        · rintro ⟨q, hq, rfl⟩
          refine ⟨x * q * x⁻¹, (hxn q).mp hq, ?_⟩
          simp [map_mul]
        · rintro ⟨q, hq, hqy⟩
          refine ⟨x⁻¹ * q * x, ?_, ?_⟩
          · have := (hxn' q).mp hq
            simpa using this
          · have : ψ x * y * (ψ x)⁻¹ = ψ q := hqy.symm
            have h3 : y = (ψ x)⁻¹ * ψ q * ψ x := by rw [← this]; group
            rw [h3]
            simp [map_mul, map_inv]
      · have hc : Nat.card (T.map ψ) = Nat.card T := Subgroup.card_map_of_injective hψinj
        rw [hc]
        exact odd_card_oddCoreIn C
    rw [h1, le_bot_iff] at hS
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    have : ψ q ∈ T.map ψ := ⟨q, hq, rfl⟩
    rw [hS] at this
    exact hψinj (by simpa using this)
  · have hcen : Subgroup.center Q = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q)).resolve_left hZ
    have hs0 : s ∈ Subgroup.center Q := by rw [hcen]; trivial
    have hC : Subgroup.centralizer ({s} : Set Q) = ⊤ := by
      refine eq_top_iff.mpr fun q _ => ?_
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      exact (Subgroup.mem_center_iff.mp hs0) q
    rw [hC]
    set T := oddCoreIn (⊤ : Subgroup Q) with hT
    have hTn : T.Normal := ⟨fun x hx g => by
      have := normalizer_oddCoreIn (⊤ : Subgroup Q) (Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.mp this x).mp hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card T) := odd_card_oddCoreIn _
      have hsT : s ∈ T := by rw [h]; trivial
      have hdvd := Subgroup.orderOf_dvd_natCard T hsT
      rw [hs] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem oddCent_bot_of_twinE4 (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    {X : Type} [Group X] [Finite X] (hO : classicalInvolutionOddCore X = ⊥) (h : TwinE4 X)
    {w : X} (hw : w * w = 1) : oddCoreIn (Subgroup.centralizer ({w} : Set X)) = ⊥ := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  have : Finite Q := Finite.of_surjective f hfs
  rcases hQ with hQ | hQ
  · have := TwinCentRes.isSimple_of_psp hQ
    exact oddCent_bot_of_surj_simple f hfs hf2 (fun s hs => hSp Q hQ s hs) hO hw
  · have := TwinCentRes.isSimple_of_pomegaPlus hQ
    exact oddCent_bot_of_surj_simple f hfs hf2
      (fun s hs => oddCoreIn_centralizer_eq_bot_of_autOddFree (hD4 Q hQ) hs) hO hw

end Models

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14

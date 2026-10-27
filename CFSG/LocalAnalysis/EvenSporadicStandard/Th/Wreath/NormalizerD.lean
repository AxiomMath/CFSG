module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerBp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndD

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.centralizer_D_inf_centralizer_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    centralizer (D : Set G) ⊓ centralizer ({t} : Set G) = Aa := by
  have hAaD : Aa ≤ D := hD.Aa_le
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxD, hxt⟩
    have hxC : x ∈ L ⊔ zpowers t := by rw [← H.centralizer_eq_zpowers]; exact hxt
    have hcomm : zpowers t ≤ centralizer (L : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun l hl => (H.comm_of_mem_L hl).symm
    obtain ⟨l, hlL, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hxC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hlt : ∀ a ∈ Aa, a * t ^ k = t ^ k * a := fun a ha =>
      (((show Commute a t from
        (H.comm_of_mem_L (W.B_le (W2.Aa_le ha))).symm).zpow_right k).eq)
    have hlAa : l ∈ Aa := by
      have hmem : l ∈ L ⊓ centralizer (Aa : Set G) := by
        refine ⟨hlL, mem_centralizer_iff.2 fun a ha => ?_⟩
        have h1 : a * (l * t ^ k) = (l * t ^ k) * a :=
          mem_centralizer_iff.1 hxD a (hAaD ha)
        have h2 : (a * l) * t ^ k = (l * a) * t ^ k := by
          calc (a * l) * t ^ k = a * (l * t ^ k) := by group
            _ = (l * t ^ k) * a := h1
            _ = l * (t ^ k * a) := by group
            _ = l * (a * t ^ k) := by rw [← hlt a ha]
            _ = (l * a) * t ^ k := by group
        exact mul_right_cancel h2
      rwa [W2.inf_centralizer_Aa_eq W] at hmem
    rcases zpow_eq_one_or_self H.sq_t k with hk | hk
    · rw [hk, mul_one]
      exact hlAa
    · exfalso
      rw [hk] at hxD
      have htD : ∀ d ∈ D, d * t = t * d := by
        intro d hd
        have h1 : d * (l * t) = (l * t) * d := mem_centralizer_iff.1 hxD d hd
        have h2 : l * (d * t) = l * (t * d) := by
          calc l * (d * t) = (l * d) * t := by group
            _ = (d * l) * t := by rw [hD.comm d hd l (hAaD hlAa)]
            _ = d * (l * t) := by group
            _ = (l * t) * d := h1
            _ = l * (t * d) := by group
        exact mul_left_cancel h2
      have hDAa : D ≤ Aa := by
        intro d hd
        refine (H.D_theta_eq_one_iff W W2 hD hd).1 ?_
        have hdt : d * t = t * d := htD d hd
        calc theta t d = (d * t) * d⁻¹ * t⁻¹ := rfl
          _ = 1 := by rw [hdt]; group
      have hcard := Subgroup.card_le_of_le hDAa
      rw [hD.card, W2.Aa_card] at hcard
      norm_num at hcard
  · intro a ha
    exact ⟨mem_centralizer_iff.2 fun d hd => (hD.comm a (hAaD ha) d hd).symm,
      mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.B_le (W2.Aa_le ha))).symm⟩

theorem ThCyc.D_inf_centralizer_t_eq_Aa (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : D ⊓ centralizer ({t} : Set G) = Aa := by
  refine le_antisymm ?_ (le_inf hD.Aa_le fun a ha =>
    mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.B_le (W2.Aa_le ha))).symm)
  rintro d ⟨hd, hdc⟩
  have hd' : d ∈ centralizer (D : Set G) :=
    mem_centralizer_iff.2 fun e he => (hD.comm d hd e he).symm
  have h2 : d ∈ centralizer (D : Set G) ⊓ centralizer ({t} : Set G) := ⟨hd', hdc⟩
  rwa [H.centralizer_D_inf_centralizer_t W W2 hD] at h2

theorem ThCyc.inf_normalizer_D_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    L ⊓ normalizer (D : Set G) = L ⊓ normalizer (A : Set G) := by
  have hDt : D ⊓ centralizer ({t} : Set G) = Aa := H.D_inf_centralizer_t_eq_Aa W W2 hD
  have hAaD : ∀ x ∈ Aa, x ∈ D := hD.Aa_le
  refine le_antisymm ?_ ?_
  · rintro l ⟨hlL, hlD⟩
    have hmemAa' : ∀ x ∈ Aa, l⁻¹ * x * l ∈ Aa := by
      intro x hx
      have hxD : l⁻¹ * x * l ∈ D := by
        have h := (mem_normalizer_iff.1 ((normalizer (D : Set G)).inv_mem hlD) x).1 (hAaD x hx)
        simpa using h
      have hxL : l⁻¹ * x * l ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem hlL) (W.B_le (W2.Aa_le hx))) hlL
      have hxC : l⁻¹ * x * l ∈ centralizer ({t} : Set G) :=
        mem_centralizer_singleton_iff.2 (H.comm_of_mem_L hxL).symm
      have h2 : l⁻¹ * x * l ∈ D ⊓ centralizer ({t} : Set G) := ⟨hxD, hxC⟩
      rwa [hDt] at h2
    have hinv : ∀ a ∈ A, l⁻¹ * a * l ∈ A := by
      intro a ha
      obtain ⟨x, hx, hx2⟩ := (W2.A_eq_sq a).1 ha
      have hxA' : l⁻¹ * x * l ∈ Aa := hmemAa' x hx
      refine (W2.A_eq_sq _).2 ⟨l⁻¹ * x * l, hxA', ?_⟩
      calc (l⁻¹ * x * l) ^ 2 = l⁻¹ * x ^ 2 * l := by rw [sq, sq]; group
        _ = l⁻¹ * a * l := by rw [hx2]
    exact ⟨hlL, mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := l) hinv)⟩
  · rintro l ⟨hlL, hlA⟩
    have hNW : l ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
      H.mem_normalizer_W5_of_L W hlL fun x hx => (mem_normalizer_iff.1 hlA x).1 hx
    exact ⟨hlL, le_normalizer_of_conj_mem hD.norm hNW⟩

theorem ThCyc.normalizer_D_inf_centralizer_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    normalizer (D : Set G) ⊓ centralizer ({t} : Set G) =
      (L ⊓ normalizer (A : Set G)) ⊔ zpowers t := by
  have hzD : zpowers t ≤ normalizer (D : Set G) :=
    zpowers_le.2 (le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD))
  have hcomm : zpowers t ≤ centralizer (L : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun l hl => (H.comm_of_mem_L hl).symm
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxN, hxt⟩
    have hxC : x ∈ L ⊔ zpowers t := by rw [← H.centralizer_eq_zpowers]; exact hxt
    obtain ⟨l, hlL, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hxC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have htkN : t ^ k ∈ normalizer (D : Set G) := hzD (zpow_mem (mem_zpowers t) k)
    have hlD : l ∈ normalizer (D : Set G) := by
      have h := (normalizer (D : Set G)).mul_mem hxN ((normalizer (D : Set G)).inv_mem htkN)
      simpa using h
    have hl : l ∈ L ⊓ normalizer (D : Set G) := ⟨hlL, hlD⟩
    rw [H.inf_normalizer_D_eq W W2 hD] at hl
    exact mul_mem_sup hl (zpow_mem (mem_zpowers t) k)
  · refine sup_le ?_ ?_
    · rintro l ⟨hlL, hlA⟩
      have h : l ∈ L ⊓ normalizer (D : Set G) := by
        rw [H.inf_normalizer_D_eq W W2 hD]
        exact ⟨hlL, hlA⟩
      exact ⟨h.2, mem_centralizer_singleton_iff.2 (H.comm_of_mem_L hlL).symm⟩
    · intro r hr
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      exact ⟨hzD (zpow_mem (mem_zpowers t) k),
        mem_centralizer_singleton_iff.2 ((Commute.refl t).zpow_right k).eq.symm⟩

theorem ThCyc.exists_mem_L_conj_eq_of_mem_normalizer_A (W : ThLocalIn L S A B z) {g : G}
    (hg : g ∈ normalizer (A : Set G)) :
    ∃ l ∈ L ⊓ normalizer (A : Set G), g * l⁻¹ ∈ centralizer (A : Set G) := by
  have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.1 hg a).1 ha
  have hgA' : ∀ a ∈ A, g⁻¹ * a * g ∈ A := fun a ha => by
    have h := (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hg) a).1 ha
    simpa using h
  obtain ⟨n, hnL, hn⟩ := W.surj (fun a => g * a * g⁻¹) hgA
    (fun a _ b _ => by group)
    (fun a _ b _ hab => by simpa using hab)
  have hna : ∀ a ∈ A, n⁻¹ * a * n = g⁻¹ * a * g := by
    intro a ha
    have ha' : g⁻¹ * a * g ∈ A := hgA' a ha
    have h1 : n * (g⁻¹ * a * g) * n⁻¹ = a := by
      rw [hn (g⁻¹ * a * g) ha']; group
    calc n⁻¹ * a * n = n⁻¹ * (n * (g⁻¹ * a * g) * n⁻¹) * n := by rw [h1]
      _ = g⁻¹ * a * g := by group
  have hninv : ∀ a ∈ A, n⁻¹ * a * n ∈ A := fun a ha => by
    rw [hna a ha]
    exact hgA' a ha
  have hnN : n ∈ normalizer (A : Set G) :=
    mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n) hninv)
  have hgn : g * n⁻¹ ∈ centralizer (A : Set G) := by
    refine mem_centralizer_iff.2 fun a ha => ?_
    have hconj : (g * n⁻¹) * a * (g * n⁻¹)⁻¹ = a := by
      calc (g * n⁻¹) * a * (g * n⁻¹)⁻¹ = g * (n⁻¹ * a * n) * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hna a ha]
        _ = a := by group
    have hcomm' : (g * n⁻¹) * a = a * (g * n⁻¹) := by
      calc (g * n⁻¹) * a = ((g * n⁻¹) * a * (g * n⁻¹)⁻¹) * (g * n⁻¹) := by group
        _ = a * (g * n⁻¹) := by rw [hconj]
    exact hcomm'.symm
  exact ⟨n, ⟨hnL, hnN⟩, hgn⟩

theorem ThCyc.normalizer_A_eq_sup (W : ThLocalIn L S A B z) :
    normalizer (A : Set G) = centralizer (A : Set G) ⊔ (L ⊓ normalizer (A : Set G)) := by
  refine le_antisymm ?_ (sup_le (Subgroup.centralizer_le_normalizer (A : Set G)) inf_le_right)
  intro g hg
  obtain ⟨l, hl, hgl⟩ := ThCyc.exists_mem_L_conj_eq_of_mem_normalizer_A W hg
  have h1 : g = (g * l⁻¹) * l := by group
  rw [h1]
  exact mul_mem_sup hgl hl

end CFSG.EvenSporadicStandard.ThStd

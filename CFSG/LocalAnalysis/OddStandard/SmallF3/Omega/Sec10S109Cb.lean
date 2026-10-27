module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TPk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_mem_normalizer_of_comm {X : Subgroup G} {b : G} (hb : ∀ a ∈ X, a * b = b * a) :
    b ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : b * x * b⁻¹ = x := by rw [← hb x hx]; group
    rwa [this]
  · intro hx
    have h : b * x * b⁻¹ * b = b * (b * x * b⁻¹) := hb _ hx
    have h' : b * x = b * (b * x * b⁻¹) := by simpa [mul_assoc] using h
    have h'' : b * x * b⁻¹ = x := (mul_left_cancel h').symm
    rwa [h''] at hx

theorem sec10C_mem_normalizer_of_invol {K : Subgroup G} {s : G} (hs2 : s * s = 1)
    (h : ∀ x ∈ K, s * x * s⁻¹ ∈ K) : s ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h' := h _ hx
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have e : s * (s * x * s⁻¹) * s⁻¹ = x := by
    rw [hs']
    calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
      _ = x := by rw [hs2]; group
  rwa [e] at h'

theorem sec10C_conjugate_eq_of_normalizer {K : Subgroup G} {s : G}
    (hs : s ∈ normalizer (K : Set G)) : CFSG.conjugate K s = K := by
  ext x
  rw [mem_conjugate_iff']
  exact (Subgroup.mem_normalizer_iff.mp hs x).symm

theorem sec10C_sup_normalizes [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    K1 ⊔ K2 ≤ normalizer (K1 : Set G) ⊓ normalizer (K2 : Set G) := by
  have hc : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  refine le_inf (sup_le Subgroup.le_normalizer fun b hb => ?_)
    (sup_le (fun a ha => ?_) Subgroup.le_normalizer)
  · exact sec10C_mem_normalizer_of_comm fun a ha => hc a ha b hb
  · exact sec10C_mem_normalizer_of_comm fun b hb => (hc a ha b hb).symm

theorem sec10C_normalizer_pocket [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {l : G}
    (hl : l ∈ L ⊓ centralizer ({z} : Set G)) (hn : l ∈ normalizer (K1 : Set G)) :
    l ∈ K1 ⊔ K2 := by
  obtain ⟨K1', K2', -, -, hne', huniq, -, hsup', -, hswap⟩ :=
    hP5 G L hpsp z hctx.toSec10Z.pocket
  by_contra hnot
  have hK : K1 ⊔ K2 = K1' ⊔ K2' := (sec10K0_pockets_sup hP5 hpsp hctx).trans hsup'
  have hl' : CFSG.conjugate K1' l = K2' := hswap l hl (by rw [← hK]; exact hnot)
  have hinj : Function.Injective (fun K : Subgroup G => CFSG.conjugate K l) :=
    Subgroup.map_injective (f := (MulAut.conj l⁻¹).toMonoidHom) (MulAut.conj l⁻¹).injective
  have hconj1 : CFSG.conjugate K1 l = K1 := sec10C_conjugate_eq_of_normalizer hn
  rcases huniq K1 hctx.pocket1 with h1 | h1
  · rw [h1] at hconj1
    exact hne' (hconj1.symm.trans hl')
  · rw [h1] at hconj1
    exact hne' (hinj (hl'.trans hconj1.symm))

theorem sec10C_no_swap [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {s : G}
    (hs : s ∈ S) (hs2 : s * s = 1)
    (hN : s ∈ normalizer ((K1 ⊔ oddCoreIn (secK0 t z) : Subgroup G) : Set G)) :
    s ∈ normalizer (K1 : Set G) ∧ s ∈ normalizer (K2 : Set G) := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  rcases sec10T_pocket_dichotomy hP5 hb hctx hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨sec10C_mem_normalizer_of_invol hs2 h1, sec10C_mem_normalizer_of_invol hs2 h2⟩
  · exfalso
    have hOC := sec10L104_oddK0_le_centralizer hK0 h36 hP5 hC5 hb hctx
    have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
      inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
    have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
    have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
    have hK21 : K2 ≤ K1 := by
      intro y hy
      have hyP : y ∈ K1 ⊔ oddCoreIn (secK0 t z) :=
        (Subgroup.mem_normalizer_iff.mp hN y).mpr
          (Subgroup.mem_sup_left (h2 y hy))
      have hcomm : ∀ k ∈ K1, ∀ o ∈ oddCoreIn (secK0 t z), k * o = o * k := fun k hk o ho =>
        Subgroup.mem_centralizer_iff.mp (hOC ho) k (hK1L hk)
      obtain ⟨k, hk, o, ho, hyko⟩ := exists_mul_of_mem_sup_of_commute hcomm hyP
      have hoL : o ∈ L := by
        have : o = k⁻¹ * y := by rw [hyko]; group
        rw [this]
        exact L.mul_mem (L.inv_mem (hK1L hk)) (hK2L hy)
      have ho1 : o = 1 := by
        have : o ∈ L ⊓ centralizer (L : Set G) := ⟨hoL, hOC ho⟩
        rw [hLC] at this
        exact Subgroup.mem_bot.mp this
      rw [hyko, ho1, mul_one]
      exact hk
    have hK12 : K1 ≤ K2 := by
      intro x hx
      have hy : s * x * s⁻¹ ∈ K2 := h1 x hx
      have hy1 : s * x * s⁻¹ ∈ K1 := hK21 hy
      have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      have e : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hs']
        calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
          _ = x := by rw [hs2]; group
      have := h1 _ hy1
      rwa [e] at this
    exact hctx.ne (le_antisymm hK12 hK21)

theorem sec10C_inner_in_W [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10)
    (h106 : Asc82Lemma106) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {x : G} (hxS : x ∈ S) (hx2 : x * x = 1)
    (hxLC : x ∈ L ⊔ centralizer (L : Set G)) (hn1 : x ∈ normalizer (K1 : Set G)) :
    x ∈ secW t K1 K2 := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hcomm : ∀ l ∈ L, ∀ c ∈ centralizer (L : Set G), l * c = c * l := fun l hl c hc =>
    Subgroup.mem_centralizer_iff.mp hc l hl
  obtain ⟨l, hlL, c, hcC, hxlc⟩ := exists_mul_of_mem_sup_of_commute hcomm hxLC
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
  have hl2 : l * l = 1 := by
    have hcc : c * l = l * c := (hcomm l hlL c hcC).symm
    have e : (l * c) * (l * c) = (l * l) * (c * c) := by
      calc (l * c) * (l * c) = l * (c * l) * c := by group
        _ = l * (l * c) * c := by rw [hcc]
        _ = (l * l) * (c * c) := by group
    have h1 : (l * l) * (c * c) = 1 := by rw [← e, ← hxlc]; exact hx2
    have h2 : l * l = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hcc2 : (c * c)⁻¹ ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).mul_mem hcC hcC)
    have hmem : l * l ∈ L ⊓ centralizer (L : Set G) :=
      ⟨L.mul_mem hlL hlL, by rw [h2]; exact hcc2⟩
    rw [hLC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hlz : l * z = z * l := by
    have hxz : x * z = z * x := hctx.central x hxS
    have hcz : c * z = z * c := (hcomm z hzL c hcC).symm
    rw [hxlc] at hxz
    have h1 : l * (c * z) = z * (l * c) := by simpa only [mul_assoc] using hxz
    rw [hcz] at h1
    have h2 : l * z * c = z * l * c := by simpa only [mul_assoc] using h1
    exact mul_right_cancel h2
  have hln1 : l ∈ normalizer (K1 : Set G) := by
    refine sec10C_mem_normalizer_of_invol hl2 fun y hy => ?_
    have hyL : y ∈ L := hK1L hy
    have hcy : c * y = y * c := (hcomm y hyL c hcC).symm
    have hxy : x * y * x⁻¹ = l * y * l⁻¹ := by
      rw [hxlc, mul_inv_rev]
      calc l * c * y * (c⁻¹ * l⁻¹) = l * (c * y * c⁻¹) * l⁻¹ := by group
        _ = l * y * l⁻¹ := by rw [hcy]; group
    rw [← hxy]
    exact (Subgroup.mem_normalizer_iff.mp hn1 y).mp hy
  have hlK : l ∈ K1 ⊔ K2 :=
    sec10C_normalizer_pocket hP5 hpsp hctx ⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr hlz⟩
      hln1
  have hlK0 : l ∈ secK0 t z := by
    obtain ⟨hK1, hK2, -⟩ := sec10D_K0_contains hK0 hctx
    exact sup_le hK1 hK2 hlK
  have hlQ : l ∈ secQ K1 K2 :=
    sec10T_two_elem_K0 hK0 h36 hP5 hC5 hb hctx hlK0 ⟨1, by simpa [pow_two] using hl2⟩
  have hlS : l ∈ S := (sec10J_Q_le hP5 hb hctx hlQ).1
  have hcS : c ∈ S := by
    have : c = l⁻¹ * x := by rw [hxlc]; group
    rw [this]
    exact S.mul_mem (S.inv_mem hlS) hxS
  have hct : c ∈ zpowers t := by
    have := h106 G t L S z K1 K2 hctx
    rw [← this]
    exact ⟨hcC, hcS⟩
  rw [hxlc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlQ) (Subgroup.mem_sup_right hct)

end CFSG.OddStandard.SmallF3.Omega

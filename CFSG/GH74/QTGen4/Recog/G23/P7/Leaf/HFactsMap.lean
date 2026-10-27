module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsSylow

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open

namespace HFactsAux

variable {X G : Type} [Group X] [Group G]

theorem map_centralizer_inf_range (ι : X →* G) (hι : Function.Injective ι) (s : Set X) :
    Subgroup.centralizer (ι '' s) ⊓ ι.range = (Subgroup.centralizer s).map ι := by
  ext x
  constructor
  · rintro ⟨hx1, y, rfl⟩
    refine ⟨y, fun h hh => ?_, rfl⟩
    have := hx1 (ι h) ⟨h, hh, rfl⟩
    exact hι (by simpa only [map_mul] using this)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ⟨y, rfl⟩⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hy h hh]

theorem map_normalizer_inf_range (ι : X →* G) (hι : Function.Injective ι) (s : Set X) :
    Subgroup.normalizer (ι '' s) ⊓ ι.range = (Subgroup.normalizer s).map ι := by
  ext x
  constructor
  · rintro ⟨hx1, y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    show y ∈ Subgroup.normalizer s
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have := Subgroup.mem_set_normalizer_iff.mp hx1 (ι n)
    have e : ι y * ι n * (ι y)⁻¹ = ι (y * n * y⁻¹) := by simp only [map_mul, map_inv]
    rw [e] at this
    rw [← hι.mem_set_image, this, hι.mem_set_image]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ⟨y, rfl⟩⟩
    show ι y ∈ Subgroup.normalizer (ι '' s)
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    by_cases hn : n ∈ ι.range
    · obtain ⟨m, rfl⟩ := hn
      have := Subgroup.mem_set_normalizer_iff.mp hy m
      have e : ι y * ι m * (ι y)⁻¹ = ι (y * m * y⁻¹) := by simp only [map_mul, map_inv]
      rw [e, hι.mem_set_image, hι.mem_set_image]
      exact this
    · constructor
      · rintro ⟨m, _, rfl⟩
        exact absurd ⟨m, rfl⟩ hn
      · rintro ⟨t, _, ht⟩
        refine absurd ⟨y⁻¹ * t * y, ?_⟩ hn
        have : n = (ι y)⁻¹ * ι t * ι y := by rw [ht]; group
        rw [this]
        simp only [map_mul, map_inv]

theorem map_cent_single (ι : X →* G) (hι : Function.Injective ι) (u : X) :
    Subgroup.centralizer ({ι u} : Set G) ⊓ ι.range =
      (Subgroup.centralizer ({u} : Set X)).map ι := by
  rw [← map_centralizer_inf_range ι hι, Set.image_singleton]

theorem map_norm_zpowers (ι : X →* G) (hι : Function.Injective ι) (u : X) :
    Subgroup.normalizer (Subgroup.zpowers (ι u) : Set G) ⊓ ι.range =
      (Subgroup.normalizer (Subgroup.zpowers u : Set X)).map ι := by
  rw [← map_normalizer_inf_range ι hι, ← MonoidHom.map_zpowers, Subgroup.coe_map]

theorem map_cent_set (ι : X →* G) (hι : Function.Injective ι) (S : Subgroup X) :
    Subgroup.centralizer (S.map ι : Set G) ⊓ ι.range =
      (Subgroup.centralizer (S : Set X)).map ι := by
  rw [← map_centralizer_inf_range ι hι, Subgroup.coe_map]

theorem map_norm_set (ι : X →* G) (hι : Function.Injective ι) (S : Subgroup X) :
    Subgroup.normalizer (S.map ι : Set G) ⊓ ι.range = (Subgroup.normalizer (S : Set X)).map ι := by
  rw [← map_normalizer_inf_range ι hι, Subgroup.coe_map]

theorem isElemAbelian_map (ι : X →* G) {p : ℕ} {E : Subgroup X} (h : IsElemAbelian p E) :
    IsElemAbelian p (E.map ι) := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    apply Subtype.ext
    show (u : G) * v = v * u
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, Subgroup.mul_comm_of_mem_isMulCommutative E hx hy]
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hp x hx, map_one]

end HFactsAux

open HFactsAux

variable {X G : Type} [Group X] [Group G]

theorem HFacts.of_map {ι : X →* G} (hι : Function.Injective ι) {a : Fin 6 → X}
    {H₁X H₂X : Subgroup X} {e : Fin 6 → G} {H H₁ H₂ : Subgroup G}
    (h0 : e 0 = ι (a 0)) (h1 : e 1 = ι (a 1)) (h2 : e 2 = ι (a 2)) (h4 : e 4 = ι (a 4))
    (hH : H = ι.range) (hH₁ : H₁ = H₁X.map ι) (hH₂ : H₂ = H₂X.map ι)
    (hX : HFacts (⊤ : Subgroup X) H₁X H₂X a) : HFacts H H₁ H₂ e := by
  have hz : zOf e = ι (zOf a) := by
    simp only [zOf, h0, h1, map_pow, map_mul]
  have hP : Psub e = (Psub a).map ι := by
    simp only [Psub, h0, h2, MonoidHom.map_closure, Set.image_pair]
  have hE : Esub e = (Esub a).map ι := by
    simp only [Esub, h4, hz, MonoidHom.map_closure, Set.image_pair]
  have hrange : (⊤ : Subgroup X).map ι = ι.range := (MonoidHom.range_eq_map ι).symm
  have hPle : Psub e ≤ H := by
    rw [hP, hH]; exact Subgroup.map_le_range ι _
  have cardH : Nat.card H = 576 := by
    rw [hH, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hι]; exact hX.card_H
  have cardP : Nat.card (Psub e) = 9 := by
    rw [hP, Subgroup.card_map_of_injective hι]; exact hX.card_P
  have elemP : IsElemAbelian 3 (Psub e) := by
    rw [hP]; exact isElemAbelian_map ι hX.elem_P
  have e0 : ({e 0} : Set G) = {ι (a 0)} := by rw [h0]
  have e2 : ({e 2} : Set G) = {ι (a 2)} := by rw [h2]
  have e4 : ({e 4} : Set G) = {ι (a 4)} := by rw [h4]
  refine
    { card_H := cardH
      card_P := cardP
      elem_P := elemP
      cent₁ := ?_
      disj₁ := ?_
      cent₂ := ?_
      disj₂ := ?_
      norm₁ := ?_
      norm₂ := ?_
      centP := ?_
      normP := ?_
      centYp := ?_
      normYp := ?_
      centYm := ?_
      normYm := ?_
      invert₁ := ?_
      invert₂ := ?_
      conj_t₂ := ?_
      conj_t₁ := ?_
      centL₁ := ?_
      centL₂ := ?_
      invK := ?_
      card_cent_t := ?_
      odd_sub := fun S hS ho => odd_sub_of_card cardH hPle cardP S hS ho
      order3 := fun x hx h3' h1' => exists_conj_into_of_pow_three cardH hPle cardP hx h3' }
  · have := congrArg (Subgroup.map ι) hX.cent₁
    rw [inf_top_eq, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    rw [hH, hH₂, h0, map_cent_single ι hι, this]
  · rw [hH₂, h0, ← MonoidHom.map_zpowers, ← Subgroup.map_inf _ _ _ hι, hX.disj₁,
      Subgroup.map_bot]
  · have := congrArg (Subgroup.map ι) hX.cent₂
    rw [inf_top_eq, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    rw [hH, hH₁, h2, map_cent_single ι hι, this]
  · rw [hH₁, h2, ← MonoidHom.map_zpowers, ← Subgroup.map_inf _ _ _ hι, hX.disj₂,
      Subgroup.map_bot]
  · have := congrArg (Subgroup.map ι) hX.norm₁
    rw [inf_top_eq, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers] at this
    rw [hH, hH₂, h0, h4, map_norm_zpowers ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.norm₂
    rw [inf_top_eq, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers] at this
    rw [hH, hH₁, h2, h4, map_norm_zpowers ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.centP
    rw [inf_top_eq, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    rw [hH, hP, hz, map_cent_set ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.normP
    rw [inf_top_eq, Subgroup.map_sup] at this
    rw [hH, hP, hE, map_norm_set ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.centYp
    rw [inf_top_eq, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    have e02 : ({e 0 * e 2} : Set G) = {ι (a 0 * a 2)} := by rw [h0, h2, map_mul]
    rw [hH, e02, hP, hz, map_cent_single ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.normYp
    rw [inf_top_eq, Subgroup.map_sup] at this
    have e02 : e 0 * e 2 = ι (a 0 * a 2) := by rw [h0, h2, map_mul]
    rw [hH, e02, hP, hE, map_norm_zpowers ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.centYm
    rw [inf_top_eq, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    have e02 : ({e 0 * (e 2)⁻¹} : Set G) = {ι (a 0 * (a 2)⁻¹)} := by
      rw [h0, h2, map_mul, map_inv]
    rw [hH, e02, hP, hz, map_cent_single ι hι, this]
  · have := congrArg (Subgroup.map ι) hX.normYm
    rw [inf_top_eq, Subgroup.map_sup] at this
    have e02 : e 0 * (e 2)⁻¹ = ι (a 0 * (a 2)⁻¹) := by rw [h0, h2, map_mul, map_inv]
    rw [hH, e02, hP, hE, map_norm_zpowers ι hι, this]
  · intro c hc heq
    rw [hH, h0, map_cent_single ι hι] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    apply hX.invert₁ c' ⟨hc', Subgroup.mem_top _⟩
    apply hι
    rw [h2] at heq
    simpa only [map_mul, map_inv] using heq
  · intro c hc heq
    rw [hH, h2, map_cent_single ι hι] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    apply hX.invert₂ c' ⟨hc', Subgroup.mem_top _⟩
    apply hι
    rw [h0] at heq
    simpa only [map_mul, map_inv] using heq
  · obtain ⟨g, hg, hgeq⟩ := hX.conj_t₂
    refine ⟨ι g, ?_, ?_⟩
    · rw [hH₂, h4, ← MonoidHom.map_zpowers, ← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem ι hg
    · rw [h4, hz]
      simpa only [map_mul, map_inv] using congrArg ι hgeq
  · obtain ⟨g, hg, hgeq⟩ := hX.conj_t₁
    refine ⟨ι g, ?_, ?_⟩
    · rw [hH₁, h4, ← MonoidHom.map_zpowers, ← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem ι hg
    · rw [h4, hz]
      simpa only [map_mul, map_inv] using congrArg ι hgeq
  · have hmap := congrArg (Subgroup.map ι) hX.centL₁
    rw [Subgroup.map_inf _ _ _ hι, ← map_cent_single ι hι, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    rw [hH₁, h0, hz]
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.map_le_range ι H₁X)] at hmap
    exact hmap
  · have hmap := congrArg (Subgroup.map ι) hX.centL₂
    rw [Subgroup.map_inf _ _ _ hι, ← map_cent_single ι hι, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    rw [hH₂, h2, hz]
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.map_le_range ι H₂X)] at hmap
    exact hmap
  · intro u hu hord huz u' hu' hord' hu'z
    rw [hH₁, hH₂, ← Subgroup.map_sup] at hu hu'
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hu'
    rw [hz] at huz hu'z
    obtain ⟨g, -, hg⟩ := hX.invK x hx (by rwa [orderOf_injective ι hι] at hord)
      (fun h => huz (by rw [h])) x' hx' (by rwa [orderOf_injective ι hι] at hord')
      (fun h => hu'z (by rw [h]))
    refine ⟨ι g, by rw [hH]; exact ⟨g, rfl⟩, ?_⟩
    simpa only [map_mul, map_inv] using congrArg ι hg
  · have := hX.card_cent_t
    rw [inf_top_eq] at this
    rw [hH, h4, map_cent_single ι hι, Subgroup.card_map_of_injective hι]
    exact this

end CFSG.GH74.QTGen4.Recog.G23.P7

module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Model
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Aux
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

open Subgroup CFSG CFSG.ABGLocalTools

section Conj

variable {G : Type} [Group G]

theorem exists_mem_range_conj {Ψ : M35 →* G} {g : G} (hg : g ∈ normalizer (Ψ.range : Set G))
    (m : M35) : ∃ m' : M35, Ψ m' = g * Ψ m * g⁻¹ :=
  (Subgroup.mem_normalizer_iff.1 hg (Ψ m)).1 ⟨m, rfl⟩

theorem card_le_of_conj_maps {Ψ : M35 →* G} (hΨ : Function.Injective Ψ) (g : G) (A B : Finset M35)
    (h : ∀ a ∈ A, ∃ b ∈ B, Ψ b = g * Ψ a * g⁻¹) : A.card ≤ B.card := by
  classical
  choose! φ hφB hφ using h
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a ha a' ha' haa'
  apply hΨ
  have h1 := hφ a ha
  have h2 := hφ a' ha'
  rw [haa'] at h1
  have h3 : g * Ψ a * g⁻¹ = g * Ψ a' * g⁻¹ := by rw [← h1, ← h2]
  simpa using h3

theorem centralizer_conj_eq (x g : G) :
    centralizer ({g⁻¹ * x * g} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    refine ⟨g * y * g⁻¹, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : g * y * g⁻¹ * x = x * (g * y * g⁻¹) := by
      calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hy]
        _ = x * (g * y * g⁻¹) := by group
    exact h1
  · rintro ⟨z, hz, rfl⟩
    rw [mem_centralizer_singleton_iff] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * z * g * (g⁻¹ * x * g) = g⁻¹ * (z * x) * g := by group
      _ = g⁻¹ * (x * z) * g := by rw [hz]
      _ = g⁻¹ * x * g * (g⁻¹ * z * g) := by group

theorem isSylowOf_map_conj [Finite G] {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map _, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem mem_cent {m c : M35} : c ∈ cent m ↔ c * m = m * c := by
  unfold cent
  simp

theorem mem_zc {m z : M35} :
    z ∈ zc m ↔ z * m = m * z ∧ ∀ c : M35, c * m = m * c → z * c = c * z := by
  unfold zc
  simp only [Finset.mem_filter, mem_cent]

theorem mem_cent_of_conj {Ψ : M35 →* G} (hΨ : Function.Injective Ψ) {g : G} {a a' m m' : M35}
    (ha' : Ψ a' = g * Ψ a * g⁻¹) (hm' : Ψ m' = g * Ψ m * g⁻¹) (h : a ∈ cent m) :
    a' ∈ cent m' := by
  rw [mem_cent] at h ⊢
  apply hΨ
  rw [map_mul, map_mul, ha', hm']
  have h' : Ψ a * Ψ m = Ψ m * Ψ a := by rw [← map_mul, ← map_mul, h]
  calc g * Ψ a * g⁻¹ * (g * Ψ m * g⁻¹) = g * (Ψ a * Ψ m) * g⁻¹ := by group
    _ = g * (Ψ m * Ψ a) * g⁻¹ := by rw [h']
    _ = g * Ψ m * g⁻¹ * (g * Ψ a * g⁻¹) := by group

end Conj

section Main

variable {G : Type} [Group G] [Finite G]

theorem range_eq_of_sylow {Ψ : M35 →* G} (hΨ : Function.Injective Ψ) {W : Subgroup G}
    (hW2 : IsPGroup 2 ↥W) (hΨW : ∀ m, Ψ m ∈ W)
    (hVsyl : IsSylowOf 2 (Vsub.map Ψ)
      (centralizer ({Ψ (inl' (DihedralGroup.r 2) 1)} : Set G))) : Ψ.range = W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : G := Ψ (inl' (DihedralGroup.r 2) 1) with hf
  set b : G := Ψ topg with hb
  have hN₁W : Ψ.range ≤ W := by
    rintro _ ⟨m, rfl⟩
    exact hΨW m
  have hVN : Vsub.map Ψ ≤ Ψ.range := by
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  have hVW : Vsub.map Ψ ≤ W := hVN.trans hN₁W
  have hbN : b ∈ Ψ.range := ⟨topg, rfl⟩
  have hCWf : ∀ y ∈ W, y * f = f * y → y ∈ Vsub.map Ψ := by
    intro y hyW hyf
    have hle : Vsub.map Ψ ≤ W ⊓ centralizer ({f} : Set G) := le_inf hVW hVsyl.le
    have hQ : IsPGroup 2 ↥(W ⊓ centralizer ({f} : Set G)) := hW2.to_inf_left
    have heq := hVsyl.eq_of_le hle inf_le_right hQ
    rw [← heq]
    exact ⟨hyW, mem_centralizer_singleton_iff.2 hyf⟩
  have hff : f * f = 1 := by rw [hf, ← map_mul, inl'_f_sq, map_one]
  have hnorm : ∀ g ∈ W, g ∈ normalizer (Ψ.range : Set G) → g ∈ Ψ.range := by
    intro g hgW hgN
    have hgN' : g⁻¹ ∈ normalizer (Ψ.range : Set G) := (normalizer (Ψ.range : Set G)).inv_mem hgN
    obtain ⟨m', hm'⟩ := exists_mem_range_conj hgN (inl' (DihedralGroup.r 2) 1)
    rw [← hf] at hm'
    have hm'2 : m' * m' = 1 := by
      apply hΨ
      rw [map_mul, hm', map_one]
      calc g * f * g⁻¹ * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
        _ = 1 := by rw [hff]; group
    have hcard1 : (cent (inl' (DihedralGroup.r 2) 1)).card ≤ (cent m').card := by
      apply card_le_of_conj_maps hΨ g
      intro a ha
      obtain ⟨a', ha'⟩ := exists_mem_range_conj hgN a
      exact ⟨a', mem_cent_of_conj hΨ ha' (by rw [hm', hf]) ha, ha'⟩
    have hcard2 : (cent m').card ≤ (cent (inl' (DihedralGroup.r 2) 1)).card := by
      apply card_le_of_conj_maps hΨ g⁻¹
      intro a ha
      obtain ⟨a', ha'⟩ := exists_mem_range_conj hgN' a
      refine ⟨a', ?_, ha'⟩
      refine mem_cent_of_conj hΨ ha' ?_ ha
      rw [hm', hf]
      group
    have hcard : (cent m').card = 64 := by
      have := cent_f
      omega
    rcases big_inv m' hm'2 hcard with h | h
    ·
      rw [h] at hm'
      have hgf : g * f = f * g := by
        calc g * f = g * f * g⁻¹ * g := by group
          _ = f * g := by rw [← hm']
      exact hVN (hCWf g hgW hgf)
    · rw [h] at hm'
      have hbf : Ψ (inl' 1 (DihedralGroup.r 2)) = b * f * b⁻¹ := by
        rw [← topg_conj_inl' (DihedralGroup.r 2) 1, map_mul, map_mul, map_inv]
      have e : g * f * g⁻¹ = b * f * b⁻¹ := by rw [← hm', hbf]
      have hbgf : b⁻¹ * g * f = f * (b⁻¹ * g) := by
        calc b⁻¹ * g * f = b⁻¹ * (g * f * g⁻¹) * g := by group
          _ = b⁻¹ * (b * f * b⁻¹) * g := by rw [e]
          _ = f * (b⁻¹ * g) := by group
      have hbW : b ∈ W := hN₁W hbN
      have hbg : b⁻¹ * g ∈ Vsub.map Ψ := hCWf _ (W.mul_mem (W.inv_mem hbW) hgW) hbgf
      have hgb : g = b * (b⁻¹ * g) := by group
      rw [hgb]
      exact Ψ.range.mul_mem hbN (hVN hbg)
  have hWeq : Ψ.range = W := by
    by_contra hne
    obtain ⟨g, hgW, hgN, hg⟩ := Thm1G33.exists_mem_normalizer_not_mem hN₁W hne hW2
    exact hg (hnorm g hgW hgN)
  exact hWeq

theorem core35 (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    {Ψ : M35 →* G} (hΨ : Function.Injective Ψ) {W : Subgroup G} (hW : IsSylowOf 2 W ⊤)
    (hΨW : ∀ m, Ψ m ∈ W)
    (hVsyl : IsSylowOf 2 (Vsub.map Ψ)
      (centralizer ({Ψ (inl' (DihedralGroup.r 2) 1)} : Set G)))
    {s : D8} (hs : alphaFn s = Multiplicative.ofAdd 1)
    (hT32 : ∀ S : Subgroup G, S ≤ centralizer ({Ψ (inl' s 1)} : Set G) → IsPGroup 2 ↥S →
      Nat.card ↥S ≤ 32) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥W := hW.isPGroup
  have hWeq : Ψ.range = W := range_eq_of_sylow hΨ hW2 hΨW hVsyl
  set U : Subgroup G := lam.ker.map Ψ with hU
  have hUW : U ≤ W := by
    rintro _ ⟨m, -, rfl⟩
    exact hΨW m
  have hUidx : U.relIndex W = 2 := by
    have hWmap : W = (⊤ : Subgroup M35).map Ψ := by rw [← hWeq, MonoidHom.range_eq_map]
    rw [hWmap, hU, Subgroup.relIndex_map_map_of_injective _ _ hΨ, Subgroup.relIndex_top_right,
      Subgroup.index_ker, MonoidHom.range_eq_top.2 lam_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hTidx : ¬ 2 ∣ W.index := by
    have := (isSylowOf_iff.1 hW).2.2
    rwa [Subgroup.relIndex_top_right] at this
  set x : G := Ψ (inl' s 1) with hx
  have hxW : x ∈ W := hΨW _
  have hxx : x * x = 1 := by rw [hx, ← map_mul, inl'_refl_sq s hs, map_one]
  have hxU : x ∉ U := by
    rintro ⟨m, hm, hmx⟩
    have hm' : m = inl' s 1 := hΨ hmx
    rw [hm'] at hm
    have h1 : lam (inl' s 1) = 1 := hm
    rw [lam_inl', hs] at h1
    have ha1 : alphaFn (1 : D8) = 1 := rfl
    rw [ha1, mul_one] at h1
    simp at h1
  have hx1 : x ≠ 1 := fun h => hxU (h ▸ U.one_mem)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  have hmin : ∀ y ∈ W, y ∉ U → orderOf x ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have hpos : 0 < orderOf y := orderOf_pos y
    rw [hx2]
    omega
  obtain ⟨g, hgU, hgext⟩ := EvenSporTransfer.exists_extremal_conj_of_thompson hW2 hTidx hUW hUidx
    hxW hxU hmin hno
  obtain ⟨mt, hmt1, hmt⟩ := hgU
  have hlam : lam mt = 1 := hmt1
  have hmtsq : mt * mt = 1 := by
    apply hΨ
    rw [map_mul, hmt, map_one]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hxx]; group
  set T' : Subgroup G := W ⊓ centralizer ({x} : Set G) with hT'
  have hT'le : T' ≤ centralizer ({x} : Set G) := inf_le_right
  have hT'2 : IsPGroup 2 ↥T' := hW2.to_inf_left
  have hmemT' : ∀ y, y ∈ T' ↔ ∃ c : M35, c * inl' s 1 = inl' s 1 * c ∧ Ψ c = y := by
    intro y
    constructor
    · rintro ⟨hyW, hyx⟩
      rw [← hWeq] at hyW
      obtain ⟨c, rfl⟩ := hyW
      refine ⟨c, ?_, rfl⟩
      apply hΨ
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hyx
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hΨW c, mem_centralizer_singleton_iff.2 ?_⟩
      rw [hx, ← map_mul, ← map_mul, hc]
  have hcard32 : 32 ≤ Nat.card ↥T' := by
    have hsub : Ψ '' (cent (inl' s 1) : Set M35) ⊆ (T' : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hmemT' _).2 ⟨c, mem_cent.1 (Finset.mem_coe.1 hc), rfl⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ hΨ, Set.ncard_coe_finset, cent_x s hs] at h1
    have h2 : Nat.card ↥T' = (T' : Set G).ncard := Nat.card_coe_set_eq (T' : Set G)
    omega
  have hT'syl : IsSylowOf 2 T' (centralizer ({x} : Set G)) := by
    obtain ⟨S₀, hS₀, hT'S₀⟩ := EvenSporTransfer.exists_isSylowOf_ge hT'le hT'2
    have h1 : Nat.card ↥S₀ ≤ 32 := hT32 S₀ hS₀.le hS₀.isPGroup
    have h2 : Nat.card ↥T' ≤ Nat.card ↥S₀ := Subgroup.card_le_of_le hT'S₀
    have heq : T' = S₀ := Subgroup.eq_of_le_of_card_ge hT'S₀ (by omega)
    rw [heq]
    exact hS₀
  have hP₁ : IsSylowOf 2 (T'.map (MulAut.conj g⁻¹).toMonoidHom)
      (centralizer ({g⁻¹ * x * g} : Set G)) := by
    rw [centralizer_conj_eq]
    exact isSylowOf_map_conj hT'syl g⁻¹
  have hA : IsSylowOf 2 (W ⊓ centralizer ({g⁻¹ * x * g} : Set G))
      (centralizer ({g⁻¹ * x * g} : Set G)) := isSylowOf_iff.2 hgext
  obtain ⟨k, hkC, hk⟩ := IsSylowOf.exists_mem_conj hP₁ hA
  set h₀ : G := g * k⁻¹ with hh₀
  have hK1 : ∀ y ∈ W ⊓ centralizer ({g⁻¹ * x * g} : Set G), h₀ * y * h₀⁻¹ ∈ T' := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := (hk y).1 hy
    have hzy' : g⁻¹ * z * g = k⁻¹ * y * k := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hzy
    have : h₀ * y * h₀⁻¹ = z := by
      rw [hh₀]
      calc g * k⁻¹ * y * (g * k⁻¹)⁻¹ = g * (k⁻¹ * y * k) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hzy']
        _ = z := by group
    rw [this]
    exact hz
  have hK2 : ∀ z ∈ T', h₀⁻¹ * z * h₀ ∈ W ⊓ centralizer ({g⁻¹ * x * g} : Set G) := by
    intro z hz
    refine (hk _).2 ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hh₀]
    group
  have hconj : ∀ z ∈ T', ∃ b' : M35, b' * mt = mt * b' ∧ Ψ b' = h₀⁻¹ * z * h₀ := by
    intro z hz
    obtain ⟨hyW, hyC⟩ := hK2 z hz
    rw [← hWeq] at hyW
    obtain ⟨b', hb'⟩ := hyW
    refine ⟨b', ?_, hb'⟩
    apply hΨ
    rw [map_mul, map_mul, hb', hmt]
    exact mem_centralizer_singleton_iff.1 hyC
  have hcent : 32 ≤ (cent mt).card := by
    have h1 := card_le_of_conj_maps hΨ h₀⁻¹ (cent (inl' s 1)) (cent mt) (fun a ha => by
      obtain ⟨b', hb', hΨb'⟩ := hconj (Ψ a) ((hmemT' _).2 ⟨a, mem_cent.1 ha, rfl⟩)
      exact ⟨b', mem_cent.2 hb', by rw [hΨb', inv_inv]⟩)
    rw [cent_x s hs] at h1
    exact h1
  have hzc : (zc (inl' s 1)).card ≤ (zc mt).card := by
    apply card_le_of_conj_maps hΨ h₀⁻¹
    intro a ha
    obtain ⟨hax, hacent⟩ := mem_zc.1 ha
    obtain ⟨b', hb', hΨb'⟩ := hconj (Ψ a) ((hmemT' _).2 ⟨a, hax, rfl⟩)
    refine ⟨b', mem_zc.2 ⟨hb', ?_⟩, by rw [hΨb', inv_inv]⟩
    intro c hc
    have hcA : Ψ c ∈ W ⊓ centralizer ({g⁻¹ * x * g} : Set G) :=
      ⟨hΨW c, mem_centralizer_singleton_iff.2 (by rw [← hmt, ← map_mul, ← map_mul, hc])⟩
    have hT'c : h₀ * Ψ c * h₀⁻¹ ∈ T' := hK1 _ hcA
    obtain ⟨c₁, hc₁, hΨc₁⟩ := (hmemT' _).1 hT'c
    have h1 := hacent c₁ hc₁
    apply hΨ
    rw [map_mul, map_mul, hΨb']
    have h2 : Ψ a * Ψ c₁ = Ψ c₁ * Ψ a := by rw [← map_mul, ← map_mul, h1]
    rw [hΨc₁] at h2
    calc h₀⁻¹ * Ψ a * h₀ * Ψ c = h₀⁻¹ * (Ψ a * (h₀ * Ψ c * h₀⁻¹)) * h₀ := by group
      _ = h₀⁻¹ * ((h₀ * Ψ c * h₀⁻¹) * Ψ a) * h₀ := by rw [h2]
      _ = Ψ c * (h₀⁻¹ * Ψ a * h₀) := by group
  have hlt := MC mt hlam hmtsq hcent
  have h8 := zc_x s hs
  omega

end Main

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end

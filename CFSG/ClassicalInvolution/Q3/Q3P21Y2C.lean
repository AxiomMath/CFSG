module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y2B
public import CFSG.ClassicalInvolution.Q3.Q3P21L3
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.Q3WASTAsm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Comp

theorem conjSub_map_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {n : K}
    {A : Subgroup K} (h : conjSub n A = A) : conjSub (e n) (A.map e.toMonoidHom) =
      A.map e.toMonoidHom := by
  ext g
  rw [mem_conjSub_iff, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have h1 : e.symm ((e n)⁻¹ * g * e n) = n⁻¹ * e.symm g * n := by simp
  rw [h1, ← mem_conjSub_iff, h]

theorem parity_comp3 {X : Type} [Group X] (cc : CompData)
    (hk : cc = CompData.model .POmegaPlus 4) (φ : cc.G →* X)
    (hφ : φ.ker ≤ Subgroup.center cc.G) (τ : X ≃* X) (hτr : ∀ k, τ (φ k) ∈ φ.range)
    {A B C C' N : Subgroup cc.G} (hA : A ∈ cc.fund) (hB : B ∈ cc.fund) (hC : C ∈ cc.fund)
    (hC' : C' ∈ cc.fund) (hN : N ∈ cc.fund) (hAB : A ≠ B) (hcAB : Commutes A B) (hCC' : C ≠ C')
    (hcAC : Commutes A C) (hcAC' : Commutes A C') (hcBC : Commutes B C)
    (hcBC' : Commutes B C') {n : cc.G} (hn : n ∈ N) (hn2 : n * n = 1) (hn1 : n ≠ 1)
    (hnA : conjSub n A = A) (hnC : conjSub n C = C) (hτA : ∀ r ∈ A, τ (φ r) = φ r)
    (hτB : ∀ r ∈ B, τ (φ r) = φ r) (hτC : ∀ r ∈ C, τ (φ r) = φ (n * r * n⁻¹))
    (hτC' : ∀ r ∈ C', τ (φ r) = φ (n * r * n⁻¹)) {xC : cc.G} (hxC : xC ∈ C)
    (hxC2 : xC * xC = 1) (hxC1 : xC ≠ 1) :
    (∀ r ∈ N, τ (φ r) = φ r) ∨ (∀ r ∈ N, τ (φ (xC * r * xC⁻¹)) = φ r) := by
  subst hk
  have hm3 : 3 ≤ 4 := by norm_num
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  let ψ : spinGroup (quadPlus 4 (GaloisField 3 1)) →* X := φ.comp ι.toMonoidHom
  have hker' : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ φ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (hφ h1)
  have hτr' : ∀ k, τ (ψ k) ∈ ψ.range := by
    intro k
    obtain ⟨y, hy⟩ := hτr (ι k)
    exact ⟨ι.symm y, by simpa [ψ] using hy⟩
  have hψ : ∀ r, ψ (ι.symm r) = φ r := fun r => by simp [ψ]
  have key := parity_model3 ψ hker' τ hτr' (A := A.map ι.symm.toMonoidHom)
    (B := B.map ι.symm.toMonoidHom) (C := C.map ι.symm.toMonoidHom)
    (C' := C'.map ι.symm.toMonoidHom) (N := N.map ι.symm.toMonoidHom)
    (map_symm_mem_fund_iso hm3 hcι hA) (map_symm_mem_fund_iso hm3 hcι hB)
    (map_symm_mem_fund_iso hm3 hcι hC) (map_symm_mem_fund_iso hm3 hcι hC')
    (map_symm_mem_fund_iso hm3 hcι hN)
    (fun h => hAB (Subgroup.map_injective ι.symm.injective h))
    ((commutes_map_equiv ι.symm).mpr hcAB)
    (fun h => hCC' (Subgroup.map_injective ι.symm.injective h))
    ((commutes_map_equiv ι.symm).mpr hcAC) ((commutes_map_equiv ι.symm).mpr hcAC')
    ((commutes_map_equiv ι.symm).mpr hcBC) ((commutes_map_equiv ι.symm).mpr hcBC')
    (n := ι.symm n) ⟨n, hn, rfl⟩ (by rw [← map_mul, hn2, map_one])
    (fun h => hn1 (ι.symm.injective (by rw [h, map_one])))
    (conjSub_map_equiv ι.symm hnA) (conjSub_map_equiv ι.symm hnC)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm r)
      rw [hψ]
      exact hτA r hr)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm r)
      rw [hψ]
      exact hτB r hr)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm n * ι.symm r * (ι.symm n)⁻¹)
      rw [hψ, ← map_inv, ← map_mul, ← map_mul, hψ]
      exact hτC r hr)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm n * ι.symm r * (ι.symm n)⁻¹)
      rw [hψ, ← map_inv, ← map_mul, ← map_mul, hψ]
      exact hτC' r hr)
    (xC := ι.symm xC) ⟨xC, hxC, rfl⟩ (by rw [← map_mul, hxC2, map_one])
    (fun h => hxC1 (ι.symm.injective (by rw [h, map_one])))
  rcases key with h | h
  · left
    intro r hr
    have := h (ι.symm r) ⟨r, hr, rfl⟩
    rwa [hψ] at this
  · right
    intro r hr
    have := h (ι.symm r) ⟨r, hr, rfl⟩
    rw [show ι.symm xC * ι.symm r * (ι.symm xC)⁻¹ = ι.symm (xC * r * xC⁻¹) by simp, hψ, hψ]
      at this
    exact this

end Comp

section Element

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {ι : Type}

theorem conjSub_eq_of_normalizes3 {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hpc : PowCop3 (D.kind i)) {L : Subgroup G} {R : Subgroup (D.kind i).G}
    (hLR : Corr3 Ω x D i L R) {t : G} (htY : t ∈ locLayer Ω x) {n : (D.kind i).G}
    (hn : D.hom i n = locMk Ω x ⟨t, htY⟩) (htL : conjSub t L = L) : conjSub n R = R := by
  set m : locQuot Ω x := locMk Ω x ⟨t, htY⟩ with hm
  have hconj : (locImg Ω x L).map (MulAut.conj m).toMonoidHom = locImg Ω x L := by
    rw [← locImg_conjSub_layer L ⟨t, htY⟩, show conjSub ((⟨t, htY⟩ : ↥(locLayer Ω x)) : G) L = L
      from htL]
  have hiff : ∀ g, g ∈ locImg Ω x L ↔ m * g * m⁻¹ ∈ locImg Ω x L := by
    intro g
    constructor
    · intro hg
      have : m * g * m⁻¹ ∈ (locImg Ω x L).map (MulAut.conj m).toMonoidHom :=
        ⟨g, hg, by simp [MulAut.conj_apply]⟩
      rwa [hconj] at this
    · intro hg
      rw [← hconj] at hg
      obtain ⟨g', hg', hgg⟩ := hg
      have h1 : m * g' * m⁻¹ = m * g * m⁻¹ := by simpa [MulAut.conj_apply] using hgg
      have h2 : g' = g := mul_left_cancel (mul_right_cancel h1)
      exact h2 ▸ hg'
  have hRim : R.map (D.hom i) = locImg Ω x L := hLR.2.2.symm
  refine eq_of_map_eq_of_pow3 (D.hom i) (D.ker_le_center i)
    (fun w hw => hpc.cop w (D.ker_le_center i hw)) (Pow3.conjSub n (hpc.pow3 R hLR.2.1))
    (hpc.pow3 R hLR.2.1) ?_
  ext g
  constructor
  · rintro ⟨r', hr', rfl⟩
    have hr'' : n⁻¹ * r' * n ∈ R := mem_conjSub_iff.mp hr'
    have h1 : D.hom i (n⁻¹ * r' * n) ∈ R.map (D.hom i) := ⟨_, hr'', rfl⟩
    rw [hRim, map_mul, map_mul, map_inv, hn] at h1
    have h2 := (hiff _).mp h1
    rw [show m * (m⁻¹ * D.hom i r' * m) * m⁻¹ = D.hom i r' by group] at h2
    rw [hRim]
    exact h2
  · intro hg
    have hg' : g ∈ locImg Ω x L := by rw [← hRim]; exact hg
    have h3 : m⁻¹ * g * m ∈ locImg Ω x L := by
      refine (hiff _).mpr ?_
      rw [show m * (m⁻¹ * g * m) * m⁻¹ = g by group]
      exact hg'
    rw [← hRim] at h3
    obtain ⟨r₁, hr₁, hr₁g⟩ := h3
    refine ⟨n * r₁ * n⁻¹, ?_, ?_⟩
    · refine mem_conjSub_iff.mpr ?_
      rw [show n⁻¹ * (n * r₁ * n⁻¹) * n = r₁ by group]
      exact hr₁
    · show D.hom i (n * r₁ * n⁻¹) = g
      rw [map_mul, map_mul, map_inv, hn, hr₁g]
      group

theorem locAut_eq_of_conj_eq3 (hΩ : ConjInvariant Ω) {y t : G} (hy : y * x * y⁻¹ = x)
    (ht : t * x * t⁻¹ = x) {L : Subgroup G} (h : ∀ k ∈ L, y * k * y⁻¹ = t * k * t⁻¹)
    {a : locQuot Ω x} (ha : a ∈ locImg Ω x L) : locAut hΩ hy a = locAut hΩ ht a := by
  obtain ⟨b, hb, rfl⟩ := ha
  show locMk Ω x (layerAut hΩ hy b) = locMk Ω x (layerAut hΩ ht b)
  congr 1
  apply Subtype.ext
  exact h b (Subgroup.mem_subgroupOf.mp hb)

theorem parity_element3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {c : ι}
    (hk : D.kind c = CompData.model .POmegaPlus 4) {K T K₂ K₂' N : Subgroup G}
    (hK : K ∈ compMembers3 Ω x D c) (hT : T ∈ compMembers3 Ω x D c)
    (hK₂ : K₂ ∈ compMembers3 Ω x D c) (hK₂' : K₂' ∈ compMembers3 Ω x D c)
    (hN : N ∈ compMembers3 Ω x D c) (hKT : K ≠ T) (hcKT : Commutes K T) (hK₂K₂' : K₂ ≠ K₂')
    (hcKK₂ : Commutes K K₂) (hcKK₂' : Commutes K K₂') (hcTK₂ : Commutes T K₂)
    (hcTK₂' : Commutes T K₂') {w t : G} (hw : IsClassicalMember3 K₂ w)
    (ht : IsClassicalMember3 N t) (hwx : w * x * w⁻¹ = x) (htx : t * x * t⁻¹ = x)
    (hwt : w * t = t * w) (htK : conjSub t K = K) (htK₂ : conjSub t K₂ = K₂) {y : G}
    (hyx : y * x * y⁻¹ = x) (hyK : K ≤ Subgroup.centralizer ({y} : Set G))
    (hyT : T ≤ Subgroup.centralizer ({y} : Set G))
    (hy₂ : ∀ k ∈ K₂, y * k * y⁻¹ = t * k * t⁻¹) (hy₂' : ∀ k ∈ K₂', y * k * y⁻¹ = t * k * t⁻¹) :
    y * t * y⁻¹ = t := by
  classical
  obtain ⟨-, hpc, -, hnc⟩ := component_facts (D.kind c) hk
  obtain ⟨RK, hRK⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK
  obtain ⟨RT, hRT⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hT
  obtain ⟨R₂, hR₂⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK₂
  obtain ⟨R₂', hR₂'⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK₂'
  obtain ⟨RN, hRN⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hN
  have htY : t ∈ locLayer Ω x := le_centralizingLayer hN.1 ht.mem
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hK₂.1 hw.mem
  set τ := locAut hΩ.conjInvariant hyx with hτ
  have hfix : ∀ {M : Subgroup G} {R : Subgroup (D.kind c).G}, Corr3 Ω x D c M R →
      M ≤ Subgroup.centralizer ({y} : Set G) → ∀ r ∈ R, τ (D.hom c r) = D.hom c r := by
    intro M R hM hMy r hr
    have h1 := (locAut_fixed_iff3 hΩ hex hP1 hO3 hyx hM.1).mp hMy
    exact h1 _ (by rw [hM.2.2]; exact ⟨r, hr, rfl⟩)
  have hτA := hfix hRK hyK
  have hτB := hfix hRT hyT
  have hτr : ∀ k, τ (D.hom c k) ∈ (D.hom c).range :=
    aut_preserves_range_of_fixed D c hk hRK.2.1 τ hτA
  obtain ⟨n, hnR, hn⟩ := Q3TLK.exists_model_elt3 hRN ht.mem
  obtain ⟨xC, hxCR, hxC⟩ := Q3TLK.exists_model_elt3 hR₂ hw.mem
  have hsq : ∀ {M : Subgroup G} {u : G}, IsClassicalMember3 M u → ∀ hu : u ∈ locLayer Ω x,
      locMk Ω x ⟨u, hu⟩ * locMk Ω x ⟨u, hu⟩ = 1 := by
    intro M u hM hu
    rw [← map_mul]
    have : (⟨u, hu⟩ : ↥(locLayer Ω x)) * ⟨u, hu⟩ = 1 :=
      Subtype.ext (Q3TLK.mul_self_eq_one_of_orderOf_eq_two3 hM.orderOf_eq_two)
    rw [this, map_one]
  obtain ⟨hn2, hn1⟩ := Q3TLK.involution_lift3 D c hnc hRN.2.1 hnR (hsq ht htY)
    (Q3TLK.locMk_involution_ne_one3 hN.1 ht) hn
  obtain ⟨hxC2, hxC1⟩ := Q3TLK.involution_lift3 D c hnc hR₂.2.1 hxCR (hsq hw hwY)
    (Q3TLK.locMk_involution_ne_one3 hK₂.1 hw) hxC
  have hnA : conjSub n RK = RK := conjSub_eq_of_normalizes3 hpc hRK htY hn htK
  have hnC : conjSub n R₂ = R₂ := conjSub_eq_of_normalizes3 hpc hR₂ htY hn htK₂
  have hact : ∀ {M : Subgroup G} {R : Subgroup (D.kind c).G}, Corr3 Ω x D c M R →
      (∀ k ∈ M, y * k * y⁻¹ = t * k * t⁻¹) → ∀ r ∈ R,
        τ (D.hom c r) = D.hom c (n * r * n⁻¹) := by
    intro M R hM hMy r hr
    have hmem : D.hom c r ∈ locImg Ω x M := by rw [hM.2.2]; exact ⟨r, hr, rfl⟩
    rw [hτ, locAut_eq_of_conj_eq3 hΩ.conjInvariant hyx htx hMy hmem,
      locAut_eq_conj3 hΩ.conjInvariant htY htx, map_mul, map_mul, map_inv, hn]
  have hτC := hact hR₂ hy₂
  have hτC' := hact hR₂' hy₂'
  have hAB : RK ≠ RT := fun h => hKT (corr_unique_right3 hΩ hex hP1 hO3 hRK (h ▸ hRT))
  have hCC' : R₂ ≠ R₂' := fun h => hK₂K₂' (corr_unique_right3 hΩ hex hP1 hO3 hR₂ (h ▸ hR₂'))
  have hcor := fun {M M' : Subgroup G} {R R' : Subgroup (D.kind c).G} (h : Corr3 Ω x D c M R)
    (h' : Corr3 Ω x D c M' R') => (corr_commutes3 hΩ hex hP1 hO3 hpc h h').mp
  have key := parity_comp3 (D.kind c) hk (D.hom c) (D.ker_le_center c) τ hτr hRK.2.1 hRT.2.1
    hR₂.2.1 hR₂'.2.1 hRN.2.1 hAB (hcor hRK hRT hcKT) hCC' (hcor hRK hR₂ hcKK₂)
    (hcor hRK hR₂' hcKK₂') (hcor hRT hR₂ hcTK₂) (hcor hRT hR₂' hcTK₂') hnR hn2 hn1 hnA hnC
    hτA hτB hτC hτC' hxCR hxC2 hxC1
  rcases key with h | h
  · have hfixN : ∀ a ∈ locImg Ω x N, τ a = a := by
      intro a ha
      rw [hRN.2.2] at ha
      obtain ⟨r, hr, rfl⟩ := ha
      exact h r hr
    have hle := (locAut_fixed_iff3 hΩ hex hP1 hO3 hyx hN.1).mpr hfixN
    have h1 : t * y = y * t := Subgroup.mem_centralizer_singleton_iff.mp (hle ht.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  · have hyw : y * w * x * (y * w)⁻¹ = x := by
      calc y * w * x * (y * w)⁻¹ = y * (w * x * w⁻¹) * y⁻¹ := by group
        _ = x := by rw [hwx, hyx]
    have hfixN : ∀ a ∈ locImg Ω x N, locAut hΩ.conjInvariant hyw a = a := by
      intro a ha
      rw [hRN.2.2] at ha
      obtain ⟨r, hr, rfl⟩ := ha
      rw [locAut_mul3 hΩ.conjInvariant hyx hwx hyw, locAut_eq_conj3 hΩ.conjInvariant hwY hwx,
        ← hxC, ← map_inv, ← map_mul, ← map_mul]
      exact h r hr
    have hle := (locAut_fixed_iff3 hΩ hex hP1 hO3 hyw hN.1).mpr hfixN
    have h1 : t * (y * w) = y * w * t := Subgroup.mem_centralizer_singleton_iff.mp (hle ht.mem)
    have h2 : t * y * w = y * t * w := by
      calc t * y * w = t * (y * w) := by group
        _ = y * w * t := h1
        _ = y * (w * t) := by group
        _ = y * (t * w) := by rw [hwt]
        _ = y * t * w := by group
    rw [mul_inv_eq_iff_eq_mul]
    exact (mul_right_cancel h2).symm

end Element

end CFSG.ClassicalInvolution.Q3.Q3P21

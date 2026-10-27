module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3S23

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem commutator_mem_of_sup_commutative {R K T : Subgroup G}
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hKT : K ≤ T) (hsup : R ⊔ K = T)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) :
    ∀ a ∈ T, ∀ b ∈ T, a⁻¹ * b⁻¹ * a * b ∈ R := by
  intro a ha b hb
  have hKN : K ≤ Subgroup.normalizer (R : Set G) := hKT.trans hTR
  rw [← hsup] at ha hb
  obtain ⟨r₁, hr₁, k₁, hk₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hKN).1 ha
  obtain ⟨r₂, hr₂, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hKN).1 hb
  have hconj : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ r ∈ R, g⁻¹ * r * g ∈ R := by
    intro g hg r hr
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hg) r).mp hr
    simpa using this
  have hconj' : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    exact (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  have hkk : k₁ * k₂ = k₂ * k₁ := hK k₁ hk₁ k₂ hk₂
  have hinv : (k₁ * k₂)⁻¹ = k₁⁻¹ * k₂⁻¹ := by rw [hkk]; group
  have hα' : k₁⁻¹ * r₁⁻¹ * k₁ ∈ R := hconj k₁ (hKN hk₁) r₁⁻¹ (R.inv_mem hr₁)
  have hu' : k₁ * r₂ * k₁⁻¹ ∈ R := hconj' k₁ (hKN hk₁) r₂ hr₂
  have hmid : r₂⁻¹ * r₁ * (k₁ * r₂ * k₁⁻¹) ∈ R :=
    R.mul_mem (R.mul_mem (R.inv_mem hr₂) hr₁) hu'
  have hmid' : (k₁ * k₂)⁻¹ * (r₂⁻¹ * r₁ * (k₁ * r₂ * k₁⁻¹)) * (k₁ * k₂) ∈ R :=
    hconj (k₁ * k₂) (Subgroup.mul_mem _ (hKN hk₁) (hKN hk₂)) _ hmid
  have hc : (r₁ * k₁)⁻¹ * (r₂ * k₂)⁻¹ * (r₁ * k₁) * (r₂ * k₂) =
      (k₁⁻¹ * r₁⁻¹ * k₁) * ((k₁ * k₂)⁻¹ * (r₂⁻¹ * r₁ * (k₁ * r₂ * k₁⁻¹)) * (k₁ * k₂)) := by
    rw [hinv]; group
  rw [hc]
  exact R.mul_mem hα' hmid'

end Generic

namespace Lin2Hyp

section Fus

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem not_conj_of_card {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hx2 : x ^ 2 = 1)
    (hxcomm : ∀ g ∈ T, x⁻¹ * g⁻¹ * x * g ∈ thompsonJ S)
    (hxtrans : ∀ i j : G, x⁻¹ * i ∈ thompsonJ S → x⁻¹ * j ∈ thompsonJ S → i ^ 2 = 1 →
      j ^ 2 = 1 → ∃ r ∈ thompsonJ S, r⁻¹ * i * r = j)
    (hcard : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G))
    (hω : Nat.card (omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G)) < Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G))
    (g : G) : g⁻¹ * s * g ≠ x := by
  intro hgx
  obtain ⟨-, hRs, -, hTs_eq, ⟨x₀, hx₀, hx₀S⟩, hsyl⟩ :=
    lemma2_4_23_main E G T M H S L D n hcfg s hs hsR hs2
  set R := thompsonJ S with hR
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set Ts := T ⊓ C with hTs
  set P := T ⊓ Cx with hP
  have hRT : R ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := E.TnR hcfg
  have hP2 : IsPGroup 2 P := hcfg.sylowT.isPGroup.to_le inf_le_left
  have hPR : P ⊔ R = T := by
    apply le_antisymm
    · exact sup_le inf_le_left hRT
    · intro g' hg'
      have h1 : x⁻¹ * (g'⁻¹ * x * g') ∈ R := by
        have := hxcomm g' hg'
        simpa [mul_assoc] using this
      have hj2 : (g'⁻¹ * x * g') ^ 2 = 1 := by
        have : (g'⁻¹ * x * g') ^ 2 = g'⁻¹ * x ^ 2 * g' := by simp only [pow_two]; group
        rw [this, hx2]; simp
      obtain ⟨r, hr, hrx⟩ := hxtrans x (g'⁻¹ * x * g') (by simp) h1 hx2 hj2
      have hgr : g' * r⁻¹ ∈ P := by
        refine ⟨T.mul_mem hg' (T.inv_mem (hRT hr)), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have e : (g' * r⁻¹)⁻¹ * x * (g' * r⁻¹) = x := by
          calc (g' * r⁻¹)⁻¹ * x * (g' * r⁻¹) = r * (g'⁻¹ * x * g') * r⁻¹ := by group
            _ = r * (r⁻¹ * x * r) * r⁻¹ := by rw [hrx]
            _ = x := by group
        calc (g' * r⁻¹) * x = (g' * r⁻¹) * ((g' * r⁻¹)⁻¹ * x * (g' * r⁻¹)) := by rw [e]
          _ = x * (g' * r⁻¹) := by group
      have : g' = (g' * r⁻¹) * r := by group
      rw [this]
      exact (P ⊔ R).mul_mem (Subgroup.mem_sup_left hgr) (Subgroup.mem_sup_right hr)
  have hcard1 : Nat.card T * Nat.card (R ⊓ Cx : Subgroup G) = Nat.card P * Nat.card R := by
    have h := card_sup_mul_card_inf (A := P) (B := R) (inf_le_left.trans hTR)
    rw [hPR] at h
    have e : P ⊓ R = R ⊓ Cx := by
      ext y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨_, hy⟩, hyR⟩
        exact ⟨hyR, hy⟩
      · rintro ⟨hyR, hy⟩
        exact ⟨⟨hRT hyR, hy⟩, hyR⟩
    rw [e] at h
    exact h
  have hcard2 : Nat.card T * Nat.card (R ⊓ C : Subgroup G) = Nat.card Ts * Nat.card R := by
    have h := card_sup_mul_card_inf (A := Ts) (B := R) (inf_le_left.trans hTR)
    rw [sup_comm, ← hTs_eq] at h
    have e : Ts ⊓ R = R ⊓ C := by
      ext y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨_, hy⟩, hyR⟩
        exact ⟨hyR, hy⟩
      · rintro ⟨hyR, hy⟩
        exact ⟨⟨hRT hyR, hy⟩, hyR⟩
    rw [e] at h
    exact h
  have hPTs : Nat.card P = Nat.card Ts := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card R)
    rw [← hcard1, ← hcard2, hcard]
  have hP'C : conjR P g⁻¹ ≤ C := by
    intro y hy
    rw [mem_conjR, inv_inv] at hy
    have h1 : g⁻¹ * y * g * x = x * (g⁻¹ * y * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [← hgx] at h1
    have h2 : g⁻¹ * (y * s) * g = g⁻¹ * (s * y) * g := by
      calc g⁻¹ * (y * s) * g = g⁻¹ * y * g * (g⁻¹ * s * g) := by group
        _ = g⁻¹ * s * g * (g⁻¹ * y * g) := h1
        _ = g⁻¹ * (s * y) * g := by group
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_left_cancel (mul_right_cancel h2))
  have hP'2 : IsPGroup 2 (conjR P g⁻¹) := (isPGroup_conjR_iff 2).mpr hP2
  have hP'syl : IsSylowTwoOf (conjR P g⁻¹) C := by
    refine isSylowTwoOf_of_card_eq hP'C hP'2 ?_
    rw [card_conjR, hPTs, hsyl.card_eq]
  obtain ⟨c, hcC, hc⟩ := hsyl.exists_conj hP'syl
  have hkey : ∀ z ∈ Ts, g⁻¹ * c * z * c⁻¹ * g ∈ P := by
    intro z hz
    have hmem : c * z * c⁻¹ ∈ conjR P g⁻¹ := by
      rw [hc]
      exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have := mem_conjR.mp hmem
    simpa [mul_assoc] using this
  have hUR : blockU L ≤ R := by
    have hRU : R = blockU L ⊔ conjR (blockU L) x₀ := (E.RUU hcfg hx₀.1 hx₀S).1
    rw [hRU]
    exact le_sup_left
  have hRsY : R ⊓ C ≤ conjR (R ⊓ Cx) (c⁻¹ * g)⁻¹ := by
    rw [hRs]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyTs, a, ha, g', rfl⟩
    rw [SetLike.mem_coe, mem_conjR]
    have hz : g⁻¹ * c * (g'⁻¹ * a * g') * c⁻¹ * g ∈ P := hkey _ hyTs
    have hzR : g⁻¹ * c * (g'⁻¹ * a * g') * c⁻¹ * g ∈ R := by
      rw [hR, E.Rstrong hcfg]
      exact Subgroup.subset_closure ⟨hz.1, a, ha, g' * c⁻¹ * g, by group⟩
    have e : (c⁻¹ * g)⁻¹ * (g'⁻¹ * a * g') * (c⁻¹ * g)⁻¹⁻¹ =
        g⁻¹ * c * (g'⁻¹ * a * g') * c⁻¹ * g := by group
    rw [e]
    exact ⟨hzR, hz.2⟩
  have hYeq : R ⊓ C = conjR (R ⊓ Cx) (c⁻¹ * g)⁻¹ := by
    refine Subgroup.eq_of_le_of_card_ge hRsY ?_
    rw [card_conjR, hcard]
  have hUe : IsElemAbelian 2 (blockU L) := (E.elemU hcfg hx₀.1 hx₀S).1
  have hWle : conjR (blockU L ⊓ C) (c⁻¹ * g) ≤ R ⊓ Cx := by
    intro y hy
    rw [mem_conjR] at hy
    have h1 : (c⁻¹ * g) * y * (c⁻¹ * g)⁻¹ ∈ R ⊓ C := ⟨hUR hy.1, hy.2⟩
    rw [hYeq, mem_conjR] at h1
    have e : (c⁻¹ * g)⁻¹ * ((c⁻¹ * g) * y * (c⁻¹ * g)⁻¹) * (c⁻¹ * g)⁻¹⁻¹ = y := by group
    rwa [e] at h1
  have hWe : IsElemAbelian 2 (conjR (blockU L ⊓ C) (c⁻¹ * g)) :=
    (isElemAbelian_conjR_iff _ _).mpr (IsElemAbelian.mono inf_le_left hUe)
  have hWΩ : conjR (blockU L ⊓ C) (c⁻¹ * g) ≤ omegaOneOf (R ⊓ Cx) := by
    intro y hy
    exact Subgroup.subset_closure ⟨hWle hy, hWe.2 y hy⟩
  have := Subgroup.card_le_of_le hWΩ
  rw [card_conjR] at this
  omega

end Fus

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2

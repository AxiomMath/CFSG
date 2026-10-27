module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {Ω : Type} [Group Ω]

structure S172Model (S B : Subgroup Ω) (G₀ : Type) [Group G₀] where
  π : ↥S →* G₀
  β : ↥B →* G₀
  surj : Function.Surjective π
  ker_π : π.ker = Subgroup.center ↥S
  split : ∀ b : ↥B, ∃ (s : ↥S) (c : Ω), c ∈ Subgroup.centralizer (S : Set Ω) ∧
    (b : Ω) = (s : Ω) * c ∧ β b = π s

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

include M

theorem conj_mem (b : ↥B) {t : Ω} (ht : t ∈ S) : (b : Ω) * t * (b : Ω)⁻¹ ∈ S := by
  obtain ⟨s, c, hc, hb, -⟩ := M.split b
  have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.1 hc t ht).symm
  have h : (b : Ω) * t * (b : Ω)⁻¹ = (s : Ω) * t * (s : Ω)⁻¹ := by
    rw [hb]
    calc (s : Ω) * c * t * ((s : Ω) * c)⁻¹ = (s : Ω) * (c * t) * c⁻¹ * (s : Ω)⁻¹ := by group
      _ = (s : Ω) * (t * c) * c⁻¹ * (s : Ω)⁻¹ := by rw [hct]
      _ = (s : Ω) * t * (s : Ω)⁻¹ := by group
  rw [h]
  exact S.mul_mem (S.mul_mem s.2 ht) (S.inv_mem s.2)

@[expose] def conjHom (b : ↥B) : ↥S →* ↥S where
  toFun t := ⟨(b : Ω) * t * (b : Ω)⁻¹, M.conj_mem b t.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjHom (b : ↥B) (t : ↥S) : ((M.conjHom b t : ↥S) : Ω) = (b : Ω) * t * (b : Ω)⁻¹ := rfl

theorem π_conjHom (b : ↥B) (t : ↥S) : M.π (M.conjHom b t) = M.β b * M.π t * (M.β b)⁻¹ := by
  obtain ⟨s₀, c, hc, hb, hβ⟩ := M.split b
  have hct : c * (t : Ω) = t * c := (Subgroup.mem_centralizer_iff.1 hc t t.2).symm
  have hs : M.conjHom b t = s₀ * t * s₀⁻¹ := by
    apply Subtype.ext
    rw [coe_conjHom, hb]
    calc (s₀ : Ω) * c * t * ((s₀ : Ω) * c)⁻¹ = (s₀ : Ω) * (c * t) * c⁻¹ * (s₀ : Ω)⁻¹ := by group
      _ = (s₀ : Ω) * (t * c) * c⁻¹ * (s₀ : Ω)⁻¹ := by rw [hct]
      _ = ((s₀ * t * s₀⁻¹ : ↥S) : Ω) := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [hs, map_mul, map_mul, map_inv, hβ]

theorem β_eq_one_iff (b : ↥B) : M.β b = 1 ↔ (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  obtain ⟨s, c, hc, hb, hβ⟩ := M.split b
  have h1 : M.β b = 1 ↔ s ∈ Subgroup.center ↥S := by
    rw [hβ, ← M.ker_π, MonoidHom.mem_ker]
  rw [h1, hb]
  constructor
  · intro hs
    have hs' : (s : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hs ⟨h, hh⟩)
    exact Subgroup.mul_mem _ hs' hc
  · intro hbc
    have hs' : (s : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
      have e : (s : Ω) = ((s : Ω) * c) * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hbc (Subgroup.inv_mem _ hc)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hs' g g.2)

theorem ker_β : M.β.ker = (Subgroup.centralizer (S : Set Ω)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, M.β_eq_one_iff, Subgroup.mem_subgroupOf]

theorem β_eq_one_iff_mem_zpowers {x : Ω}
    (hx : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x) (b : ↥B) :
    M.β b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x := by
  rw [M.β_eq_one_iff]
  exact hx b b.2

@[expose] def img (D : Subgroup Ω) : Subgroup G₀ := (D.subgroupOf B).map M.β

theorem mem_img {D : Subgroup Ω} {g : G₀} :
    g ∈ M.img D ↔ ∃ b : ↥B, (b : Ω) ∈ D ∧ M.β b = g := by
  simp only [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem img_mono {D D' : Subgroup Ω} (h : D ≤ D') : M.img D ≤ M.img D' := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := M.mem_img.1 hg
  exact M.mem_img.2 ⟨b, h hb, rfl⟩

theorem img_le_range (D : Subgroup Ω) : M.img D ≤ M.β.range := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := M.mem_img.1 hg
  exact ⟨b, rfl⟩

theorem img_zpowers {a : Ω} (ha : a ∈ B) :
    M.img (Subgroup.zpowers a) = Subgroup.zpowers (M.β ⟨a, ha⟩) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := M.mem_img.1 hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have : b = (⟨a, ha⟩ : ↥B) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow]
  · rw [Subgroup.zpowers_le]
    exact M.mem_img.2 ⟨⟨a, ha⟩, Subgroup.mem_zpowers a, rfl⟩

theorem img_sup {D D' : Subgroup Ω} (hD : D ≤ B) (hD' : D' ≤ B) :
    M.img (D ⊔ D') = M.img D ⊔ M.img D' := by
  have hr : B.subtype.range = B := Subgroup.range_subtype B
  have h := Subgroup.comap_sup_eq_of_le_range B.subtype (H := D) (K := D')
    (by rw [hr]; exact hD) (by rw [hr]; exact hD')
  show Subgroup.map M.β (Subgroup.comap B.subtype (D ⊔ D')) =
    Subgroup.map M.β (Subgroup.comap B.subtype D) ⊔ Subgroup.map M.β (Subgroup.comap B.subtype D')
  rw [← h, Subgroup.map_sup]

end S172Model

private lemma mem_sup_centralizer_decomposition {S B : Subgroup Ω} (hSn : S.Normal)
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∀ b : ↥B, ∃ (s : ↥S) (c : Ω), c ∈ Subgroup.centralizer (S : Set Ω) ∧
      (b : Ω) = (s : Ω) * c := by
  intro b
  haveI := hSn
  obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup_of_normal_left.1 (hBin b b.2)
  exact ⟨⟨s, hs⟩, c, hc, hsc.symm⟩

private lemma pi_eq_of_mul_centralizer_eq {S : Subgroup Ω} {G₀ : Type} [Group G₀]
    (π : ↥S →* G₀) (hπ_ker : π.ker = Subgroup.center ↥S) :
    ∀ (s s' : ↥S) (c c' : Ω), c ∈ Subgroup.centralizer (S : Set Ω) →
      c' ∈ Subgroup.centralizer (S : Set Ω) → (s : Ω) * c = s' * c' → π s = π s' := by
  intro s s' c c' hc hc' h
  have hz : (s'⁻¹ * s : ↥S) ∈ Subgroup.center ↥S := by
    have e : ((s'⁻¹ * s : ↥S) : Ω) = c' * c⁻¹ := by
      have h1 : (s' : Ω)⁻¹ * (s * c) = c' := by rw [h]; group
      calc ((s'⁻¹ * s : ↥S) : Ω) = (s' : Ω)⁻¹ * (s * c) * c⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = c' * c⁻¹ := by rw [h1]
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Ω) * ((s'⁻¹ * s : ↥S) : Ω) = ((s'⁻¹ * s : ↥S) : Ω) * g
    rw [e]
    have hcc : c' * c⁻¹ ∈ Subgroup.centralizer (S : Set Ω) :=
      Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)
    exact Subgroup.mem_centralizer_iff.1 hcc (g : Ω) g.2
  have h0 : π (s'⁻¹ * s) = 1 := by
    rw [← MonoidHom.mem_ker, hπ_ker]
    exact hz
  rw [map_mul, map_inv, inv_mul_eq_one] at h0
  exact h0.symm

theorem S172Model.nonempty_of_mem_sup {S B : Subgroup Ω} (hSn : S.Normal)
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) {G₀ : Type} [Group G₀]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* G₀) : Nonempty (S172Model S B G₀) := by
  classical
  let π : ↥S →* G₀ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hπ_surj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ_ker : π.ker = Subgroup.center ↥S := by
    rw [MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hdec : ∀ b : ↥B, ∃ (s : ↥S) (c : Ω), c ∈ Subgroup.centralizer (S : Set Ω) ∧
      (b : Ω) = (s : Ω) * c := mem_sup_centralizer_decomposition hSn hBin
  have huniq := pi_eq_of_mul_centralizer_eq π hπ_ker
  choose s c hc hsc using hdec
  have hcomm : ∀ (b : ↥B) (t : ↥S), (c b) * (t : Ω) = t * c b := fun b t =>
    (Subgroup.mem_centralizer_iff.1 (hc b) (t : Ω) t.2).symm
  let β : ↥B →* G₀ :=
    { toFun := fun b => π (s b)
      map_one' := by
        refine (huniq (s 1) 1 (c 1) 1 (hc 1) (Subgroup.one_mem _) ?_).trans (map_one π)
        rw [← hsc 1]
        simp
      map_mul' := fun b₁ b₂ => by
        rw [← map_mul]
        refine huniq (s (b₁ * b₂)) (s b₁ * s b₂) (c (b₁ * b₂)) (c b₁ * c b₂) (hc _)
          (Subgroup.mul_mem _ (hc b₁) (hc b₂)) ?_
        rw [← hsc (b₁ * b₂), Subgroup.coe_mul, hsc b₁, hsc b₂, Subgroup.coe_mul]
        calc (s b₁ : Ω) * c b₁ * ((s b₂ : Ω) * c b₂)
            = (s b₁ : Ω) * (c b₁ * (s b₂ : Ω)) * c b₂ := by group
          _ = (s b₁ : Ω) * ((s b₂ : Ω) * c b₁) * c b₂ := by rw [hcomm b₁ (s b₂)]
          _ = (s b₁ : Ω) * (s b₂ : Ω) * (c b₁ * c b₂) := by group }
  exact ⟨⟨π, β, hπ_surj, hπ_ker, fun b => ⟨s b, c b, hc b, hsc b, rfl⟩⟩⟩

theorem mem_sup_centralizer_of_autThreePowInner {S B : Subgroup Ω} {G₀ : Type} [Group G₀]
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hB : IsElemAbelian 3 B) (hAut : AutThreePowInner G₀)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* G₀) : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  intro b hb
  have hperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp ⟨hSq.1⟩
  refine mem_sup_centralizer_of_three_pow_normalizer_cover hAut S hperf θ (k := 1) ?_ ?_
  · rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top b
  · simpa using hB.2 b hb

theorem nonempty_centerQuot_equiv {p : ℕ} [Finite Ω] {S : Subgroup Ω} {G₀ : Type} [Group G₀]
    [Nontrivial G₀] (hSq : CFSG.Open.IsQuasisimple ↥S) (e : PSimple p S ≃* G₀) :
    Nonempty (↥S ⧸ Subgroup.center ↥S ≃* G₀) := by
  haveI : Group.IsPerfect ↥S := ⟨hSq.1⟩
  have hOne : GLAPPrimeCore p ↥S ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PSimple p S) := by
      have h1 : Subsingleton (↥S ⧸ GLAPPrimeCore p ↥S) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (QuotientGroup.mk'_surjective
        (Subgroup.center (↥S ⧸ GLAPPrimeCore p ↥S))).subsingleton
    haveI : Subsingleton G₀ := e.symm.injective.subsingleton
    exact not_subsingleton G₀ ‹_›
  have hOZ : GLAPPrimeCore p ↥S ≤ Subgroup.center ↥S :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hSq inferInstance hOne
  exact ⟨(CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hOZ).trans e⟩

theorem S172Model.nonempty_of_pSimple_equiv {p : ℕ} [Finite Ω] {S B : Subgroup Ω} {G₀ : Type}
    [Group G₀] [Nontrivial G₀] (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) (e : PSimple p S ≃* G₀) :
    Nonempty (S172Model S B G₀) := by
  obtain ⟨θ⟩ := nonempty_centerQuot_equiv hSq e
  exact S172Model.nonempty_of_mem_sup hSn hBin θ

theorem LiftableRank.nontrivial {p : ℕ} {G₀ : Type} [Group G₀] {m : ℕ} (hR : LiftableRank p G₀ m) :
    Nontrivial G₀ := by
  obtain ⟨e, t, T, -, -, -, -, -, hT, -⟩ := hR.2
  obtain ⟨g, hg⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT
  exact nontrivial_of_ne (g : G₀) 1 (fun h => hg (Subtype.ext h))

end CFSG.LocalAnalysis.GLTheoremA.S172X

end

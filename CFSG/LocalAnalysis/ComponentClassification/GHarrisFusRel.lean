module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusSound
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSTransport
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem Fus.not_bad {R : ℕ → ℕ → Prop} (hsymm : ∀ i j, R i j → R j i)
    (htrans : ∀ i j k, R i j → R j k → R i k) (P : ℕ → ℕ) (hP : ∀ i, R i (P i))
    (F : List (ℕ × ℕ)) (hF : ∀ p ∈ F, ¬ R p.1 p.2) (B : List (ℕ × ℕ))
    (hB : ∀ b ∈ B, ∃ p ∈ F, (P p.1 = P b.1 ∧ P p.2 = P b.2) ∨ (P p.1 = P b.2 ∧ P p.2 = P b.1)) :
    ∀ b ∈ B, ¬ R b.1 b.2 := by
  intro b hb hR
  obtain ⟨p, hp, h⟩ := hB b hb
  apply hF p hp
  have hPP : R (P b.1) (P b.2) := htrans _ _ _ (hsymm _ _ (hP b.1)) (htrans _ _ _ hR (hP b.2))
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : R p.1 (P b.1) := h1 ▸ hP p.1
    have h2' : R (P b.2) p.2 := h2 ▸ hsymm _ _ (hP p.2)
    exact htrans _ _ _ h1' (htrans _ _ _ hPP h2')
  · have h1' : R p.1 (P b.2) := h1 ▸ hP p.1
    have h2' : R (P b.1) p.2 := h2 ▸ hsymm _ _ (hP p.2)
    exact htrans _ _ _ h1' (htrans _ _ _ (hsymm _ _ hPP) h2')


variable {G : Type} [Group G] [Finite G]

theorem exists_extremal_conj_lt {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {u : G} (hu : u ∈ S)
    (hne : ¬ IsSylowOf 2 (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G))) :
    ∃ g : G, g⁻¹ * u * g ∈ S ∧
      IsSylowOf 2 (S ⊓ centralizer ({g⁻¹ * u * g} : Set G))
        (centralizer ({g⁻¹ * u * g} : Set G)) ∧
      Nat.card ↥(S ⊓ centralizer ({u} : Set G)) <
        Nat.card ↥(S ⊓ centralizer ({g⁻¹ * u * g} : Set G)) ∧
      ∀ c ∈ S ⊓ centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ S ⊓ centralizer ({g⁻¹ * u * g} : Set G) := by
  classical
  have : Nonempty {h : G // h⁻¹ * u * h ∈ S} := ⟨⟨1, by simpa using hu⟩⟩
  obtain ⟨⟨h, hh⟩, hmax⟩ := Finite.exists_max
    (fun h : {h : G // h⁻¹ * u * h ∈ S} =>
      Nat.card ↥(S ⊓ centralizer ({h.1⁻¹ * u * h.1} : Set G)))
  set v := h⁻¹ * u * h with hv
  have hvext : IsSylowOf 2 (S ⊓ centralizer ({v} : Set G)) (centralizer ({v} : Set G)) := by
    refine isSylowOf_of_card_le hS hh fun k hk => ?_
    have := hmax ⟨h * k, by
      rw [show (h * k)⁻¹ * u * (h * k) = k⁻¹ * v * k by rw [hv]; group]; exact hk⟩
    simp only at this
    rwa [show (h * k)⁻¹ * u * (h * k) = k⁻¹ * v * k by rw [hv]; group] at this
  have hlt : Nat.card ↥(S ⊓ centralizer ({u} : Set G)) <
      Nat.card ↥(S ⊓ centralizer ({v} : Set G)) := by
    by_contra hge
    push Not at hge
    apply hne
    refine isSylowOf_of_card_le hS hu fun k hk => ?_
    exact (hmax ⟨k, hk⟩).trans hge
  obtain ⟨g, hg, hC⟩ := exists_conj_extremal (u := u) hS.isPGroup hvext
    (show h⁻¹⁻¹ * v * h⁻¹ = u by rw [hv]; group)
  refine ⟨g, hg ▸ hh, hg ▸ hvext, hg ▸ hlt, ?_⟩
  rw [hg]
  exact hC


namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem fusN_symm {i j : ℕ} (h : D.FusN i j) : D.FusN j i := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

omit [Finite G] in
theorem fusN_trans {i j k : ℕ} (h1 : D.FusN i j) (h2 : D.FusN j k) : D.FusN i k := by
  obtain ⟨g, hg⟩ := h1
  obtain ⟨g', hg'⟩ := h2
  exact ⟨g * g', by rw [← hg', ← hg]; group⟩

omit [Finite G] in
theorem fusN_refl (i : ℕ) : D.FusN i i := ⟨1, by group⟩


theorem not_fusN_of_lt {i j : Fin 9}
    (hi : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G))
      (centralizer ({D.toG (SE.invRep i)} : Set G)))
    (hlt : SE.invRepCent i < SE.invRepCent j) : ¬ D.FusN i j ∧ ¬ D.FusN j i := by
  have key : ¬ D.FusN j i := by
    rintro ⟨g, hg⟩
    have hi' : Fin.ofNat 9 i.val = i := Fin.ext (by simp)
    have hj' : Fin.ofNat 9 j.val = j := Fin.ext (by simp)
    rw [hi', hj'] at hg
    set Q := ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom
    have hQ : Q ≤ centralizer ({D.toG (SE.invRep i)} : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      have hcw := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
      rw [mem_centralizer_singleton_iff]
      change g⁻¹ * c * g⁻¹⁻¹ * _ = _ * (g⁻¹ * c * g⁻¹⁻¹)
      rw [← hg, inv_inv]
      calc g⁻¹ * c * g * (g⁻¹ * D.toG (SE.invRep j) * g) = g⁻¹ * (c * D.toG (SE.invRep j)) * g := by
            group
        _ = g⁻¹ * (D.toG (SE.invRep j) * c) * g := by rw [hcw]
        _ = g⁻¹ * D.toG (SE.invRep j) * g * (g⁻¹ * c * g) := by group
    have hQ2 : IsPGroup 2 Q := (D.S.isPGroup'.to_le inf_le_left).map _
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hi hQ hQ2
    have hle : Q.map (MulAut.conj c).toMonoidHom ≤
        (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hc q hq
    have hcard := card_le_of_le hle
    rw [card_map_of_injective (MulAut.conj c).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective, D.card_centralizer_invRep_G,
      D.card_centralizer_invRep_G] at hcard
    omega
  exact ⟨fun h => key (D.fusN_symm h), key⟩

omit [Finite G] in
theorem img_conj {A : Fus.Data} (hA : A.checkM (· * ·) = true) {g : G}
    (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {k : ℕ} (hk : k < 32) :
    D.toG (A.img (· * ·) (D.fusQ A g) k) = g⁻¹ * D.toG (A.elt (· * ·) k) * g := by
  rw [← (D.fus_img hA hgu hgC k hk).2, D.toG_conjM (hgC _ (D.fus_img hA hgu hgC k hk).1)]

omit [Finite G] in
theorem hasEdge_conj {A : Fus.Data} (hA : A.checkM (· * ·) = true) (hcls : SE.clsOk = true)
    {g : G} (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {i j : ℕ} (h : A.hasEdge (· * ·) (D.fusQ A g) i j = true) :
    ∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
      g⁻¹ * (s₁⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 i)) * s₁) * g =
        s₂⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 j)) * s₂ := by
  unfold Fus.Data.hasEdge at h
  obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨hinv, hci⟩, hcj⟩ := hk'
  have himg := D.fus_img hA hgu hgC k hk
  have hdI : SE.isInvB (A.img (· * ·) (D.fusQ A g) k) = true := by
    rw [← himg.2]
    exact D.isInv_conjM hgC himg.1 hinv
  obtain ⟨-, c₁, hc₁⟩ := SE.cls_spec hcls (s := A.elt (· * ·) k) hinv
  obtain ⟨-, c₂, hc₂⟩ := SE.cls_spec hcls hdI
  rw [hci] at hc₁
  rw [hcj] at hc₂
  refine ⟨(D.toG c₁)⁻¹, inv_mem (D.toG_mem _), (D.toG c₂)⁻¹, inv_mem (D.toG_mem _), ?_⟩
  rw [← hc₁, ← hc₂]
  simp only [map_mul, map_inv, inv_inv]
  rw [D.img_conj hA hgu hgC hk]
  group

end GHSylow

end CFSG.ComponentClassification.GHarris

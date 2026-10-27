module

public import CFSG.GF2Type.Aschbacher1976Full.HSQuot

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransY

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G} {W : Subgroup G}

@[expose] def imgW (z : G) (W : Subgroup G) (hW : W ≤ Hz z) : Subgroup (Qbar z) :=
  ((qmk z).comp (Subgroup.inclusion hW)).range

theorem mem_imgW_iff (hW : W ≤ Hz z) {y : Qbar z} :
    y ∈ imgW z W hW ↔ ∃ h : ↥(Hz z), (h : G) ∈ W ∧ qmk z h = y :=
  ⟨fun ⟨w, hw⟩ => ⟨Subgroup.inclusion hW w, w.2, hw⟩, fun ⟨h, hh, e⟩ => ⟨⟨h, hh⟩, e⟩⟩

theorem qmk_mem_imgW (hW : W ≤ Hz z) {h : ↥(Hz z)} (hh : (h : G) ∈ W) :
    qmk z h ∈ imgW z W hW :=
  ⟨⟨h, hh⟩, rfl⟩

theorem imgW_comm (hW : W ≤ Hz z) (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    ∀ x ∈ imgW z W hW, ∀ x' ∈ imgW z W hW, x * x' = x' * x := by
  intro x hx x' hx'
  obtain ⟨h, hh, rfl⟩ := (mem_imgW_iff hW).mp hx
  obtain ⟨h', hh', rfl⟩ := (mem_imgW_iff hW).mp hx'
  rw [← map_mul, ← map_mul]
  exact congrArg (qmk z) (Subtype.ext (hab _ hh _ hh'))

theorem imgW_sq (hW : W ≤ Hz z) (hsq : ∀ a ∈ W, a * a ∈ Fz z) :
    ∀ x ∈ imgW z W hW, x * x = 1 := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (mem_imgW_iff hW).mp hx
  rw [← map_mul, qmk_eq_one_iff]
  exact hsq _ hh

theorem card_le_imgW_mul (hW : W ≤ Hz z) :
    Nat.card W ≤ Nat.card (imgW z W hW) * Nat.card ↥(W ⊓ Fz z) := by
  let ψ : ↥W →* Qbar z := (qmk z).comp (Subgroup.inclusion hW)
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.ker ≤ Nat.card ↥(W ⊓ Fz z) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : ↥W) : G), x.1.2, ?_⟩ : ↥(W ⊓ Fz z))) ?_
    · exact (qmk_eq_one_iff z _).mp (MonoidHom.mem_ker.mp x.2)
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card W = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
    _ ≤ Nat.card ↥(W ⊓ Fz z) * Nat.card ψ.range := Nat.mul_le_mul_right _ h2
    _ = Nat.card (imgW z W hW) * Nat.card ↥(W ⊓ Fz z) := mul_comm _ _

theorem qmk_mem_normalizer_imgW (hW : W ≤ Hz z) {n : G} (hn : n ∈ Hz z)
    (hf : ∀ x ∈ W, n * x * n⁻¹ ∈ W) (hb : ∀ x ∈ W, n⁻¹ * x * n ∈ W) :
    qmk z ⟨n, hn⟩ ∈ Subgroup.normalizer (imgW z W hW : Set (Qbar z)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨h, hh, rfl⟩ := (mem_imgW_iff hW).mp hy
    have e : qmk z ⟨n, hn⟩ * qmk z h * (qmk z ⟨n, hn⟩)⁻¹ = qmk z (⟨n, hn⟩ * h * ⟨n, hn⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact qmk_mem_imgW hW (hf _ hh)
  · intro hy
    obtain ⟨h', hh', he⟩ := (mem_imgW_iff hW).mp hy
    have e : y = qmk z (⟨n, hn⟩⁻¹ * h' * ⟨n, hn⟩) := by
      rw [map_mul, map_mul, map_inv, he]
      group
    rw [e]
    exact qmk_mem_imgW hW (hb _ hh')

end CFSG.GF2Type.Aschbacher1976Full.HS.TransY

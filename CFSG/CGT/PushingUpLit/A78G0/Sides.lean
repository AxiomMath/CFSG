module

public import CFSG.CGT.PushingUpLit.A78G0.Fusion
public import CFSG.CGT.PushingUpLit.A78G0.Borel

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4 CFSG.CGT.PushingUpLit.A78S4
  CFSG.ABGLocalTools

section Rho

variable {G : Type} [Group G] {L V K : Subgroup G} {e : ℕ}

@[expose] noncomputable def rhoHom (D : NatCoordK G L V K (GaloisField 2 e)) :
    ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
  MonoidHom.mk' (fun l => D.ρ l) (fun a b => D.ρ_mul a a.2 b b.2)

theorem rhoHom_apply (D : NatCoordK G L V K (GaloisField 2 e)) (l : ↥L) :
    rhoHom D l = D.ρ l := rfl

theorem rhoHom_surjective (D : NatCoordK G L V K (GaloisField 2 e)) :
    Function.Surjective (rhoHom D) := by
  intro g
  obtain ⟨l, hl, hlg⟩ := D.ρ_surj g
  exact ⟨⟨l, hl⟩, hlg⟩

theorem rhoHom_ker (D : NatCoordK G L V K (GaloisField 2 e)) :
    (rhoHom D).ker = V.subgroupOf L := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact D.ρ_eq_one x x.2

end Rho

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem V_le_L : V ≤ L₁ := h.side₁.V_le_L

theorem J_le_L : V ⊔ W ≤ L₁ := h.side₁.J_le_L

theorem L_le_M : L₁ ≤ Subgroup.normalizer (V : Set G) := h.side₁.L_le_M

theorem M_le_normalizer_L : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L₁ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.side₁.L_le_M).1 h.side₁.normal_L

theorem card_J : Nat.card ↥(V ⊔ W) = Nat.card V * 2 ^ e := by
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := fun w hw =>
    le_normalizer_of_conj' h.jst.conj_V ((le_sup_right : W ≤ V ⊔ W) hw)
  have h1 : V.relIndex (W ⊔ V) = V.relIndex W := relIndex_sup_of_le_normalizer hWV
  rw [sup_comm] at h1
  have h2 : V.relIndex W = 2 ^ e := by
    rw [← Subgroup.inf_relIndex_right]
    exact h.jst.index_V₂
  have h3 := Subgroup.relIndex_mul_card V (V ⊔ W)
  rw [inf_eq_left.2 le_sup_left, h1, h2] at h3
  rw [mul_comm]
  exact h3.symm

theorem borel_facts :
    {C : Subgroup G | ∃ x ∈ L₁, C = cs (V ⊔ W) x}.ncard = 2 ^ e + 1 ∧
      ∀ x ∈ L₁, ∀ x' ∈ L₁, cs (V ⊔ W) x ≠ cs (V ⊔ W) x' →
        cs (V ⊔ W) x ⊓ cs (V ⊔ W) x' ≤ V := by
  obtain ⟨D⟩ := h.pair.side₁.nat
  have hs := rhoHom_surjective D
  have hk := rhoHom_ker D
  have hJq : Nat.card (img (rhoHom D) (V ⊔ W)) = 2 ^ e :=
    card_img_eq (rhoHom D) hk le_sup_left h.J_le_L h.card_J
  refine ⟨ncard_conj_class_L (rhoHom D) h.two_le hs hk h.V_le_L le_sup_left h.J_le_L hJq,
    fun x hx x' hx' hne => ?_⟩
  exact inf_cs_le_V (rhoHom D) h.two_le hk h.V_le_L le_sup_left h.J_le_L hJq hx hx' hne

theorem M_conj_eq_L_conj :
    {C : Subgroup G | ∃ m ∈ Subgroup.normalizer (V : Set G), C = cs (V ⊔ W) m} =
      {C : Subgroup G | ∃ x ∈ L₁, C = cs (V ⊔ W) x} := by
  ext C
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmL : cs L₁ m = L₁ := cs_of_mem_normalizer (h.M_le_normalizer_L hm)
    have hsyl : IsSylowOf 2 (cj m (V ⊔ W)) L₁ := by
      have := isSylowOf_cj h.pair.side₁.sylowJ m
      have hc : cj m L₁ = L₁ := hmL
      rwa [hc] at this
    obtain ⟨k, hk, hkc⟩ := exists_eq_cj_of_isSylowOf h.pair.side₁.sylowJ hsyl
    exact ⟨k, hk, hkc⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, h.L_le_M hx, rfl⟩

theorem ncard_M_conj :
    {C : Subgroup G | ∃ m ∈ Subgroup.normalizer (V : Set G), C = cs (V ⊔ W) m}.ncard =
      2 ^ e + 1 := by
  rw [h.M_conj_eq_L_conj]
  exact h.borel_facts.1

theorem inf_cs_J_le_V {m m' : G} (hm : m ∈ Subgroup.normalizer (V : Set G))
    (hm' : m' ∈ Subgroup.normalizer (V : Set G)) (hne : cs (V ⊔ W) m ≠ cs (V ⊔ W) m') :
    cs (V ⊔ W) m ⊓ cs (V ⊔ W) m' ≤ V := by
  have h1 : cs (V ⊔ W) m ∈ {C : Subgroup G | ∃ x ∈ L₁, C = cs (V ⊔ W) x} := by
    rw [← h.M_conj_eq_L_conj]
    exact ⟨m, hm, rfl⟩
  have h2 : cs (V ⊔ W) m' ∈ {C : Subgroup G | ∃ x ∈ L₁, C = cs (V ⊔ W) x} := by
    rw [← h.M_conj_eq_L_conj]
    exact ⟨m', hm', rfl⟩
  obtain ⟨x, hx, hxe⟩ := h1
  obtain ⟨x', hx', hxe'⟩ := h2
  rw [hxe, hxe'] at hne ⊢
  exact h.borel_facts.2 x hx x' hx' hne

theorem normalizer_W_subgroupOf :
    (Subgroup.normalizer (W : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) =
      (Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G)) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, h.normalizer_J_eq]
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

theorem ncard_conj_W :
    {U : Subgroup G | ∃ m ∈ Subgroup.normalizer (V : Set G), U = cs W m}.ncard = 2 ^ e + 1 := by
  rw [ncard_conj_class, h.normalizer_W_subgroupOf, ← ncard_conj_class, h.ncard_M_conj]

theorem normalizer_Z_subgroupOf₂ :
    (Subgroup.normalizer (Z : Set G)).subgroupOf (Subgroup.normalizer (W : Set G)) =
      (Subgroup.normalizer (V : Set G)).subgroupOf (Subgroup.normalizer (W : Set G)) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, h.side₁.normalizer_Z]

theorem ncard_conj_Z₂ :
    {B : Subgroup G | ∃ n ∈ Subgroup.normalizer (W : Set G), B = cs Z n}.ncard = 2 ^ e + 1 := by
  rw [ncard_conj_class, h.normalizer_Z_subgroupOf₂, ← ncard_conj_class]
  exact h.symm.ncard_conj_W

end G0Core

end CFSG.CGT.PushingUpLit.A78G0

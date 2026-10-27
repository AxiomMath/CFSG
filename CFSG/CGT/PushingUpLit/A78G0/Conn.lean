module

public import CFSG.CGT.PushingUpLit.A78G0.ConnInv
import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.Timmesfeld.Bridge.StrongEmbedding

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools

section Graph

variable {G : Type} [Group G]

abbrev CommAdj (Z X Y : Subgroup G) : Prop :=
  X ∈ zClass Z ∧ Y ∈ zClass Z ∧ Commuting X Y

theorem commAdj_symm {Z X Y : Subgroup G} (hXY : CommAdj Z X Y) : CommAdj Z Y X :=
  ⟨hXY.2.1, hXY.1, fun y hy x hx => (hXY.2.2 x hx y hy).symm⟩

theorem commAdj_cs {Z X Y : Subgroup G} (hXY : CommAdj Z X Y) (g : G) :
    CommAdj Z (cs X g) (cs Y g) :=
  ⟨cs_mem_zClass hXY.1 g, cs_mem_zClass hXY.2.1 g, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hXY.2.2 a ha b hb).map (MulAut.conj g).toMonoidHom⟩

theorem reflTransGen_commAdj_symm {Z X Y : Subgroup G}
    (h : Relation.ReflTransGen (CommAdj Z) X Y) : Relation.ReflTransGen (CommAdj Z) Y X := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (commAdj_symm hbc) ih

theorem reflTransGen_commAdj_cs {Z X Y : Subgroup G}
    (h : Relation.ReflTransGen (CommAdj Z) X Y) (g : G) :
    Relation.ReflTransGen (CommAdj Z) (cs X g) (cs Y g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (commAdj_cs hbc g)

def compStab (Z : Subgroup G) : Subgroup G where
  carrier := {g | Relation.ReflTransGen (CommAdj Z) Z (cs Z g)}
  one_mem' := by
    show Relation.ReflTransGen (CommAdj Z) Z (cs Z 1)
    rw [cs_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : Relation.ReflTransGen (CommAdj Z) Z (cs Z a) := ha
    have hb' : Relation.ReflTransGen (CommAdj Z) Z (cs Z b) := hb
    have h1 : Relation.ReflTransGen (CommAdj Z) (cs Z a) (cs Z (a * b)) := by
      rw [cs_mul]
      exact reflTransGen_commAdj_cs hb' a
    exact ha'.trans h1
  inv_mem' := by
    intro a ha
    have ha' : Relation.ReflTransGen (CommAdj Z) Z (cs Z a) := ha
    have h1 := reflTransGen_commAdj_cs ha' a⁻¹
    rw [cs_cs_inv] at h1
    exact reflTransGen_commAdj_symm h1

theorem mem_compStab {Z : Subgroup G} {g : G} :
    g ∈ compStab Z ↔ Relation.ReflTransGen (CommAdj Z) Z (cs Z g) := Iff.rfl

theorem normalizer_le_compStab (Z : Subgroup G) :
    Subgroup.normalizer (Z : Set G) ≤ compStab Z := by
  intro g hg
  rw [mem_compStab, cs_of_mem_normalizer hg]

end Graph

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem normalizer_V_le_stab : Subgroup.normalizer (V : Set G) ≤ compStab Z := by
  rw [← h.normalizer_Z_eq]
  exact normalizer_le_compStab Z

theorem normalizer_W_le_stab : Subgroup.normalizer (W : Set G) ≤ compStab Z := by
  intro n hn
  rw [mem_compStab]
  refine Relation.ReflTransGen.single ⟨self_mem_zClass Z, cs_mem_zClass (self_mem_zClass Z) n, ?_⟩
  exact fun a ha b hb => h.jst.abelian_V₂ a (h.Z_le_W ha) b (h.cs_le_W_of_mem hn hb)

theorem cent_le_stab_of_type {s : G} (hs1 : s ≠ 1)
    (hs : s ∈ Z ∨ s ∈ Z₂ ∨ UType V W Z Z₂ s) :
    Subgroup.centralizer ({s} : Set G) ≤ compStab Z := by
  rcases hs with hs | hs | hs
  · exact (h.side₁.cent_z s hs hs1).trans h.normalizer_V_le_stab
  · exact (h.side₂.cent_z s hs hs1).trans h.normalizer_W_le_stab
  · exact (h.cent_le_normalizer_J hs.1 hs.2.1 hs.2.2).trans
      (h.normalizer_J_le_V.trans h.normalizer_V_le_stab)

theorem cent_le_stab_of_mem_J {s : G} (hs : s ∈ V ⊔ W) (hss : s * s = 1) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≤ compStab Z := by
  have hconj : ∃ g ∈ compStab Z, g⁻¹ * s * g ∈ Z ∨ g⁻¹ * s * g ∈ Z₂ ∨
      UType V W Z Z₂ (g⁻¹ * s * g) := by
    rcases h.jst.involution_mem hs hss with hV | hW
    · obtain ⟨g, hg, hty⟩ := h.exists_conj_L hV
      exact ⟨g, h.normalizer_V_le_stab (h.L_le_M hg), hty⟩
    · obtain ⟨g, hg, hty⟩ := h.symm.exists_conj_L hW
      refine ⟨g, h.normalizer_W_le_stab (h.symm.L_le_M hg), ?_⟩
      rcases hty with h1 | h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨by rw [inf_comm]; exact h1.1, h1.2.2, h1.2.1⟩)
  obtain ⟨g, hgH, hty⟩ := hconj
  have hs'1 : g⁻¹ * s * g ≠ 1 := by
    intro h1
    apply hs1
    have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hC' := h.cent_le_stab_of_type hs'1 hty
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hx]
      _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group
  have h3 := (compStab Z).mul_mem ((compStab Z).mul_mem hgH (hC' hx')) ((compStab Z).inv_mem hgH)
  have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e1] at h3
  exact h3

theorem cent_le_stab_of_mem_stab {t : G} (ht : t ∈ compStab Z) (ht2 : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ compStab Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2, pow_two] at this
    exact this
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht2
  have hJH : V ⊔ W ≤ compStab Z := h.J_le_L.trans (h.L_le_M.trans h.normalizer_V_le_stab)
  have hJsyl : IsSylowOf 2 (V ⊔ W) (compStab Z) := h.sylow.of_le hJH le_top
  obtain ⟨k, hk, hkJ⟩ := exists_conj_le_of_isSylowOf hJsyl (Subgroup.zpowers_le.2 ht)
    (isPGroup_zpowers_of_mul_self htt)
  have hkt : k * t * k⁻¹ ∈ V ⊔ W := hkJ (mul_mem_cj k (Subgroup.mem_zpowers t))
  have hktt : (k * t * k⁻¹) * (k * t * k⁻¹) = 1 := by
    calc (k * t * k⁻¹) * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hkt1 : k * t * k⁻¹ ≠ 1 := by
    intro h1
    apply ht1
    have : t = k⁻¹ * (k * t * k⁻¹) * k := by group
    rw [this, h1]
    group
  have hC := h.cent_le_stab_of_mem_J hkt hktt hkt1
  intro x hx
  have hx' : k * x * k⁻¹ ∈ Subgroup.centralizer ({k * t * k⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc k * x * k⁻¹ * (k * t * k⁻¹) = k * (x * t) * k⁻¹ := by group
      _ = k * (t * x) * k⁻¹ := by rw [hx]
      _ = k * t * k⁻¹ * (k * x * k⁻¹) := by group
  have h3 := (compStab Z).mul_mem ((compStab Z).mul_mem ((compStab Z).inv_mem hk) (hC hx')) hk
  have e1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [e1] at h3
  exact h3

theorem stab_stronglyEmbedded (hne : compStab Z ≠ ⊤) :
    CFSG.Open.fusionStronglyEmbedded (compStab Z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := h.isPGroup_J.toSylow h.odd_index_J
  have heven : Even (Nat.card (compStab Z)) := by
    have hZH : Z ≤ compStab Z :=
      (h.Z_le_V.trans Subgroup.le_normalizer).trans h.normalizer_V_le_stab
    have h1 := Subgroup.card_dvd_of_le hZH
    rw [h.card_Z] at h1
    exact even_iff_two_dvd.2 ((dvd_pow_self 2 (by have := h.two_le; omega)).trans h1)
  have hSE := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le hne heven
    (fun t ht ht2 => h.cent_le_stab_of_mem_stab ht ht2) S
    (h.normalizer_J_le_V.trans h.normalizer_V_le_stab)
  exact (CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_iff _).2 hSE

theorem compStab_eq_top : compStab Z = ⊤ := by
  by_contra hne
  have hSE := h.stab_stronglyEmbedded hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
  obtain ⟨⟨z₂, hz₂⟩, hz₂1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.Z₂_ne_bot
  have hz₂1' : z₂ ≠ 1 := fun h1 => hz₂1 (Subtype.ext h1)
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.sq_Z z hz) hz1
  have hz₂o : orderOf z₂ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.jst.sq_V z₂ (h.Z₂_le_V hz₂)) hz₂1'
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Timmesfeld.Bridge.isConj_of_orderOf_eq_two hSE hzo hz₂o)
  have hz₂Z : z₂ ∉ Z := by
    intro hZ
    have : z₂ ∈ Z ⊓ Z₂ := ⟨hZ, hz₂⟩
    rw [h.inf_Z] at this
    exact hz₂1' this
  exact h.not_conj_of_mem_V (h.Z₂_le_V hz₂) hz₂Z hz c hc

theorem connected : ∀ B ∈ zClass Z, ∀ C ∈ zClass Z, Relation.ReflTransGen
    (fun X Y : Subgroup G => X ∈ zClass Z ∧ Y ∈ zClass Z ∧ Commuting X Y) B C := by
  have hZ : ∀ B ∈ zClass Z, Relation.ReflTransGen (CommAdj Z) Z B := by
    rintro B ⟨g, rfl⟩
    have hg : g ∈ compStab Z := h.compStab_eq_top ▸ Subgroup.mem_top g
    exact mem_compStab.1 hg
  intro B hB C hC
  exact (reflTransGen_commAdj_symm (hZ B hB)).trans (hZ C hC)

end G0Core

end CFSG.CGT.PushingUpLit.A78G0

module

public import CFSG.GH74.Generic.S45.PumpA1

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section B

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem S45Conf.card_autGx (h : S45Conf x K T) :
    Nat.card ↥(T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) = 21 := by
  have h1 := orbit_card T.normalizerMonoidHom.range
    (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T))
    (⟨x, h.x_mem⟩ : ↥T) (fun f hf => MulAction.mem_stabilizer_iff.1 hf.2)
    (fun f hf hfx => ⟨hf, MulAction.mem_stabilizer_iff.2 hfx⟩) inf_le_left
  rw [h.card_orbit_x, h.aut_card] at h1
  omega

omit [Finite G] in
theorem S45Conf.autG_mem_R (h : S45Conf x K T) {f : MulAut ↥T}
    (hf : f ∈ T.normalizerMonoidHom.range) {y : ↥T} (hy : (y : G) ∈ Pre x K) :
    ((f y : ↥T) : G) ∈ Pre x K := by
  obtain ⟨⟨n, hn⟩, rfl⟩ := hf
  have := h.conj_mem_R hn (show (y : G) ∈ T ⊓ Pre x K from ⟨y.2, hy⟩)
  exact this.2

omit [Finite G] in
theorem S45Conf.ncard_R_ne_one (h : S45Conf x K T) :
    ({y : ↥T | (y : G) ∈ Pre x K ∧ y ≠ 1} : Set ↥T).ncard = 7 := by
  have h8 : ((((Pre x K).subgroupOf T : Subgroup ↥T) : Set ↥T)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    have h2 := card_subgroupOf_eq (Pre x K) T
    rw [inf_comm] at h2
    exact h2.trans h.R_card
  have h1 : ({y : ↥T | (y : G) ∈ Pre x K ∧ y ≠ 1} : Set ↥T) =
      (((Pre x K).subgroupOf T : Subgroup ↥T) : Set ↥T) \ {1} := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  rw [h1, Set.ncard_sdiff_singleton_of_mem (one_mem _), h8]

theorem S45Conf.exists_autGx_apply_eq (h : S45Conf x K T) {r s : ↥T} (hr : (r : G) ∈ Pre x K)
    (hs : (s : G) ∈ Pre x K) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ f ∈ T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T), f r = s := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set xT : ↥T := ⟨x, h.x_mem⟩ with hxT
  set B := T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) xT
  have hxnot : (xT : G) ∉ Pre x K := (h.fusion x h.x_mem).1 ⟨1, by simp⟩
  have hxTne : xT ≠ 1 := by
    intro h1
    have : (xT : G) = 1 := congrArg Subtype.val h1
    exact hxnot (this ▸ one_mem (Pre x K))
  have hT16 : Nat.card ↥T = 16 := h.card
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 (by rw [h.card_autGx]; norm_num)
  have hb7 : orderOf (b : MulAut ↥T) = 7 := by rw [Subgroup.orderOf_coe]; exact hb
  have hxfix : ∀ g ∈ B, g xT = xT := fun g hg => MulAction.mem_stabilizer_iff.1 hg.2
  have hPle : zpowers (b : MulAut ↥T) ≤ B := by
    rw [zpowers_le]; exact b.2
  have hord7 : ∀ g ∈ zpowers (b : MulAut ↥T), g ≠ 1 → orderOf g = 7 := by
    intro g hg hg1
    have hc : Nat.card ↥(zpowers (b : MulAut ↥T)) = 7 := by rw [Nat.card_zpowers, hb7]
    have h1 : orderOf g ∣ 7 := hc ▸ Subgroup.orderOf_dvd_natCard _ hg
    exact ((Nat.dvd_prime Fact.out).1 h1).resolve_left (fun h' => hg1 (orderOf_eq_one_iff.1 h'))
  have hfree : ∀ g ∈ zpowers (b : MulAut ↥T), g ≠ 1 → ∀ t : ↥T, g t = t → t = 1 ∨ t = xT := by
    intro g hg hg1 t ht
    obtain ⟨u, hu1, hgu, huniq⟩ := fix_seven hT16 g (hord7 g hg hg1)
    have hxu : xT = u := by
      rcases huniq xT (hxfix g (hPle hg)) with h1 | h1
      · exact absurd h1 hxTne
      · exact h1
    rcases huniq t ht with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans hxu.symm)
  have hPinv : ∀ g ∈ zpowers (b : MulAut ↥T), ∀ y : ↥T, (y : G) ∈ Pre x K →
      ((g y : ↥T) : G) ∈ Pre x K := fun g hg y hy => h.autG_mem_R (hPle hg).1 hy
  let ψ : ↥(zpowers (b : MulAut ↥T)) → {y : ↥T // (y : G) ∈ Pre x K ∧ y ≠ 1} := fun g =>
    ⟨(g : MulAut ↥T) r, hPinv g g.2 r hr, by
      intro h1
      apply hr1
      have : (g : MulAut ↥T) r = (g : MulAut ↥T) 1 := by rw [h1, map_one]
      exact (g : MulAut ↥T).injective this⟩
  have hinj : Function.Injective ψ := by
    intro g g' hgg
    have h1 : (g : MulAut ↥T) r = (g' : MulAut ↥T) r := congrArg Subtype.val hgg
    have h2 : ((g' : MulAut ↥T)⁻¹ * (g : MulAut ↥T)) r = r := by
      rw [MulAut.mul_apply, h1]
      exact MulAut.inv_apply_self _ _ _
    have hmem : ((g' : MulAut ↥T)⁻¹ * (g : MulAut ↥T)) ∈ zpowers (b : MulAut ↥T) :=
      mul_mem (inv_mem g'.2) g.2
    by_contra hne
    have hne' : ((g' : MulAut ↥T)⁻¹ * (g : MulAut ↥T)) ≠ 1 := by
      intro h'
      apply hne
      apply Subtype.ext
      exact (inv_mul_eq_one.1 h').symm
    rcases hfree _ hmem hne' r h2 with h3 | h3
    · exact hr1 h3
    · exact hxnot (h3 ▸ hr)
  have hc7 : Nat.card ↥(zpowers (b : MulAut ↥T)) = 7 := by rw [Nat.card_zpowers, hb7]
  have hcardR : Nat.card {y : ↥T // (y : G) ∈ Pre x K ∧ y ≠ 1} = 7 :=
    (Nat.card_coe_set_eq {y : ↥T | (y : G) ∈ Pre x K ∧ y ≠ 1}).trans h.ncard_R_ne_one
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le (by rw [hcardR, hc7])
  obtain ⟨g, hg⟩ := hbij.2 ⟨s, hs, hs1⟩
  exact ⟨(g : MulAut ↥T), hPle g.2, congrArg Subtype.val hg⟩


theorem S45Conf.mem_orbit_v_iff (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K)
    (hv1 : v ≠ 1) (y : ↥T) :
    y ∈ MulAction.orbit ↥T.normalizerMonoidHom.range v ↔ (y : G) ∈ Pre x K ∧ y ≠ 1 := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨h.autG_mem_R f.2 hv, ?_⟩
    intro h1
    apply hv1
    have : (f : MulAut ↥T) v = (f : MulAut ↥T) 1 := by rw [map_one]; exact h1
    exact (f : MulAut ↥T).injective this
  · rintro ⟨hy, hy1⟩
    obtain ⟨f, hf, hfv⟩ := h.exists_autGx_apply_eq hv hy hv1 hy1
    exact ⟨⟨f, hf.1⟩, hfv⟩

theorem S45Conf.card_orbit_v (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1) :
    Nat.card (MulAction.orbit ↥T.normalizerMonoidHom.range v) = 7 := by
  have hset : (MulAction.orbit ↥T.normalizerMonoidHom.range v : Set ↥T) =
      {y : ↥T | (y : G) ∈ Pre x K ∧ y ≠ 1} := by
    ext y
    exact h.mem_orbit_v_iff hv hv1 y
  rw [hset, Nat.card_coe_set_eq]
  exact h.ncard_R_ne_one

theorem S45Conf.card_autGv (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1) :
    Nat.card ↥(T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v) = 24 := by
  have h1 := orbit_card T.normalizerMonoidHom.range
    (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v) v
    (fun f hf => MulAction.mem_stabilizer_iff.1 hf.2)
    (fun f hf hfv => ⟨hf, MulAction.mem_stabilizer_iff.2 hfv⟩) inf_le_left
  rw [h.card_orbit_v hv hv1, h.aut_card] at h1
  omega

end B

end CFSG.GH74.Generic.S45

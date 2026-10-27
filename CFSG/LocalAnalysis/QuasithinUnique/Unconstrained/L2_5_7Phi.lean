module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Thompson
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Gamma
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {n : ℕ} {K₁ K₂ V V' : Subgroup G} {s : G}

namespace L257

omit [Finite G] in
theorem isMaxElemAbelian_conjugate {S A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian S (CFSG.conjugate A g) := by
  rw [conjugate_eq_cjSub]
  exact isMaxElemAbelian_cjSub (inv_mem hg) hA

theorem mem_of_mem_center_of_max {S A : Subgroup G} (hA : IsMaxElemAbelian S A) {z : G}
    (hz : z ∈ centerOf S) (hz2 : z ^ 2 = 1) : z ∈ A := by
  have hZ : IsElemAbelian 2 (Subgroup.zpowers z) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      apply Subtype.ext
      show (x : G) * y = y * x
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self z i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hz.2 a (hA.1 ha)).symm.symm i).eq)
  have hsup : IsElemAbelian 2 (A ⊔ Subgroup.zpowers z) :=
    B2F.isElemAbelian_sup_of_commute hA.2.1 hZ hcomm
  have hle : A ⊔ Subgroup.zpowers z ≤ S := sup_le hA.1 (Subgroup.zpowers_le.mpr hz.1)
  have hcard : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≤ Nat.card A := hA.2.2 _ hle hsup
  have heq : A = A ⊔ Subgroup.zpowers z := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

omit [Finite G] in
theorem relIndex_eq_two_of_xor {X Y : Subgroup G} (a : G) (ha : a ∈ X)
    (h : ∀ g ∈ X, (g ∈ Y ∧ g * a ∉ Y) ∨ (g ∉ Y ∧ g * a ∈ Y)) : Y.relIndex X = 2 := by
  unfold Subgroup.relIndex
  refine Subgroup.index_eq_two_iff.mpr ⟨⟨a, ha⟩, fun b => ?_⟩
  have := h (b : G) b.2
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩

omit [Finite G] in
theorem conjugate_sup' (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem z_mem_centerOf_S (N : Notation25 hs) : N.z ∈ centerOf N.S :=
  ⟨N.tuple.center_le N.tuple.z_mem,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.tuple.le_T) N.tuple.z_mem.2⟩

end L257

namespace Conf257

variable (c : Conf257 N n K₁ K₂ V V' s)

omit c in
theorem S_le_normalizer_RC : N.S ≤ Subgroup.normalizer (thompsonJ N.SC : Set G) :=
  N.S_le_normalizer_SC.trans (normalizer_le_normalizer_thompsonJ N.SC)

include c in
theorem conjugate_RC : CFSG.conjugate (thompsonJ N.SC) s = thompsonJ N.SC :=
  BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (S_le_normalizer_RC c.setup.s_mem)

include c in
theorem K_le_centralizer_RC : N.K ≤ Subgroup.centralizer (thompsonJ N.SC : Set G) := fun k hk =>
  Subgroup.mem_centralizer_iff.mpr fun _ hr =>
    (Subgroup.mem_centralizer_iff.mp (c.SC_le_centralizer (thompsonJ_le_self _ hr)) k hk).symm

include c in
theorem sup_RC_inf_K {W : Subgroup G} (hW : W = V ∨ W = V') :
    (W ⊔ thompsonJ N.SC) ⊓ N.K = W := by
  refine le_antisymm ?_ (le_inf le_sup_left (c.rad_le_K hW))
  intro x hx
  obtain ⟨w, hw, r, hr, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => c.rad_comm hW ha (c.SC_le_centralizer (thompsonJ_le_self _ hb))) hx.1
  have hrK : r ∈ N.K := by
    have := N.K.mul_mem (N.K.inv_mem (c.rad_le_K hW hw)) hx.2
    simpa using this
  have hrZ : r ∈ centerOf N.K := ⟨hrK, c.SC_le_centralizer (thompsonJ_le_self _ hr)⟩
  exact W.mul_mem hw (c.rad_center_le hW hrZ)

variable (hel : IsElemAbelian 2 (thompsonJ N.SC))

include hel in
theorem eq_RC_of_max {E : Subgroup G} (hE : IsMaxElemAbelian N.SC E) : E = thompsonJ N.SC := by
  have hle : E ≤ thompsonJ N.SC := le_iSup₂_of_le E hE le_rfl
  exact Subgroup.eq_of_le_of_card_ge hle (hE.2.2 _ (thompsonJ_le_self _) hel)

include hel in
theorem isMax_RC : IsMaxElemAbelian N.SC (thompsonJ N.SC) := by
  obtain ⟨E₀, hE₀⟩ := exists_isMaxElemAbelian N.SC
  have := eq_RC_of_max hel hE₀
  rwa [this] at hE₀

include c hel in
theorem max_cases {A : Subgroup G} (hA : IsMaxElemAbelian N.S A) :
    A = V ⊔ thompsonJ N.SC ∨ A = V' ⊔ thompsonJ N.SC := by
  obtain ⟨E, hE, h⟩ := c.exists_of_isMaxElemAbelian hA
  rw [eq_RC_of_max hel hE] at h
  exact h

include c in
theorem Q_ne_Q' : V ⊔ thompsonJ N.SC ≠ V' ⊔ thompsonJ N.SC := by
  intro h
  apply c.geom.V_ne
  rw [← c.sup_RC_inf_K (Or.inl rfl), ← c.sup_RC_inf_K (Or.inr rfl), h]

include c in
theorem conjugate_Q : CFSG.conjugate (V ⊔ thompsonJ N.SC) s = V' ⊔ thompsonJ N.SC := by
  rw [L257.conjugate_sup', c.conjugate_V_eq, c.conjugate_RC]

include c hel in
theorem xor_aux {g : G} (hg : g ∈ Subgroup.normalizer (N.S : Set G)) :
    (g ∈ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G) ∧
        g * s⁻¹ ∉ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G)) ∨
      (g ∉ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G) ∧
        g * s⁻¹ ∈ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G)) := by
  set Q := V ⊔ thompsonJ N.SC with hQ
  have hcQ : CFSG.conjugate Q s = V' ⊔ thompsonJ N.SC := c.conjugate_Q
  have hAg : CFSG.conjugate Q g = Q ∨ CFSG.conjugate Q g = V' ⊔ thompsonJ N.SC :=
    c.max_cases hel (L257.isMaxElemAbelian_conjugate hg
      (c.isMaxElemAbelian_of_exists (Or.inl rfl) (isMax_RC hel) : IsMaxElemAbelian N.S Q))
  by_cases hgN : g ∈ Subgroup.normalizer (Q : Set G)
  · left
    refine ⟨hgN, fun h => ?_⟩
    have h1 : CFSG.conjugate Q (g * s⁻¹) = Q :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr h
    rw [← BenderBranch.conjugate_conjugate,
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgN] at h1
    have h2 : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp h1
    have h3 : s ∈ Subgroup.normalizer (Q : Set G) := by simpa using inv_mem h2
    have h4 := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr h3
    rw [hcQ] at h4
    exact c.Q_ne_Q' h4.symm
  · right
    refine ⟨hgN, ?_⟩
    have hne : CFSG.conjugate Q g ≠ Q := fun e =>
      hgN (BenderBranch.conjugate_eq_iff_mem_normalizer.mp e)
    have hg' : CFSG.conjugate Q g = V' ⊔ thompsonJ N.SC := hAg.resolve_left hne
    have key : CFSG.conjugate Q (g * s⁻¹) = Q := by
      rw [← BenderBranch.conjugate_conjugate, hg', ← hcQ, BenderBranch.conjugate_conjugate,
        mul_inv_cancel, BenderBranch.conjugate_one]
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp key

include c hel in
theorem relIndex_normalizer_Q :
    (N.S ⊓ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G)).relIndex N.S = 2 := by
  refine L257.relIndex_eq_two_of_xor (s⁻¹) (N.S.inv_mem c.setup.s_mem) fun g hg => ?_
  rcases c.xor_aux hel (Subgroup.le_normalizer hg) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨⟨hg, h1⟩, fun h => h2 h.2⟩
  · exact Or.inr ⟨fun h => h1 h.2, ⟨N.S.mul_mem hg (N.S.inv_mem c.setup.s_mem), h2⟩⟩

include c hel in
theorem isConfining_normalizer_Q :
    IsConfining M (N.S ⊓ Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G)) := by
  set Q := V ⊔ thompsonJ N.SC with hQ
  have hQS : Q ≤ N.S := sup_le c.V_le_S ((thompsonJ_le_self _).trans c.SC_le_S)
  have hVN : N.SK ≤ Subgroup.normalizer (V : Set G) := c.SK_le_K₁.trans c.K₁_le_normalizer_V
  have hRCN : N.SK ≤ Subgroup.normalizer (thompsonJ N.SC : Set G) :=
    ((L257.SK_le_K N).trans c.K_le_centralizer_RC).trans (Subgroup.centralizer_le_normalizer _)
  have hJN : thompsonJ N.S ≤ Subgroup.normalizer (Q : Set G) := by
    rw [c.thompsonJ_eq]
    exact sup_le (B2F.le_normalizer_sup hVN hRCN) (le_sup_right.trans Subgroup.le_normalizer)
  have hSCcV : N.SC ≤ Subgroup.centralizer (V : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      c.V_comm_centralizer hv (c.SC_le_centralizer ha)
  have hSCV : N.SC ≤ Subgroup.normalizer (V : Set G) :=
    hSCcV.trans (Subgroup.centralizer_le_normalizer _)
  have hSC : N.SC ≤ N.S ⊓ Subgroup.normalizer (Q : Set G) :=
    le_inf c.SC_le_S (B2F.le_normalizer_sup hSCV (c.SC_le_S.trans (S_le_normalizer_RC)))
  have hQR' : Q ≤ N.S ⊓ Subgroup.normalizer (Q : Set G) := le_inf hQS Subgroup.le_normalizer
  refine IsGamma0.isConfining_of_relIndex_two_of_le hs.setting N.tuple.gamma0
    N.tuple.sylow_inf inf_le_left (c.relIndex_normalizer_Q hel)
    (le_inf (thompsonJ_le_self _) hJN) (by rw [← N.SC_eq]; exact hSC) fun y hy => ?_
  refine ⟨hy.1, ?_⟩
  have hyQ : y ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQR') hy.2
  exact Subgroup.centralizer_le_normalizer _ hyQ

include c hel in
theorem card_TQ_ge :
    Nat.card N.S ≤ Nat.card ↥(Subgroup.normalizer ((V ⊔ thompsonJ N.SC : Subgroup G) : Set G) ⊓
      (T ⊓ Subgroup.normalizer (N.S : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := V ⊔ thompsonJ N.SC with hQ
  set X := T ⊓ Subgroup.normalizer (N.S : Set G) with hX
  have hSX : N.S ≤ X := le_inf N.tuple.le_T Subgroup.le_normalizer
  have hidx : (Subgroup.normalizer (Q : Set G)).relIndex X = 2 := by
    refine L257.relIndex_eq_two_of_xor (s⁻¹) (X.inv_mem (hSX c.setup.s_mem)) fun g hg => ?_
    exact c.xor_aux hel hg.2
  have hmul := Subgroup.relIndex_mul_card (Subgroup.normalizer (Q : Set G)) X
  rw [hidx] at hmul
  obtain ⟨x, hxX, hxS⟩ := exists_mem_inf_normalizer_of_ne (p := 2)
    hs.setting.sylow.isPGroup N.tuple.le_T N.tuple.lt.ne
  have hlt : N.S < X := lt_of_le_of_ne hSX fun e => hxS (e ▸ hxX)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSX
  have hcard_lt : Nat.card N.S < Nat.card X := Subgroup.card_lt_of_lt hlt
  have hSpos : 0 < Nat.card N.S := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk1
    push Not at hk1
    interval_cases k
    · exact absurd hk Nat.card_pos.ne'
    · omega
  have : 2 * Nat.card N.S ≤ Nat.card X := by
    rw [hk]
    nlinarith
  omega

include c in
theorem not_isElemAbelian_thompsonJ_SC : ¬ IsElemAbelian 2 (thompsonJ N.SC) := by
  intro hel
  set Q := V ⊔ thompsonJ N.SC with hQ
  have hQmax : IsMaxElemAbelian N.S Q := c.isMaxElemAbelian_of_exists (Or.inl rfl) (isMax_RC hel)
  have hzQ : N.z ∈ Q :=
    L257.mem_of_mem_center_of_max hQmax (L257.z_mem_centerOf_S N) N.tuple.z_sq
  have hQ2 : IsPGroup 2 Q := B2F.isPGroup_of_isElemAbelian hQmax.2.1
  have hconf := c.isConfining_normalizer_Q hel
  have hTQ_le_T : Subgroup.normalizer (Q : Set G) ⊓ (T ⊓ Subgroup.normalizer (N.S : Set G)) ≤ T :=
    inf_le_right.trans inf_le_left
  have hle : N.S ⊓ Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (Q : Set G) ⊓ (T ⊓ Subgroup.normalizer (N.S : Set G)) :=
    le_inf inf_le_right (le_inf (inf_le_left.trans N.tuple.le_T)
      (inf_le_left.trans Subgroup.le_normalizer))
  have hconfTQ := hconf.of_le (hs.setting.sylow.isPGroup.to_le hTQ_le_T) hle
  have hK₁N : K₁ ≤ Subgroup.normalizer (Q : Set G) :=
    B2F.le_normalizer_sup c.K₁_le_normalizer_V
      ((c.setup.pair.lt_K₁.le.trans c.K_le_centralizer_RC).trans
        (Subgroup.centralizer_le_normalizer _))
  exact N.false_of_normalizer_witness hQ2 hzQ hconfTQ inf_le_left (c.card_TQ_ge hel)
    fun h => c.not_K₁_le_M (hK₁N.trans h)

end Conf257

end CFSG.QuasithinUnique

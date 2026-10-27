module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.TypeArg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core73d
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem isElemAbelian_of_sq_one {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 ↥E :=
  { is_comm := ⟨fun a b => Subtype.ext
      (B.comm_of_forall_sq hE a.2 b.2)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      simpa [pow_two] using hE x x.2 }

namespace Cfg7

theorem t_ord (h : Cfg7 G z S K₁ K₂ t u q) : orderOf t = 2 := by
  obtain ⟨g, hg⟩ := M.exists_conj_inv h.ch.t_conj
  exact orderOf_conj_z h.std.std hg

theorem t_sq (h : Cfg7 G z S K₁ K₂ t u q) : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two h.t_ord

theorem t_inv (h : Cfg7 G z S K₁ K₂ t u q) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem mem_K₂_iff (h : Cfg7 G z S K₁ K₂ t u q) (x : G) : x ∈ K₂ ↔ t * x * t⁻¹ ∈ K₁ := by
  have := ((interchanges_iff t).1 h.ch.t_swap).1
  rw [← this]; exact M.mem_cj

theorem mem_K₁_iff (h : Cfg7 G z S K₁ K₂ t u q) (x : G) : x ∈ K₁ ↔ t * x * t⁻¹ ∈ K₂ := by
  have := ((interchanges_iff t).1 h.ch.t_swap).2
  rw [← this]; exact M.mem_cj

theorem t_nS1 (h : Cfg7 G z S K₁ K₂ t u q) : t ∉ S1 S K₁ := by
  intro ht
  have h1 : t ∈ normalizer (K₁ : Set G) := ht.2
  have h2 := M.cj_eq_iff_normalizer.2 h1
  have h3 := ((interchanges_iff t).1 h.ch.t_swap).1
  exact h.std.std.ne (h2.symm.trans h3)

theorem S1_relIndex (h : Cfg7 G z S K₁ K₂ t u q) : (S1 S K₁).relIndex S = 2 := by
  have h1 : (S1 S K₁).relIndex S ≤ 2 := h.std.p66.2.1.1
  have h2 : (S1 S K₁).relIndex S ≠ 1 := fun h' =>
    h.t_nS1 (Subgroup.relIndex_eq_one.1 h' h.ch.t_mem)
  have h3 := C73.relIndex_pos (S1 S K₁) S
  omega

theorem cmap_t_K₁ (h : Cfg7 G z S K₁ K₂ t u q) : cmap t K₁ = K₂ := by
  ext x
  rw [mem_cmap, h.mem_K₂_iff x, h.t_inv]

theorem cmap_t_K₂ (h : Cfg7 G z S K₁ K₂ t u q) : cmap t K₂ = K₁ := by
  ext x
  rw [mem_cmap, h.mem_K₁_iff x, h.t_inv]

theorem tP₁ (h : Cfg7 G z S K₁ K₂ t u q) : ∀ x ∈ Pof S K₁, t * x * t⁻¹ ∈ Pof S K₂ := fun x hx =>
  ⟨S.mul_mem (S.mul_mem h.ch.t_mem hx.1) (S.inv_mem h.ch.t_mem), (h.mem_K₁_iff x).1 hx.2⟩

theorem tP₂ (h : Cfg7 G z S K₁ K₂ t u q) : ∀ x ∈ Pof S K₂, t * x * t⁻¹ ∈ Pof S K₁ := fun x hx =>
  ⟨S.mul_mem (S.mul_mem h.ch.t_mem hx.1) (S.inv_mem h.ch.t_mem), (h.mem_K₂_iff x).1 hx.2⟩

theorem tQ₁ (h : Cfg7 G z S K₁ K₂ t u q) : ∀ x ∈ Qof S K₁, t * x * t⁻¹ ∈ Qof S K₂ := by
  intro x hx
  refine ⟨S.mul_mem (S.mul_mem h.ch.t_mem hx.1) (S.inv_mem h.ch.t_mem), ?_⟩
  have h1 := cmap_mem_centralizerSection hx.2 t
  rw [← pPrimeCoreOf_cmap, h.cmap_t_K₁] at h1
  exact h1

theorem tQ₂ (h : Cfg7 G z S K₁ K₂ t u q) : ∀ x ∈ Qof S K₂, t * x * t⁻¹ ∈ Qof S K₁ := by
  intro x hx
  refine ⟨S.mul_mem (S.mul_mem h.ch.t_mem hx.1) (S.inv_mem h.ch.t_mem), ?_⟩
  have h1 := cmap_mem_centralizerSection hx.2 t
  rw [← pPrimeCoreOf_cmap, h.cmap_t_K₂] at h1
  exact h1

theorem hasSL2_odd (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    HasSL2Model (HatT K) Odd := by
  rcases hK with rfl | rfl
  · obtain ⟨F, hF, hFin, hq, he⟩ := h.ch.hq₁
    exact ⟨F, hF, hFin, by rw [show Nat.card F = q from hq]; exact h.ch.q_odd, he⟩
  · obtain ⟨F, hF, hFin, hq, he⟩ := h.ch.hq₂
    exact ⟨F, hF, hFin, by rw [show Nat.card F = q from hq]; exact h.ch.q_odd, he⟩

theorem transfer_gen (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ (Y : Subgroup G) (v : G), Y ≤ S → Y.relIndex S = 2 → v ∈ S → v ∉ Y →
      (∀ w ∈ S, w ∉ Y → orderOf v ≤ orderOf w) →
      ∃ g : G, g⁻¹ * v * g ∈ Y ∧ ∀ x ∈ S, x * v = v * x → g⁻¹ * x * g ∈ S := by
  intro Y v hYS hY2 hvS hvY hord
  have hM := h.m4 hII
  have hSsyl : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In S ⊤ := hM.S_top
  have hsimple := h.std.std.simple
  have hY1 : Y ≠ S := by
    intro e
    rw [e] at hY2
    simp at hY2
  have hYn : ∀ s ∈ S, ∀ q ∈ Y, s * q * s⁻¹ ∈ Y := fun s hs q hq =>
    A.conj_mem_of_relIndex_two hY2 hs hq hYS
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Y := by
    refine ⟨v, hvS, fun s hs => ?_⟩
    rcases A.relIndex_two_pigeon hY2 hvS hs with h1 | h1 | h1
    · exact absurd h1 hvY
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * v * g = y) →
      CFSG.GH74.GLS.Stage1.Thm6.Sec12.IsExtremal S y → y ∈ Y ∨ v⁻¹ * y ∈ Y := by
    intro y hyS _ _
    rcases A.relIndex_two_pigeon hY2 hvS hyS with h1 | h1 | h1
    · exact absurd h1 hvY
    · exact Or.inl h1
    · exact Or.inr h1
  rcases CFSG.GH74.GLS.Stage1.Thm6.Sec12.ig_15_15 G S Y v hSsyl hYS hYn hY1 hcyc hvS hvY hord hext
    with ⟨N, hN, hcycN, -, hvN⟩ | ⟨g, hgY, -, hgC⟩
  · exfalso
    rcases hsimple.1.eq_bot_or_eq_top_of_normal N with e | e
    · subst e
      obtain ⟨a, b, hab⟩ := hsimple.2.1
      have hcycG : IsCyclic G := isCyclic_of_surjective
        (QuotientGroup.quotientBot (G := G)).toMonoidHom
        (QuotientGroup.quotientBot (G := G)).surjective
      have hc : IsMulCommutative G := IsCyclic.isMulCommutative
      exact hab (hc.is_comm.comm a b)
    · exact hvN (e ▸ Subgroup.mem_top v)
  · refine ⟨g, hgY, fun x hxS hxv => ?_⟩
    exact (hgC x ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 hxv⟩).1

theorem transfer (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ (Y : Subgroup G) (v : G), Y ≤ S → Y.relIndex S = 2 → v ∈ S → v ∉ Y → v * v = 1 →
      ∃ g : G, g⁻¹ * v * g ∈ Y ∧ ∀ x ∈ S, x * v = v * x → g⁻¹ * x * g ∈ S := by
  intro Y v hYS hY2 hvS hvY hv2
  have hv1 : v ≠ 1 := fun e => hvY (e ▸ Y.one_mem)
  have hvo : orderOf v = 2 := orderOf_eq_prime (by simpa [pow_two] using hv2) hv1
  refine h.transfer_gen hII Y v hYS hY2 hvS hvY ?_
  intro w _ hwY
  have hw1 : w ≠ 1 := fun e => hwY (e ▸ Y.one_mem)
  have h1 : orderOf w ≠ 1 := fun e => hw1 (orderOf_eq_one_iff.1 e)
  have h2 := orderOf_pos w
  rw [hvo]; omega

theorem ctx73 (hII : II4_4_4_center) (hq : II4_4_quat) (h14j : IVK_1_4j_lifted) (h225 : IV2_2_5)
    (h : Cfg7 G z S K₁ K₂ t u q) :
    C73.Ctx73 z t S (Pof S K₁) (Pof S K₂) (Qof S K₁) (Qof S K₂) (S1 S K₁) where
  S2 := h.S_pgroup hII
  z_sq := h.z_sq
  z_ne := h.z_ne
  zP₁ := h.z_mem_P hII (Or.inl rfl)
  zP₂ := h.z_mem_P hII (Or.inr rfl)
  P₁S := inf_le_left
  P₂S := inf_le_left
  S₁S := inf_le_left
  P₁Q₂ := h.P₁_le_Q₂ hII
  P₂Q₁ := h.P₂_le_Q₁ hII
  Q₁S₁ := h.Q₁_le_S1
  Q₂S₁ := h.Q₂_le_S1 hII
  P₁P₂ := h.P_comm hII
  Q₁P₁ := h.Q_comm_P hII (Or.inl rfl)
  Q₂P₂ := h.Q_comm_P hII (Or.inr rfl)
  P₁₂ := (h.P_inf hII).le
  P₁Q₁ := h.P_inf_Q hII (Or.inl rfl)
  P₂Q₂ := h.P_inf_Q hII (Or.inr rfl)
  Q₁Q₂ := h.Q_inf_Q hII
  S₁Q₁ := h.S1_normalizes_Q₁
  S₁Q₂ := h.S1_normalizes_Q₂ hII
  PnS := h.S_normalizes_P hII
  t_mem := h.ch.t_mem
  t_sq := h.t_sq
  t_nS₁ := h.t_nS1
  S₁idx := h.S1_relIndex
  tP₁ := h.tP₁
  tP₂ := h.tP₂
  tQ₁ := h.tQ₁
  tQ₂ := h.tQ₂
  Q₁idx := h.std.p66.1.2.2.1
  Q₂idx := h.std.p66.1.2.2.2
  S₁Pidx := by rw [← h.Pz_eq_sup hII]; exact h.std.p66.2.1.2
  d₁ := fun h4 => by
    rw [← h.Pz_eq_sup hII] at h4
    exact (h.std.p66.2.2.2 h4).2
  d₂ := fun h4 => by
    rw [← h.Pz_eq_sup hII] at h4 ⊢
    obtain ⟨hN, ⟨e⟩⟩ := (h.std.p66.2.2.2 h4).1
    exact B.sq_mem_of_iso_E4 e
  P₁card := ((h.m4 hII).zs K₁ (Or.inl rfl)).2
  P₂card := ((h.m4 hII).zs K₂ (Or.inr rfl)).2
  P₁q := by
    obtain ⟨n, hn3, ⟨e⟩⟩ := hq G h.std.std.simple z h.std.std.orderOf_z S K₁ h.std.std.sylow
      (h.std.std.comp_isPCompIn (Or.inl rfl)) (h.std.std.comp_pRank (Or.inl rfl))
    exact ⟨2 ^ (n - 2), ⟨by positivity⟩, ⟨e⟩⟩
  P₂q := by
    obtain ⟨n, hn3, ⟨e⟩⟩ := hq G h.std.std.simple z h.std.std.orderOf_z S K₂ h.std.std.sylow
      (h.std.std.comp_isPCompIn (Or.inr rfl)) (h.std.std.comp_pRank (Or.inr rfl))
    exact ⟨2 ^ (n - 2), ⟨by positivity⟩, ⟨e⟩⟩
  Q₁q := by
    obtain ⟨n, hn3, ⟨e⟩⟩ := h.std.p66.1.1
    exact ⟨2 ^ (n - 2), ⟨by positivity⟩, ⟨e⟩⟩
  Q₂q := by
    obtain ⟨n, hn3, ⟨e⟩⟩ := h.std.p66.1.2.1
    exact ⟨2 ^ (n - 2), ⟨by positivity⟩, ⟨e⟩⟩
  C₁ := fun x hx hc =>
    ⟨hx.1, h14j G z S K₁ K₂ h.std.std K₁ (by simp) (h.hasSL2_odd (Or.inl rfl)) x hx.1 hx.2 hc⟩
  C₂ := fun x hx hc =>
    ⟨hx.1, h14j G z S K₁ K₂ h.std.std K₂ (by simp) (h.hasSL2_odd (Or.inr rfl)) x hx.1
      (h.S1_norm₂ hII hx) hc⟩
  nf := fun u hu hc => h.std.nonfused u (by rw [h.Pz_eq_sup hII]; exact hu) hc
  tr := h.transfer hII
  mix := h.mix hII
  h225 := by
    intro T R₁ R₂ X₁ X₂ U hT hTR hTX hn₁ hn₂ hX₁ hX₂ hXX hc₁ hc₂ hR₁ hR₂ hR₂X hR₁X hC₁ hC₂ hU hUc
      hRU
    have hF : IVK.IsFourSubgroup U :=
      ⟨isElemAbelian_of_sq_one hU, hUc⟩
    exact h225 G T R₁ R₂ X₁ X₂ U z hT hTR hTX hn₁ hn₂ ⟨by norm_num, hX₁⟩ ⟨by norm_num, hX₂⟩ hXX hc₁
      hc₂ ⟨by norm_num, hR₁⟩ ⟨by norm_num, hR₂⟩ hR₂X hR₁X hC₁ hC₂ hF hRU

end Cfg7

theorem lemma_7_3 (hII : II4_4_4_center) (hq : II4_4_quat) (h14j : IVK_1_4j_lifted)
    (h225 : IV2_2_5) : Lemma7_3 := by
  intro G _ _ z S K₁ K₂ t u q h
  obtain ⟨h1, h2, h3⟩ := C73.core73 (h.ctx73 hII hq h14j h225)
  refine ⟨?_, h2, h3⟩
  rw [h.Pz_eq_sup hII]
  exact h1

end CFSG.GH74.GLS.Stage1.Thm3.Sec7

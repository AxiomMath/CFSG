module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineGammaFiveOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.SectionRank Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def PGroupExtraspecialNormalizer (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : Subgroup G, IsExtraspecialExpP p Y → ∀ M : Subgroup G,
    (∀ E : Subgroup G, E ≤ Y → IsElemAbelian p E → Nat.card E = p ^ 2 →
      normalizer (E : Set G) ≤ M) →
    normalizer (Y : Set G) ≤ M ∨
      ∀ T : Subgroup G, T ≤ normalizer (Y : Set G) → IsPGroup p T →
        T ≤ Y ⊔ centralizer (Y : Set G)

@[expose] def PGroupExtraspecialOmegaOne (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y C : Subgroup G, IsExtraspecialExpP p Y → 2 ≤ Open.pRank p Y →
    C ≤ centralizer (Y : Set G) → Open.pRank p (Y ⊔ C) ≤ 2 → ∀ x ∈ Y ⊔ C, x ^ p = 1 → x ∈ Y

namespace PGroupL515

theorem isPGroup_of_pow_eq_one {p : ℕ} {H : Subgroup G} (h : ∀ x ∈ H, x ^ p = 1) :
    IsPGroup p H := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (h x x.2)⟩

theorem mem_map_conj_iff {H : Subgroup G} {m t : G} :
    t ∈ H.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * t * m ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro ht
    exact ⟨m⁻¹ * t * m, ht, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem normalizer_le_of_conj {H M : Subgroup G} {m : G} (hm : m ∈ M)
    (h : normalizer ((H.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    normalizer (H : Set G) ≤ M := by
  intro g hg
  have h1 := h (conj_mem_normalizer (T := H.map (MulAut.conj m).toMonoidHom) (T₀ := H)
    (fun t => mem_map_conj_iff) hg)
  have e : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm

theorem exists_mem_conj_le_sylow {p : ℕ} [Fact p.Prime] {M K : Subgroup G} (V : Sylow p G)
    (hVM : (V : Subgroup G) ≤ M) (hKM : K ≤ M) (hK : IsPGroup p K) :
    ∃ m ∈ M, K.map (MulAut.conj m).toMonoidHom ≤ V := by
  have hK' : IsPGroup p (K.subgroupOf M) := hK.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨P', hP'⟩ := hK'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P' (V.subtype hVM)
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hkP : (⟨k, hKM hk⟩ : M) ∈ (P' : Subgroup M) := hP' (Subgroup.mem_subgroupOf.mpr hk)
  have h1 : g * ⟨k, hKM hk⟩ * g⁻¹ ∈ ((g • P' : Sylow p M) : Subgroup M) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hkP, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
  simpa [MulAut.conj_apply] using h1

end PGroupL515

open PGroupL515

theorem pGroupLemmaFiveOneFive_of (h1 : PGroupRankTwoCharSubgroup G)
    (h2 : PGroupExtraspecialNormalizer G) (h3 : PGroupExtraspecialOmegaOne G) :
    PGroupLemmaFiveOneFive G := by
  intro p hp hp2 M V hVM hV3 hW hE
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have ha : ∀ Q : Subgroup G, Q ≤ V → 2 ≤ Open.pRank p Q →
      3 ≤ Open.pRank p (Q ⊔ ((V : Subgroup G) ⊓ centralizer (Q : Set G))) →
      normalizer (Q : Set G) ≤ M := fun Q hQ hQ2 hQ3 =>
    (le_sSup ⟨Q, hQ, hQ2, hQ3, rfl⟩ : normalizer (Q : Set G) ≤ GLBWeakCore p V).trans hW
  have hb : ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
      normalizer (E : Set G) ≤ M := by
    intro E hEM hEe hEc
    obtain ⟨E3, hE3le, hE3e, hE3c⟩ := exists_pRank hp1 (centralizer (E : Set G) ⊓ M)
    have h3 := hE E hEM hEe hEc
    have hE3C : E3 ≤ centralizer (E : Set G) := hE3le.trans inf_le_left
    have hEC3 : E ≤ centralizer (E3 : Set G) := Subgroup.le_centralizer_iff.mp hE3C
    have hKp : IsPGroup p (E ⊔ E3 : Subgroup G) :=
      (isPGroup_of_pow_eq_one hEe.2).to_sup_of_normal_right' (isPGroup_of_pow_eq_one hE3e.2)
        (hEC3.trans ((Subgroup.centralizer_le_normalizer _)))
    obtain ⟨m, hm, hmK⟩ := exists_mem_conj_le_sylow V hVM (sup_le hEM (hE3le.trans inf_le_right))
      hKp
    apply normalizer_le_of_conj hm
    have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
    have hE'V : E.map (MulAut.conj m).toMonoidHom ≤ V :=
      (Subgroup.map_mono le_sup_left).trans hmK
    have hE3'V : E3.map (MulAut.conj m).toMonoidHom ≤ V :=
      (Subgroup.map_mono le_sup_right).trans hmK
    refine ha _ hE'V ?_ ?_
    · exact le_pRank hp1 le_rfl (isElemAbelian_map hEe _)
        (by rw [Subgroup.card_map_of_injective hinj, hEc])
    · refine le_trans h3 (le_pRank hp1 (E := E3.map (MulAut.conj m).toMonoidHom) ?_
        (isElemAbelian_map hE3e _) (by rw [Subgroup.card_map_of_injective hinj, hE3c]))
      refine le_trans ?_ le_sup_right
      refine le_inf hE3'V ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hab : b * a = a * b := (Subgroup.mem_centralizer_iff.mp (hE3C ha) b hb)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc m * b * m⁻¹ * (m * a * m⁻¹) = m * (b * a) * m⁻¹ := by group
        _ = m * (a * b) * m⁻¹ := by rw [hab]
        _ = m * a * m⁻¹ * (m * b * m⁻¹) := by group
  refine sSup_le ?_
  rintro _ ⟨Q, hQV, hQ2, rfl⟩
  by_cases hQ3 : 3 ≤ Open.pRank p (Q ⊔ ((V : Subgroup G) ⊓ centralizer (Q : Set G)))
  · exact ha Q hQV hQ2 hQ3
  have hQeq : Open.pRank p Q = 2 := by
    have := pRank_mono hp1
      (le_sup_left : Q ≤ Q ⊔ ((V : Subgroup G) ⊓ centralizer (Q : Set G)))
    omega
  obtain ⟨Y, hYQ, hNY, hY2, hYcase⟩ := h1 p hp hp2 Q (V.isPGroup'.to_le hQV) hQeq
  refine le_trans hNY ?_
  have hYV : Y ≤ V := hYQ.trans hQV
  rcases hYcase with ⟨hYe, hYc⟩ | hYx
  · exact hb Y (hYV.trans hVM) hYe hYc
  by_cases hY3 : 3 ≤ Open.pRank p (Y ⊔ ((V : Subgroup G) ⊓ centralizer (Y : Set G)))
  · exact ha Y hYV hY2 hY3
  rcases h2 p hp hp2 Y hYx M
    (fun E hEY hEe hEc => hb E (hEY.trans (hYV.trans hVM)) hEe hEc) with hN | hT
  · exact hN
  exfalso
  set C := (V : Subgroup G) ⊓ centralizer (Y : Set G) with hC
  set R := Y ⊔ C with hR
  have hR2 : Open.pRank p R ≤ 2 := by omega
  have hRV : R ≤ V := sup_le hYV inf_le_left
  have hΩ : ∀ x ∈ R, x ^ p = 1 → x ∈ Y := h3 p hp hp2 Y C hYx hY2 inf_le_right hR2
  have hYn : Y ≤ normalizer (centralizer (Y : Set G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  have hNR : ∀ v ∈ (V : Subgroup G), v ∈ normalizer (R : Set G) → v ∈ R := by
    intro v hvV hvN
    have hconj : ∀ w : G, w ∈ normalizer (R : Set G) → ∀ y ∈ Y, w * y * w⁻¹ ∈ Y := by
      intro w hwN y hy
      apply hΩ
      · exact (mem_normalizer_iff.mp hwN y).mp (le_sup_left (a := Y) hy)
      · rw [conj_pow, hYx.2.2 y hy, mul_one, mul_inv_cancel]
    have hvY : v ∈ normalizer (Y : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      refine ⟨hconj v hvN y, fun hy => ?_⟩
      have := hconj v⁻¹ (inv_mem hvN) _ hy
      simpa [mul_assoc] using this
    have hvT := hT (zpowers v) (zpowers_le.mpr hvY) (V.isPGroup'.to_le (zpowers_le.mpr hvV))
      (mem_zpowers v)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hYn] at hvT
    obtain ⟨y, hy, c, hc, rfl⟩ := hvT
    refine mul_mem_sup hy ⟨?_, hc⟩
    have := (V : Subgroup G).mul_mem ((V : Subgroup G).inv_mem (hYV hy)) hvV
    rw [inv_mul_cancel_left] at this
    exact this
  have hVR : (V : Subgroup G) ≤ R := by
    by_contra hne
    have hlt : R.subgroupOf V < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne fun x hx => ?_
      have : (⟨x, hx⟩ : V) ∈ R.subgroupOf V := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    haveI : Group.IsNilpotent V := V.isPGroup'.isNilpotent
    obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
    rw [← subgroupOf_normalizer_eq hRV, Subgroup.mem_subgroupOf] at hxN
    exact hxR (Subgroup.mem_subgroupOf.mpr (hNR x x.2 hxN))
  have := pRank_mono hp1 hVR
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC

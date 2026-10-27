module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6U6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6U6Good
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigDiv
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup iInf_fixSubgroup_zpowers)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

namespace BTwE6

theorem xun6_exists_good_zpowers_of_fix_involution (A : Subgroup (MulAut (xunM 6)))
    (hA : IsElemAbelian 3 A) (h3 : 3 ^ 3 ≤ Nat.card A) {t : xunM 6} (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (hfix : ∀ a ∈ A, a t = t) :
    ∃ a ∈ A, a ≠ 1 ∧ IsGood 3 (Subgroup.zpowers a) := by
  obtain ⟨hcard, c, hc⟩ := exists_diag_conj_of_fix_involution A hA h3 ht1 ht2 hfix
  obtain ⟨g, hg, hg1, hgood⟩ := exists_good_of_diag_conj _ c hc hcard
  exact ⟨_, hg, hg1, hgood⟩

private theorem nonempty_mulEquiv_xunM_six {G : Type} [Group G] (h : catalogIs G S9.isU6two) :
    Nonempty (G ≃* xunM 6) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first
        | exact hi.elim
        | exact ⟨e.trans (nonempty_mulEquiv_xunM 5 q hv hi).some⟩
    | _ => exact hi.elim
  | _ => exact hi.elim

private theorem false_of_nlAct_fix {Ω : Type} [Group Ω] [Finite Ω] {X K B D : Subgroup Ω}
    (hB : IsElemAbelian 3 B) (hact : NLAct 3 X K B D) (hK : catalogIs (PSimple 3 K) S9.isU6two)
    (hD : Nat.card D = 3 ^ 2) (h5 : Nat.card B = 3 ^ 5) {t : PSimple 3 K} (ht : orderOf t = 2)
    (ht1 : t ≠ 1)
    (hfix : ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (K : Set Ω), chevAut 3 K ⟨b, hb⟩ t = t) :
    False := by
  let φ : ↥B →* MulAut (PSimple 3 K) := (chevAut 3 K).comp (Subgroup.inclusion hact.norm)
  let A : Subgroup (MulAut (PSimple 3 K)) := φ.range
  have hker : φ.ker = D.subgroupOf B := by
    ext e
    rw [Subgroup.mem_subgroupOf]
    exact hact.ker e.1 e.2 (hact.norm e.2)
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥D := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hact.le).toEquiv
  have hcardB : Nat.card ↥B = Nat.card ↥D * Nat.card ↥A := by
    rw [← Subgroup.card_ker_mul_card_range φ, hcardker]
  have hAel : IsElemAbelian 3 A := by
    have h := CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hB B) φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have h27 : 3 ^ 3 ≤ Nat.card A := by
    rw [hcardB, hD] at h5
    norm_num at h5 ⊢
    omega
  have hAfix : ∀ a ∈ A, a t = t := by
    rintro _ ⟨e, rfl⟩
    exact hfix e.1 e.2 (hact.norm e.2)
  obtain ⟨e0⟩ := nonempty_mulEquiv_xunM_six hK
  have hA'el : IsElemAbelian 3 (A.map (MulAut.congr e0).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr e0).injective hAel
  have hA'card : 3 ^ 3 ≤ Nat.card (A.map (MulAut.congr e0).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.congr e0).injective]
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have he1 : e0 t ≠ 1 := fun h1 => ht1 (e0.injective (h1.trans (map_one e0).symm))
  have he2 : e0 t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hA'fix : ∀ a ∈ A.map (MulAut.congr e0).toMonoidHom, a (e0 t) = e0 t := by
    rintro _ ⟨a, ha, rfl⟩
    change e0 (a (e0.symm (e0 t))) = e0 t
    rw [MulEquiv.symm_apply_apply, hAfix a ha]
  obtain ⟨a, haA, ha1, hgood⟩ := BBig.exists_good_zpowers_of_mulEquiv e0
    (xun6_exists_good_zpowers_of_fix_involution _ hA'el hA'card he1 he2 hA'fix)
  unfold IsGood at hgood
  rw [iInf_fixSubgroup_zpowers] at hgood
  obtain ⟨e, he⟩ := haA
  have hφe : φ e ≠ 1 := fun h1 => ha1 (he.symm.trans h1)
  have heD : e.1 ∉ D := fun heD => hφe ((hact.ker e.1 e.2 (hact.norm e.2)).2 heD)
  have hval : a = chevAut 3 K ⟨e.1, hact.norm e.2⟩ := by
    rw [← he]
    rfl
  exact hgood (hval ▸ hact.layer e.1 e.2 heD (hact.norm e.2))

end BTwE6

theorem qsBRes_twE6 (hR2 : TwE6U6Even) : QSBResTwE6 := by
  intro Ω _ _ S B T x D K h hS hK h5 hTB
  have hc := h.cfg
  obtain ⟨-, -, hDcard, -⟩ := hc.std
  obtain ⟨t, ht, hfix⟩ := hR2 Ω S B T x D K h hS hK h5 hTB
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    norm_num at ht
  have hpK : 3 ∣ Nat.card K :=
    T123C.dvd_card_of_nontrivial_pSimple hc.prime (X := K) (nontrivial_of_ne t 1 ht1)
  exact (BTwE6.false_of_nlAct_fix hc.elem (h.nlAct hpK) hK hDcard h5 ht ht1 hfix).elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end

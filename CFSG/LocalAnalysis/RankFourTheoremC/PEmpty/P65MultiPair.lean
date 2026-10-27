module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitFin
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp cjComp_one cjComp_mul cjComp_inj π
  π_conj π_ext π_one π_zpow conj_mem_layer)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit (coordHom coordHom_mem π_congr')

theorem exists_conj_le_sylow {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p Y) (E : Subgroup Y) (hE : IsPGroup p E) :
    ∃ y : Y, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S Q
  refine ⟨g, ?_⟩
  have hgS : (g • S : Sylow p Y).toSubgroup = S.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgS
  rw [hgS]
  exact Subgroup.map_mono hES

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_pair_of_layer {p : ℕ} (hp : p.Prime)
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (hcard : Nat.card (ComponentIndex Y) = p)
    (hrank : ∀ (C : ComponentIndex Y) (F : Subgroup Y), F ≤ C.1 → IsElemAbelian p F →
      Nat.card F ≤ p)
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ p) (hEl : E ≤ layer Y) :
    ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧ ∀ g : Y, g * a * g⁻¹ ∉ zpowers b := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hEp⟩ := (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).mp hE
  let Fc : ComponentIndex Y → Subgroup Y := fun C =>
    (E.subgroupOf (layer Y)).map (coordHom hZ C)
  have hFe : ∀ C, IsElemAbelian p (Fc C) := fun C => (hE.subgroupOf (layer Y)).map _
  have hFc : ∀ C, Nat.card (Fc C) ≤ p := fun C => by
    refine hrank C (Fc C) ?_ (hFe C)
    rintro _ ⟨a, -, rfl⟩
    exact coordHom_mem hZ C a
  let ι : ↥E → ∀ C : ComponentIndex Y, ↥(Fc C) := fun e C =>
    ⟨coordHom hZ C ⟨e, hEl e.2⟩, ⟨⟨e, hEl e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro e e' hee'
    apply Subtype.ext
    refine π_ext (hZ := hZ) (hEl e.2) (hEl e'.2) fun C => ?_
    have := congrArg Subtype.val (congrFun hee' C)
    exact this
  have h1 := Nat.card_le_card_of_injective ι hι
  rw [Nat.card_pi, hEc] at h1
  have hp1 : p ^ p = p ^ (p - 1) * p := by
    rw [← pow_succ]
    congr 1
    have := hp.pos
    omega
  have hFeq : ∀ C, Nat.card (Fc C) = p := by
    intro C₀
    by_contra hne
    have hlt : Nat.card (Fc C₀) < p := lt_of_le_of_ne (hFc C₀) hne
    have h2 : ∏ C, Nat.card (Fc C) =
        Nat.card (Fc C₀) * ∏ C ∈ Finset.univ.erase C₀, Nat.card (Fc C) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ C₀)).symm
    have h3 : ∏ C ∈ Finset.univ.erase C₀, Nat.card (Fc C) ≤
        p ^ (Finset.univ.erase C₀).card := Finset.prod_le_pow_card _ _ _ fun C _ => hFc C
    have h4 : (Finset.univ.erase C₀).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ C₀), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hcard]
    rw [h4] at h3
    rw [h2] at h1
    have h5 : Nat.card (Fc C₀) * ∏ C ∈ Finset.univ.erase C₀, Nat.card (Fc C) ≤
        Nat.card (Fc C₀) * p ^ (p - 1) := Nat.mul_le_mul_left _ h3
    have h6 : Nat.card (Fc C₀) * p ^ (p - 1) < p * p ^ (p - 1) :=
      Nat.mul_lt_mul_of_pos_right hlt (pow_pos hp.pos _)
    rw [hp1, mul_comm (p ^ (p - 1)) p] at h1
    omega
  have hbij : Function.Bijective ι := by
    refine hι.bijective_of_nat_card_le ?_
    rw [Nat.card_pi, hEc, Finset.prod_congr rfl (fun C _ => hFeq C), Finset.prod_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨C₁, C₂, hC12⟩ : ∃ C₁ C₂ : ComponentIndex Y, C₁ ≠ C₂ := by
    have : 1 < Nat.card (ComponentIndex Y) := by rw [hcard]; exact hp.one_lt
    haveI := Finite.one_lt_card_iff_nontrivial.mp this
    exact exists_pair_ne _
  have hnt : ∀ C, ∃ c : ↥(Fc C), c ≠ 1 := fun C => by
    have : 1 < Nat.card (Fc C) := by rw [hFeq C]; exact hp.one_lt
    haveI := Finite.one_lt_card_iff_nontrivial.mp this
    exact exists_ne _
  obtain ⟨c₁, hc₁⟩ := hnt C₁
  obtain ⟨c₂, hc₂⟩ := hnt C₂
  let t₁ : ∀ C : ComponentIndex Y, ↥(Fc C) := Pi.mulSingle C₁ c₁
  let t₂ : ∀ C : ComponentIndex Y, ↥(Fc C) := Pi.mulSingle C₁ c₁ * Pi.mulSingle C₂ c₂
  obtain ⟨a, ha⟩ := hbij.2 t₁
  obtain ⟨b, hb⟩ := hbij.2 t₂
  have hal : (a : Y) ∈ layer Y := hEl a.2
  have hbl : (b : Y) ∈ layer Y := hEl b.2
  have hπa : ∀ C, π hZ C (a : Y) hal = ((t₁ C : ↥(Fc C)) : Y) := fun C =>
    congrArg Subtype.val (congrFun ha C)
  have hπb : ∀ C, π hZ C (b : Y) hbl = ((t₂ C : ↥(Fc C)) : Y) := fun C =>
    congrArg Subtype.val (congrFun hb C)
  have ha1 : π hZ C₁ (a : Y) hal = (c₁ : Y) := by
    rw [hπa]
    simp [t₁]
  have hb1 : π hZ C₁ (b : Y) hbl = (c₁ : Y) := by
    rw [hπb]
    simp [t₂, Pi.mulSingle_eq_of_ne hC12]
  have hb2 : π hZ C₂ (b : Y) hbl = (c₂ : Y) := by
    rw [hπb]
    simp [t₂, Pi.mulSingle_eq_of_ne hC12.symm]
  have hc₁' : (c₁ : Y) ≠ 1 := fun h => hc₁ (Subtype.ext h)
  have hord : ∀ (C : ComponentIndex Y) (c : ↥(Fc C)), c ≠ 1 → orderOf (c : Y) = p := by
    intro C c hc
    refine orderOf_eq_prime ((hFe C).2 c c.2) ?_
    exact fun h => hc (Subtype.ext h)
  have hne_one : ∀ (x : Y) (hx : x ∈ layer Y), π hZ C₁ x hx ≠ 1 → x ≠ 1 := by
    intro x hx hπ h
    apply hπ
    rw [π_congr' hZ C₁ hx (one_mem _) h, π_one]
  have ha_ne : (a : Y) ≠ 1 := hne_one _ hal (by rw [ha1]; exact hc₁')
  have hb_ne : (b : Y) ≠ 1 := hne_one _ hbl (by rw [hb1]; exact hc₁')
  refine ⟨a, a.2, ha_ne, b, b.2, hb_ne, fun g hg => ?_⟩
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hg
  have hag : g * (a : Y) * g⁻¹ ∈ layer Y := conj_mem_layer g hal
  have key : ∀ C' : ComponentIndex Y, cjComp g⁻¹ C' ≠ C₁ → (π hZ C' (b : Y) hbl) ^ m = 1 := by
    intro C' hne
    have hC1 : cjComp g (cjComp g⁻¹ C') = C' := by
      rw [← cjComp_mul, mul_inv_cancel, cjComp_one]
    have h := π_conj (hZ := hZ) g (cjComp g⁻¹ C') hal
    rw [hC1] at h
    have hπ1 : π hZ (cjComp g⁻¹ C') (a : Y) hal = 1 := by
      rw [hπa]
      simp [t₁, Pi.mulSingle_eq_of_ne hne]
    rw [hπ1] at h
    have h2 : π hZ C' (g * (a : Y) * g⁻¹) hag = 1 := by rw [h]; group
    have h3 : π hZ C' ((b : Y) ^ m) (zpow_mem hbl m) = π hZ C' (g * (a : Y) * g⁻¹) hag :=
      π_congr' hZ C' (zpow_mem hbl m) hag hm
    rw [π_zpow, h2] at h3
    exact h3
  have hdvd : ∀ (C' : ComponentIndex Y) (c : ↥(Fc C')), c ≠ 1 → π hZ C' (b : Y) hbl = (c : Y) →
      cjComp g⁻¹ C' ≠ C₁ → (p : ℤ) ∣ m := by
    intro C' c hc hπ hne
    have h1 := key C' hne
    rw [hπ] at h1
    have h2 := (orderOf_dvd_iff_zpow_eq_one).mpr h1
    rwa [hord C' c hc] at h2
  have hpm : (p : ℤ) ∣ m := by
    by_cases h1 : cjComp g⁻¹ C₁ = C₁
    · have h2 : cjComp g⁻¹ C₂ ≠ C₁ := fun h => hC12 (cjComp_inj g⁻¹ (h.trans h1.symm)).symm
      exact hdvd C₂ c₂ hc₂ hb2 h2
    · exact hdvd C₁ c₁ hc₁ hb1 h1
  obtain ⟨k, hk⟩ := hpm
  have hbm : (b : Y) ^ m = 1 := by
    rw [hk, zpow_mul, zpow_natCast, hEp (b : Y) b.2, one_zpow]
  rw [hbm] at hm
  have h1 : g * (a : Y) * g⁻¹ = 1 := hm.symm
  exact ha_ne (by simpa using h1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

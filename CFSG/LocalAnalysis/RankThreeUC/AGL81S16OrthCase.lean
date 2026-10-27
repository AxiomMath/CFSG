module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFacts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Weak

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_of_mem_normalizer {A : Subgroup G} {t a : G}
    (ht : t ∈ normalizer (A : Set G)) (ha : a ∈ A) : ⁅t, a⁆ ∈ A := by
  have h1 : t * a * t⁻¹ ∈ A := (mem_normalizer_iff.mp ht a).mp ha
  have h2 : t * a * t⁻¹ * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
  simpa [commutatorElement_def] using h2

theorem qProp_base_orth {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : O6LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : O6LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hAM : cj g V ≤ M) :
    ∀ B : Subgroup G, B ≤ cj g V → B.relIndex (cj g V) < 2 ^ (2 * n) →
      V ⊓ centralizer (B : Set G) ≤ centralizer ((cj g V : Subgroup G) : Set G) := by
  have hmono : 2 ^ (2 * n) ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lemmaQ (k := 2 * n) (M := M) (M' := cj g M) hS.elemAbelian.2 hAM
    (le_of_eq hS.normalizer_eq.symm) (le_of_eq hSg.normalizer_eq.symm)
    (cj_ne_of_not_mem hS.self_normalizing hg) ?_ ?_ ?_
  · intro u hu hu1 hle
    exact absurd hle (not_inf_centralizer_le_of_dvd (hS.spe g hg) (hF.p_dvd u hu hu1))
  · intro U' hU' hcU'
    exact le_trans hmono (le_of_lt (hSg.hr_strict_of_facts hp hn hFg U' hU' hcU'))
  · intro t ht ht2 a ha hat hCu
    by_contra hlt
    have htnc : t ∉ centralizer ((cj g V : Subgroup G) : Set G) := by
      intro htc
      apply hat
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact mem_centralizer_iff.mp htc a ha
    have hta : ⁅t, a⁆ ∈ cj g V :=
      commutator_mem_of_mem_normalizer (le_of_eq hSg.normalizer_eq.symm ht) ha
    have hta1 : ⁅t, a⁆ ≠ 1 := by
      intro h
      apply hat
      rw [← commutatorElement_inv, h, inv_one]
    have hns := hFg.transvection t ht ht2 htnc (not_le.mp hlt) a ha hta1
    have hgood := hFg.nonsing_good ⁅t, a⁆ hta hta1 hns
    have hcu := hSg.centralizer_le_of_good hp hta hta1 hgood
    apply hCu
    have hinv : centralizer ({⁅a, t⁆} : Set G) = centralizer ({⁅t, a⁆} : Set G) := by
      have h : ⁅a, t⁆ = ⁅t, a⁆⁻¹ := (commutatorElement_inv t a).symm
      rw [h]
      ext x
      simp only [mem_centralizer_singleton_iff]
      exact Commute.inv_right_iff
    rw [hinv]
    exact hcu

theorem orth_le_L_sup {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : O6LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : O6LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hAM : cj g V ≤ M) : cj g V ≤ L ⊔ (M ⊓ centralizer (V : Set G)) := by
  by_contra hAL
  obtain ⟨a, haA, haL⟩ := SetLike.not_le_iff_exists.mp hAL
  have haM : a ∈ M := hAM haA
  have ha2 : a ^ 2 = 1 := hSg.elemAbelian.2 a haA
  obtain ⟨v, hvV, hav1, hns⟩ := hF.outer_nonsing a haM ha2 haL
  have hv0V : ⁅a, v⁆ ∈ V := by
    have h1 : a * v * a⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (le_of_eq hS.normalizer_eq.symm haM) v).mp hvV
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hvV)
    simpa [commutatorElement_def] using h2
  have hVM' : ¬ V ≤ cj g M := by
    intro hVM'
    have hv0A : ⁅a, v⁆ ∈ cj g V := by
      have h := commutator_mem_of_mem_normalizer
        (le_of_eq hSg.normalizer_eq.symm (hVM' hvV)) haA
      have h' : ⁅v, a⁆⁻¹ ∈ cj g V := (cj g V).inv_mem (commutator_mem_of_mem_normalizer
        (le_of_eq hSg.normalizer_eq.symm (hVM' hvV)) haA)
      simpa [commutatorElement_inv] using h'
    have hgood := hF.nonsing_good ⁅a, v⁆ hv0V hav1 hns
    have hcu : centralizer ({⁅a, v⁆} : Set G) ≤ M :=
      hS.centralizer_le_of_good hp hv0V hav1 hgood
    exact not_inf_centralizer_le_of_dvd' (hS.spe g hg) (hFg.p_dvd ⁅a, v⁆ hv0A hav1)
      (le_trans inf_le_right hcu)
  have hVB0 : V ≤ centralizer ((cj g V ⊓ (M ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp hb.2.2 w hw).symm
  have hlt := hSg.hr_strict_of_facts hp hn hFg (cj g V ⊓ (M ⊓ centralizer (V : Set G)))
    inf_le_left (fun hle => hVM' (hVB0.trans hle))
  have hle := hF.outer_rank (cj g V) hAM hSg.elemAbelian hAL
  have hpow : 2 ^ (3 * n + 1) ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem normalizes_weakClosureIn_of_commutator {T V P R : Subgroup G} (hRT : R ≤ T)
    (h : ∀ g : G, cj g V ≤ T → ∀ a ∈ cj g V, ∀ x ∈ P, ⁅x, a⁆ ∈ R) :
    P ≤ normalizer (weakClosureIn V T : Set G) := by
  have key : ∀ x ∈ P, ∀ y ∈ weakClosureIn V T, x * y * x⁻¹ ∈ weakClosureIn V T := by
    intro x hx y hy
    refine Subgroup.iSup_induction _ (C := fun y => x * y * x⁻¹ ∈ weakClosureIn V T) hy
      (fun g z hz => ?_) ?_ (fun a b ha hb => ?_)
    · obtain ⟨z₀, hz₀, rfl⟩ := hz
      have hxg : V.map (MulAut.conj (x * (g : G))).toMonoidHom ≤ T := by
        rintro _ ⟨v, hv, rfl⟩
        have hwT : (g : G) * v * (g : G)⁻¹ ∈ T := g.2 ⟨v, hv, rfl⟩
        have hwA : (g : G) * v * (g : G)⁻¹ ∈ cj (g : G) V := ⟨v, hv, rfl⟩
        have hc : ⁅x, (g : G) * v * (g : G)⁻¹⁆ ∈ R := h (g : G) g.2 _ hwA x hx
        have e1 : (x * (g : G)) * v * (x * (g : G))⁻¹ =
            ⁅x, (g : G) * v * (g : G)⁻¹⁆ * ((g : G) * v * (g : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
        show (x * (g : G)) * v * (x * (g : G))⁻¹ ∈ T
        rw [e1]
        exact T.mul_mem (hRT hc) hwT
      exact map_conj_le_weakClosureIn hxg ⟨z₀, hz₀, by simp [mul_assoc]⟩
    · simp
    · simpa [mul_assoc] using mul_mem ha hb
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key x hx y hy, fun hy => by
    simpa [mul_assoc] using key x⁻¹ (P.inv_mem hx) _ hy⟩

theorem orth_normalizes {p n : ℕ} {M L V T : Subgroup G} {sing : G → Prop} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : O6LocalFacts p n M L V sing)
    (hSg : ∀ g : G, LocalSetting p (cj g M) (cj g V))
    (hFg : ∀ g : G, O6LocalFacts p n (cj g M) (cj g L) (cj g V)
      (fun x => sing (g⁻¹ * x * g)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    ∃ P : Subgroup G, P ≤ L ∧ 2 ≤ CFSG.Open.pRank p P ∧
      P ≤ normalizer (weakClosureIn V T : Set G) := by
  obtain ⟨P, R, hPL, hRT, hP2, hcomm⟩ := hF.parabolic T hT
  refine ⟨P, hPL, hP2, normalizes_weakClosureIn_of_commutator hRT ?_⟩
  intro g hgT a ha x hx
  have hTM : T ≤ M := hT.le
  have hAab : IsElemAbelian 2 (cj g V) := (hSg g).elemAbelian
  by_cases hAC : cj g V ≤ centralizer (V : Set G)
  · have hAL : cj g V ≤ L ⊔ (M ⊓ centralizer (V : Set G)) :=
      le_sup_of_le_right (le_inf (hgT.trans hTM) hAC)
    have hQ : ∀ B : Subgroup G, B ≤ cj g V → B.relIndex (cj g V) < 2 ^ (2 * n) →
        V ⊓ centralizer (B : Set G) ≤ centralizer ((cj g V : Subgroup G) : Set G) := by
      intro B _ _ v hv
      rw [mem_centralizer_iff]
      intro a' ha'
      exact (mem_centralizer_iff.mp (hAC ha') v hv.1).symm
    exact hcomm (cj g V) hgT hAab hQ hAL a ha x hx
  · have hg : g ∉ M := by
      intro hgM
      apply hAC
      have h1 : cj g V = V :=
        mem_normalizer_iff_map_conj_eq.mp (le_of_eq hS.normalizer_eq.symm hgM)
      rw [h1]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hS.elemAbelian.1
    have hAM : cj g V ≤ M := hgT.trans hTM
    exact hcomm (cj g V) hgT hAab
      (qProp_base_orth hp hn hS hF (hSg g) (hFg g) hg hAM)
      (orth_le_L_sup hp hn hS hF (hSg g) (hFg g) hg hAM) a ha x hx

end CFSG.LocalAnalysis.RankThreeUC

module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiYDelta
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hg]
    exact ⟨x, hx, rfl⟩
  · rw [← hg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have h2 : y = x := by simpa using h1
    rwa [← h2]

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (mem_normalizer_iff''.mp hg x).mp hx, ?_⟩
    simp [mul_assoc]

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K}

theorem SzR2.secondLevel (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    (∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x) ∧
    normalizer (szR T₁ R₂ t : Set G) ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) ∧
    normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (R₂ : Set G) ∧
    (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).ncard = Fintype.card K ∧
    ∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range,
        σ Q₁ = Z₁ ∧ σ Q₂ = Z₂ := by
  obtain ⟨φ, γ, c, h⟩ := hS.exists_coords hc ha hK hμ
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  exact ⟨h.commute_of_gamma_eq_zero hγ, h.normalizer_le_normalizer_sup ha hK hγ,
    h.normalizer_le_normalizer_R₂ hS ha hK hγ, h.ncard_gmsRootConjugates hG hS hc ha hK hμ hCt,
    h.two_transitive_gmsRootConjugates hG hS hc ha hK hμ hCt⟩

namespace SzStart

variable {L : Subgroup G} {f : ℕ} {T : Subgroup G}

theorem card_sylow_centralizer_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {d : G} {u v : G → K} {κ : K}
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hK : Fintype.card K = 2 ^ f) :
    ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card (szT₁ L T) := by
  intro P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := h.sylow
  obtain ⟨-, -, hcardT, -⟩ := h.facts_of_card_sylow hS2
  rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity P₀, hP₀,
    Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv, hcardT, hc.card_eq,
    Nat.card_eq_fintype_card, hK]
  ring

theorem not_exists_normal_index_two (h : SzStart G L f t T) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : IsSimpleGroup G := h.setting.1
  exact Endings.not_exists_normal_index_two h.setting.2.1

theorem not_isSylow_szR_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d) :
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = szT₁ L T ⊔ R₂ ⊔ zpowers t) ∧
    ¬ IsSylowOf 2 (szT₁ L T ⊔ R₂ ⊔ zpowers t)
      (normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) := by
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  exact ⟨hR.not_isSylow h.not_exists_normal_index_two hc ha hKa hμ hCt,
    hR.not_isSylowOf_normalizer h.not_exists_normal_index_two hc ha hKa hμ hCt⟩

theorem card_range_inf_stabilizer_of_card_sylow
    (h : SzStart G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤ normalizer (szR (szT₁ L T) R₂ t : Set G)) :
    Odd (Nat.card ((gmsRootConjugateAction (szR (szT₁ L T) R₂ t) (szA L T t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t))))) ∧
    Nat.card ((gmsRootConjugateAction (szR (szT₁ L T) R₂ t) (szA L T t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szR (szT₁ L T) R₂ t) (szA L T t)))) ∣
      (2 ^ f - 1) * f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hG := h.not_exists_normal_index_two
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  obtain ⟨φ, γ, c, hφ⟩ := hR.exists_coords hc ha hKa hμ
  obtain ⟨hTeq, -, hcardT, -, -, -, -, hCA, hnA₁, -⟩ := h.facts_of_card_sylow hS2
  set R := szR (szT₁ L T) R₂ t with hRdef
  set A := szA L T t with hAdef
  set Y := normalizer (R : Set G) with hYdef
  set Δ := gmsRootConjugates R A
  set ψ := gmsRootConjugateAction R A with hψ
  set α₀ : Δ := ⟨A, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩
  set M := normalizer (A : Set G) ⊓ centralizer ({t} : Set G) with hMdef
  have htriv : ∀ r ∈ R, ∀ hr : r ∈ Y, ψ ⟨r, hr⟩ = 1 := by
    intro r hrR hr
    refine Equiv.ext fun S => Subtype.ext ?_
    exact hφ.map_conj_eq_of_mem_szR hG hR hc ha hKa hμ hCt S.2 hrR
  have hMY : M ≤ Y := inf_le_left.trans hNR
  have hTR : T ≤ R := by
    rw [hTeq]
    exact sup_le (le_szR_left _ R₂ t) (zpowers_le.mpr (mem_szR_right _ R₂ t))
  have hTM : T ≤ M := le_inf (fun x hx => centralizer_le_normalizer _ (hCA ▸ hx)) h.le
  have hH : ψ.range ⊓ MulAction.stabilizer (Equiv.Perm Δ) α₀ = (M.subgroupOf Y).map ψ := by
    have h1 : ψ.range ⊓ MulAction.stabilizer (Equiv.Perm Δ) α₀ =
        (MulAction.stabilizer Y α₀).map ψ := range_inf_stabilizer_eq_map α₀
    rw [h1]
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      have hnA : (n : G) ∈ normalizer (A : Set G) :=
        mem_normalizer_of_map_conj_eq (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hn))
      have htA : (n : G) * t * (n : G)⁻¹ ∈ A :=
        (mem_normalizer_iff.mp hnA t).mp (mem_szA_right L T t)
      have htA₁ : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
        centralizer_le (szA₁_le _) h.mem_centralizer_szT₁
      obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ htA
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
      · exfalso
        apply hnA₁ (n : G)⁻¹
        rw [inv_inv, ← hbz, hz1, mul_one]
        exact hb
      rw [hz1] at hbz
      obtain ⟨r, hr, hrt⟩ := hR.rho_surj b hb
      have hrR : r ∈ R := le_szR_mid _ R₂ t hr
      have hrY : r ∈ Y := le_normalizer hrR
      have hrA : r ∈ normalizer (A : Set G) :=
        mem_normalizer_of_map_conj_eq (hφ.map_conj_eq_of_mem_szR hG hR hc ha hKa hμ hCt
          (szA_mem_gmsRootConjugates (szT₁ L T) R₂ t) hrR)
      have hmM : r⁻¹ * (n : G) ∈ M := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem hrA) hnA, mem_centralizer_singleton_iff.mpr ?_⟩
        have e1 : r * t * r⁻¹ = (n : G) * t * (n : G)⁻¹ := by
          rw [← hbz]
          calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
            _ = b * t := by rw [hrt]
        calc r⁻¹ * (n : G) * t = r⁻¹ * ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
          _ = r⁻¹ * (r * t * r⁻¹) * (n : G) := by rw [e1]
          _ = t * (r⁻¹ * (n : G)) := by group
      refine ⟨⟨r⁻¹ * n, hMY hmM⟩, mem_subgroupOf.mpr hmM, ?_⟩
      have e : (⟨r⁻¹ * n, hMY hmM⟩ : Y) = (⟨r, hrY⟩ : Y)⁻¹ * n := rfl
      rw [e, map_mul, map_inv, htriv r hrR hrY, inv_one, one_mul]
    · rintro _ ⟨m, hm, rfl⟩
      refine ⟨m, MulAction.mem_stabilizer_iff.mpr (Subtype.ext ?_), rfl⟩
      exact map_conj_eq_of_mem_normalizer (mem_inf.mp (mem_subgroupOf.mp hm)).1
  set ψ' := ψ.comp (M.subgroupOf Y).subtype with hψ'
  have hrange : ψ'.range = (M.subgroupOf Y).map ψ := by
    rw [hψ', MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardM : Nat.card ψ'.ker * Nat.card ψ'.range = Nat.card M := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index,
      Nat.card_congr (subgroupOfEquivOfLe hMY).toEquiv]
  have hTker : (T.subgroupOf Y).subgroupOf (M.subgroupOf Y) ≤ ψ'.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    exact htriv _ (hTR (mem_subgroupOf.mp (mem_subgroupOf.mp hm))) _
  have hTY : T ≤ Y := hTM.trans hMY
  have hTT : T.subgroupOf Y ≤ M.subgroupOf Y := fun y hy =>
    mem_subgroupOf.mpr (hTM (mem_subgroupOf.mp hy))
  have hcardT' : Nat.card ((T.subgroupOf Y).subgroupOf (M.subgroupOf Y)) = Nat.card T := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTT).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hTY).toEquiv]
  have hTdvd : Nat.card T ∣ Nat.card ψ'.ker := hcardT' ▸ Subgroup.card_dvd_of_le hTker
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have key : ∀ m : ℕ, Nat.card M ∣ Nat.card T * m → Nat.card ψ'.range ∣ m := by
    intro m hm
    refine Nat.dvd_of_mul_dvd_mul_left hTpos ?_
    calc Nat.card T * Nat.card ψ'.range ∣ Nat.card ψ'.ker * Nat.card ψ'.range :=
          Nat.mul_dvd_mul_right hTdvd _
      _ = Nat.card M := hcardM
      _ ∣ Nat.card T * m := hm
  rw [hH, ← hrange]
  refine ⟨?_, key _ ?_⟩
  · obtain ⟨P, hP⟩ := h.sylow
    have hidx := P.not_dvd_index
    have hC := Subgroup.card_mul_index (P : Subgroup (centralizer ({t} : Set G)))
    rw [hP, Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv] at hC
    rw [hP] at hidx
    have h2 := key _ (hC ▸ Subgroup.card_dvd_of_le (inf_le_right : M ≤ centralizer ({t} : Set G)))
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2n => hidx (h2n.trans h2)
  · have hdvd := h.card_normalizer_szA_inf_centralizer_dvd_of_card_sylow hS2
    rw [hcardT]
    calc Nat.card M ∣ 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := hdvd
      _ = 2 * 2 ^ f * 2 ^ f * ((2 ^ f - 1) * f) := by ring

theorem secondLevel_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) :
    (∀ x ∈ szT₁ L T, ∀ r ∈ R₂, x * r = r * x) ∧
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ∧
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (R₂ : Set G) ∧
    (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).ncard = 2 ^ f ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t),
      Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
        ∃ σ ∈ (gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range,
          σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) ∧
    Odd (Nat.card ((gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range ⊓
        MulAction.stabilizer
          (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t))))) ∧
    Nat.card ((gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range ⊓
        MulAction.stabilizer
          (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))) ∣
      (2 ^ f - 1) * f := by
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR.secondLevel h.not_exists_normal_index_two hc ha hKa hμ hCt
  obtain ⟨h6, h7⟩ := h.card_range_inf_stabilizer_of_card_sylow hS2 ha hfa hK hc hμ hR hNR
  exact ⟨h1, h2, h3, h4.trans hK, h5, h6, h7⟩

theorem secondLevel
    (h : SzStart G L f t T) (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) :
    (∀ x ∈ szT₁ L T, ∀ r ∈ R₂, x * r = r * x) ∧
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ∧
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (R₂ : Set G) ∧
    (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).ncard = 2 ^ f ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t),
      Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
        ∃ σ ∈ (gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range,
          σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) ∧
    Odd (Nat.card ((gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range ⊓
        MulAction.stabilizer
          (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t))))) ∧
    Nat.card ((gmsRootConjugateAction (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)).range ⊓
        MulAction.stabilizer
          (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))
          (⟨szA L T t, szA_mem_gmsRootConjugates (szT₁ L T) R₂ t⟩ :
            gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szT₁ L T ⊔ R₂ ⊔ zpowers t) (szA L T t)))) ∣
      (2 ^ f - 1) * f :=
  h.secondLevel_of_card_sylow h.card_sylow ha hfa hK hc hμ hR hNR

end SzStart

end CFSG.SeitzReduction.RankOne

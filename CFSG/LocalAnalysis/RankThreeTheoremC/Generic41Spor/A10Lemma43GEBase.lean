module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GImage
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GRho
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GPsiE
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_eb_mem_pre {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    (Λ : Subgroup Q) {g : G} :
    g ∈ a10Pre J ψ Λ ↔ ∃ hg : g ∈ J, ψ ⟨g, hg⟩ ∈ Λ := by
  unfold a10Pre
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, hj⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem a10t1_eb_pre_le {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    (Λ : Subgroup Q) : a10Pre J ψ Λ ≤ J :=
  fun _ hg => ((a10t1_eb_mem_pre ψ Λ).mp hg).1

theorem a10t1_eb_E_le_pre {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    (Λ : Subgroup Q) : a10E J ψ Λ ≤ a10Pre J ψ Λ :=
  (Subgroup.closure_le _).mpr (fun _ hg => hg.1)

theorem a10t1_eb_conj_fiveRes_le {G : Type} [Group G] {H K : Subgroup G} (c : G)
    (h : ∀ g ∈ H, c * g * c⁻¹ ∈ K) {e : G} (he : e ∈ fiveRes H) :
    c * e * c⁻¹ ∈ fiveRes K := by
  have hle : fiveRes H ≤ (fiveRes K).comap (MulAut.conj c).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, k, hk⟩
    refine Subgroup.subset_closure ⟨h g hg, k, ?_⟩
    show (c * g * c⁻¹) ^ 5 ^ k = 1
    rw [conj_pow, hk]
    simp
  exact hle he

theorem a10t1_eb_fiveRes_gen {G : Type} [Group G] (H : Subgroup G) :
    Subgroup.closure {g : G | g ∈ fiveRes H ∧ ∃ k : ℕ, g ^ 5 ^ k = 1} = fiveRes H := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (fun g hg => hg.1)
  · exact (Subgroup.closure_le _).mpr (fun g hg => Subgroup.subset_closure ⟨Subgroup.subset_closure hg, hg.2⟩)

theorem a10t1_eb_conj_E_le {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    (w : G) (hw : w ∈ Subgroup.normalizer (J : Set G)) (σ : Q →* Q)
    (hσ : ∀ (j : ↥J) (hj : w * (j : G) * w⁻¹ ∈ J), σ (ψ j) = ψ ⟨w * j * w⁻¹, hj⟩)
    (Λ Λ' : Subgroup Q) (hΛ : Λ.map σ ≤ Λ') {e : G} (he : e ∈ a10E J ψ Λ) :
    w * e * w⁻¹ ∈ a10E J ψ Λ' := by
  refine a10t1_eb_conj_fiveRes_le w (fun g hg => ?_) he
  obtain ⟨hgJ, hgΛ⟩ := (a10t1_eb_mem_pre ψ Λ).mp hg
  have hj : w * g * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hw g).mp hgJ
  refine (a10t1_eb_mem_pre ψ Λ').mpr ⟨hj, ?_⟩
  rw [← hσ ⟨g, hgJ⟩ hj]
  exact hΛ ⟨_, hgΛ, rfl⟩

theorem a10t1_eb_comm_E_le {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    (Λ₁ Λ₂ : Subgroup Q) (hcomm : ∀ a ∈ Λ₁, ∀ b ∈ Λ₂, a * b = b * a)
    {e : G} (he : e ∈ a10Pre J ψ Λ₂) {a : G} (ha : a ∈ a10E J ψ Λ₁) :
    e * a * e⁻¹ ∈ a10E J ψ Λ₁ := by
  obtain ⟨heJ, heΛ⟩ := (a10t1_eb_mem_pre ψ Λ₂).mp he
  refine a10t1_eb_conj_fiveRes_le e (fun g hg => ?_) ha
  obtain ⟨hgJ, hgΛ⟩ := (a10t1_eb_mem_pre ψ Λ₁).mp hg
  have hj : e * g * e⁻¹ ∈ J := J.mul_mem (J.mul_mem heJ hgJ) (J.inv_mem heJ)
  refine (a10t1_eb_mem_pre ψ Λ₁).mpr ⟨hj, ?_⟩
  have h1 : (⟨e * g * e⁻¹, hj⟩ : ↥J) = ⟨e, heJ⟩ * ⟨g, hgJ⟩ * ⟨e, heJ⟩⁻¹ := rfl
  have h2 : ψ ⟨e * g * e⁻¹, hj⟩ = ψ ⟨g, hgJ⟩ := by
    rw [h1, map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
    exact (hcomm _ hgΛ _ heΛ).symm
  rw [h2]
  exact hgΛ

theorem a10t1_eb_A5 {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q) {Λ : Subgroup Q}
    (iso : ↥Λ ≃* alternatingGroup (Fin 5)) (O : Subgroup G) (hker : ψ.ker = O.subgroupOf J)
    (hpsi : ((a10E J ψ Λ).subgroupOf J).map ψ = Λ) :
    ∃ f : ↥(a10E J ψ Λ) →* alternatingGroup (Fin 5),
      Function.Surjective f ∧ f.ker = O.subgroupOf (a10E J ψ Λ) := by
  have hEL : a10E J ψ Λ ≤ a10Pre J ψ Λ := a10t1_eb_E_le_pre ψ Λ
  have hEJ : a10E J ψ Λ ≤ J := hEL.trans (a10t1_eb_pre_le ψ Λ)
  let φ : ↥(a10E J ψ Λ) →* Q := ψ.comp (Subgroup.inclusion hEJ)
  have hφ : ∀ x : ↥(a10E J ψ Λ), φ x ∈ Λ := by
    intro x
    obtain ⟨hg, hmem⟩ := (a10t1_eb_mem_pre ψ Λ).mp (hEL x.2)
    exact hmem
  let φ' : ↥(a10E J ψ Λ) →* ↥Λ := φ.codRestrict Λ hφ
  refine ⟨iso.toMonoidHom.comp φ', ?_, ?_⟩
  · intro a
    have hq : ((iso.symm a : ↥Λ) : Q) ∈ ((a10E J ψ Λ).subgroupOf J).map ψ := by
      rw [hpsi]
      exact (iso.symm a).2
    obtain ⟨y, hy, hyq⟩ := hq
    refine ⟨⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    have h1 : φ' ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩ = iso.symm a := Subtype.ext hyq
    show iso (φ' ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩) = a
    rw [h1]
    exact iso.apply_symm_apply a
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show iso (φ' x) = 1 ↔ _
    rw [map_eq_one_iff _ iso.injective]
    have h2 : φ' x = 1 ↔ ψ ⟨x, hEJ x.2⟩ = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have h3 : ψ ⟨x, hEJ x.2⟩ = 1 ↔ (x : G) ∈ O := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [h2, h3]

theorem a10_E_base (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : A10Facts) (hXe : A10Ext)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ)
    {Λ₁ Λ₂ : Subgroup Q} (hΛ : A10GammaStructAt Q (S : Subgroup Q) Λ₁ Λ₂) :
    A10EBase (M ⊓ Subgroup.centralizer ({x} : Set G)) (rankThreePrimeCore 5 J)
      (a10E J ψ Λ₁) (a10E J ψ Λ₂) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hOM : rankThreePrimeCore 5 J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  have hMJ := a10_MJ_image hS hD1 hU0 hX hXe hc ψ hψ hker hQ S hSyl
  have hLM : ∀ {Λ : Subgroup Q}, Λ ≤ A10Gamma Q (S : Subgroup Q) → a10Pre J ψ Λ ≤ M := by
    intro Λ hΛΓ l hl
    obtain ⟨hlJ, hlΛ⟩ := (a10t1_eb_mem_pre ψ Λ).mp hl
    have h1 : ψ ⟨l, hlJ⟩ ∈ ((M ⊓ J).subgroupOf J).map ψ := by
      rw [hMJ]
      exact hΛΓ hlΛ
    obtain ⟨m, hm, hmψ⟩ := h1
    have h2 : (⟨l, hlJ⟩ : ↥J) * m⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmψ, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have h3 : l * (m : G)⁻¹ ∈ M := hOM h2
    have h4 : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).1
    have h5 := M.mul_mem h3 h4
    simpa using h5
  have hEW : ∀ {Λ : Subgroup Q}, Λ ≤ A10Gamma Q (S : Subgroup Q) →
      a10E J ψ Λ ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro Λ hΛΓ
    refine le_inf ((a10t1_eb_E_le_pre ψ Λ).trans (hLM hΛΓ)) ?_
    exact ((a10t1_eb_E_le_pre ψ Λ).trans (a10t1_eb_pre_le ψ Λ)).trans hc.le_cent
  obtain ⟨ρ, hρ, -⟩ := a10_rho hc ψ hψ hker (W := M ⊓ Subgroup.centralizer ({x} : Set G)) inf_le_right
  refine ⟨hEW hΛ.le_gamma₁, hEW hΛ.le_gamma₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact le_inf hOM (hOJ.trans hc.le_cent)
  ·
    intro w hw o ho
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_core_conj (hc.cent_le hw.2) ho
  ·
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J)
  ·
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (J : Set G) := hc.cent_le hw.2
    have hΓle : (A10Gamma Q (S : Subgroup Q)).map (ρ ⟨w, hw⟩).toMonoidHom ≤ A10Gamma Q (S : Subgroup Q) := by
      rintro _ ⟨q0, hq0, rfl⟩
      rw [← hMJ] at hq0
      obtain ⟨m, hm, rfl⟩ := hq0
      have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).1
      have hj : w * (m : G) * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hwN m).mp m.2
      have h1 : (ρ ⟨w, hw⟩).toMonoidHom (ψ m) = ψ ⟨w * m * w⁻¹, hj⟩ := hρ ⟨w, hw⟩ m hj
      rw [h1, ← hMJ]
      exact ⟨⟨w * m * w⁻¹, hj⟩, Subgroup.mem_subgroupOf.mpr
        ⟨M.mul_mem (M.mul_mem hw.1 hmM) (M.inv_mem hw.1), hj⟩, rfl⟩
    have hρΓ : (A10Gamma Q (S : Subgroup Q)).map (ρ ⟨w, hw⟩).toMonoidHom = A10Gamma Q (S : Subgroup Q) :=
      Subgroup.eq_of_le_of_card_ge hΓle (Subgroup.card_map_of_injective (ρ ⟨w, hw⟩).injective).ge
    have hσ : ∀ (j : ↥J) (hj : w * (j : G) * w⁻¹ ∈ J),
        (ρ ⟨w, hw⟩).toMonoidHom (ψ j) = ψ ⟨w * j * w⁻¹, hj⟩ := fun j hj => hρ ⟨w, hw⟩ j hj
    have key : ∀ {Λ : Subgroup Q}, (Λ.map (ρ ⟨w, hw⟩).toMonoidHom ≤ Λ₁ ∨ Λ.map (ρ ⟨w, hw⟩).toMonoidHom ≤ Λ₂) →
        a10E J ψ Λ ≤ (a10E J ψ Λ₁ ⊔ a10E J ψ Λ₂).comap (MulAut.conj w).toMonoidHom := by
      intro Λ h e he
      rcases h with h | h
      · exact Subgroup.mem_sup_left (a10t1_eb_conj_E_le ψ w hwN _ hσ Λ Λ₁ h he)
      · exact Subgroup.mem_sup_right (a10t1_eb_conj_E_le ψ w hwN _ hσ Λ Λ₂ h he)
    have hperm := a10g_aut_perm hΛ (ρ ⟨w, hw⟩) hρΓ
    have h1 := key (Λ := Λ₁) (by
      rcases hperm with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h.le
      · exact Or.inr h.le)
    have h2 := key (Λ := Λ₂) (by
      rcases hperm with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr h.le
      · exact Or.inl h.le)
    intro e he
    exact (sup_le h1 h2) he
  ·
    intro e he a ha
    exact a10t1_eb_comm_E_le ψ Λ₁ Λ₂ hΛ.comm (a10t1_eb_E_le_pre ψ Λ₂ he) ha
  ·
    intro e he a ha
    exact a10t1_eb_comm_E_le ψ Λ₂ Λ₁ (fun a ha b hb => (hΛ.comm b hb a ha).symm) (a10t1_eb_E_le_pre ψ Λ₁ he) ha
  · exact a10t1_eb_fiveRes_gen _
  · exact a10t1_eb_fiveRes_gen _
  · obtain ⟨iso⟩ := hΛ.iso₁
    exact a10t1_eb_A5 ψ iso _ hker (a10_psi_E ψ hψ (a10g_five_gen hΛ).1)
  · obtain ⟨iso⟩ := hΛ.iso₂
    exact a10t1_eb_A5 ψ iso _ hker (a10_psi_E ψ hψ (a10g_five_gen hΛ).2)
  ·
    intro a ha b hb
    obtain ⟨haJ, haΛ⟩ := (a10t1_eb_mem_pre ψ Λ₁).mp (a10t1_eb_E_le_pre ψ Λ₁ ha)
    obtain ⟨hbJ, hbΛ⟩ := (a10t1_eb_mem_pre ψ Λ₂).mp (a10t1_eb_E_le_pre ψ Λ₂ hb)
    have hj : a * b * a⁻¹ * b⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem haJ hbJ) (J.inv_mem haJ)) (J.inv_mem hbJ)
    have hmem : (⟨a * b * a⁻¹ * b⁻¹, hj⟩ : ↥J) ∈ ψ.ker := by
      have h1 : (⟨a * b * a⁻¹ * b⁻¹, hj⟩ : ↥J) = ⟨a, haJ⟩ * ⟨b, hbJ⟩ * ⟨a, haJ⟩⁻¹ * ⟨b, hbJ⟩⁻¹ := rfl
      rw [MonoidHom.mem_ker, h1, map_mul, map_mul, map_mul, map_inv, map_inv, hΛ.comm _ haΛ _ hbΛ]
      group
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact hmem

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwMapA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwAct
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

namespace Map

variable {G : Type} [Group G] {M K : Subgroup G} {t : G}
  (φ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42))

open Classical in
noncomputable def phiG (g : G) : Equiv.Perm (Fin 42) :=
  if h : g ∈ normalizer (K : Set G) then φ ⟨g, h⟩ else 1

theorem phiG_of_mem {g : G} (hg : g ∈ normalizer (K : Set G)) : phiG φ g = φ ⟨g, hg⟩ := by
  unfold phiG
  exact dif_pos hg

theorem phiG_of_not_mem {g : G} (hg : g ∉ normalizer (K : Set G)) : phiG φ g = 1 := by
  unfold phiG
  exact dif_neg hg

theorem phiG_mul {g g' : G} (hg : g ∈ normalizer (K : Set G)) (hg' : g' ∈ normalizer (K : Set G)) :
    phiG φ (g * g') = phiG φ g * phiG φ g' := by
  rw [phiG_of_mem φ (mul_mem hg hg'), phiG_of_mem φ hg, phiG_of_mem φ hg']
  exact map_mul φ ⟨g, hg⟩ ⟨g', hg'⟩

theorem phiG_mem_R (hφR : ∀ n, φ n ∈ R) (g : G) : phiG φ g ∈ R := by
  by_cases hg : g ∈ normalizer (K : Set G)
  · rw [phiG_of_mem φ hg]
    exact hφR _
  · rw [phiG_of_not_mem φ hg]
    exact R.one_mem

theorem phiG_eq_one (hφ1 : ∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K)
    {g : G} (hg : g ∈ coreActionKernel K) : phiG φ g = 1 := by
  rw [phiG_of_mem φ hg.1]
  exact (hφ1 ⟨g, hg.1⟩).mpr hg

theorem mem_coreActionKernel_of_phiG_eq_one
    (hφ1 : ∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K)
    {g : G} (hn : g ∈ normalizer (K : Set G)) (h : phiG φ g = 1) : g ∈ coreActionKernel K := by
  rw [phiG_of_mem φ hn] at h
  exact (hφ1 ⟨g, hn⟩).mp h

theorem phiG_of_mem_K {q : L34Facts.Jhat K →* Equiv.Perm (Fin 42)}
    (hφK : ∀ k : ↥K, φ ⟨k, le_normalizer k.2⟩ = q (L34Facts.jq K k)) {k : G} (hk : k ∈ K) :
    phiG φ k = q (L34Facts.jq K ⟨k, hk⟩) := by
  rw [phiG_of_mem φ (le_normalizer hk)]
  exact hφK ⟨k, hk⟩

open Classical in
noncomputable def rhoFun (t : G) (g : G) : WrE :=
  if g ∈ normalizer (K : Set G) then ⟨phiG φ g, phiG φ (t⁻¹ * g * t), false⟩
  else ⟨phiG φ (t⁻¹ * g), phiG φ (g * t), true⟩

theorem rhoFun_of_mem {g : G} (hg : g ∈ normalizer (K : Set G)) :
    rhoFun φ t g = ⟨phiG φ g, phiG φ (t⁻¹ * g * t), false⟩ := by
  unfold rhoFun
  exact if_pos hg

theorem rhoFun_of_not_mem {g : G} (hg : g ∉ normalizer (K : Set G)) :
    rhoFun φ t g = ⟨phiG φ (t⁻¹ * g), phiG φ (g * t), true⟩ := by
  unfold rhoFun
  exact if_neg hg

theorem mul_of_e_false (x y : WrE) (hy : y.e = false) :
    x * y = ⟨x.a * y.a, x.b * y.b, x.e⟩ := by
  rw [WrE.mul_def, hy]
  simp

theorem mul_of_e_true (x y : WrE) (hy : y.e = true) :
    x * y = ⟨x.b * y.a, x.a * y.b, !x.e⟩ := by
  rw [WrE.mul_def, hy]
  simp

theorem mem_wrR_iff {x : WrE} : x ∈ wrR ↔ x.a ∈ R ∧ x.b ∈ R := Iff.rfl

theorem rhoFun_mul (d : TwoCompData M K t) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) :
    rhoFun φ t (m * m') = rhoFun φ t m * rhoFun φ t m' := by
  by_cases h1 : m ∈ normalizer (K : Set G) <;> by_cases h2 : m' ∈ normalizer (K : Set G)
  ·
    have h3 : m * m' ∈ normalizer (K : Set G) := mul_mem h1 h2
    have e1 := conj_mem d hm h1
    have e2 := conj_mem d hm' h2
    rw [rhoFun_of_mem φ h3, rhoFun_of_mem φ h1, rhoFun_of_mem φ h2, mul_of_e_false _ _ rfl]
    show (⟨phiG φ (m * m'), phiG φ (t⁻¹ * (m * m') * t), false⟩ : WrE) =
      ⟨phiG φ m * phiG φ m', phiG φ (t⁻¹ * m * t) * phiG φ (t⁻¹ * m' * t), false⟩
    rw [show t⁻¹ * (m * m') * t = (t⁻¹ * m * t) * (t⁻¹ * m' * t) by group,
      phiG_mul φ h1 h2, phiG_mul φ e1 e2]
  ·
    have h3 : m * m' ∉ normalizer (K : Set G) := fun h =>
      h2 (((mul_mem_normalizer_iff d hm hm').mp h).mp h1)
    have e1 := conj_mem d hm h1
    have e2 := inv_mul_mem d hm' h2
    have e3 := mul_mem_of_not_mem d hm' h2
    rw [rhoFun_of_not_mem φ h3, rhoFun_of_mem φ h1, rhoFun_of_not_mem φ h2,
      mul_of_e_true _ _ rfl]
    show (⟨phiG φ (t⁻¹ * (m * m')), phiG φ (m * m' * t), true⟩ : WrE) =
      ⟨phiG φ (t⁻¹ * m * t) * phiG φ (t⁻¹ * m'), phiG φ m * phiG φ (m' * t), !false⟩
    rw [show t⁻¹ * (m * m') = (t⁻¹ * m * t) * (t⁻¹ * m') by group, phiG_mul φ e1 e2,
      show m * m' * t = m * (m' * t) by group, phiG_mul φ h1 e3]
    rfl
  ·
    have h3 : m * m' ∉ normalizer (K : Set G) := fun h =>
      h1 (((mul_mem_normalizer_iff d hm hm').mp h).mpr h2)
    have e1 := inv_mul_mem d hm h1
    have e2 := mul_mem_of_not_mem d hm h1
    have e3 := conj_mem d hm' h2
    rw [rhoFun_of_not_mem φ h3, rhoFun_of_not_mem φ h1, rhoFun_of_mem φ h2,
      mul_of_e_false _ _ rfl]
    show (⟨phiG φ (t⁻¹ * (m * m')), phiG φ (m * m' * t), true⟩ : WrE) =
      ⟨phiG φ (t⁻¹ * m) * phiG φ m', phiG φ (m * t) * phiG φ (t⁻¹ * m' * t), true⟩
    rw [show t⁻¹ * (m * m') = (t⁻¹ * m) * m' by group, phiG_mul φ e1 h2,
      show m * m' * t = (m * t) * (t⁻¹ * m' * t) by group, phiG_mul φ e2 e3]
  ·
    have h3 : m * m' ∈ normalizer (K : Set G) :=
      (mul_mem_normalizer_iff d hm hm').mpr ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    have e1 := mul_mem_of_not_mem d hm h1
    have e2 := inv_mul_mem d hm' h2
    have e3 := inv_mul_mem d hm h1
    have e4 := mul_mem_of_not_mem d hm' h2
    rw [rhoFun_of_mem φ h3, rhoFun_of_not_mem φ h1, rhoFun_of_not_mem φ h2,
      mul_of_e_true _ _ rfl]
    show (⟨phiG φ (m * m'), phiG φ (t⁻¹ * (m * m') * t), false⟩ : WrE) =
      ⟨phiG φ (m * t) * phiG φ (t⁻¹ * m'), phiG φ (t⁻¹ * m) * phiG φ (m' * t), !true⟩
    rw [show m * m' = (m * t) * (t⁻¹ * m') by group, phiG_mul φ e1 e2,
      show t⁻¹ * (m * t * (t⁻¹ * m')) * t = (t⁻¹ * m) * (m' * t) by group, phiG_mul φ e3 e4]
    rfl

@[expose] noncomputable def rhoHom (d : TwoCompData M K t) : ↥M →* WrE :=
  MonoidHom.mk' (fun m => rhoFun φ t (m : G)) (fun m m' => rhoFun_mul φ d m.2 m'.2)

theorem rhoHom_apply (d : TwoCompData M K t) (m : ↥M) : rhoHom φ d m = rhoFun φ t (m : G) := rfl

section Ker

variable [Finite G]

theorem ker_le_pPrimeCore (d : TwoCompData M K t) {T : Subgroup G}
    (hT : ∃ P : Sylow 2 ↥M, (P : Subgroup ↥M) = T.subgroupOf M)
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1)
    (hφ1 : ∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K) :
    (rhoHom φ d).ker ≤ pPrimeCore 2 ↥M := by
  obtain ⟨P, hP⟩ := hT
  refine le_pPrimeCore_of_inf_sylow_eq_bot P ?_
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyk, hyP⟩ := mem_inf.mp hy
  rw [hP] at hyP
  have hyT : (y : G) ∈ T := hyP
  have hρ : rhoFun φ t (y : G) = 1 := hyk
  have hyn : (y : G) ∈ normalizer (K : Set G) := by
    by_contra h
    rw [rhoFun_of_not_mem φ h] at hρ
    have := congrArg WrE.e hρ
    simp [WrE.one_def] at this
  rw [rhoFun_of_mem φ hyn] at hρ
  have ha : phiG φ (y : G) = 1 := congrArg WrE.a hρ
  have hb : phiG φ (t⁻¹ * (y : G) * t) = 1 := congrArg WrE.b hρ
  have hyc : (y : G) ∈ coreActionKernel K := mem_coreActionKernel_of_phiG_eq_one φ hφ1 hyn ha
  have hyc' : t⁻¹ * (y : G) * t ∈ coreActionKernel K :=
    mem_coreActionKernel_of_phiG_eq_one φ hφ1 (conj_mem d y.2 hyn) hb
  have h1 : (y : G) = 1 := eq_one_of_conj_mem d hQ hyT hyc hyc'
  exact mem_bot.mpr (Subtype.ext h1)

theorem rhoHom_eq_one_of_mem_oddIn (d : TwoCompData M K t)
    (hφ1 : ∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K) {m : ↥M}
    (hm : (m : G) ∈ oddIn M) : rhoHom φ d m = 1 := by
  have hc : (m : G) ∈ coreActionKernel K := oddIn_le_coreActionKernel d hm
  have hc' : t⁻¹ * (m : G) * t ∈ coreActionKernel K := by
    have h1 : t⁻¹ * (m : G) * t⁻¹⁻¹ ∈ oddIn M := conj_mem_oddIn (inv_mem d.htM) hm
    rw [inv_inv] at h1
    exact oddIn_le_coreActionKernel d h1
  show rhoFun φ t (m : G) = 1
  rw [rhoFun_of_mem φ hc.1, phiG_eq_one φ hφ1 hc, phiG_eq_one φ hφ1 hc']
  rfl

end Ker

theorem twModel_rhoHom [Finite G] (d : TwoCompData M K t) {T : Subgroup G}
    (hT : ∃ P : Sylow 2 ↥M, (P : Subgroup ↥M) = T.subgroupOf M)
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1)
    {q : L34Facts.Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hφR : ∀ n, φ n ∈ R)
    (hφS : ∀ n : ↥(normalizer (K : Set G)), φ n ∈ S ↔ (n : G) ∈ withKernel K)
    (hφ1 : ∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K)
    (hφK : ∀ k : ↥K, φ ⟨k, le_normalizer k.2⟩ = q (L34Facts.jq K k)) :
    TwModel M K t (rhoHom φ d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro m
    rw [rhoHom_apply, mem_wrR_iff]
    by_cases h : (m : G) ∈ normalizer (K : Set G)
    · rw [rhoFun_of_mem φ h]
      exact ⟨phiG_mem_R φ hφR _, phiG_mem_R φ hφR _⟩
    · rw [rhoFun_of_not_mem φ h]
      exact ⟨phiG_mem_R φ hφR _, phiG_mem_R φ hφR _⟩
  ·
    intro m
    constructor
    · intro h1
      have h2 : m ∈ pPrimeCore 2 ↥M := ker_le_pPrimeCore φ d hT hQ hφ1 h1
      show (m : G) ∈ (pPrimeCore 2 ↥M).map M.subtype
      exact ⟨m, h2, rfl⟩
    · intro h1
      exact rhoHom_eq_one_of_mem_oddIn φ d hφ1 h1
  ·
    intro m
    show (rhoFun φ t (m : G)).e = true ↔ _
    by_cases h : (m : G) ∈ normalizer (K : Set G)
    · rw [rhoFun_of_mem φ h]
      simp [h]
    · rw [rhoFun_of_not_mem φ h]
      simp [h]
  ·
    intro m hm
    show _ ↔ (rhoFun φ t (m : G)).a ∈ S
    rw [rhoFun_of_mem φ hm]
    show _ ↔ phiG φ (m : G) ∈ S
    rw [phiG_of_mem φ hm]
    exact (hφS ⟨(m : G), hm⟩).symm
  ·
    intro m hmK
    have hmn : (m : G) ∈ normalizer (K : Set G) := le_normalizer hmK
    have hc : t⁻¹ * (m : G) * t ∈ coreActionKernel K :=
      conjugate_le_coreActionKernel d (conj_mem_conjugate hmK t)
    show (rhoFun φ t (m : G)).e = false ∧ (rhoFun φ t (m : G)).b = 1 ∧
      (rhoFun φ t (m : G)).a ∈ S
    rw [rhoFun_of_mem φ hmn]
    refine ⟨rfl, phiG_eq_one φ hφ1 hc, ?_⟩
    show phiG φ (m : G) ∈ S
    rw [phiG_of_mem_K φ hφK hmK]
    exact hqS _
  ·
    intro m hm
    have hc : (m : G) ∈ coreActionKernel K := conjugate_le_coreActionKernel d hm
    have hK1 : t⁻¹ * (m : G) * t ∈ K := conj_mem_K d hm
    show (rhoFun φ t (m : G)).e = false ∧ (rhoFun φ t (m : G)).a = 1 ∧
      (rhoFun φ t (m : G)).b ∈ S
    rw [rhoFun_of_mem φ hc.1]
    refine ⟨rfl, phiG_eq_one φ hφ1 hc, ?_⟩
    show phiG φ (t⁻¹ * (m : G) * t) ∈ S
    rw [phiG_of_mem_K φ hφK hK1]
    exact hqS _
  ·
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs
    obtain ⟨k, hk⟩ := L34Facts.jq_surjective K e
    have hkM : (k : G) ∈ M := d.hKM k.2
    refine ⟨⟨k, hkM⟩, k.2, ?_⟩
    show rhoFun φ t (k : G) = ⟨s, 1, false⟩
    have hc : t⁻¹ * (k : G) * t ∈ coreActionKernel K :=
      conjugate_le_coreActionKernel d (conj_mem_conjugate k.2 t)
    have h1 : q (L34Facts.jq K ⟨(k : G), k.2⟩) = s := by
      have : (⟨(k : G), k.2⟩ : ↥K) = k := rfl
      rw [this, hk, he]
    rw [rhoFun_of_mem φ (le_normalizer k.2), phiG_eq_one φ hφ1 hc, phiG_of_mem_K φ hφK k.2, h1]
  ·
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs
    obtain ⟨k, hk⟩ := L34Facts.jq_surjective K e
    have hkM : (k : G) ∈ M := d.hKM k.2
    have hmt : t * (k : G) * t⁻¹ ∈ conjugate K t := mul_mem_conjugate d k.2
    have hmM : t * (k : G) * t⁻¹ ∈ M := mul_mem (mul_mem d.htM hkM) (inv_mem d.htM)
    refine ⟨⟨_, hmM⟩, hmt, ?_⟩
    show rhoFun φ t (t * (k : G) * t⁻¹) = ⟨1, s, false⟩
    have hc : t * (k : G) * t⁻¹ ∈ coreActionKernel K := conjugate_le_coreActionKernel d hmt
    have h1 : q (L34Facts.jq K ⟨(k : G), k.2⟩) = s := by
      have : (⟨(k : G), k.2⟩ : ↥K) = k := rfl
      rw [this, hk, he]
    rw [rhoFun_of_mem φ hc.1, show t⁻¹ * (t * (k : G) * t⁻¹) * t = (k : G) by group,
      phiG_eq_one φ hφ1 hc, phiG_of_mem_K φ hφK k.2, h1]

end Map

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}

theorem exists_twModel (h : TwHyp G a x J S' W K T t) :
    ∃ ρ : ↥(normalizer (W : Set G)) →* WrE, TwModel (normalizer (W : Set G)) K t ρ := by
  have d : Map.TwoCompData (normalizer (W : Set G)) K t :=
    ⟨h.hKM, h.hKc, h.hTsyl.1 h.htT, h.htK, h.hr2⟩
  obtain ⟨q, φ, hqS, hqsurj, -, hφR, hφS, hφ1, hφK, -⟩ :=
    exists_phi (Map.perfect d) h.hKL
  exact ⟨Map.rhoHom φ d, Map.twModel_rhoHom φ d h.hTsyl.2 h.hQ hqS hqsurj hφR hφS hφ1 hφK⟩

end CFSG.ComponentClassification.GrSLit.L34Tw

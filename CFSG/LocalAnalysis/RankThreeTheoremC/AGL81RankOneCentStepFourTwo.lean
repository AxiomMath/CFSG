module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mulAut_conj_apply_eq {K : Type} [Group K] (σ : MulAut K) (k : K) :
    MulAut.conj (σ k) = σ * MulAut.conj k * σ⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_normalizer_map_conj {K : Type} [Group K] {T : Subgroup K} {σ : MulAut K}
    (hσ : ∀ t, t ∈ T ↔ σ t ∈ T) :
    σ ∈ Subgroup.normalizer ((T.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨σ t, (hσ t).mp ht, by simp [mulAut_conj_apply_eq]⟩
  · rintro ⟨t', ht', he⟩
    refine ⟨σ⁻¹ t', (hσ _).mpr (by rwa [MulAut.apply_inv_self]), ?_⟩
    change MulAut.conj (σ⁻¹ t') = h
    rw [mulAut_conj_apply_eq, he]
    group

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem mem_iff_act_mem_normalizer (hI4 : KFactStepThreeMaximal) {P : Sylow p G}
    {M : Subgroup G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hSt : StepThreeGroup p ↥K) (hA : IsEmpty (↥K ≃* alternatingGroup (Fin 10)))
    (hKX : ¬ K ≤ d1X0 p M C)
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B) (c : C) :
    (c : G) ∈ M ↔ φ c ∈ Subgroup.normalizer
      ((((B ⊓ hyp111Pre p C K).subgroupOf C).map φ : Subgroup (MulAut ↥K)) :
        Set (MulAut ↥K)) := by
  set O := primeComplementCore (G := C) p with hO
  set Kp := hyp111Pre p C K with hKp
  set B₁ := B ⊓ Kp with hB₁
  set S' : Subgroup (MulAut ↥K) := (B₁.subgroupOf C).map φ with hS'
  set Kc : Subgroup C := K.comap (QuotientGroup.mk' O) with hKc
  set ψ : ↥K →* MulAut ↥K := MulAut.conj with hψ
  refine ⟨fun hcM => ?_, fun hc => le_of_act_mem_normalizer hcore hp2 hZ hK1 hXM hXr hBC hBM hbB
    hb hbo hE hEc hEB hc⟩
  have hψi : Function.Injective ψ := RankOneSylow.conj_injective fun k hk => by
    have : k ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun k' => (hk k').symm
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  have hKpC : Kp ≤ C := Subgroup.map_subtype_le _
  have hKpc : Kp.subgroupOf C = Kc := Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  set f : ↥Kc →* ↥K := (QuotientGroup.mk' O).subgroupComap K with hf
  have hfs : Function.Surjective f :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective O)
  have hφf : ∀ x : ↥Kc, φ (x : C) = ψ (f x) := fun x => by
    rw [RankOneSylow.act_eq_conj x.2]
    rfl
  have hB₁syl : CFSG.ABGLocalTools.IsSylowOf p B₁ Kp :=
    hBC.inf_of_le_normalizer hKpC (le_normalizer_hyp111Pre hK)
  have hB₁c : CFSG.ABGLocalTools.IsSylowOf p (B₁.subgroupOf C) Kc := by
    rw [← hKpc, ← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right.trans hKpC),
      inf_eq_left.mpr hKpC]
    exact hB₁syl
  obtain ⟨Q, hQ⟩ := hB₁c
  set T : Sylow p ↥K := Q.mapSurjective hfs with hT
  have hmemT : ∀ k : ↥K, k ∈ (T : Subgroup ↥K) ↔ ψ k ∈ S' := by
    intro k
    rw [hT, Sylow.coe_mapSurjective]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(x : C), ?_, hφf x⟩
      rw [← hQ]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨u, hu, hue⟩
      rw [← hQ] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      exact ⟨x, hx, hψi ((hφf x).symm.trans hue)⟩
  have hS'eq : S' = (T : Subgroup ↥K).map ψ := by
    ext h
    constructor
    · intro hh
      obtain ⟨u, hu, rfl⟩ := hh
      have huK : u ∈ Kc := by
        rw [← hKpc]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hu).2
      refine ⟨f ⟨u, huK⟩, (hmemT _).mpr ?_, (hφf ⟨u, huK⟩).symm⟩
      rw [← hφf]
      exact ⟨u, hu, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact (hmemT k).mp hk
  set Y : Subgroup ↥K := ((Kc ⊓ M.comap C.subtype).map φ).comap ψ with hY
  have hmemY : ∀ k : ↥K, k ∈ Y ↔ ∃ d : C, d ∈ Kc ∧ (d : G) ∈ M ∧ φ d = ψ k := by
    intro k
    constructor
    · rintro ⟨d, ⟨hd1, hd2⟩, he⟩
      exact ⟨d, hd1, hd2, he⟩
    · rintro ⟨d, hd1, hd2, he⟩
      exact ⟨d, ⟨hd1, hd2⟩, he⟩
  have hNY : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ Y := by
    intro k hk
    obtain ⟨x, rfl⟩ := hfs k
    refine (hmemY _).mpr ⟨x, x.2, ?_, hφf x⟩
    refine le_of_act_mem_normalizer hcore hp2 hZ hK1 hXM hXr hBC hBM hbB hb hbo hE hEc hEB ?_
    rw [hφf, ← hS', hS'eq]
    refine mem_normalizer_map_conj fun t => ?_
    simp only [hψ, MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp hk t
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hKX
    intro k hk
    obtain ⟨d, hdK, hdM, hde⟩ := (hmemY ⟨k, hk⟩).mp (htop ▸ Subgroup.mem_top _)
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective O k
    have hc₀ : c₀ ∈ Kc := hk
    have he : φ c₀ = ψ ⟨QuotientGroup.mk' O c₀, hk⟩ := hφf ⟨c₀, hc₀⟩
    have hker : c₀ * d⁻¹ ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, hde, mul_inv_cancel]
    have hX := hXM ((mem_d1PlusCore_iff_mem_ker _).mpr hker)
    have hc₀M : (c₀ : G) ∈ M := by
      have := M.mul_mem hX hdM
      simpa using this
    exact ⟨c₀, Subgroup.mem_subgroupOf.mpr ⟨c₀.2, hc₀M⟩, rfl⟩
  have hco := hI4 p ↥K hSt hA T
  have hYN : Y = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) := by
    by_contra hne
    exact hYne (hco.2 Y (lt_of_le_of_ne hNY (Ne.symm hne)))
  have hKcn : Kc.Normal := hK.comap _
  have hmapT : ∀ c : C, (c : G) ∈ M → ∀ t ∈ (T : Subgroup ↥K), φ c t ∈ (T : Subgroup ↥K) := by
    intro c hcM
    have hYY : ∀ k ∈ Y, φ c k ∈ Y := by
      intro k hk
      obtain ⟨d, hdK, hdM, hde⟩ := (hmemY k).mp hk
      refine (hmemY _).mpr ⟨c * d * c⁻¹, hKcn.conj_mem d hdK c, ?_, ?_⟩
      · have := M.mul_mem (M.mul_mem hcM hdM) (M.inv_mem hcM)
        simpa using this
      · rw [hψ, mulAut_conj_apply_eq, map_mul, map_mul, map_inv, hde]
    set σ := φ c with hσ
    set P' : Sylow p ↥K := σ • T with hP'
    have hP'N : (P' : Subgroup ↥K) ≤ Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) := by
      intro x hx
      rw [hP', Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hYN]
      exact hYY y (hYN ▸ Subgroup.le_normalizer hy)
    have hTN : (T : Subgroup ↥K) ≤ Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
      Subgroup.le_normalizer
    have hnorm : (T.subtype hTN).toSubgroup.Normal := by
      rw [Sylow.coe_subtype]
      exact Subgroup.normal_in_normalizer
    haveI := Sylow.unique_of_normal (T.subtype hTN) hnorm
    have heq : T.subtype hTN = P'.subtype hP'N := Subsingleton.elim _ _
    have hTP : T = P' := Sylow.subtype_injective heq
    intro t ht
    have htP : σ t ∈ (P' : Subgroup ↥K) := by
      rw [hP', Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨t, ht, rfl⟩
    rwa [← hTP] at htP
  rw [hS'eq]
  refine mem_normalizer_map_conj fun t => ⟨hmapT c hcM t, fun ht => ?_⟩
  have := hmapT c⁻¹ (by simpa using M.inv_mem hcM) _ ht
  rwa [map_inv, MulAut.inv_apply_self] at this

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GImage

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_fs_fiveRes_map {G : Type} [Group G] (e : G ≃* G) (H : Subgroup G) :
    (fiveRes H).map e.toMonoidHom = fiveRes (H.map e.toMonoidHom) := by
  unfold fiveRes
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, ⟨hH, k, hk⟩, rfl⟩
    refine ⟨⟨h, hH, rfl⟩, k, ?_⟩
    rw [← map_pow e.toMonoidHom, hk, map_one]
  · rintro ⟨⟨h, hH, rfl⟩, k, hk⟩
    refine ⟨h, ⟨hH, k, ?_⟩, rfl⟩
    apply e.injective
    have := hk
    rw [← map_pow e.toMonoidHom] at this
    simpa using this

theorem a10t1_fs_pre_map {G Q : Type} [Group G] [Group Q] {J : Subgroup G} (ψ : ↥J →* Q)
    {Λ₁ Λ₂ : Subgroup Q} {f : G} (hf : f ∈ J) {n : Q} (hfn : ψ ⟨f, hf⟩ = n)
    (hn : Λ₁.map (MulAut.conj n).toMonoidHom = Λ₂) :
    (a10Pre J ψ Λ₁).map (MulAut.conj f).toMonoidHom = a10Pre J ψ Λ₂ := by
  subst hfn
  ext g
  simp only [a10Pre, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨⟨f, hf⟩ * j * ⟨f, hf⟩⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, ← hn]
      exact ⟨ψ j, hj, rfl⟩
    · simp
  · rintro ⟨j, hj, rfl⟩
    refine ⟨f⁻¹ * j * f, ⟨⟨f, hf⟩⁻¹ * j * ⟨f, hf⟩, ?_, ?_⟩, ?_⟩
    · rw [← hn] at hj
      obtain ⟨l, hl, hlj⟩ := hj
      have : ψ (⟨f, hf⟩⁻¹ * j * ⟨f, hf⟩) = l := by
        rw [map_mul, map_mul, map_inv, ← hlj]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact hl
    · simp
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem a10t1_fs_img_map {G : Type} [Group G] (M : Subgroup G) {f : G} (hf : f ∈ M) (H : Subgroup G) :
    (a10Img M H).map (MulAut.conj (a10π M ⟨f, hf⟩)).toMonoidHom =
      a10Img M (H.map (MulAut.conj f).toMonoidHom) := by
  ext y
  simp only [a10Img, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨⟨f, hf⟩ * m * ⟨f, hf⟩⁻¹, ⟨m, hm, ?_⟩, ?_⟩
    · simp
    · simp
  · rintro ⟨m, ⟨h, hh, hhm⟩, rfl⟩
    have hmh : (m : G) = f * h * f⁻¹ := by
      rw [← hhm]
      simp [MulAut.conj_apply]
    have hhM : h ∈ M := by
      have : h = f⁻¹ * (m : G) * f := by
        rw [hmh]; group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem hf) m.2) hf
    refine ⟨a10π M ⟨h, hhM⟩, ⟨⟨h, hhM⟩, hh, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hmh]

theorem a10t1_fs_zpowers_conj {G : Type} [Group G] {T L₁ L₂ : Subgroup G} {a₁ a₂ f : G}
    (hfN : f ∈ Subgroup.normalizer (T : Set G)) (hL : L₁.map (MulAut.conj f).toMonoidHom = L₂)
    (h₁ : Subgroup.zpowers a₁ = T ⊓ L₁) (h₂ : Subgroup.zpowers a₂ = T ⊓ L₂) :
    Subgroup.zpowers (f * a₁ * f⁻¹) = Subgroup.zpowers a₂ := by
  have hT : T.map (MulAut.conj f).toMonoidHom = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp hfN
  have h := congrArg (Subgroup.map (MulAut.conj f).toMonoidHom) h₁
  rw [MonoidHom.map_zpowers, Subgroup.map_inf _ _ _ (MulAut.conj f).injective, hT, hL, ← h₂] at h
  simpa using h

theorem a10_F_swap (hS : Setting G) (hU0 : FullCoreLocal G) (hX : A10Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ)
    {Λ₁ Λ₂ : Subgroup Q} (hΛ : A10GammaStructAt Q (S : Subgroup Q) Λ₁ Λ₂) {a₁ a₂ : G}
    (ha₁M : a₁ ∈ M) (ha₂M : a₂ ∈ M)
    (hz₁ : Subgroup.zpowers a₁ = u3T P x J ⊓ a10Pre J ψ Λ₁)
    (hz₂ : Subgroup.zpowers a₂ = u3T P x J ⊓ a10Pre J ψ Λ₂) :
    ∃ f ∈ a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)),
      (a10Img M (a10E J ψ Λ₁)).map (MulAut.conj f).toMonoidHom = a10Img M (a10E J ψ Λ₂) ∧
      (Subgroup.zpowers (a10π M ⟨a₁, ha₁M⟩)).map (MulAut.conj f).toMonoidHom =
        Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hnN, hn⟩ := hΛ.swap
  have hnT : n ∈ Subgroup.normalizer ((((u3T P x J).subgroupOf J).map ψ : Subgroup Q) : Set Q) := by
    rw [← hSyl]; exact hnN
  obtain ⟨f, hfJ, hfN, hfψ⟩ := a10_frattini hc ψ hψ hker (B := u3T P x J) le_rfl hnT
  have hT1 : u3T P x J ≠ ⊥ := by
    intro h
    obtain ⟨hcard, -, -⟩ := plane_T_structure hX.sylow hc
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hfM : f ∈ M := a10_NJ_le_M hS hU0 hX hc (B := u3T P x J) le_rfl hT1 ⟨hfJ, hfN⟩
  have hpre : (a10Pre J ψ Λ₁).map (MulAut.conj f).toMonoidHom = a10Pre J ψ Λ₂ :=
    a10t1_fs_pre_map ψ hfJ hfψ hn
  refine ⟨a10π M ⟨f, hfM⟩, ⟨⟨f, hfM⟩, ⟨hfJ, hfN⟩, rfl⟩, ?_, ?_⟩
  · rw [a10t1_fs_img_map M hfM]
    congr 1
    unfold a10E
    rw [a10t1_fs_fiveRes_map, hpre]
  · rw [MonoidHom.map_zpowers]
    have hz := a10t1_fs_zpowers_conj hfN hpre hz₁ hz₂
    have hzM : Subgroup.zpowers ((⟨f, hfM⟩ : M) * ⟨a₁, ha₁M⟩ * (⟨f, hfM⟩ : M)⁻¹) =
        Subgroup.zpowers (⟨a₂, ha₂M⟩ : M) := by
      apply Subgroup.map_injective M.subtype_injective
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      simpa using hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul, ← MonoidHom.map_zpowers, hzM, MonoidHom.map_zpowers]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

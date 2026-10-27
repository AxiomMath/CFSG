module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Normalizers

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {A : Subgroup G} {g b : G} :
    b ∈ CFSG.conjugate A g ↔ g * b * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨g * b * g⁻¹, h, by simp [mul_assoc]⟩

theorem le_normalizer_conjJoin (S L : Subgroup G) :
    S ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun s hs y hy => ?_
  have key : (conjJoin S L).map (MulAut.conj s).toMonoidHom ≤ conjJoin S L := by
    unfold conjJoin
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_map]
    refine le_trans ?_ (le_iSup _ (⟨s, hs⟩ * g))
    refine le_of_eq ?_
    congr 1
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have := key (Subgroup.mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

end Normalizers

namespace Notation25

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem K_le_K0 : N.K ≤ N.K0 := by
  refine le_trans ?_ (le_iSup _ (⟨1, N.S.one_mem⟩ : N.S))
  intro y hy
  exact ⟨y, hy, by simp⟩

theorem S_le_normalizer_K0 : N.S ≤ Subgroup.normalizer (N.K0 : Set G) :=
  le_normalizer_conjJoin N.S N.K

theorem H_le_normalizer_of {A : Subgroup G} (hK : N.K0 ≤ Subgroup.centralizer (A : Set G))
    (hS : N.S ≤ Subgroup.normalizer (A : Set G)) : N.H ≤ Subgroup.normalizer (A : Set G) := by
  rw [N.join]
  exact sup_le ((N.K_le_K0.trans hK).trans (Subgroup.centralizer_le_normalizer _)) hS

theorem SC_le_S : N.SC ≤ N.S := inf_le_left

theorem SC_le_centralizer : N.SC ≤ Subgroup.centralizer (N.K0 : Set G) := inf_le_right

theorem S_le_normalizer_SC : N.S ≤ Subgroup.normalizer (N.SC : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun s hs c hc => ?_
  refine ⟨N.S.mul_mem (N.S.mul_mem hs hc.1) (N.S.inv_mem hs),
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hk' : s⁻¹ * k * s ∈ N.K0 := by
    have := Subgroup.le_normalizer_iff.mp N.S_le_normalizer_K0 s⁻¹ (N.S.inv_mem hs) k hk
    simpa using this
  have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hk'
  calc k * (s * c * s⁻¹) = s * ((s⁻¹ * k * s) * c) * s⁻¹ := by group
    _ = s * (c * (s⁻¹ * k * s)) * s⁻¹ := by rw [hc']
    _ = s * c * s⁻¹ * k := by group

theorem conjugate_SC_le : CFSG.conjugate N.SC N.x ≤ N.S := by
  intro b hb
  have hx : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  have hb' := mem_conjugate_iff.mp hb
  exact (Subgroup.mem_normalizer_iff.mp hx b).mpr (N.SC_le_S hb')

theorem S_le_normalizer_conjugate_SC :
    N.S ≤ Subgroup.normalizer (CFSG.conjugate N.SC N.x : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun s hs b hb => ?_
  have hx : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  have hs' : N.x * s * N.x⁻¹ ∈ N.S := (Subgroup.mem_normalizer_iff.mp hx s).mp hs
  have hmem := Subgroup.le_normalizer_iff.mp N.S_le_normalizer_SC _ hs' _ (mem_conjugate_iff.mp hb)
  refine mem_conjugate_iff.mpr ?_
  have : N.x * (s * b * s⁻¹) * N.x⁻¹ =
      N.x * s * N.x⁻¹ * (N.x * b * N.x⁻¹) * (N.x * s * N.x⁻¹)⁻¹ := by group
  rw [this]
  exact hmem

end Notation25

theorem lemma255 : Lemma255 := by
  intro G _ _ T M hs N
  have hSCx_le := N.conjugate_SC_le
  have hS_SC := N.S_le_normalizer_SC
  have hS_SCx := N.S_le_normalizer_conjugate_SC
  have hS₀ : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥ := by
    by_contra hne
    set S₀ := N.SC ⊓ CFSG.conjugate N.SC N.x with hS₀def
    have hS₀S : S₀ ≤ N.S := inf_le_left.trans N.SC_le_S
    have hS₀2 : IsPGroup 2 S₀ := N.tuple.sylow.isPGroup.to_le hS₀S
    have hK0 : N.K0 ≤ Subgroup.centralizer (S₀ : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer ha.1) k hk).symm
    have hSN : N.S ≤ Subgroup.normalizer (S₀ : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _ hS_SC hS_SCx
    have hHN : N.H ≤ Subgroup.normalizer (S₀ : Set G) := N.H_le_normalizer_of hK0 hSN
    have hx2 : N.x ^ 2 ∈ N.S := N.x_sq
    have hx2' : (N.x ^ 2)⁻¹ ∈ N.S := N.S.inv_mem hx2
    have hP : ∀ c ∈ S₀, N.x * c * N.x⁻¹ ∈ S₀ := by
      rintro c ⟨hc1, hc2⟩
      have hc2' := mem_conjugate_iff.mp hc2
      refine ⟨hc2', mem_conjugate_iff.mpr ?_⟩
      have h := Subgroup.le_normalizer_iff.mp hS_SC _ hx2 c hc1
      have : N.x * (N.x * c * N.x⁻¹) * N.x⁻¹ = N.x ^ 2 * c * (N.x ^ 2)⁻¹ := by
        simp only [pow_two]; group
      rw [this]
      exact h
    have hP' : ∀ c ∈ S₀, N.x⁻¹ * c * N.x ∈ S₀ := by
      rintro c ⟨hc1, hc2⟩
      have hc2' := mem_conjugate_iff.mp hc2
      refine ⟨?_, mem_conjugate_iff.mpr ?_⟩
      · have h := Subgroup.le_normalizer_iff.mp hS_SC _ hx2' _ hc2'
        have : (N.x ^ 2)⁻¹ * (N.x * c * N.x⁻¹) * ((N.x ^ 2)⁻¹)⁻¹ = N.x⁻¹ * c * N.x := by
          simp only [pow_two]; group
        rw [this] at h
        exact h
      · have : N.x * (N.x⁻¹ * c * N.x) * N.x⁻¹ = c := by group
        rw [this]
        exact hc1
    have hxN : N.x ∈ Subgroup.normalizer (S₀ : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨hP c, fun hc => ?_⟩
      have := hP' _ hc
      have e : N.x⁻¹ * (N.x * c * N.x⁻¹) * N.x = c := by group
      rwa [e] at this
    have hcore : pCoreOf 2 (Subgroup.normalizer (S₀ : Set G)) ≠ ⊥ := by
      intro hbot
      have hle : S₀ ≤ pCoreOf 2 (Subgroup.normalizer (S₀ : Set G)) :=
        CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 S₀ _
          Subgroup.le_normalizer
          ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
          hS₀2
      rw [hbot] at hle
      exact hne (le_bot_iff.mp hle)
    have hΓ : IsGamma M (Subgroup.normalizer (S₀ : Set G)) := by
      obtain ⟨-, U, HU, hpair, hUH⟩ := N.gammaU.isGamma
      exact ⟨hcore, U, HU, hpair, hUH.trans hHN⟩
    obtain ⟨-, hSsyl, -, -, -⟩ :=
      IsGamma0.overgroup_of_le hs.setting N.tuple.gamma0 N.tuple.sylow_inf hΓ hHN
    have hX2 : IsPGroup 2 ↥(N.S ⊔ Subgroup.zpowers N.x) :=
      hs.setting.isPGroup.to_le (sup_le N.tuple.lt.le (Subgroup.zpowers_le.mpr N.x_mem.1))
    have hXN : N.S ⊔ Subgroup.zpowers N.x ≤ Subgroup.normalizer (S₀ : Set G) :=
      sup_le hSN (Subgroup.zpowers_le.mpr hxN)
    have heq := hSsyl.eq_of_le le_sup_left hXN hX2
    exact N.x_not_mem (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers N.x))
  refine ⟨hS₀, hSCx_le, fun a ha b hb => ?_⟩
  have hbS : b ∈ N.S := hSCx_le hb
  have haS : a ∈ N.S := N.SC_le_S ha
  have hc1 : a * b * a⁻¹ * b⁻¹ ∈ N.SC := by
    have h := Subgroup.le_normalizer_iff.mp hS_SC b hbS a⁻¹ (N.SC.inv_mem ha)
    have := N.SC.mul_mem ha h
    simpa [mul_assoc] using this
  have hc2 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.conjugate N.SC N.x := by
    have h := Subgroup.le_normalizer_iff.mp hS_SCx a haS b hb
    exact (CFSG.conjugate N.SC N.x).mul_mem h ((CFSG.conjugate N.SC N.x).inv_mem hb)
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have : a * b * a⁻¹ * b⁻¹ ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨hc1, hc2⟩
    rw [hS₀] at this
    exact Subgroup.mem_bot.mp this
  have h2 : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  exact h2

end CFSG.QuasithinUnique

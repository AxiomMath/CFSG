module

public import CFSG.Goldschmidt75.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conjSub_le_of_le_sup (P : Sylow p G) (N : Subgroup G) [N.Normal]
    {R : Subgroup G} (hRle : R ≤ N ⊔ P) (hR : IsPGroup p R) :
    ∃ n ∈ N, conjSub n R ≤ P := by
  set M := N ⊔ (P : Subgroup G)
  let PM : Sylow p M := P.subtype le_sup_right
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M PM Q
  obtain ⟨n, hn, q, hq, hnq⟩ := Subgroup.mem_sup_of_normal_left.mp m.2
  refine ⟨n, hn, fun x hx => ?_⟩
  rw [mem_conjSub] at hx
  have hxR : n * x * n⁻¹ ∈ R := hx
  have hxM : n * x * n⁻¹ ∈ M := hRle hxR
  have hxQ : (⟨n * x * n⁻¹, hxM⟩ : M) ∈ (Q : Subgroup M) := hQ (by simpa [mem_subgroupOf] using hxR)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨w, hw, hwe⟩ := hxQ
  have hwP : ((w : M) : G) ∈ (P : Subgroup G) := hw
  have hwe' : (m : G) * (w : G) * (m : G)⁻¹ = n * x * n⁻¹ := by
    have := congrArg Subtype.val hwe
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  rw [← hnq] at hwe'
  have : x = q * (w : G) * q⁻¹ := by
    have h1 : n * (q * (w : G) * q⁻¹) * n⁻¹ = n * x * n⁻¹ := by
      rw [← hwe']; group
    have h2 := congrArg (fun z => n⁻¹ * z * n) h1
    rw [show n⁻¹ * (n * (q * (w : G) * q⁻¹) * n⁻¹) * n = q * (w : G) * q⁻¹ by group,
      show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h2
    exact h2.symm
  rw [this]
  exact P.mul_mem (P.mul_mem hq hwP) (P.inv_mem hq)

variable (N : Subgroup G) [N.Normal]

noncomputable abbrev sylowMap (P : Sylow p G) : Sylow p (G ⧸ N) :=
  P.mapSurjective (QuotientGroup.mk'_surjective N)

theorem coe_sylowMap (P : Sylow p G) :
    ((sylowMap N P : Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) =
      (P : Subgroup G).map (QuotientGroup.mk' N) :=
  Sylow.coe_mapSurjective _ _

theorem stronglyClosed_map (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    fusionStronglyClosed ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      ((sylowMap N P : Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) := by
  intro z hz gb hgb
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
  set y := g⁻¹ * x * g
  have hy : y ∈ N ⊔ (P : Subgroup G) := by
    rw [coe_sylowMap] at hgb
    have : QuotientGroup.mk' N y ∈ (P : Subgroup G).map (QuotientGroup.mk' N) := by
      simpa [y, map_mul, map_inv] using hgb
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    rwa [sup_comm]
  have hyp : IsPGroup p (zpowers y) := by
    have hxp : IsPGroup p (zpowers x) :=
      (P.isPGroup'.to_le ((zpowers_le).mpr (hSP hx)))
    have := hxp.map (MulAut.conj g⁻¹).toMonoidHom
    have e : (MulAut.conj g⁻¹).toMonoidHom x = y := by simp [y]
    rwa [MonoidHom.map_zpowers, e] at this
  obtain ⟨n, hn, hnle⟩ := exists_conjSub_le_of_le_sup P N ((zpowers_le).mpr hy) hyp
  have hyn : n⁻¹ * y * n ∈ (P : Subgroup G) :=
    hnle (mem_conjSub.2 (by simp [mul_assoc]))
  have hxS : (g * n)⁻¹ * x * (g * n) ∈ S := hS x hx _ (by simpa [y, mul_assoc] using hyn)
  refine ⟨(g * n)⁻¹ * x * (g * n), hxS, ?_⟩
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  simp only [map_mul, map_inv, hn1, mul_one]

theorem normalizer_map (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    normalizer ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (normalizer (S : Set G)).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map _)
  intro gb hgb
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
  have hle : conjSub g S ≤ N ⊔ (P : Subgroup G) := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 : QuotientGroup.mk' N y ∈ S.map (QuotientGroup.mk' N) := by
      have h2 := (mem_normalizer_iff.mp ((normalizer _).inv_mem hgb)
        (QuotientGroup.mk' N (g * y * g⁻¹))).mp ⟨_, hy, rfl⟩
      simpa [map_mul, map_inv, mul_assoc] using h2
    have h3 : QuotientGroup.mk' N y ∈ (P : Subgroup G).map (QuotientGroup.mk' N) :=
      Subgroup.map_mono hSP h1
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
    rwa [sup_comm]
  have hp : IsPGroup p (conjSub g S) := (P.isPGroup'.to_le hSP).map _
  obtain ⟨n, hn, hnle⟩ := exists_conjSub_le_of_le_sup P N hle hp
  rw [← conjSub_mul] at hnle
  have heq := conj_eq_of_conj_le hS hnle
  refine ⟨g * n, mem_normalizer_of_conjSub_eq heq, ?_⟩
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [map_mul, hn1, mul_one]

omit [Finite G] in
theorem eq_of_image_eq {X Y : Set G} (hX : X * (N : Set G) = X) (hY : Y * (N : Set G) = Y)
    (h : QuotientGroup.mk' N '' X = QuotientGroup.mk' N '' Y) : X = Y := by
  have key : ∀ {X Y : Set G}, Y * (N : Set G) = Y →
      QuotientGroup.mk' N '' X = QuotientGroup.mk' N '' Y → X ⊆ Y := by
    intro X Y hY h x hx
    have : QuotientGroup.mk' N x ∈ QuotientGroup.mk' N '' Y := h ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := this
    obtain ⟨z, hz, hyz⟩ := (QuotientGroup.mk'_eq_mk' N).mp hyx
    rw [← hY, ← hyz]
    exact Set.mul_mem_mul hy hz
  exact le_antisymm (key hY h) (key hX h.symm)

omit [Finite G] in
theorem mul_normal_eq {A : Subgroup G} (hNA : N ≤ A) (U : Set G) :
    (A : Set G) * U * (N : Set G) = (A : Set G) * U := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, ha, u, hu, rfl⟩, n, hn, rfl⟩
    refine ⟨a * (u * n * u⁻¹), A.mul_mem ha (hNA ?_), u, hu, by group⟩
    exact (inferInstance : N.Normal).conj_mem n hn u
  · intro x hx
    exact ⟨x, hx, 1, N.one_mem, mul_one x⟩

end CFSG.Goldschmidt75

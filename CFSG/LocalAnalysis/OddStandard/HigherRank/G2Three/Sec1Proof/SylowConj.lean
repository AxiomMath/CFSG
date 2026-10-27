module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjBasic

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem exists_conj_of_isSylowIn [Finite Γ] {p : ℕ} [Fact p.Prime] {V P P' : Subgroup Γ}
    (h : IsSylowIn p V P) (h' : IsSylowIn p V P') : ∃ g ∈ V, P' = conjSub g P := by
  obtain ⟨hPV, hPp, hPidx⟩ := h
  obtain ⟨hP'V, hP'p, hP'idx⟩ := h'
  have hidxeq : (P.subgroupOf V).index = P.relIndex V := by
    rw [← Subgroup.relIndex_top_right (H := P.subgroupOf V), ← Subgroup.subgroupOf_self V]
    exact Subgroup.relIndex_subgroupOf (H := P) (K := V) (L := V) le_rfl
  have hidxeq' : (P'.subgroupOf V).index = P'.relIndex V := by
    rw [← Subgroup.relIndex_top_right (H := P'.subgroupOf V), ← Subgroup.subgroupOf_self V]
    exact Subgroup.relIndex_subgroupOf (H := P') (K := V) (L := V) le_rfl
  have hidx : ¬ p ∣ (P.subgroupOf V).index := by rwa [hidxeq]
  have hidx' : ¬ p ∣ (P'.subgroupOf V).index := by rwa [hidxeq']
  let Q : Sylow p ↥V := (hPp.comap_subtype (K := V)).toSylow hidx
  let Q' : Sylow p ↥V := (hP'p.comap_subtype (K := V)).toSylow hidx'
  haveI : Finite ↥V := inferInstance
  haveI : Finite (Sylow p ↥V) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥V Q Q'
  have hQmap : (Q : Subgroup ↥V).map V.subtype = P := by
    change (P.subgroupOf V).map V.subtype = P
    exact Subgroup.map_subgroupOf_eq_of_le hPV
  have hQ'map : (Q' : Subgroup ↥V).map V.subtype = P' := by
    change (P'.subgroupOf V).map V.subtype = P'
    exact Subgroup.map_subgroupOf_eq_of_le hP'V
  have hcomp : V.subtype.comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj (g : Γ)).toMonoidHom.comp V.subtype := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conj_apply', conj_apply']
    rfl
  have hsub : ((g • Q : Sylow p ↥V) : Subgroup ↥V)
      = (Q : Subgroup ↥V).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hmain : (Q' : Subgroup ↥V).map V.subtype
      = P.map (MulAut.conj (g : Γ)).toMonoidHom := by
    calc (Q' : Subgroup ↥V).map V.subtype
        = ((Q : Subgroup ↥V).map (MulAut.conj g).toMonoidHom).map V.subtype := by
            rw [← hg, hsub]
      _ = ((Q : Subgroup ↥V).map V.subtype).map (MulAut.conj (g : Γ)).toMonoidHom := by
            rw [Subgroup.map_map, hcomp, Subgroup.map_map]
      _ = P.map (MulAut.conj (g : Γ)).toMonoidHom := by rw [hQmap]
  refine ⟨(g : Γ), g.2, ?_⟩
  rw [← hQ'map]
  simpa [conjSub] using hmain

theorem actsRegularly_conj {T V Z : Subgroup Γ} {g : Γ} (hV : g ∈ normalizer (V : Set Γ))
    (hZ : g ∈ normalizer (Z : Set Γ)) (h : ActsRegularly T V Z) :
    ActsRegularly (conjSub g T) V Z := by
  obtain ⟨hTV, hTZ, hreg⟩ := h
  have hginvV : g⁻¹ ∈ normalizer (V : Set Γ) := inv_mem hV
  have hginvZ : g⁻¹ ∈ normalizer (Z : Set Γ) := inv_mem hZ
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_conjSub.mp hx
    exact mul_mem (mul_mem hV (hTV ht)) (inv_mem hV)
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_conjSub.mp hx
    exact mul_mem (mul_mem hZ (hTZ ht)) (inv_mem hZ)
  · intro u huV huZ v hvV hvZ
    set u' : Γ := g⁻¹ * u * g with hu'def
    set v' : Γ := g⁻¹ * v * g with hv'def
    have hu'V : u' ∈ V := by
      rw [hu'def]
      simpa using (mem_set_normalizer_iff.mp hginvV u).mp huV
    have hu'Z : u' ∉ Z := by
      rw [hu'def]
      intro hmem
      have hconj := (mem_set_normalizer_iff.mp hZ (g⁻¹ * u * g)).mp hmem
      exact huZ (by simpa [mul_assoc] using hconj)
    have hv'V : v' ∈ V := by
      rw [hv'def]
      simpa using (mem_set_normalizer_iff.mp hginvV v).mp hvV
    have hv'Z : v' ∉ Z := by
      rw [hv'def]
      intro hmem
      have hconj := (mem_set_normalizer_iff.mp hZ (g⁻¹ * v * g)).mp hmem
      exact hvZ (by simpa [mul_assoc] using hconj)
    obtain ⟨k, ⟨hkT, hkZ⟩, hkuniq⟩ := hreg u' hu'V hu'Z v' hv'V hv'Z
    refine ⟨g * k * g⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hkT, by rw [conj_apply']⟩
    · have heq : g * (v'⁻¹ * (k * u' * k⁻¹)) * g⁻¹
          = v⁻¹ * ((g * k * g⁻¹) * u * (g * k * g⁻¹)⁻¹) := by
        rw [hu'def, hv'def]; group
      rw [← heq]
      exact (mem_set_normalizer_iff.mp hZ _).mp hkZ
    · intro y hy
      obtain ⟨hyT, hyZ⟩ := hy
      obtain ⟨t, htT, hty⟩ := mem_conjSub.mp hyT
      have hty' : y = g * t * g⁻¹ := by rw [← hty]
      have htZ : v'⁻¹ * (t * u' * t⁻¹) ∈ Z := by
        have h := (mem_set_normalizer_iff.mp hginvZ _).mp hyZ
        rw [hty'] at h
        have heq : g⁻¹ * (v⁻¹ * (g * t * g⁻¹ * u * (g * t * g⁻¹)⁻¹)) * g⁻¹⁻¹
            = v'⁻¹ * (t * u' * t⁻¹) := by
          rw [hu'def, hv'def]; group
        rwa [heq] at h
      have : t = k := hkuniq t ⟨htT, htZ⟩
      rw [hty', this]

private lemma orbitMod_conj {T Z : Subgroup Γ} {g : Γ} (hZ : g ∈ normalizer (Z : Set Γ))
    (u : Γ) :
    {w : Γ | g⁻¹ * w * g ∈ orbitMod T Z u}
      = orbitMod (conjSub g T) Z (g * u * g⁻¹) := by
  ext w
  simp only [Set.mem_setOf_eq, orbitMod]
  constructor
  · rintro ⟨k, hkT, hk⟩
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hkT, by rw [conj_apply']⟩
    · have hconj := (mem_set_normalizer_iff.mp hZ _).mp hk
      have heq : g * ((k * u * k⁻¹)⁻¹ * (g⁻¹ * w * g)) * g⁻¹
          = (g * k * g⁻¹ * (g * u * g⁻¹) * (g * k * g⁻¹)⁻¹)⁻¹ * w := by group
      rwa [heq] at hconj
  · rintro ⟨k', hk'mem, hk'⟩
    obtain ⟨k, hkT, hk'eq⟩ := mem_conjSub.mp hk'mem
    refine ⟨k, hkT, ?_⟩
    have hconj := (mem_set_normalizer_iff.mp (inv_mem hZ) _).mp hk'
    have hk'val : k' = g * k * g⁻¹ := by rw [← hk'eq]
    rw [hk'val] at hconj
    have heq : g⁻¹ * ((g * k * g⁻¹ * (g * u * g⁻¹) * (g * k * g⁻¹)⁻¹)⁻¹ * w) * g⁻¹⁻¹
        = (k * u * k⁻¹)⁻¹ * (g⁻¹ * w * g) := by group
    rwa [heq] at hconj

theorem isOrbitMod_conj {T Z : Subgroup Γ} {O : Set Γ} {g : Γ}
    (hZ : g ∈ normalizer (Z : Set Γ)) (hO : ∀ x, x ∈ O ↔ g * x * g⁻¹ ∈ O)
    (h : IsOrbitMod T Z O) : IsOrbitMod (conjSub g T) Z O := by
  obtain ⟨u, huO, hOeq⟩ := h
  refine ⟨g * u * g⁻¹, (hO u).mp huO, ?_⟩
  have hOinv : ∀ x, x ∈ O ↔ g⁻¹ * x * g ∈ O := by
    intro x
    have := hO (g⁻¹ * x * g)
    simpa [mul_assoc] using this.symm
  rw [hOeq, ← orbitMod_conj hZ u]
  ext w
  rw [← hOeq]
  exact hOinv w

theorem forall_isSylowIn_of_one [Finite Γ] {p : ℕ} [Fact p.Prime] {V T₀ : Subgroup Γ}
    (h₀ : IsSylowIn p V T₀) {P : Subgroup Γ → Prop} (hP : P T₀)
    (hinv : ∀ g ∈ V, P T₀ → P (conjSub g T₀)) : ∀ T : Subgroup Γ, IsSylowIn p V T → P T := by
  intro T hT
  obtain ⟨g, hgV, hg⟩ := exists_conj_of_isSylowIn h₀ hT
  rw [hg]
  exact hinv g hgV hP


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

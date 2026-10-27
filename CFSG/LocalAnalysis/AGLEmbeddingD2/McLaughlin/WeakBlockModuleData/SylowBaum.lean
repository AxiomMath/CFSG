module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open CFSG.AGLEmbeddingD2.GN

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_of_mem_normalizer_of_baum_le {C T S' : Subgroup G} [C.Normal]
    (hT : IsSylowTwoOf T ⊤) (hCS : C ≤ S') (hST : S' ≤ T ⊔ C) (hb : baum T ≤ S')
    {g : G} (hg : g ∈ Subgroup.normalizer (S' : Set G)) :
    ∃ s ∈ S', s⁻¹ * g ∈ Subgroup.normalizer (baum T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hTodd⟩ := hT
  set S : Subgroup G := T ⊓ S' with hS
  have hSK : S ≤ S' := inf_le_right
  have hdec : S' = S ⊔ C := by
    refine le_antisymm (fun s hs => ?_) (sup_le hSK hCS)
    obtain ⟨t, ht, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hST hs)
    have htS' : t ∈ S' := by
      have := S'.mul_mem hs (S'.inv_mem (hCS hc))
      simpa using this
    exact Subgroup.mul_mem_sup (⟨ht, htS'⟩ : t ∈ S) hc
  have hSodd : ¬ 2 ∣ (S.subgroupOf S').index := by
    have h1 : C.relIndex (S ⊔ C) = C.relIndex S := Subgroup.relIndex_sup_right S C
    rw [← hdec] at h1
    have hSC : S ⊓ C ≤ S := inf_le_left
    have hSC' : S ⊓ C ≤ C := inf_le_right
    have hCS' : C ≤ S' := hCS
    have e1 := Subgroup.relIndex_mul_relIndex (S ⊓ C) S S' hSC hSK
    have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ C) C S' hSC' hCS'
    rw [Subgroup.inf_relIndex_left] at e1
    rw [h1] at e2
    have hne : C.relIndex S ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have e3 : S.relIndex S' = (S ⊓ C).relIndex C := by
      have : C.relIndex S * S.relIndex S' = C.relIndex S * (S ⊓ C).relIndex C := by
        rw [e1, ← e2, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this
    have hSCeq : S ⊓ C = T ⊓ C := by
      ext x
      simp only [hS, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCS h.2⟩, h.2⟩⟩
    have hodd := not_two_dvd_relIndex_inf_of_normalizes (T := T) (K := C) (M := ⊤) le_top le_top
      (by
        intro t _
        rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t) hTodd
    show ¬ 2 ∣ S.relIndex S'
    rw [e3, hSCeq]
    exact hodd
  have hS2 : IsPGroup 2 (S.subgroupOf S') :=
    (hT2.to_le inf_le_left).comap_of_injective S'.subtype Subtype.coe_injective
  set B : Subgroup G := S.map (MulAut.conj g).toMonoidHom with hB
  have hBK : B ≤ S' := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg s).mp (hSK hs)
  have hBodd : ¬ 2 ∣ (B.subgroupOf S').index := by
    show ¬ 2 ∣ B.relIndex S'
    rw [hB, relIndex_map_conj_eq S S' g hg hSK]
    exact hSodd
  have hB2 : IsPGroup 2 (B.subgroupOf S') :=
    ((hT2.to_le inf_le_left).map (MulAut.conj g).toMonoidHom).comap_of_injective S'.subtype
      Subtype.coe_injective
  obtain ⟨x, hxK, hxS⟩ := exists_conj_eq_of_sylow hSK hBK hS2 hSodd hB2 hBodd
  have hmemB : ∀ s : G, g * s * g⁻¹ ∈ B ↔ s ∈ S := by
    intro s
    constructor
    · intro hmem
      obtain ⟨s', hs', he⟩ := Subgroup.mem_map.mp hmem
      have he' : g * s' * g⁻¹ = g * s * g⁻¹ := he
      have hss : s' = s := mul_left_cancel (mul_right_cancel he')
      exact hss ▸ hs'
    · intro hs
      exact ⟨s, hs, rfl⟩
  have huN : x⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have key := hxS (g * s * g⁻¹)
    have hconj : (x⁻¹ * g) * s * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * s * g⁻¹) * x := by
      simp [mul_assoc]
    rw [hconj, ← key, hmemB]
  have hbS : baum T ≤ S := le_inf (show baum T ≤ T from inf_le_left) hb
  have heq : baum T = baum S := baum_eq_of_le hbS inf_le_left
  refine ⟨x, hxK, ?_⟩
  rw [heq]
  exact normalizer_le_normalizer_baum S huN

end Abstract

section GN

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem normalizer_le_normalizer_gnImg_baum_of_le (hX : GNSetting X T)
    {S : Subgroup (X ⧸ gnC T)} (hPS : gnImg T (baum T) ≤ S) (hST : S ≤ gnImg T T) :
    Subgroup.normalizer (S : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) := by
  intro e he
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  have hg : g ∈ Subgroup.normalizer ((S.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at he ⊢
    intro h
    have := he (QuotientGroup.mk' (gnC T) h)
    simpa [Subgroup.mem_comap, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
  have hCS : gnC T ≤ S.comap (QuotientGroup.mk' (gnC T)) := by
    intro c hc
    rw [Subgroup.mem_comap, show QuotientGroup.mk' (gnC T) c = 1 from (QuotientGroup.eq_one_iff c).2 hc]
    exact S.one_mem
  have hST' : S.comap (QuotientGroup.mk' (gnC T)) ≤ T ⊔ gnC T := by
    intro s hs
    rw [mem_sup_gnC_iff]
    exact hST hs
  have hb : baum T ≤ S.comap (QuotientGroup.mk' (gnC T)) := fun x hx =>
    hPS (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨s, hs, hn⟩ := exists_mul_of_mem_normalizer_of_baum_le hX.sylow hCS hST' hb hg
  have hs1 : QuotientGroup.mk' (gnC T) s ∈
      Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) := by
    have h1 : QuotientGroup.mk' (gnC T) s ∈ gnImg T T := hST hs
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp h1
    rw [← hts]
    exact (Subgroup.le_normalizer_map _) (Subgroup.mem_map_of_mem _
      ((normalizer_le_normalizer_baum T) (Subgroup.le_normalizer ht)))
  have hn1 : QuotientGroup.mk' (gnC T) (s⁻¹ * g) ∈
      Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) :=
    (Subgroup.le_normalizer_map _) (Subgroup.mem_map_of_mem _ hn)
  have : (g : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) s * QuotientGroup.mk' (gnC T) (s⁻¹ * g) := by
    simp
  rw [this]
  exact Subgroup.mul_mem _ hs1 hn1

end GN

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

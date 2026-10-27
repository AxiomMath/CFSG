module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Presentation.Co2Exact
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenTr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.Sporadic.Co2Cert

section Hyp

structure Co2Hyp {G : Type} [Group G] (B K R0 R1 : Subgroup G) (y : G) : Prop where
  elem : IsElemAbelian 3 B
  card_B : Nat.card B = 27
  mem_B : y ∈ B
  ne_one : y ≠ 1
  le_cent : K ≤ Subgroup.centralizer ({y} : Set G)
  maps_A6 : MapsOntoType K S8.isA6
  card_R0 : Nat.card R0 = 2
  norm_R0 : K ⊔ B ≤ Subgroup.normalizer (R0 : Set G)
  pgroup_R1 : IsPGroup 2 R1
  norm_R1 : K ⊔ B ≤ Subgroup.normalizer (R1 : Set G)
  lt : R0 < R1

theorem Co2Hyp.map {G H : Type} [Group G] [Group H] (ψ : G →* H) (hψ : Function.Injective ψ)
    {B K R0 R1 : Subgroup G} {y : G} (h : Co2Hyp B K R0 R1 y) :
    Co2Hyp (B.map ψ) (K.map ψ) (R0.map ψ) (R1.map ψ) (ψ y) := by
  have hN : ∀ R : Subgroup G, K ⊔ B ≤ Subgroup.normalizer (R : Set G) →
      K.map ψ ⊔ B.map ψ ≤ Subgroup.normalizer ((R.map ψ : Subgroup H) : Set H) := fun R hR => by
    rw [← Subgroup.map_sup]
    exact (Subgroup.map_mono hR).trans (Subgroup.le_normalizer_map ψ)
  refine ⟨CFSG.SectionRank.isElemAbelian_map h.elem ψ,
    (Subgroup.card_map_of_injective hψ).trans h.card_B, Subgroup.mem_map_of_mem ψ h.mem_B,
    fun h1 => h.ne_one (hψ (h1.trans (map_one ψ).symm)), ?_, ?_,
    (Subgroup.card_map_of_injective hψ).trans h.card_R0, hN R0 h.norm_R0, h.pgroup_R1.map ψ,
    hN R1 h.norm_R1, (Subgroup.map_lt_map_iff_of_injective hψ).2 h.lt⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hx)]
  · obtain ⟨i, hi, f, hf⟩ := h.maps_A6
    exact ⟨i, hi, f.comp (Subgroup.equivMapOfInjective K ψ hψ).symm.toMonoidHom,
      hf.comp (Subgroup.equivMapOfInjective K ψ hψ).symm.surjective⟩

@[expose] def Co2ModelStmt : Prop :=
  ∀ (B K R0 R1 : Subgroup (Equiv.Perm (Fin 2300))) (y : Equiv.Perm (Fin 2300)),
    B ≤ co2P → K ≤ co2P → R0 ≤ co2P → R1 ≤ co2P → Co2Hyp B K R0 R1 y → IsExtraSpec2 R1

end Hyp

section Row


theorem rowCo2_of_model (h : Co2ModelStmt) : I301BRow .co2 := by
  intro S _ _ hS B I K R0 R1 y _ hBe hBc hyB hy1 _ _ _ _ _ hR0c hKy hK hKB hR1 hKB1 h01
  obtain ⟨i, hi, ⟨e₁⟩⟩ := hS
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have eS : S ≃* NativeSporadic.Co2 := e₁.trans (by exact b.symm)
  have hAutS : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g :=
    CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model S eS
  have hZ1 : ∀ t : NativeSporadic.Co2, (∀ u : NativeSporadic.Co2, u * t = t * u) → t = 1 := by
    intro t ht
    haveI : IsSimpleGroup NativeSporadic.Co2 := CFSG.Sporadic.Co2.isSimpleGroup_Co2
    have hnc : ¬ IsMulCommutative NativeSporadic.Co2 := by
      intro hcomm
      haveI : IsMulCommutative NativeSporadic.Co2 := hcomm
      have hp : (Nat.card NativeSporadic.Co2).Prime :=
        (Group.is_simple_iff_prime_card).mp inferInstance
      rw [CFSG.Sporadic.Co2.card_Co2] at hp
      exact (by norm_num : ¬ Nat.Prime 42305421312000) hp
    have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (G := NativeSporadic.Co2) hnc
    exact Subgroup.mem_bot.1 (hZ ▸ Subgroup.mem_center_iff.2 ht)
  obtain ⟨Φ⟩ := @nonempty_mulAut_equiv_of_inner S NativeSporadic.Co2 _ inferInstance eS
    hZ1 hAutS
  set ψ : MulAut S →* Equiv.Perm (Fin 2300) := co2P.subtype.comp (Φ.trans co2PermEquiv).toMonoidHom
  have hψ : Function.Injective ψ := co2P.subtype_injective.comp (Φ.trans co2PermEquiv).injective
  have hle : ∀ A : Subgroup (MulAut S), A.map ψ ≤ co2P := by
    rintro A _ ⟨x, -, rfl⟩
    exact ((Φ.trans co2PermEquiv) x).2
  have hH : Co2Hyp B K R0 R1 y := ⟨hBe, hBc, hyB, hy1, hKy, hK, hR0c, hKB, hR1, hKB1, h01⟩
  exact (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_congr
    (Subgroup.equivMapOfInjective R1 ψ hψ)).2
      (h _ _ _ _ _ (hle B) (hle K) (hle R0) (hle R1) (hH.map ψ hψ))

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

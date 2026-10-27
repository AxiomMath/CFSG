module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Lift

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem isPlaneDiagonal_map (O : Subgroup H) [O.Normal] {D : Subgroup H} {z g : H}
    (h : IsPlaneDiagonal p D z g) :
    IsPlaneDiagonal p (D.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O z)
      (QuotientGroup.mk' O g) := by
  obtain ⟨hgN, hcop, a, b, hab, hord, hgz, hgd⟩ := h
  refine ⟨?_, ?_, a, b, hab, hord, ?_, ?_⟩
  · exact Subgroup.le_normalizer_map (QuotientGroup.mk' O) ⟨g, hgN, rfl⟩
  · exact hcop.coprime_dvd_right (orderOf_map_dvd _ g)
  · have := congrArg (QuotientGroup.mk' O) hgz
    simpa [map_mul, map_inv, map_pow] using this
  · intro d hd hdz
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hd0z : d₀ ∉ zpowers z := fun hmem => hdz (by
      rw [← MonoidHom.map_zpowers]
      exact mem_map_of_mem _ hmem)
    obtain ⟨c, hc⟩ := hgd d₀ hd₀ hd0z
    refine ⟨c, ?_⟩
    have := congrArg (QuotientGroup.mk' O) hc
    simpa [map_mul, map_inv, map_pow] using this

theorem eq_of_map_eq_of_le (hp : p.Prime) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {D A B : Subgroup H} (hD : IsPGroup p D) (hA : A ≤ D)
    (hB : B ≤ D) (h : A.map (QuotientGroup.mk' O) = B.map (QuotientGroup.mk' O)) : A = B := by
  apply le_antisymm
  · intro a ha
    have : QuotientGroup.mk' O a ∈ B.map (QuotientGroup.mk' O) := h ▸ mem_map_of_mem _ ha
    obtain ⟨b, hb, hab⟩ := this
    have := eq_of_mk_eq_of_isPGroup hp O hO hD (hB hb) (hA ha) hab
    rw [← this]
    exact hb
  · intro b hb
    have : QuotientGroup.mk' O b ∈ A.map (QuotientGroup.mk' O) := h ▸ mem_map_of_mem _ hb
    obtain ⟨a, ha, hab⟩ := this
    have := eq_of_mk_eq_of_isPGroup hp O hO hD (hA ha) (hB hb) hab
    rw [← this]
    exact ha

theorem lift_conclusion (hp : p.Prime) {z : H} {D : Subgroup H} (hD : IsPGroup p D) (hzD : z ∈ D)
    (hX : (∀ T : Subgroup (H ⧸ primeComplementCore (G := H) p), p.Coprime (Nat.card T) →
        D.map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ normalizer (T : Set _) →
          T = ⊥) ∨
      (∀ y ∈ D.map (QuotientGroup.mk' (primeComplementCore (G := H) p)), y ≠ 1 →
        ∃ h ∈ normalizer ((D.map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
            Subgroup _) : Set _),
          zpowers y = (zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) z)).map
            (MulAut.conj h).toMonoidHom)) :
    (∀ T : Subgroup H, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set H) →
        T ≤ primeComplementCore (G := H) p) ∨
      (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set H),
        zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom) := by
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set π := QuotientGroup.mk' O with hπ
  rcases hX with hA | hB
  · left
    intro T hT hDT
    have hDT' : D.map π ≤ normalizer ((T.map π : Subgroup _) : Set _) := by
      rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.le_normalizer_map π ⟨d, hDT hd, rfl⟩
    have hTbot : T.map π = ⊥ := hA _ (hT.of_dvd_right (T.card_map_dvd π)) hDT'
    intro t ht
    have hmem : π t ∈ T.map π := mem_map_of_mem π ht
    rw [hTbot, mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff t).1 hmem
  · right
    intro y hy hy1
    have hyπ : π y ≠ 1 := by
      intro h1
      have hmem : y ∈ D ⊓ O := ⟨hy, (QuotientGroup.eq_one_iff y).1 h1⟩
      rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hD hO, mem_bot] at hmem
      exact hy1 hmem
    obtain ⟨hbar, hhbarN, hhbar⟩ := hB (π y) (mem_map_of_mem π hy) hyπ
    obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective O hbar
    have hh₀ : h₀ ∈ ((O ⊔ normalizer (D : Set H) : Subgroup H) : Set H) :=
      comap_normalizer_map_le_sup hp O hO hD hhbarN
    rw [Subgroup.normal_mul, Set.mem_mul] at hh₀
    obtain ⟨o, ho, h, hh, rfl⟩ := hh₀
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    have hπh : π (o * h) = π h := by rw [map_mul, hπo, one_mul]
    rw [hπh] at hhbar
    refine ⟨h, hh, ?_⟩
    have hAle : zpowers y ≤ D := zpowers_le.2 hy
    have hBle : (zpowers z).map (MulAut.conj h).toMonoidHom ≤ D := by
      rintro _ ⟨w, hw, rfl⟩
      have hwD : w ∈ D := zpowers_le.2 hzD hw
      exact (mem_normalizer_iff.1 hh w).1 hwD
    refine eq_of_map_eq_of_le hp O hO hD hAle hBle ?_
    have e1 : (zpowers y).map π = zpowers (π y) := MonoidHom.map_zpowers π y
    have e2 : ((zpowers z).map (MulAut.conj h).toMonoidHom).map π =
        ((zpowers z).map π).map (MulAut.conj (π h)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [e1, e2, MonoidHom.map_zpowers, hhbar]

end Lift

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

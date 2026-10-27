module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42A5
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

variable {Y K : Type} [Group Y] [Group K] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem hasNormalPComplement_of_surjective' (θ : Y →* K) (hθ : Function.Surjective θ)
    (h : CFSG.HasNormalPComplement p Y) : CFSG.HasNormalPComplement p K := by
  obtain ⟨N, hN, hNc, hNp⟩ := h
  have hNf : (N.map θ).Normal := hN.map θ hθ
  refine ⟨N.map θ, hNf, Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := N) θ) hNc, ?_⟩
  have hle : N ≤ (N.map θ).comap θ := Subgroup.le_comap_map θ N
  let φ : Y ⧸ N →* K ⧸ N.map θ := QuotientGroup.map N (N.map θ) θ hle
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := hθ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact hNp.of_surjective φ hφ

variable (θ : Y →* K) (hker : Nat.Coprime (Nat.card θ.ker) p)
include hker

theorem inf_ker_eq_bot {Q : Subgroup Y} (hQ : IsPGroup p Q) : Q ⊓ θ.ker = ⊥ := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  exact Subgroup.inf_eq_bot_of_coprime (by rw [hn]; exact Nat.Coprime.pow_left n hker.symm)

theorem eq_of_map_eq {Q : Subgroup Y} (hQ : IsPGroup p Q) {a b : Y} (ha : a ∈ Q) (hb : b ∈ Q)
    (h : θ a = θ b) : a = b := by
  have hm : a⁻¹ * b ∈ Q ⊓ θ.ker :=
    ⟨Q.mul_mem (Q.inv_mem ha) hb,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h, inv_mul_cancel])⟩
  rw [inf_ker_eq_bot θ hker hQ, Subgroup.mem_bot] at hm
  exact inv_mul_eq_one.mp hm

omit hker in
theorem exists_mem_normalizer_map (hθ : Function.Surjective θ) (Q : Sylow p Y) {k : K}
    (hk : k ∈ Subgroup.normalizer (((Q : Subgroup Y).map θ : Subgroup K) : Set K)) :
    ∃ y ∈ Subgroup.normalizer ((Q : Subgroup Y) : Set Y), θ y = k := by
  obtain ⟨y₀, rfl⟩ := hθ k
  set D := ((Q : Subgroup Y).map θ).comap θ with hD
  have hy₀ : y₀ ∈ Subgroup.normalizer (D : Set Y) := by
    rw [hD, ← Subgroup.comap_normalizer_eq_of_surjective _ hθ]
    exact hk
  obtain ⟨n, hn, q, hq, rfl⟩ :=
    CFSG.OddStandard.Seitz77.frattini_aux Q D (Subgroup.le_comap_map θ _) hy₀
  obtain ⟨q', hq', hqe⟩ := hq
  refine ⟨n * q', Subgroup.mul_mem _ hn (Subgroup.le_normalizer hq'), ?_⟩
  rw [map_mul, map_mul, hqe]

theorem map_frattini_map_eq {Q : Subgroup Y} (hQ : IsPGroup p Q) :
    (frattini ↥(Q.map θ)).map (Q.map θ).subtype = ((frattini ↥Q).map Q.subtype).map θ := by
  set f : ↥Q →* ↥(Q.map θ) := θ.subgroupMap Q with hf
  have hfi : Function.Injective f := fun a b hab =>
    Subtype.ext (eq_of_map_eq θ hker hQ a.2 b.2 (congrArg Subtype.val hab))
  set e : ↥Q ≃* ↥(Q.map θ) := MulEquiv.ofBijective f ⟨hfi, θ.subgroupMap_surjective Q⟩ with he
  have h := CFSG.RankThree.PartOne.Torsion37.frattini_map_mulEquiv e
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem irred_of_irred_map (hθ : Function.Surjective θ) (Q : Sylow p Y)
    (hirr : ∀ V : Subgroup K, V ≤ Q.mapSurjective hθ →
      ¬ V ≤ (frattini ↥((Q.mapSurjective hθ : Sylow p K) : Subgroup K)).map
        ((Q.mapSurjective hθ : Sylow p K) : Subgroup K).subtype →
      Subgroup.normalizer (((Q.mapSurjective hθ : Sylow p K) : Subgroup K) : Set K) ≤
        Subgroup.normalizer (V : Set K) → V = Q.mapSurjective hθ)
    (V : Subgroup Y) (hVQ : V ≤ Q) (hVΦ : ¬ V ≤ (frattini ↥(Q : Subgroup Y)).map
      (Q : Subgroup Y).subtype)
    (hNV : Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤ Subgroup.normalizer (V : Set Y)) :
    V = Q := by
  have hQ := Q.2
  have hirr' : ∀ W : Subgroup K, W ≤ (Q : Subgroup Y).map θ →
      ¬ W ≤ (frattini ↥((Q : Subgroup Y).map θ)).map ((Q : Subgroup Y).map θ).subtype →
      Subgroup.normalizer ((((Q : Subgroup Y).map θ : Subgroup K)) : Set K) ≤
        Subgroup.normalizer (W : Set K) → W = (Q : Subgroup Y).map θ := hirr
  have heq := hirr' (V.map θ) (Subgroup.map_mono hVQ) ?_ ?_
  · refine le_antisymm hVQ fun q hq => ?_
    obtain ⟨v, hv, hve⟩ := (heq.symm ▸ ⟨q, hq, rfl⟩ : θ q ∈ V.map θ)
    rw [← eq_of_map_eq θ hker hQ (hVQ hv) hq hve]
    exact hv
  · rw [map_frattini_map_eq θ hker hQ]
    rintro hle
    apply hVΦ
    intro v hv
    obtain ⟨f, hf, hfe⟩ := hle ⟨v, hv, rfl⟩
    have hfQ : f ∈ (Q : Subgroup Y) := Subgroup.map_subtype_le _ hf
    rwa [← eq_of_map_eq θ hker hQ hfQ (hVQ hv) hfe]
  · intro k hk
    obtain ⟨y, hy, rfl⟩ := exists_mem_normalizer_map θ hθ Q hk
    exact Subgroup.le_normalizer_map θ ⟨y, hNV hy, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

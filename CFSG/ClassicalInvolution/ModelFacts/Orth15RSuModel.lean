module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuKlein
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuLayerAGrp
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuLayerB
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows
public import CFSG.ClassicalInvolution.ModelFacts.Models
import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer)

section Twin

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_layer_u0 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∃ Q : Subgroup (Su K p f 4), SLayer (u0 K p f) Q ∧ t0 K p f ∈ Q ∧
      ∃ m ∈ Q, MixProp (suMat m) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω * ω = -1 := by
    have hsq : IsSquare (-1 : K) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
      have hodd : Odd (p ^ f) := (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      ring_nf
      omega
    obtain ⟨ω, hω⟩ := hsq
    exact ⟨ω, hω.symm⟩
  have hσω2 : unitaryInvolution K p f ω * unitaryInvolution K p f ω = -1 := by
    rw [← map_mul, hω, map_neg, map_one]
  have hcase : unitaryInvolution K p f ω = ω ∨ unitaryInvolution K p f ω = -ω := by
    have : (unitaryInvolution K p f ω - ω) * (unitaryInvolution K p f ω + ω) = 0 := by
      linear_combination hσω2 - hω
    rcases mul_eq_zero.mp this with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  rcases hcase with h | h
  · exact exists_layer_u0_of_pos (ω := ω) ⟨hK, h2, hω, h⟩ hq
  · exact exists_layer_u0_of_neg hK h2 hq hω h

theorem blockEmb_two_negOne_eq : blockEmb K p f 4 2 2 (by norm_num) (negOneSU K p f) =
    zneg K p f * x0 K p f := by
  rw [zneg_mul_x0]
  simp [blk]

theorem twin_neg_su (h2 : (2 : K) ≠ 0) {g : Su K p f 4}
    {x x' : Su K p f 4} (hxg : x = g * x0 K p f * g⁻¹) {R' : Subgroup (Su K p f 4)}
    (hR'g : R' = (R0' K p f).map (MulAut.conj g).toMonoidHom) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) : x' = zneg K p f * x := by
  rw [hR'g] at hx'R'
  obtain ⟨y, hy, rfl⟩ := hx'R'
  obtain ⟨B, rfl⟩ := hy
  have hyy : blockEmb K p f 4 2 2 (by norm_num) B * blockEmb K p f 4 2 2 (by norm_num) B = 1 := by
    have h1 : (MulAut.conj g) (blockEmb K p f 4 2 2 (by norm_num) B *
        blockEmb K p f 4 2 2 (by norm_num) B) = (MulAut.conj g) 1 := by
      rw [map_mul, map_one]
      exact hx'2
    exact (MulAut.conj g).injective h1
  have hBB : B * B = 1 := by
    apply blockEmb_injective (K := K) (p := p) (f := f) (m := 4) (k := 2) (i := 2) (by norm_num)
    rw [map_mul, map_one]
    exact hyy
  have hB : suMat B * suMat B = (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← suMat_mul, hBB, suMat_one, one_smul]
  have hBneg : B = negOneSU K p f := by
    rcases su2_sq_cases h2 B hB with ⟨-, hB1 | hB1⟩ | ⟨h1, -⟩
    · exfalso
      apply hx'1
      have : B = 1 := suMat_injective (by rw [hB1, suMat_one])
      rw [this]
      simp
    · exact suMat_injective (by rw [hB1, suMat_negOneSU])
    · exfalso
      apply h2
      linear_combination h1
  rw [hBneg, blockEmb_two_negOne_eq, hxg]
  show g * (zneg K p f * x0 K p f) * g⁻¹ = zneg K p f * (g * x0 K p f * g⁻¹)
  calc g * (zneg K p f * x0 K p f) * g⁻¹
      = (g * zneg K p f * g⁻¹) * (g * x0 K p f * g⁻¹) := by group
    _ = zneg K p f * (g * x0 K p f * g⁻¹) := by rw [zneg_conj]

theorem alphaOf_twin_psu (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {H : Type} [Group H] [Finite H] (ψ : Su K p f 4 →* H)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R')
    {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x') {u : H}
    (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨Q, hQu, ht0Q, m, hmQ, hmix⟩ := exists_layer_u0 hK hp hq
  have hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hsame, mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hRg' : R = (R0 K p f).map (MulAut.conj g).toMonoidHom := hRg
  have hR'g' : R' = (R0' K p f).map (MulAut.conj g).toMonoidHom := hR'g
  have hxg' : x = g * x0 K p f * g⁻¹ := hxg
  have hx'neg := twin_neg_su h2 hxg' hR'g' hx'R' hx'2 hx'1
  have hzneg : ψ (zneg K p f) = 1 := by
    have h1 : ψ x' = ψ (zneg K p f) * ψ x := by rw [hx'neg, map_mul]
    rw [← hsame] at h1
    exact mul_eq_right.mp h1.symm
  have hu' : u ∈ (R ⊔ R').map ψ := by
    rw [Subgroup.map_sup]
    exact hu
  obtain ⟨s, hs, hsu⟩ := hu'
  have hs' : s ∈ (R0 K p f ⊔ R0' K p f).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, ← hRg', ← hR'g']
    exact hs
  obtain ⟨w, hw, rfl⟩ := hs'
  have hsu' : ψ (g * w * g⁻¹) = u := hsu
  have hww : w * w ∈ Subgroup.center (Su K p f 4) := by
    have h1 : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ Subgroup.center (Su K p f 4) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, hsu', hu2])
    have e : (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [e] at h1
    exact InnerL4.mem_center_of_conj_mem_center h1
  rcases classify_w hK h2 hw hww with rfl | rfl | rfl | rfl | ⟨h, hh, rfl⟩
  · exact absurd (by simpa using hsu'.symm) hu1
  · exact absurd (by rw [hxg']; exact hsu'.symm) huz
  · refine absurd ?_ huz
    have e : g * (zneg K p f * x0 K p f) * g⁻¹ = zneg K p f * x := by
      calc g * (zneg K p f * x0 K p f) * g⁻¹
          = (g * zneg K p f * g⁻¹) * (g * x0 K p f * g⁻¹) := by group
        _ = zneg K p f * x := by rw [zneg_conj, hxg']
    rw [e, map_mul, hzneg, one_mul] at hsu'
    exact hsu'.symm
  · refine absurd ?_ hu1
    rw [zneg_conj, hzneg] at hsu'
    exact hsu'.symm
  · have hxh : h * x0 K p f = x0 K p f * h := (slayer_x0 hK h2 hq).comm h hh
    have key := alphaOf_klein_psu hK hp hq ψ hker hzneg hQu ht0Q hmQ hmix (g * h)
    have e1 : toInducedAutOn ψ.range ⟨u, hun⟩ = innerHom ψ (g * h * u0 K p f * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show u = ψ (g * h * u0 K p f * (g * h)⁻¹)
      rw [← hsu']
      congr 1
      group
    have e2 : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ =
        innerHom ψ (g * h * x0 K p f * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show ψ x = ψ (g * h * x0 K p f * (g * h)⁻¹)
      congr 1
      rw [hxg']
      calc g * x0 K p f * g⁻¹ = g * (h * x0 K p f * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 K p f * (g * h)⁻¹ := by group
    rw [e1, e2]
    exact key

end Twin


theorem alphaOf_closure_congr {H : Type} [Group H] {L L' : Subgroup H} (hL : L = L') {a b b' : H}
    (ha : a ∈ Subgroup.normalizer (L : Set H)) (hb : b ∈ Subgroup.normalizer (L : Set H))
    (ha' : a ∈ Subgroup.normalizer (L' : Set H)) (hb' : b' ∈ Subgroup.normalizer (L' : Set H))
    (hbb : b = b') :
    alphaOf (Subgroup.closure ({toInducedAutOn L ⟨a, ha⟩, toInducedAutOn L ⟨b, hb⟩} :
      Set ↥(inducedAutOn L))) = ⊥ ↔
    alphaOf (Subgroup.closure ({toInducedAutOn L' ⟨a, ha'⟩, toInducedAutOn L' ⟨b', hb'⟩} :
      Set ↥(inducedAutOn L'))) = ⊥ := by
  subst hL hbb
  exact Iff.rfl

theorem twinInnerAlpha_psu4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 4 p e) : TwinInnerAlpha p e .PSU 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 huz
  set ψ' : Su (GaloisField p (2 * e)) p e 4 →* H := ψ.comp φ.symm.toMonoidHom with hψ'
  have hrange : ψ.range = ψ'.range := by
    ext h
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨φ s, by simp [hψ']⟩
    · rintro ⟨s, rfl⟩
      exact ⟨φ.symm s, rfl⟩
  have hψ'φ : ∀ s, ψ' (φ s) = ψ s := fun s => by simp [hψ']
  have hmapR : ∀ S : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).K,
      (S.map φ.toMonoidHom).map ψ' = S.map ψ := fun S => by
    rw [Subgroup.map_map]
    congr 1
    ext s
    simp [hψ']
  have hker' : ψ'.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    intro s hs
    have h1 : φ.symm s ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hs
    have h2 := (mulEquiv_mem_center_iff φ (φ.symm s)).mpr (hpair.ker h1)
    simpa using h2
  have hun' : u ∈ Subgroup.normalizer (ψ'.range : Set H) := hrange ▸ hun
  have key := alphaOf_twin_psu hK hp2 hq ψ' hker' ((hφ R).mp hpair.mem) ((hφ R').mp hpair.mem')
    (fun h => hpair.ne (Subgroup.map_injective φ.injective h)) (x := φ x) (x' := φ x')
    ⟨x, hpair.hx, rfl⟩ (by rw [← map_mul, hpair.hx2, map_one])
    (fun h => hpair.hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hpair.hx', rfl⟩
    (by rw [← map_mul, hpair.hx'2, map_one])
    (fun h => hpair.hx'1 (φ.injective (h.trans (map_one φ).symm)))
    (by rw [hψ'φ, hψ'φ]; exact hpair.same) (u := u) hun'
    (by rw [hmapR, hmapR]; exact hu) hu2 hu1 (by rw [hψ'φ]; exact huz)
  exact (alphaOf_closure_congr hrange hun (FrameVertex.mem_normalizer_range ψ x) hun'
    (FrameVertex.mem_normalizer_range ψ' (φ x)) (by rw [hψ'φ])).mpr key

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

namespace CFSG.ClassicalInvolution.Asc77

theorem twinSmallInnerSU (p : ℕ) [Fact p.Prime] : TwinSmallInnerSU p := fun hp2 _ hq hadm =>
  ModelFacts.Orth15.InnerSu.twinInnerAlpha_psu4 hp2 hq hadm

end CFSG.ClassicalInvolution.Asc77

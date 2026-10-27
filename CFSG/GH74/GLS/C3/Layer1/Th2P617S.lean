module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem isSylowOf_cj' {P H : Subgroup G} (h : IsSylowOf 2 P H) (g : G) :
    IsSylowOf 2 (cj g P) (cj g H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [show Nat.card ↥(cj g P) = Nat.card ↥P from
      Subgroup.card_map_of_injective (MulAut.conj g).injective,
    show Nat.card ↥(cj g H) = Nat.card ↥H from
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h.card_eq

omit [Finite G] in
theorem cj_top (c : G) : cj c (⊤ : Subgroup G) = ⊤ :=
  eq_top_iff.2 fun g _ => ⟨c⁻¹ * g * c, Subgroup.mem_top _, by show c * (c⁻¹ * g * c) * c⁻¹ = g; group⟩

omit [Finite G] in
theorem cj_eq_of_mem' {H : Subgroup G} {c : G} (hc : c ∈ H) : cj c H = H :=
  C3.Layer1.Thm1.map_conj_eq_self_of_mem hc

omit [Finite G] in
theorem cj_CxK_eq {x c : G} {K : Subgroup G} (hcx : c ∈ centralizer ({x} : Set G))
    (hcK : cj c K = K) : cj c (CxK x K) = CxK x K := by
  have h1 := PumpTerm.CxK_cmap' c x K
  have hcx' : c * x * c⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 hcx
    rw [this]; group
  rw [hcx'] at h1
  have h2 : Stage1.Thm3.Sec4.cmap c K = K := hcK
  rw [h2] at h1
  exact h1.symm

omit [Finite G] in
theorem cj_centralizer_pair {x y c : G} (hcx : c ∈ centralizer ({x} : Set G)) :
    cj c (centralizer ({x, y} : Set G)) = centralizer ({x, c * y * c⁻¹} : Set G) := by
  have hcx' : c * x = x * c := mem_centralizer_singleton_iff.1 hcx
  have hx1 : c * x * c⁻¹ = x := by rw [hcx']; group
  have hx2 : c⁻¹ * x * c = x := by
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [hcx']
      _ = x := by group
  ext g
  rw [mem_cj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    rcases hw with hw | hw
    · have h1 := h x (by simp)
      rw [hw]
      calc x * g = (c * x * c⁻¹) * g := by rw [hx1]
        _ = c * (x * (c⁻¹ * g * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * g * c) * x) * c⁻¹ := by rw [h1]
        _ = g * (c * x * c⁻¹) := by group
        _ = g * x := by rw [hx1]
    · have h1 := h y (by simp)
      rw [hw]
      calc c * y * c⁻¹ * g = c * (y * (c⁻¹ * g * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * g * c) * y) * c⁻¹ := by rw [h1]
        _ = g * (c * y * c⁻¹) := by group
  · intro h w hw
    rcases hw with hw | hw
    · have h1 := h x (by simp)
      rw [hw]
      calc x * (c⁻¹ * g * c) = c⁻¹ * ((c * x * c⁻¹) * g) * c := by group
        _ = c⁻¹ * (x * g) * c := by rw [hx1]
        _ = c⁻¹ * (g * x) * c := by rw [h1]
        _ = c⁻¹ * g * c * (c⁻¹ * x * c) := by group
        _ = c⁻¹ * g * c * x := by rw [hx2]
    · have h1 := h (c * y * c⁻¹) (by simp)
      rw [hw]
      calc y * (c⁻¹ * g * c) = c⁻¹ * ((c * y * c⁻¹) * g) * c := by group
        _ = c⁻¹ * (g * (c * y * c⁻¹)) * c := by rw [h1]
        _ = c⁻¹ * g * c * y := by group


omit [Finite G] in
theorem conj_mem_cSec_of_cj_eq {K : Subgroup G} {d : G} (hdK : cj d K = K) {z : G}
    (hz : z ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    d * z * d⁻¹ ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  have h : d * z * d⁻¹ ∈ centralizerSection (cj d K) (cj d (pPrimeCoreOf 2 K)) :=
    Stage1.Thm2.Recip.cj_mem_centralizerSection hz d
  have hO : cj d (pPrimeCoreOf 2 K) = pPrimeCoreOf 2 K := by
    rw [← pPrimeCoreOf_cj, hdK]
  rw [hdK, hO] at h
  exact h

theorem _root_.CFSG.GH74.GLS.Th2Std.conj_A7 (hL34 : B_gen4_noL34_elem) (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hQ2 : 2 ≤ pRank 2 ↥(CxK x K))
    {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    Th2Std x (c * y * c⁻¹) K (cj c T) (cj c S) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN := hs.K_normal_A7 hG h7
  have hcN : c ∈ normalizer (K : Set G) :=
    C3.Layer1.P34.mem_normalizer_of_conj_le (fun a ha => by
      have := hKN c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) a ha
      simpa using this)
  have hcK : cj c K = K := cj_eq_of_mem_normalizer hcN
  have hcx' : c * x * c⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 hc
    rw [this]; group
  have hcC : cj c (centralizer ({x} : Set G)) = centralizer ({x} : Set G) := by
    rw [cj_centralizer_singleton, hcx']
  have hcCx : cj c (CxK x K) = CxK x K := cj_CxK_eq hc hcK
  have hcNx : cj c (NxK x K) = NxK x K := cj_eq_of_mem' ⟨hc, hcN⟩
  have hcen := centerlessBar_of_A7 h7
  have hno34 : ¬ IsL34Quotient (kBar K) := by
    intro hl34
    refine hL34 G hG.gen4 x K hs.orderOf_x hs.comp ⟨hl34, ?_, ?_⟩
    · have hC : center (kBar K) = ⊥ := by
        refine eq_bot_iff.2 fun a ha => ?_
        rw [Subgroup.mem_center_iff] at ha
        exact (Subgroup.mem_bot.2 (hcen a (fun b => (ha b).symm)))
      exact Th2.Bal.isElementaryAbelian_two_of_sq _ (fun d hd => by
        rw [hC, Subgroup.mem_bot] at hd
        rw [hd, one_mul])
    · have hC : center (kBar K) = ⊥ := by
        refine eq_bot_iff.2 fun a ha => ?_
        rw [Subgroup.mem_center_iff] at ha
        exact (Subgroup.mem_bot.2 (hcen a (fun b => (ha b).symm)))
      rw [hC, Subgroup.card_bot]
      norm_num
  have hLU := hs.v2ss.isV2Triple.1
  have hLU' : IsLocallyUnbalancing x (c * y * c⁻¹) K := by
    obtain ⟨hIL, hy2, hyC, hyN, hyO⟩ := hLU
    refine ⟨hIL, ?_, ?_, ?_, ?_⟩
    · have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
      rw [show (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ from rfl] at this
      rw [this, hy2]
    · exact (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hc hyC)
        ((centralizer ({x} : Set G)).inv_mem hc)
    · exact (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem hcN hyN)
        ((normalizer (K : Set G)).inv_mem hcN)
    · intro hle
      apply hyO
      intro g hg
      have hg' : c * g * c⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({x, c * y * c⁻¹} : Set G)) := by
        rw [← cj_centralizer_pair hc, pPrimeCoreOf_cj, mem_cj_iff]
        rw [show c⁻¹ * (c * g * c⁻¹) * c = g by group]
        exact hg
      have h1 := hle hg'
      have hinvK : cj c⁻¹ K = K := cj_eq_of_mem_normalizer ((normalizer (K : Set G)).inv_mem hcN)
      have h2 := conj_mem_cSec_of_cj_eq hinvK h1
      rw [show c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g by group] at h2
      exact h2
  have hV3 : IsV2Triple x (c * y * c⁻¹) K :=
    ⟨hLU', hs.v2ss.isV2Triple.2.1, Or.inl hQ2, fun h => absurd h hno34⟩
  refine ⟨⟨?_, fun hL2 => absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hL2)⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨⟨⟨⟨-, A1⟩, A2⟩, A3⟩, A4⟩ := hs.v2ss.1
    exact ⟨⟨⟨⟨hV3, A1⟩, A2⟩, A3⟩, A4⟩
  · have h1 := isSylowOf_cj' hs.setup.sylowT c
    rwa [hcC] at h1
  · have h1 := isSylowOf_cj' hs.setup.sylowT0 c
    have e : cj c (T ⊓ NxK x K) = cj c T ⊓ cj c (NxK x K) :=
      Subgroup.map_inf_eq T (NxK x K) (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    rw [e, hcNx] at h1
    exact h1
  · rw [mem_cj_iff, show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hs.y_mem
  · have h1 := isSylowOf_cj' hs.sylowS c
    rwa [cj_top] at h1
  · exact Subgroup.map_mono hs.T_le_S

end CFSG.GH74.GLS.Th2.Obs

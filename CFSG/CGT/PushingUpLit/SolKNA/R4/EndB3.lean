module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Spine
public import CFSG.ClassicalInvolution.Q3.Q3TLT3Fusion
public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {r : ℕ} {R : Subgroup G} {S : Sylow 2 R} {t : G}
  {T : Sylow 2 G}

omit [Finite G] in
private theorem isSylow2In_mono' {P M H : Subgroup G} (h : IsSylow2In P H) (hPM : P ≤ M)
    (hMH : M ≤ H) : IsSylow2In P M :=
  ⟨hPM, h.2.1, fun V' hV'M hV'2 hle => h.2.2 V' (hV'M.trans hMH) hV'2 hle⟩

theorem StdR.mem_genFittingFStar (h : StdR r R S t T)
    (hO : classicalInvolutionOddCore G = ⊥) : t ∈ genFittingFStar G := by
  have hd := h.datum
  set F : Subgroup G := genFittingFStar G with hF
  have hFn : F.Normal := genFittingFStar_normal G
  set S₀ : Subgroup G := (S : Subgroup R).map R.subtype with hS₀
  by_contra htF
  have hSF : S₀ ⊓ F = ⊥ := by
    by_contra hne
    exact htF (Subgroup.mem_inf.mp (hd.mem_of_ne_bot (inf_le_left.trans hd.S₀_le)
      ((hd.sylow_core.2.1).to_le inf_le_left) hne)).2
  have h1 := comm613Gen_normal hd.hypOmegaGen hd.S₀_mem_RSet hFn hSF
  have h2 : oddCoreOf F = ⊥ := by
    rw [AscThmA.oddCoreOf_eq_inf, hO, inf_bot_eq]
  rw [h2, le_bot_iff] at h1
  have hSc : S₀ ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  exact htF ((hSc.trans (CFSG.Adapters.generalized_fitting_self_centralizing G)) hd.mem)

theorem StdR.normalizes_S₀ (h : StdR r R S t T) {x : G} (hx : x ∈ (T : Subgroup G))
    {s : G} (hs : s ∈ (S : Subgroup R).map R.subtype) :
    x * s * x⁻¹ ∈ (S : Subgroup R).map R.subtype := by
  set S₀ : Subgroup G := (S : Subgroup R).map R.subtype with hS₀
  have hd := h.datum
  have hsyl : IsSylow2In S₀ (tightCore R) := hd.sylow_core
  have hxN : x ∈ Subgroup.normalizer (tightCore R : Set G) :=
    hd.le_normalizer_core (h.hTt hx)
  have hKT : IsPGroup 2 ↥(tightCore R ⊓ (T : Subgroup G)) := T.isPGroup'.to_le inf_le_right
  have heq : tightCore R ⊓ (T : Subgroup G) = S₀ :=
    hsyl.2.2 _ inf_le_left hKT (le_inf hsyl.1 h.hST)
  have hmem : x * s * x⁻¹ ∈ tightCore R ⊓ (T : Subgroup G) := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxN s).mp (hsyl.1 hs), ?_⟩
    exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hx (h.hST hs))
      ((T : Subgroup G).inv_mem hx)
  rwa [heq] at hmem

theorem StdR.false_of_conj_mem_cStar (h : StdR r R S t T) {k : G}
    (hkT : k * t * k⁻¹ ∈ (T : Subgroup G)) (hkt : k * t * k⁻¹ ≠ t)
    (hkC : k * t * k⁻¹ ∈ centralizerModOdd ⊤ (tightCore R)) : False := by
  set S₀ : Subgroup G := (S : Subgroup R).map R.subtype with hS₀
  set u : G := k * t * k⁻¹ with hu
  have hd := h.datum
  have hsyl : IsSylow2In S₀ (tightCore R) := hd.sylow_core
  have hcomm : ∀ s ∈ S₀, s * u = u * s := by
    intro s hs
    have hc : ⁅u, s⁆ ∈ oddCoreOf (tightCore R) := hkC.2.2.2 s (hsyl.1 hs)
    have hcS : ⁅u, s⁆ ∈ S₀ := by
      rw [commutatorElement_def]
      exact S₀.mul_mem (h.normalizes_S₀ hkT hs) (S₀.inv_mem hs)
    have h1 : ⁅u, s⁆ = 1 := by
      have hodd : Odd (Nat.card ↥(oddCoreOf (tightCore R))) := oddCoreOf_odd_natCard _
      have h2 : IsPGroup 2 ↥(Subgroup.zpowers ⁅u, s⁆) :=
        hsyl.2.1.to_le (Subgroup.zpowers_le.mpr hcS)
      exact eq_one_of_isPGroup_of_mem_odd hodd hc h2
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hSN : S₀ ≤ Subgroup.normalizer (conjSub k (tightCore R) : Set G) := by
    intro s hs
    have hsc : k⁻¹ * s * k ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcomm s hs
      calc k⁻¹ * s * k * t = k⁻¹ * (s * (k * t * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * t * k⁻¹) * s) * k := by rw [this]
        _ = t * (k⁻¹ * s * k) := by group
    have hn := hd.le_normalizer_core hsc
    rw [mem_normalizer_iff_conjSub_eq] at hn ⊢
    calc conjSub s (conjSub k (tightCore R))
        = conjSub k (conjSub (k⁻¹ * s * k) (tightCore R)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub k (tightCore R) := by rw [hn]
  have hKΩ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJΩ : conjSub k (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨k, rfl⟩
  have hne : tightCore R ≠ conjSub k (tightCore R) := by
    intro heq
    have hmem : u ∈ tightCore R := by
      rw [heq]
      exact conj_mem_conjSub hd.isUniqueInvolution_core.mem
    have hinv : u * u = 1 := by
      calc u * u = k * (t * t) * k⁻¹ := by rw [hu]; group
        _ = 1 := by rw [t_mul_t hd]; group
    rcases hd.isUniqueInvolution_core.unique _ hmem hinv with h1 | h1
    · apply hd.isUniqueInvolution_core.ne_one
      calc t = k⁻¹ * u * k := by rw [hu]; group
        _ = 1 := by rw [h1]; group
    · exact hkt h1
  exact h.edgeless _ hJΩ _ hKΩ
    (Or.inl ⟨hKΩ, hne, S₀, hd.S₀_mem_RSet, hsyl.1, hSN⟩)

theorem StdR.exists_conj_mem_sylow (h : StdR r R S t T) {B : Subgroup G}
    (hBT : B ≤ (T : Subgroup G)) (hsc : fusionStronglyClosed (B : Set G) (T : Subgroup G))
    {g : G} (hgB : g ∈ Subgroup.centralizer (B : Set G)) (hgt : g * t * g⁻¹ ≠ t)
    (hgc : g * t * g⁻¹ * t = t * (g * t * g⁻¹)) :
    ∃ k ∈ Subgroup.centralizer (B : Set G), k * t * k⁻¹ ∈ (T : Subgroup G) ∧
      k * t * k⁻¹ ≠ t := by
  classical
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hC
  set Ct : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCt
  have hTN : (T : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 : (x⁻¹)⁻¹ * b * x⁻¹ ∈ (T : Subgroup G) := by
        rw [inv_inv]
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hx (hBT hb))
          ((T : Subgroup G).inv_mem hx)
      have := hsc b hb x⁻¹ h1
      rwa [inv_inv] at this
    · intro hb
      have h1 : x⁻¹ * (x * b * x⁻¹) * x ∈ (T : Subgroup G) :=
        (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hx)
          (hBT hb)) hx
      have := hsc _ hb x h1
      rwa [show x⁻¹ * (x * b * x⁻¹) * x = b by group] at this
  have hTsyl : IsSylow2In (T : Subgroup G) (Subgroup.normalizer (B : Set G)) :=
    isSylow2In_mono' ⟨le_top, T.isPGroup', fun _ _ hV2 hle => T.is_maximal' hV2 hle⟩ hTN le_top
  have hCN : C ≤ Subgroup.normalizer (B : Set G) := Subgroup.centralizer_le_normalizer _
  have hNC : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc b hb
      have hb' : n⁻¹ * b * n ∈ B := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (B : Set G)).inv_mem hn)
          b).mp hb
        rwa [inv_inv] at this
      have := hc _ hb'
      calc b * (n * c * n⁻¹) = n * ((n⁻¹ * b * n) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * b * n)) * n⁻¹ := by rw [this]
        _ = n * c * n⁻¹ * b := by group
    · intro hc b hb
      have hb' : n * b * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn b).mp hb
      have := hc _ hb'
      calc b * c = n⁻¹ * ((n * b * n⁻¹) * (n * c * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * c * n⁻¹) * (n * b * n⁻¹)) * n := by rw [this]
        _ = c * b := by group
  have hTC : IsSylow2In ((T : Subgroup G) ⊓ C) C :=
    Sec6Gen.isSylow2In_inf_of_le_normalizer' hTsyl hCN hNC
  have hTCt : IsSylow2In ((T : Subgroup G) ⊓ C) (C ⊓ Ct) :=
    isSylow2In_mono' hTC (le_inf inf_le_right (inf_le_left.trans h.hTt)) inf_le_left
  set t' : G := g * t * g⁻¹ with ht'
  have ht'2 : IsPGroup 2 ↥(Subgroup.zpowers t') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht', Q3.orderOf_conj_eq, h.datum.order, pow_one]
  have ht'C : t' ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbt : b * t = t * b :=
      (Subgroup.mem_centralizer_iff.mp (h.hTt (hBT hb)) t (Set.mem_singleton t)).symm
    have hbg : b * g = g * b := (Subgroup.mem_centralizer_iff.mp hgB b hb)
    have hbg' : b * g⁻¹ = g⁻¹ * b := by
      calc b * g⁻¹ = g⁻¹ * (g * b) * g⁻¹ := by group
        _ = g⁻¹ * (b * g) * g⁻¹ := by rw [hbg]
        _ = g⁻¹ * b := by group
    calc b * (g * t * g⁻¹) = (b * g) * t * g⁻¹ := by group
      _ = (g * b) * t * g⁻¹ := by rw [hbg]
      _ = g * (b * t) * g⁻¹ := by group
      _ = g * (t * b) * g⁻¹ := by rw [hbt]
      _ = g * t * (b * g⁻¹) := by group
      _ = g * t * (g⁻¹ * b) := by rw [hbg']
      _ = (g * t * g⁻¹) * b := by group
  have ht'Ct : t' ∈ Ct := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hgc
  obtain ⟨V, hV, hV'⟩ := IsSylow2In.exists_ge ht'2
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨ht'C, ht'Ct⟩))
  obtain ⟨d, hd, hdV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hTCt
  refine ⟨d * g, (C.mul_mem (Subgroup.mem_inf.mp hd).1 hgB), ?_, ?_⟩
  · have h1 : d * t' * d⁻¹ ∈ conjSub d V := conj_mem_conjSub (hV' (Subgroup.mem_zpowers t'))
    rw [hdV] at h1
    have : d * g * t * (d * g)⁻¹ = d * t' * d⁻¹ := by rw [ht']; group
    rw [this]
    exact h1.1
  · intro heq
    apply hgt
    have hdt : d * t = t * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
    calc g * t * g⁻¹ = d⁻¹ * (d * g * t * (d * g)⁻¹) * d := by group
      _ = d⁻¹ * t * d := by rw [heq]
      _ = d⁻¹ * (t * d) := by group
      _ = d⁻¹ * (d * t) := by rw [hdt]
      _ = t := by group

end CFSG.CGT.PushingUpLit.SolKNA.R4

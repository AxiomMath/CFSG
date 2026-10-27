module

public import CFSG.ClassicalInvolution.Asc77.AscC5O1
public import CFSG.ClassicalInvolution.Asc77.AscC5O1G
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem not_conj_z (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) (y : G) : y * z * y⁻¹ ≠ a := by
  intro h
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hu₁K : u₁ ∈ K := C.hyp.hR.2.1 C.hyp.hu₁.1
  refine T7ER.not_commute_of_conj hs C.hyp.hW C.hyp.hE4 hs.stand.mem hs.hz
    (by rw [h]; exact C.haz) hu₁K C.hyp.hu₁.2.1 ?_
  rw [h]
  exact C.haR u₁ C.hyp.hu₁.1

theorem R_le [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    R ≤ exactLayer Ω a := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨-, -, -, hK₂, -, -⟩ := C.om5
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one C.ha2
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (C.haR x hx).symm
  have hS₂ : IsSylow2In R (exactCore a K) :=
    (isSylow2In_exactCore_iff hs.stand.hyp hcpg hs.stand.mem hK₂.2).mpr ⟨h.hRsyl, hRc⟩
  exact hS₂.1.trans (exactCore_le_exactLayer hK₂)

theorem R'_le [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    R' ≤ exactLayer Ω a := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨-, -, -, -, hK₂', -⟩ := C.om5
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one C.ha2
  have hRc : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (C.haR' x hx).symm
  have hS₂ : IsSylow2In R' (exactCore a K') :=
    (isSylow2In_exactCore_iff hs.stand.hyp hcpg hs.hK'.1 hK₂'.2).mpr ⟨h.hR'syl, hRc⟩
  exact hS₂.1.trans (exactCore_le_exactLayer hK₂')

theorem z_not_triv [IsSimpleGroup G] (hM5 : Om5Centerless p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : z ∉ trivialOnQuot (exactLayer Ω a) := by
  intro hz
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  have hb : conjSub z (exactLayer Ω a) = exactLayer Ω a := conjSub_eq_self_of_mem hzY
  have hfix := (layerAut_eq_id_iff (exactLayer Ω a) hb).mpr hz
  refine hD.twin.hzA.ne_one (hM5 _ _ _ _ _ _ _ hD _ fun x => ?_)
  induction x using QuotientGroup.induction_on with
  | H y =>
    have h1 := hfix (QuotientGroup.mk y)
    rw [C25Y.layerAut_mk] at h1
    have h2 : (QuotientGroup.mk (C25Y.conjOnSub (exactLayer Ω a) hb y) :
        ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)) =
        T7H.toBar Ω a z hzY * QuotientGroup.mk y * (T7H.toBar Ω a z hzY)⁻¹ := by
      unfold T7H.toBar
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      rfl
    rw [h2] at h1
    calc T7H.toBar Ω a z hzY * QuotientGroup.mk y
        = (T7H.toBar Ω a z hzY * QuotientGroup.mk y * (T7H.toBar Ω a z hzY)⁻¹) *
            T7H.toBar Ω a z hzY := by group
      _ = QuotientGroup.mk y * T7H.toBar Ω a z hzY := by rw [h1]

theorem a_triv (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    a ∈ trivialOnQuot (exactLayer Ω a) := by
  have hΩ : HypOmegaMod p f Ω := C.hyp.std.setting.stand.hyp
  refine ⟨mem_normalizer_of_conjSub_eq (conjSub_exactLayer hΩ.conjInvariant
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)), fun y hy => ?_⟩
  have hc : y * a = a * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hy)
  rw [(commutatorElement_eq_one_iff_mul_comm).mpr hc.symm]
  exact one_mem _

theorem mem_S_triv [IsSimpleGroup G] (hM5 : Om5Centerless p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {w : G} (hwS : w ∈ (S : Subgroup G))
    (hw : w ∈ trivialOnQuot (exactLayer Ω a)) : w = 1 ∨ w = a := by
  have hO := odd_card_oddCoreIn (exactLayer Ω a)
  have key : ∀ r ∈ exactLayer Ω a, r ∈ (S : Subgroup G) →
      r ∈ Subgroup.centralizer ({w} : Set G) := by
    intro r hrX hrS
    have h1 : ⁅w, r⁆ ∈ oddCoreIn (exactLayer Ω a) := hw.2 r hrX
    have h2 : ⁅w, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
        ((S : Subgroup G).mul_mem hwS hrS) ((S : Subgroup G).inv_mem hwS))
        ((S : Subgroup G).inv_mem hrS)
    have h3 := eq_one_of_isPGroup_of_odd S.isPGroup' hO h2 h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3.symm
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G) :=
    sup_le (fun r hr => key r (C.R_le hr) (C.hyp.hR.2.2 hr))
      (fun r hr => key r (C.R'_le hr) (C.hyp.hR'.2.2 hr))
  have hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    refine ⟨hwS, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rcases C.hA0 w hwA with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h ▸ hw) (C.z_not_triv hM5)
  · exfalso
    apply C.z_not_triv hM5
    have := (trivialOnQuot (exactLayer Ω a)).mul_mem
      ((trivialOnQuot (exactLayer Ω a)).inv_mem C.a_triv) (h ▸ hw)
    simpa using this

theorem twoElt_triv [IsSimpleGroup G] (hM5 : Om5Centerless p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {w : G} (hwa : w * a = a * w)
    (hw : w ∈ trivialOnQuot (exactLayer Ω a)) (h2 : IsPGroup 2 (Subgroup.zpowers w)) :
    w = 1 ∨ w = a := by
  classical
  set X := exactLayer Ω a with hX
  have hΩ : HypOmegaMod p f Ω := C.hyp.std.setting.stand.hyp
  have hz2 : z * z = 1 := C.hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  have hwT : Subgroup.zpowers w ≤ trivialOnQuot X := Subgroup.zpowers_le.mpr hw
  obtain ⟨n, hn, hfix⟩ := exists_conj_fixed_of_isPGroup (A := Subgroup.zpowers w)
    (N := oddCoreIn X) h2 (odd_card_oddCoreIn X)
    (fun x hx m hm => conj_mem_oddCoreIn_of_mem_normalizer (hwT hx).1 hm) hz2
    (fun m hm => conj_mem_oddCoreIn hzY hm) (by
      intro x hx
      have h1 : ⁅x, z⁆ ∈ oddCoreIn X := (hwT hx).2 z hzY
      have h3 := conj_mem_oddCoreIn hzY h1
      have e : z * ⁅x, z⁆ * z⁻¹ = z * (x * z * x⁻¹) := by
        rw [commutatorElement_def, hzi]
        calc z * (x * z * x⁻¹ * z) * z = z * (x * z * x⁻¹) * (z * z) := by group
          _ = z * (x * z * x⁻¹) := by rw [hz2, mul_one]
      rwa [e] at h3)
  have hnX : n ∈ X := oddCoreIn_le X hn
  have hna : n * a = a * n :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hnX)
  set w₁ := n⁻¹ * w * n with hw₁
  have hw₁z : w₁ * z * w₁⁻¹ = z := by
    have h := hfix w (Subgroup.mem_zpowers w)
    calc w₁ * z * w₁⁻¹ = n⁻¹ * (w * (n * z * n⁻¹) * w⁻¹) * n := by rw [hw₁]; group
      _ = z := by rw [h]; group
  have hw₁a : w₁ * a * w₁⁻¹ = a := by
    calc w₁ * a * w₁⁻¹ = n⁻¹ * w * (n * a * n⁻¹) * w⁻¹ * n := by rw [hw₁]; group
      _ = n⁻¹ * (w * a * w⁻¹) * n := by
          rw [show n * a * n⁻¹ = a by rw [hna]; group]; group
      _ = n⁻¹ * a * n := by rw [show w * a * w⁻¹ = a by rw [hwa]; group]
      _ = a := by rw [mul_assoc, ← hna]; group
  have hw₁T : w₁ ∈ trivialOnQuot X := by
    have hOT : ∀ m ∈ oddCoreIn X, m ∈ trivialOnQuot X := by
      intro m hm
      have hmX : m ∈ X := oddCoreIn_le X hm
      refine ⟨mem_normalizer_of_conjSub_eq (conjSub_eq_self_of_mem hmX), fun y hy => ?_⟩
      rw [commutatorElement_def]
      have h1 : y * m⁻¹ * y⁻¹ ∈ oddCoreIn X := conj_mem_oddCoreIn hy ((oddCoreIn X).inv_mem hm)
      have := (oddCoreIn X).mul_mem hm h1
      simpa [mul_assoc] using this
    rw [hw₁]
    exact (trivialOnQuot X).mul_mem ((trivialOnQuot X).mul_mem
      ((trivialOnQuot X).inv_mem (hOT n hn)) hw) (hOT n hn)
  have h2₁ : IsPGroup 2 (Subgroup.zpowers w₁) := by
    have e : Subgroup.zpowers w₁ = (Subgroup.zpowers w).map (MulAut.conj n⁻¹).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      congr 1
      simp [hw₁]
    rw [e]
    exact h2.map _
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hzA₀ : z ∈ A₀ := T7T.z_mem_centralizer_of_hyp C.hyp
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A₀ : Set G) := fun s hs =>
    mem_normalizer_of_conjSub_eq (T7T.conjSub_centralizer_of_hyp C.hyp hs)
  have hSsyl : IsSylow2In (S : Subgroup G) (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hSN, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hfixA : ∀ h ∈ A₀, w₁ * h * w₁⁻¹ = h := by
    intro h hh
    rcases C.hA0 h hh with rfl | rfl | rfl | rfl
    · group
    · exact hw₁a
    · exact hw₁z
    · calc w₁ * (a * z) * w₁⁻¹ = (w₁ * a * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = a * z := by rw [hw₁a, hw₁z]
  have hw₁N : Subgroup.zpowers w₁ ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_,
      fun hh => ?_⟩)
    · rw [hfixA h hh]; exact hh
    · have e1 := hfixA _ hh
      have e2 : h = w₁ * h * w₁⁻¹ := by
        calc h = w₁⁻¹ * (w₁ * h * w₁⁻¹) * w₁ := by group
          _ = w₁⁻¹ * (w₁ * (w₁ * h * w₁⁻¹) * w₁⁻¹) * w₁ := by rw [e1]
          _ = w₁ * h * w₁⁻¹ := by group
      rw [e2]; exact hh
  obtain ⟨V, hV, hVle⟩ := IsSylow2In.exists_ge h2₁ hw₁N
  obtain ⟨g, hg, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSsyl)
    (show IsSylow2Of _ _ from hV)
  have hw₂S : g⁻¹ * w₁ * g ∈ (S : Subgroup G) := by
    have h := hVle (Subgroup.mem_zpowers w₁)
    rw [hVeq] at h
    exact mem_conjSubgroup_iff.mp h
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A₀ : Set G) := Subgroup.inv_mem _ hg
  have hb : g⁻¹ * a * g⁻¹⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp hginv a).mp C.haA
  rw [inv_inv] at hb
  have hbcases : g⁻¹ * a * g = a ∨ g⁻¹ * a * g = a * z := by
    rcases C.hA0 _ hb with h | h | h | h
    · exfalso; apply C.ha1
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl h
    · exfalso; apply C.not_conj_z g
      calc g * z * g⁻¹ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [h]
        _ = a := by group
    · exact Or.inr h
  have hw₂T : g⁻¹ * w₁ * g ∈ trivialOnQuot (exactLayer Ω (g⁻¹ * a * g)) := by
    have h := trivialOnQuot_conjSub hw₁T g⁻¹
    rw [inv_inv] at h
    have e := exactLayer_conj hΩ.conjInvariant g⁻¹ a
    rw [inv_inv] at e
    rw [e]
    exact h
  have hw₂ : g⁻¹ * w₁ * g = 1 ∨ g⁻¹ * w₁ * g = g⁻¹ * a * g := by
    rcases hbcases with hb' | hb'
    · rw [hb'] at hw₂T ⊢
      exact C.mem_S_triv hM5 hw₂S hw₂T
    · rw [hb'] at hw₂T ⊢
      exact C.swap.mem_S_triv hM5 hw₂S hw₂T
  have hw₁' : w₁ = 1 ∨ w₁ = a := by
    rcases hw₂ with h | h
    · left
      calc w₁ = g * (g⁻¹ * w₁ * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc w₁ = g * (g⁻¹ * w₁ * g) * g⁻¹ := by group
        _ = a := by rw [h]; group
  rcases hw₁' with h | h
  · left
    calc w = n * w₁ * n⁻¹ := by rw [hw₁]; group
      _ = 1 := by rw [h]; group
  · right
    calc w = n * w₁ * n⁻¹ := by rw [hw₁]; group
      _ = n * a * n⁻¹ := by rw [h]
      _ = a := by rw [hna]; group

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O

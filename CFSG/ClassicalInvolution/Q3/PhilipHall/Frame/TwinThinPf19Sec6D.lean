module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Five
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Yu
public import CFSG.ClassicalInvolution.Q3.TL3T41

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem thin_Yu {u : G} (hu : PairInv K K' z π g u)
    (horb : ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x (conjSub g K) = L) :
    ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ t : G, IsUniqueInvolution L t →
      ∀ Q : Subgroup G, Q ≤ centLayer (CoreAssembly.conjClass K₀) u →
      (∀ x ∈ centLayer (CoreAssembly.conjClass K₀) u, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) →
      IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = t := by
  intro L hL t ht Q hQY hQn hQ2 x hxL hxQ
  have hX := S.pairInv_commute hu
  have hXY := S.piGen_le_centLayer hX
  obtain ⟨y, hy, rfl⟩ := horb L hL
  have heq : y * (g * z * g⁻¹) * y⁻¹ = t := ((S.hz.conj g).conj y).eq ht
  have hx' : y⁻¹ * x * y ∈ conjSub g K := mem_conjSub_iff.mp hxL
  have hxQ' : y⁻¹ * x * y ∈ Q := by
    have := hQn y⁻¹ ((centLayer (CoreAssembly.conjClass K₀) u).inv_mem hy) x hxQ
    simpa using this
  have hKgX : conjSub g K ≤ piGen π := le_piGen S.hg
  have hQX : Q ⊓ piGen π ≤ Qz z := by
    refine normalTwo_le_Qz S.X_le_cent (S.hos.piGen_normal S.hK S.hπ S.hH1 S.hz) inf_le_right
      (fun x hx q hq => ?_) (hQ2.to_le inf_le_left)
    exact Subgroup.mem_inf.mpr ⟨hQn x (hXY hx) q (Subgroup.mem_inf.mp hq).1,
      (piGen π).mul_mem ((piGen π).mul_mem hx (Subgroup.mem_inf.mp hq).2) ((piGen π).inv_mem hx)⟩
  have hmax : MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) K (conjSub g K) :=
    maxAdj_of_mem_maxOrb S.hos.graph S.hπ S.hg
  have hKgΩ : conjSub g K ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K S.hK g
  have h1 := eq_of_mem_Qz' S.hs.hyp S.hs.two S.card8 hKgΩ (S.thin K (conjSub g K) hmax)
    S.hz (S.hz.conj g) hx' (hQX (Subgroup.mem_inf.mpr ⟨hxQ', hKgX hx'⟩))
  rcases h1 with h | h
  · left
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = y * (g * z * g⁻¹) * y⁻¹ := by rw [h]
      _ = t := heq

theorem exists_five_X {m : ℕ} (hm : 5 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ∃ x : G, x ∈ piGen π ∧ x ^ 5 = 1 ∧ x ≠ 1 := by
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  obtain ⟨x', hx5, w, hxw⟩ := TwinThinPf19.exists_pow_five_not_comm J hm hk
  have hx'X : (x' : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (x' : G)).mp x'.2
  have hxX : g⁻¹ * (x' : G) * g ∈ piGen π := by
    have := mem_conjSub_iff.mp hx'X
    simpa using this
  refine ⟨g⁻¹ * (x' : G) * g, hxX, ?_, fun h1 => hxw ?_⟩
  · have h5 : (x' : G) ^ 5 = 1 := by
      have := congrArg Subtype.val hx5
      simpa using this
    have : (g⁻¹ * (x' : G) * g) ^ 5 = g⁻¹ * (x' : G) ^ 5 * g := by
      have h := conj_pow (a := g⁻¹) (b := (x' : G)) (i := 5)
      rwa [inv_inv] at h
    rw [this, h5]
    group
  · have h2 : (x' : G) = 1 := by
      have : (x' : G) = g * (g⁻¹ * (x' : G) * g) * g⁻¹ := by group
      rw [this, h1]
      group
    have h3 : x' = 1 := Subtype.ext h2
    rw [h3]
    simp

theorem d2_Yu {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hG : Nat.card G ≤ n)
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 5 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G} (hu : PairInv K K' z π g u)
    (hO : classicalInvolutionOddCore ↥(centLayer (CoreAssembly.conjClass K₀) u) = ⊥)
    (horb : ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x (conjSub g K) = L)
    (hnb : conjSub g K' ∈ π)
    (hE2 : ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ t : G, IsUniqueInvolution L t →
      t ∈ pCoreOf 2 (centLayer (CoreAssembly.conjClass K₀) u)) :
    ∃ k : ℕ, 5 ≤ k ∧ Nonempty (AEIdent (centMembers (CoreAssembly.conjClass K₀) u) k) := by
  classical
  set Yu := centLayer (CoreAssembly.conjClass K₀) u with hYu
  set P := centMembers (CoreAssembly.conjClass K₀) u with hPdef
  have hX := S.pairInv_commute hu
  have hXY := S.piGen_le_centLayer hX
  have hD : ThmDGenBelow 3 n := TL4.thmDGenBelow_of_gen hP.thmD
  have hΩ0 : HypOmegaGen (CoreAssembly.conjClass K₀) := S.hs.hyp
  have hKgΩ : conjSub g K ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K S.hK g
  have hKg'Ω : conjSub g K' ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K' S.hK'.1 g
  have hKgP : conjSub g K ∈ P := S.mem_centMembers_of_pi hX S.hg
  have hKg'P : conjSub g K' ∈ P := S.mem_centMembers_of_pi hX hnb
  have hPΩ : P ⊆ CoreAssembly.conjClass K₀ := fun L hL => hL.1
  have hspan : pSpan P = Yu := rfl
  have hcard : Nat.card ↥(pSpan P) < n :=
    lt_of_lt_of_le (natCard_lt_of_ne_top (S.centLayer_ne_top hS hnab hu.2.2.2.1)) hG
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L' := by
    intro L hL L' hL'
    obtain ⟨a, ha, rfl⟩ := horb L hL
    obtain ⟨b, hb, rfl⟩ := horb L' hL'
    refine ⟨b * a⁻¹, Yu.mul_mem hb (Yu.inv_mem ha), ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  have hYuC : Yu ≤ Subgroup.centralizer ({u} : Set G) := centLayer_le fun L hL => hL.2
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    intro L hL x hx
    have h := conjSub_mem_centMembers hΩ0.conjInvariant (n := x) hL
    have hxu : x * u * x⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hYuC hx)
      rw [this]
      group
    rwa [hxu] at h
  have hodd' : classicalInvolutionOddCore ↥(pSpan P) = ⊥ := hO
  have hPcore : ((pCoreOf 2 Yu).subgroupOf Yu).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 Yu Yu le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hE2' : ∀ L ∈ P, ∀ t : G, IsUniqueInvolution L t → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ t ∈ Q := by
    intro L hL t ht
    refine ⟨pCoreOf 2 Yu, CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 Yu,
      fun x hx q hq => ?_, CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 Yu,
      hE2 L hL t ht⟩
    have := hPcore.conj_mem ⟨q, CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 Yu hq⟩
      (Subgroup.mem_subgroupOf.mpr hq) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp this
  have h8 := S.card8
  obtain ⟨x5, hx5X, hx5, hx51⟩ := S.exists_five_X hm J
  have hx5Y : (⟨x5, hXY hx5X⟩ : ↥Yu) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have hx5ne : (⟨x5, hXY hx5X⟩ : ↥Yu) ≠ 1 := fun h => hx51 (congrArg Subtype.val h)
  have hk2 : ∀ {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AE.AEQ m)}
      (I : AEIdentOn P m 𝒜 H), IsPGroup 2 I.φ.ker := fun I =>
    (isPGroup_center_of_corefree hodd').to_le I.ker_le
  rcases hD G (CoreAssembly.conjClass K₀) hΩ0 S.hs.two (fun J hJ => by rw [h8 J hJ]; norm_num)
      S.aEmpty P hPΩ hcard htrans hinv hodd' hE2' with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | h64 | hAE | h29
  ·
    exfalso
    have := hsing _ hKgP _ hKg'P
    have h2 := congrArg (conjSub g⁻¹) this
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
    exact S.hne h2.symm
  ·
    exfalso
    exact false_of_WIn_eq hΩ0 S.hs.two h8 hPΩ ⟨_, hKgP⟩ hinv
      (fun L hL t ht Q hQY hQn hQ2 x hxL hxQ => S.thin_Yu hu horb L hL t ht Q hQY hQn hQ2 x hxL hxQ)
      hW
  ·
    exfalso
    have hE8card : Nat.card ↥(pSpan P) = 1344 := by
      have h1 := Subgroup.relIndex_mul_card E (pSpan P)
      rw [inf_eq_left.mpr hE.le, hE.index, hE.card] at h1
      omega
    have h5dvd : orderOf (⟨x5, hXY hx5X⟩ : ↥Yu) ∣ 1344 := by
      have h := orderOf_dvd_natCard (⟨x5, hXY hx5X⟩ : ↥Yu)
      rwa [show Nat.card ↥Yu = 1344 from hE8card] at h
    have h5ord : orderOf (⟨x5, hXY hx5X⟩ : ↥Yu) = 5 :=
      orderOf_eq_prime hx5Y hx5ne
    rw [h5ord] at h5dvd
    omega
  ·
    exfalso
    obtain ⟨I⟩ := h64
    exact hx5ne (I.pow_five (hk2 I)
      (fun h hh h5' => aeBarOver_pow_five (fun σ hσ hσ5 => l32_pow_five hσ hσ5) hh h5') hx5Y)
  · exact hAE
  ·
    exfalso
    obtain ⟨I⟩ := h29
    exact hx5ne (I.pow_five (hk2 I)
      (fun h hh h5' => aeBarOver_pow_five (fun σ hσ hσ5 => agl32_pow_five hσ hσ5) hh h5') hx5Y)

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

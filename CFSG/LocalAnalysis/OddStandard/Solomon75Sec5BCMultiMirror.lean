module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiBase
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiQ8
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneTrans

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Mirror

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem bcdMirror_eq_of_central {L V : Subgroup X}
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) (hV : IsPGroup 2 ↥V)
    (hcent : ∀ x ∈ V, x ∈ L → ∀ l ∈ L, ⁅l, x⁆ ∈ oddCoreOf L) {x y : X}
    (hxV : x ∈ V) (hyV : y ∈ V) (hxL : x ∈ L) (hyL : y ∈ L) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  let C := AhatData.CoverSetup.ofCover hLn
  have hcen : ∀ u : X, u ∈ V → ∀ hu : u ∈ L,
      (QuotientGroup.mk (⟨u, hu⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
        Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) := by
    intro u huV hu
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨hb1, hb2⟩ := mem_oddCoreOf_iff.1 (hcent u huV hu b b.2)
    have h1 : ⁅b, (⟨u, hu⟩ : ↥L)⁆ ∈ pPrimeCore 2 ↥L := hb2
    have h2 : ⁅QuotientGroup.mk' (pPrimeCore 2 ↥L) b,
        QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨u, hu⟩ : ↥L)⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hne : ∀ u : X, u ∈ V → ∀ hu : u ∈ L, u ≠ 1 →
      (QuotientGroup.mk (⟨u, hu⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ≠ 1 := by
    intro u huV hu hu1 h1
    have h2 : u ∈ oddCoreOf L := mem_oddCoreOf_iff.2 ⟨hu, (QuotientGroup.eq_one_iff _).1 h1⟩
    exact hu1 (eq_one_of_mem_of_mem_odd (oddCoreOf L) V (odd_card_oddCoreOf L) hV huV h2)
  have heq := C.center_eq_of_ne_one (hcen x hxV hxL) (hcen y hyV hyL) (hne x hxV hxL hx1)
    (hne y hyV hyL hy1)
  have h3 : (⟨x, hxL⟩ : ↥L)⁻¹ * ⟨y, hyL⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 heq
  have h4 : x⁻¹ * y ∈ oddCoreOf L := ⟨_, h3, rfl⟩
  have h5 : x⁻¹ * y ∈ V := V.mul_mem (V.inv_mem hxV) hyV
  have h6 := eq_one_of_mem_of_mem_odd (oddCoreOf L) V (odd_card_oddCoreOf L) hV h5 h4
  have h7 : y = x := by simpa using congrArg (fun t => x * t) h6
  exact h7.symm

private theorem bcdMirror_le_centralizer {s : X} {Zs : Subgroup X}
    {S₁ : Sylow 2 ↥(normalizer (Zs : Set X))} (hS₁ : Sec5Data X n s Zs S₁) {Q : Subgroup X}
    (hQZs : Q ≤ normalizer (Zs : Set X))
    (hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X)) :
    Q ≤ centralizer (Zs : Set X) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  have hZs : Zs ≤ centralizer ({q} : Set X) := by
    refine hS₁.pair.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 ?_)
    rintro w ⟨hwZs, L, hL, hLn⟩
    have hqL : q ∈ normalizer (L : Set X) := hQn L ⟨⟨w, hL⟩, hLn⟩ hq
    have hwL : w ∈ L := hL.2.1
    have hw1 : w ≠ 1 := by
      intro h1
      have h2 := hL.1
      rw [h1, orderOf_one] at h2
      omega
    have hvZs : q * w * q⁻¹ ∈ Zs := (Subgroup.mem_normalizer_iff.1 (hQZs hq) w).1 hwZs
    have hvL : q * w * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hqL w).1 hwL
    have hv1 : q * w * q⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      have h2 := congrArg (fun t => q⁻¹ * t * q) h1
      simpa [mul_assoc] using h2
    have hcent : ∀ x ∈ Zs, x ∈ L → ∀ l ∈ L, ⁅l, x⁆ ∈ oddCoreOf L := fun x hx _ l hl =>
      (hS₁.pair.le_centralizerSection hL hLn hx).2.2 l hl
    have heq := bcdMirror_eq_of_central hLn hS₁.pair.isPGroup hcent hwZs hvZs hwL hvL hw1 hv1
    show w ∈ centralizer ({q} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * q = (q * w * q⁻¹) * q := by rw [← heq]
      _ = q * w := by group
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.1 (hZs hw)

private theorem bcdMirror_isSec5Inv (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {u : X} (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u) {g : X} {Zs : Subgroup X}
    (hZsg : Zs = Z.map (MulAut.conj g).toMonoidHom)
    (hZs : IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Zs)
    (huN : u ∈ normalizer (Zs : Set X)) : IsSec5Inv X Zs u := by
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have huC : u ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hus
  have hnot : u ∉ Zs := by
    intro huZs
    have hzs : u ∈ zStar (K0 X n (centralizer ({s} : Set X))) := hZs.1 huZs
    obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
    have hBK : B ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup hB
    have hBK' : IsPCompIn 2 (K0 X n (centralizer ({s} : Set X))) B :=
      ⟨hBK, isPComponent_subgroupOf_mono hBK (K0_le n _) hB.isPCompIn.2⟩
    have huK : u ∈ normalizer ((K0 X n (centralizer ({s} : Set X)) : Subgroup X) : Set X) :=
      mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer huC))
    have hsc : u ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
      normalizes_isPCompIn_of_comm_mem (D := K0 X n (centralizer ({s} : Set X))) hBK' huK
        (fun b hb => hzs.2.2.2 b (hBK hb))
    exact K0_ne_bot_of_centralizerSection (by rw [sq]; exact hu2) hB hsc
      (sec5_K0_inf_eq_bot h hs huZ hu1 hus)
  refine ⟨huN, hnot, hu2, g⁻¹, ?_, ?_⟩
  · rw [hZsg]
    exact ⟨u, huZ, by simp [MulAut.conj_apply]⟩
  · intro h1
    apply hu1
    have h2 : g * u * g⁻¹ = 1 := by simpa using h1
    have h3 : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [h3, h2]
    group

private theorem bcdMirror_exists_cover {s : X} {Zs : Subgroup X}
    {S₁ : Sylow 2 ↥(normalizer (Zs : Set X))} (hS₁ : Sec5Data X n s Zs S₁) {A' : Subgroup X}
    (hA' : Sec5Comp X n (normalizer (Zs : Set X)) A') :
    ∃ B : Subgroup X, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      A' = oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) := by
  obtain ⟨⟨w, hw⟩, hAn⟩ := hA'
  have hAN : IsPCompIn 2 (normalizer (Zs : Set X)) A' := hw.2.2.1
  have hZN : Zs ≤ normalizer (Zs : Set X) := Subgroup.le_normalizer
  have hAC : A' ≤ centralizer (Zs : Set X) :=
    le_centralizer_of_isPCompIn_of_normal_pgroup hAN hZN le_rfl hS₁.pair.isPGroup
  have hCs : centralizer (Zs : Set X) ≤ centralizer ({s} : Set X) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hS₁.pair.mem)
  have hAH : A' ≤ normalizer (Zs : Set X) ⊓ centralizer ({s} : Set X) :=
    le_inf hAN.1 (hAC.trans hCs)
  have hw' : IsIntrinsicIn X (normalizer (Zs : Set X) ⊓ centralizer ({s} : Set X)) A' w :=
    ⟨hw.1, hw.2.1, ⟨hAH, isPComponent_subgroupOf_mono hAH inf_le_left hAN.2⟩, hw.2.2.2⟩
  obtain ⟨B, hB, hBn, hEB⟩ := exists_isIntrinsicIn_centralizer hS₁.hypA hS₁.maxdeg (s := s)
    hS₁.pair.orderOf_z inf_le_right hw' hAn
  have hBc : Sec5Comp X n (centralizer ({s} : Set X)) B := ⟨⟨w, hB⟩, hBn⟩
  obtain ⟨hEc, -, -⟩ := exists_mirror_comp hS₁ hBc
  refine ⟨B, hBc, ?_⟩
  obtain ⟨hE'A', -, hE'q⟩ := hw.cover_oTwoPrimeOf
  have hE'le : oTwoPrimeOf (A' ⊓ centralizer ({w} : Set X)) ≤
      oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) := by
    have hself := oTwoPrimeOf_eq_self_of_primeResidual
      (primeResidual_oTwoPrimeOf (A' ⊓ centralizer ({w} : Set X)))
    have hle : oTwoPrimeOf (A' ⊓ centralizer ({w} : Set X)) ≤ B ⊓ centralizer (Zs : Set X) :=
      le_inf hEB (hE'A'.trans hAC)
    have := oTwoPrimeOf_mono hle
    rwa [hself] at this
  exact eq_of_isPCompIn_of_le hAN hEc.isPCompIn hE'A' hE'le hE'q

private theorem bcdMirror_normalizes_E {Zs B : Subgroup X} {u : X}
    (huN : u ∈ normalizer (Zs : Set X)) (huB : u ∈ normalizer (B : Set X)) :
    u ∈ normalizer (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) : Set X) := by
  have hCZ : u ∈ normalizer ((centralizer (Zs : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y : X, y ∈ normalizer (Zs : Set X) → ∀ x : X, x ∈ centralizer (Zs : Set X) →
        y * x * y⁻¹ ∈ centralizer (Zs : Set X) := by
      intro y hy x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : y⁻¹ * z * y ∈ Zs := by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Zs : Set X)).inv_mem hy) z).1 hz
        simpa using this
      have hxc := Subgroup.mem_centralizer_iff.1 hx (y⁻¹ * z * y) hz'
      calc z * (y * x * y⁻¹) = y * ((y⁻¹ * z * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [hxc]
        _ = y * x * y⁻¹ * z := by group
    refine ⟨fun hx => key u huN x hx, fun hx => ?_⟩
    have := key u⁻¹ ((normalizer (Zs : Set X)).inv_mem huN) _ hx
    simpa [mul_assoc] using this
  exact oTwoPrimeOf_normalizes (A := Subgroup.zpowers u) (H := B ⊓ centralizer (Zs : Set X))
    ((Subgroup.zpowers_le).2 (mem_normalizer_inf huB hCZ)) (Subgroup.mem_zpowers u)

theorem mirror_package (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {u : X}
    (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u) {Q : Subgroup X}
    (hQs : Q ≤ centralizer ({s} : Set X)) (hQ2 : IsPGroup 2 ↥Q) (hQ8 : Nat.card ↥Q = 8)
    (huQ : u ∈ Q) (hQpow : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q)
    (hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X))
    (hn15 : n ≤ 15) :
    ∃ (g : X) (Zs : Subgroup X) (S₁ : Sylow 2 ↥(normalizer (Zs : Set X))),
      Zs = Z.map (MulAut.conj g).toMonoidHom ∧ Q ≤ normalizer (Zs : Set X) ∧
      Q ≤ centralizer (Zs : Set X) ∧ Sec5Data X n s Zs S₁ ∧ IsSec5Inv X Zs u ∧
      (∀ A', Sec5Comp X n (normalizer (Zs : Set X)) A' → u ∈ normalizer (A' : Set X)) ∧
      (∀ A', Sec5Comp X n (normalizer (Zs : Set X)) A' → ∀ hu : u ∈ normalizer (A' : Set X),
        ∀ M' : AhatModel X n A', M'.perm u hu ≠ 1 ∧ fixCount (M'.perm u hu) = n - 8 ∧
          transCount (M'.perm u hu) = 4) := by
  have hn : 8 ≤ n := h.maxdeg.1
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  obtain ⟨g, Zs, S₁, hZsg, hZs, hQN, hS₁⟩ := exists_mirror_of_Q h hs hQ2 hQs
  have huN : u ∈ normalizer (Zs : Set X) := hQN huQ
  refine ⟨g, Zs, S₁, hZsg, hQN, bcdMirror_le_centralizer hS₁ hQN hQn, hS₁,
    bcdMirror_isSec5Inv h hs huZ hu1 hus hZsg hZs huN, ?_, ?_⟩
  · intro A' hA'
    obtain ⟨B, hB, rfl⟩ := bcdMirror_exists_cover hS₁ hA'
    exact bcdMirror_normalizes_E huN (hQn B hB huQ)
  · intro A' hA' hu M'
    obtain ⟨B, hB, rfl⟩ := bcdMirror_exists_cover hS₁ hA'
    obtain ⟨-, hEB, hcov⟩ := exists_mirror_comp hS₁ hB
    have hQB : Q ≤ normalizer (B : Set X) := hQn B hB
    set MB : AhatModel X n B := AhatModel.ofCover hB.2 with hMB
    set τ : Perm (Fin n) := MB.perm u (hQB huQ) with hτ
    have hperm : (MB.transport hEB hcov).perm u hu = τ :=
      MB.perm_transport hn hEB hcov hu (hQB huQ)
    obtain ⟨c, hc⟩ := AhatModel.exists_perm_conj hn (MB.transport hEB hcov) M' hu
    have hτ1 : τ ≠ 1 := perm_ne_one_of_mem_Z h hs huZ hu1 hus hB (hQB huQ) MB
    obtain ⟨W, hW8, -, hWτ, hWc, -⟩ := q8_perm_data hn MB hQB hQ8 huQ hQpow hu2 hτ1
    have hsupp : τ.support.card = 8 := q8_support_card_eq (by omega) hτ1 hW8 hWτ hWc
    have hfix : fixCount τ = n - 8 := by
      have := fixCount_add_support τ
      omega
    have htrans : transCount τ = 4 := by
      unfold transCount
      rw [hsupp]
    rw [hc, hperm]
    refine ⟨fun h1 => hτ1 (conj_eq_one_iff.1 h1), ?_, ?_⟩
    · rw [fixCount_conj, hfix]
    · rw [transCount_conj, htrans]

end Mirror

end CFSG.OddStandard.Solomon75

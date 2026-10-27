module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Cent
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Basic

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem K0_ne_bot_of_centralizerSection {H B : Subgroup X} {w : X} (hw2 : w ^ 2 = 1)
    (hB : Sec5Comp X n H B) (hsc : w ∈ centralizerSection B (pPrimeCoreOf 2 B)) :
    K0 X n (K0 X n H ⊓ centralizer ({w} : Set X)) ≠ ⊥ := by
  obtain ⟨⟨u, hu⟩, hBn⟩ := hB
  obtain ⟨u', hu', hu'c⟩ := hu.exists_witness_centralizer_singleton hw2 hsc
  obtain ⟨hd1, hd2, -⟩ := hu'.descend_singleton hBn hw2 hsc hu'c
  set E : Subgroup X := oTwoPrimeOf (B ⊓ centralizer ({w} : Set X)) with hE
  have hEC : E ≤ H ⊓ centralizer ({w} : Set X) := hd1.2.2.1.1
  have hEB : E ≤ B := (oTwoPrimeOf_le _).trans inf_le_left
  have hEK : E ≤ K0 X n H := hEB.trans (le_sSup ⟨⟨u, hu⟩, hBn⟩)
  have hle : E ≤ K0 X n H ⊓ centralizer ({w} : Set X) := le_inf hEK (hEC.trans inf_le_right)
  have hI : IsIntrinsicIn X (K0 X n H ⊓ centralizer ({w} : Set X)) E u' :=
    ⟨hd1.1, hd1.2.1, ⟨hle, isPComponent_subgroupOf_mono hle
      (inf_le_inf_right _ (K0_le n H)) hd1.2.2.1.2⟩, hd1.2.2.2⟩
  have hEK0 : E ≤ K0 X n (K0 X n H ⊓ centralizer ({w} : Set X)) := le_sSup ⟨⟨u', hI⟩, hd2⟩
  intro hbot
  rw [hbot] at hEK0
  exact ne_bot_of_isDoubleCoverOfAlt hd2 (le_bot_iff.1 hEK0)

theorem comm_of_mem_Z_of_norm (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) {w : X} (hwZ : w ∈ Z) (hwA : w ∈ A) (hw1 : w ≠ 1) :
    w * s = s * w := by
  set N : Subgroup X := normalizer (Z : Set X) with hN
  have hAD : A ≤ K0 X n N := le_sSup hA
  let C := AhatData.CoverSetup.ofCover hA.2
  have hvZ : s * w * s⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hs.mem w).1 hwZ
  have hvA : s * w * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hsA w).1 hwA
  have hv1 : s * w * s⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have := congrArg (fun t => s⁻¹ * t * s) h1
    simpa [mul_assoc] using this
  have hcen : ∀ u : X, u ∈ Z → ∀ hu : u ∈ A,
      (QuotientGroup.mk (⟨u, hu⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈
        Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A) := fun u huZ hu =>
    mk_mem_center_of_comm hu fun a ha => (h.Z_le_center_K0 huZ (hAD ha)).symm
  have hne : ∀ u : X, u ∈ Z → ∀ hu : u ∈ A, u ≠ 1 →
      (QuotientGroup.mk (⟨u, hu⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ≠ 1 := by
    intro u huZ hu hu1 h1
    have h2 : u ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hu, (QuotientGroup.eq_one_iff _).1 h1⟩
    exact hu1 (eq_one_of_mem_of_mem_odd (oddCoreOf A) Z (odd_card_oddCoreOf A) h.isPGroup_Z huZ h2)
  have heq := C.center_eq_of_ne_one (hcen w hwZ hwA) (hcen _ hvZ hvA) (hne w hwZ hwA hw1)
    (hne _ hvZ hvA hv1)
  have h3 : (⟨w, hwA⟩ : ↥A)⁻¹ * ⟨s * w * s⁻¹, hvA⟩ ∈ pPrimeCore 2 ↥A := QuotientGroup.eq.1 heq
  have h4 : w⁻¹ * (s * w * s⁻¹) ∈ oddCoreOf A := ⟨_, h3, rfl⟩
  have h5 : w⁻¹ * (s * w * s⁻¹) ∈ Z := Z.mul_mem (Z.inv_mem hwZ) hvZ
  have h6 := eq_one_of_mem_of_mem_odd (oddCoreOf A) Z (odd_card_oddCoreOf A) h.isPGroup_Z h5 h4
  have h7 : s * w * s⁻¹ = w := by
    have := congrArg (fun t => w * t) h6
    simpa using this
  have : s * w = w * s := by
    have := congrArg (fun t => t * s) h7
    simpa [mul_assoc] using this
  exact this.symm

theorem exists_mirror_comp {s : X} {Zs : Subgroup X} {S₁ : Sylow 2 ↥(normalizer (Zs : Set X))}
    (hS₁ : Sec5Data X n s Zs S₁) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) :
    Sec5Comp X n (normalizer (Zs : Set X)) (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X))) ∧
      oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) ≤ B ∧
      ∀ c ∈ B, ∃ a ∈ oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)), ∃ o ∈ oddCoreOf B,
        c = a * o := by
  have hB' := hB
  obtain ⟨⟨u₀, hu₀⟩, hBn⟩ := hB'
  obtain ⟨u, huZs, hu⟩ := hS₁.pair.exists_witness_mem hu₀ hBn
  obtain ⟨h1, h2, h3⟩ := hS₁.pair.isIntrinsicIn_normalizer huZs hu hBn
  have hEB : oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) ≤ B :=
    (oTwoPrimeOf_le _).trans inf_le_left
  refine ⟨⟨⟨u, h1⟩, h2⟩, hEB, ?_⟩
  intro c hc
  have hc' : c ∈ pPrimeCoreOf 2 B ⊔ oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) := h3 hc
  obtain ⟨o, ho, a, ha, hoa⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
    (pPrimeCoreOf 2 B) (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)))
    (fun x hx => le_normalizer_oddCoreOf B (hEB hx)) c).1 hc'
  refine ⟨a, ha, a⁻¹ * o * a, ?_, ?_⟩
  · have hn1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf B (hEB (inv_mem ha))) o)
    have := hn1.1 ho
    simpa [mul_assoc] using this
  · rw [← hoa]; group

theorem normalizes_comps_of_mem_Z (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂)
    {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {w : X} (hwZ : w ∈ Z) (hwA : w ∈ A)
    (hw1 : w ≠ 1) :
    ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → w ∈ normalizer (B : Set X) := by
  classical
  intro B hB
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  have hsA : s ∈ normalizer (A : Set X) := mem_normalizer_of_map_conj_eq (hN X n z Z S h s hs A hA)
  have hws : w * s = s * w := comm_of_mem_Z_of_norm h hs hA hsA hwZ hwA hw1
  have ha' := sec5_a_prime hF hN h hk hs hA hwA hw1 hw2 hws
  have hwC : w ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hws
  have hBK : B ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup hB
  obtain ⟨Zs, hZs, hwZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers w) (isPGroup_zpowers_of_mul_self hw2)
    (Subgroup.zpowers_le.2 hwC)
  have hwn : w ∈ normalizer (Zs : Set X) := hwZs (Subgroup.mem_zpowers w)
  obtain ⟨g, S₁, hZsg, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs
  have hwnZs : w ∉ Zs := by
    intro hwZs'
    have hzs : w ∈ zStar (K0 X n (centralizer ({s} : Set X))) := hZs.1 hwZs'
    have hBK' : IsPCompIn 2 (K0 X n (centralizer ({s} : Set X))) B :=
      ⟨hBK, isPComponent_subgroupOf_mono hBK (K0_le n _) hB.isPCompIn.2⟩
    have hwK : w ∈ normalizer ((K0 X n (centralizer ({s} : Set X)) : Subgroup X) : Set X) :=
      mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hwC))
    have hsc : w ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
      normalizes_isPCompIn_of_comm_mem (D := K0 X n (centralizer ({s} : Set X))) hBK' hwK
        (fun b hb => hzs.2.2.2 b (hBK hb))
    exact K0_ne_bot_of_centralizerSection (by rw [sq]; exact hw2) hB hsc ha'
  have hconj : ∃ g' : X, g'⁻¹ * w * g' ∈ Zs ∧ g'⁻¹ * w * g' ≠ 1 := by
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hZsg]
      exact ⟨w, hwZ, by simp [MulAut.conj_apply]⟩
    · intro h1
      apply hw1
      have h2 : g * w * g⁻¹ = 1 := by simpa using h1
      have h3 : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [h3, h2]; group
  have hinv : IsSec5Inv X Zs w := ⟨hwn, hwnZs, hw2, hconj⟩
  obtain ⟨hEc, hEB, hcov⟩ := exists_mirror_comp hS₁ hB
  set E : Subgroup X := oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) with hE
  have hwE : w ∈ normalizer (E : Set X) :=
    mem_normalizer_of_map_conj_eq (hN X n s Zs S₁ hS₁ w hinv _ hEc)
  have hEN : E ≤ normalizer (Zs : Set X) := hEc.isPCompIn.1
  have hEq : IsTwoGenQuasi ↥E :=
    (isTwoGenQuasi_subgroupOf_iff hEN).1 (isPComponent_two_iff.1 hEc.isPCompIn.2).2
  have hB' : Sec5Comp X n (centralizer ({s} : Set X)) (B.map (MulAut.conj w).toMonoidHom) :=
    hB.map_conj (Subgroup.le_normalizer hwC)
  have hEB' : E ≤ B.map (MulAut.conj w).toMonoidHom := by
    intro e he
    have h1 : w⁻¹ * e * w ∈ E := by
      have := (mem_normalizer_iff.1 ((normalizer (E : Set X)).inv_mem hwE) e).1 he
      simpa using this
    exact ⟨w⁻¹ * e * w, hEB h1, by simp [MulAut.conj_apply, mul_assoc]⟩
  exact mem_normalizer_of_map_conj_eq
    (eq_of_isPCompIn_of_le hB'.isPCompIn hB.isPCompIn hEB' hEB hEq)

theorem le_LPlusIn_of_isPCompIn_inf {s r : X} (hs2 : s ^ 2 = 1) (hsr : s * r = r * s)
    {Δ : Subgroup X}
    (hΔ : IsPCompIn 2 (centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X)) Δ) :
    Δ ≤ LPlusIn (centralizer ({r} : Set X)) := by
  set D : Subgroup X := centralizer ({r} : Set X) with hD
  set Cu : Subgroup X := centralizer ({s} : Set X) with hCu
  have hΔCu : Δ ≤ Cu := hΔ.1.trans inf_le_left
  have hΔD : Δ ≤ D := hΔ.1.trans inf_le_right
  have huD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2 hsr
  set uD : ↥D := ⟨s, huD⟩ with huDdef
  have hcen : centralizer ({uD} : Set ↥D) = Cu.subgroupOf D := centralizer_singleton_subgroup huD
  have hEC_D : Δ.subgroupOf D ≤ centralizer ({uD} : Set ↥D) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono D hΔCu
  have hE_D : IsPComponent 2 ((Δ.subgroupOf D).subgroupOf (centralizer ({uD} : Set ↥D))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hΔCu hΔD).2 hΔ.2
  have hu2 : uD ^ 2 = 1 := by
    apply Subtype.ext
    exact hs2
  have hB : IsPGroup 2 (Subgroup.zpowers uD) := aux_isPGroup_zpowers_of_sq hu2
  have hbal := layer_balance (Subgroup.zpowers uD) hB
  have hcz : centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) =
      centralizer ({uD} : Set ↥D) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hEC_D' : Δ.subgroupOf D ≤ centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) := by
    rw [hcz]
    exact hEC_D
  have hE_D' : IsPComponent 2 ((Δ.subgroupOf D).subgroupOf
      (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D))) := by
    rw [hcz]
    exact hE_D
  have h1 := le_sSup (s := {L | IsPComponent 2 L}) hE_D'
  have h2 := Subgroup.map_mono (f := (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) :
    Set ↥D)).subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hEC_D'] at h2
  have hEL : Δ.subgroupOf D ≤ pLayer ↥D 2 := h2.trans hbal
  intro m hm
  refine ⟨⟨m, hΔD hm⟩, ?_, rfl⟩
  rw [LPlus_eq_pLayer_sup_NPlus]
  exact Subgroup.mem_sup_left (hEL (Subgroup.mem_subgroupOf.2 hm))

theorem Z_le_centralizer_of_noSwap (hN : Solomon75NoSwap) (h : Sec5Data X n z Z S) {s : X}
    (hs : IsSec5Inv X Z s) : Z ≤ centralizer ({s} : Set X) := by
  refine h.pair.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨huZ, L, hL, hLn⟩
  obtain ⟨h1, h2, -⟩ := h.pair.isIntrinsicIn_normalizer huZ hL hLn
  have hE : Sec5Comp X n (normalizer (Z : Set X)) (oTwoPrimeOf (L ⊓ centralizer (Z : Set X))) :=
    ⟨⟨u, h1⟩, h2⟩
  have hsE := mem_normalizer_of_map_conj_eq (hN X n z Z S h s hs _ hE)
  have hu1 : u ≠ 1 := by
    intro hu
    have := h1.1
    rw [hu, orderOf_one] at this
    omega
  exact Subgroup.mem_centralizer_singleton_iff.2
    (comm_of_mem_Z_of_norm h hs hE hsE huZ h1.2.1 hu1)

omit [Finite X] in
theorem map_conj_subgroupOf {C₀ : Subgroup X} {r : X} (hr : r ∈ C₀) (A : Subgroup X) :
    (A.subgroupOf C₀).map (MulAut.conj (⟨r, hr⟩ : ↥C₀)).toMonoidHom =
      (A.map (MulAut.conj r).toMonoidHom).subgroupOf C₀ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : X), hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨a, ha, hax⟩
    have hxC : (x : X) ∈ C₀ := x.2
    have haC : a ∈ C₀ := by
      have hax' : r * a * r⁻¹ = (x : X) := by simpa [MulAut.conj_apply] using hax
      have : a = r⁻¹ * (x : X) * r := by rw [← hax']; group
      rw [this]
      exact C₀.mul_mem (C₀.mul_mem (C₀.inv_mem hr) hxC) hr
    refine ⟨⟨a, haC⟩, ha, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hax

theorem normalizes_comps_of_swap_diag (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂)
    {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {r : X} (hrA : r ∈ A) (hr1 : r ≠ 1)
    (hr2 : r * r = 1) (hrs : r * s = s * r) :
    ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → r ∈ normalizer (B : Set X) := by
  classical
  intro B hB
  by_contra hrB
  set Cs : Subgroup X := centralizer ({s} : Set X) with hCs
  have hs2 : s ^ 2 = 1 := by rw [sq]; exact hs.sq
  have hr2' : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hr2o : orderOf r = 2 := orderOf_eq_prime hr2' hr1
  have hsA : s ∈ normalizer (A : Set X) := mem_normalizer_of_map_conj_eq (hN X n z Z S h s hs A hA)
  have hrN : r ∈ normalizer (Z : Set X) := hA.isPCompIn.1 hrA
  have hrK0 : r ∈ K0 X n (normalizer (Z : Set X)) :=
    (le_sSup hA : A ≤ K0 X n (normalizer (Z : Set X))) hrA
  have hrC : r ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hrs
  obtain ⟨w, hwZ, hwA, hw1⟩ := h.exists_mem_Z_inf hA
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  have hw2' : w ^ 2 = 1 := by rw [sq]; exact hw2
  have hws : w * s = s * w := comm_of_mem_Z_of_norm h hs hA hsA hwZ hwA hw1
  have hwr : w * r = r * w := h.Z_le_center_K0 hwZ hrK0
  have hwC : w ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hws
  have hwB : w ∈ normalizer (B : Set X) :=
    normalizes_comps_of_mem_Z hF hN h hk hs hA hwZ hwA hw1 B hB
  have ha' := sec5_a_prime hF hN h hk hs hA hwA hw1 hw2 hws
  have hB' : Sec5Comp X n Cs (B.map (MulAut.conj r).toMonoidHom) :=
    hB.map_conj (Subgroup.le_normalizer hrC)
  have hBCs : B ≤ Cs := hB.isPCompIn.1
  have hB'Cs : B.map (MulAut.conj r).toMonoidHom ≤ Cs := hB'.isPCompIn.1
  have hBc : IsPComponent 2 (B.subgroupOf Cs) := hB.isPCompIn.2
  have hZB : IsPGroup 2 ↥(center (↥(B.subgroupOf Cs) ⧸ pPrimeCore 2 ↥(B.subgroupOf Cs))) := by
    have hc : Nat.card (center (↥B ⧸ pPrimeCore 2 ↥B)) = 2 := hB.2.2.1
    have h0 : IsPGroup 2 ↥(center (↥B ⧸ pPrimeCore 2 ↥B)) :=
      IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hBCs)
    exact h0.of_equiv (centerCongr f).symm
  set trc : ↥Cs := ⟨r, hrC⟩ with htrc
  set twc : ↥Cs := ⟨w, hwC⟩ with htwc
  have htr : trc * trc = 1 := Subtype.ext hr2
  have hcomm : twc * trc = trc * twc := Subtype.ext hwr
  have hne : (B.subgroupOf Cs).map (MulAut.conj trc).toMonoidHom ≠ B.subgroupOf Cs := by
    rw [map_conj_subgroupOf hrC B]
    intro heq
    apply hrB
    have : B.map (MulAut.conj r).toMonoidHom = B := by
      have h1 := heq
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hB'Cs, inf_of_le_left hBCs] at h1
      exact h1
    exact mem_normalizer_of_map_conj_eq this
  have htw : ∀ b ∈ B.subgroupOf Cs, twc * b * twc⁻¹ ∈ B.subgroupOf Cs := by
    intro b hb
    exact (Subgroup.mem_normalizer_iff.1 hwB (b : X)).1 hb
  obtain ⟨Δ, hΔC, hΔpc, hΔn, hkey⟩ := exists_diag_lift hBc hZB htr hcomm hne htw
  set ΔX : Subgroup X := Δ.map Cs.subtype with hΔX
  have hΔXs : ΔX ≤ Cs := Subgroup.map_subtype_le Δ
  have hΔXr : ΔX ≤ centralizer ({r} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔC hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({trc} : Set ↥Cs)).map Cs.subtype =
      Cs ⊓ centralizer ({r} : Set X) := by
    rw [centralizer_singleton_subgroup hrC, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔXpc : IsPCompIn 2 (Cs ⊓ centralizer ({r} : Set X)) ΔX := by
    refine ⟨le_inf hΔXs hΔXr, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 Cs.subtype Cs.subtype_injective hΔC).2 hΔpc
    rwa [hcenmap] at h1
  have hΔL : ΔX ≤ LPlusIn (centralizer ({r} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hs2 hrs.symm hΔXpc
  have hJ0 : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥ := by
    obtain ⟨Aj, hAj, hne'⟩ : ∃ Aj : Subgroup X,
        Sec5Comp X n (normalizer (Z : Set X)) Aj ∧ Aj ≠ A := by
      obtain ⟨A₁, A₂, h₁, h₂, h12⟩ := hk
      by_cases h1A : A₁ = A
      · exact ⟨A₂, h₂, fun h => h12 (h1A.trans h.symm)⟩
      · exact ⟨A₁, h₁, h1A⟩
    have hrN' : r ∈ normalizer ((normalizer (Z : Set X) : Subgroup X) : Set X) :=
      Subgroup.le_normalizer (hA.isPCompIn.1 hrA)
    have hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj) :=
      normalizes_isPCompIn_of_comm_mem hAj.isPCompIn hrN' (fun l hl =>
        commutator_mem_oddCoreOf_of_ne hAj.isPCompIn hA.isPCompIn hne' hl hrA)
    exact K0_ne_bot_of_centralizerSection hr2' hAj hscj
  have hL34 := h.l52.c r hrN hr2o hJ0
  set OO : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) with hOO
  set W₂ : Subgroup X := Z ⊓ centralizer ({r} : Set X) with hW₂
  have hZs : Z ≤ Cs := Z_le_centralizer_of_noSwap hN h hs
  have hCn : centralizer ({r} : Set X) ≤ normalizer (OO : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hOOodd : Odd (Nat.card OO) := odd_card_oddCoreOf _
  have hW₂p : IsPGroup 2 ↥W₂ := h.isPGroup_Z.to_le inf_le_left
  set OOc : Subgroup ↥Cs := OO.comap Cs.subtype with hOOc
  set W₂c : Subgroup ↥Cs := W₂.comap Cs.subtype with hW₂c
  have hOOcodd : Odd (Nat.card OOc) := by
    refine Odd.of_dvd_nat hOOodd (Subgroup.card_dvd_of_injective
      (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : OOc →* ↥OO) ?_)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥OO => (t : X)) hab))
  have hW₂cp : IsPGroup 2 ↥W₂c := by
    refine hW₂p.of_injective (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : W₂c →* ↥W₂) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥W₂ => (t : X)) hab))
  have hconjOO : ∀ y : ↥Cs, (y : X) ∈ centralizer ({r} : Set X) →
      y ∈ normalizer (OOc : Set ↥Cs) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro t
    exact mem_normalizer_iff.1 (hCn hy) (t : X)
  have hΔOO : Δ ≤ normalizer (OOc : Set ↥Cs) := fun x hx =>
    hconjOO x (hΔXr ⟨x, hx, rfl⟩)
  have hW₂OO : W₂c ≤ normalizer (OOc : Set ↥Cs) := fun x hx => hconjOO x hx.2
  have hV : ∀ x ∈ Δ, ⁅x, twc⁆ ∈ OOc ⊔ W₂c := by
    intro x hx
    have hxX : (x : X) ∈ LPlusIn (centralizer ({r} : Set X)) := hΔL ⟨x, hx, rfl⟩
    obtain ⟨o, ho, w', hw', hxw⟩ := commutator_decomp_of_mirror hwZ hwr.symm hL34 hxX
    have hw'C : w' ∈ Cs := hZs hw'.1
    have hcx : (((⁅x, twc⁆ : ↥Cs)) : X) = ⁅(x : X), w⁆ := by
      simp [commutatorElement_def, htwc]
    have hoC : o ∈ Cs := by
      have : o = (((⁅x, twc⁆ : ↥Cs)) : X) * w'⁻¹ := by rw [hcx, hxw]; group
      rw [this]
      exact Cs.mul_mem (⁅x, twc⁆ : ↥Cs).2 (Cs.inv_mem hw'C)
    have hprod : ⁅x, twc⁆ = (⟨o, hoC⟩ : ↥Cs) * ⟨w', hw'C⟩ :=
      Subtype.ext (by rw [hcx, hxw]; rfl)
    rw [hprod]
    exact Subgroup.mul_mem_sup (show (⟨o, hoC⟩ : ↥Cs) ∈ OOc from ho)
      (show (⟨w', hw'C⟩ : ↥Cs) ∈ W₂c from hw')
  have hcommAll := hkey OOc W₂c hOOcodd hΔOO hW₂cp hW₂OO hV
  have hsc : w ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
    refine ⟨hwB, mem_normalizer_oddCoreOf_of_mem_normalizer hwB, fun b hb => ?_⟩
    have h1 := hcommAll ⟨b, hBCs hb⟩ hb
    have h2 : ⁅b, w⁆ ∈ oddCoreOf Cs :=
      ⟨_, h1, by simp [commutatorElement_def, htwc]⟩
    have h3 : ⁅b, w⁆ ∈ B := by
      have e : ⁅b, w⁆ = b * (w * b⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hwB b⁻¹).1 (B.inv_mem hb))
    exact inf_oddCoreOf_le hBCs ⟨h3, h2⟩
  exact K0_ne_bot_of_centralizerSection hw2' hB hsc ha'

theorem lemma54pNorm (hF : Solomon75Frac53) (hN : Solomon75NoSwap) : Solomon75Lemma54pNorm := by
  intro X _ _ n z Z S h hk s hs A hA r hrA hr1 hr2 hrs B hB
  exact normalizes_comps_of_swap_diag hF hN h hk hs hA hrA hr1 hr2 hrs B hB

end Basic

end CFSG.OddStandard.Solomon75

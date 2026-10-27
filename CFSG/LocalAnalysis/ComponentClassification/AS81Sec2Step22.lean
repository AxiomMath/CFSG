module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step24

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec2

omit [Finite G] in
theorem exists_not_mem_conj_mem {P C : Subgroup G} (hne : ¬ P ≤ C)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ C) (hsq : ∀ a ∈ P, a * a ∈ C) {n : G}
    (hnP : n ∈ normalizer (P : Set G))
    (hn2 : ∀ p ∈ P, p⁻¹ * (n * n * p * (n * n)⁻¹) ∈ C) :
    ∃ h ∈ P, h ∉ C ∧ h⁻¹ * (n * h * n⁻¹) ∈ C := by
  obtain ⟨h₁, hh₁, hh₁C⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hh₂ : n * h₁ * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnP h₁).mp hh₁
  by_cases H : h₁⁻¹ * (n * h₁ * n⁻¹) ∈ C
  · exact ⟨h₁, hh₁, hh₁C, H⟩
  refine ⟨h₁ * (n * h₁ * n⁻¹), P.mul_mem hh₁ hh₂, fun h => H ?_, ?_⟩
  · have := C.mul_mem (C.inv_mem (hsq h₁ hh₁)) h
    simpa [mul_assoc] using this
  · have h1 := hn2 h₁ hh₁
    have h2 := hPab _ (P.inv_mem hh₂) _ (P.inv_mem hh₁)
    have heq : (h₁ * (n * h₁ * n⁻¹))⁻¹ * (n * (h₁ * (n * h₁ * n⁻¹)) * n⁻¹) =
        ((n * h₁ * n⁻¹)⁻¹ * h₁⁻¹ * (n * h₁ * n⁻¹)⁻¹⁻¹ * h₁⁻¹⁻¹) *
          (h₁⁻¹ * (n * n * h₁ * (n * n)⁻¹)) := by group
    rw [heq]
    exact C.mul_mem h2 h1

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem sec2S_inf_sec2P
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    sec2S A R E F ⊓ sec2P E = centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCF : C ≤ normalizer (F : Set G) := (le_sup_right : C ≤ sec2S A R E F).trans hSF
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hCP)
  have hx' : x ∈ ((F ⊔ C : Subgroup G) : Set G) := hx.1
  rw [coe_mul_of_right_le_normalizer_left F C hCF] at hx'
  obtain ⟨f, hf, c, hc, rfl⟩ := hx'
  have hfP : f ∈ sec2P E := by
    have := (sec2P E).mul_mem hx.2 ((sec2P E).inv_mem (hCP hc))
    simpa using this
  have hfR : f ∈ normalizer (R : Set G) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => hFcomm r (hF.R_le_F hr) f hf)
  exact C.mul_mem (le_centralizerMod hF (hPR.le ⟨hfP, hfR⟩)) hc

theorem sec2P_sup_sec2S_inf_normalizer
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    (sec2P E ⊔ sec2S A R E F) ⊓ normalizer (F : Set G) = sec2S A R E F := by
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hSE : sec2S A R E F ≤ normalizer (E : Set G) :=
    sup_le (hF.F_le_normalizer hL hodd) (fun c hc => Sec2.sec2P_le E (mem_centralizerMod.mp hc).1)
  have hSN : sec2S A R E F ≤ normalizer (sec2P E : Set G) :=
    hSE.trans (Sec2.normalizer_le_normalizer_sec2P E)
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hSF)
  have hx' : x ∈ ((sec2P E ⊔ sec2S A R E F : Subgroup G) : Set G) := hx.1
  rw [coe_mul_of_right_le_normalizer_left _ _ hSN] at hx'
  obtain ⟨p, hp, s, hs, rfl⟩ := hx'
  have hpF : p ∈ normalizer (F : Set G) := by
    have := (normalizer (F : Set G)).mul_mem hx.2 ((normalizer (F : Set G)).inv_mem (hSF hs))
    simpa using this
  have hpEF : p ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨Sec2.sec2P_le E hp, hpF⟩
  have hle : rightConjugate R p ≤ E ⊓ F := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hREF p
    rwa [(rightConjugate_eq_self_iff _ _).mpr hpEF] at h
  have hpC := mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hp hle
  exact mul_mem ((le_sup_right : _ ≤ sec2S A R E F) hpC) hs

theorem card_conjSet_sec2P
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : Nat.card (conjSet F (sec2P E)) = 4 := by
  have hPN := sec2P_sup_sec2S_inf_normalizer h11 hE16 hF hL hodd
  have hSP := sec2S_inf_sec2P h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hPq := isElemQuot_sec2P h11 hE16 hF hL hodd
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hPF : sec2P E ⊓ normalizer (F : Set G) = C := by
    refine le_antisymm (fun p hp => ?_) (le_inf hCP ((le_sup_right : C ≤ sec2S A R E F).trans hSF))
    have h1 : p ∈ (sec2P E ⊔ sec2S A R E F) ⊓ normalizer (F : Set G) := ⟨mem_sup_left hp.1, hp.2⟩
    rw [hPN] at h1
    rw [← hSP]
    exact ⟨h1, hp.1⟩
  have hCidx' : C.relIndex (sec2P E) = 4 := by
    have h := relIndex_mul_relIndex E C (sec2P E) hEC hCP
    rw [hCidx, hPq.2.1] at h
    omega
  let _ : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)
  let _ : MulAction ↥(sec2P E) (Subgroup G) := MulAction.compHom (Subgroup G) (sec2P E).subtype
  have hsmul : ∀ p : ↥(sec2P E), p • F = rightConjugate F (p : G)⁻¹ := fun p => by
    rw [rightConjugate, inv_inv]
    rfl
  have horbit : MulAction.orbit ↥(sec2P E) F = conjSet F (sec2P E) := by
    ext V
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : G)⁻¹, (sec2P E).inv_mem p.2, hsmul p⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q⁻¹, (sec2P E).inv_mem hq⟩, ?_⟩
      rw [hsmul]
      simp
  have hstab : MulAction.stabilizer ↥(sec2P E) F =
      (normalizer (F : Set G)).subgroupOf (sec2P E) := by
    ext p
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, hsmul, rightConjugate_eq_self_iff]
    exact ⟨fun h => by simpa using inv_mem h, inv_mem⟩
  rw [← horbit, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥(sec2P E) F),
    ← (MulAction.stabilizer ↥(sec2P E) F).index_eq_card, hstab]
  change (normalizer (F : Set G)).relIndex (sec2P E) = 4
  rw [← inf_relIndex_left, hPF, hCidx']

theorem inf_eq_bot_of_not_le_inf
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {Q : Subgroup G} (hQ : Q ∈ pointsIn R E)
    (hQEF : ¬ Q ≤ E ⊓ F) : Q ⊓ (E ⊓ F) = ⊥ := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  by_contra hy1
  have hyA : y ∉ A := fun h => hy1 (by
    have : y ∈ Q ⊓ (E ⊓ A) := ⟨hy.1, hQ.1 hy.1, h⟩
    rwa [hD.inf_H Q hQ, mem_bot] at this)
  obtain ⟨Q', hQ', hQ'EF, hyQ'⟩ := exists_mem_point_le_inf h11 hE16 hF hL hodd hy.2 hyA
  have hne : Q ≠ Q' := fun h => hQEF (h ▸ hQ'EF)
  have hm : y ∈ Q ⊓ Q' := ⟨hy.1, hyQ'⟩
  rw [hD.disj Q hQ Q' hQ' hne, mem_bot] at hm
  exact hy1 hm

theorem mem_of_mem_normalizer_of_not_le'
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {m : G}
    (hmE : m ∈ normalizer (E : Set G)) (hmc : ∀ y ∈ E ⊓ F, m * y = y * m) {k : ℕ}
    (hm2 : m ^ 2 ^ k = 1) {Q : Subgroup G} (hQ : Q ∈ pointsIn R E) (hQEF : ¬ Q ≤ E ⊓ F)
    (hmQ : m ∈ normalizer (Q : Set G)) : m ∈ E := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hmEA := hD.normalizer_le_normalizer hmE
  have hbot := inf_eq_bot_of_not_le_inf h11 hE16 hF hL hodd hQ hQEF
  have hmq : ∀ q ∈ Q, q * m = m * q := by
    intro q hq
    obtain ⟨a, ha, r, hr, rfl⟩ := hD.eq_mul _ (hQ.1 hq)
    have hmr : m * r = r * m := hmc r (hREF hr)
    have h1 : m * (a * r) * m⁻¹ * (a * r)⁻¹ ∈ Q ⊓ (E ⊓ A) := by
      refine ⟨Q.mul_mem ((mem_normalizer_iff.mp hmQ _).mp hq) (Q.inv_mem hq), ?_⟩
      have hmr' : m * r * m⁻¹ = r := by rw [hmr, mul_inv_cancel_right]
      have heq : m * (a * r) * m⁻¹ * (a * r)⁻¹ = (m * a * m⁻¹) * a⁻¹ := by
        calc m * (a * r) * m⁻¹ * (a * r)⁻¹ = (m * a * m⁻¹) * (m * r * m⁻¹) * r⁻¹ * a⁻¹ := by
              group
          _ = (m * a * m⁻¹) * r * r⁻¹ * a⁻¹ := by rw [hmr']
          _ = (m * a * m⁻¹) * a⁻¹ := by group
      rw [heq]
      exact (E ⊓ A).mul_mem ((mem_normalizer_iff.mp hmEA a).mp ha) ((E ⊓ A).inv_mem ha)
    rw [hD.inf_H Q hQ, mem_bot] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨-, y, hy⟩ := hQ
    rw [hy, rightConjugate_card, hF.cardR]
  have hN : E ⊓ F ≤ normalizer (Q : Set G) := fun x hx => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun q hq => hD.comm q (hQ.1 hq) x hx.1)
  have hsup : Q ⊔ (E ⊓ F) = E := by
    refine eq_of_le_of_card_ge (sup_le hQ.1 inf_le_left) ?_
    have h := card_sup_mul_card_inf (H := Q) (R := E ⊓ F) hN
    rw [hbot, card_bot, mul_one, hQ4, hF.card_inf] at h
    rw [hF.cardE]
    omega
  have hle : E ≤ centralizer ({m} : Set G) := by
    rw [← hsup]
    exact sup_le (fun q hq => mem_centralizer_singleton_iff.mpr (hmq q hq))
      (fun y hy => mem_centralizer_singleton_iff.mpr (hmc y hy).symm)
  exact mem_of_mem_centralizer_of_frame hF hL hodd m
    (mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hle he)) k hm2

theorem exists_mem_commutator
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {h : G} (hh : h ∈ sec2P E)
    (hhC : h ∉ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) {c₀ : G}
    (hc₀ : c₀ ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) :
    ∃ f ∈ F, c₀ * (h⁻¹ * f⁻¹ * h * f) ∈ E := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCN : C ≤ normalizer (E : Set G) := hCP.trans (Sec2.sec2P_le E)
  have hFS : F ≤ sec2S A R E F := le_sup_left
  have hCS : C ≤ sec2S A R E F := le_sup_right
  have hhN := Sec2.sec2P_le E hh
  have hχC : ∀ f ∈ F, h⁻¹ * f⁻¹ * h * f ∈ C := fun f hf => by
    have := C.inv_mem (mem_centralizerMod_of_mem_sec2P h11 hE16 hF hL hodd
      ((sec2P E).inv_mem hh) hf)
    simpa [mul_assoc] using this
  have hEn : (E.subgroupOf C).Normal := ⟨fun x hx c => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hCN c.2) _).mp hx⟩
  have hq : ∀ x y : ↥C, (QuotientGroup.mk x : ↥C ⧸ E.subgroupOf C) = QuotientGroup.mk y ↔
      ((x : G)⁻¹ * y) ∈ E := fun x y => by
    rw [QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv]
  let χ : ↥F →* ↥C ⧸ E.subgroupOf C := MonoidHom.mk'
    (fun f => QuotientGroup.mk (⟨h⁻¹ * (f : G)⁻¹ * h * f, hχC f f.2⟩ : ↥C)) (fun f₁ f₂ => by
      rw [← QuotientGroup.mk_mul, hq]
      show (h⁻¹ * ((f₁ : G) * f₂)⁻¹ * h * ((f₁ : G) * f₂))⁻¹ *
        ((h⁻¹ * (f₁ : G)⁻¹ * h * f₁) * (h⁻¹ * (f₂ : G)⁻¹ * h * f₂)) ∈ E
      have hχ₁ := hχC f₁ f₁.2
      have hχ₂ := hχC f₂ f₂.2
      have hz := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd
        (hFS (F.inv_mem f₂.2)) (hCS (C.inv_mem hχ₁))).2
      have hc := (hD.sq_mem_and_commutator_mem hT hCE ((sec2P E).inv_mem (hCP hχ₁))
        ((sec2P E).inv_mem (hCP hχ₂))).2
      have heq : (h⁻¹ * ((f₁ : G) * f₂)⁻¹ * h * ((f₁ : G) * f₂))⁻¹ *
          ((h⁻¹ * (f₁ : G)⁻¹ * h * f₁) * (h⁻¹ * (f₂ : G)⁻¹ * h * f₂)) =
          ((f₂ : G)⁻¹ * (h⁻¹ * (f₁ : G)⁻¹ * h * f₁)⁻¹ * (f₂ : G)⁻¹⁻¹ *
            (h⁻¹ * (f₁ : G)⁻¹ * h * f₁)⁻¹⁻¹) *
          ((h⁻¹ * (f₁ : G)⁻¹ * h * f₁)⁻¹ * (h⁻¹ * (f₂ : G)⁻¹ * h * f₂)⁻¹ *
            (h⁻¹ * (f₁ : G)⁻¹ * h * f₁)⁻¹⁻¹ * (h⁻¹ * (f₂ : G)⁻¹ * h * f₂)⁻¹⁻¹) := by group
      rw [heq]
      exact E.mul_mem (hZE hz) hc)
  have hker : χ.ker = (E ⊓ F).subgroupOf F := by
    ext f
    have hiff : χ f = 1 ↔ h⁻¹ * (f : G)⁻¹ * h * f ∈ E := by
      show (QuotientGroup.mk (⟨h⁻¹ * (f : G)⁻¹ * h * f, hχC f f.2⟩ : ↥C) :
        ↥C ⧸ E.subgroupOf C) = QuotientGroup.mk (1 : ↥C) ↔ _
      rw [hq]
      show (h⁻¹ * (f : G)⁻¹ * h * f)⁻¹ * 1 ∈ E ↔ _
      rw [mul_one, inv_mem_iff]
    rw [MonoidHom.mem_ker, mem_subgroupOf, hiff]
    constructor
    · intro hfE
      refine ⟨?_, f.2⟩
      by_contra hfE'
      have hQ : rightConjugate R h⁻¹ ∈ pointsIn R E :=
        rightConjugate_mem_pointsIn hD.self_mem (inv_mem hhN)
      have hf2 : (f : G) * f = 1 := by rw [← sq]; exact hF.elemF.2 f f.2
      have hfinv : (f : G)⁻¹ = f := inv_eq_of_mul_eq_one_left hf2
      have hfh : (f : G) * h * (f : G)⁻¹ = h * (h⁻¹ * (f : G)⁻¹ * h * f) := by
        calc (f : G) * h * (f : G)⁻¹ = (f : G)⁻¹ * h * f := by rw [hfinv]
          _ = h * (h⁻¹ * (f : G)⁻¹ * h * f) := by group
      have hfQ : (f : G) ∈ normalizer (rightConjugate R h⁻¹ : Set G) := by
        refine Sec2.mem_normalizer_of_forall_conj_mem fun q hq => ?_
        rw [mem_rightConjugate_iff, inv_inv] at hq ⊢
        obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, h * r * h⁻¹ = q := ⟨h⁻¹ * q * h, hq, by group⟩
        have hfr : (f : G) * r * (f : G)⁻¹ = r := by
          rw [hFcomm f f.2 r (hF.R_le_F hr), mul_inv_cancel_right]
        have hcomm := hD.comm _ hfE _ (hF.R_le_E hr)
        have key : h⁻¹ * ((f : G) * (h * r * h⁻¹) * (f : G)⁻¹) * h = r := by
          calc h⁻¹ * ((f : G) * (h * r * h⁻¹) * (f : G)⁻¹) * h
              = h⁻¹ * (((f : G) * h * (f : G)⁻¹) * ((f : G) * r * (f : G)⁻¹) *
                ((f : G) * h * (f : G)⁻¹)⁻¹) * h := by group
            _ = h⁻¹ * ((h * (h⁻¹ * (f : G)⁻¹ * h * f)) * r *
                (h * (h⁻¹ * (f : G)⁻¹ * h * f))⁻¹) * h := by rw [hfh, hfr]
            _ = (h⁻¹ * (f : G)⁻¹ * h * f) * r * (h⁻¹ * (f : G)⁻¹ * h * f)⁻¹ := by group
            _ = r * (h⁻¹ * (f : G)⁻¹ * h * f) * (h⁻¹ * (f : G)⁻¹ * h * f)⁻¹ := by rw [hcomm]
            _ = r := by group
        rw [key]
        exact hr
      have hle : rightConjugate R h⁻¹ ≤ E ⊓ F := by
        by_contra hnot
        exact hfE' (mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd f.2 hQ hnot hfQ)
      apply hhC
      have := C.inv_mem (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd
        ((sec2P E).inv_mem hh) hle)
      simpa using this
    · rintro ⟨hfE, -⟩
      have := E.mul_mem ((mem_normalizer_iff.mp (inv_mem hhN) _).mp (E.inv_mem hfE)) hfE
      simpa [mul_assoc] using this
  have hrange : χ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hker]
    change (E ⊓ F).relIndex F = E.relIndex C
    rw [hCidx]
    have h1 := relIndex_mul_card (E ⊓ F) F
    rw [inf_eq_left.mpr (inf_le_right : E ⊓ F ≤ F), hF.card_inf, hF.cardF] at h1
    omega
  obtain ⟨f, hf⟩ := MonoidHom.range_eq_top.mp hrange
    (QuotientGroup.mk (⟨c₀⁻¹, C.inv_mem hc₀⟩ : ↥C))
  refine ⟨f, f.2, ?_⟩
  have h1 : (h⁻¹ * (f : G)⁻¹ * h * f)⁻¹ * c₀⁻¹ ∈ E := (hq _ _).mp hf
  have := E.inv_mem h1
  simpa [mul_assoc] using this

theorem exists_mem_of_mem_normalizer_of_centralizes
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hFT : F ≤ T) {n : G} (hnT : n ∈ T) (hnE : n ∈ normalizer (E : Set G))
    (hnc : ∀ y ∈ E ⊓ F, n * y = y * n) (hnS : n * n ∈ sec2S A R E F) :
    ∃ f ∈ F, f⁻¹ * n ∈ E := by
  obtain ⟨hD, T', hT'⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hPq := isElemQuot_sec2P h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCF : C ≤ normalizer (F : Set G) := (le_sup_right : C ≤ sec2S A R E F).trans hSF
  have hnP := Sec2.normalizer_le_normalizer_sec2P E hnE
  have hPab : ∀ a ∈ sec2P E, ∀ b ∈ sec2P E, a * b * a⁻¹ * b⁻¹ ∈ C := fun a ha b hb =>
    hEC (hD.sq_mem_and_commutator_mem hT' hCE ha hb).2
  have hPsq : ∀ a ∈ sec2P E, a * a ∈ C := fun a ha =>
    hEC (hD.sq_mem_and_commutator_mem hT' hCE ha ha).1
  have hn2 : ∀ p ∈ sec2P E, p⁻¹ * (n * n * p * (n * n)⁻¹) ∈ C := by
    intro p hp
    have hs : n * n ∈ ((F ⊔ C : Subgroup G) : Set G) := hnS
    rw [coe_mul_of_right_le_normalizer_left F C hCF] at hs
    obtain ⟨f₀, hf₀, c₀, hc₀, hfc⟩ := hs
    rw [← hfc]
    have he₁ := (hD.sq_mem_and_commutator_mem hT' hCE ((sec2P E).inv_mem hp) (hCP hc₀)).2
    have h1 := C.inv_mem (mem_centralizerMod_of_mem_sec2P h11 hE16 hF hL hodd
      ((sec2P E).inv_mem hp) (F.inv_mem hf₀))
    have h2 := (mem_normalizer_iff.mp (hF.F_le_normalizer hL hodd hf₀) _).mp he₁
    have heq : p⁻¹ * (f₀ * c₀ * p * (f₀ * c₀)⁻¹) =
        (f₀⁻¹⁻¹ * p⁻¹ * f₀⁻¹ * p⁻¹⁻¹)⁻¹ * (f₀ * (p⁻¹ * c₀ * p⁻¹⁻¹ * c₀⁻¹) * f₀⁻¹) := by group
    rw [heq]
    exact C.mul_mem h1 (hEC h2)
  obtain ⟨h, hh, hhC, hnh⟩ := Sec2.exists_not_mem_conj_mem
    (fun hle => by
      have := le_antisymm hCP hle
      rw [this, hPq.2.1] at hCidx
      omega) hPab hPsq hnP hn2
  obtain ⟨f, hf, hfe⟩ := exists_mem_commutator h11 hE16 hF hL hodd hh hhC hnh
  refine ⟨f, hf, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, m = f⁻¹ * n := ⟨_, rfl⟩
  rw [← hm]
  have hmT : m ∈ T := hm ▸ T.mul_mem (T.inv_mem (hFT hf)) hnT
  obtain ⟨k, hk⟩ := hT2 ⟨m, hmT⟩
  have hmk : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hmE : m ∈ normalizer (E : Set G) :=
    hm ▸ mul_mem (inv_mem (hF.F_le_normalizer hL hodd hf)) hnE
  have hmc : ∀ y ∈ E ⊓ F, m * y = y * m := by
    intro y hy
    have h1 : f * y = y * f := hFcomm f hf y hy.2
    have h2 := hnc y hy
    have h3 : f⁻¹ * y = y * f⁻¹ := by
      calc f⁻¹ * y = f⁻¹ * (y * f) * f⁻¹ := by group
        _ = f⁻¹ * (f * y) * f⁻¹ := by rw [h1]
        _ = y * f⁻¹ := by group
    rw [hm]
    calc f⁻¹ * n * y = f⁻¹ * (n * y) := by group
      _ = f⁻¹ * (y * n) := by rw [h2]
      _ = f⁻¹ * y * n := by group
      _ = y * f⁻¹ * n := by rw [h3]
      _ = y * (f⁻¹ * n) := by group
  have hmh : h⁻¹ * (m * h * m⁻¹) ∈ E := by
    have hz := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd
      ((le_sup_right : C ≤ sec2S A R E F) (C.inv_mem hnh))
      ((le_sup_left : F ≤ sec2S A R E F) (F.inv_mem hf))).2
    have h1 : (h⁻¹ * f⁻¹ * h * f) * (h⁻¹ * (n * h * n⁻¹)) ∈ E := by
      have := (mem_normalizer_iff.mp (Sec2.sec2P_le E (inv_mem (hCP hnh))) _).mp hfe
      have heq : (h⁻¹ * (n * h * n⁻¹))⁻¹ * ((h⁻¹ * (n * h * n⁻¹)) * (h⁻¹ * f⁻¹ * h * f)) *
          (h⁻¹ * (n * h * n⁻¹))⁻¹⁻¹ = (h⁻¹ * f⁻¹ * h * f) * (h⁻¹ * (n * h * n⁻¹)) := by group
      rw [← heq]
      exact this
    have heq : h⁻¹ * (m * h * m⁻¹) =
        ((h⁻¹ * f⁻¹ * h * f) * (h⁻¹ * (n * h * n⁻¹))) *
          ((h⁻¹ * (n * h * n⁻¹))⁻¹ * f⁻¹ * (h⁻¹ * (n * h * n⁻¹))⁻¹⁻¹ * f⁻¹⁻¹) := by
      rw [hm]
      group
    rw [heq]
    exact E.mul_mem h1 (hZE hz)
  have hhN := Sec2.sec2P_le E hh
  have hQ : rightConjugate R h⁻¹ ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (inv_mem hhN)
  have hmQ : m ∈ normalizer (rightConjugate R h⁻¹ : Set G) := by
    refine Sec2.mem_normalizer_of_forall_conj_mem fun q hq => ?_
    rw [mem_rightConjugate_iff, inv_inv] at hq ⊢
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, h * r * h⁻¹ = q := ⟨h⁻¹ * q * h, hq, by group⟩
    have hmr : m * r * m⁻¹ = r := by rw [hmc r (hREF hr), mul_inv_cancel_right]
    have hcomm := hD.comm _ hmh _ (hF.R_le_E hr)
    have key : h⁻¹ * (m * (h * r * h⁻¹) * m⁻¹) * h = r := by
      calc h⁻¹ * (m * (h * r * h⁻¹) * m⁻¹) * h
          = h⁻¹ * (m * h * m⁻¹) * (m * r * m⁻¹) * (h⁻¹ * (m * h * m⁻¹))⁻¹ := by group
        _ = h⁻¹ * (m * h * m⁻¹) * r * (h⁻¹ * (m * h * m⁻¹))⁻¹ := by rw [hmr]
        _ = r * (h⁻¹ * (m * h * m⁻¹)) * (h⁻¹ * (m * h * m⁻¹))⁻¹ := by rw [hcomm]
        _ = r := by group
    rw [key]
    exact hr
  have hle : ¬ rightConjugate R h⁻¹ ≤ E ⊓ F := fun hle => hhC (by
    have := C.inv_mem (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd
      ((sec2P E).inv_mem hh) hle)
    simpa using this)
  exact mem_of_mem_normalizer_of_not_le' h11 hE16 hF hL hodd hmE hmc hmk hQ hle hmQ

theorem sec2S_le_centralizer_inf
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    sec2S A R E F ≤ centralizer (sec2Z A E F : Set G) ⊓
      centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓ normalizer (E : Set G) ⊓
        normalizer (F : Set G) := by
  have hPZ := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hZ := hF.sec2Z_eq
  have hRZ := hF.sup_sec2Z
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZF : sec2Z A E F ≤ F := by rw [hZ]; exact inf_le_left.trans inf_le_right
  have hZEA : sec2Z A E F ≤ E ⊓ A := by rw [hZ]; exact fun z hz => ⟨hz.1.1, hz.2⟩
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) hSF
  · exact sup_le (fun f hf => mem_centralizer_iff.mpr fun z hz => hFcomm z (hZF hz) f hf)
      (fun c hc => mem_centralizer_iff.mpr fun z hz =>
        mem_centralizer_iff.mp (hPZ (mem_centralizerMod.mp hc).1) z (hZEA hz))
  · refine sup_le (fun f hf => mem_centralizerMod.mpr ⟨mem_top f, centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun z hz => hFcomm z (hZF hz) f hf), fun y hy => ?_⟩)
      (fun c hc => mem_centralizerMod.mpr ⟨mem_top c, (mem_centralizerMod.mp hc).2.1,
        (mem_centralizerMod.mp hc).2.2⟩)
    have hyF : y ∈ F := (by rw [← hRZ]; exact hy : y ∈ E ⊓ F).2
    have h1 : y⁻¹ * f⁻¹ * y * f = 1 := by
      calc y⁻¹ * f⁻¹ * y * f = y⁻¹ * f⁻¹ * (y * f) := by group
        _ = y⁻¹ * f⁻¹ * (f * y) := by rw [hFcomm y hyF f hf]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  · exact sup_le (hF.F_le_normalizer hL hodd)
      (fun c hc => Sec2.sec2P_le E (mem_centralizerMod.mp hc).1)

theorem le_normalizer_sec2S {A R E F : Subgroup G} :
    centralizer (sec2Z A E F : Set G) ⊓ centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓
      normalizer (E : Set G) ⊓ normalizer (F : Set G) ≤
        normalizer (sec2S A R E F : Set G) := by
  rintro x ⟨⟨⟨-, hxM⟩, hxE⟩, hxF⟩
  have hxRZ : x ∈ normalizer ((R ⊔ sec2Z A E F : Subgroup G) : Set G) :=
    Sec2.mem_normalizer_of_mem_centralizerMod le_sup_right hxM
  have hxZ := (mem_centralizerMod.mp hxM).2.1
  have hxP := Sec2.normalizer_le_normalizer_sec2P E hxE
  have hxC : x ∈ normalizer
      (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) : Set G) :=
    Sec2.mem_normalizer_of_forall_conj_mem fun c hc => by
      obtain ⟨hcP, hcZ, hcc⟩ := mem_centralizerMod.mp hc
      refine mem_centralizerMod.mpr ⟨(mem_normalizer_iff.mp hxP c).mp hcP,
        mul_mem (mul_mem hxZ hcZ) (inv_mem hxZ), fun y hy => ?_⟩
      have hy' : x⁻¹ * y * x ∈ R ⊔ sec2Z A E F := by
        have := (mem_normalizer_iff.mp (inv_mem hxRZ) y).mp hy
        simpa using this
      have h2 := (mem_normalizer_iff.mp hxZ _).mp (hcc _ hy')
      have heq : y⁻¹ * (x * c * x⁻¹)⁻¹ * y * (x * c * x⁻¹) =
          x * ((x⁻¹ * y * x)⁻¹ * c⁻¹ * (x⁻¹ * y * x) * c) * x⁻¹ := by group
      rw [heq]
      exact h2
  exact mem_normalizer_sup hxF hxC

theorem isSylowOf_sec2S
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    IsSylowOf 2 (sec2S A R E F) (centralizer (sec2Z A E F : Set G) ⊓
      centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓ normalizer (E : Set G) ⊓
        normalizer (F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hSX := sec2S_le_centralizer_inf h11 hE16 hF hL hodd
  have hXS := le_normalizer_sec2S (A := A) (R := R) (E := E) (F := F)
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRZ := hF.sup_sec2Z
  have hR := hF.sylowR
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hR.le hR.isPGroup hodd
  have hZA : sec2Z A E F ≤ A := by rw [hF.sec2Z_eq]; exact inf_le_right
  set X := centralizer (sec2Z A E F : Set G) ⊓ centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓
    normalizer (E : Set G) ⊓ normalizer (F : Set G)
  have hS := (isElemQuot_sec2S h11 hE16 hF hL hodd).2
  have hS2 : IsPGroup 2 (sec2S A R E F) := by
    have h1 := relIndex_mul_card E (sec2S A R E F)
    rw [inf_eq_left.mpr hS.1, hS.2.1, hF.cardE] at h1
    exact IsPGroup.of_card (n := 10) (by rw [← h1]; norm_num)
  obtain ⟨Q, hQ⟩ := (hS2.comap_subtype : IsPGroup 2 ((sec2S A R E F).subgroupOf X)).exists_le_sylow
  have hTsyl : IsSylowOf 2 ((Q : Subgroup ↥X).map X.subtype) X := ⟨Q, rfl⟩
  set T := (Q : Subgroup ↥X).map X.subtype
  have hST : sec2S A R E F ≤ T := fun s hs => ⟨⟨s, hSX hs⟩, hQ hs, rfl⟩
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hTX : T ≤ X := hTsyl.le
  suffices hTS : T ≤ sec2S A R E F by rwa [le_antisymm hTS hST] at hTsyl
  by_contra hTS
  obtain ⟨t, htT, htS⟩ := IsConcreteLE.not_le_iff_exists.mp hTS
  obtain ⟨t', ht'T, ht'S, ht'2⟩ : ∃ t' ∈ T, t' ∉ sec2S A R E F ∧ t' * t' ∈ sec2S A R E F := by
    classical
    obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
    have hex : ∃ j, t ^ 2 ^ j ∈ sec2S A R E F := ⟨k, by
      have : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact one_mem _⟩
    have hj := Nat.find_spec hex
    have hj0 : Nat.find hex ≠ 0 := fun h0 => htS (by rw [h0, pow_zero, pow_one] at hj; exact hj)
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hmin := Nat.find_min hex (show i < Nat.find hex by omega)
    refine ⟨t ^ 2 ^ i, T.pow_mem htT _, hmin, ?_⟩
    rw [← pow_add, ← two_mul, ← pow_succ', show i + 1 = Nat.find hex by omega]
    exact hj
  have ht'X := hTX ht'T
  obtain ⟨⟨⟨-, -⟩, ht'E⟩, ht'F⟩ := hTX ht'T
  have ht'EF : t' ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨ht'E, ht'F⟩
  have hle : rightConjugate R t' ≤ E ⊓ F := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hREF t'
    rwa [(rightConjugate_eq_self_iff _ _).mpr ht'EF] at h
  obtain ⟨p, hp, hpQ⟩ := htr _ (rightConjugate_mem_pointsIn hD.self_mem ht'E)
  have hpC := mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hp
    (by rw [hpQ]; exact hle)
  have hpS : p ∈ sec2S A R E F := (le_sup_right : _ ≤ sec2S A R E F) hpC
  obtain ⟨n, hn⟩ : ∃ n, n = t' * p⁻¹ := ⟨_, rfl⟩
  have hnT : n ∈ T := hn ▸ T.mul_mem ht'T (T.inv_mem (hST hpS))
  have hnS : n ∉ sec2S A R E F := fun h => ht'S (by
    have := (sec2S A R E F).mul_mem h hpS
    rwa [hn, inv_mul_cancel_right] at this)
  have hnR : n ∈ normalizer (R : Set G) := by
    rw [← rightConjugate_eq_self_iff, hn, ← rightConjugate_mul, ← hpQ, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  obtain ⟨⟨⟨hnZ, hnM⟩, hnE⟩, -⟩ := hTX hnT
  have hnRc : ∀ r ∈ R, r * n = n * r := by
    intro r hr
    have h1 := (mem_centralizerMod.mp hnM).2.2 r (mem_sup_left hr)
    have h2 : r⁻¹ * n⁻¹ * r * n ∈ R := by
      have := R.mul_mem (R.inv_mem hr) ((mem_normalizer_iff.mp (inv_mem hnR) r).mp hr)
      simpa [mul_assoc] using this
    have h3 : r⁻¹ * n⁻¹ * r * n = 1 := by
      have : r⁻¹ * n⁻¹ * r * n ∈ R ⊓ A := ⟨h2, hZA h1⟩
      rwa [hRA1, mem_bot] at this
    calc r * n = n * (r * (r⁻¹ * n⁻¹ * r * n)) := by group
      _ = n * r := by rw [h3, mul_one]
  have hnc : ∀ y ∈ E ⊓ F, n * y = y * n := by
    intro y hy
    rw [← hRZ] at hy
    have hle' : R ⊔ sec2Z A E F ≤ centralizer ({n} : Set G) := sup_le
      (fun r hr => mem_centralizer_singleton_iff.mpr (hnRc r hr))
      (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hnZ z hz))
    exact (mem_centralizer_singleton_iff.mp (hle' hy)).symm
  have hn2 : n * n ∈ sec2S A R E F := by
    have h1 := (mem_normalizer_iff.mp (hXS (inv_mem ht'X)) p⁻¹).mp (inv_mem hpS)
    have heq : n * n = (t' * t') * (t'⁻¹ * p⁻¹ * t'⁻¹⁻¹) * p⁻¹ := by rw [hn]; group
    rw [heq]
    exact mul_mem (mul_mem ht'2 h1) (inv_mem hpS)
  obtain ⟨f, hf, hfn⟩ := exists_mem_of_mem_normalizer_of_centralizes h11 hE16 hF hL hodd hT2
    ((le_sup_left : F ≤ sec2S A R E F).trans hST) hnT hnE hnc hn2
  apply hnS
  have := (sec2S A R E F).mul_mem ((le_sup_left : F ≤ sec2S A R E F) hf)
    (((le_centralizerMod hF).trans (le_sup_right : _ ≤ sec2S A R E F)) hfn)
  simpa using this

end Frame

theorem step22_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step22 := by
  intro G _ _ A R g E F hS
  exact ⟨sec2P_sup_sec2S_inf_normalizer h11 hE16 hS.frame hS.type hS.odd,
    card_conjSet_sec2P h11 hE16 hS.frame hS.type hS.odd,
    isSylowOf_sec2S h11 hE16 hS.frame hS.type hS.odd⟩

end CFSG.ComponentClassification.AS81

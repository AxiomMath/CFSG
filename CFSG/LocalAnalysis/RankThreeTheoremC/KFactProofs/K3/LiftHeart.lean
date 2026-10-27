module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftFaith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftEbar


public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open Subgroup CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] def IsLift {X Y : Type} [Group X] [Group Y] (π : X →* Y) (E : Subgroup Y) (s : X)
    (J : Subgroup X) : Prop :=
  J.map π = E ∧ s ∈ Subgroup.normalizer (J : Set X)

theorem lf_commutator_le_self {X : Type} [Group X] (J : Subgroup X) : ⁅J, J⁆ ≤ J := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)

theorem exists_minimal_lift {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (E : Subgroup Y) (s : X)
    (hE : ∀ y : Y, y ∈ E ↔ π s * y * (π s)⁻¹ ∈ E) :
    ∃ J : Subgroup X, IsLift π E s J ∧ ∀ J' : Subgroup X, IsLift π E s J' → J' ≤ J → J' = J := by
  refine exists_minimal_subgroup (IsLift π E s) ⟨E.comap π, ?_, ?_⟩
  · exact Subgroup.map_comap_eq_self_of_surjective hπ E
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
    exact hE (π x)

theorem minimal_lift_perfect {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y) (E : Subgroup Y)
    (hE : ⁅E, E⁆ = E) (s : X) (J : Subgroup X) (hJ : IsLift π E s J)
    (hmin : ∀ J' : Subgroup X, IsLift π E s J' → J' ≤ J → J' = J) : ⁅J, J⁆ = J := by
  have hJs : ∀ x : X, x ∈ J ↔ s * x * s⁻¹ ∈ J := by
    have := Subgroup.mem_normalizer_iff.mp hJ.2
    simpa using this
  have hmapJ : J.map (MulAut.conj s).toMonoidHom = J := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hJs x).mp hx
    · intro hy
      refine ⟨s⁻¹ * y * s, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      refine (hJs _).mpr ?_
      simpa [mul_assoc] using hy
  have hmapC : (⁅J, J⁆).map (MulAut.conj s).toMonoidHom = ⁅J, J⁆ := by
    rw [Subgroup.map_commutator, hmapJ]
  refine hmin ⁅J, J⁆ ⟨?_, ?_⟩ (lf_commutator_le_self J)
  · rw [Subgroup.map_commutator, hJ.1, hE]
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hmapC]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hmapC] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := (MulAut.conj s).injective (by simpa using hyx)
      rw [← this]; exact hy

theorem lf_conj_mem_iff {X : Type} [Group X] {K : Subgroup X} {s : X} (hs : s ∈ K) (x : X) :
    x ∈ K ↔ s * x * s⁻¹ ∈ K := by
  constructor
  · intro h
    exact K.mul_mem (K.mul_mem hs h) (K.inv_mem hs)
  · intro h
    have := K.mul_mem (K.mul_mem (K.inv_mem hs) h) hs
    simpa [mul_assoc] using this

theorem lf_conj_centralizer {X : Type} [Group X] (J R : Subgroup X) (g : X)
    (hgJ : ∀ x : X, x ∈ J → g * x * g⁻¹ ∈ J) (hgR : ∀ r ∈ R, g⁻¹ * r * g ∈ R) :
    ∀ c ∈ J ⊓ Subgroup.centralizer (R : Set X), g * c * g⁻¹ ∈ J ⊓ Subgroup.centralizer (R : Set X) := by
  intro c hc
  obtain ⟨hcJ, hcC⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨hgJ c hcJ, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have hcr := Subgroup.mem_centralizer_iff.mp hcC _ (hgR r hr)
  calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcr]
    _ = g * c * g⁻¹ * r := by group

theorem exists_invariant_normal_sylow {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (E : Subgroup Y) (s : X) (hker : ¬ 3 ∣ Nat.card π.ker) (hs3 : ∃ n : ℕ, s ^ 3 ^ n = 1)
    (q : ℕ) (hq : q.Prime) (J : Subgroup X) (hJ : IsLift π E s J)
    (hmin : ∀ J' : Subgroup X, IsLift π E s J' → J' ≤ J → J' = J) :
    ∃ R : Subgroup X, R ≤ J ⊓ π.ker ∧ IsPGroup q R ∧ ¬ q ∣ R.relIndex (J ⊓ π.ker) ∧
      (∀ j ∈ J, ∀ r ∈ R, j * r * j⁻¹ ∈ R) ∧ s ∈ Subgroup.normalizer (R : Set X) := by
  classical
  set A : Subgroup X := J ⊓ π.ker with hA
  have hJs : ∀ x : X, x ∈ J ↔ s * x * s⁻¹ ∈ J := by
    have := Subgroup.mem_normalizer_iff.mp hJ.2
    simpa using this
  have hkerN : ∀ x : X, x ∈ π.ker ↔ s * x * s⁻¹ ∈ π.ker := by
    intro x
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · intro h; rw [h]; simp
    · intro h
      have := congrArg (fun z => (π s)⁻¹ * z * π s) h
      simpa [mul_assoc] using this
  have hsA : ∀ a : X, a ∈ A ↔ s * a * s⁻¹ ∈ A := fun a => by
    simp only [hA, Subgroup.mem_inf]
    rw [← hJs a, ← hkerN a]
  have h3A : ¬ 3 ∣ Nat.card A := fun h => hker (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨R, hRA, hRq, hRidx, hRs⟩ := exists_invariant_sylow_zpowers A s hsA hs3 h3A q hq
  have hAJ : A ≤ J := inf_le_left
  have hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A := by
    intro j hj a ha
    refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hj (Subgroup.mem_inf.mp ha).1) (J.inv_mem hj),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp ha).2, mul_one, map_inv,
      mul_inv_cancel]
  have hfr := frattini_argument_subgroup J A R q hq hAJ hAn hRA hRq hRidx
  have hNlift : IsLift π E s (J ⊓ Subgroup.normalizer (R : Set X)) := by
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · rw [← hJ.1]; exact Subgroup.map_mono inf_le_left
      · rw [← hJ.1]
        rintro y ⟨j, hj, rfl⟩
        obtain ⟨a, haA, haN⟩ := hfr j hj
        refine ⟨a * j, Subgroup.mem_inf.mpr ⟨J.mul_mem (hAJ haA) hj, haN⟩, ?_⟩
        rw [map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp haA).2, one_mul]
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, Subgroup.mem_inf]
      rw [hJs x, lf_conj_mem_iff hRs x]
  have hJN : J ⊓ Subgroup.normalizer (R : Set X) = J := hmin _ hNlift inf_le_left
  refine ⟨R, hRA, hRq, hRidx, fun j hj r hr => ?_, hRs⟩
  have hjN : j ∈ Subgroup.normalizer (R : Set X) := by
    have : j ∈ J ⊓ Subgroup.normalizer (R : Set X) := by rw [hJN]; exact hj
    exact (Subgroup.mem_inf.mp this).2
  exact (Subgroup.mem_normalizer_iff.mp hjN r).mp hr

theorem minimal_lift_centralizes {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker)
    {L₁ L₂ L₃ : Subgroup Y} {s : X} (hT : TriData L₁ L₂ L₃ (π s)) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2)
    (J : Subgroup X) (hJ : IsLift π (L₁ ⊔ L₂ ⊔ L₃) s J)
    (hmin : ∀ J' : Subgroup X, IsLift π (L₁ ⊔ L₂ ⊔ L₃) s J' → J' ≤ J → J' = J)
    (R : Subgroup X) (hRA : R ≤ J ⊓ π.ker) (hRq : IsPGroup q R)
    (hRJ : ∀ j ∈ J, ∀ r ∈ R, j * r * j⁻¹ ∈ R) (hRs : s ∈ Subgroup.normalizer (R : Set X)) :
    ∀ j ∈ J, ∀ r ∈ R, j * r = r * j := by
  classical
  haveI : Finite Y := Finite.of_surjective π hπ
  haveI : Fact q.Prime := ⟨hq⟩
  set E : Subgroup Y := L₁ ⊔ L₂ ⊔ L₃ with hE
  set C : Subgroup X := J ⊓ Subgroup.centralizer (R : Set X) with hC
  have hJE : J.map π = E := hJ.1
  have hJs : ∀ x : X, x ∈ J ↔ s * x * s⁻¹ ∈ J := by
    have := Subgroup.mem_normalizer_iff.mp hJ.2
    simpa using this
  have hRJ' : ∀ j ∈ J, ∀ r ∈ R, j⁻¹ * r * j ∈ R := fun j hj r hr => by
    have := hRJ j⁻¹ (J.inv_mem hj) r hr
    simpa using this
  have hRs1 : ∀ r ∈ R, s * r * s⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.mp hRs r).mp hr
  have hRs2 : ∀ r ∈ R, s⁻¹ * r * s ∈ R := fun r hr => by
    have := (Subgroup.mem_normalizer_iff.mp hRs (s⁻¹ * r * s)).mpr (by simpa [mul_assoc] using hr)
    exact this
  have hCnorm : ∀ j ∈ J, ∀ c ∈ C, j * c * j⁻¹ ∈ C := fun j hj c hc =>
    lf_conj_centralizer J R j (fun x hx => J.mul_mem (J.mul_mem hj hx) (J.inv_mem hj))
      (hRJ' j hj) c hc
  have hCs : ∀ c ∈ C, s * c * s⁻¹ ∈ C := fun c hc =>
    lf_conj_centralizer J R s (fun x hx => (hJs x).mp hx) hRs2 c hc
  have hgJ' : ∀ x : X, x ∈ J → s⁻¹ * x * s⁻¹⁻¹ ∈ J := fun x hx =>
    (hJs (s⁻¹ * x * s⁻¹⁻¹)).mpr (by simpa [mul_assoc] using hx)
  have hgR' : ∀ r ∈ R, s⁻¹⁻¹ * r * s⁻¹ ∈ R := fun r hr => by simpa using hRs1 r hr
  have hCs' : ∀ c ∈ C, s⁻¹ * c * s ∈ C := fun c hc => by
    have := lf_conj_centralizer J R s⁻¹ hgJ' hgR' c hc
    rwa [inv_inv] at this
  set M : Subgroup Y := C.map π with hM
  have hMe : M ≤ E := by
    rw [← hJE]; exact Subgroup.map_mono inf_le_left
  have hMn : ∀ e ∈ E, ∀ m ∈ M, e * m * e⁻¹ ∈ M := by
    intro e he m hm
    rw [← hJE] at he
    obtain ⟨j, hj, rfl⟩ := he
    obtain ⟨c, hc, rfl⟩ := hm
    exact ⟨j * c * j⁻¹, hCnorm j hj c hc, by simp⟩
  have hMg : ∀ m ∈ M, π s * m * (π s)⁻¹ ∈ M := by
    intro m hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact ⟨s * c * s⁻¹, hCs c hc, by simp⟩
  have hJnorm : ∀ j ∈ J, j ∈ Subgroup.normalizer (R : Set X) := fun j hj =>
    Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hRJ j hj h hh, fun hh => by
      have := hRJ' j hj _ hh
      simpa [mul_assoc] using this⟩
  rcases ebar_dichotomy hT M hMe hMn hMg with hcen | hbig
  · exfalso
    obtain ⟨T, hTE, hT27, hTab, hT3, hTc⟩ := exists_T hT
    obtain ⟨B, hBJ, hB27, hBab, hB3, hBT, hBinj⟩ :=
      exists_sylow_three_lift π J hker T (by rw [hJE]; exact hTE) hT27 hTab hT3
    refine no_faithful_E27 hq5 hrank hRq (B := B) (fun b hb => hJnorm b (hBJ hb)) hB27 hBab hB3 ?_
    intro b hb hbR
    have hbC : b ∈ C := Subgroup.mem_inf.mpr ⟨hBJ hb,
      Subgroup.mem_centralizer_iff.mpr fun r hr => (hbR r hr).symm⟩
    have hπb : π b ∈ T := by rw [← hBT]; exact Subgroup.mem_map_of_mem π hb
    have h1 : π b = 1 :=
      hTc (π b) hπb (fun e he => hcen (π b) (Subgroup.mem_map_of_mem π hbC) e he)
    exact hBinj b hb h1
  · have hClift : IsLift π E s C := by
      refine ⟨le_antisymm hMe hbig, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hCs x, fun hx => ?_⟩
      have := hCs' _ hx
      simpa [mul_assoc] using this
    have hCJ : C = J := hmin C hClift inf_le_left
    intro j hj r hr
    have hjC : j ∈ C := by rw [hCJ]; exact hj
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hjC).2) r hr).symm

theorem lift_heart {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) {L₁ L₂ L₃ : Subgroup Y} (s : X)
    (hs3 : ∃ n : ℕ, s ^ 3 ^ n = 1) (hT : TriData L₁ L₂ L₃ (π s)) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hqd : q ∣ Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁))
    (hqM : ¬ q ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L₁ ⧸ Subgroup.center ↥L₁))) :
    3 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  classical
  by_contra hlt
  have hrank : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2 := by omega
  haveI : Finite Y := Finite.of_surjective π hπ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨J, hJ, hmin⟩ := exists_minimal_lift π hπ (L₁ ⊔ L₂ ⊔ L₃) s (ebar_conj hT)
  have hJperf : ⁅J, J⁆ = J := minimal_lift_perfect π (L₁ ⊔ L₂ ⊔ L₃) (ebar_perfect hT) s J hJ hmin
  obtain ⟨R, hRA, hRq, hRsyl, hRJ, hRs⟩ :=
    exists_invariant_normal_sylow π (L₁ ⊔ L₂ ⊔ L₃) s hker hs3 q hq J hJ hmin
  have hcent : ∀ j ∈ J, ∀ r ∈ R, j * r = r * j :=
    minimal_lift_centralizes π hπ hker hT hq hq5 hrank J hJ hmin R hRA hRq hRJ hRs
  set A : Subgroup X := J ⊓ π.ker with hA
  have hAJ : A ≤ J := inf_le_left
  have hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A := by
    intro j hj a ha
    refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hj (Subgroup.mem_inf.mp ha).1) (J.inv_mem hj),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp ha).2, mul_one, map_inv,
      mul_inv_cancel]
  have hAiff : ∀ j ∈ J, ∀ a : X, a ∈ A ↔ j * a * j⁻¹ ∈ A := by
    intro j hj a
    refine ⟨hAn j hj a, fun h => ?_⟩
    have := hAn j⁻¹ (J.inv_mem hj) _ h
    rwa [show j⁻¹ * (j * a * j⁻¹) * j⁻¹⁻¹ = a by group] at this
  obtain ⟨C, hCA, hCq, hCinv, hAC⟩ :=
    exists_normal_q_complement J A R hAJ hAn hRA hRq hRsyl hcent
  have hCJ : C ≤ J := hCA.trans hAJ
  let φ : ↥J →* Y := π.comp J.subtype
  haveI hCn : (C.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hCinv g.1 (hAiff g.1 g.2) n hn
    simpa using this⟩
  have hCker' : C.subgroupOf J ≤ φ.ker := by
    intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp (hCA hc)).2)
  have hCq' : ¬ q ∣ Nat.card (C.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCJ).toEquiv]
    exact hCq
  have hxA : ∀ x : ↥J, x ∈ φ.ker → (x : X) ∈ A := fun x hx =>
    Subgroup.mem_inf.mpr ⟨x.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)⟩
  have hcen' : ∀ x ∈ φ.ker, ∀ y : ↥J, ⁅x, y⁆ ∈ C.subgroupOf J := by
    intro x hx y
    obtain ⟨r, hr, c, hc, hxrc⟩ := hAC x (hxA x hx)
    rw [Subgroup.mem_subgroupOf]
    have hcom_r : ∀ z : X, z ∈ J → r * z * r⁻¹ = z := by
      intro z hz
      rw [← hcent z hz r hr, mul_assoc, mul_inv_cancel, mul_one]
    have e1 : ((⁅x, y⁆ : ↥J) : X) = r * (c * y * c⁻¹) * r⁻¹ * y⁻¹ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxrc]
      group
    have e2 : ((⁅x, y⁆ : ↥J) : X) = c * (y * c⁻¹ * y⁻¹) := by
      rw [e1, hcom_r (c * y * c⁻¹) (J.mul_mem (J.mul_mem (hCJ hc) y.2) (J.inv_mem (hCJ hc)))]
      group
    rw [e2]
    exact C.mul_mem hc (hCinv y.1 (hAiff y.1 y.2) c⁻¹ (C.inv_mem hc))
  have hpow' : ∀ x ∈ φ.ker, ∃ n : ℕ, x ^ q ^ n ∈ C.subgroupOf J := by
    intro x hx
    obtain ⟨r, hr, c, hc, hxrc⟩ := hAC x (hxA x hx)
    obtain ⟨n, hn⟩ := hRq ⟨r, hr⟩
    refine ⟨n, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    have hrn : r ^ q ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hcomm : Commute r c := (hcent c (hCJ hc) r hr).symm
    have e : ((x ^ q ^ n : ↥J) : X) = c ^ q ^ n := by
      rw [Subgroup.coe_pow, hxrc, hcomm.mul_pow, hrn, one_mul]
    rw [e]
    exact C.pow_mem hc _
  have hLφ : ∀ {L : Subgroup Y}, L ≤ L₁ ⊔ L₂ ⊔ L₃ → L ≤ φ.range := by
    intro L hL y hy
    have hmem : y ∈ J.map π := by rw [hJ.1]; exact hL hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨x, hx⟩, hxy⟩
  haveI : Group.IsPerfect ↥L₁ := hT.qs₁.1
  have hcl₁ : QClean q (↥L₁ ⧸ Subgroup.center ↥L₁) := qClean_of_not_dvd_hopf q _ hqM
  obtain ⟨e₂⟩ := quotCenter_mulEquiv (π s) hT.cyc₁
  have hcl₂ := QClean.congr e₂ hcl₁
  obtain ⟨e₃⟩ := quotCenter_mulEquiv (π s) hT.cyc₂
  have hcl₃ := QClean.congr e₃ hcl₂
  obtain ⟨t₁, ht₁, ho₁⟩ := exists_orderOf_eq_of_dvd_quot hq hqd
  have hconj : ∀ t : Y, orderOf (π s * t * (π s)⁻¹) = orderOf t := fun t => by
    have := orderOf_injective (MulAut.conj (π s)).toMonoidHom (MulAut.conj (π s)).injective t
    simpa using this
  have ht₂ : π s * t₁ * (π s)⁻¹ ∈ L₂ := by
    rw [← hT.cyc₁]
    exact Subgroup.mem_map.mpr ⟨t₁, ht₁, by simp⟩
  have ht₃ : π s * (π s * t₁ * (π s)⁻¹) * (π s)⁻¹ ∈ L₃ := by
    rw [← hT.cyc₂]
    exact Subgroup.mem_map.mpr ⟨_, ht₂, by simp⟩
  obtain ⟨H, hH, hHcard⟩ := exists_elemAbelian_of_cover hq φ (C.subgroupOf J) hCq' hCker' hcen'
    hpow' L₁ L₂ L₃ hT.qs₁ hT.qs₂ hT.qs₃ hT.c12 hT.c13 hT.c23
    (hLφ (le_sup_left.trans le_sup_left)) (hLφ (le_sup_right.trans le_sup_left))
    (hLφ le_sup_right) hcl₁ hcl₂ hcl₃ t₁ (π s * t₁ * (π s)⁻¹)
    (π s * (π s * t₁ * (π s)⁻¹) * (π s)⁻¹) ht₁ ht₂ ht₃ ho₁
    ((hconj t₁).trans ho₁) (((hconj _).trans (hconj t₁)).trans ho₁)
  have h3 : 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥J) :=
    CFSG.SectionRank.le_pRank hq.one_lt le_top hH hHcard
  have h4 := CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt J.subtype J.subtype_injective
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

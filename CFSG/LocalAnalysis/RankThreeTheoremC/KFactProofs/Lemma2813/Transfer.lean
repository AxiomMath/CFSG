module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.HbarFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.QuotModule

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

section Transfer

variable {ψ : ↥X →* GL32} {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N]
  {ι : ↥(TT X) → N} {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]
  {π : N →+ M} {D : Subgroup A} {d₀ : A}

theorem tr_iota_one (hι : IsTBridge X ψ ι) : ι 1 = 0 := by
  have h := hι.mul 1 1
  rw [mul_one] at h
  simpa using h

theorem tr_iota_inv (hι : IsTBridge X ψ ι) (t : ↥(TT X)) : ι t⁻¹ = - ι t := by
  have h := hι.mul t t⁻¹
  rw [mul_inv_cancel, tr_iota_one hι] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem tr_iota_mul_inv (hι : IsTBridge X ψ ι) (a b : ↥(TT X)) : ι (a * b⁻¹) = ι a - ι b := by
  rw [hι.mul, tr_iota_inv hι, sub_eq_add_neg]

theorem tr_conj_mem_TT {g : A} (hg : g ∈ normalizer (X : Set A)) {w : A} (hw : w ∈ TT X) :
    g * w * g⁻¹ ∈ TT X :=
  (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_TT X hg) w).1 hw

theorem tr_conj_mem_T0 {g : A} (hg : g ∈ normalizer (X : Set A)) {w : A} (hw : w ∈ T0 X) :
    g * w * g⁻¹ ∈ T0 X := by
  obtain ⟨hwT, hwX⟩ := (mem_T0_iff X).1 hw
  refine (mem_T0_iff X).2 ⟨tr_conj_mem_TT hg hwT, fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ X := (Subgroup.mem_normalizer_iff''.1 hg x).1 hx
  have h1 := hwX _ hx'
  calc x * (g * w * g⁻¹) = g * ((g⁻¹ * x * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * w * g⁻¹ * x := by group

theorem tr_exists_sub (hι : IsTBridge X ψ ι) (B : AddSubgroup N) :
    ∃ W : Subgroup ↥(TT X), ∀ t, t ∈ W ↔ ι t ∈ B :=
  ⟨{ carrier := {t | ι t ∈ B}
     mul_mem' := fun {a b} ha hb => by
       have ha' : ι a ∈ B := ha
       have hb' : ι b ∈ B := hb
       have : ι (a * b) ∈ B := by
         rw [hι.mul]
         exact add_mem ha' hb'
       exact this
     one_mem' := by
       have : ι 1 ∈ B := by
         rw [tr_iota_one hι]
         exact zero_mem _
       exact this
     inv_mem' := fun {a} ha => by
       have ha' : ι a ∈ B := ha
       have : ι a⁻¹ ∈ B := by
         rw [tr_iota_inv hι]
         exact neg_mem ha'
       exact this }, fun _ => Iff.rfl⟩

theorem tr_psi_mem_zpowers (hD : D = zpowers d₀) (hDX : D ≤ X) (hd₀D : d₀ ∈ D) {x : ↥X}
    (hx : (x : A) ∈ D) : ψ x ∈ zpowers (ψ ⟨d₀, hDX hd₀D⟩) := by
  rw [hD] at hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hxk : x = (⟨d₀, hDX hd₀D⟩ : ↥X) ^ k := Subtype.ext (by simp [hk])
  rw [hxk, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

theorem tr_pi_eq_zero_iff (hι : IsTBridge X ψ ι) (hψs : Function.Surjective ψ)
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) {w : A} (hwT : w ∈ TT X) :
    π (ι ⟨w, hwT⟩) = 0 ↔ w ∈ T0 X :=
  (hπk _).trans (hι.mem_fixSub_top_iff hψs ⟨w, hwT⟩)

theorem tr_pi_mem_fixSub (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n) {H : Subgroup GL32}
    {n : N} (hn : n ∈ fixSub N H) : π n ∈ fixSub M H := by
  rw [mem_fixSub] at hn ⊢
  intro g hg
  rw [← hπe, hn g hg]

theorem tr_pi_mem_F (h : Hyp2813 X K R P) (hι : IsTBridge X ψ ι)
    (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n) (hDX : D ≤ X) (hd₀D : d₀ ∈ D) {w : A}
    (hw : w ∈ omegaCenter (pCoreOf 2 P)) (hwD : ∀ d ∈ D, w * d = d * w) (hwT : w ∈ TT X) :
    π (ι ⟨w, hwT⟩) ∈
      fixSub M (Hbar X ψ (pCoreOf 2 P) ⊔ zpowers (ψ ⟨d₀, hDX hd₀D⟩)) := by
  have hd₀X : d₀ ∈ X := hDX hd₀D
  have hSX : pCoreOf 2 P ≤ X := (pCoreOf_le_self P).trans h.P_le
  have hwS := (h.mem_omegaCenter_S_iff.1 hw).2
  have hfix : ι ⟨w, hwT⟩ ∈ fixSub N (Hbar X ψ (pCoreOf 2 P)) :=
    (hι.mem_fixSub_iff hSX ⟨w, hwT⟩).2 fun x hx => hwS x hx
  have hwd : ψ ⟨d₀, hd₀X⟩ • ι ⟨w, hwT⟩ = ι ⟨w, hwT⟩ := by
    have hc : d₀ * w * d₀⁻¹ ∈ TT X := tr_conj_mem_TT (Subgroup.le_normalizer hd₀X) hwT
    have h1 := hι.equiv ⟨d₀, hd₀X⟩ ⟨w, hwT⟩ hc
    have h2 : (⟨d₀ * w * d₀⁻¹, hc⟩ : ↥(TT X)) = ⟨w, hwT⟩ := Subtype.ext (by
      have h3 := hwD d₀ hd₀D
      calc d₀ * w * d₀⁻¹ = w * d₀ * d₀⁻¹ := by rw [← h3]
        _ = w := by group)
    rw [h2] at h1
    exact h1.symm
  rw [fixSub_sup, AddSubgroup.mem_inf]
  refine ⟨tr_pi_mem_fixSub hπe hfix, ?_⟩
  rw [mem_fixSub_zpowers, ← hπe, hwd]

theorem tr_eq_of_card_le_two {M : Type} [AddCommGroup M] (F : AddSubgroup M) [Finite F]
    (hF : Nat.card F ≤ 2) {a b : M} (ha : a ∈ F) (hb : b ∈ F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    a = b := by
  by_contra hab
  haveI := Fintype.ofFinite F
  have h3 : 2 < Fintype.card F := by
    rw [Fintype.two_lt_card_iff]
    refine ⟨⟨0, F.zero_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact ha0 (congrArg Subtype.val h).symm
    · intro h
      exact hb0 (congrArg Subtype.val h).symm
    · intro h
      exact hab (congrArg Subtype.val h)
  rw [← Nat.card_eq_fintype_card] at h3
  omega

theorem Hyp2813.card_comm_le (h : Hyp2813 X K R P) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) (hι : IsTBridge X ψ ι) (hN2 : ∀ n : N, n + n = 0)
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n)
    (hDX : D ≤ X) (hd₀D : d₀ ∈ D) (hD : D = zpowers d₀) (hd₀3 : orderOf d₀ = 3)
    (hi : Nat.card (commSub M (zpowers (ψ ⟨d₀, hDX hd₀D⟩))) ≤ 16) :
    Nat.card ↥⁅omegaCenter (pCoreOf 2 P), D⁆ ≤ 16 := by
  classical
  have hdbar3 : orderOf (ψ ⟨d₀, hDX hd₀D⟩) = 3 := dbar_order X hψk (hDX hd₀D) hd₀3
  obtain ⟨W, hWmem⟩ :=
    tr_exists_sub hι (commSub N (zpowers (ψ ⟨d₀, hDX hd₀D⟩)))
  have hVT : omegaCenter (pCoreOf 2 P) ≤ TT X := fun v hv => (h.mem_omegaCenter_S_iff.1 hv).1
  have hcomm : ∀ v ∈ omegaCenter (pCoreOf 2 P), ∀ d ∈ D,
      ∃ hc : v * d * v⁻¹ * d⁻¹ ∈ TT X,
        ι ⟨v * d * v⁻¹ * d⁻¹, hc⟩ ∈ commSub N (zpowers (ψ ⟨d₀, hDX hd₀D⟩)) := by
    intro v hv d hd
    have hvT : v ∈ TT X := hVT hv
    have hdX : d ∈ X := hDX hd
    have hc0 : d * v⁻¹ * d⁻¹ ∈ TT X :=
      tr_conj_mem_TT (Subgroup.le_normalizer hdX) ((TT X).inv_mem hvT)
    have e2 : v * d * v⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
    have hc' : v * (d * v * d⁻¹)⁻¹ ∈ TT X := by
      have e : v * (d * v * d⁻¹)⁻¹ = v * (d * v⁻¹ * d⁻¹) := by group
      rw [e]
      exact (TT X).mul_mem hvT hc0
    have hc : v * d * v⁻¹ * d⁻¹ ∈ TT X := by
      rw [e2]
      exact hc'
    refine ⟨hc, ?_⟩
    have heq : (⟨v * d * v⁻¹ * d⁻¹, hc⟩ : ↥(TT X)) = ⟨v * (d * v * d⁻¹)⁻¹, hc'⟩ :=
      Subtype.ext e2
    rw [heq, hι.map_commutator ⟨d, hdX⟩ ⟨v, hvT⟩ hc']
    have hg : ψ ⟨d, hdX⟩ ∈ zpowers (ψ ⟨d₀, hDX hd₀D⟩) := tr_psi_mem_zpowers hD hDX hd₀D hd
    have hmem : ψ ⟨d, hdX⟩ • ι ⟨v, hvT⟩ - ι ⟨v, hvT⟩ ∈
        commSub N (zpowers (ψ ⟨d₀, hDX hd₀D⟩)) :=
      AddSubgroup.subset_closure ⟨ψ ⟨d, hdX⟩, hg, ι ⟨v, hvT⟩, rfl⟩
    rw [← neg_sub]
    exact neg_mem hmem
  have hle : (⁅omegaCenter (pCoreOf 2 P), D⁆ : Subgroup A) ≤ TT X := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    exact (hcomm v hv d hd).1
  have hW : (⁅omegaCenter (pCoreOf 2 P), D⁆ : Subgroup A) ≤ W.map (TT X).subtype := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    obtain ⟨hc, hιc⟩ := hcomm v hv d hd
    exact ⟨⟨v * d * v⁻¹ * d⁻¹, hc⟩, (hWmem _).2 hιc, rfl⟩
  let f : ↥(⁅omegaCenter (pCoreOf 2 P), D⁆ : Subgroup A) →
      ↥(commSub N (zpowers (ψ ⟨d₀, hDX hd₀D⟩))) := fun u =>
    ⟨ι ⟨u, hle u.2⟩, by
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 (hW u.2)
      have hweq : (⟨u, hle u.2⟩ : ↥(TT X)) = w := Subtype.ext hwu.symm
      rw [hweq]
      exact (hWmem w).1 hw⟩
  have hf : Function.Injective f := by
    intro u u' huu'
    have h1 : ι ⟨u, hle u.2⟩ = ι ⟨u', hle u'.2⟩ := congrArg Subtype.val huu'
    have h2 := hι.bij.1 h1
    have h3 : (u : A) = u' := congrArg (fun t : ↥(TT X) => (t : A)) h2
    exact Subtype.ext h3
  calc Nat.card ↥⁅omegaCenter (pCoreOf 2 P), D⁆
      ≤ Nat.card ↥(commSub N (zpowers (ψ ⟨d₀, hDX hd₀D⟩))) := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card ↥(commSub M (zpowers (ψ ⟨d₀, hDX hd₀D⟩))) :=
        card_commSub_le_of_quot hπk hπe hN2 hdbar3
    _ ≤ 16 := hi

theorem Hyp2813.V1_le_T0 (h : Hyp2813 X K R P) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) (hι : IsTBridge X ψ ι) (hN2 : ∀ n : N, n + n = 0)
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n)
    (hDX : D ≤ X) (hd₀D : d₀ ∈ D) (hD : D = zpowers d₀) (hd₀3 : orderOf d₀ = 3)
    (hiii : (∃ m ∈ fixSub M (Hbar X ψ (pCoreOf 2 P)), (ψ ⟨d₀, hDX hd₀D⟩) • m ≠ m) →
      fixSub M (Hbar X ψ (pCoreOf 2 P) ⊔ zpowers (ψ ⟨d₀, hDX hd₀D⟩)) = ⊥)
    {z : A} (hz : z ∈ omegaCenter R) (hzD : ∃ d ∈ D, z * d ≠ d * z)
    {v : A} (hv : v ∈ omegaCenter (pCoreOf 2 P)) (hvD : ∀ d ∈ D, v * d = d * v) :
    v ∈ T0 X := by
  have hdbar3 : orderOf (ψ ⟨d₀, hDX hd₀D⟩) = 3 := dbar_order X hψk (hDX hd₀D) hd₀3
  obtain ⟨hzT, hzR⟩ := h.mem_omegaCenter_R_iff.1 hz
  have hSX : pCoreOf 2 P ≤ X := (pCoreOf_le_self P).trans h.P_le
  have hd₀X : d₀ ∈ X := hDX hd₀D
  have hd₀N : d₀ ∈ normalizer (X : Set A) := Subgroup.le_normalizer hd₀X
  have hzd₀ : z * d₀ ≠ d₀ * z := by
    intro hc
    obtain ⟨d, hd, hne⟩ := hzD
    rw [hD] at hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact hne (Commute.zpow_right (show Commute z d₀ from hc) k)
  have hzfix : ι ⟨z, hzT⟩ ∈ fixSub N (Hbar X ψ (pCoreOf 2 P)) :=
    (hι.mem_fixSub_iff hSX ⟨z, hzT⟩).2 fun x hx => hzR x (h.pCore_P_le_R hx)
  have hzmove : ψ ⟨d₀, hd₀X⟩ • ι ⟨z, hzT⟩ ≠ ι ⟨z, hzT⟩ := by
    intro heq
    have hc : d₀ * z * d₀⁻¹ ∈ TT X := tr_conj_mem_TT hd₀N hzT
    have h1 := hι.equiv ⟨d₀, hd₀X⟩ ⟨z, hzT⟩ hc
    rw [heq] at h1
    have h2 := hι.bij.1 h1
    have h3 : d₀ * z * d₀⁻¹ = z := congrArg Subtype.val h2
    have h4 : d₀ * z = z * d₀ := by
      calc d₀ * z = (d₀ * z * d₀⁻¹) * d₀ := by group
        _ = z * d₀ := by rw [h3]
    exact hzd₀ h4.symm
  have hne : ∃ m ∈ fixSub M (Hbar X ψ (pCoreOf 2 P)), (ψ ⟨d₀, hDX hd₀D⟩) • m ≠ m :=
    ⟨π (ι ⟨z, hzT⟩), tr_pi_mem_fixSub hπe hzfix,
      smul_ne_of_quot hπk hπe hN2 hdbar3 hzmove⟩
  have hF := hiii hne
  have hvT : v ∈ TT X := (h.mem_omegaCenter_S_iff.1 hv).1
  have hπv := tr_pi_mem_F (π := π) h hι hπe hDX hd₀D hv hvD hvT
  rw [hF] at hπv
  have hπv0 : π (ι ⟨v, hvT⟩) = 0 := (AddSubgroup.mem_bot).1 hπv
  exact (tr_pi_eq_zero_iff hι hψs hπk hvT).1 hπv0

theorem Hyp2813.comm_mem_T0 (h : Hyp2813 X K R P) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) (hι : IsTBridge X ψ ι) (hN2 : ∀ n : N, n + n = 0)
    (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤) (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n)
    (hDX : D ≤ X) (hd₀D : d₀ ∈ D) (hD : D = zpowers d₀) (hd₀3 : orderOf d₀ = 3)
    (hii : Nat.card (fixSub M (Hbar X ψ (pCoreOf 2 P) ⊔ zpowers (ψ ⟨d₀, hDX hd₀D⟩))) ≤ 2)
    {y : A} (hyX : y ∈ normalizer (X : Set A)) (hyS : y ∈ normalizer (pCoreOf 2 P : Set A))
    (hyD : ∀ d ∈ D, y * d = d * y)
    {v : A} (hv : v ∈ omegaCenter (pCoreOf 2 P)) (hvD : ∀ d ∈ D, v * d = d * v) :
    v * y * v⁻¹ * y⁻¹ ∈ T0 X := by
  have hyN' : y ∈ normalizer (omegaCenter (pCoreOf 2 P) : Set A) :=
    normalizer_le_normalizer_omegaCenter _ hyS
  have hu : y * v * y⁻¹ ∈ omegaCenter (pCoreOf 2 P) :=
    (Subgroup.mem_normalizer_iff.1 hyN' v).1 hv
  have huD : ∀ d ∈ D, (y * v * y⁻¹) * d = d * (y * v * y⁻¹) := by
    intro d hd
    have h1 := hyD d hd
    have h2 := hvD d hd
    have h3 : y⁻¹ * d = d * y⁻¹ := by
      calc y⁻¹ * d = y⁻¹ * (d * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * d) * y⁻¹ := by rw [h1]
        _ = d * y⁻¹ := by group
    calc (y * v * y⁻¹) * d = y * v * (y⁻¹ * d) := by group
      _ = y * v * (d * y⁻¹) := by rw [h3]
      _ = y * (v * d) * y⁻¹ := by group
      _ = y * (d * v) * y⁻¹ := by rw [h2]
      _ = (y * d) * v * y⁻¹ := by group
      _ = (d * y) * v * y⁻¹ := by rw [h1]
      _ = d * (y * v * y⁻¹) := by group
  have hvT : v ∈ TT X := (h.mem_omegaCenter_S_iff.1 hv).1
  have huT : y * v * y⁻¹ ∈ TT X := (h.mem_omegaCenter_S_iff.1 hu).1
  have hvF := tr_pi_mem_F (π := π) h hι hπe hDX hd₀D hv hvD hvT
  have huF := tr_pi_mem_F (π := π) h hι hπe hDX hd₀D hu huD huT
  have hiff : v ∈ T0 X ↔ y * v * y⁻¹ ∈ T0 X := by
    refine ⟨fun hv0 => tr_conj_mem_T0 hyX hv0, fun hu0 => ?_⟩
    have := tr_conj_mem_T0 ((normalizer (X : Set A)).inv_mem hyX) hu0
    simpa [mul_assoc] using this
  have hclaim : π (ι ⟨v, hvT⟩) = π (ι ⟨y * v * y⁻¹, huT⟩) := by
    by_cases ha : π (ι ⟨v, hvT⟩) = 0
    · have hv0 : v ∈ T0 X := (tr_pi_eq_zero_iff hι hψs hπk hvT).1 ha
      have hu0 : y * v * y⁻¹ ∈ T0 X := hiff.1 hv0
      rw [ha, (tr_pi_eq_zero_iff hι hψs hπk huT).2 hu0]
    · have hb : π (ι ⟨y * v * y⁻¹, huT⟩) ≠ 0 := fun hb0 =>
        ha ((tr_pi_eq_zero_iff hι hψs hπk hvT).2
          (hiff.2 ((tr_pi_eq_zero_iff hι hψs hπk huT).1 hb0)))
      exact tr_eq_of_card_le_two _ hii hvF huF ha hb
  have ht0 : π (ι ((⟨v, hvT⟩ : ↥(TT X)) * (⟨y * v * y⁻¹, huT⟩ : ↥(TT X))⁻¹)) = 0 := by
    rw [tr_iota_mul_inv hι, map_sub, hclaim, sub_self]
  have hmem := (hι.mem_fixSub_top_iff hψs
    ((⟨v, hvT⟩ : ↥(TT X)) * (⟨y * v * y⁻¹, huT⟩ : ↥(TT X))⁻¹)).1 ((hπk _).1 ht0)
  have e : v * y * v⁻¹ * y⁻¹ = v * (y * v * y⁻¹)⁻¹ := by group
  rw [e]
  exact hmem

end Transfer

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

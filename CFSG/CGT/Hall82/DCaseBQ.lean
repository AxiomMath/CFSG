module

public import CFSG.CGT.Hall82.DBasic
public import CFSG.GroupTheory.StabilizerSeriesThree
public import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
public import CFSG.CGT.Hall82.Fusion

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

@[expose] noncomputable def fiveCent (rep : Fin 64 → G) : Subgroup G :=
  Subgroup.centralizer ({rep 5} : Set G)

@[expose] noncomputable def fiveQ (rep : Fin 64 → G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (fiveCent rep)

private theorem commute_of_mem_fiveCent
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {g : G}
    (hg : g ∈ fiveCent rep) : g * rep 5 = rep 5 * g :=
  (Subgroup.mem_centralizer_iff.mp hg (rep 5) (by simp)).symm

private theorem blockU_le_fiveCent (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    blockU L ≤ fiveCent rep := by
  intro x hx
  rw [fiveCent, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact (S.blockU_comm hx (hc.mem 5)).symm

private theorem normalizer_zpowers_of_commute {a b : G} (h : a * b = b * a) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  simp only [MulAut.conj_apply, MonoidHom.coe_coe]
  rw [show a * b * a⁻¹ = b from by rw [h]; group]

private theorem zpowers_five_le_fiveQ
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    Subgroup.zpowers (rep 5) ≤ fiveQ rep := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · refine Subgroup.zpowers_le.mpr ?_
    rw [fiveCent, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rfl
  · intro h hh
    exact normalizer_zpowers_of_commute (commute_of_mem_fiveCent hc hh)
  · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using rep_mul_self hc 5)

private theorem fiveQ_le_fiveCent (rep : Fin 64 → G) : fiveQ rep ≤ fiveCent rep :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 _

private theorem fiveQ_isPGroup (rep : Fin 64 → G) : IsPGroup 2 (fiveQ rep) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

private theorem fiveCent_normalizes_fiveQ (rep : Fin 64 → G) :
    fiveCent rep ≤ Subgroup.normalizer (fiveQ rep : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

private theorem conj_mem_fiveQ {g q : G} (hg : g ∈ fiveCent rep) (hq : q ∈ fiveQ rep) :
    g * q * g⁻¹ ∈ fiveQ rep :=
  (Subgroup.mem_normalizer_iff.mp (fiveCent_normalizes_fiveQ rep hg) q).mp hq

private theorem le_fiveQ_of_normal {K : Subgroup G} (hKH : K ≤ fiveCent rep)
    (hKn : ∀ h ∈ fiveCent rep, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hKp : IsPGroup 2 K) :
    K ≤ fiveQ rep := by
  have hKn' : fiveCent rep ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hk => hKn h hh x hk, fun hk => ?_⟩
    have h1 := hKn h⁻¹ ((fiveCent rep).inv_mem hh) (h * x * h⁻¹) hk
    simpa [mul_assoc] using h1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hKn' hKp

theorem pCoreOf_centralizer_five_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    fiveQ rep ≤ M := by
  have ht : rep 5 ∈ CFSG.Open.pCoreOf 2 M := by
    rw [S.pCoreOf_eq_blockU hF hc hC1]
    exact hc.mem 5
  simpa [fiveQ, fiveCent] using
    S.pCoreOf_centralizer_singleton_le (t := rep 5) hF hc
      (S.hW2_of_eq_bot hC1) (S.hWab_of_eq_bot hC1) ht

private theorem inf_centralizer_fiveQ_le (S : Setting G M L)
    (hF : ModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    fiveCent rep ⊓ Subgroup.centralizer (fiveQ rep : Set G) ≤ fiveQ rep := by
  have ht : rep 5 ∈ CFSG.Open.pCoreOf 2 M := by
    rw [S.pCoreOf_eq_blockU hF hc hC1]
    exact hc.mem 5
  have ht1 : rep 5 ≠ 1 := by
    intro h
    exact absurd ((rep_eq_one_iff hc).mp h) (by decide)
  exact CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
    (Y := fiveCent rep) (S.cent (rep 5) ht ht1)

private theorem mem_fiveQ_of_commute (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {h : G} (hh : h ∈ fiveCent rep)
    (hcomm : ∀ q ∈ fiveQ rep, h * q = q * h) : h ∈ fiveQ rep := by
  refine inf_centralizer_fiveQ_le S hF hc hC1 (Subgroup.mem_inf.mpr ⟨hh, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (hcomm q hq).symm

private theorem commutator_eq_rep (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {q : G} (hqM : q ∈ M)
    (v : Fin 64) :
    rep v * q * (rep v)⁻¹ * q⁻¹ =
      rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) := by
  have h1 : (rep v * q * (rep v)⁻¹ * q⁻¹)⁻¹ =
      rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) := by
    calc (rep v * q * (rep v)⁻¹ * q⁻¹)⁻¹
        = q * rep v * q⁻¹ * (rep v)⁻¹ := by group
      _ = q * rep v * q⁻¹ * rep v := by
          rw [inv_eq_of_mul_eq_one_right (rep_mul_self hc v)]
      _ = rep (S.psiM hc ⟨q, hqM⟩ v) * rep v := by
          rw [S.rep_psiM hc ⟨q, hqM⟩ v]
      _ = rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) := (hc.add _ v).symm
  calc rep v * q * (rep v)⁻¹ * q⁻¹
      = ((rep v * q * (rep v)⁻¹ * q⁻¹)⁻¹)⁻¹ := by group
    _ = rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) := by
        rw [h1, inv_eq_of_mul_eq_one_right (rep_mul_self hc _)]

private theorem exists_mem_L_fiveCent (S : Setting G M L)
    (hF : ModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    {a : Equiv.Perm (Fin 64)} (ha : a ∈ hexaL) (ha5 : a 5 = 5) :
    ∃ m : ↥M, (m : G) ∈ L ∧ (m : G) ∈ fiveCent rep ∧ S.psiM hc m = a := by
  obtain ⟨m, hmL, hmψ⟩ := S.exists_mem_L_psiM_eq hF hc ha
  refine ⟨m, hmL, ?_, hmψ⟩
  rw [fiveCent, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  have hconj : (m : G) * rep 5 * (m : G)⁻¹ = rep 5 :=
    (conj_rep_eq_iff S hc m 5).mpr (by rw [hmψ, ha5])
  calc rep 5 * (m : G) = ((m : G) * rep 5 * (m : G)⁻¹) * (m : G) := by rw [hconj]
    _ = (m : G) * rep 5 := by group

private theorem conj_rep_mem_fiveQ (S : Setting G M L)
    (hF : ModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    {a : Equiv.Perm (Fin 64)} (ha : a ∈ hexaL) (ha5 : a 5 = 5) {w : Fin 64}
    (hw : rep w ∈ fiveQ rep) : rep (a w) ∈ fiveQ rep := by
  obtain ⟨m, -, hmH, hmψ⟩ := exists_mem_L_fiveCent S hF hc ha ha5
  have hnorm : (m : G) ∈ Subgroup.normalizer (fiveQ rep : Set G) :=
    fiveCent_normalizes_fiveQ rep hmH
  have hconj : (m : G) * rep w * (m : G)⁻¹ ∈ fiveQ rep :=
    (Subgroup.mem_normalizer_iff.mp hnorm (rep w)).mp hw
  have hrep : rep (a w) = (m : G) * rep w * (m : G)⁻¹ := by
    rw [← hmψ]
    exact S.rep_psiM hc m w
  rw [hrep]
  exact hconj

private theorem conj_mem_psiSub_of_mem_hexaL_fiveCent (S : Setting G M L)
    (hF : ModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    {A : Subgroup G} (hAM : A ≤ M)
    (hAn : ∀ g ∈ fiveCent rep, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {a : Equiv.Perm (Fin 64)} (ha : a ∈ hexaL) (ha5 : a 5 = 5) :
    ∀ b ∈ S.psiSub hc A, a * b * a⁻¹ ∈ S.psiSub hc A := by
  obtain ⟨m, hmL, hmH, hmψ⟩ := exists_mem_L_fiveCent S hF hc ha ha5
  have hmM : (m : G) ∈ M := S.le hmL
  intro b hb
  rw [mem_psiSub S hc hAM] at hb ⊢
  obtain ⟨x, hxA, hxM, rfl⟩ := hb
  have hx' : (m : G) * x * (m : G)⁻¹ ∈ A := hAn (m : G) hmH x hxA
  have hxM' : (m : G) * x * (m : G)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hmM hxM) (M.inv_mem hmM)
  refine ⟨(m : G) * x * (m : G)⁻¹, hx', hxM', ?_⟩
  have harg : (⟨(m : G) * x * (m : G)⁻¹, hxM'⟩ : ↥M) =
      m * ⟨x, hxM⟩ * m⁻¹ := Subtype.ext rfl
  rw [harg]
  simp only [map_mul, map_inv, hmψ]

theorem psiSub_pCoreOf_le (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    S.psiSub hc (fiveQ rep) ≤ hallRM := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  refine hD.le_rm _ (S.psiSub_le_hexaM hc _)
    (S.isPGroup_psiSub hc (fiveQ_isPGroup rep)) ?_ ?_
  · intro b hb
    rw [mem_psiSub S hc hQM] at hb
    obtain ⟨q, hq, hqM, rfl⟩ := hb
    refine (conj_rep_eq_iff S hc ⟨q, hqM⟩ 5).mp ?_
    have hcomm : q * rep 5 = rep 5 * q :=
      commute_of_mem_fiveCent hc (fiveQ_le_fiveCent rep hq)
    calc q * rep 5 * q⁻¹ = rep 5 * q * q⁻¹ := by rw [hcomm]
      _ = rep 5 := by group
  · intro a ha ha5 b hb
    exact conj_mem_psiSub_of_mem_hexaL_fiveCent S hF hc hQM
      (fun g hg q hq => conj_mem_fiveQ hg hq)
      ha ha5 b hb

theorem rep_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {u : Fin 64} (hu : InHallU u) :
    rep u ∈ fiveQ rep := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hHZ : ∀ h ∈ fiveCent rep, ∀ z ∈ Subgroup.zpowers (rep 5),
      h * z * h⁻¹ ∈ Subgroup.zpowers (rep 5) := by
    intro h hh z hz
    exact (Subgroup.mem_normalizer_iff.mp
      (normalizer_zpowers_of_commute (commute_of_mem_fiveCent hc hh)) z).mp hz
  have hkH : rep u ∈ fiveCent rep := blockU_le_fiveCent S hc (hc.mem u)
  have hkZ : ∀ z ∈ Subgroup.zpowers (rep 5), rep u * z * (rep u)⁻¹ = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm : rep u * rep 5 = rep 5 * rep u := S.blockU_comm (hc.mem u) (hc.mem 5)
    calc rep u * rep 5 ^ k * (rep u)⁻¹
        = (rep u * rep 5 * (rep u)⁻¹) ^ k := (conj_zpow (i := k)).symm
      _ = rep 5 ^ k := by
          rw [show rep u * rep 5 * (rep u)⁻¹ = rep 5 from by rw [hcomm]; group]
  have hkQ : ∀ q ∈ fiveQ rep,
      rep u * q * (rep u)⁻¹ * q⁻¹ ∈ Subgroup.zpowers (rep 5) := by
    intro q hq
    have hqM : q ∈ M := hQM hq
    have hψq : S.psiM hc ⟨q, hqM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨q, hqM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨q, hq, hqM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    obtain ⟨e, he⟩ := (hD.mem_rm_iff _).mp hψq
    rw [commutator_eq_rep S hc hqM u, ← he]
    rcases hD.rm_comm_u e u hu with h | h
    · rw [h, hc.rep_zero]
      exact (Subgroup.zpowers (rep 5)).one_mem
    · rw [h]
      exact Subgroup.mem_zpowers (rep 5)
  exact CFSG.GroupTheory.mem_of_stabilizes_two (p := 2) (fiveQ_isPGroup rep)
    (zpowers_five_le_fiveQ hc) (fun h hh => mem_fiveQ_of_commute S hF hc hC1 hh)
    (fun h hh q hq => conj_mem_fiveQ hh hq) hHZ (fun K hKH => le_fiveQ_of_normal hKH)
    hkH hkZ hkQ

theorem rep_mem_pCoreOf_iff (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) (v : Fin 64) :
    rep v ∈ fiveQ rep ↔ InHallU v := by
  constructor
  · intro hv
    let W : Set (Fin 64) := {w | rep w ∈ fiveQ rep}
    have hWadd : ∀ a ∈ W, ∀ b ∈ W, xorF a b ∈ W := by
      intro a ha b hb
      show rep (xorF a b) ∈ fiveQ rep
      rw [hc.add]
      exact (fiveQ rep).mul_mem ha hb
    have hWU : ∀ w, InHallU w → w ∈ W := fun w hw =>
      rep_mem_pCoreOf S hF hD hc hC1 hw
    have hWinv : ∀ a ∈ hexaL, a 5 = 5 → ∀ w ∈ W, a w ∈ W := by
      intro a ha ha5 w hw
      exact conj_rep_mem_fiveQ S hF hc hC1 ha ha5 hw
    have hvW : v ∈ W := hv
    rcases hD.u_maximal W hWadd hWU hWinv with hW | hW
    · rw [hW] at hvW
      exact hvW
    · exfalso
      have hVQ : blockU L ≤ fiveQ rep := by
        intro x hx
        obtain ⟨w, rfl⟩ := (mem_blockU_iff hc).mp hx
        have hw : w ∈ W := by rw [hW]; exact Set.mem_univ w
        exact hw
      have ht : rep 5 ∈ CFSG.Open.pCoreOf 2 M := by
        rw [S.pCoreOf_eq_blockU hF hc hC1]
        exact hc.mem 5
      have hHM : fiveCent rep ≤ M := by
        intro g hg
        let A : Subgroup G := (blockU L).map (MulAut.conj g).toMonoidHom
        have hAQ : A ≤ fiveQ rep := by
          intro x hx
          rw [show A = (blockU L).map (MulAut.conj g).toMonoidHom from rfl,
            Subgroup.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have hyQ : y ∈ fiveQ rep := hVQ hy
          have hnorm : g ∈ Subgroup.normalizer (fiveQ rep : Set G) :=
            fiveCent_normalizes_fiveQ rep hg
          have h := (Subgroup.mem_normalizer_iff.mp hnorm y).mp hyQ
          simpa [MulAut.conj_apply] using h
        have hQle : fiveQ rep ≤ CFSG.Open.pCoreOf 2 (M ⊓ fiveCent rep) := by
          refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
            (fiveQ_isPGroup rep)
          · exact le_inf (pCoreOf_centralizer_five_le S hF hc hC1) (fiveQ_le_fiveCent rep)
          · intro m hm
            exact fiveCent_normalizes_fiveQ rep hm.2
        have hA : A ≤ CFSG.Open.pCoreOf 2 (M ⊓ fiveCent rep) := hAQ.trans hQle
        have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
          intro a ha b hb
          rw [show A = (blockU L).map (MulAut.conj g).toMonoidHom from rfl,
            Subgroup.mem_map] at ha hb
          obtain ⟨a0, ha0, rfl⟩ := ha
          obtain ⟨b0, hb0, rfl⟩ := hb
          calc g * a0 * g⁻¹ * (g * b0 * g⁻¹) = g * (a0 * b0) * g⁻¹ := by group
            _ = g * (b0 * a0) * g⁻¹ := by rw [S.blockU_comm ha0 hb0]
            _ = (g * b0 * g⁻¹) * (g * a0 * g⁻¹) := by group
        have hAcard : Nat.card A = 64 := by
          rw [show A = (blockU L).map (MulAut.conj g).toMonoidHom from rfl,
            Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_blockU]
        have hJcard : Nat.card (CFSG.Open.pCoreOf 2 M) = 64 := by
          rw [S.pCoreOf_eq_blockU hF hc hC1, S.card_blockU]
        have hcard : Nat.card (CFSG.Open.pCoreOf 2 M) ≤ Nat.card A := by omega
        have hAeqJ := S.eq_of_le_pCoreOf_centralizer hF hc
          (S.hW2_of_eq_bot hC1) (S.hWab_of_eq_bot hC1) ht hA hAab hcard
        have hAeqV : A = blockU L := by
          rw [hAeqJ, S.pCoreOf_eq_blockU hF hc hC1]
        have hAnorm : g ∈ Subgroup.normalizer (blockU L : Set G) :=
          (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (by simpa [A] using hAeqV)
        rwa [S.normalizer_blockU_eq] at hAnorm
      exact hcM hHM
  · intro hu
    exact rep_mem_pCoreOf S hF hD hc hC1 hu

private theorem hallRM_comm (hD : DModelFacts) {x y : Equiv.Perm (Fin 64)}
    (hx : x ∈ hallRM) (hy : y ∈ hallRM) : x * y = y * x := by
  obtain ⟨e, rfl⟩ := (hD.mem_rm_iff x).mp hx
  obtain ⟨f, rfl⟩ := (hD.mem_rm_iff y).mp hy
  have h : xor8 e f = xor8 f e := Fin.ext (Nat.xor_comm e.val f.val)
  rw [hD.rm_mul, hD.rm_mul, h]

private theorem hallRMPerm_zero (hD : DModelFacts) : hallRMPerm 0 = 1 := by
  have h00 : xor8 (0 : Fin 8) 0 = 0 := by
    apply Fin.ext
    simp [xor8]
  have h1 : hallRMPerm 0 * hallRMPerm 0 = hallRMPerm 0 := by
    simpa [h00] using hD.rm_mul 0 0
  have h1' : hallRMPerm 0 * hallRMPerm 0 = 1 * hallRMPerm 0 := by
    simpa using h1
  exact (mul_right_inj (hallRMPerm 0)).mp h1'

private theorem card_hallRM (hD : DModelFacts) : Nat.card hallRM = 8 := by
  calc Nat.card hallRM = Nat.card (Set.range hallRMPerm) :=
        Nat.card_congr ((Equiv.refl (Equiv.Perm (Fin 64))).subtypeEquiv (fun x => hD.mem_rm_iff x))
    _ = Nat.card (Fin 8) := (Nat.card_congr (Equiv.ofInjective hallRMPerm hD.rm_inj)).symm
    _ = 8 := Nat.card_fin 8

private theorem card_inHallU : Nat.card {v : Fin 64 // InHallU v} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem false_of_quadratic (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) {Q₀ : Subgroup G}
    (hQ₀n : ∀ g ∈ fiveCent rep, ∀ q ∈ Q₀, g * q * g⁻¹ ∈ Q₀)
    (hUQ₀ : ∀ u, InHallU u → rep u ∈ Q₀)
    (hQ₀Q : Q₀ ≤ fiveQ rep)
    (hquad : ∀ a ∈ S.psiSub hc Q₀, ∀ b ∈ S.psiSub hc Q₀, ∀ v,
      xorF (xorF (a (b v)) (a v)) (xorF (b v) v) = 0) : False := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hQ₀M : Q₀ ≤ M := hQ₀Q.trans hQM
  let Z : Subgroup G := Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G)
  have hZQ₀ : Z ≤ Q₀ := inf_le_left
  have hZQ : Z ≤ fiveQ rep := hZQ₀.trans hQ₀Q
  have hHZ : ∀ h ∈ fiveCent rep, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z := by
    intro h hh z hz
    refine Subgroup.mem_inf.mpr ⟨hQ₀n h hh z hz.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : h⁻¹ * q * h ∈ Q₀ := by
      have h1 := hQ₀n h⁻¹ ((fiveCent rep).inv_mem hh) q hq
      simpa [mul_assoc] using h1
    have hzq : (h⁻¹ * q * h) * z = z * (h⁻¹ * q * h) :=
      Subgroup.mem_centralizer_iff.mp hz.2 (h⁻¹ * q * h) hq'
    calc q * (h * z * h⁻¹) = h * ((h⁻¹ * q * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * q * h)) * h⁻¹ := by rw [hzq]
      _ = (h * z * h⁻¹) * q := by group
  have hkQ : ∀ v, ∀ q ∈ fiveQ rep, rep v * q * (rep v)⁻¹ * q⁻¹ ∈ Q₀ := by
    intro v q hq
    have hqM : q ∈ M := hQM hq
    have hvH : rep v ∈ fiveCent rep := blockU_le_fiveCent S hc (hc.mem v)
    have hconj : rep v * q * (rep v)⁻¹ ∈ fiveQ rep := conj_mem_fiveQ hvH hq
    have hxQ : rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) ∈ fiveQ rep := by
      rw [← commutator_eq_rep S hc hqM v]
      exact (fiveQ rep).mul_mem hconj ((fiveQ rep).inv_mem hq)
    have hxU : InHallU (xorF (S.psiM hc ⟨q, hqM⟩ v) v) :=
      (rep_mem_pCoreOf_iff S hF hD hc hC1 hcM _).mp hxQ
    rw [commutator_eq_rep S hc hqM v]
    exact hUQ₀ _ hxU
  have hkQ₀ : ∀ v, ∀ q ∈ Q₀, rep v * q * (rep v)⁻¹ * q⁻¹ ∈ Z := by
    intro v q hq
    have hqM : q ∈ M := hQ₀M hq
    have hvH : rep v ∈ fiveCent rep := blockU_le_fiveCent S hc (hc.mem v)
    have hnorm : rep v ∈ Subgroup.normalizer (Q₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hQ₀n (rep v) hvH x hx, fun hx => ?_⟩
      have h1 := hQ₀n (rep v)⁻¹ ((fiveCent rep).inv_mem hvH) (rep v * x * (rep v)⁻¹) hx
      simpa [mul_assoc] using h1
    have hxQ₀ : rep v * q * (rep v)⁻¹ * q⁻¹ ∈ Q₀ :=
      Q₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm q).mp hq) (Q₀.inv_mem hq)
    refine Subgroup.mem_inf.mpr ⟨hxQ₀, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrM : r ∈ M := hQ₀M hr
    have hψq : S.psiM hc ⟨q, hqM⟩ ∈ S.psiSub hc Q₀ := by
      rw [mem_psiSub S hc hQ₀M]
      exact ⟨q, hq, hqM, rfl⟩
    have hψr : S.psiM hc ⟨r, hrM⟩ ∈ S.psiSub hc Q₀ := by
      rw [mem_psiSub S hc hQ₀M]
      exact ⟨r, hr, hrM, rfl⟩
    have hzero : xorF (S.psiM hc ⟨r, hrM⟩
        (xorF (S.psiM hc ⟨q, hqM⟩ v) v))
        (xorF (S.psiM hc ⟨q, hqM⟩ v) v) = 0 := by
      rw [S.psiM_xorF hc ⟨r, hrM⟩]
      exact hquad _ hψr _ hψq v
    have hcomm : rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) * r *
        (rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v))⁻¹ * r⁻¹ = 1 := by
      rw [commutator_eq_rep S hc hrM, hzero, hc.rep_zero]
    have hrcomm : r * rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) =
        rep (xorF (S.psiM hc ⟨q, hqM⟩ v) v) * r :=
      (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
    rw [commutator_eq_rep S hc hqM v]
    exact hrcomm
  have hkZ : ∀ v, ∀ z ∈ Z, rep v * z * (rep v)⁻¹ = z := by
    intro v z hz
    have hzQ : z ∈ fiveQ rep := hZQ hz
    have hzQ₀ : z ∈ Q₀ := hz.1
    have hzM : z ∈ M := hQM hzQ
    have hψz : S.psiM hc ⟨z, hzM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨z, hzM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨z, hzQ, hzM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    obtain ⟨e, he⟩ := (hD.mem_rm_iff _).mp hψz
    have hfix : ∀ u, InHallU u → hallRMPerm e u = u := by
      intro u hu
      have hrep : rep u ∈ Q₀ := hUQ₀ u hu
      have hconj : z * rep u * z⁻¹ = rep u := by
        have hcent := Subgroup.mem_centralizer_iff.mp hz.2 (rep u) hrep
        calc z * rep u * z⁻¹ = rep u * z * z⁻¹ := by rw [← hcent]
          _ = rep u := by group
      have h1 : rep (hallRMPerm e u) = rep u := by
        rw [he, S.rep_psiM hc ⟨z, hzM⟩ u]
        exact hconj
      exact hc.inj h1
    have he0 : e = 0 := hD.rm_eq_zero_of_fix_u e hfix
    have hψz1 : S.psiM hc ⟨z, hzM⟩ = 1 := by
      rw [← he, he0]
      exact hallRMPerm_zero hD
    have hzV : z ∈ blockU L :=
      (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨z, hzM⟩).mp hψz1
    have hcomm : rep v * z = z * rep v := (S.blockU_comm hzV (hc.mem v)).symm
    calc rep v * z * (rep v)⁻¹ = z * rep v * (rep v)⁻¹ := by rw [hcomm]
      _ = z := by group
  have hall : ∀ v : Fin 64, rep v ∈ fiveQ rep := by
    intro v
    have hvH : rep v ∈ fiveCent rep := blockU_le_fiveCent S hc (hc.mem v)
    exact CFSG.GroupTheory.mem_of_stabilizes_three (p := 2) (fiveQ_isPGroup rep)
      hZQ₀ hQ₀Q (fun h hh => mem_fiveQ_of_commute S hF hc hC1 hh)
      (fun h hh q hq => conj_mem_fiveQ hh hq) hQ₀n hHZ (fun K hKH => le_fiveQ_of_normal hKH)
      hvH (hkZ v) (hkQ₀ v) (hkQ v)
  have hVQ : blockU L ≤ fiveQ rep := by
    intro x hx
    obtain ⟨v, rfl⟩ := (mem_blockU_iff hc).mp hx
    exact hall v
  have h2 : rep 2 ∈ fiveQ rep := hall 2
  have h2U : InHallU 2 := (rep_mem_pCoreOf_iff S hF hD hc hC1 hcM 2).mp h2
  exact absurd h2U (by decide)

private theorem mem_fiveQ_inf_blockU_iff (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) {x : G} :
    x ∈ fiveQ rep ⊓ blockU L ↔ ∃ u, InHallU u ∧ rep u = x := by
  constructor
  · intro hx
    obtain ⟨hxQ, hxV⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨v, rfl⟩ := (mem_blockU_iff hc).mp hxV
    exact ⟨v, (rep_mem_pCoreOf_iff S hF hD hc hC1 hcM v).mp hxQ, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨rep_mem_pCoreOf S hF hD hc hC1 hu, hc.mem u⟩

private theorem card_fiveQ_inf_blockU (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) :
    Nat.card ↥(fiveQ rep ⊓ blockU L) = 16 := by
  refine (Nat.card_congr ?_).trans card_inHallU
  refine
    { toFun := fun x =>
        ⟨hc.equiv.symm ⟨x.1, (Subgroup.mem_inf.mp x.2).2⟩, ?_⟩
      invFun := fun u =>
        ⟨rep u.1, Subgroup.mem_inf.mpr
          ⟨rep_mem_pCoreOf S hF hD hc hC1 u.2, hc.mem u.1⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine (rep_mem_pCoreOf_iff S hF hD hc hC1 hcM _).mp ?_
    rw [hc.rep_symm]
    exact (Subgroup.mem_inf.mp x.2).1
  · intro x
    apply Subtype.ext
    exact hc.rep_symm ⟨x.1, (Subgroup.mem_inf.mp x.2).2⟩
  · intro u
    apply Subtype.ext
    exact hc.equiv.symm_apply_apply u.1

theorem psiSub_pCoreOf_eq (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) :
    S.psiSub hc (fiveQ rep) = hallRM := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hB : S.psiSub hc (fiveQ rep) ≤ hallRM :=
    psiSub_pCoreOf_le S hF hD hc hC1
  have hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ S.psiSub hc (fiveQ rep),
      a * b * a⁻¹ ∈ S.psiSub hc (fiveQ rep) :=
    fun a ha ha5 => conj_mem_psiSub_of_mem_hexaL_fiveCent S hF hc hQM
      (fun g hg q hq => conj_mem_fiveQ hg hq) ha ha5
  rcases hD.rm_le_or_quad _ hB hnorm with hge | hquad
  · exact le_antisymm hB hge
  · exact (false_of_quadratic S hF hD hc hC1 hcM
      (fun g hg q hq => conj_mem_fiveQ hg hq)
      (fun u hu => rep_mem_pCoreOf S hF hD hc hC1 hu) le_rfl hquad).elim

theorem psiSub_M_eq_hexaM (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) :
    S.psiSub hc M = hexaM := by
  rcases S.psiSub_M_eq hF hc hC1 with h | h
  · exfalso
    have hRM : hallRM ≤ S.psiSub hc M := by
      rw [← psiSub_pCoreOf_eq S hF hD hc hC1 hcM]
      exact S.psiSub_mono hc (pCoreOf_centralizer_five_le S hF hc hC1)
    rw [h] at hRM
    exact hD.rm_not_le hRM
  · exact h

theorem card_pCoreOf_five (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) : Nat.card (fiveQ rep) = 128 := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hcard := S.card_eq_card_inf_blockU_mul hc hC1 hQM
  have hcardInf : Nat.card ↥(fiveQ rep ⊓ blockU L) = 16 :=
    card_fiveQ_inf_blockU S hF hD hc hC1 hcM
  have hcardRM : Nat.card (S.psiSub hc (fiveQ rep)) = 8 := by
    rw [psiSub_pCoreOf_eq S hF hD hc hC1 hcM, card_hallRM hD]
  rw [hcard, hcardInf, hcardRM]

theorem eq_pCoreOf_of_normal (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) {Q₀ : Subgroup G}
    (hQ₀n : ∀ g ∈ fiveCent rep, ∀ q ∈ Q₀, g * q * g⁻¹ ∈ Q₀)
    (hUQ₀ : ∀ u, InHallU u → rep u ∈ Q₀)
    (hQ₀Q : Q₀ ≤ fiveQ rep) : Q₀ = fiveQ rep := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hQ₀M : Q₀ ≤ M := hQ₀Q.trans hQM
  have hB : S.psiSub hc Q₀ ≤ hallRM :=
    (S.psiSub_mono hc hQ₀Q).trans (psiSub_pCoreOf_le S hF hD hc hC1)
  have hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ S.psiSub hc Q₀,
      a * b * a⁻¹ ∈ S.psiSub hc Q₀ :=
    fun a ha ha5 => conj_mem_psiSub_of_mem_hexaL_fiveCent S hF hc hQ₀M hQ₀n ha ha5
  have hψeq : S.psiSub hc Q₀ = S.psiSub hc (fiveQ rep) := by
    rcases hD.rm_le_or_quad _ hB hnorm with hge | hquad
    · rw [le_antisymm hB hge, psiSub_pCoreOf_eq S hF hD hc hC1 hcM]
    · exact (false_of_quadratic S hF hD hc hC1 hcM hQ₀n hUQ₀ hQ₀Q hquad).elim
  apply le_antisymm hQ₀Q
  intro q hq
  have hqM : q ∈ M := hQM hq
  have hψq : S.psiM hc ⟨q, hqM⟩ ∈ S.psiSub hc Q₀ := by
    rw [hψeq, mem_psiSub S hc hQM]
    exact ⟨q, hq, hqM, rfl⟩
  rw [mem_psiSub S hc hQ₀M] at hψq
  obtain ⟨q₀, hq₀, hq₀M, hψq₀⟩ := hψq
  have hmemM : q₀⁻¹ * q ∈ M := M.mul_mem (M.inv_mem hq₀M) hqM
  have hψ1 : S.psiM hc ⟨q₀⁻¹ * q, hmemM⟩ = 1 := by
    have harg : (⟨q₀⁻¹ * q, hmemM⟩ : ↥M) = ⟨q₀, hq₀M⟩⁻¹ * ⟨q, hqM⟩ :=
      Subtype.ext rfl
    rw [harg, map_mul, map_inv, hψq₀]
    group
  have hV : q₀⁻¹ * q ∈ blockU L :=
    (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨q₀⁻¹ * q, hmemM⟩).mp hψ1
  have hQ : q₀⁻¹ * q ∈ fiveQ rep :=
    (fiveQ rep).mul_mem ((fiveQ rep).inv_mem (hQ₀Q hq₀)) hq
  have hU : q₀⁻¹ * q ∈ Q₀ := by
    obtain ⟨u, hu, hrep⟩ :=
      (mem_fiveQ_inf_blockU_iff S hF hD hc hC1 hcM).mp (Subgroup.mem_inf.mpr ⟨hQ, hV⟩)
    rw [← hrep]
    exact hUQ₀ u hu
  have hqeq : q = q₀ * (q₀⁻¹ * q) := by group
  rw [hqeq]
  exact Q₀.mul_mem hq₀ hU

theorem commute_pCoreOf_iff (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) {x : G} (hx : x ∈ fiveQ rep) :
    (∀ q ∈ fiveQ rep, x * q = q * x) ↔ x = 1 ∨ x = rep 5 := by
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  constructor
  · intro hxc
    have hxM : x ∈ M := hQM hx
    have hfixU : ∀ u, InHallU u → S.psiM hc ⟨x, hxM⟩ u = u := by
      intro u hu
      have huQ : rep u ∈ fiveQ rep := rep_mem_pCoreOf S hF hD hc hC1 hu
      have hcomm : x * rep u = rep u * x := hxc (rep u) huQ
      apply hc.inj
      rw [S.rep_psiM hc ⟨x, hxM⟩ u]
      calc x * rep u * x⁻¹ = rep u * x * x⁻¹ := by rw [hcomm]
        _ = rep u := by group
    have hψx : S.psiM hc ⟨x, hxM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨x, hxM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨x, hx, hxM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    obtain ⟨e, he⟩ := (hD.mem_rm_iff _).mp hψx
    have he0 : e = 0 := hD.rm_eq_zero_of_fix_u e (fun u hu => by
      have h := hfixU u hu
      rw [← he] at h
      exact h)
    have hψx1 : S.psiM hc ⟨x, hxM⟩ = 1 := by
      rw [← he, he0]
      exact hallRMPerm_zero hD
    have hxV : x ∈ blockU L :=
      (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨x, hxM⟩).mp hψx1
    obtain ⟨v, rfl⟩ := (mem_blockU_iff hc).mp hxV
    have hfixall : ∀ e : Fin 8, hallRMPerm e v = v := by
      intro e
      have hmem : hallRMPerm e ∈ S.psiSub hc (fiveQ rep) := by
        rw [psiSub_pCoreOf_eq S hF hD hc hC1 hcM]
        exact (hD.mem_rm_iff _).mpr ⟨e, rfl⟩
      rw [mem_psiSub S hc hQM] at hmem
      obtain ⟨q, hq, hqM, hψq⟩ := hmem
      have hcomm : rep v * q = q * rep v := hxc q hq
      have hconj : q * rep v * q⁻¹ = rep v := by
        calc q * rep v * q⁻¹ = rep v * q * q⁻¹ := by rw [← hcomm]
          _ = rep v := by group
      have h2 : S.psiM hc ⟨q, hqM⟩ v = v := by
        apply hc.inj
        rw [S.rep_psiM hc ⟨q, hqM⟩ v]
        exact hconj
      rwa [hψq] at h2
    rcases hD.fix_rm v hfixall with rfl | rfl
    · left
      exact hc.rep_zero
    · right
      rfl
  · rintro (rfl | rfl)
    · intro q hq
      group
    · intro q hq
      exact (commute_of_mem_fiveCent hc (fiveQ_le_fiveCent rep hq)).symm

private theorem le_centralizer_of_le_blockU_of_normal (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) {Y : Subgroup G} (hYQ : Y ≤ fiveQ rep)
    (hYV : Y ≤ blockU L)
    (hYn : ∀ g ∈ fiveCent rep, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    Y ≤ Subgroup.centralizer (fiveQ rep : Set G) := by
  let Q₀ : Subgroup G := fiveQ rep ⊓ Subgroup.centralizer (Y : Set G)
  have hQ₀n : ∀ g ∈ fiveCent rep, ∀ q ∈ Q₀, g * q * g⁻¹ ∈ Q₀ := by
    intro g hg q hq
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact conj_mem_fiveQ hg hq.1
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Y := by
        have h := hYn g⁻¹ ((fiveCent rep).inv_mem hg) y hy
        simpa using h
      have hcomm := Subgroup.mem_centralizer_iff.mp hq.2 (g⁻¹ * y * g) hy'
      calc y * (g * q * g⁻¹) = g * ((g⁻¹ * y * g) * q) * g⁻¹ := by group
        _ = g * (q * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * q * g⁻¹) * y := by group
  have hUQ₀ : ∀ u, InHallU u → rep u ∈ Q₀ := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨rep_mem_pCoreOf S hF hD hc hC1 hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact S.blockU_comm (hYV hy) (hc.mem u)
  have hQ₀eq : Q₀ = fiveQ rep :=
    eq_pCoreOf_of_normal S hF hD hc hC1 hcM hQ₀n hUQ₀ inf_le_left
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqQ₀ : q ∈ Q₀ := by rw [hQ₀eq]; exact hq
  have hqY : q ∈ Subgroup.centralizer (Y : Set G) := (Subgroup.mem_inf.mp hqQ₀).2
  exact (Subgroup.mem_centralizer_iff.mp hqY y hy).symm

theorem comm_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) :
    ∀ a ∈ fiveQ rep, ∀ b ∈ fiveQ rep,
      a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = rep 5 := by
  intro a ha b hb
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hYQ : ⁅fiveQ rep, fiveQ rep⁆ ≤ fiveQ rep := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact (fiveQ rep).mul_mem ((fiveQ rep).mul_mem ((fiveQ rep).mul_mem hx hy)
      ((fiveQ rep).inv_mem hx)) ((fiveQ rep).inv_mem hy)
  have hYV : ⁅fiveQ rep, fiveQ rep⁆ ≤ blockU L := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxM : x ∈ M := hQM hx
    have hyM : y ∈ M := hQM hy
    have hψx : S.psiM hc ⟨x, hxM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨x, hxM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨x, hx, hxM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    have hψy : S.psiM hc ⟨y, hyM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨y, hyM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨y, hy, hyM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    have hcommM : ⁅x, y⁆ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM)
    have hψcomm : S.psiM hc ⟨⁅x, y⁆, hcommM⟩ = 1 := by
      have harg : (⟨⁅x, y⁆, hcommM⟩ : ↥M) =
          ⁅(⟨x, hxM⟩ : ↥M), (⟨y, hyM⟩ : ↥M)⁆ := Subtype.ext rfl
      rw [harg, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hallRM_comm hD hψx hψy
    exact (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨⁅x, y⁆, hcommM⟩).mp hψcomm
  have hYn : ∀ g ∈ fiveCent rep, ∀ y ∈ ⁅fiveQ rep, fiveQ rep⁆,
      g * y * g⁻¹ ∈ ⁅fiveQ rep, fiveQ rep⁆ := by
    intro g hg y hy
    have hQmap : (fiveQ rep).map (MulAut.conj g).toMonoidHom = fiveQ rep :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (fiveCent_normalizes_fiveQ rep hg)
    have hmap : (⁅fiveQ rep, fiveQ rep⁆).map (MulAut.conj g).toMonoidHom =
        ⁅fiveQ rep, fiveQ rep⁆ := by
      rw [Subgroup.map_commutator, hQmap]
    have hmem : g * y * g⁻¹ ∈ (⁅fiveQ rep, fiveQ rep⁆).map
        (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [hmap] at hmem
  have hcent := le_centralizer_of_le_blockU_of_normal S hF hD hc hC1 hcM hYQ hYV hYn
  have hxY : ⁅a, b⁆ ∈ ⁅fiveQ rep, fiveQ rep⁆ :=
    Subgroup.commutator_mem_commutator ha hb
  have hxQ : ⁅a, b⁆ ∈ fiveQ rep := hYQ hxY
  have hxc : ⁅a, b⁆ ∈ Subgroup.centralizer (fiveQ rep : Set G) := hcent hxY
  have hcentral : ∀ q ∈ fiveQ rep, ⁅a, b⁆ * q = q * ⁅a, b⁆ := by
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp hxc q hq).symm
  exact (commute_pCoreOf_iff S hF hD hc hC1 hcM hxQ).mp hcentral

theorem mul_self_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ fiveCent rep ≤ M) :
    ∀ a ∈ fiveQ rep, a * a = 1 ∨ a * a = rep 5 := by
  intro a ha
  have hQM : fiveQ rep ≤ M := pCoreOf_centralizer_five_le S hF hc hC1
  have hsq_rm : ∀ e : Fin 8, hallRMPerm e * hallRMPerm e = 1 := by
    intro e
    have hee : xor8 e e = 0 := by
      apply Fin.ext
      simp [xor8]
    rw [hD.rm_mul e e, hee, hallRMPerm_zero hD]
  let Ys : Subgroup G := Subgroup.closure {x : G | ∃ b ∈ fiveQ rep, x = b * b}
  have hYQ : Ys ≤ fiveQ rep := by
    change Subgroup.closure {x : G | ∃ b ∈ fiveQ rep, x = b * b} ≤ fiveQ rep
    refine (Subgroup.closure_le (K := fiveQ rep)).mpr ?_
    rintro x ⟨b, hb, rfl⟩
    exact (fiveQ rep).mul_mem hb hb
  have hYV : Ys ≤ blockU L := by
    change Subgroup.closure {x : G | ∃ b ∈ fiveQ rep, x = b * b} ≤ blockU L
    refine (Subgroup.closure_le (K := blockU L)).mpr ?_
    rintro x ⟨b, hb, rfl⟩
    have hbM : b ∈ M := hQM hb
    have hbbM : b * b ∈ M := M.mul_mem hbM hbM
    have hψb : S.psiM hc ⟨b, hbM⟩ ∈ hallRM := by
      have hmem : S.psiM hc ⟨b, hbM⟩ ∈ S.psiSub hc (fiveQ rep) := by
        rw [mem_psiSub S hc hQM]
        exact ⟨b, hb, hbM, rfl⟩
      exact psiSub_pCoreOf_le S hF hD hc hC1 hmem
    have hψbb : S.psiM hc ⟨b * b, hbbM⟩ = 1 := by
      have harg : (⟨b * b, hbbM⟩ : ↥M) = ⟨b, hbM⟩ * ⟨b, hbM⟩ := Subtype.ext rfl
      rw [harg, map_mul]
      obtain ⟨e, he⟩ := (hD.mem_rm_iff _).mp hψb
      rw [← he, hsq_rm e]
    exact (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨b * b, hbbM⟩).mp hψbb
  have hYn : ∀ g ∈ fiveCent rep, ∀ y ∈ Ys, g * y * g⁻¹ ∈ Ys := by
    intro g hg y hy
    have hQmap : (fiveQ rep).map (MulAut.conj g).toMonoidHom = fiveQ rep :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (fiveCent_normalizes_fiveQ rep hg)
    have hmap : Ys.map (MulAut.conj g).toMonoidHom = Ys := by
      change (Subgroup.closure {x : G | ∃ b ∈ fiveQ rep, x = b * b}).map
        (MulAut.conj g).toMonoidHom = Subgroup.closure {x : G | ∃ b ∈ fiveQ rep, x = b * b}
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨b, hb, rfl⟩, rfl⟩
        refine ⟨g * b * g⁻¹,
          conj_mem_fiveQ hg hb, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨b, hb, rfl⟩
        have hmem : g⁻¹ * b * g ∈ fiveQ rep := by
          have h := conj_mem_fiveQ ((fiveCent rep).inv_mem hg) hb
          simpa using h
        refine ⟨g⁻¹ * (b * b) * g, ⟨g⁻¹ * b * g, hmem, ?_⟩, ?_⟩
        · group
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
    have hmem : g * y * g⁻¹ ∈ Ys.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [hmap] at hmem
  have hcent := le_centralizer_of_le_blockU_of_normal S hF hD hc hC1 hcM hYQ hYV hYn
  have hxY : a * a ∈ Ys := Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hxQ : a * a ∈ fiveQ rep := hYQ hxY
  have hxc : a * a ∈ Subgroup.centralizer (fiveQ rep : Set G) := hcent hxY
  have hcentral : ∀ q ∈ fiveQ rep, (a * a) * q = q * (a * a) := by
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp hxc q hq).symm
  exact (commute_pCoreOf_iff S hF hD hc hC1 hcM hxQ).mp hcentral

theorem exists_conj_five_mem (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∃ g : G, g * rep 5 * g⁻¹ ∈ fiveQ rep ∧ g * rep 5 * g⁻¹ ≠ rep 5 := by
  obtain ⟨a, ha, ha5⟩ := hD.five_trans 10 (by decide) (by decide)
  obtain ⟨m, -, hmψ⟩ := S.exists_mem_L_psiM_eq hF hc ha
  have hrep : (m : G) * rep 5 * (m : G)⁻¹ = rep 10 := by
    rw [← S.rep_psiM hc m 5, hmψ, ha5]
  refine ⟨(m : G), ?_, ?_⟩ <;> rw [hrep]
  · exact rep_mem_pCoreOf S hF hD hc hC1 (by decide)
  · intro h
    exact absurd (hc.inj h) (by decide)

end CFSG.CGT.Hall82.Setting

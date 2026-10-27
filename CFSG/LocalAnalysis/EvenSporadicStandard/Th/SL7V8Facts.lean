module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerVMod
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.EInvariant

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

@[expose] def thV (t v : G) : G := v * (t * v * t⁻¹)

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.mem_normalizer_W5_of_mem_normInL {n : G} (hn : n ∈ normInL L A) :
    n ∈ normalizer ((W5 A t : Subgroup G) : Set G) := by
  have hnc : t * n = n * t := H.comm_of_mem_L hn.1
  have hone : ∀ m : G, m ∈ normInL L A → ∀ y ∈ W5 A t, m * y * m⁻¹ ∈ W5 A t := by
    intro m hm y hy
    have hmt : m * t * m⁻¹ = t * 1 := by
      have := H.comm_of_mem_L hm.1
      calc m * t * m⁻¹ = (m * t) * m⁻¹ := rfl
        _ = (t * m) * m⁻¹ := by rw [this]
        _ = t * 1 := by group
    exact conj_mem_sup_zpowers_of_conj_eq_mul hm.2 ⟨1, A.one_mem, hmt⟩ hy
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => hone n hn y hy, fun hy => ?_⟩
  have := hone n⁻¹ ((normInL L A).inv_mem hn) _ hy
  simpa [mul_assoc] using this

theorem ThCyc.t_conj_mem_omega1 {v : G} (hv : v ∈ omega1 D hD.comm) :
    t * v * t⁻¹ ∈ omega1 D hD.comm :=
  (mem_normalizer_iff.1 (H.normalizer_le_normalizer_omega1 W W2 hD
    (H.t_mem_normalizer W W2 hD)) v).1 hv

theorem ThCyc.thV_mem_omega1 {v : G} (hv : v ∈ omega1 D hD.comm) :
    thV t v ∈ omega1 D hD.comm :=
  (omega1 D hD.comm).mul_mem hv (H.t_conj_mem_omega1 W W2 hD hv)

theorem ThCyc.omega1_mul_self {v : G} (hv : v ∈ omega1 D hD.comm) : v * v = 1 := by
  rw [← sq]
  exact hv.2

theorem ThCyc.omega1_comm {v w : G} (hv : v ∈ omega1 D hD.comm) (hw : w ∈ omega1 D hD.comm) :
    v * w = w * v := hD.comm v hv.1 w hw.1

theorem ThCyc.t_comm_thV {v : G} (hv : v ∈ omega1 D hD.comm) : t * thV t v = thV t v * t := by
  have htv := H.t_conj_mem_omega1 W W2 hD hv
  have hcomm := H.omega1_comm W W2 hD hv htv
  have h2 : t * (t * v * t⁻¹) * t⁻¹ = v := by
    have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
    calc t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t⁻¹ * t⁻¹) := by group
      _ = v := by
        have : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
        rw [ht2, this]; group
  simp only [thV]
  calc t * (v * (t * v * t⁻¹)) = (t * v * t⁻¹) * (t * (t * v * t⁻¹) * t⁻¹) * t := by group
    _ = (t * v * t⁻¹) * v * t := by rw [h2]
    _ = v * (t * v * t⁻¹) * t := by rw [← hcomm]

theorem ThCyc.thV_mem_A {v : G} (hv : v ∈ omega1 D hD.comm) : thV t v ∈ A := by
  have hmem : thV t v ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) :=
    ⟨H.thV_mem_omega1 W W2 hD hv, mem_centralizer_singleton_iff.2
      (H.t_comm_thV W W2 hD hv).symm⟩
  rwa [H.omega1_inf_centralizer_t W W2 hD] at hmem

theorem ThCyc.thV_mul {v w : G} (hv : v ∈ omega1 D hD.comm) (hw : w ∈ omega1 D hD.comm) :
    thV t (v * w) = thV t v * thV t w := by
  have htv := H.t_conj_mem_omega1 W W2 hD hv
  have htw := H.t_conj_mem_omega1 W W2 hD hw
  have h := H.omega1_comm W W2 hD hw htv
  simp only [thV]
  calc v * w * (t * (v * w) * t⁻¹) = v * w * ((t * v * t⁻¹) * (t * w * t⁻¹)) := by group
    _ = v * (w * (t * v * t⁻¹)) * (t * w * t⁻¹) := by group
    _ = v * ((t * v * t⁻¹) * w) * (t * w * t⁻¹) := by rw [h]
    _ = v * (t * v * t⁻¹) * (w * (t * w * t⁻¹)) := by group

theorem ThCyc.thV_eq_one_iff {v : G} (hv : v ∈ omega1 D hD.comm) : thV t v = 1 ↔ v ∈ A := by
  constructor
  · intro h
    rw [← H.omega1_inf_centralizer_t W W2 hD]
    refine ⟨hv, mem_centralizer_singleton_iff.2 ?_⟩
    have hv2 := H.omega1_mul_self W W2 hD hv
    simp only [thV] at h
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have h1 : t * v * t⁻¹ = v := by
      have := eq_inv_of_mul_eq_one_right h
      rw [this, hvi]
    calc v * t = (t * v * t⁻¹) * t := by rw [h1]
      _ = t * v := by group
  · intro hvA
    have hvt : t * v = v * t := (H.comm_of_mem_L (le_trans
      (fun y hy => ((W.mem_A_iff y).1 hy).1) W.S_le hvA))
    simp only [thV]
    have hv2 : v * v = 1 := H.omega1_mul_self W W2 hD (H.A_le_omega1 W W2 hD hvA)
    calc v * (t * v * t⁻¹) = v * ((v * t) * t⁻¹) := by rw [← hvt]
      _ = v * v := by group
      _ = 1 := hv2

theorem ThCyc.thV_conj {n v : G} (hn : n ∈ L) :
    thV t (n * v * n⁻¹) = n * thV t v * n⁻¹ := by
  have hnc : t * n = n * t := H.comm_of_mem_L hn
  have h1 : t * n * t⁻¹ = n := by
    calc t * n * t⁻¹ = (n * t) * t⁻¹ := by rw [hnc]
      _ = n := by group
  have h2 : t * n⁻¹ * t⁻¹ = n⁻¹ := by
    calc t * n⁻¹ * t⁻¹ = (t * n * t⁻¹)⁻¹ := by group
      _ = n⁻¹ := by rw [h1]
  have e : t * (n * v * n⁻¹) * t⁻¹ = n * (t * v * t⁻¹) * n⁻¹ := by
    calc t * (n * v * n⁻¹) * t⁻¹ = (t * n * t⁻¹) * (t * v * t⁻¹) * (t * n⁻¹ * t⁻¹) := by group
      _ = n * (t * v * t⁻¹) * n⁻¹ := by rw [h1, h2]
  simp only [thV]
  rw [e]
  group

theorem ThCyc.comm_omega1_of_mem_B (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {n : G} (hnB : n ∈ B)
    {v : G} (hv : v ∈ omega1 D hD.comm) : n * v * n⁻¹ = v := by
  have hdv : ∀ d ∈ D, d * v * d⁻¹ = v := fun d hd => by
    rw [mul_inv_eq_iff_eq_mul]; exact hD.comm d hd v hv.1
  have hbv : b * v * b⁻¹ = v := by
    rw [hb v hv.1, inv_eq_of_mul_eq_one_right (H.omega1_mul_self W W2 hD hv)]
  rcases W2.mem_Aa_or_mul_b W hnB with h | h
  · exact hdv n (hD.Aa_le h)
  · have hnb : n = (n * b) * b⁻¹ := by group
    rw [hnb]
    calc n * b * b⁻¹ * v * (n * b * b⁻¹)⁻¹ = (n * b) * (b⁻¹ * v * b) * (n * b)⁻¹ := by group
      _ = (n * b) * v * (n * b)⁻¹ := by
        have : b⁻¹ * v * b = v := by
          have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact W2.b_sq)
          rw [hbi]
          have := hbv
          rwa [hbi] at this
        rw [this]
      _ = v := hdv _ (hD.Aa_le h)

theorem ThCyc.thV_surj (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    ∀ a ∈ A, ∃ v ∈ omega1 D hD.comm, thV t v = a := by
  classical
  let V := omega1 D hD.comm
  let θ : ↥V →* ↥A :=
    { toFun := fun v => ⟨thV t v, H.thV_mem_A W W2 hD v.2⟩
      map_one' := Subtype.ext (by simp [thV])
      map_mul' := fun v w => Subtype.ext (H.thV_mul W W2 hD v.2 w.2) }
  have hker : θ.ker = A.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (H.thV_eq_one_iff W W2 hD v.2).1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((H.thV_eq_one_iff W W2 hD v.2).2 h)
  have hAV : A ≤ V := H.A_le_omega1 W W2 hD
  have hkcard : Nat.card θ.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAV).toEquiv, W.A_card]
  have hVcard : Nat.card ↥V = 2 ^ 8 := H.card_omega1 W W2 hD hsq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have h2 : Nat.card (↥V ⧸ θ.ker) = Nat.card θ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  have hrange : Nat.card θ.range = Nat.card ↥A := by
    rw [h2, hkcard, hVcard] at h1
    rw [W.A_card]
    omega
  have htop : θ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange]
  intro a ha
  have : (⟨a, ha⟩ : ↥A) ∈ θ.range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨v, hv⟩ := this
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

end

end CFSG.EvenSporadicStandard.ThStd

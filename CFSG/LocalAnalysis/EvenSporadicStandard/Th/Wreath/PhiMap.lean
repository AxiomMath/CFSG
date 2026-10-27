module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.VEnd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AbelianSylowPower
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AutAFacts

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q : Subgroup G} {z b : G}

private noncomputable def phiFun (Q : Subgroup G) (c : G) : G → G := by
  classical
  exact fun v => if h : ∃ q ∈ Q, q ^ 2 = v then
    (Classical.choose h)⁻¹ * c * Classical.choose h * c⁻¹ else 1

noncomputable def phiQ (hD : DHyp A Aa t D) (Q : Subgroup G) (c : G) :
    AddMonoid.End (VSub hD) :=
  AbelianSub.endOf _ _ (phiFun Q c)

private theorem phiFun_eq_of_sq_eq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) (h : q ^ 2 = q' ^ 2) :
    q⁻¹ * c * q * c⁻¹ = q'⁻¹ * c * q' * c⁻¹ := by
  set r : G := q * q'⁻¹ with hr
  have hrQ : r ∈ Q := Q.mul_mem hq (Q.inv_mem hq')
  have hcomm : Commute q q' := hQ.comm q hq q' hq'
  have hr2 : r ^ 2 = 1 := by
    rw [hr, hcomm.inv_right.mul_pow 2, inv_pow, h, mul_inv_cancel]
  have hrV : r ∈ omega1 D hD.comm :=
    CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2
      ⟨hQ.mem_of_sq_eq_one r hrQ hr2, hr2⟩
  have hcr : c * r = r * c := (mem_centralizer_iff.1 hc.2 r hrV).symm
  have hval : r⁻¹ * c * r = c := by
    calc r⁻¹ * c * r = r⁻¹ * (c * r) := by group
      _ = r⁻¹ * (r * c) := by rw [hcr]
      _ = c := by group
  have hqr : q = r * q' := by rw [hr]; group
  rw [hqr]
  calc (r * q')⁻¹ * c * (r * q') * c⁻¹
      = q'⁻¹ * (r⁻¹ * c * r) * q' * c⁻¹ := by group
    _ = q'⁻¹ * c * q' * c⁻¹ := by rw [hval]

private theorem phiFun_sq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q : G} (hq : q ∈ Q) : phiFun Q c (q ^ 2) = q⁻¹ * c * q * c⁻¹ := by
  classical
  simp only [phiFun]
  split_ifs with h
  · exact phiFun_eq_of_sq_eq hD hQ hc (Classical.choose_spec h).1 hq (Classical.choose_spec h).2
  · exact absurd ⟨q, hq, rfl⟩ h

private theorem phiFun_mem_sq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q : G} (hq : q ∈ Q) : q⁻¹ * c * q * c⁻¹ ∈ omega1 D hD.comm := by
  have hq2V : q ^ 2 ∈ omega1 D hD.comm := by
    refine CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2 ⟨?_, ?_⟩
    · exact hQ.mem_of_sq_eq_one _ (Q.pow_mem hq 2) (by
        rw [← pow_mul]; norm_num; exact hq4 q hq)
    · rw [← pow_mul]; norm_num; exact hq4 q hq
  have hxQ : c * q * c⁻¹ ∈ Q := (mem_normalizer_iff.1 hc.1 q).1 hq
  have hx2 : (c * q * c⁻¹) ^ 2 = q ^ 2 := by
    have hcV : c * (q ^ 2) * c⁻¹ = q ^ 2 := by
      rw [← mem_centralizer_iff.1 hc.2 (q ^ 2) hq2V]
      group
    calc (c * q * c⁻¹) ^ 2 = c * (q * q) * c⁻¹ := by rw [sq]; group
      _ = c * (q ^ 2) * c⁻¹ := by rw [sq]
      _ = q ^ 2 := hcV
  have hψQ : q⁻¹ * (c * q * c⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq) hxQ
  have hcomm : Commute q (c * q * c⁻¹) := hQ.comm q hq _ hxQ
  have hψ2 : (q⁻¹ * (c * q * c⁻¹)) ^ 2 = 1 := by
    rw [hcomm.inv_left.mul_pow 2, hx2, inv_pow]
    exact inv_mul_cancel (q ^ 2)
  have hψV : q⁻¹ * (c * q * c⁻¹) ∈ omega1 D hD.comm :=
    CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2
      ⟨hQ.mem_of_sq_eq_one _ hψQ hψ2, hψ2⟩
  simpa only [mul_assoc] using hψV

private theorem phiFun_mem (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {v : G} (hv : v ∈ omega1 D hD.comm) : phiFun Q c v ∈ omega1 D hD.comm := by
  obtain ⟨q, hq, rfl⟩ := hsq v hv
  rw [phiFun_sq hD hQ hc hq]
  exact phiFun_mem_sq hD hQ hq4 hc hq

private theorem phiFun_mul_sq_comp (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q r : G} (hq : q ∈ Q) (hr : r ∈ Q) :
    (q * r)⁻¹ * c * (q * r) * c⁻¹ =
      (q⁻¹ * c * q * c⁻¹) * (r⁻¹ * c * r * c⁻¹) := by
  have hψqV : q⁻¹ * c * q * c⁻¹ ∈ omega1 D hD.comm :=
    phiFun_mem_sq hD hQ hq4 hc hq
  have hqval : c * q * c⁻¹ = q * (q⁻¹ * c * q * c⁻¹) := by group
  have hrval : c * r * c⁻¹ = r * (r⁻¹ * c * r * c⁻¹) := by group
  have hψqQ : q⁻¹ * c * q * c⁻¹ ∈ Q := hQ.D_le hψqV.1
  have hcomm : Commute (q⁻¹ * c * q * c⁻¹) r := hQ.comm _ hψqQ r hr
  calc (q * r)⁻¹ * c * (q * r) * c⁻¹
      = (q * r)⁻¹ * ((c * q * c⁻¹) * (c * r * c⁻¹)) := by group
    _ = (q * r)⁻¹ * ((q * (q⁻¹ * c * q * c⁻¹)) *
          (r * (r⁻¹ * c * r * c⁻¹))) := by rw [hqval, hrval]
    _ = r⁻¹ * (q⁻¹ * c * q * c⁻¹) * r * (r⁻¹ * c * r * c⁻¹) := by group
    _ = (q⁻¹ * c * q * c⁻¹) * (r⁻¹ * c * r * c⁻¹) := by
        rw [show r⁻¹ * (q⁻¹ * c * q * c⁻¹) * r = q⁻¹ * c * q * c⁻¹ by
          calc r⁻¹ * (q⁻¹ * c * q * c⁻¹) * r
              = r⁻¹ * ((q⁻¹ * c * q * c⁻¹) * r) := by group
            _ = r⁻¹ * (r * (q⁻¹ * c * q * c⁻¹)) := by rw [hcomm.eq]
            _ = q⁻¹ * c * q * c⁻¹ := by group]

private theorem phiFun_mul_sq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) {c c' : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (hc' : c' ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q : G} (hq : q ∈ Q) :
    q⁻¹ * (c * c') * q * (c * c')⁻¹ =
      (q⁻¹ * c * q * c⁻¹) * (q⁻¹ * c' * q * c'⁻¹) := by
  have hψ'V : q⁻¹ * c' * q * c'⁻¹ ∈ omega1 D hD.comm := phiFun_mem_sq hD hQ hq4 hc' hq
  have hcψ' : c * (q⁻¹ * c' * q * c'⁻¹) * c⁻¹ = q⁻¹ * c' * q * c'⁻¹ := by
    calc c * (q⁻¹ * c' * q * c'⁻¹) * c⁻¹
        = (q⁻¹ * c' * q * c'⁻¹) * c * c⁻¹ := by
          rw [← mem_centralizer_iff.1 hc.2 _ hψ'V]
      _ = q⁻¹ * c' * q * c'⁻¹ := by group
  have hsplit : c' * q * c'⁻¹ = q * (q⁻¹ * c' * q * c'⁻¹) := by group
  calc q⁻¹ * (c * c') * q * (c * c')⁻¹
      = q⁻¹ * c * (c' * q * c'⁻¹) * c⁻¹ := by group
    _ = q⁻¹ * c * (q * (q⁻¹ * c' * q * c'⁻¹)) * c⁻¹ := by rw [hsplit]
    _ = q⁻¹ * (c * q * c⁻¹) * (c * (q⁻¹ * c' * q * c'⁻¹) * c⁻¹) := by group
    _ = (q⁻¹ * c * q * c⁻¹) * (q⁻¹ * c' * q * c'⁻¹) := by rw [hcψ']; group

private theorem phiFun_mul (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {v w : G} (hv : v ∈ omega1 D hD.comm) (hw : w ∈ omega1 D hD.comm) :
    phiFun Q c (v * w) = phiFun Q c v * phiFun Q c w := by
  obtain ⟨q, hq, rfl⟩ := hsq v hv
  obtain ⟨r, hr, rfl⟩ := hsq w hw
  have hcomm : Commute q r := hQ.comm q hq r hr
  have hmul : q ^ 2 * r ^ 2 = (q * r) ^ 2 := (hcomm.mul_pow 2).symm
  rw [hmul, phiFun_sq hD hQ hc (Q.mul_mem hq hr),
    phiFun_sq hD hQ hc hq, phiFun_sq hD hQ hc hr]
  exact phiFun_mul_sq_comp hD hQ hq4 hc hq hr

theorem QHyp.mem_normalizer_omega1 (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {n : G}
    (hn : n ∈ normalizer (Q : Set G)) :
    n ∈ normalizer (omega1 D hD.comm : Set G) := by
  refine mem_normalizer_iff.2 fun v => ⟨?_, ?_⟩
  · rintro ⟨hvD, hv2⟩
    have hnq : n * v * n⁻¹ ∈ Q := (mem_normalizer_iff.1 hn v).1 (hQ.D_le hvD)
    have hsq : (n * v * n⁻¹) ^ 2 = 1 := by
      calc (n * v * n⁻¹) ^ 2 = n * v ^ 2 * n⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [hv2]; group
    exact CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2
      ⟨hQ.mem_of_sq_eq_one _ hnq hsq, hsq⟩
  · intro hv
    have hvD : v = n⁻¹ * (n * v * n⁻¹) * n := by group
    rw [hvD]
    have hn' : n⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hn
    have hnq : n⁻¹ * (n * v * n⁻¹) * n ∈ Q := by
      simpa using (mem_normalizer_iff.1 hn' _).1
        (hQ.D_le (CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.1 hv).1)
    have hv2 : v ^ 2 = 1 := by
      calc v ^ 2 = (n⁻¹ * (n * v * n⁻¹) * n) ^ 2 := by conv_lhs => rw [hvD]
        _ = n⁻¹ * (n * v * n⁻¹) ^ 2 * n := by rw [sq, sq]; group
        _ = 1 := by rw [(CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.1 hv).2]; group
    have hsq : (n⁻¹ * (n * v * n⁻¹) * n) ^ 2 = 1 := by
      rw [← hvD, hv2]
    exact CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2
      ⟨hQ.mem_of_sq_eq_one _ hnq hsq, hsq⟩

theorem QHyp.val_phiQ_apply (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    {q : G} (hq : q ∈ Q) (x : VSub hD) (hx : x.val = q ^ 2) :
    (phiQ hD Q c x).val = q⁻¹ * c * q * c⁻¹ := by
  have hf : ∀ v ∈ omega1 D hD.comm, phiFun Q c v ∈ omega1 D hD.comm :=
    fun v hv => phiFun_mem hD hQ hq4 hsq hc hv
  have hm : ∀ v ∈ omega1 D hD.comm, ∀ w ∈ omega1 D hD.comm,
      phiFun Q c (v * w) = phiFun Q c v * phiFun Q c w :=
    fun v hv w hw => phiFun_mul hD hQ hq4 hsq hc hv hw
  rw [phiQ, AbelianSub.val_endOf_apply hf hm x, hx, phiFun_sq hD hQ hc hq]

private theorem mem_omega1_sq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) {q : G} (hq : q ∈ Q) :
    q ^ 2 ∈ omega1 D hD.comm := by
  refine CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2 ⟨?_, ?_⟩
  · exact hQ.mem_of_sq_eq_one _ (Q.pow_mem hq 2) (by
      rw [← pow_mul]; norm_num; exact hq4 q hq)
  · rw [← pow_mul]; norm_num; exact hq4 q hq

theorem QHyp.phiQ_mul (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c c' : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (hc' : c' ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q (c * c') = phiQ hD Q c + phiQ hD Q c' := by
  refine AbelianSub.end_ext fun x => ?_
  obtain ⟨q, hq, hx⟩ := hsq x.val (AbelianSub.val_mem x)
  have hcc' : c * c' ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    Subgroup.mul_mem _ hc hc'
  rw [QHyp.val_phiQ_apply hD hQ hq4 hsq hcc' hq x hx.symm]
  change q⁻¹ * (c * c') * q * (c * c')⁻¹ =
    ((phiQ hD Q c) x + (phiQ hD Q c') x).val
  rw [AbelianSub.val_add,
    QHyp.val_phiQ_apply hD hQ hq4 hsq hc hq x hx.symm,
    QHyp.val_phiQ_apply hD hQ hq4 hsq hc' hq x hx.symm]
  exact phiFun_mul_sq hD hQ hq4 hc hc' hq

theorem QHyp.phiQ_eq_zero_iff (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c = 0 ↔ c ∈ centralizer (Q : Set G) := by
  constructor
  · intro hzero
    refine mem_centralizer_iff.2 fun q hq => ?_
    let x : VSub hD := AbelianSub.mk (q ^ 2) (mem_omega1_sq hD hQ hq4 hq)
    have hv := QHyp.val_phiQ_apply hD hQ hq4 hsq hc hq x rfl
    rw [hzero] at hv
    have hψ : q⁻¹ * c * q * c⁻¹ = 1 := by simpa using hv.symm
    have hcq : c * q = q * c := by
      calc c * q = q * (q⁻¹ * c * q * c⁻¹) * c := by group
        _ = q * 1 * c := by rw [hψ]
        _ = q * c := by group
    exact hcq.symm
  · intro hcen
    refine AbelianSub.end_ext fun x => ?_
    obtain ⟨q, hq, hx⟩ := hsq x.val (AbelianSub.val_mem x)
    rw [QHyp.val_phiQ_apply hD hQ hq4 hsq hc hq x hx.symm]
    have hqc : q * c = c * q := mem_centralizer_iff.1 hcen q hq
    have hψ : q⁻¹ * c * q * c⁻¹ = 1 := by
      calc q⁻¹ * c * q * c⁻¹ = q⁻¹ * (c * q) * c⁻¹ := by group
        _ = q⁻¹ * (q * c) * c⁻¹ := by rw [← hqc]
        _ = 1 := by group
    rw [hψ]
    rfl

theorem QHyp.conj_mem_NV (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {n c : G} (hn : n ∈ normalizer (Q : Set G))
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    n * c * n⁻¹ ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := QHyp.mem_normalizer_omega1 hD hQ hn
  have hn'Q : n⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hn
  have hmQ : n * c * n⁻¹ ∈ normalizer (Q : Set G) :=
    (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem hn hc.1) ((normalizer (Q : Set G)).inv_mem hn)
  refine ⟨hmQ, ?_⟩
  · refine mem_centralizer_iff.2 fun v hv => ?_
    have hv' : n⁻¹ * v * n ∈ omega1 D hD.comm := by
      simpa using (mem_normalizer_iff.1
        ((normalizer (omega1 D hD.comm : Set G)).inv_mem hnV) v).1 hv
    have hcv : (n⁻¹ * v * n) * c = c * (n⁻¹ * v * n) :=
      mem_centralizer_iff.1 hc.2 _ hv'
    calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [hcv]
      _ = (n * c * n⁻¹) * v := by group

theorem QHyp.phiQ_conj (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {n c : G} (hn : n ∈ normalizer (Q : Set G))
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q (n * c * n⁻¹) * vConj hD n = vConj hD n * phiQ hD Q c := by
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := QHyp.mem_normalizer_omega1 hD hQ hn
  have hc' := QHyp.conj_mem_NV hD hQ hq4 hsq hn hc
  refine AbelianSub.end_ext fun x => ?_
  obtain ⟨q, hq, hx⟩ := hsq x.val (AbelianSub.val_mem x)
  have hnq : n * q * n⁻¹ ∈ Q := (mem_normalizer_iff.1 hn q).1 hq
  have hy : (vConj hD n x).val = (n * q * n⁻¹) ^ 2 := by
    rw [val_vConj_apply hD hnV x, ← hx, sq, sq]
    group
  change (phiQ hD Q (n * c * n⁻¹) (vConj hD n x)).val =
    (vConj hD n (phiQ hD Q c x)).val
  rw [QHyp.val_phiQ_apply hD hQ hq4 hsq hc' hnq (vConj hD n x) hy,
    val_vConj_apply hD hnV, QHyp.val_phiQ_apply hD hQ hq4 hsq hc hq x hx.symm]
  group

theorem ThCyc.b_mem_NV (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) :
    b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
  have hbL : b ∈ L := W.B_le W2.b_mem
  have hb2 : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbA : b ∈ normalizer (A : Set G) := by
    refine mem_normalizer_iff.2 fun a => ⟨?_, ?_⟩
    · intro ha
      rw [W2.b_inv a (W2.A_le ha)]
      exact A.inv_mem ha
    · intro ha
      have hmem : b * a * b⁻¹ ∈ A := ha
      have h1 : b * (b * a * b⁻¹) * b⁻¹ = (b * a * b⁻¹)⁻¹ := W2.b_inv _ (W2.A_le hmem)
      have h2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
        rw [hbinv]
        calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
          _ = a := by rw [hb2]; group
      rw [h2] at h1
      rw [h1]
      exact A.inv_mem hmem
  have hbHn : b ∈ L ⊓ normalizer (A : Set G) := ⟨hbL, hbA⟩
  have hbQ : b ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨?_, ?_⟩
    · intro hq
      exact hQ.conj_mem b hbHn q hq
    · intro hq
      have e : q = b * (b * q * b⁻¹) * b⁻¹ := by
        rw [hbinv]
        calc q = (b * b) * q * (b * b) := by rw [hb2]; group
          _ = b * (b * q * b) * b := by group
      rw [e]
      exact hQ.conj_mem b hbHn _ hq
  refine ⟨hbQ, mem_centralizer_iff.2 fun v hv => ?_⟩
  have hbv : b * v * b⁻¹ = v := by
    rw [hb v hv.1]
    exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hv.2)
  calc v * b = (b * v * b⁻¹) * b := by rw [hbv]
    _ = b * v := by group

theorem ThCyc.phiQ_b_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (x : VSub hD) (hx : x.val ∈ A) : phiQ hD Q b x = x := by
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  obtain ⟨q, hq, hqx⟩ := hsq x.val (AbelianSub.val_mem x)
  have hqD : q ∈ D :=
    (QHyp.sq_mem_A_iff H W W2 hD h4 hQ hq).1 (by rw [hqx]; exact hx)
  have hq2sq : q ^ 2 * q ^ 2 = 1 := by
    rw [← pow_add]; norm_num; exact hq4 q hq
  have hval : (phiQ hD Q b x).val = x.val := by
    rw [QHyp.val_phiQ_apply hD hQ hq4 hsq hbNV hq x hqx.symm]
    calc q⁻¹ * b * q * b⁻¹ = q⁻¹ * (b * q * b⁻¹) := by group
      _ = q⁻¹ * q⁻¹ := by rw [hb q hqD]
      _ = (q ^ 2)⁻¹ := by rw [← mul_inv_rev, sq]
      _ = q ^ 2 := inv_eq_of_mul_eq_one_right hq2sq
      _ = x.val := hqx
  exact AbelianSub.ext hval

theorem QHyp.NV_le_K (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hQ : QHyp L A D t Q) :
    normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ≤
      normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
  rintro c ⟨hcQ, hcV⟩
  have hconj_sq : ∀ d ∈ D, (c * d * c⁻¹) ^ 2 = d ^ 2 := by
    intro d hd
    have hd2V : d ^ 2 ∈ omega1 D hD.comm := by
      refine CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2 ⟨?_, ?_⟩
      · exact hD.Aa_le (W2.A_le (H.D_sq_mem_A_of_fourth W W2 hD h4 hd))
      · rw [← pow_mul]; norm_num; exact h4 d hd
    calc (c * d * c⁻¹) ^ 2 = c * (d * d) * c⁻¹ := by rw [sq]; group
      _ = c * (d ^ 2) * c⁻¹ := by rw [sq]
      _ = d ^ 2 := by
          rw [← mem_centralizer_iff.1 hcV (d ^ 2) hd2V]
          group
  have hdis : ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro d hd
    have hcdQ : c * d * c⁻¹ ∈ Q := (mem_normalizer_iff.1 hcQ d).1 (hQ.D_le hd)
    refine (QHyp.sq_mem_A_iff H W W2 hD h4 hQ hcdQ).1 ?_
    rw [hconj_sq d hd]
    exact H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hcQ' : c⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hcQ
  have hcV' : c⁻¹ ∈ centralizer (omega1 D hD.comm : Set G) :=
    (centralizer (omega1 D hD.comm : Set G)).inv_mem hcV
  refine ⟨mem_normalizer_iff.2 fun d => ⟨fun hd => hdis d hd, fun hd => ?_⟩, hcV⟩
  have hd' : c⁻¹ * (c * d * c⁻¹) * c ∈ D := by
    have hcd : c * d * c⁻¹ ∈ D := hd
    have hQ' : c⁻¹ * (c * d * c⁻¹) * c ∈ Q := by
      simpa using (mem_normalizer_iff.1 hcQ' _).1 (hQ.D_le hcd)
    have hy2A : (c * d * c⁻¹) ^ 2 ∈ A := H.D_sq_mem_A_of_fourth W W2 hD h4 hcd
    have hy2V : (c * d * c⁻¹) ^ 2 ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD hy2A
    have hc'' : c⁻¹ * ((c * d * c⁻¹) ^ 2) * c = (c * d * c⁻¹) ^ 2 := by
      rw [← mem_centralizer_iff.1 hcV' ((c * d * c⁻¹) ^ 2) hy2V]
      group
    refine (QHyp.sq_mem_A_iff H W W2 hD h4 hQ hQ').1 ?_
    have hsq : (c⁻¹ * (c * d * c⁻¹) * c) ^ 2 = (c * d * c⁻¹) ^ 2 := by
      calc (c⁻¹ * (c * d * c⁻¹) * c) ^ 2
          = c⁻¹ * ((c * d * c⁻¹) * (c * d * c⁻¹)) * c := by rw [sq]; group
        _ = c⁻¹ * ((c * d * c⁻¹) ^ 2) * c := by rw [sq]
        _ = (c * d * c⁻¹) ^ 2 := hc''
    rw [hsq]
    exact hy2A
  simpa [mul_assoc] using hd'

private theorem nsmul_eq_self_of_odd {M : Type*} [AddMonoid M] (h2 : ∀ x : M, x + x = 0)
    {n : ℕ} (hn : Odd n) (x : M) : n • x = x := by
  rcases hn with ⟨t, rfl⟩
  rw [add_nsmul, mul_nsmul, two_nsmul, h2, nsmul_zero, zero_add, one_nsmul]

private theorem phiQ_pow (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (n : ℕ) : phiQ hD Q (c ^ n) = n • phiQ hD Q c := by
  induction n with
  | zero =>
      rw [pow_zero, zero_nsmul]
      exact (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq
        (show (1 : G) ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) from
          ⟨one_mem _, one_mem _⟩)).2 (by simp)
  | succ n ih =>
      rw [pow_succ, QHyp.phiQ_mul hD hQ hq4 hsq (Subgroup.pow_mem _ hc n) hc, ih,
        succ_nsmul]

private theorem phiQ_eq_zero_of_odd_order (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (hodd : Odd (orderOf c)) : phiQ hD Q c = 0 := by
  have hone : phiQ hD Q (1 : G) = 0 :=
    (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq
      (show (1 : G) ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) from
        ⟨one_mem _, one_mem _⟩)).2 (by simp)
  have hpow := phiQ_pow hD hQ hq4 hsq hc (orderOf c)
  rw [pow_orderOf_eq_one, hone] at hpow
  have hzero : orderOf c • phiQ hD Q c = 0 := hpow.symm
  rw [nsmul_eq_self_of_odd (fun x => VSub.add_self hD x) hodd] at hzero
  exact hzero

theorem QHyp.phiQ_eq_zero_of_mem_centralizer_D (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c : G} (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (hcD : c ∈ centralizer (D : Set G)) : phiQ hD Q c = 0 := by
  classical
  have hn0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨k, m, hm_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hcop : Nat.Coprime (2 ^ k) m :=
    (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hm_odd.not_two_dvd_nat).symm
  have hgcd : Nat.gcd (2 ^ k) m = 1 := hcop
  set u : ℤ := Nat.gcdA (2 ^ k) m with hu
  set v : ℤ := Nat.gcdB (2 ^ k) m with hv
  have hbez : (1 : ℤ) = (2 ^ k : ℤ) * u + (m : ℤ) * v := by
    have h := Nat.gcd_eq_gcd_ab (2 ^ k) m
    rw [hgcd] at h
    simpa [u, v] using h
  let c₂ : G := c ^ ((m : ℤ) * v)
  let codd : G := c ^ ((2 ^ k : ℤ) * u)
  have hc₂_mem : c₂ ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    Subgroup.zpow_mem _ hc _
  have hcodd_mem : codd ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    Subgroup.zpow_mem _ hc _
  have hc₂D : c₂ ∈ centralizer (D : Set G) := Subgroup.zpow_mem _ hcD _
  have hc_eq : c = c₂ * codd := by
    have h1 : (1 : ℤ) = (m : ℤ) * v + (2 ^ k : ℤ) * u := by linarith
    calc c = c ^ (1 : ℤ) := by rw [zpow_one]
      _ = c ^ ((m : ℤ) * v + (2 ^ k : ℤ) * u) := by rw [h1]
      _ = c ^ ((m : ℤ) * v) * c ^ ((2 ^ k : ℤ) * u) := zpow_add _ _ _
      _ = c₂ * codd := rfl
  have hc₂_pow : c₂ ^ (2 ^ k) = 1 := by
    dsimp [c₂]
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : ((m : ℤ) * v) * ((2 ^ k : ℕ) : ℤ) = (orderOf c : ℤ) * v := by
      rw [hn_eq]; push_cast; ring
    rw [hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hcodd_pow : codd ^ m = 1 := by
    dsimp [codd]
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : ((2 ^ k : ℤ) * u) * ((m : ℕ) : ℤ) = (orderOf c : ℤ) * u := by
      rw [hn_eq]; push_cast; ring
    rw [hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hP : IsPGroup 2 (Subgroup.zpowers c₂) := by
    refine (isPGroup_iff_card_dvd_pow (p := 2) (G := Subgroup.zpowers c₂)).mpr ⟨k, ?_⟩
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc₂_pow
  have hnorm : Subgroup.zpowers c₂ ≤ normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hc₂_mem.1
  let Y : Subgroup G := Subgroup.zpowers c₂ ⊔ Q
  have hYp : IsPGroup 2 Y := hP.to_sup_of_normal_right' hQ.pgroup hnorm
  have hYC : Y ≤ centralizer (D : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hc₂D) hQ.le_centralizer
  have hc₂Y : c₂ ∈ Y := Subgroup.mem_sup_left (Subgroup.mem_zpowers c₂)
  have hc₂Q : c₂ ∈ Q := hQ.maximal Y hYC hYp (le_sup_right : Q ≤ Y) hc₂Y
  have hphi₂ : phiQ hD Q c₂ = 0 :=
    (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq hc₂_mem).2
      (mem_centralizer_iff.2 fun q hq => hQ.comm q hq c₂ hc₂Q)
  have hodd : Odd (orderOf codd) :=
    hm_odd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hcodd_pow)
  have hphi_odd : phiQ hD Q codd = 0 :=
    phiQ_eq_zero_of_odd_order hD hQ hq4 hsq hcodd_mem hodd
  rw [hc_eq, QHyp.phiQ_mul hD hQ hq4 hsq hc₂_mem hcodd_mem, hphi₂, hphi_odd, zero_add]

theorem ThCyc.phiQ_cases (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c = 0 ∨ phiQ hD Q c = phiQ hD Q b ∨
      phiQ hD Q c = phiQ hD Q e ∨
        phiQ hD Q c = phiQ hD Q b + phiQ hD Q e := by
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  have hbK1 : b ∈ ThCyc.K1 H W W2 hD h4 := H.b_mem_K1 W W2 hD h4 hb
  have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have hcK : c ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    QHyp.NV_le_K H W W2 hD h4 hQ hc
  have heK : e ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    QHyp.NV_le_K H W W2 hD h4 hQ he
  have hc_union : c ∈ (ThCyc.K1 H W W2 hD h4 : Set G) ∪
      (fun k => k * e) '' (ThCyc.K1 H W W2 hD h4 : Set G) := by
    rw [← H.K_eq_K1_union_mul_of_mem W W2 hD h4 hb heK heK1]
    exact hcK
  rcases hc_union with hc1 | ⟨k, hk, rfl⟩
  · rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hc1 with hcC | hcCb
    · left
      exact QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq hc hcC
    · right; left
      have hc₀NV : c * b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
        Subgroup.mul_mem _ hc hbNV
      have hzero : phiQ hD Q (c * b) = 0 :=
        QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq hc₀NV hcCb
      calc phiQ hD Q c = phiQ hD Q ((c * b) * b) := by rw [mul_assoc, hbb, mul_one]
        _ = phiQ hD Q b := by
            rw [QHyp.phiQ_mul hD hQ hq4 hsq hc₀NV hbNV, hzero, zero_add]
  · have hkNV : k ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
      have := Subgroup.mul_mem
        (normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) hc
        (Subgroup.inv_mem _ he)
      simpa [mul_assoc] using this
    have hkK1 : k ∈ ThCyc.K1 H W W2 hD h4 := hk
    rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hkK1 with hkC | hkCb
    · right; right; left
      have hzero : phiQ hD Q k = 0 :=
        QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq hkNV hkC
      rw [QHyp.phiQ_mul hD hQ hq4 hsq hkNV he, hzero, zero_add]
    · right; right; right
      have hk₀NV : k * b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
        Subgroup.mul_mem _ hkNV hbNV
      have hzero : phiQ hD Q (k * b) = 0 :=
        QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq hk₀NV hkCb
      have hk_eq : phiQ hD Q k = phiQ hD Q b := by
        calc phiQ hD Q k = phiQ hD Q ((k * b) * b) := by rw [mul_assoc, hbb, mul_one]
          _ = phiQ hD Q b := by
              rw [QHyp.phiQ_mul hD hQ hq4 hsq hk₀NV hbNV, hzero, zero_add]
      rw [QHyp.phiQ_mul hD hQ hq4 hsq hkNV he, hk_eq]

theorem ThCyc.phiQ_ne_of_not_mem_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) :
    phiQ hD Q e ≠ 0 ∧ phiQ hD Q e ≠ phiQ hD Q b := by
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  have hbK1 : b ∈ ThCyc.K1 H W W2 hD h4 := H.b_mem_K1 W W2 hD h4 hb
  have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have hcentralizer : ∀ x ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      x ∈ centralizer (Q : Set G) → x ∈ ThCyc.K1 H W W2 hD h4 := by
    intro x hx hxQ
    refine H.centralizer_le_K1 W W2 hD h4 (mem_centralizer_iff.2 fun d hd => ?_)
    exact mem_centralizer_iff.1 hxQ d (hQ.D_le hd)
  constructor
  · intro hzero
    exact heK1 (hcentralizer e he ((QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq he).1 hzero))
  · intro heq
    have hebNV : e * b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
      Subgroup.mul_mem _ he hbNV
    have hzero : phiQ hD Q (e * b) = 0 := by
      rw [QHyp.phiQ_mul hD hQ hq4 hsq he hbNV, heq]
      exact VSub.add_self hD (phiQ hD Q b)
    have hebK1 : e * b ∈ ThCyc.K1 H W W2 hD h4 :=
      hcentralizer (e * b) hebNV ((QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq hebNV).1 hzero)
    have he_eq : e = (e * b) * b⁻¹ := by group
    exact heK1 (by
      rw [he_eq]
      exact (ThCyc.K1 H W W2 hD h4).mul_mem hebK1
        ((ThCyc.K1 H W W2 hD h4).inv_mem hbK1))

private theorem phiQ_conj_eq (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {n c : G} (hn : n ∈ normalizer (Q : Set G))
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q (n * c * n⁻¹) =
      vConj hD n * phiQ hD Q c * vConj hD n⁻¹ := by
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := QHyp.mem_normalizer_omega1 hD hQ hn
  calc phiQ hD Q (n * c * n⁻¹)
      = phiQ hD Q (n * c * n⁻¹) * 1 := (mul_one _).symm
    _ = phiQ hD Q (n * c * n⁻¹) * (vConj hD n * vConj hD n⁻¹) := by
          rw [vConj_mul_inv hD hnV]
    _ = (phiQ hD Q (n * c * n⁻¹) * vConj hD n) * vConj hD n⁻¹ := by group
    _ = (vConj hD n * phiQ hD Q c) * vConj hD n⁻¹ := by
          rw [QHyp.phiQ_conj hD hQ hq4 hsq hn hc]

private theorem phiQ_b_conj_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G)) : phiQ hD Q (n * b * n⁻¹) = phiQ hD Q b := by
  have hbL : b ∈ L := W.B_le W2.b_mem
  have hnL : n ∈ L := hn.1
  have hnNL : n ∈ normInL L A :=
    mem_normInL.2 ⟨hnL, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
  have hnN : n ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem n hn q hq, fun hq => ?_⟩
    have := hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) (n * q * n⁻¹) hq
    simpa [mul_assoc] using this
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  have hnW5 : n ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_mem_normInL W W2 hD hnNL
  have hnAa : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa := H.Aa_normal W W2 hnW5
  have hxnL : n * b * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hnL hbL) (L.inv_mem hnL)
  have hxnB : n * b * n⁻¹ ∈ B := by
    refine (W.mem_B_iff _ hxnL).2 fun a ha => ?_
    have hna : n⁻¹ * a * n ∈ A := by
      simpa using (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hn.2) a).1 ha
    have hbcomm : b * (n⁻¹ * a * n) = (n⁻¹ * a * n) * b :=
      (W.mem_B_iff b hbL).1 W2.b_mem _ hna
    calc (n * b * n⁻¹) * a = n * (b * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * b) * n⁻¹ := by rw [hbcomm]
      _ = a * (n * b * n⁻¹) := by group
  have hxn_not_Aa : n * b * n⁻¹ ∉ Aa := by
    intro hxA
    have hbAa : b ∈ Aa := by
      have := H.Aa_normal W W2 ((normalizer ((W5 A t : Subgroup G) : Set G)).inv_mem hnW5)
        (n * b * n⁻¹) hxA
      simpa [mul_assoc] using this
    exact W2.b_not_mem hbAa
  have hb2 : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have hyNV : n * b * n⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    QHyp.conj_mem_NV hD hQ hq4 hsq hnN hbNV
  rcases W2.mem_Aa_or_mul_b W hxnB with h | h
  · exact absurd h hxn_not_Aa
  · have hy_eq : (n * b * n⁻¹ * b) * b = n * b * n⁻¹ := by
      rw [mul_assoc, hb2, mul_one]
    have ha₀NV : n * b * n⁻¹ * b ∈ normalizer (Q : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G) := Subgroup.mul_mem _ hyNV hbNV
    have ha₀D : n * b * n⁻¹ * b ∈ centralizer (D : Set G) :=
      mem_centralizer_iff.2 fun d hd =>
        (hD.comm _ (hD.Aa_le h) d hd).symm
    have hzero : phiQ hD Q (n * b * n⁻¹ * b) = 0 :=
      QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq ha₀NV ha₀D
    rw [← hy_eq, QHyp.phiQ_mul hD hQ hq4 hsq ha₀NV hbNV, hzero, zero_add]

private theorem B_le_Hn (W : ThLocalIn L S A B z) : B ≤ L ⊓ normalizer (A : Set G) := by
  intro x hx
  refine ⟨W.B_le hx, mem_normalizer_iff.2 fun a => ⟨?_, ?_⟩⟩
  · intro ha
    have hcomm : x * a = a * x := (W.mem_B_iff x (W.B_le hx)).1 hx a ha
    have hconj : x * a * x⁻¹ = a := by
      calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [hcomm]
        _ = a := by group
    rwa [hconj]
  · intro ha
    have hx'inv : x⁻¹ ∈ B := B.inv_mem hx
    have hcomm : x⁻¹ * (x * a * x⁻¹) = (x * a * x⁻¹) * x⁻¹ :=
      (W.mem_B_iff x⁻¹ (W.B_le hx'inv)).1 hx'inv (x * a * x⁻¹) ha
    have ha' : a = x * a * x⁻¹ := by
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = (x * a * x⁻¹) * x⁻¹ * x := by rw [hcomm]
        _ = x * a * x⁻¹ := by group
    rwa [ha']

private theorem vConj_eq_one_of_mem_B (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {x : G} (hx : x ∈ B) : vConj hD x = 1 := by
  have hxHn : x ∈ L ⊓ normalizer (A : Set G) := B_le_Hn W hx
  have hxNL : x ∈ normInL L A :=
    mem_normInL.2 ⟨hxHn.1, fun a ha => (mem_normalizer_iff.1 hxHn.2 a).1 ha⟩
  have hxV : x ∈ normalizer (omega1 D hD.comm : Set G) :=
    H.normalizer_le_normalizer_omega1 W W2 hD
      (H.mem_normalizer_W5_of_mem_normInL W W2 hD hxNL)
  refine AbelianSub.end_ext fun v => ?_
  rw [val_vConj_apply hD hxV v]
  change x * v.val * x⁻¹ = v.val
  exact H.comm_omega1_of_mem_B W W2 hD hb hx (AbelianSub.val_mem v)

private theorem vConj_phiQ_b_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    vConj hD n * phiQ hD Q b * vConj hD n⁻¹ = phiQ hD Q b := by
  have hnQ : n ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem n hn q hq, fun hq => ?_⟩
    have := hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) (n * q * n⁻¹) hq
    simpa [mul_assoc] using this
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  rw [← phiQ_conj_eq hD hQ hq4 hsq hnQ hbNV]
  exact phiQ_b_conj_eq H W W2 hD h4 hb hQ hq4 hsq hn

private theorem phiQ_b_ne_zero (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) :
    phiQ hD Q b ≠ 0 := by
  intro hzero
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  have hbCQ : b ∈ centralizer (Q : Set G) :=
    (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq hbNV).1 hzero
  refine ThCyc.b_not_mem_centralizer_D W W2 hD hb (mem_centralizer_iff.2 fun d hd => ?_)
  exact mem_centralizer_iff.1 hbCQ d (hQ.D_le hd)

private theorem phiQ_b_add_e_ne_e (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} : phiQ hD Q b + phiQ hD Q e ≠ phiQ hD Q e := by
  intro h
  have h' : phiQ hD Q b + phiQ hD Q e = 0 + phiQ hD Q e := by
    rw [zero_add]
    exact h
  have hzero : phiQ hD Q b = 0 := add_right_cancel h'
  exact phiQ_b_ne_zero H W W2 hD h4 hb hQ hq4 hsq hzero

private theorem Hn_mem_normalizer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    n ∈ normalizer (omega1 D hD.comm : Set G) := by
  have hnNL : n ∈ normInL L A :=
    mem_normInL.2 ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
  exact H.normalizer_le_normalizer_omega1 W W2 hD
    (H.mem_normalizer_W5_of_mem_normInL W W2 hD hnNL)

private theorem phiQ_conj_e_cases (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    phiQ hD Q (n * e * n⁻¹) = phiQ hD Q e ∨
      phiQ hD Q (n * e * n⁻¹) = phiQ hD Q b + phiQ hD Q e := by
  have hnQ : n ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem n hn q hq, fun hq => ?_⟩
    have := hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) (n * q * n⁻¹) hq
    simpa [mul_assoc] using this
  have he' : n * e * n⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    QHyp.conj_mem_NV hD hQ hq4 hsq hnQ he
  have hcases := ThCyc.phiQ_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 he'
  have hne := ThCyc.phiQ_ne_of_not_mem_K1 H W W2 hD h4 hb hQ hq4 hsq he heK1
  rcases hcases with h0 | hb' | he' | hsum
  · exfalso
    have hq : phiQ hD Q e = vConj hD n⁻¹ * phiQ hD Q (n * e * n⁻¹) *
        vConj hD (n⁻¹)⁻¹ := by
      have := phiQ_conj_eq hD hQ hq4 hsq
        ((normalizer (Q : Set G)).inv_mem hnQ) he'
      simpa [mul_assoc] using this
    rw [h0] at hq
    exact hne.1 (by simpa using hq)
  · exfalso
    have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
    have hninv : n⁻¹ ∈ L ⊓ normalizer (A : Set G) :=
      (L ⊓ normalizer (A : Set G)).inv_mem hn
    have hq : phiQ hD Q e = vConj hD n⁻¹ * phiQ hD Q (n * e * n⁻¹) *
        vConj hD (n⁻¹)⁻¹ := by
      have := phiQ_conj_eq hD hQ hq4 hsq ((normalizer (Q : Set G)).inv_mem hnQ) he'
      simpa [mul_assoc] using this
    rw [hb'] at hq
    have hfixb := vConj_phiQ_b_eq H W W2 hD h4 hb hQ hq4 hsq hninv
    have := hq.trans hfixb
    exact hne.2 this
  · exact Or.inl he'
  · exact Or.inr hsum

private noncomputable def swapVal (hD : DHyp A Aa t D) (Q : Subgroup G) (e : G)
    (n : ↥(L ⊓ normalizer (A : Set G))) : ZMod 2 := by
  classical
  exact if vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ = phiQ hD Q e then 0 else 1

private theorem swapVal_eq_zero_of (hD : DHyp A Aa t D) (Q : Subgroup G) (e : G)
    {n : ↥(L ⊓ normalizer (A : Set G))}
    (h : vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ = phiQ hD Q e) :
    swapVal hD Q e n = 0 := by
  rw [swapVal, if_pos h]

private theorem swapVal_eq_one_of (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} {n : ↥(L ⊓ normalizer (A : Set G))}
    (h : vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ =
      phiQ hD Q b + phiQ hD Q e) : swapVal hD Q e n = 1 := by
  have hne : vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ ≠ phiQ hD Q e := by
    intro h'
    exact phiQ_b_add_e_ne_e H W W2 hD h4 hb hQ hq4 hsq (h.symm.trans h')
  rw [swapVal, if_neg hne]

private theorem swapVal_cases (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) (n : ↥(L ⊓ normalizer (A : Set G))) :
    (swapVal hD Q e n = 0 ∧ vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ =
      phiQ hD Q e) ∨
    (swapVal hD Q e n = 1 ∧ vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ =
      phiQ hD Q b + phiQ hD Q e) := by
  have hnQ : (n : G) ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem _ n.2 q hq, fun hq => ?_⟩
    have := hQ.conj_mem _ ((L ⊓ normalizer (A : Set G)).inv_mem n.2) ((n : G) * q * (n : G)⁻¹) hq
    simpa [mul_assoc] using this
  have hconj : vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ =
      phiQ hD Q ((n : G) * e * (n : G)⁻¹) :=
    (phiQ_conj_eq hD hQ hq4 hsq hnQ he).symm
  rcases phiQ_conj_e_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 n.2 with h | h
  · exact Or.inl ⟨swapVal_eq_zero_of hD Q e (by rw [hconj, h]),
      by rw [hconj, h]⟩
  · exact Or.inr ⟨swapVal_eq_one_of H W W2 hD h4 hb hQ hq4 hsq (by rw [hconj, h]),
      by rw [hconj, h]⟩

private theorem swap_conj_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (Q : Subgroup G) {e : G}
    (n m : ↥(L ⊓ normalizer (A : Set G))) :
    vConj hD ((n : G) * (m : G)) * phiQ hD Q e * vConj hD ((n : G) * (m : G))⁻¹ =
      vConj hD (n : G) * (vConj hD (m : G) * phiQ hD Q e *
        vConj hD (m : G)⁻¹) * vConj hD (n : G)⁻¹ := by
  have hnV : (n : G) ∈ normalizer (omega1 D hD.comm : Set G) :=
    Hn_mem_normalizer_omega1 H W W2 hD n.2
  have hmV : (m : G) ∈ normalizer (omega1 D hD.comm : Set G) :=
    Hn_mem_normalizer_omega1 H W W2 hD m.2
  have hmV' : (m : G)⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hmV
  have hnV' : (n : G)⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hnV
  have hnm : vConj hD ((n : G) * (m : G)) = vConj hD (n : G) * vConj hD (m : G) :=
    vConj_mul hD hnV hmV
  have hnm_inv : vConj hD ((n : G) * (m : G))⁻¹ = vConj hD (m : G)⁻¹ * vConj hD (n : G)⁻¹ := by
    have h := vConj_mul hD hmV' hnV'
    rwa [show (m : G)⁻¹ * (n : G)⁻¹ = ((n : G) * (m : G))⁻¹ by group] at h
  rw [hnm, hnm_inv]
  simp only [mul_assoc]

private theorem swapVal_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4)
    (n m : ↥(L ⊓ normalizer (A : Set G))) :
    swapVal hD Q e (n * m) = swapVal hD Q e n + swapVal hD Q e m := by
  have hnm := swap_conj_mul H W W2 hD Q (e := e) n m
  have hb2 : (m : G) ∈ L ⊓ normalizer (A : Set G) := m.2
  rcases swapVal_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 n with ⟨hn0, hnf⟩ | ⟨hn1, hns⟩
  · rcases swapVal_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 m with ⟨hm0, hmf⟩ | ⟨hm1, hms⟩
    · have hc : vConj hD ((n : G) * (m : G)) * phiQ hD Q e *
          vConj hD ((n : G) * (m : G))⁻¹ = phiQ hD Q e := by
        rw [hnm, hmf, hnf]
      rw [swapVal_eq_zero_of hD Q e hc, hn0, hm0]
      decide
    · have hc : vConj hD ((n : G) * (m : G)) * phiQ hD Q e *
          vConj hD ((n : G) * (m : G))⁻¹ = phiQ hD Q b + phiQ hD Q e := by
        rw [hnm, hms]
        calc vConj hD (n : G) * (phiQ hD Q b + phiQ hD Q e) * vConj hD (n : G)⁻¹
            = vConj hD (n : G) * phiQ hD Q b * vConj hD (n : G)⁻¹ +
              vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ := by
              rw [mul_add, add_mul]
          _ = phiQ hD Q b + phiQ hD Q e := by
              rw [vConj_phiQ_b_eq H W W2 hD h4 hb hQ hq4 hsq n.2, hnf]
      rw [swapVal_eq_one_of H W W2 hD h4 hb hQ hq4 hsq hc, hn0, hm1]
      decide
  · rcases swapVal_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 m with ⟨hm0, hmf⟩ | ⟨hm1, hms⟩
    · have hc : vConj hD ((n : G) * (m : G)) * phiQ hD Q e *
          vConj hD ((n : G) * (m : G))⁻¹ = phiQ hD Q b + phiQ hD Q e := by
        rw [hnm, hmf, hns]
      rw [swapVal_eq_one_of H W W2 hD h4 hb hQ hq4 hsq hc, hn1, hm0]
      decide
    · have hc : vConj hD ((n : G) * (m : G)) * phiQ hD Q e *
          vConj hD ((n : G) * (m : G))⁻¹ = phiQ hD Q e := by
        rw [hnm, hms]
        calc vConj hD (n : G) * (phiQ hD Q b + phiQ hD Q e) * vConj hD (n : G)⁻¹
            = vConj hD (n : G) * phiQ hD Q b * vConj hD (n : G)⁻¹ +
              vConj hD (n : G) * phiQ hD Q e * vConj hD (n : G)⁻¹ := by
              rw [mul_add, add_mul]
          _ = phiQ hD Q b + (phiQ hD Q b + phiQ hD Q e) := by
              rw [vConj_phiQ_b_eq H W W2 hD h4 hb hQ hq4 hsq n.2, hns]
          _ = phiQ hD Q e := by
              rw [← add_assoc, VSub.add_self hD, zero_add]
      rw [swapVal_eq_zero_of hD Q e hc, hn1, hm1]
      decide

private noncomputable def swapHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) :
    ↥(L ⊓ normalizer (A : Set G)) →* Multiplicative (ZMod 2) where
  toFun n := Multiplicative.ofAdd (swapVal hD Q e n)
  map_one' := by
    apply Multiplicative.ofAdd.injective
    change swapVal hD Q e 1 = 0
    apply swapVal_eq_zero_of
    show vConj hD (1 : G) * phiQ hD Q e * vConj hD (1 : G)⁻¹ = phiQ hD Q e
    simp [vConj_one hD]
  map_mul' n m := by
    rw [← ofAdd_add]
    exact congrArg Multiplicative.ofAdd
      (swapVal_mul H W W2 hD h4 hb hQ hq4 hsq he heK1 n m)

private theorem swapHom_eq_one_of_mem_B (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4)
    (x : ↥(L ⊓ normalizer (A : Set G))) (hx : (x : G) ∈ B) :
    swapHom H W W2 hD h4 hb hQ hq4 hsq he heK1 x = 1 := by
  change Multiplicative.ofAdd (swapVal hD Q e x) = 1
  have hvx : vConj hD (x : G) = 1 := vConj_eq_one_of_mem_B H W W2 hD hb hx
  have hvx' : vConj hD (x : G)⁻¹ = 1 :=
    vConj_eq_one_of_mem_B H W W2 hD hb (B.inv_mem hx)
  have hfix : vConj hD (x : G) * phiQ hD Q e * vConj hD (x : G)⁻¹ = phiQ hD Q e := by
    rw [hvx, hvx']; simp
  rw [swapVal_eq_zero_of hD Q e hfix]
  rfl

theorem ThCyc.vConj_commute_phiQ (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (he : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) {c : G}
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    vConj hD n * phiQ hD Q c = phiQ hD Q c * vConj hD n := by
  have hbNV := ThCyc.b_mem_NV W W2 hD hb hQ
  have hnQ : n ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem n hn q hq, fun hq => ?_⟩
    have := hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) (n * q * n⁻¹) hq
    simpa [mul_assoc] using this
  have hntriv : ∀ x : ↥(L ⊓ normalizer (A : Set G)),
      swapHom H W W2 hD h4 hb hQ hq4 hsq he heK1 x = 1 := by
    refine ThLocalIn.map_eq_one_of_card_lt W (swapHom H W W2 hD h4 hb hQ hq4 hsq he heK1) ?_
      (fun x hx => swapHom_eq_one_of_mem_B H W W2 hD h4 hb hQ hq4 hsq he heK1 x hx)
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
    norm_num
  have hfixe : vConj hD n * phiQ hD Q e * vConj hD n⁻¹ = phiQ hD Q e := by
    have hx := hntriv ⟨n, hn⟩
    have hzero : swapVal hD Q e ⟨n, hn⟩ = 0 := by
      simpa [swapHom] using congrArg Multiplicative.toAdd hx
    by_contra hne
    have hone : swapVal hD Q e ⟨n, hn⟩ = 1 := by rw [swapVal, if_neg hne]
    rw [hzero] at hone
    exact zero_ne_one hone
  have hnb : vConj hD n * phiQ hD Q b = phiQ hD Q b * vConj hD n := by
    have h := QHyp.phiQ_conj hD hQ hq4 hsq hnQ hbNV
    rw [phiQ_b_conj_eq H W W2 hD h4 hb hQ hq4 hsq hn] at h
    exact h.symm
  have hne : vConj hD n * phiQ hD Q e = phiQ hD Q e * vConj hD n := by
    have h := QHyp.phiQ_conj hD hQ hq4 hsq hnQ he
    have hfix : phiQ hD Q (n * e * n⁻¹) = phiQ hD Q e := by
      rw [phiQ_conj_eq hD hQ hq4 hsq hnQ he]
      exact hfixe
    rw [hfix] at h
    exact h.symm
  rcases ThCyc.phiQ_cases H W W2 hD h4 hb hQ hq4 hsq he heK1 hc with h0 | hb' | he' | hsum
  · rw [h0, mul_zero, zero_mul]
  · rw [hb']; exact hnb
  · rw [he']; exact hne
  · rw [hsum, mul_add, add_mul, hnb, hne]


module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealBBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealNF
public import Certificates.Certificate22220
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsRealBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

theorem realBParts : RealBParts := by
  have h := Certificates.certificate22220
  simp only [realBOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem invIdx_spec {k : ℕ} (hk : k < 64) :
    invIdx k < 64 ∧ (t1Entry k (invIdx k)).1 = 0 := by
  have h := realBParts.c2
  simp only [c2OK, invIdxOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  exact h.1 k hk

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem mulM_lt {x y : MElt} (hx : x.1 < 64) (hy : y.1 < 64) :
    (mulM x y).1 < 64 :=
  t1_lt hx hy

theorem betaRepM_lt {i : ℕ} (hi : i < 36) {x : MElt}
    (hx : x.1 < 64) : (betaRepM i x).1 < 64 :=
  alpha_lt hi hx

theorem invM_lt {x : MElt} (hx : x.1 < 64) : (invM x).1 < 64 :=
  (invIdx_spec hx).1

theorem betaYM_lt {t i : ℕ}
    (ht : t < 64) (hi : i < 36) {x : MElt} (hx : x.1 < 64) : (betaYM t i x).1 < 64 :=
  mulM_lt (mulM_lt ht (betaRepM_lt hi hx)) (invM_lt (x := (t, 0, 0)) ht)

section Setting

theorem nfM_mul (h : IsQSetting q l) {x y : MElt} (hx : x.1 < 64) (hy : y.1 < 64) :
    nfM l x * nfM l y = nfM l (mulM x y) :=
  nf_mul h hx hy _ _ _ _

theorem nfM_inv (h : IsQSetting q l) {x : MElt} (hx : x.1 < 64) :
    (nfM l x)⁻¹ = nfM l (invM x) := by
  obtain ⟨k, a, b⟩ := x
  have hk : k < 64 := hx
  obtain ⟨hi, h0⟩ := invIdx_spec hk
  have e1 : nfM l (k, a, b) = nf l k 0 0 * zz l a b := by
    show l (cv (tw k)) * zz l a b = l (cv (tw k)) * zz l 0 0 * zz l a b
    rw [zz_zero, mul_one]
  rw [e1, mul_inv_rev, nf_inv h hk hi h0, zz_inv]
  show zz l (-a) (-b) * (l (cv (tw (invIdx k))) * zz l _ _) =
    l (cv (tw (invIdx k))) * zz l _ _
  rw [← mul_assoc, ← zz_comm h (-a) (-b) (l (cv (tw (invIdx k)))), mul_assoc, zz_mul]
  have e2 : -a + -((t1Entry k (invIdx k)).2.1 : ZMod 4) =
      -((t1Entry k (invIdx k)).2.1 : ZMod 4) - a := by
    ring
  have e3 : -b + -((t1Entry k (invIdx k)).2.2.1 : ZMod 4) =
      -((t1Entry k (invIdx k)).2.2.1 : ZMod 4) - b := by ring
  rw [e2, e3]
  rfl

theorem q_nfM (h : IsQSetting q l) {x : MElt} (hx : x.1 < 64) : q (nfM l x) = wordPerm (tg x.1) :=
  q_nf h hx _ _

theorem eqKM_iff (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x y : MElt} (hx : x.1 < 64)
    (hy : y.1 < 64) : eqKM κ x y = true ↔ nfM l x = nfM l y := by
  rw [nfM, nfM, nf_eq_iff h hx hy, hκ, eqKM, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    inKC_iff]

theorem betaY_nfM
    (h : IsQSetting q l) {β : E ≃* E} {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hβ : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)))
    {x : MElt} (hx : x.1 < 64) : β (nfM l x) = nfM l (betaYM t i x) := by
  set β' : E ≃* E := β.trans (MulAut.conj (nf l t 0 0)⁻¹) with hβ'
  have hβ'e : ∀ e, β' e = (nf l t 0 0)⁻¹ * β e * nf l t 0 0 := fun e => by
    rw [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hβ'w : ∀ w, β' (l (cv w)) = l (cv (substWord (aut i) w)) := fun w => by
    rw [hβ'e, hβ]
  have h1 := beta_nf h hi hx hβ'w x.2.1 x.2.2
  have ht' : (t, (0 : ZMod 4), (0 : ZMod 4)).1 < 64 := ht
  have e1 : β (nfM l x) = nfM l (t, 0, 0) * β' (nfM l x) * (nfM l (t, 0, 0))⁻¹ := by
    rw [hβ'e]
    simp only [nfM]
    group
  have h1' : β' (nfM l x) = nfM l (betaRepM i x) := h1
  rw [e1, nfM_inv h ht', h1', nfM_mul h ht' (betaRepM_lt hi hx),
    nfM_mul h (mulM_lt ht' (betaRepM_lt hi hx)) (invM_lt ht')]
  rfl

theorem liftsK_of (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {β : E ≃* E} {i : ℕ} (hi : i < 36)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut i) w))) : liftsK κ i = true := by
  unfold liftsK
  rw [List.all_eq_true]
  intro m _
  rw [decide_eq_true_eq, inKC_iff, ← hκ, ← beta_zz h hi hβ, (hκ _ _).2 ⟨m, rfl, rfl⟩, map_one]

theorem nfM_mem_bHat
    (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x : MElt} (hx : x.1 < 64)
    (hb : isBhM κ x = true) : nfM l x ∈ l34BHat q := by
  simp only [isBhM, Bool.and_eq_true] at hb
  refine ⟨by rw [q_nfM h hx]; exact tg_mem_T0 _ hx, fun t ht => ?_, ?_⟩
  · rw [q_nfM h hx]
    have hz : x.1 ∈ [0, 4, 8, 12] := by simpa [zT0] using hb.1
    exact (mem_centralizer_iff.mp (tg_mem_centralizer_T0 hz) t ht).symm
  · rw [nfM_mul h hx hx, ← nfM_one]
    exact (eqKM_iff h hκ (mulM_lt hx hx) (by decide)).1 hb.2

theorem isBhM_of_mem
    (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x : MElt} (hx : x.1 < 64)
    (hb : nfM l x ∈ l34BHat q) : isBhM κ x = true := by
  obtain ⟨hT, hc, h2⟩ := hb
  simp only [isBhM, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk, hke⟩ := mem_center_T0 hT fun t' ht' => (hc t' ht')
    rw [q_nfM h hx] at hke
    have hk64 : k < 64 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      omega
    have := tg_injective hk64 hx hke
    subst this
    simpa [zT0] using hk
  · rw [eqKM_iff h hκ (mulM_lt hx hx) (by decide), ← nfM_mul h hx hx, nfM_one]
    exact h2

theorem nfM_mem_aHat
    (h : IsQSetting q l)
    {κ : ZMod 4 × ZMod 4} (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x : MElt}
    (hx : x.1 < 64) (ha : isAhM κ x = true) : nfM l x ∈ l34AHat q := by
  refine ⟨by rw [q_nfM h hx]; exact tg_mem_T0 _ hx, fun b hb => ?_⟩
  obtain ⟨k, hk, i, j, rfl⟩ := exists_nf h hb.1
  have hbM := isBhM_of_mem (x := (k, i, j)) h hκ hk hb
  unfold isAhM at ha
  rw [List.all_eq_true] at ha
  have := ha (k, i, j) (mem_allM hk)
  rw [hbM, Bool.not_true, Bool.false_or, eqKM_iff h hκ (mulM_lt hx hk) (mulM_lt hk hx),
    ← nfM_mul h hx hk, ← nfM_mul h hk hx] at this
  exact this

theorem isAhM_of_mem
    (h : IsQSetting q l)
    {κ : ZMod 4 × ZMod 4} (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x : MElt}
    (hx : x.1 < 64) (ha : nfM l x ∈ l34AHat q) : isAhM κ x = true := by
  unfold isAhM
  rw [List.all_eq_true]
  intro b hb
  have hb64 := lt_of_mem_allM hb
  cases hB : isBhM κ b
  · rfl
  · rw [Bool.not_true, Bool.false_or, eqKM_iff h hκ (mulM_lt hx hb64) (mulM_lt hb64 hx),
      ← nfM_mul h hx hb64, ← nfM_mul h hb64 hx]
    exact ha.2 _ (nfM_mem_bHat h hκ hb64 hB)

theorem fixBM_of
    (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {β : E ≃* E} {t i : ℕ} (ht : t < 64)
    (hi : i < 36)
    (hβ : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)))
    (hB : ∀ b ∈ l34BHat q, β b = b) : fixBM κ t i = true := by
  unfold fixBM
  rw [List.all_eq_true]
  intro x hx
  have hx64 := lt_of_mem_allM hx
  cases hxB : isBhM κ x
  · rfl
  · rw [Bool.not_true, Bool.false_or, eqKM_iff h hκ (betaYM_lt ht hi hx64) hx64,
      ← betaY_nfM h ht hi hβ hx64]
    exact hB _ (nfM_mem_bHat h hκ hx64 hxB)

end Setting

theorem c2_spec {κ : ZMod 4 × ZMod 4} (hκ : κ ∈ kGens) {i : ℕ}
    (hi : i < 36) (hl : liftsK κ i = true) {t : ℕ} (ht : t < 64) (hf : fixBM κ t i = true) :
    pow4M t i = true := by
  have h := realBParts.c2
  simp only [c2OK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_range] at h
  rcases h.2 κ (kGensC_eq ▸ hκ) i hi with h1 | h1
  · rw [hl] at h1
    exact Bool.noConfusion h1
  · rcases h1 t ht with h2 | h2
    · rw [hf] at h2
      exact Bool.noConfusion h2
    · exact h2

end CFSG.ComponentClassification.GrSLit.L34Facts.Real

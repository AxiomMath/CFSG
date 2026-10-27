module

public import Certificates.Data.Kernel.ConjRec
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Mathlib.GroupTheory.Sylow
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.L34KSnd.Tab
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Mathlib

public section

namespace CFSG.KC.ConjRec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep)

section Group

variable {G : Type} [Group G] [Finite G]

theorem no_orderOf_ten {H : Subgroup G} {m : ℕ} (hH : Nat.card H = 5 * m) (hm : ¬ 5 ∣ m)
    {t : G} (htH : t ∈ H) (ht : orderOf t = 5) (L : List G)
    (hL : ∀ e ∈ L, ∃ g ∈ H, e = g * t * g⁻¹) (hd : L.Nodup) (hlen : Nat.card H < 10 * L.length) :
    ∀ z ∈ H, orderOf z ≠ 10 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro z hz hz10
  set T : H := ⟨t, htH⟩ with hTdef
  set Z : H := ⟨z, hz⟩ with hZdef
  have hT5 : orderOf T = 5 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hZ10 : orderOf Z = 10 := by rw [← Subgroup.orderOf_coe]; exact hz10
  set C := MulAction.stabilizer (ConjAct H) T with hC
  have hmemC : ∀ x : H, x * T * x⁻¹ = T → ConjAct.toConjAct x ∈ C := by
    intro x hx
    rw [hC, MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul]
    exact hx
  have : Finite (ConjAct H) := Finite.of_equiv H ConjAct.toConjAct.toEquiv
  have hcard : Nat.card C * Nat.card (MulAction.orbit (ConjAct H) T) = Nat.card H := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
    exact Nat.card_congr (ConjAct.toConjAct (G := H)).toEquiv.symm
  have hLen : L.length ≤ Nat.card (MulAction.orbit (ConjAct H) T) := by
    classical
    have hsub : (L.toFinset : Set G) ⊆
        (H.subtype '' (MulAction.orbit (ConjAct H) T) : Set G) := by
      intro e he
      simp only [Finset.mem_coe, List.mem_toFinset] at he
      obtain ⟨g, hg, rfl⟩ := hL e he
      refine ⟨ConjAct.toConjAct (⟨g, hg⟩ : H) • T, MulAction.mem_orbit _ _, ?_⟩
      rw [ConjAct.toConjAct_smul]
      rfl
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hd,
      Set.ncard_image_of_injective _ H.subtype_injective, ← Nat.card_coe_set_eq] at h1
    exact h1
  have hC10 : Nat.card C < 10 := by
    by_contra hge
    have : 10 * L.length ≤ Nat.card H := by
      rw [← hcard]
      exact Nat.mul_le_mul (not_lt.mp hge) hLen
    omega
  have hidx : ∀ P : Subgroup H, Nat.card P = 5 → ¬ 5 ∣ P.index := by
    intro P hP h5
    have h := P.card_mul_index
    rw [hP, hH] at h
    have h' : P.index = m := by omega
    exact hm (h' ▸ h5)
  have hp5 : ∀ P : Subgroup H, Nat.card P = 5 → IsPGroup 5 P := fun P hP =>
    IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  set a := Z ^ 2 with ha
  have ha5 : orderOf a = 5 := by
    rw [ha, orderOf_pow_of_dvd (by norm_num) (by rw [hZ10]; norm_num), hZ10]
  have hPc : Nat.card (Subgroup.zpowers T) = 5 := by rw [Nat.card_zpowers, hT5]
  have hQc : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, ha5]
  let PS : Sylow 5 H := (hp5 _ hPc).toSylow (hidx _ hPc)
  let QS : Sylow 5 H := (hp5 _ hQc).toSylow (hidx _ hQc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H QS PS
  have hPeq : Subgroup.zpowers T = (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • QS : Sylow 5 H) : Subgroup H) = (PS : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  rw [MonoidHom.map_zpowers] at hPeq
  set y := g * Z * g⁻¹ with hy
  have hy2 : (MulAut.conj g).toMonoidHom a = y ^ 2 := by
    rw [hy, conj_pow, ha]
    rfl
  rw [hy2] at hPeq
  have hTy : T ∈ Subgroup.zpowers (y ^ 2) := hPeq ▸ Subgroup.mem_zpowers T
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hTy
  have hcomm : y ^ 5 * T * (y ^ 5)⁻¹ = T := by
    rw [← hk]
    have hc : Commute (y ^ 5) ((y ^ 2) ^ k) := ((Commute.refl y).pow_pow 5 2).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
  have hy5 : orderOf (y ^ 5) = 2 := by
    rw [hy, conj_pow]
    have h := MulEquiv.orderOf_eq (MulAut.conj g) (Z ^ 5)
    rw [MulAut.conj_apply] at h
    rw [h, orderOf_pow_of_dvd (by norm_num) (by rw [hZ10]; norm_num), hZ10]
  have h2 : 2 ∣ Nat.card C := by
    have h := Subgroup.orderOf_dvd_natCard C (hmemC _ hcomm)
    rwa [MulEquiv.orderOf_eq, hy5] at h
  have h5 : 5 ∣ Nat.card C := by
    have h := Subgroup.orderOf_dvd_natCard C (hmemC T (by group))
    rwa [MulEquiv.orderOf_eq, hT5] at h
  have h10 : 10 ∣ Nat.card C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 5) h2 h5
  have hpos : 0 < Nat.card C := Nat.card_pos
  have := Nat.le_of_dvd hpos h10
  omega

end Group

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_iff {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem bIf_iff {c t e : Bool} : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem allBlk_true {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true at h
    rw [bAnd_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact allBlk_true h.2 l hl
    · exact h.1

theorem okO_spec {n w cw pb X XI Y YI R T N i : Nat}
    (h : okO n w cw pb X XI Y YI R T N i = true) :
    let r := fun j => rdO (cw + (pb + 6)) T j
    (i + 1 = N ∨ fldO (r i) 0 cw < fldO (r (i + 1)) 0 cw) ∧ fldO (r i) cw pb < N ∧
      (fldO (r i) (cw + (pb + 1)) 5 = 0 → fldO (r i) 0 cw = R) ∧
      (fldO (r i) (cw + (pb + 1)) 5 ≠ 0 →
        fldO (r (fldO (r i) cw pb)) (cw + (pb + 1)) 5 + 1 = fldO (r i) (cw + (pb + 1)) 5 ∧
        fldO (r i) 0 cw = cjO n w X XI Y YI (fldO (r i) (cw + pb) 1)
          (fldO (r (fldO (r i) cw pb)) 0 cw)) := by
  intro r
  unfold okO okRec at h
  simp only [strictB_eq, Nat.add_eq, Nat.succ_eq_add_one] at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [bAnd_iff] at h2
  obtain ⟨h2, h3⟩ := h2
  refine ⟨?_, Nat.blt_eq.mp h2, fun hd => ?_, fun hd => ?_⟩
  · rw [bIf_iff] at h1
    rcases h1 with ⟨hc, -⟩ | ⟨-, hlt⟩
    · exact Or.inl (Nat.eq_of_beq_eq_true hc)
    · exact Or.inr (Nat.blt_eq.mp hlt)
  · rw [bIf_iff] at h3
    rcases h3 with ⟨-, he⟩ | ⟨hc, -⟩
    · exact Nat.eq_of_beq_eq_true he
    · have hd' : fldO (rdO (cw + (pb + 6)) T i) (cw + (pb + 1)) 5 = 0 := hd
      rw [hd'] at hc
      simp at hc
  · rw [bIf_iff] at h3
    rcases h3 with ⟨hc, -⟩ | ⟨-, h4⟩
    · exact absurd (Nat.eq_of_beq_eq_true hc) hd
    · rw [bAnd_iff] at h4
      exact ⟨Nat.eq_of_beq_eq_true h4.1, Nat.eq_of_beq_eq_true h4.2⟩

variable {n w : Nat}

theorem tabRep_pcomp {p q : Nat} {a b : Equiv.Perm (Fin n)}
    (hp : canonK n w (mask w) (n * w) p = true) (hq : canonK n w (mask w) (n * w) q = true)
    (ha : TabRep (unpack n w p) a) (hb : TabRep (unpack n w q) b) :
    TabRep (unpack n w (pcomp n w (mask w) p q)) (a * b) := by
  rw [← CFSG.KC.L34KSnd.comp_unpack' hp hq]
  exact ha.comp hb

theorem conj_step {s si e : Nat} {a b : Equiv.Perm (Fin n)}
    (hs : canonK n w (mask w) (n * w) s = true) (hsi : canonK n w (mask w) (n * w) si = true)
    (he : canonK n w (mask w) (n * w) e = true) (hsr : TabRep (unpack n w s) a)
    (hsir : TabRep (unpack n w si) a⁻¹) (her : TabRep (unpack n w e) b) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) s (pcomp n w (mask w) e si)) = true ∧
      TabRep (unpack n w (pcomp n w (mask w) s (pcomp n w (mask w) e si))) (a * b * a⁻¹) := by
  have hc1 := CFSG.KC.BfsPin.canonK_pcomp he hsi
  refine ⟨CFSG.KC.BfsPin.canonK_pcomp hs hc1, ?_⟩
  rw [mul_assoc]
  exact tabRep_pcomp hs hc1 hsr (tabRep_pcomp he hsi her hsir)

theorem conjRec_sound {cw pb X XI Y YI R T N : Nat} {x y t : Equiv.Perm (Fin n)}
    (hcw : cw = n * w)
    (hX : canonK n w (mask w) (n * w) X = true) (hXr : TabRep (unpack n w X) x)
    (hXI : canonK n w (mask w) (n * w) XI = true) (hXIr : TabRep (unpack n w XI) x⁻¹)
    (hY : canonK n w (mask w) (n * w) Y = true) (hYr : TabRep (unpack n w Y) y)
    (hYI : canonK n w (mask w) (n * w) YI = true) (hYIr : TabRep (unpack n w YI) y⁻¹)
    (hR : canonK n w (mask w) (n * w) R = true) (hRr : TabRep (unpack n w R) t)
    (h : ∀ i < N, okO n w cw pb X XI Y YI R T N i = true) :
    ∃ L : List (Equiv.Perm (Fin n)), L.length = N ∧ L.Nodup ∧
      ∀ e ∈ L, ∃ g ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin n))), e = g * t * g⁻¹ := by
  subst hcw
  set r := fun j => rdO (n * w + (pb + 6)) T j with hr
  set c := fun j => fldO (r j) 0 (n * w) with hc
  set d := fun j => fldO (r j) (n * w + (pb + 1)) 5 with hd
  set p := fun j => fldO (r j) (n * w) pb with hp
  set H := Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin n))) with hH
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have key : ∀ k, ∀ i < N, d i = k → canonK n w (mask w) (n * w) (c i) = true ∧
      ∃ g ∈ H, TabRep (unpack n w (c i)) (g * t * g⁻¹) := by
    intro k
    induction k with
    | zero =>
      intro i hi hdi
      have hs := (okO_spec (h i hi)).2.2.1 hdi
      change c i = R at hs
      rw [hs]
      exact ⟨hR, 1, H.one_mem, by simpa using hRr⟩
    | succ k ih =>
      intro i hi hdi
      obtain ⟨-, hpN, -, hs⟩ := okO_spec (h i hi)
      obtain ⟨hdp, hce⟩ := hs (by change d i ≠ 0; omega)
      change d (p i) + 1 = d i at hdp
      obtain ⟨hcp, g, hg, hgr⟩ := ih (p i) hpN (by omega)
      change c i = cjO n w X XI Y YI _ (c (p i)) at hce
      rw [hce]
      unfold cjO
      cases hb : Nat.beq (fldO (r i) (n * w + pb) 1) 1
      · obtain ⟨h1, h2⟩ := conj_step hX hXI hcp hXr hXIr hgr
        refine ⟨h1, x * g, H.mul_mem hxH hg, ?_⟩
        simpa [mul_assoc] using h2
      · obtain ⟨h1, h2⟩ := conj_step hY hYI hcp hYr hYIr hgr
        refine ⟨h1, y * g, H.mul_mem hyH hg, ?_⟩
        simpa [mul_assoc] using h2
  have key' : ∀ i < N, canonK n w (mask w) (n * w) (c i) = true ∧
      ∃ σ : Equiv.Perm (Fin n), TabRep (unpack n w (c i)) σ ∧ ∃ g ∈ H, σ = g * t * g⁻¹ := by
    intro i hi
    obtain ⟨h1, g, hg, h2⟩ := key (d i) i hi rfl
    exact ⟨h1, _, h2, g, hg, rfl⟩
  have hmono : ∀ i j, i < j → j < N → c i < c j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ihj =>
      have hstep : c j < c (j + 1) := by
        rcases (okO_spec (h j (by omega))).1 with h1 | h1
        · omega
        · exact h1
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h1 | rfl
      · exact (ihj h1 (by omega)).trans hstep
      · exact hstep
  classical
  let σ : Fin N → Equiv.Perm (Fin n) := fun i => Classical.choose (key' i.1 i.2).2
  have hσ : ∀ i : Fin N, TabRep (unpack n w (c i.1)) (σ i) ∧ ∃ g ∈ H, σ i = g * t * g⁻¹ :=
    fun i => Classical.choose_spec (key' i.1 i.2).2
  refine ⟨List.ofFn σ, List.length_ofFn, ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    have e1 : unpack n w (c i.1) = unpack n w (c j.1) := (hσ i).1.tab_eq (hij ▸ (hσ j).1)
    have e2 := CFSG.KC.L34KSnd.unpack_inj' (key' i.1 i.2).1 (key' j.1 j.2).1 e1
    apply Fin.ext
    rcases lt_trichotomy i.1 j.1 with h1 | h1 | h1
    · exact absurd e2 (Nat.ne_of_lt (hmono _ _ h1 j.2))
    · exact h1
    · exact absurd e2.symm (Nat.ne_of_lt (hmono _ _ h1 i.2))
  · intro e he
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact (hσ i).2

end CFSG.KC.ConjRec

module

public import CFSG.GH74.Generic.S45.LEvSporJ2Spec
public import Certificates.Certificate5153
public import Certificates.Certificate5150

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45.EvSpor
open CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Bk.J2C

noncomputable abbrev tA : Equiv.Perm (Fin 315) := tp 315 j2Row2A.rep

noncomputable abbrev Esub : Subgroup (Equiv.Perm (Fin 315)) :=
  closure (tp 315 '' {x | x ∈ j2EGens.toArray})

noncomputable abbrev Ysub : Subgroup (Equiv.Perm (Fin 315)) :=
  j2P ⊓ Subgroup.centralizer ({tA} : Set (Equiv.Perm (Fin 315)))

theorem hn315 : (315 : ℕ) < 2 ^ 32 := by norm_num

theorem evalWord_rep {gs : Array Table} {H : Subgroup (Equiv.Perm (Fin 315))}
    (hrep : ∀ x ∈ gs, Rep 315 x (tp 315 x))
    (hgs : closure (tp 315 '' {x | x ∈ gs}) ≤ H) {w : List ℕ}
    (hw : ∀ i ∈ w, i < 2 * gs.size) :
    ∃ g ∈ H, Rep 315 (evalWord 315 gs w) g := by
  have key : ∀ (w : List ℕ), (∀ i ∈ w, i < 2 * gs.size) → ∀ (acc : Table) (g0 : Equiv.Perm (Fin 315)),
      Rep 315 acc g0 → g0 ∈ H →
      ∃ g ∈ H, Rep 315 (w.foldl (fun acc i => compT 315 acc
        (if i < gs.size then gs[i]! else invT 315 gs[i - gs.size]!)) acc) g := by
    intro w
    induction w with
    | nil => intro _ acc g0 h0 hH; exact ⟨g0, hH, h0⟩
    | cons i w ih =>
      intro hw acc g0 h0 hH
      rw [List.foldl_cons]
      have hi : i < 2 * gs.size := hw i List.mem_cons_self
      have hw' : ∀ j ∈ w, j < 2 * gs.size := fun j hj => hw j (List.mem_cons_of_mem _ hj)
      by_cases hlt : i < gs.size
      · rw [ite_eq_left hlt]
        have hmem : gs[i]! ∈ gs := by
          rw [getElem!_pos gs i hlt]; exact Array.getElem_mem hlt
        have hgH : tp 315 gs[i]! ∈ H := hgs (subset_closure ⟨_, hmem, rfl⟩)
        exact ih hw' _ _ (Rep.compT h0 (hrep _ hmem)) (H.mul_mem hH hgH)
      · rw [ite_eq_right hlt]
        have hlt' : i - gs.size < gs.size := by omega
        have hmem : gs[i - gs.size]! ∈ gs := by
          rw [getElem!_pos gs (i - gs.size) hlt']; exact Array.getElem_mem hlt'
        have hgH : tp 315 gs[i - gs.size]! ∈ H := hgs (subset_closure ⟨_, hmem, rfl⟩)
        exact ih hw' _ _ (Rep.compT h0 (rep_invT_of_rep hn315 (hrep _ hmem)))
          (H.mul_mem hH (H.inv_mem hgH))
  exact key w hw (idT 315) 1 (Rep.idT hn315) H.one_mem


theorem Y_facts :
    EnumsSub 315 j2C2A Ysub ∧ invsOK 315 j2C2A = true ∧
      closure (tp 315 '' {x | x ∈ j2CG}) = Ysub ∧ Nat.card ↥Ysub = 1920 ∧
      Rep 315 j2TA tA ∧ (∀ x ∈ j2CG, Rep 315 x (tp 315 x)) := by
  obtain ⟨hreps, hC2A, -⟩ := Certificates.certificate5150
  obtain ⟨-, hrepA, -⟩ := j2_reps hreps
  obtain ⟨hE, hinv⟩ := j2_C2A_enums hC2A
  have hr := (j2_rows_spec.1 j2Row2A j2Row2A_mem)
  have hC2A' : enumOK 315 cap j2Row2A.centGens 1920 = true := by
    simp only [j2C2AEnumOK, Bool.and_eq_true] at hC2A
    exact hC2A.1
  obtain ⟨-, -, hgr⟩ := enumOK_spec hn315 hC2A'
  refine ⟨hE, hinv, hr.2.2.2.1, hr.2.2.2.2.trans j2Row2A_centOrder, hrepA, fun x hx => ?_⟩
  exact hgr x (by simpa [j2CG] using hx)

theorem j2CG_size : j2CG.size = 4 := rfl

theorem j2EWords_lt : ∀ w ∈ j2EWords, ∀ i ∈ w, i < 8 := by decide

theorem E_facts
    (h : j2EEnumOK = true) :
    EnumsSub 315 j2E Esub ∧ Nat.card ↥Esub = 32 ∧ invsOK 315 j2E = true ∧
      (∀ x ∈ j2EGens, Rep 315 x (tp 315 x)) ∧ tA ∈ Esub ∧ Esub ≤ Ysub ∧
      (∀ x ∈ j2EGens, orderOf (tp 315 x) = 2 ∧ tp 315 x ≠ tA) := by
  obtain ⟨hYE, -, hYcl, -, hrepA, hrepCG⟩ := Y_facts
  simp only [j2EEnumOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hE, hcard, hgr⟩ := enumOK_spec hn315 h1
  refine ⟨hE, hcard, h2, hgr, (hE.mem_iff hrepA).1 h3, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ j2EGens := List.mem_toArray.mp hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx'
    have hw' : ∀ i ∈ w, i < 2 * j2CG.size := by
      rw [j2CG_size]
      exact j2EWords_lt w hw
    obtain ⟨g, hgY, hgrep⟩ := evalWord_rep hrepCG hYcl.le hw'
    have : tp 315 (evalWord 315 j2CG w) = g := rep_unique (hgr _ hx') hgrep
    rw [SetLike.mem_coe, this]
    exact hgY
  · intro x hx
    have hx4 := (List.all_eq_true.1 h4) x hx
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hx4
    refine ⟨orderOf_eq_two_of_involOK hn315 (hgr x hx) hx4.1, fun heq => ?_⟩
    have := (tblEq_iff_eq (hgr x hx) hrepA).2 heq
    rw [this] at hx4
    exact Bool.false_ne_true hx4.2.symm

theorem forall_mem_of_all {E : Array Table} {H : Subgroup (Equiv.Perm (Fin 315))}
    (hE : EnumsSub 315 E H) {p : Table → Bool} (h : E.all p = true)
    {P : Equiv.Perm (Fin 315) → Prop}
    (hp : ∀ T ∈ E, ∀ g, Rep 315 T g → p T = true → P g) : ∀ x ∈ H, P x := by
  intro x hx
  obtain ⟨T, hT, hrep⟩ := hE.rep_mem hx
  rw [Array.all_eq_true_iff_forall_mem] at h
  exact hp T hT x hrep (h T hT)

theorem inv_rep_of_mem {E : Array Table} (hinv : invsOK 315 E = true) {T : Table} (hT : T ∈ E)
    {g : Equiv.Perm (Fin 315)} (hg : Rep 315 T g) : Rep 315 (invT 315 T) g⁻¹ := by
  rw [invsOK, Array.all_eq_true_iff_forall_mem] at hinv
  exact Rep.inv_of_invOK hg (hinv T hT)

theorem rep_commutatorT {X Y : Table} {x y : Equiv.Perm (Fin 315)} (hx : Rep 315 X x)
    (hy : Rep 315 Y y) (hix : Rep 315 (invT 315 X) x⁻¹) (hiy : Rep 315 (invT 315 Y) y⁻¹) :
    Rep 315 (commutatorT 315 X Y) ⁅x, y⁆ := by
  have e : ⁅x, y⁆ = x * y * (x⁻¹ * y⁻¹) := by rw [commutatorElement_def, mul_assoc (x * y)]
  rw [e]
  exact Rep.compT (Rep.compT hx hy) (Rep.compT hix hiy)

theorem E_normal (hE : EnumsSub 315 j2E Esub) (hrepE : ∀ x ∈ j2EGens, Rep 315 x (tp 315 x))
    (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub) (h : j2ENormalOK = true) :
    ∀ y ∈ Ysub, ∀ e ∈ Esub, y * e * y⁻¹ ∈ Esub := by
  have hgen : ∀ x ∈ j2CG, tp 315 x ∈ normalizer (Esub : Set (Equiv.Perm (Fin 315))) := by
    intro x hx
    apply mem_normalizer_of_conj_le
    apply conj_mem_closure_of_gens (S := tp 315 '' {x | x ∈ j2EGens.toArray})
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ j2EGens := List.mem_toArray.mp he
    simp only [j2ENormalOK, Array.all_eq_true_iff_forall_mem, List.all_eq_true] at h
    have := h x hx e he'
    exact (hE.mem_iff (Rep.compT (Rep.compT (hrepCG x hx) (hrepE e he'))
      (rep_invT_of_rep hn315 (hrepCG x hx)))).1 this
  have hle : Ysub ≤ normalizer (Esub : Set (Equiv.Perm (Fin 315))) := by
    rw [← hYcl, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hgen x hx
  intro y hy e he
  exact (Subgroup.mem_normalizer_iff.1 (hle hy) e).1 he


theorem rep_of_mem_enums {E : Array Table} {H : Subgroup (Equiv.Perm (Fin 315))}
    (hE : EnumsSub 315 E H) {T : Table} (hT : T ∈ E) : ∃ c ∈ H, Rep 315 T c := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hT
  have := hE.1 k hk
  rw [getElem!_pos E k hk] at this
  exact this

theorem E_struct (hE : EnumsSub 315 j2E Esub) (hinv : invsOK 315 j2E = true)
    (hA : Rep 315 j2TA tA) (h : j2EStructOK = true) :
    (∀ x ∈ Esub, x * x = 1 ∨ x * x = tA) ∧
      (∀ x ∈ Esub, ∀ y ∈ Esub, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = tA) ∧
      (∀ x ∈ Esub, (∀ y ∈ Esub, x * y = y * x) → x = 1 ∨ x = tA) ∧
      (∀ y ∈ Esub, tA * y = y * tA) := by
  simp only [j2EStructOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  have hid : Rep 315 (idT 315) (1 : Equiv.Perm (Fin 315)) := Rep.idT hn315
  have hsq_comm : ∀ x ∈ Esub, (x * x = 1 ∨ x * x = tA) ∧
      ∀ y ∈ Esub, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = tA := by
    refine forall_mem_of_all hE h1 ?_
    intro T hT x hx hp
    rw [Bool.and_eq_true] at hp
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨?_, ?_⟩
    · rw [Bool.or_eq_true] at hp1
      rcases hp1 with h' | h'
      · exact Or.inl ((tblEq_iff_eq (Rep.compT hx hx) hid).1 h')
      · exact Or.inr ((tblEq_iff_eq (Rep.compT hx hx) hA).1 h')
    · intro y hy
      obtain ⟨Ty, hTy, hy'⟩ := hE.rep_mem hy
      have := (Array.all_eq_true_iff_forall_mem.1 hp2) Ty hTy
      have hc := rep_commutatorT hx hy' (inv_rep_of_mem hinv hT hx) (inv_rep_of_mem hinv hTy hy')
      rw [Bool.or_eq_true] at this
      rcases this with h' | h'
      · exact Or.inl ((tblEq_iff_eq hc hid).1 h')
      · exact Or.inr ((tblEq_iff_eq hc hA).1 h')
  refine ⟨fun x hx => (hsq_comm x hx).1, fun x hx => (hsq_comm x hx).2, ?_, ?_⟩
  · refine forall_mem_of_all hE h2 ?_
    intro T hT x hx hp hcent
    have hall : j2E.all (fun y => commTT 315 T y) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro Ty hTy
      obtain ⟨c, hc, hrep⟩ := rep_of_mem_enums hE hTy
      exact (commTT_iff hx hrep).2 (hcent c hc)
    simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
    rcases hp with h' | h'
    · exact Or.inl ((tblEq_iff_eq hx hid).1 h')
    · exact Or.inr ((tblEq_iff_eq hx hA).1 h')
  · intro y hy
    obtain ⟨Ty, hTy, hy'⟩ := hE.rep_mem hy
    have := (Array.all_eq_true_iff_forall_mem.1 h3) Ty hTy
    exact (commTT_iff hA hy').1 this


theorem E_cent (hY : EnumsSub 315 j2C2A Ysub) (hrepE : ∀ x ∈ j2EGens, Rep 315 x (tp 315 x))
    (hA : Rep 315 j2TA tA) (h : j2ECentOK = true) :
    ∀ g ∈ Ysub, (∀ e ∈ Esub, g * e = e * g) → g = 1 ∨ g = tA := by
  intro g hg hcent
  obtain ⟨T, hT, hrep⟩ := hY.rep_mem hg
  have hp := (Array.all_eq_true_iff_forall_mem.1 h) T hT
  have hall : j2EGens.all (fun e => commTT 315 T e) = true := by
    rw [List.all_eq_true]
    intro e he
    have heE : tp 315 e ∈ Esub := subset_closure ⟨e, List.mem_toArray.2 he, rfl⟩
    exact (commTT_iff hrep (hrepE e he)).2 (hcent _ heE)
  simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
  rcases hp with h' | h'
  · exact Or.inl ((tblEq_iff_eq hrep (Rep.idT hn315)).1 h')
  · exact Or.inr ((tblEq_iff_eq hrep hA).1 h')

theorem conjOrbit_rep {root : List ℕ} {cs : List (List ℕ)} (hroot : ∀ i ∈ root, i < 8)
    (hcs : ∀ w ∈ cs, ∀ i ∈ w, i < 8) (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub) :
    ∃ r ∈ Ysub, Rep 315 (evalWord 315 j2CG root) r ∧
      ∀ T ∈ conjOrbit root cs, ∃ c ∈ Ysub, Rep 315 T (c * r * c⁻¹) := by
  have hsz : 2 * j2CG.size = 8 := by rw [j2CG_size]
  obtain ⟨r, hrY, hrrep⟩ := evalWord_rep hrepCG hYcl.le (w := root) (by rw [hsz]; exact hroot)
  refine ⟨r, hrY, hrrep, fun T hT => ?_⟩
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hT
  obtain ⟨c, hcY, hcrep⟩ := evalWord_rep hrepCG hYcl.le (w := w) (by rw [hsz]; exact hcs w hw)
  exact ⟨c, hcY, Rep.compT (Rep.compT hcrep hrrep) (rep_invT_of_rep hn315 hcrep)⟩


theorem orbit_words_lt :
    (∀ i ∈ j2Orb1Root, i < 8) ∧ (∀ w ∈ j2Orb1Conj, ∀ i ∈ w, i < 8) ∧
      (∀ i ∈ j2Orb2Root, i < 8) ∧ (∀ w ∈ j2Orb2Conj, ∀ i ∈ w, i < 8) := by decide

theorem orbit_gen {root : List ℕ} {cs : List (List ℕ)} (hroot : ∀ i ∈ root, i < 8)
    (hcs : ∀ w ∈ cs, ∀ i ∈ w, i < 8) (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub)
    (hEn : ∀ y ∈ Ysub, ∀ e ∈ Esub, y * e * y⁻¹ ∈ Esub)
    (hE32 : Nat.card ↥Esub = 32) (h32 : enumOK 315 cap (j2TA :: conjOrbit root cs) 32 = true)
    {N : Subgroup (Equiv.Perm (Fin 315))} (hNE : N ≤ Esub) (htA : tA ∈ N)
    (hNn : ∀ y ∈ Ysub, ∀ n ∈ N, y * n * y⁻¹ ∈ N) {x : Equiv.Perm (Fin 315)} (hxN : x ∈ N)
    (hx : ∃ T ∈ conjOrbit root cs, Rep 315 T x) : Esub ≤ N := by
  obtain ⟨r, hrY, hrrep, hconj⟩ := conjOrbit_rep hroot hcs hrepCG hYcl
  obtain ⟨T0, hT0, hxrep⟩ := hx
  obtain ⟨c0, hc0, hT0rep⟩ := hconj T0 hT0
  have hx_eq : x = c0 * r * c0⁻¹ := rep_unique hxrep hT0rep
  have hrN : r ∈ N := by
    have := hNn c0⁻¹ (Ysub.inv_mem hc0) x hxN
    rw [hx_eq] at this
    simpa [mul_assoc] using this
  have hrE : r ∈ Esub := by
    have := hEn c0⁻¹ (Ysub.inv_mem hc0) x (hNE hxN)
    rw [hx_eq] at this
    simpa [mul_assoc] using this
  obtain ⟨hEnum, hcard, hgr⟩ := enumOK_spec hn315 h32
  have hmem : ∀ y ∈ (j2TA :: conjOrbit root cs).toArray, tp 315 y ∈ N ∧ tp 315 y ∈ Esub := by
    intro y hy
    have hy' : y ∈ j2TA :: conjOrbit root cs := List.mem_toArray.1 hy
    rcases List.mem_cons.1 hy' with rfl | hyO
    · exact ⟨htA, hNE htA⟩
    · obtain ⟨c, hcY, hcrep⟩ := hconj y hyO
      have : tp 315 y = c * r * c⁻¹ := rep_unique (hgr y hy') hcrep
      rw [this]
      exact ⟨hNn c hcY r hrN, hEn c hcY r hrE⟩
  have hleN : closure (tp 315 '' {y | y ∈ (j2TA :: conjOrbit root cs).toArray}) ≤ N := by
    rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y hy).1
  have hleE : closure (tp 315 '' {y | y ∈ (j2TA :: conjOrbit root cs).toArray}) ≤ Esub := by
    rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y hy).2
  have heq : closure (tp 315 '' {y | y ∈ (j2TA :: conjOrbit root cs).toArray}) = Esub :=
    Subgroup.eq_of_le_of_card_ge hleE (by rw [hcard, hE32])
  rw [← heq]
  exact hleN


theorem exists_mem_of_memT {L : List Table} {x : Table} (h : memT 315 L.toArray x = true) :
    ∃ T ∈ L, tblEq 315 x T = true := by
  rw [memT, Array.any_eq_true] at h
  obtain ⟨k, hk, hxk⟩ := h
  exact ⟨L.toArray[k], by simp, hxk⟩

theorem E_irred (hE : EnumsSub 315 j2E Esub) (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub)
    (hEn : ∀ y ∈ Ysub, ∀ e ∈ Esub, y * e * y⁻¹ ∈ Esub) (hA : Rep 315 j2TA tA)
    (hE32 : Nat.card ↥Esub = 32) (h : j2OrbitOK = true)
    {N : Subgroup (Equiv.Perm (Fin 315))} (hNE : N ≤ Esub) (htA : tA ∈ N)
    (hNn : ∀ y ∈ Ysub, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hx : ∃ x ∈ N, x ≠ 1 ∧ x ≠ tA) :
    Esub ≤ N := by
  obtain ⟨hw1, hw2, hw3, hw4⟩ := orbit_words_lt
  simp only [j2OrbitOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨x, hxN, hx1, hxA⟩ := hx
  obtain ⟨Tx, hTx, hxrep⟩ := hE.rep_mem (hNE hxN)
  have hp := (Array.all_eq_true_iff_forall_mem.1 h3) Tx hTx
  have hid : Rep 315 (idT 315) (1 : Equiv.Perm (Fin 315)) := Rep.idT hn315
  have hne1 : tblEq 315 Tx (idT 315) = false := by
    cases e : tblEq 315 Tx (idT 315)
    · rfl
    · exact absurd ((tblEq_iff_eq hxrep hid).1 e) hx1
  have hneA : tblEq 315 Tx j2TA = false := by
    cases e : tblEq 315 Tx j2TA
    · rfl
    · exact absurd ((tblEq_iff_eq hxrep hA).1 e) hxA
  rw [hne1, hneA] at hp
  simp only [Bool.false_or, Bool.or_eq_true] at hp
  rcases hp with hm | hm
  · obtain ⟨T, hT, hT'⟩ := exists_mem_of_memT hm
    obtain ⟨r, hrY, hrrep, hconj⟩ := conjOrbit_rep hw1 hw2 hrepCG hYcl
    obtain ⟨c, hcY, hcrep⟩ := hconj T hT
    have : Rep 315 Tx (c * r * c⁻¹) := rep_of_tblEq hcrep hT'
    exact orbit_gen hw1 hw2 hrepCG hYcl hEn hE32 h1 hNE htA hNn hxN
      ⟨T, hT, by rw [rep_unique hxrep this]; exact hcrep⟩
  · obtain ⟨T, hT, hT'⟩ := exists_mem_of_memT hm
    obtain ⟨r, hrY, hrrep, hconj⟩ := conjOrbit_rep hw3 hw4 hrepCG hYcl
    obtain ⟨c, hcY, hcrep⟩ := hconj T hT
    have : Rep 315 Tx (c * r * c⁻¹) := rep_of_tblEq hcrep hT'
    exact orbit_gen hw3 hw4 hrepCG hYcl hEn hE32 h2 hNE htA hNn hxN
      ⟨T, hT, by rw [rep_unique hxrep this]; exact hcrep⟩


theorem perf_words_lt : ∀ p ∈ j2PerfPairs, (∀ i ∈ p.1, i < 8) ∧ (∀ i ∈ p.2, i < 8) := by decide

theorem Y_perfect (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub) (hYcard : Nat.card ↥Ysub = 1920)
    (h : j2PerfectOK = true) : ⁅Ysub, Ysub⁆ = Ysub := by
  obtain ⟨hEnum, hcard, hgr⟩ := enumOK_spec hn315 h
  have hsz : 2 * j2CG.size = 8 := by rw [j2CG_size]
  have hle : closure (tp 315 '' {x | x ∈ j2PerfComm.toArray}) ≤ ⁅Ysub, Ysub⁆ := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ j2PerfComm := List.mem_toArray.1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx'
    obtain ⟨a, haY, harep⟩ := evalWord_rep hrepCG hYcl.le (w := p.1)
      (by rw [hsz]; exact (perf_words_lt p hp).1)
    obtain ⟨b, hbY, hbrep⟩ := evalWord_rep hrepCG hYcl.le (w := p.2)
      (by rw [hsz]; exact (perf_words_lt p hp).2)
    have hc := rep_commutatorT harep hbrep (rep_invT_of_rep hn315 harep)
      (rep_invT_of_rep hn315 hbrep)
    have : tp 315 (commutatorT 315 (evalWord 315 j2CG p.1) (evalWord 315 j2CG p.2)) = ⁅a, b⁆ :=
      rep_unique (hgr _ hx') hc
    rw [SetLike.mem_coe, this]
    exact Subgroup.commutator_mem_commutator haY hbY
  have hY : ⁅Ysub, Ysub⁆ ≤ Ysub := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Ysub.mul_mem (Ysub.mul_mem (Ysub.mul_mem ha hb) (Ysub.inv_mem ha)) (Ysub.inv_mem hb)
  refine Subgroup.eq_of_le_of_card_ge hY ?_
  rw [hYcard, ← hcard]
  exact Subgroup.card_le_of_le hle

theorem le_of_normal_isPGroup {G : Type*} [Group G] [Finite G] {Y S N : Subgroup G}
    (hS : IsSylowOf 2 S Y) (hNY : N ≤ Y) (hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hN : IsPGroup 2 ↥N) : N ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS
  have : (N.subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g g.2 n hn⟩
  have hN' : IsPGroup 2 ↥(N.subgroupOf Y) := hN.comap_subtype
  have hle := hN'.le_sylow_of_normal Q
  intro x hx
  have hxY : x ∈ Y := hNY hx
  have hmem : (⟨x, hxY⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) := hle (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [← hQ]
  exact ⟨⟨x, hxY⟩, hmem, rfl⟩

theorem factorization_1920 : (1920 : ℕ).factorization 2 = 7 := by
  rw [show (1920 : ℕ) = 2 ^ 7 * 15 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]


theorem j2CG_zero_mem : j2CG[0]! ∈ j2CG := by
  rw [getElem!_pos j2CG 0 (by decide)]; exact Array.getElem_mem _
theorem j2CG_one_mem : j2CG[1]! ∈ j2CG := by
  rw [getElem!_pos j2CG 1 (by decide)]; exact Array.getElem_mem _
theorem j2CG_three_mem : j2CG[3]! ∈ j2CG := by
  rw [getElem!_pos j2CG 3 (by decide)]; exact Array.getElem_mem _

theorem Y_two_core (hrepCG : ∀ x ∈ j2CG, Rep 315 x (tp 315 x))
    (hYcl : closure (tp 315 '' {x | x ∈ j2CG}) = Ysub) (hYcard : Nat.card ↥Ysub = 1920)
    (hE : EnumsSub 315 j2E Esub) (hEY : Esub ≤ Ysub)
    (h : j2SylowOK = true)
    {N : Subgroup (Equiv.Perm (Fin 315))} (hNY : N ≤ Ysub)
    (hNn : ∀ y ∈ Ysub, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hN : IsPGroup 2 ↥N) : N ≤ Esub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [j2SylowOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hE1, hc1, hg1⟩ := enumOK_spec hn315 h1
  obtain ⟨hE2, hc2, hg2⟩ := enumOK_spec hn315 h2
  have hCGY : ∀ x ∈ j2CG, tp 315 x ∈ Ysub := fun x hx => by
    rw [← hYcl]; exact subset_closure ⟨x, hx, rfl⟩
  have hS1gen : ∀ x ∈ j2S1Gens, tp 315 x ∈ Ysub := by
    intro x hx
    simp only [j2S1Gens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hEY (subset_closure ⟨x, List.mem_toArray.2 hx, rfl⟩)
    · exact hCGY _ j2CG_zero_mem
    · exact hCGY _ j2CG_one_mem
  have hS1 : closure (tp 315 '' {x | x ∈ j2S1Gens.toArray}) ≤ Ysub := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hS1gen x (List.mem_toArray.1 hx)
  have hg3 : tp 315 j2CG[3]! ∈ Ysub := hCGY _ j2CG_three_mem
  have hS2 : closure (tp 315 '' {x | x ∈ j2S2Gens.toArray}) ≤ Ysub := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ j2S2Gens := List.mem_toArray.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx'
    have hsrep : Rep 315 s (tp 315 s) := hg1 s hs
    have hrep := Rep.compT (Rep.compT (hrepCG _ j2CG_three_mem) hsrep)
      (rep_invT_of_rep hn315 (hrepCG _ j2CG_three_mem))
    have : tp 315 (conjT 315 j2CG[3]! (invT 315 j2CG[3]!) s) =
        tp 315 j2CG[3]! * tp 315 s * (tp 315 j2CG[3]!)⁻¹ := rep_unique (hg2 _ hx') hrep
    rw [SetLike.mem_coe, this]
    exact Ysub.mul_mem (Ysub.mul_mem hg3 (hS1gen s hs)) (Ysub.inv_mem hg3)
  have hfact : (Nat.card ↥Ysub).factorization 2 = 7 := by rw [hYcard]; exact factorization_1920
  have hsyl1 : IsSylowOf 2 (closure (tp 315 '' {x | x ∈ j2S1Gens.toArray})) Ysub :=
    isSylowOf_of_card hS1 (by rw [hc1, hfact]; norm_num)
  have hsyl2 : IsSylowOf 2 (closure (tp 315 '' {x | x ∈ j2S2Gens.toArray})) Ysub :=
    isSylowOf_of_card hS2 (by rw [hc2, hfact]; norm_num)
  have hN1 := le_of_normal_isPGroup hsyl1 hNY hNn hN
  have hN2 := le_of_normal_isPGroup hsyl2 hNY hNn hN
  intro x hx
  have hx1 := hN1 hx
  have hx2 := hN2 hx
  obtain ⟨T, hT, hTrep⟩ := hE1.rep_mem hx1
  have hm2 : memT 315 (closArr 315 cap j2S2Gens) T = true := (hE2.mem_iff hTrep).2 hx2
  have := (Array.all_eq_true_iff_forall_mem.1 h3) T hT
  rw [hm2] at this
  simp only [Bool.not_true, Bool.false_or] at this
  exact (hE.mem_iff hTrep).1 this


theorem mem_quadIdx {k : ℕ} {a b c d : ℕ} :
    (a, b, c, d) ∈ quadIdx k ↔ a < k ∧ b < k ∧ c < k ∧ d < k := by
  simp [quadIdx]

theorem hom_ext_closure {G M : Type*} [Group G] [Group M] {S : Set G}
    {f g : ↥(closure S) →* M} (h : ∀ (x : G) (hx : x ∈ S),
      f ⟨x, subset_closure hx⟩ = g ⟨x, subset_closure hx⟩) : f = g := by
  ext z
  have hz : z ∈ (⊤ : Subgroup ↥(closure S)) := Subgroup.mem_top z
  rw [← Subgroup.closure_closure_coe_preimage (k := S)] at hz
  refine Subgroup.closure_induction (p := fun z _ => f z = g z) ?_ ?_ ?_ ?_ hz
  · intro x hx
    exact h x.1 hx
  · simp
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro x _ hx
    simp [hx]

theorem aut_card_le (hE : EnumsSub 315 j2E Esub) (hA : Rep 315 j2TA tA)
    (hgr : ∀ x ∈ j2EGens, Rep 315 x (tp 315 x))
    (hgi : ∀ x ∈ j2EGens, orderOf (tp 315 x) = 2 ∧ tp 315 x ≠ tA)
    (hcenter : ∀ x ∈ Esub, (∀ y ∈ Esub, x * y = y * x) → x = 1 ∨ x = tA)
    (htAc : ∀ y ∈ Esub, tA * y = y * tA)
    (htA2 : orderOf tA = 2) (htAmem : tA ∈ Esub) (hcount : j2AutCount ≤ 1920) :
    Nat.card (MulAut ↥Esub) ≤ 1920 := by
  classical
  have hsz : j2EGens.toArray.size = 4 := rfl
  have hE4mem : ∀ i : Fin 4, j2EGens.toArray[i.val]! ∈ j2EGens := fun i => by
    rw [getElem!_pos j2EGens.toArray i.val (by omega)]
    exact List.mem_toArray.1 (Array.getElem_mem _)
  have hgmem : ∀ i : Fin 4, tp 315 j2EGens.toArray[i.val]! ∈ Esub := fun i =>
    subset_closure ⟨_, List.mem_toArray.2 (hE4mem i), rfl⟩
  let ge : Fin 4 → ↥Esub := fun i => ⟨tp 315 j2EGens.toArray[i.val]!, hgmem i⟩
  have hdet : ∀ α α' : MulAut ↥Esub, (∀ i, α (ge i) = α' (ge i)) → α = α' := by
    intro α α' h
    have hmh : α.toMonoidHom = α'.toMonoidHom := by
      refine hom_ext_closure ?_
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨k, hk, hky⟩ := Array.getElem_of_mem hy
      have hk' : k < 4 := by rw [← hsz]; exact hk
      have : (⟨tp 315 y, subset_closure ⟨y, hy, rfl⟩⟩ : ↥Esub) = ge ⟨k, hk'⟩ := by
        apply Subtype.ext
        show tp 315 y = tp 315 j2EGens.toArray[k]!
        rw [getElem!_pos j2EGens.toArray k hk, hky]
      exact (congrArg (fun z => α.toMonoidHom z) this).trans
        ((h ⟨k, hk'⟩).trans (congrArg (fun z => α'.toMonoidHom z) this.symm))
    exact MulEquiv.ext fun z => by simpa using congrArg (fun f => f z) hmh
  let tAe : ↥Esub := ⟨tA, htAmem⟩
  have htAe1 : tAe ≠ 1 := by
    intro h
    have : tA = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at htA2
    omega
  have hfix : ∀ α : MulAut ↥Esub, α tAe = tAe := by
    intro α
    have hc : ∀ y ∈ Esub, ((α tAe : ↥Esub) : Equiv.Perm (Fin 315)) * y =
        y * ((α tAe : ↥Esub) : Equiv.Perm (Fin 315)) := by
      intro y hy
      obtain ⟨y0, hy0⟩ := α.surjective ⟨y, hy⟩
      have h1 : tAe * y0 = y0 * tAe := Subtype.ext (htAc y0.1 y0.2)
      have := congrArg α h1
      rw [map_mul, map_mul, hy0] at this
      exact congrArg Subtype.val this
    rcases hcenter _ (α tAe).2 hc with h | h
    · exfalso
      apply htAe1
      apply α.injective
      rw [map_one]
      exact Subtype.ext h
    · exact Subtype.ext h
  have hI : ∀ (α : MulAut ↥Esub) (i : Fin 4), ∃ k < j2NCInvs.size,
      Rep 315 j2NCInvs[k]! ((α (ge i) : ↥Esub) : Equiv.Perm (Fin 315)) := by
    intro α i
    have hge2 : orderOf (ge i : ↥Esub) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact (hgi _ (hE4mem i)).1
    have hz2 : orderOf ((α (ge i) : ↥Esub) : Equiv.Perm (Fin 315)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hge2
    have hzne : (α (ge i) : ↥Esub) ≠ tAe := by
      intro h
      have : ge i = tAe := by
        apply α.injective
        rw [h, hfix α]
      exact (hgi _ (hE4mem i)).2 (congrArg Subtype.val this)
    obtain ⟨T, hT, hrep⟩ := hE.rep_mem (α (ge i)).2
    have hinvol : involOK 315 T = true := involOK_of_orderOf hn315 hrep hz2
    have hne : tblEq 315 T j2TA = false := by
      cases e : tblEq 315 T j2TA
      · rfl
      · exact absurd (Subtype.ext ((tblEq_iff_eq hrep hA).1 e)) hzne
    have hTI : T ∈ j2NCInvs := by
      rw [j2NCInvs, Array.mem_filter]
      exact ⟨hT, by simp [hinvol, hne]⟩
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hTI
    exact ⟨k, hk, by rw [getElem!_pos j2NCInvs k hk, hkT]; exact hrep⟩
  choose kf hkf using hI
  let f : MulAut ↥Esub → ℕ × ℕ × ℕ × ℕ := fun α => (kf α 0, kf α 1, kf α 2, kf α 3)
  have hfinj : Function.Injective f := by
    intro α α' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    apply hdet
    intro i
    have hk : kf α i = kf α' i := by fin_cases i <;> simp [h0, h1, h2, h3]
    apply Subtype.ext
    exact rep_unique (hkf α i).2 (hk ▸ (hkf α' i).2)
  have hfmem : ∀ α, f α ∈ (quadIdx j2NCInvs.size).filter autPatOK := by
    intro α
    rw [List.mem_filter]
    refine ⟨mem_quadIdx.2 ⟨(hkf α 0).1, (hkf α 1).1, (hkf α 2).1, (hkf α 3).1⟩, ?_⟩
    have hcomm : ∀ i j : Fin 4, commTT 315 j2NCInvs[kf α i]! j2NCInvs[kf α j]! =
        commTT 315 j2EGens.toArray[i.val]! j2EGens.toArray[j.val]! := by
      intro i j
      apply Bool.eq_iff_iff.2
      rw [commTT_iff (hkf α i).2 (hkf α j).2, commTT_iff (hgr _ (hE4mem i)) (hgr _ (hE4mem j))]
      constructor
      · intro h'
        have h2 : α (ge i * ge j) = α (ge j * ge i) := by
          rw [map_mul, map_mul]
          exact Subtype.ext h'
        have h3 := α.injective h2
        exact congrArg Subtype.val h3
      · intro h'
        have h2 : ge i * ge j = ge j * ge i := Subtype.ext h'
        have h3 := congrArg α h2
        rw [map_mul, map_mul] at h3
        exact congrArg Subtype.val h3
    unfold autPatOK
    simp only [f, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨hcomm 0 1, hcomm 0 2⟩, hcomm 0 3⟩, hcomm 1 2⟩, hcomm 1 3⟩, hcomm 2 3⟩
  have : Finite (MulAut ↥Esub) := Finite.of_injective (fun α : MulAut ↥Esub => α.toEquiv)
    (fun a b h => MulEquiv.ext fun z => congrArg (fun e => e z) h)
  let _ : Fintype (MulAut ↥Esub) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h1 : Fintype.card (MulAut ↥Esub) ≤
      (((quadIdx j2NCInvs.size).filter autPatOK).toFinset).card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (MulAut ↥Esub)))
      (t := ((quadIdx j2NCInvs.size).filter autPatOK).toFinset) f
      (fun α _ => List.mem_toFinset.2 (hfmem α)) (hfinj.injOn)
    simpa using this
  have h2 := List.toFinset_card_le ((quadIdx j2NCInvs.size).filter autPatOK)
  have h3 : ((quadIdx j2NCInvs.size).filter autPatOK).length = j2AutCount := rfl
  omega


structure J2CentModel : Prop where
  tA_order : orderOf tA = 2
  card_Y : Nat.card ↥Ysub = 1920
  E_le : Esub ≤ Ysub
  card_E : Nat.card ↥Esub = 32
  tA_mem : tA ∈ Esub
  E_normal : ∀ y ∈ Ysub, ∀ e ∈ Esub, y * e * y⁻¹ ∈ Esub
  sq_mem : ∀ x ∈ Esub, x * x = 1 ∨ x * x = tA
  comm_mem : ∀ x ∈ Esub, ∀ y ∈ Esub, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = tA
  center : ∀ x ∈ Esub, (∀ y ∈ Esub, x * y = y * x) → x = 1 ∨ x = tA
  cent_E : ∀ g ∈ Ysub, (∀ e ∈ Esub, g * e = e * g) → g = 1 ∨ g = tA
  irred : ∀ N : Subgroup (Equiv.Perm (Fin 315)), N ≤ Esub → tA ∈ N →
    (∀ y ∈ Ysub, ∀ n ∈ N, y * n * y⁻¹ ∈ N) → (∃ x ∈ N, x ≠ 1 ∧ x ≠ tA) → Esub ≤ N
  perfect : ⁅Ysub, Ysub⁆ = Ysub
  two_core : ∀ N : Subgroup (Equiv.Perm (Fin 315)), N ≤ Ysub →
    (∀ y ∈ Ysub, ∀ n ∈ N, y * n * y⁻¹ ∈ N) → IsPGroup 2 ↥N → N ≤ Esub
  aut : Nat.card (MulAut ↥Esub) ≤ 1920

theorem j2_cent_model :
    J2CentModel := by
  obtain ⟨hEnum, hnorm, hstruct, hcent, horbit, hperf, hsyl, hcount⟩ :=
    Certificates.certificate5153
  obtain ⟨hYE, hYinv, hYcl, hYcard, hrepA, hrepCG⟩ := Y_facts
  obtain ⟨hE, hEcard, hEinv, hgr, htAmem, hEY, hgi⟩ := E_facts hEnum
  have hEn := E_normal hE hgr hrepCG hYcl hnorm
  obtain ⟨hsq, hcomm, hcen, htAc⟩ := E_struct hE hEinv hrepA hstruct
  have htA2 : orderOf tA = 2 := (j2_rows_spec.1 j2Row2A j2Row2A_mem).2.1
  exact
    { tA_order := htA2
      card_Y := hYcard
      E_le := hEY
      card_E := hEcard
      tA_mem := htAmem
      E_normal := hEn
      sq_mem := hsq
      comm_mem := hcomm
      center := hcen
      cent_E := E_cent hYE hgr hrepA hcent
      irred := fun N hNE htA hNn hx => E_irred hE hrepCG hYcl hEn hrepA hEcard horbit hNE htA hNn hx
      perfect := Y_perfect hrepCG hYcl hYcard hperf
      two_core := fun N hNY hNn hN => Y_two_core hrepCG hYcl hYcard hE hEY hsyl hNY hNn hN
      aut := aut_card_le hE hrepA hgr hgi hcen htAc htA2 htAmem hcount }

end CFSG.GH74.GLS.C3.Layer1.Bk.J2C

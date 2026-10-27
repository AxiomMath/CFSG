module

public import CFSG.Certificates.Kernel.SporLatDcOrbits

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

theorem isS_spec {w : List ℕ} (h : isS P.C w = true) : ∀ l ∈ w, 2 ≤ l ∧ l < 2 + P.C.ns := by
  intro l hl
  have h1 := (List.all_eq_true.mp h) l hl
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
  exact h1

theorem isS_lt {w : List ℕ} (h : isS P.C w = true) : ∀ l ∈ w, l < 2 + P.C.ns :=
  fun l hl => (isS_spec P h l hl).2

private theorem orbOK_Kpart {j : ℕ} (hj : j < P.D.obase.length) :
    (Nat.beq (P.D.K.getD j []).length 0 ||
      ((P.D.K.getD j []).all (fun k => isS P.C k &&
          Nat.beq (wordF P.C.L k (P.D.obase.getD j 0)) (P.D.obase.getD j 0)) &&
        sortedLt ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)) &&
        Nat.beq (Nat.mul (P.D.K.getD j []).length (P.D.osz.getD j 0)) P.s)) = true := by
  have h := orbOK_of_lt P hj
  unfold orbOKS at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

private theorem orbOK_Kpart' {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) :
    ((P.D.K.getD j []).all (fun k => isS P.C k &&
        Nat.beq (wordF P.C.L k (P.D.obase.getD j 0)) (P.D.obase.getD j 0)) &&
      sortedLt ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)) &&
      Nat.beq (Nat.mul (P.D.K.getD j []).length (P.D.osz.getD j 0)) P.s) = true := by
  have h := orbOK_Kpart P hj
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Nat.beq_eq] at h
    omega
  · exact h

theorem K_isS {j : ℕ} (hj : j < P.D.obase.length) {k : List ℕ}
    (hk : k ∈ P.D.K.getD j []) : isS P.C k = true := by
  have h := orbOK_Kpart' P hj (List.length_pos_iff.mpr (List.ne_nil_of_mem hk))
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have h2 := (List.all_eq_true.mp h.1.1) k hk
  rw [Bool.and_eq_true] at h2
  exact h2.1

theorem K_fixes_word {j : ℕ} (hj : j < P.D.obase.length) {k : List ℕ}
    (hk : k ∈ P.D.K.getD j []) :
    wordF P.C.L k (P.D.obase.getD j 0) = P.D.obase.getD j 0 := by
  have h := orbOK_Kpart' P hj (List.length_pos_iff.mpr (List.ne_nil_of_mem hk))
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have h2 := (List.all_eq_true.mp h.1.1) k hk
  rw [Bool.and_eq_true, Nat.beq_eq] at h2
  exact h2.2

private theorem K_sortedLt {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) :
    sortedLt ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)) = true := by
  have h := orbOK_Kpart' P hj h0
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

private theorem K_mul_osz {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) :
    (P.D.K.getD j []).length * P.D.osz.getD j 0 = P.s := by
  have h := orbOK_Kpart' P hj h0
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.2

private def Kelts (j : ℕ) : List Γ := (P.D.K.getD j []).map (evalElt P.els)

private theorem get_mem_K {j : ℕ} (i : Fin (P.D.K.getD j []).length) :
    (P.D.K.getD j []).get i ∈ P.D.K.getD j [] := by
  rw [List.get_eq_getElem]
  exact List.getElem_mem i.2

private theorem Kelts_mem_S {j : ℕ} (hj : j < P.D.obase.length) {k : List ℕ}
    (hk : k ∈ P.D.K.getD j []) : evalElt P.els k ∈ P.S :=
  evalElt_mem_S P (isS_spec P (K_isS P hj hk))

private theorem Kelts_act {j : ℕ} (hj : j < P.D.obase.length) {k : List ℕ}
    (hk : k ∈ P.D.K.getD j []) :
    act n (evalElt P.els k) (P.D.obase.getD j 0) = P.D.obase.getD j 0 := by
  rw [P.act_wordF_eq (isS_lt P (K_isS P hj hk)) (obase_lt P hj), K_fixes_word P hj hk]

private theorem sep_map_eq {j : ℕ} (hj : j < P.D.obase.length) {k₁ k₂ : List ℕ}
    (hk₁ : k₁ ∈ P.D.K.getD j []) (hk₂ : k₂ ∈ P.D.K.getD j [])
    (h : evalElt P.els k₁ = evalElt P.els k₂) :
    P.D.sep.map (wordF P.C.L k₁) = P.D.sep.map (wordF P.C.L k₂) := by
  rw [List.map_inj_left]
  intro p hp
  rw [← P.act_wordF_eq (isS_lt P (K_isS P hj hk₁)) (sep_lt P hp),
    ← P.act_wordF_eq (isS_lt P (K_isS P hj hk₂)) (sep_lt P hp), h]

private theorem Kelts_nodup {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) : (P.Kelts j).Nodup := by
  have himg : ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)).Nodup :=
    sortedLt_nodup (K_sortedLt P hj h0)
  have hinj : ∀ x ∈ P.D.K.getD j [], ∀ y ∈ P.D.K.getD j [],
      evalElt P.els x = evalElt P.els y → x = y := by
    intro x hx y hy he
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    obtain ⟨j', hj', hjy⟩ := List.getElem_of_mem hy
    have he' : evalElt P.els ((P.D.K.getD j [])[i]'hi) =
        evalElt P.els ((P.D.K.getD j [])[j']'hj') := by
      have h := he
      rw [← hix, ← hjy] at h
      exact h
    have hml : ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)).get
          ⟨i, by simpa using hi⟩ =
        ((P.D.K.getD j []).map fun k => P.D.sep.map (wordF P.C.L k)).get
          ⟨j', by simpa using hj'⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [List.getElem_map]
      exact sep_map_eq P hj (List.getElem_mem hi) (List.getElem_mem hj') he'
    have hij : i = j' := by
      have h2 := (himg.get_inj_iff).mp hml
      simpa using h2
    rw [← hix, ← hjy]
    subst hij
    rfl
  exact List.Nodup.map_on hinj (List.Nodup.of_map _ himg)

private def Kstab {j : ℕ} (hj : j < P.D.obase.length)
    (i : Fin (P.D.K.getD j []).length) :
    ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
  ⟨⟨evalElt P.els ((P.D.K.getD j []).get i), Kelts_mem_S P hj (get_mem_K P i)⟩,
   by
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [← act_eq]
    exact Kelts_act P hj (get_mem_K P i)⟩

private theorem Kstab_injective {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) : Function.Injective (Kstab P hj) := by
  intro i j' hij
  have h1 : evalElt P.els ((P.D.K.getD j []).get i) =
      evalElt P.els ((P.D.K.getD j []).get j') := by
    have h2 := congrArg (fun x :
        ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) =>
        ((x : ↥P.S) : Γ)) hij
    simpa only [Kstab, Subtype.coe_mk] using h2
  have h2 : (P.Kelts j)[i.1]'(by simpa [Kelts] using i.2) =
      (P.Kelts j)[j'.1]'(by simpa [Kelts] using j'.2) := by
    simp only [Kelts, List.getElem_map]
    rw [List.get_eq_getElem] at h1
    exact h1
  have h3 : i.1 = j'.1 := (Kelts_nodup P hj h0).getElem_inj_iff.mp h2
  exact Fin.ext h3

private theorem Kelts_card_le {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) :
    (P.D.K.getD j []).length ≤
      Nat.card (MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) := by
  haveI : Fintype ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
    Fintype.ofFinite _
  have h := Fintype.card_le_of_injective (Kstab P hj) (Kstab_injective P hj h0)
  rw [Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  exact h

private theorem Kelts_card_eq {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) :
    (P.D.K.getD j []).length =
      Nat.card (MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) := by
  have h1 : (P.D.K.getD j []).length * P.D.osz.getD j 0 = P.s := K_mul_osz P hj h0
  have h2 : Nat.card (MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) *
      P.D.osz.getD j 0 = P.s := by
    rw [Nat.mul_comm, osz_mul_stab P hj, S_card]
  have h3 : (P.D.K.getD j []).length * P.D.osz.getD j 0 =
      Nat.card (MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) *
        P.D.osz.getD j 0 := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right (osz_pos P hj) h3

theorem K_enum {j : ℕ} (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    {s : Γ} (hsS : s ∈ P.S)
    (hfix : act n s (P.D.obase.getD j 0) = P.D.obase.getD j 0) :
    ∃ k ∈ P.D.K.getD j [], evalElt P.els k = s := by
  classical
  haveI : Fintype ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
    Fintype.ofFinite _
  have hbij : Function.Bijective (Kstab P hj) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨Kstab_injective P hj h0, by
        rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Kelts_card_eq P hj h0]⟩
  let x : ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
    ⟨⟨s, hsS⟩, by
      rw [MulAction.mem_stabilizer_iff]
      apply Fin.ext
      rw [← act_eq]
      exact hfix⟩
  obtain ⟨i, hi⟩ := hbij.2 x
  refine ⟨(P.D.K.getD j []).get i, get_mem_K P i, ?_⟩
  have hg : ((Kstab P hj i : ↥(MulAction.stabilizer P.S
      (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n))) : Γ) = s := by
    rw [hi]
  simpa [Kstab] using hg

end DcSoundCtx

end CFSG.KC.SLDc

end
